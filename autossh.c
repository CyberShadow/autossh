/*
 *	Start an ssh session (or tunnel) and monitor it.
 *	If it fails or blocks, restart it.
 *
 * 	From the example of rstunnel.
 *
 * Copyright (c) Carson Harding, 2002,2003,2004.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are freely permitted.
 *
 * THIS SOFTWARE IS PROVIDED ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, 
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY 
 * AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL 
 * THE AUTHOR OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, 
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, 
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR 
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF 
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

#include <sys/types.h>
#include <sys/time.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <fcntl.h>
#include <netdb.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <signal.h>
#include <limits.h>
#include <sys/wait.h>
#include <setjmp.h>
#include <stdarg.h>
#include <syslog.h>
#include <time.h>
#include <errno.h>

#if defined(__APPLE__)
#include "fakepoll.h"
typedef int socklen_t;
#else
#include <poll.h>
#endif

#if defined(__OpenBSD__) || defined(__FreeBSD__) || defined(__NetBSD__)
#define HAVE_SETPROCTITLE
#endif

#if defined(__svr4__) && !defined(__aix__)
#ifndef _PATH_DEVNULL
#define _PATH_DEVNULL "/dev/null"
#endif
#include "daemon.h"
#else
#define HAVE_DAEMON_FUNC
#endif

#if !defined(__svr4__) && !defined(__aix__)
extern char *__progname;
#else
char *__progname;
#define u_int16_t uint16_t
#endif

const char *rcsid = "$Id: autossh.c,v 1.33 2004/02/19 17:53:50 harding Exp $";

#ifndef SSH_PATH
#define SSH_PATH "/usr/bin/ssh"
#endif

#define POLL_TIME	600	/* 10 minutes default */
#define GATE_TIME	30	/* 30 seconds default */
#define TIMEO_IO	1	/* read/write timeout (secs) */
#define TIMEO_POLLA	15000	/* poll on accept() timeout (msecs) */
#define TIMEO_POLLIO	15000	/* poll on net io (msecs) */
#define MAX_CONN_TRIES	3	/* how many attempts */

#define P_CONTINUE	0	/* continue monitoring */
#define P_RESTART	1	/* restart ssh process */
#define P_EXIT		2	/* exit */

#define L_FILELOG 	0x01	/* log to file   */
#define L_SYSLOG  	0x02	/* log to syslog */

int	logtype  = L_SYSLOG;	/* default log to syslog */
int	loglevel = LOG_INFO;	/* default loglevel */
int	syslog_perror;		/* use PERROR option? */
FILE	*flog;			/* log file */

char	*writep;		/* write port as string */
char	readp[16];		/* read port as string */
char	*mhost = "127.0.0.1";	/* host in port forwards */
char	*env_port;		/* port spec'd in environment */
int	poll_time = POLL_TIME;	/* default connection poll time */
double	gate_time = GATE_TIME;	/* time to "make it out of the gate" */
char	*ssh_path = SSH_PATH;	/* default path to ssh */
int	start_count;		/* # of times exec()d ssh */
time_t	start_time;		/* time we exec()d ssh */

int	newac;			/* argc, argv for ssh */
char	**newav;
#define START_AV_SZ	16

int	cchild;			/* current child */

volatile sig_atomic_t	dolongjmp;
sigjmp_buf jumpbuf;

void	usage(void);
void	get_env_args(void);
void	add_arg(char *s);
void	strip_arg(char *arg, char ch);
void	ssh_run(int sock, char **argv);
int	ssh_watch(int sock);
int	ssh_wait(int options);
void	ssh_kill(void);
int	conn_test(int sock, char *host, char *write_port);
void	conn_addr(char *host,  char *port, struct addrinfo **resp);
int	conn_listen(char *host,  char *port);
int	conn_remote(char *host,  char *port);
void	grace_time(time_t last_start);
void	errlog(int level, char *fmt, ...);
void	xerrlog(int level, char *fmt, ...);
void	doerrlog(int level, char *fmt, va_list ap);
char	*timestr(void);
void	sig_catch(int sig);
#if !defined(HAVE_DAEMON_FUNC)
int	daemon(int nochdir, int noclose);
#endif

void
usage(void)
{
	fprintf(stderr, 
	    "usage: %s -M monitor_port [-f] [SSH_OPTIONS]\n", 
	    __progname);
}

int
main(int argc, char **argv)
{
	int	i;
	int	n;
	int	ch;
	char	*s;
	int	wp, rp;
	char	wmbuf[256], rmbuf[256];

	int	sock;
	int	done_fwds = 0;
	int	runasdaemon = 0;

#if defined(__svr4__) || defined(__aix__)
	__progname = "autossh";
#endif	

	/* 
	 * set up options from environment
	 */
	get_env_args();

	/*
	 * We accept all ssh args, and quietly pass them on
	 * to ssh when we call it.
	 */
	while ((ch = getopt(argc, argv, 
	    "M:VafgknqstvxACNPTX1246b:c:e:i:l:m:o:p:F:L:R:D:")) != -1) {
		switch(ch) {
		case 'M':
			if (!env_port)
				writep = optarg;
			break;
		case 'V':
			fprintf(stderr, "%s %s\n", __progname, VER);
			exit(0);
			break;
		case 'f':
			runasdaemon = 1;
			break;
		case '?':
			usage();
			exit(1);
			break;
		default:
			/* other options get passed to ssh */
			break;
		}
	}

	/* if we got it from the environment */
	if (env_port)
		writep = env_port;

	/*
	 * We must at least have a monitor port and a remote host.
	 */
	if (env_port) { 
		if (argc < 2) {
			usage();
			exit(1);
		}
	} else if (!writep || argc < 4) {
		usage();
		exit(1);
	}

	/* 
	 * Check, and get the read port (write port + 1);
	 * then construct port-forwarding arguments for ssh.
	 */
	wp = strtoul(writep, &s, 0);
	if (wp == 0) {
		errlog(LOG_INFO, "port set to 0, monitoring disabled");
		writep = NULL;
	}
	else if (*s != '\0')
		xerrlog(LOG_ERR, "invalid port \"%s\"", writep);
	else if (wp > 65534 || wp < 0)
		xerrlog(LOG_ERR, "monitor ports (%d,%d) out of range",wp,rp);
	else {
		rp = wp+1;
		/* all this for solaris; we could use asprintf() */
		(void)snprintf(readp, sizeof(readp), "%d", rp);

		/* port-forward arg strings */
		n = snprintf(wmbuf, sizeof(wmbuf), "%d:%s:%d", wp, mhost, wp);
		if (n > sizeof(wmbuf))
			xerrlog(LOG_ERR, 
			    "overflow building forwarding string");
		n = snprintf(rmbuf, sizeof(rmbuf), "%d:%s:%d", wp, mhost, rp);
		if (n > sizeof(rmbuf))
			xerrlog(LOG_ERR, 
			    "overflow building forwarding string");
	}

	if (logtype & L_SYSLOG)
#if !defined(__svr4__) && !defined(__aix__)
		openlog(__progname, LOG_PID|syslog_perror, LOG_USER);
#else
		openlog(__progname, LOG_PID, LOG_USER);
#endif

	/*
	 * Build a new arg list, skipping -f, -M and inserting 
	 * port forwards.
	 */
	add_arg(ssh_path);
	for (i = 1; i < argc; i++) {
 		if (env_port && !done_fwds) {
			add_arg("-L");
			add_arg(wmbuf);
			add_arg("-R");
			add_arg(rmbuf);
			done_fwds = 1;
		} else if (argv[i][0] == '-' && argv[i][1] == 'M') {
			if (argv[i][2] == '\0')
				i++;
			if (wp && !done_fwds) {
				add_arg("-L");
				add_arg(wmbuf);
				add_arg("-R");
				add_arg(rmbuf);
				done_fwds = 1;
			}
			continue;
		}
		/* look for -f in option args and strip out */
		strip_arg(argv[i], 'f');
		add_arg(argv[i]);
	}

	/* 
	 * Only if we're doing the network monitor thing.
	 * Socket once opened stays open for listening for 
	 * the duration of the program.
	 */
	if (writep) {
		sock = conn_listen(mhost, readp);
		/* set close-on-exec */
		(void)fcntl(sock, F_SETFD, 1);
	}

	if (runasdaemon) {
		if (daemon(0, 0) == -1) {
			xerrlog(LOG_ERR, "run as daemon failed: %s", 
			    strerror(errno));
		}
	}

	ssh_run(sock, newav);

	shutdown(sock, SHUT_RDWR);
	close(sock);

	if (logtype & L_SYSLOG)
		closelog();

	exit(0);
}

/*
 * Add an argument to the argument array.
 */
void
add_arg(char *s) 
{
	char	*p;
	size_t	len;
	static	size_t newamax = START_AV_SZ;

	len = strlen(s);
	if (len == 0)
		return;

	if (!newav) {
		newav = malloc(START_AV_SZ * sizeof(char *));
		if (!newav)
			xerrlog(LOG_ERR, "malloc: %s", strerror(errno));
	} else if (newac >= newamax-1) {
		newamax *= 2;
		newav = realloc(newav, newamax * sizeof(char *));
		if (!newav)
			xerrlog(LOG_ERR, "realloc: %s", strerror(errno));
	}
	p = malloc(len+1);		
	if (!p) xerrlog(LOG_ERR, "malloc: %s", strerror(errno));
	memmove(p, s, len);
	p[len] = '\0';
	newav[newac++] = p;
	newav[newac] = NULL;
	
	return;
}

/*
 * strip an argument option from an option string; strings that
 * end up with just a '-' become zero length (add_arg() will
 * skip them). An option that enters as '-' is untouched.
 */
void
strip_arg(char *arg, char ch)
{
	char *f;

	if (arg[0] == '-' && arg[1] != '\0') {
		f = arg;
		while ((f = strchr(f, ch)) != NULL)
			(void)strcpy(f, f+1);
		/* left with "-" alone? then truncate */
		if (arg[1] == '\0')
			arg[0] = '\0';
	}

	return;
}

/* 
 * Ugly, but as we've used so many command args...
 */
void
get_env_args(void)
{
	char	*s;
	char	*t;

	if ((s = getenv("AUTOSSH_PATH")) != NULL)
		ssh_path = s;

	if ((s = getenv("AUTOSSH_DEBUG")) != NULL) {
#if !defined(__svr4__) && !defined(__aix__)
		syslog_perror = LOG_PERROR;
#endif
		loglevel = LOG_DEBUG;
	} else if ((s = getenv("AUTOSSH_LOGLEVEL")) != NULL) {
		loglevel = strtoul(s, &t, 0);
		if (*t != '\0' ||
		    loglevel < LOG_EMERG || loglevel > LOG_DEBUG)
			xerrlog(LOG_ERR, "invalid log level \"%s\"", s);
	}

	if ((s = getenv("AUTOSSH_LOGFILE")) != NULL) {
		flog = fopen(s, "a");
		if (!flog)
			xerrlog(LOG_ERR, "%s: %s", s, strerror(errno));
		logtype = L_FILELOG;
	}

	if ((s = getenv("AUTOSSH_POLL")) != NULL) {
		poll_time = strtoul(s, &t, 0);
		if (poll_time == 0 || *t != '\0' )
			xerrlog(LOG_ERR, 
			    "invalid poll time \"%s\"", s);
		if (poll_time <= 0)
			poll_time = POLL_TIME; 
	}

	if ((s = getenv("AUTOSSH_GATETIME")) != NULL) {
		gate_time = (double)strtoul(s, &t, 0);
		if (gate_time < 0 || *t != '\0' )
			xerrlog(LOG_ERR, "invalid gate time \"%s\"", s);
	}		

	if ((s = getenv("AUTOSSH_PORT")) != NULL)
		env_port = s;

	return;
}

/*
 * Run ssh
 */
void
ssh_run(int sock, char **av) 
{
	struct	sigaction act;
	struct	timeval tv;

	act.sa_handler = sig_catch;
	sigemptyset(&act.sa_mask);
	act.sa_flags = 0;

	sigaction(SIGTERM, &act, NULL);
	sigaction(SIGINT,  &act, NULL);
	sigaction(SIGHUP,  &act, NULL);
	sigaction(SIGUSR1, &act, NULL);
	sigaction(SIGUSR2, &act, NULL);
	sigaction(SIGCHLD, &act, NULL);

	act.sa_flags |= SA_RESTART;
	sigaction(SIGALRM, &act, NULL);

	/* 
	 * There are much better things. and we all wait
	 * for solaris to get /dev/random.
	 */
	gettimeofday(&tv, NULL);
	srandom(getpid() ^ tv.tv_usec ^ tv.tv_sec);

	while (1) {
		start_count++;
		grace_time(start_time);
		time(&start_time);
		errlog(LOG_INFO, "starting ssh (count %d)", 
		   start_count);
		cchild = fork();
		switch (cchild) {
		case 0:
			errlog(LOG_DEBUG, "execing %s", av[0]);
			execvp(av[0], av);
			xerrlog(LOG_ERR, "%s: %s", av[0], strerror(errno));
			 /* else can loop restarting! */
			kill(SIGTERM, getppid());
			exit(1);
			break;
		case -1:
			cchild = 0;
			xerrlog(LOG_ERR, "fork: %s", strerror(errno));
			break;
		default:
			errlog(LOG_INFO, "ssh child pid is %d", (int)cchild);
			if (ssh_watch(sock) == P_EXIT)
				return;
			break;
		}
	}

}

/*
 * Periodically test network connection. On signals, determine what
 * happened or what to do with child. Return as necessary for exit 
 * or restart of child.
 */
int
ssh_watch(int sock)
{
	int	r;
	int	val;
	static	int	secs_left;

#if defined(HAVE_PROCTITLE)
	setproctitle("parent of %d (%d)", 
	    (int)cchild, start_count);
#endif

	for (;;) {	
		if ((val = sigsetjmp(jumpbuf, 1)) == 0) {

			errlog(LOG_DEBUG, "check on child %d", cchild);

			/* poll for expired child */
			r = ssh_wait(WNOHANG);
			if (r != P_CONTINUE) {
				errlog(LOG_DEBUG, 
				    "expired child, returning %d", r);
				return r;
			}

			secs_left = alarm(0);

			errlog(LOG_DEBUG, 
			    "set alarm for %d secs", 
			     poll_time - secs_left);

			alarm(poll_time - secs_left);
			dolongjmp = 1;
			pause();

		} else {

			switch(val) {
			case SIGINT:
			case SIGTERM:
			case SIGQUIT:
			case SIGABRT:
				errlog(LOG_INFO, 
				    "received signal to exit (%d)", val);
				ssh_kill();
				return P_EXIT;
				break;
			case SIGALRM:
				if (writep &&
				    !conn_test(sock, mhost, writep)) {
					errlog(LOG_INFO, 
					    "port down, restarting ssh");
					ssh_kill();
					return P_RESTART;
				}
				break;
			default:
				break;
			}
		}
	}
}

/*
 * Wait on child: with options == WNOHANG, poll for
 * dead child, else if options == 0, then wait for
 * known dead child.
 *
 * If child was deliberately killed (TERM, INT, KILL),
 * or if child called exit(0) or _exit(0), then pass
 * message on return to give up (P_EXIT). Otherwise death 
 * was unnatural (or unintended), and pass message back
 * to restart (P_RESTART).
 *
 * However, if child died with exit(1) on first try, then
 * there is some startup error (anything from network
 * connection to authentication failure), so we exit. 
 * If on a restart, however, we keep trying as it must
 * have worked once. This doesn't necessarily work if
 * the user did an interactive authentication, and then
 * isn't there on the restart to enter his password....
 * But we can only know very little about what's going 
 * on inside ssh.
 *
 * This is further complicated by the behaviour of 
 * OpenSSH when sent SIGTERM (15). It is possible to 
 * kill it before it installs the handler for that 
 * signal, in which case it autossh behaves as above 
 * and exits. But, in  at least interactive use, it 
 * appears that once the session is established ssh 
 * installs a handler, and then when signalled (killed) 
 * it exits with status 255. autossh does not know 
 * it (ssh) was signalled, so restarts it.
 *
 */
int
ssh_wait(int options) {

	int	status;
	int	evalue;
	time_t	now;

	if (waitpid(cchild, &status, options) > 0) {
		if (WIFSIGNALED(status)) {
			switch(WTERMSIG(status)) {
			case SIGINT: 
			case SIGTERM: 
			case SIGKILL:
				/* someone meant it */
				errlog(LOG_INFO, 
				    "ssh exited on signal %d; parent exiting", 
				    WTERMSIG(status));
				return P_EXIT;
				break;
			default:
				/* continue on and restart */
				errlog(LOG_INFO, 
				    "ssh exited on signal %d, restarting ssh", 
				    WTERMSIG(status));
				return P_RESTART;
				break;
			}
		} else if (WIFEXITED(status)) {
			evalue = WEXITSTATUS(status);
			if (start_count == 1 && gate_time != 0) {
				/*
				 * If ssh exits too quickly, give up.
				 */
				time(&now);
				if (difftime(now, start_time) <= gate_time) {
					errlog(LOG_ERR, 
					    "ssh exited prematurely "
					    "with status %d; %s exiting", 
					    evalue, __progname);
					return P_EXIT;
				}
			}
			switch(evalue) {
			case 255:
				/* 
				 * we can get this on an initial
				 * connection if the connection itself
				 * is ok, but authentication fails.
				 * But there's no way to do this nicely:
				 * we don't have enough info from the
			 	 * ssh session and we get the same exit
				 * status from a dropped connection.
				 * Hence the gate_time above.
				 */ 
				errlog(LOG_INFO,
				    "ssh exited with error "
				    "status %d; restarting ssh",
				    evalue);
				return P_RESTART;
				break;
			case 1:	
				/*
				 * the first time, it could be any of
				 * a number of errors; so we exit and let
				 * the user fix. But if been running ok
				 * already, then network may be down and
				 * then ssh fails exit(1) on the attempt 
				 * to reconnect....so we try to restart.
				 */
				if (start_count > 1 || gate_time == 0) {
					errlog(LOG_INFO,
					    "ssh exited with error "
					    "status %d; restarting ssh",
					    evalue);
					return P_RESTART;
				}
				/* FALLTHROUGH */
			case 0:  /* exited on success */
			default: /* remote command error status */
				errlog(LOG_INFO,
				    "ssh exited with status %d; %s exiting",
				    evalue, __progname);
				return P_EXIT;
				break;
			}
		}
	}

	/* do nothing */	
	return P_CONTINUE;
}

/*
 * Kill ssh child. This can be overly aggressive, and
 * result in kill KILL before TERM has time to take....
 * Perhaps just use TERM?
 */
void
ssh_kill(void)
{
	int w;
	int status;

	if (cchild) {
		/* overkill */
		kill(cchild, SIGTERM);
		/* if (kill(cchild, 0) != -1)
		 +	kill(cchild, SIGKILL);
		 */
		if ((w = waitpid(cchild, &status, 0)) <= 0) {
			errlog(LOG_ERR, 
			    "waitpid() not successful, returned %d", w);
		}
	}
	return;
}

/*
 * Try to prevent rapid-fire restarts on such things
 * as connection refused. Back off and try more slowly.
 * Calculate a grace period to wait based time between
 * now and the last restart and the number of tries
 * in a row that have had less than the poll_time
 * between them. 
 *
 * Questions:
 *	- should it back off faster? slower?
 */
void
grace_time(time_t last_start)
{
	int	n;
	double	t;
	int	interval;
	time_t	now;
	static	int tries;

	double	min_time;

	/* 
	 * Minimum time we have to stay up to avoid backoff
	 * behaviour. With default poll_time this is 60 secs.
	 * This may be too complicated.
	 */
	min_time = (double)(poll_time / 10);
	if (min_time < 10) min_time = 10;

	time(&now);
	if (difftime(now, last_start) >= min_time)
		tries = 0;
	else
		tries++;

	errlog(LOG_DEBUG,
	    "checking for grace period, tries = %d", tries);

	if (tries > 5) {
		t = (double)(tries - 5);
		n = (int)(poll_time / 100) * (t * (t/3));
		interval = (n > poll_time) ? poll_time : n;
		if (interval) {
			errlog(LOG_DEBUG, 
			    "sleeping for grace time %d secs", interval);
			sleep(interval);
		}
	}
	return;
}

/*
 * If we're primed, longjump back.
 */
void
sig_catch(int sig)
{
	if (dolongjmp) {
		dolongjmp = 0;
		siglongjmp(jumpbuf, sig);
	}
	return;
}

/*
 * Test the connection monitor loop can pass traffic, and that
 * we get back what we send. This needs the most testing.
 */
int
conn_test(int sock, char *host, char *write_port)
{
	int	rval;			/* default return value (failure) */
	int	tries;			/* message attempts */
	socklen_t	len;		/* listen socket info */
	struct sockaddr cliaddr;
	struct	pollfd	pfd[2];		/* poll fds */
	int	ntopoll;		/* # fds to poll */
	int	timeo_polla;		/*           - accept()       */
	int	timeo_pollio;		/*           - network io     */
	int	rd, wd;			/* read and write descriptors */
	long	id;			/* for a random number */

	size_t	wleft, rleft;		/* buffer ptrs and counters */
	ssize_t nwrite, nread;
	char	*wp, *rp;
	char	wbuf[64];
	char	rbuf[sizeof(wbuf)];

	wd = -1;			/* default desc. values */
	rd = -1;
	rval = 0;			/* default return value */
	tries = 0;			/* number of attempts */

	timeo_polla  = TIMEO_POLLA;	/* timeout value for accept() */
	timeo_pollio = TIMEO_POLLIO;	/* timeout value for net io */

	id = random();

	if (dolongjmp != 0)
		errlog(LOG_ERR, "conn_test(): error: dolongjmp != 0");

	/* set up write connection */
	if ((wd = conn_remote(host, write_port)) == -1)
		return 0;

	pfd[1].fd = wd;
	pfd[1].events = POLLOUT;

start_accept:

	/* close read socket if we're coming around again */
	if (rd != -1) {
		shutdown(rd, SHUT_RDWR);
		close(rd);
		rd = -1;
	}
	
	if (tries++ > MAX_CONN_TRIES) {
		errlog(LOG_INFO, "tried connection %d times and failed");
		goto abort_test;
	} 

	/* 
	 * Some data to send: something that is identifiable 
	 * as coming from ourselves. Any user can still trash 
	 * our listening port. We'd really like to be able to 
	 * connect and accept connections from  certain pids 
	 * (ourself, our children).
	 */
	if (snprintf(wbuf, sizeof(wbuf), 
	    "%s %d %ld", __progname, getpid(), id) >= sizeof(wbuf))
		xerrlog(LOG_ERR, "conn_test: buffer overflow");
	strcpy(rbuf, wbuf);
	rleft = wleft = strlen(wbuf);
	wp = wbuf;
	rp = rbuf;

	/* 
	 * first we're going to poll for accept()
	 */
	pfd[0].fd = sock;
	pfd[0].events = POLLIN;

	for (;;) {
		switch(poll(pfd, 1, timeo_polla)) {
		case 0:
			errlog(LOG_INFO, 
			    "timeout polling to accept read connection");
			goto abort_test;
		case -1:
			errlog(LOG_INFO, 
			    "error polling to accept read connection",
			    strerror(errno));
			goto abort_test;
		default:
			break;
		}

		if (pfd[0].revents & POLLIN) {
			rd = accept(sock, &cliaddr, &len);
			if (rd == -1) {
				errlog(LOG_INFO, 
				    "error accepting read connection",
				    strerror(errno));
				goto abort_test;
			}
			break;
		}
	}

	/* replace socket fd with accepted connection fd */
	pfd[0].fd = rd;
	pfd[0].events = POLLIN;

	/*
	 * Now, send and receive. We stop polling for write() once
	 * we've sent the whole message.
	 */
	ntopoll = 2;
	while (rleft > 0) {

		switch (poll(pfd, ntopoll, timeo_pollio)) {
		case 0:
			errlog(LOG_DEBUG, 
			    "timeout on io poll, looping to accept again");
			goto start_accept;
		case -1:
			errlog(LOG_ERR, "error on poll: %s", strerror(errno));
			goto abort_test;
		default:
			break;
		}

		if (wleft && pfd[1].revents & POLLOUT) {
			while (wleft > 0) {
				nwrite = write(wd, wp, wleft);
				if (nwrite == 0) {
					wleft = 0; /* EOF */
					break;
				} else if (nwrite == -1) {
				    if (errno == EINTR || errno == EAGAIN)
					break;
			            else
					goto abort_test;
				}
				wleft -= nwrite;
				wp    += nwrite;
			}
			/* if complete, turn off polling for write */
			if (wleft == 0)
				ntopoll = 1;
		}

		if (pfd[0].revents & POLLIN) {
			while (rleft > 0) {
				nread = read(rd, rp, rleft);
				if (nread == 0) {
					rleft = 0; /* EOF */
					break;
				} else if (nread == -1) {
				    if (errno == EINTR || errno == EAGAIN)
					break;
			            else
					goto abort_test;
				}
				rleft -= nread;
				rp    += nread;
			}
		}
	}

	/* we jump back up from here if received does not match sent */
	if (strcmp(rbuf, wbuf) != 0) {
		errlog(LOG_DEBUG, 
		    "not what I sent: \"%s\" : \"%s\"", wbuf, rbuf);
		goto start_accept;
	}

	errlog(LOG_DEBUG, "connection ok");

	rval = 1;

abort_test:

	shutdown(wd, SHUT_RDWR);
	close(wd); 
	shutdown(rd, SHUT_RDWR);
	close(rd);

	return rval;
}

/*
 * Convert names to addresses, setup for connection.
 */
void
conn_addr(char *host,  char *port, struct addrinfo **resp)
{
	int family = AF_INET;
	struct addrinfo hints;
	int error;

	memset(&hints, 0, sizeof(struct addrinfo));
	hints.ai_family = family;
	hints.ai_socktype = SOCK_STREAM;
	hints.ai_protocol = IPPROTO_TCP;

	/* Allow nodename to be null */
	hints.ai_flags |= AI_PASSIVE;

	/*
	 * In the case of binding to a wildcard address
	 * default to binding to an ipv4 address.
	 */
	if (host == NULL && hints.ai_family == AF_UNSPEC)
		hints.ai_family = AF_INET;

	if ((error = getaddrinfo(host, port, &hints, resp)))
                xerrlog(LOG_ERR, "%s", gai_strerror(error));

	return;
}

/*
 * Open connection we're writing to.
 */
int
conn_remote(char *host, char *port)
{
	int	sock;
	static  struct addrinfo *res;

	/* Cache the address info */
	if (!res)
		conn_addr(host, port, &res);

	if ((sock = socket(res->ai_family, res->ai_socktype, 
	    res->ai_protocol)) == -1)
		xerrlog(LOG_ERR, "socket: %s", strerror(errno));

	if (connect(sock, res->ai_addr, res->ai_addrlen) == -1) {
		errlog(LOG_INFO, "%s:%s: %s", host, port, strerror(errno));
		close(sock);
		return -1;
	}

	return sock;
}

/*
 * Return's a socket listening on a local port, binds to specified source
 * address. Errors in binding to the local listening port are fatal.
 */
int
conn_listen(char *host,  char *port)
{
	int sock;
	struct addrinfo *res;
	int on = 1;

	/* 
	 * Unlike conn_remote, we don't need to cache the 
	 * info; we're only calling once at start. All errors
	 * here are fatal.
	 */
	conn_addr(host, port, &res);

	if ((sock = socket(res->ai_family, res->ai_socktype,
	    res->ai_protocol)) == -1)
		xerrlog(LOG_ERR, "socket: %s", strerror(errno));

	if (setsockopt(sock, SOL_SOCKET, SO_REUSEADDR,
	    (char *) &on, sizeof on) != 0) {
		xerrlog(LOG_ERR, "setsockopt: %s", strerror(errno));
	}

	if (bind(sock, (struct sockaddr *)res->ai_addr,
	    res->ai_addrlen) == -1)
		xerrlog(LOG_ERR, "bind on %s:%s: %s", 
		    host, port, strerror(errno));

	if (listen(sock, 1) < 0)
		xerrlog(LOG_ERR, "listen: %s", strerror(errno));

	freeaddrinfo(res);

	return sock;
}

/*
 * Nicely formatted time string for logging
 */
char *
timestr(void)
{
	static	char timestr[32];
	time_t  now;
	struct	tm *tm;

	(void)time(&now);
	tm = localtime(&now);
	(void)strftime(timestr, sizeof(timestr), 
	    "%Y/%m/%d %H:%M:%S", tm);

	return timestr;
}

/*
 * Log errors.
 */	
void
errlog(int level, char *fmt, ...)
{
	va_list	ap;

	va_start(ap, fmt);
	doerrlog(level, fmt, ap);
	va_end(ap);
}

/*
 * Log and then exit with error status.
 */
void
xerrlog(int level, char *fmt, ...)
{
	va_list	ap;

	va_start(ap, fmt);
	doerrlog(level, fmt, ap);
	va_end(ap);

	ssh_kill();
	_exit(1);
}

/*
 * Log to file and/or syslog as directed. We want different
 * behaviour before syslog has been called and set up; and
 * different behaviour before we fork for ssh: errors before
 * that point result in exit.
 */
void
doerrlog(int level, char *fmt, va_list ap)
{
	FILE	*fl;
#if defined(__aix__)
	char	logbuf[1024];
#endif

	fl = flog;	/* only set per-call */

	if (loglevel >= level) {
		if (logtype & L_SYSLOG) {
#if defined(__aix__)
			(void)vsnprintf(logbuf, sizeof(logbuf), fmt, ap);
			syslog(level, logbuf);
#else
			vsyslog(level, fmt, ap);
#endif
		} else if (!fl) {
			/* 
			 * if we're not using syslog, and we
			 * don't have a log file, then use
			 * stderr.
			 */
			fl = stderr;
		}
		if ((logtype & L_FILELOG) && fl) {
			fprintf(fl, 
			    "%s %s[%d]: ", timestr(),
			    __progname, (int)getpid());
			vfprintf(fl, fmt, ap);
			fprintf(fl, "\n");
			fflush(fl);
		}
	}
	return;
}

/* END */

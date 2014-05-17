/*
** gfind 4.9 -- search for gliders in semitotalistic cellular automata
** David Eppstein, UC Irvine, 7 Mar 1998
**
** This program performs very fast searches for low-period gliders. For example,
** in Conway's Life, it can find a 10x12 c/3 spaceship instantaneously: try
**     gfind b3/s23/o3v/l36
** (This set of arguments means rule B3/S23 (Life); c/3 orthogonal,
** even bilateral symmetry, level of difficulty = 36. Run gfind without
** arguments and type return to the prompt for a full list of options.)
**
** The technique is to build a "de Bruijn graph" in which a vertex represents
** the states that a whole row of cells might sequence through in some
** (2*period)-generation time interval.  If two vertices share (2*period-1)
** row states in common, and they overlap to form a (2*period+1)-generation
** interval, then the first, middle, and last generations of the interval
** form a contiguous block of three rows in the same phase. Applying the CA
** rule to this block shows what the middle of the three rows would look like
** in the next generation.  We connect the two vertices by an edge if the
** CA rule result matches the state of this middle row in the two vertices.
** A glider corresponds to a path in this graph starting and ending at the
** constant-0 vertex.  The level of difficulty (L parameter) is the log(base 2)
** of the number of vertices in the de Bruijn graph; that is, L=2*width*period.
** However in most cases many fewer than 2^L vertices are actually searched.
**
** To reduce the size of the de Bruijn graph, we restrict our attention to
** "extensible" states, i.e. those which in which we will be able to find an
** outgoing edge for each future generation within two periods of the pattern.
** The search for extensible neighbors of a given vertex is performed by
** representing these neighbors as paths in a small auxiliary de Bruijn graph,
** in which vertices represent pairs of cells in two new rows and edges
** represent triples for which the CA rule produces the correct result.
** Reachability in this auxiliary graph is determined by a fast algorithm
** that uses table lookups to achieve 16-way bit-parallelism.
**
** The program uses two big data structures. The first keeps track of the graph
** visited so far: each vertex is represented by a pointer to its predecessor,
** and by the cells of the single row not shared with that predecessor.
** The predecessor pointers are kept in a compressed form in which blocks of
** vertices share a common base pointer, to which small offsets are added.
** Second, to avoid repeatedly visiting the same vertices, we use a hash table.
**
** Version history:
** 1.0, March 1998:
**     Creation.
**     Proliferation of symmetry modes.
**     Garbage collection of BFS Q.
** 2.0, March 1999:
**     Replace backtracking search for successors of partial pattern
**     with graph path enumeration, including one period of lookahead.
**     Temporarily disable c/1 search and skew gutter mode.
**     Automatically reduce search width when BFS tree becomes too full.
** 3.0, May 1999:
**     Add mode for searching from rear of ship forwards instead of vice versa.
**     Partial two-period lookahead in all forward searches with period >= 2,
**     and infinite lookahead (via rear-first search for width-5 pattern
**     w/don't-care boundary conditions) for c/2 orthogonal searches.
**     Re-enable search for photons (always uses rear-first ordering).
**     Disable broken 2c/n orthogonal glide-reflect modes.
**     Re-code and re-enable orthogonal skew gutter mode.
**     Allow specification of unusable rule bits, so we can find patterns
**     that work in many rules simultaneously.
**     Output whole pattern, not just asym half of it, even when width >= 16.
**     Fix various memory stomping bugs on Q overflow and in success.
**     Start tracking of versions, add version history, redo top comment.
**     Behave nicely under MacOS non-preemptive multitasking.
**     Display banner and cmd-line args at startup.
** 3.1, July 1999:
**     Diagonal gutter mode.  Reduce length of log lines.
**     Adjust the width reported in the log for diagonal skew gutter mode.
**     Include badRuleBits in tests for whether to try speed or mode with given rule.
** 3.2, September 1999:
**     Only do o2 and d3 searches if rule includes one of B2/S1234
**     Allow speeds up to c/19 ("1" followed by digit means teen period)
**     Update default basebits to match my more usual extreme-settings usage
**     Add param 'T' to taper width up gradually rather than sudden start
**     Add '*' depth-first-search variant (still need to add hybrid dfs-bfs combo)
** 4.0, November 1999:
**     In place of separate BFS and DFS (with garbage collection in BFS when
**     queue becomes full) make a combined hybrid BFS / depth first iterated
**     deepening search.  Main search is BFS, but with a limited-depth
**     depth-first search to eliminate most of the BFS queue prior to each garbage
**     collection round.  The DFS is much faster because of the depth limit
**     and because it terminates early when a path is found exceeding this limit.
**     The iterated deepening part happens by, whenever we do a depth-first round,
**     making the total depth (current level + number of levels of DFS) be one
**     period more than the previous search.  As an example of the improvement due
**     to this change, we can now do the (unsuccessful) B3/S23/O6/L100 in a day
**     (on a 333MHz iMac) while previously the BFS ran out of memory and the DFS
**     ran for a month without completing.  Get rid of taper parameter from 3.2.
**     Apply width reduction based on deepening amount rather than size of queue
**     and change command-line character for reduction limit from percent to minus.
** 4.1, January 2000:
**     Slightly strengthen c/2 double lookahead.  Simplify deepening amount logic.
**     Disable hashing while deepening.  Turn WIDE on by default.
** 4.2, February 2000:
**     Slight cleanup to c/2 lookahead setup. Avoid c/2 setup when too fast for rule.
**     Make deepening compaction handle completely empty queue better.
**     Implement search for glide-reflect orthogonal patterns w/even offset
**     (nice test case: b36s12/n2o5g/l80). Implement forward search for photons.
**     Implement skew gutter mode for HighLife and other rules with B36 (and w/o B4).
**     Jam successor graph construction and reachability; allow early loop termination.
**     Avoid output while deepening if we want to find multiple patterns (/fNN option).
** 4.3, April 2000:
**     Keep track of phase so we can allow gcd(offset,period) > 1.
**     Avoid generating children in last level of deepening recursion.
** 4.4, September 2000:
**     Test period/gcd against input flags rather than true period
**     Fix bug setting nRowsInState when mode==diagMirror
** 4.5, February 2001:
**     Puffer output mode
** 4.6, July 2002:
**     Fix bugs with free() of non-malloced pointer (srows).
** 4.7, August 2002:
**     Implement searches for B0 patterns.
** 4.8, September 2002:
**     Implement trace mode (t parameter).  Disable broken B0 lookahead.
** 4.9, August 2011:
**     Misc fixes from AKT. Also make this work when compiled in 64-bit mode.
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

// AKT: on Mac OS 10.6 or later compile for 32-bit ints:
// cc -o gfind -m32 gfind.c

#define BANNER "gfind 4.9, D. Eppstein, 20 August 2011"
#define WIDE

/* Default values for the most important parameters controlling our search:
   logs (base 2) of how many nodes we can actually visit,
   how many nodes we can store in the hash table
   and how big a graph we will attempt to search */

#ifdef WIDE
#define QBITS 22
#else
#define QBITS 23
#endif

#define HASHBITS 21
#define DEFAULT_DEPTHLIMIT (qBits-3)
#define SEARCHLIMIT 50

/* command-line parameters */
#define P_BIRTHS 0
#define P_SURVIVES 1
#define P_NUMERATORS 2
#define P_ORTHOG 3
#define P_DIAG 4
#define P_MODES 5
#define P_NOBIRTHS 6
#define P_NODEATHS 7
#define PARAM_IS_BITMASK(p) (p <= 7)

#define P_FINDLIMIT 8
#define P_SEARCHLIMIT 9
#define P_BASEBITS 10
#define P_REDLEVEL 11
#define P_QBITS 12
#define P_HASHBITS 13
#define P_REVERSE 14
#define P_DEPTHLIMIT 15
#define P_PUFFER 16
#define P_TRACING 17
#define NUM_PARAMS 18

#define M_ASYM 1
#define M_GLIDE 2
#define M_ODD 4
#define M_EVEN 8
#define M_GUTTER 16

/* globals and typedefs */
int params[NUM_PARAMS];
int width;
int widthReduction;
int deepeningAmount;
int lastdeep;
int nRowsInState;
int phase;

int period;
#define MAXPERIOD 19

/* offsets for different phases */
int fwdOff[MAXPERIOD], backOff[MAXPERIOD], doubleOff[MAXPERIOD], parity[MAXPERIOD];

int offset;
int sdrawkcab = 0;
unsigned long rule;
unsigned long badRuleBits;
enum mode {
	asymmetric,				/* basic orthogonal or diagonal pattern */
	mirror,					/* orthogonal glide reflect, period = 2*speed (e.g. life LWSS) */
	bigMirror,				/* same but with width+1 */
	odd, even,				/* orthogonal with bilateral symmetry */
	gutter,					/* orthogonal bilateral symmetry with empty column in middle */
	diagMirror,				/* diagonal with bilateral symmetry */
	diagGlide,				/* diagonal with glide-reflect symmetry (e.g. life glider) */
	diagGutter,				/* diagonal bilateral sym w/empty middle diagonal */
	skew,						/* orthog w/empty mid col, one side ahead of other (B2 rules) */
	diagSkew					/* diag w/2 empty mid diags, one side ahead of other (B3 w/o B4) */
} mode;

int diagonal;
int aborting;
int nFound;

int perdidor = 0;			/* flag for avoiding output while deepening */

#define findLimit params[P_FINDLIMIT]
#define searchLimit params[P_SEARCHLIMIT]

/* the big data structures */
#define qBits params[P_QBITS]
#define QSIZE (1<<qBits)

#define hashBits params[P_HASHBITS]
#define HASHSIZE (1<<hashBits)
#define HASHMASK (HASHSIZE - 1)

typedef uint32_t node;

#ifdef WIDE
typedef uint32_t row;
#else
typedef uint16_t row;
#endif

row * rows;
node * base;
node * hash;

/*
** Representation of vertices.
**
** Each vertex is represented by an entry in the rows[] array.
** That entry consists of the bits of the last row of the vertex's pattern
** concatenated with a number, the "offset" of the vertex.
** The parent of vertex i is formed by adding the offset of i
** with the number in base[i/BASEFACTOR].
**
** If node i has offset -1, the entry is considered to be empty and is skipped.
** This is to deal with the case that base[i/BASEFACTOR] is already set to
** something too far away to deal with via the offset.
**
** qIsEmpty() checks the size of the queue
** enqueue(n,r) adds a new node with last row r and parent n
** dequeue() returns the index of the next unprocessed node
** pop() undoes the previous enqueue operation
** resetQ() clears the queue
**
** ROW(b) returns the last row of b
** PARENT(b) returns the index of the parent of b
*/

#ifdef WIDE
#define MAXWIDTH (28)
#else
#define MAXWIDTH (14)
#endif

#define ROWBITS ((1<<width)-1)
#define BASEBITS (params[P_BASEBITS])
#define BASEFACTOR (1<<BASEBITS)
#define MAXOFFSET ((((row) -1) >> width) - 1)

#define ROW(i) (rows[i] & ROWBITS)
#define OFFSET(i) (rows[i] >> width)
#define EMPTY(i) (rows[i] == (row)-1)
#define MAKEEMPTY(i) rows[i] = (row)-1
#define PARENT(i) (base[(i)>>BASEBITS]+OFFSET(i))
#define FIRSTBASE(i) (((i) & ((1<<BASEBITS) - 1)) == 0)

/* ====================================================== */
/*  Hash table for detecting equivalent partial patterns  */
/* ====================================================== */

void resetHash() { if (hash != 0) memset(hash,0,4*HASHSIZE); }

int hashPhase = 0;

inline long hashFunction(node b, row r) {
	long h = r;
	int i;
	for (i = 0; i < nRowsInState; i++) {
		h = (h * 269) + ROW(b);
		b = PARENT(b);
	}
	h += (h>>16)*269;
	h += (h>>8)*269;
	return h & HASHMASK;
}

/* test if q+r is same as p */
inline int same(node p, node q, row r) {
	int i;
	for (i = 0; i < nRowsInState; i++) {
		if (p >= QSIZE || q >= QSIZE || EMPTY(p) || EMPTY(q)) return 0;	/* sanity check */
		if (ROW(p) != r) return 0;
		p = PARENT(p);
		r = ROW(q);
		q = PARENT(q);
	}
	return 1;
}

/* test if weve seen this child before */
void success(node);
inline int isVisited(node b, row r) {
	if (same(0,b,r)) {
		if (b != 0 && period == 1) success(b); /* photon never gets to usual terminal call */
		return 1;
	}
	if (hash != 0) {
		int hashVal = hashFunction(b,r);
		node hashNode = hash[hashVal];
		if (hashNode == 0) return 0;
		if (same(hashNode,b,r)) return 1;
	}
	return 0;
}

/* set node (NOT child) to be visited */
inline void setVisited(node b) {
	if (hash != 0) hash[ hashFunction(PARENT(b),ROW(b)) ] = b;
}

/* ============================================================== */
/*  Behave nicely under non-preemptive multitasking (i.e. MacOS)  */
/* ============================================================== */

#ifdef __MWERKS__

#include <Events.h>
#include <SIOUX.h>

long niceTimer = 0;
#define NICE(niceness) if ((niceTimer -= niceness) <= 0) beNice()

/* arguments to NICE - bigger number means call beNice() more often */
#define L2NICENESS 1  /* for searchL2() */
#define GCNICENESS 1  /* for BFS queue compaction */
#define PQNICENESS 8  /* for main processing queue node loop and enqueue() */

/* global timer value - call beNice every (k/niceness) iterations */
#define TOTALNICENESS (1<<16)

void beNice()
{
	EventRecord evRec;
	niceTimer = TOTALNICENESS;
	while (WaitNextEvent(-1, &evRec, 0, 0))
		SIOUXHandleOneEvent(&evRec);
}

#else
#define NICE(niceness)
#endif

/* ================================================ */
/*  Queue of partial patterns still to be examined  */
/* ================================================ */

long qHead,qTail;

/* Maintain phase of queue nodes. After dequeue(), the global variable phase
   gives the phase of the dequeued item.  If the queue is compacted, this information
   needs to be reinitialized by a call to rephase(), after which phase will not be
   valid until the next call to dequeue().  Variable nextRephase points to the next
   node for which dequeue will need to increment the phase. Phase is not maintained
   when treating queue as a stack (using pop()) -- caller must do it in that case.
   It's ok to change phase since we maintain a separate copy in queuePhase. */

int queuePhase = 0;
node nextRephase = 0;
void rephase() {
	node x, y;
	while (qHead < qTail && EMPTY(qHead)) qHead++;	/* skip past empty queue cells */
	x = qHead;	/* find next item in queue */
	queuePhase = 0;
	while (x != 0) {
		x = PARENT(x);
		queuePhase++;
	}
	queuePhase %= period;
	
	/* now walk forward through queue finding breakpoints between each generation
	   invariants: y is always the first in its generation */
	x = 0; y = 0;
	while (y <= qHead) {
		++x;
		if (x >= qTail || !EMPTY(x) && PARENT(x) >= y) y = x;
	}
	nextRephase = y;
}

/* phase of an item on the queue */
int peekPhase(node i) {
	return (i < nextRephase? queuePhase : (queuePhase+1)%period);
}

/* Test queue status */

inline int qIsEmpty() {
	while (qHead < qTail && EMPTY(qHead)) qHead++;
	return (qTail == qHead);
}

void qFull() {
 	if (aborting != 2) {
		printf("Exceeded %d node limit, search aborted\n", QSIZE);
		fflush(stdout);
		aborting = 2;
	}
}

inline void enqueue(node b, row r) {
	int i = qTail++;
	if (i >= QSIZE) qFull();
	else if (FIRSTBASE(i)) {
		base[i>>BASEBITS] = b;
		rows[i] = r;
	} else {
		long o = b - base[i>>BASEBITS];
		if (o < 0 || o > MAXOFFSET) {	/* offset out of range */
			while (!FIRSTBASE(i)) {
				rows[i] = -1;
				i = qTail++;
				if (i >= QSIZE) qFull();
			}
			base[i>>BASEBITS] = b;
			rows[i] = r;
		} else rows[i] = (o << width) + r;
	}
	if (params[P_TRACING])
	    fprintf(stderr, "Create node %d: %lo\n", i, (long unsigned int)r);
}

inline node dequeue() { 
	while (qHead < qTail && EMPTY(qHead)) qHead++;
	if (qHead >= nextRephase) {
		queuePhase = (queuePhase+1)%period;
		if (params[P_TRACING]) fprintf(stderr, "Phase %d\n", queuePhase);
		nextRephase = qTail;
	}
	phase = queuePhase;
	if (params[P_TRACING])
	    fprintf(stderr, "Processing node %ld: %lo\n", qHead,
	        (long unsigned int) (ROW(qHead)));
	return qHead++;
}

inline void pop() {
	qTail--;
	while (qTail > qHead && EMPTY(qTail-1)) qTail--;
}

void resetQ() { qHead = qTail = 0; }

inline int qTop() { return qTail - 1; }


/* ================================= */
/*  Compaction of nearly full queue  */
/* ================================= */

void putnum(long n) {
	char suffix;
	if (n >= 1000000) {
		n /= 100000;
		suffix = 'M';
	} else if (n >= 1000) {
		n /= 100;
		suffix = 'k';
	} else {
		printf("%ld", n);
		return;
	}
	
	if (n >= 100) printf("%ld", n/10);
	else printf("%ld.%ld", n/10, n%10);
	putchar(suffix);
}

long currentDepth() {
	long i;
	node x;
	x = qTail - 1;
	i = 1;
	while (x != 0) {
		x = PARENT(x);
		i++;
	}
	return i;
}

void doCompact()
{
	node x,y;
	node oldTail = qTail;
	
	/* make sure we still have something left in the queue */
	if (qIsEmpty()) {
		qTail = qHead = 0;	/* nothing left, make an extremely compact queue */
		return;
	}

	/* make a pass backwards from the end finding unused nodes at or before qHead */
	x = qTail - 1;
	y = qHead - 1;
	while (y > 0) {
		/* invariants: everything after y is still active.
		   			   everything after x points to something after y.
		   			   x is nonempty and points to y or something before y.
		   			   so, if x doesnt point to y, y must be unused and can be removed. */
		NICE(GCNICENESS);
		if (!EMPTY(y)) {
			if (y > PARENT(x)) rows[y] = -1;
			else while (EMPTY(x) || PARENT(x) == y) x--;
		}
		y--;
	}
	
	/* make a pass forwards converting parent pointers to offset from prev parent ptr.
	   note that after unused nodes are eliminated, all these offsets are zero or one. */
	y = 0;
	for (x = 0; x < qTail; x++) if (!EMPTY(x)) {
		NICE(GCNICENESS);
		if (PARENT(x) == y) rows[x] = ROW(x);
		else {
			y = PARENT(x);
			rows[x] = (1<<width) + ROW(x);
		}
	}
	
	/*
		Make a pass backwards compacting gaps.
	
		For most times we run this, it could be combined with the next phase, but
		every once in a while the process of repacking the remaining items causes them
		to use *MORE* space than they did before they were repacked (because of the need
		to leave empty space when OFFSET gets too big) and without this phase the repacked
		stuff overlaps the not-yet-repacked stuff causing major badness.
		
		For this phase, y points to the current item to be repacked, and x points
		to the next free place to pack an item.
	 */
	x = y = qTail-1;
	for (;;) {
		NICE(GCNICENESS);
		if (qHead == y) qHead = x;
		if (!EMPTY(y)) {
			rows[x] = rows[y];
			x--;
		}
		if (y-- == 0) break;	/* circumlocution for while (y >= 0) because x is unsigned */
	}

	/*
	   Make a pass forwards converting parent bits back to parent pointers.
	   
	   For this phase, x points to the current item to be repacked, and y points
	   to the parent of the previously repacked item.
	   After the previous pass, x is initialized to first nonempty item,
	   and all items after x are nonempty. 
	 */
	qTail = 0; y = 0;
	resetHash();
	for (x++; x < oldTail; x++) {
		NICE(GCNICENESS);
		if (OFFSET(x)) {	/* skip forward to next parent */
			y++;
			while (EMPTY(y)) y++;
		}
		enqueue(y,ROW(x));
		if (aborting) return;
		if (qHead == x) qHead = qTail - 1;
		setVisited(qTail - 1);
	}
	
	rephase();
}

/* ============================================= */
/*  Reversal of rows for glide-reflection modes  */
/* ============================================= */

#ifdef WIDE
#define HALFWIDTH ((MAXWIDTH+1)>>1)
#define MAXMAXWIDTH HALFWIDTH
#define HALFMASK ((1L<<HALFWIDTH)-1)
#define REVERSE(r) ((((reversals[r&HALFMASK])<<HALFWIDTH)|reversals[r>>HALFWIDTH])>>(2*HALFWIDTH-width))

#else
#define MAXMAXWIDTH MAXWIDTH
#define REVERSE(r) (reversals[r]>>(MAXMAXWIDTH-width))
#endif

row reversals[1<<MAXMAXWIDTH];

void makeReversals() {
	row r;
	int i;
	for (r = 0; r < (1<<MAXMAXWIDTH); r++) {
		row rr = 0;
		for (i = 0; i < MAXMAXWIDTH; i++)
			if (r & (1<<i))
				rr |= 1 << (MAXMAXWIDTH - i - 1);
		reversals[r] = rr;
	}
}

/* ============================================== */
/*  Output patterns found by successful searches  */
/* ============================================== */

#define MAXRLELINEWIDTH 63
int RLEcount = 0;
int RLElineWidth = 0;
char RLEchar;

void sendRLE(char c) {
  if (RLEcount > 0 && c != RLEchar) {
  	 if (RLElineWidth++ >= MAXRLELINEWIDTH) {
  	 	if (RLEchar != '\n') putchar('\n');
  	 	RLElineWidth = 0;
  	 }
    if (RLEcount == 1) putchar(RLEchar);
    else {
    	printf("%d%c", RLEcount, RLEchar);
    	RLElineWidth ++;
    	if (RLEcount > 9) RLElineWidth++;
    }
    RLEcount = 0;
    if (RLEchar == '\n') RLElineWidth = 0;
  }
  if (c != '\0') {
    RLEcount++;
    RLEchar = c;
  } else RLElineWidth = 0;
}

int outputParity = 0;

void putRow(row rr, row r, int shift) {
	while (r | rr) {
		if (shift == 0) sendRLE(r & 01? 'o' : 'b');
		else shift--;
		r >>= 1;
		if (rr & 1) r |= (1<<31);
		rr >>= 1;
	}
	sendRLE('$');
}

void printRule() {
  int i;
  printf("B");
  for (i = 0; i < 9; i++) if (rule & (1 << (9+i))) putchar(i+'0');
  printf("/S");
  for (i = 0; i < 9; i++) if (rule & (1 << i)) putchar(i+'0');
}

int modeWidth() {
	switch(mode) {
		case asymmetric:
		case mirror:
		case bigMirror:
			return width;

		case diagMirror:
		case odd:
			return 2*width-1;

		case even:
		case diagGlide:
			return 2*width;

		case gutter:
		case diagGutter:
		case skew:
			return 2*width+1;

		case diagSkew:
			return 2*width+2;
	}
	return 0;
}

void success(node b) {
	node c;
	int nrows = 0;
	int skewAmount = 0;
	int swidth;
	int p, i, j, margin;
	row *srows, *ssrows, *drows, *ddrows;
	static row *oldsrows = 0, *oldssrows = 0;
	static row *olddrows = 0, *oldddrows = 0;
	static int oldnrows = 0;
	
	if (mode == skew) {
		if (rule & 010000) skewAmount = 2;	/* skew gutter w/B3 is shifted by two */
		else skewAmount = 1;						/* but otherwise only by one */
	}
	
	/* check if output disabled while deepening */
	if (perdidor) {
		perdidor = 2;
		return;
	}

	/* shift until we find nonzero row.
	   then shift PERIOD-1 more times to get leading edge of glider */
	while (ROW(b) == 0) {
		b = PARENT(b);
		if (b == 0) {
			printf("Success called on search root!\n");
			aborting = 1;
			return;
		}
	}
	if (mode != diagGlide) for (p = 0; p < period-1; p++) b = PARENT(b);
	if (b == 0) {
		printf("Success called on search root!\n");
		aborting = 1;
		return;
	}

	/* count rows */
	c = b;
	while (c != 0) {
		for (p = 0; p < period; p++)
			c = PARENT(c);
		nrows++;
	}
	
	/* build data structure of rows so we can reduce width etc */
	srows = malloc((nrows+MAXWIDTH+1) * sizeof(unsigned long));
	ssrows = malloc((nrows+MAXWIDTH+1) * sizeof(unsigned long));
	drows = srows; ddrows = ssrows; /* save orig ptr for free() */
	for (i = 0; i <= nrows+MAXWIDTH; i++) srows[i]=ssrows[i]=0;
	for (i = nrows - 1; i >= 0; i--) {
		row r = ROW(b);
		row rx;
		for (p = 0; p < period; p++) {
			if (mode == diagGlide && p == period/2) rx = ROW(b);
			b = PARENT(b);
		}
		switch(mode) {
			case asymmetric:
				srows[i] = r;
				break;

			case mirror:
			case bigMirror:
				if (i & offset & 01) srows[i] = REVERSE(r);
				else srows[i] = r;
				break;
			
			case odd:
				srows[i] = r << (MAXWIDTH - 1);
				ssrows[i] = r >> (32 - (MAXWIDTH - 1));
				for (j = 1; j < MAXWIDTH; j++)
					if (r & (1<<j))
						srows[i] |= 1 << (MAXWIDTH - 1 - j);
				break;
				
			case even:
				srows[i] = r << MAXWIDTH;
				ssrows[i] = r >> (32 - MAXWIDTH);
				for (j = 0; j < MAXWIDTH; j++)
					if (r & (1<<j))
						srows[i] |= 1 << (MAXWIDTH - 1 - j);
				break;
				
			case gutter:
			case skew:
				srows[i] = r << MAXWIDTH + 1;
				ssrows[i] = r >> (32 - (MAXWIDTH + 1));
				for (j = 0; j < MAXWIDTH; j++)
					if (r & (1<<j))
						srows[i+skewAmount] |= 1 << (MAXWIDTH - 1 - j);
				break;
			
			case diagMirror:
				srows[i] = r << (MAXWIDTH - 1);
				ssrows[i] = r >> (32 - (MAXWIDTH - 1));
				for (j = 1; j < MAXWIDTH; j++)
					if (r & (1<<j))
						srows[i+j] |= 1 << (MAXWIDTH - 1 - j);
				break;
			
			case diagGutter:
				srows[i] = r << (MAXWIDTH + 1);
				ssrows[i] = r >> (32 - (MAXWIDTH + 1));
				for (j = 0; j < MAXWIDTH; j++)
					if (r & (1<<j))
						srows[i+j+1] |= 1 << (MAXWIDTH - 1 - j);
				break;

			case diagSkew:
				srows[i] = r << (MAXWIDTH + 2);
				ssrows[i] = r >> (32 - (MAXWIDTH + 2));
				for (j = 0; j < MAXWIDTH; j++)
					if (r & (1<<j))
						srows[i+j+1] |= 1 << (MAXWIDTH - 1 - j);
				break;
				
			case diagGlide:
				srows[i] = r << MAXWIDTH;
				ssrows[i] = r >> (32 - MAXWIDTH);
				for (j = 0; j < MAXWIDTH; j++)
					if (rx & (1 << j))
						srows[i+j] |= 1 << (MAXWIDTH - 1 - j);
				break;
			
			default:
				printf("Unexpected mode in success!\n");
				aborting = 1;
				return;
		}
	}
	
	/* normalize nrows to only include blank rows */
	nrows += MAXWIDTH;
	while (srows[nrows-1] == 0 && ssrows[nrows-1] == 0 && nrows>0) nrows--;
	while (srows[0] == 0 && ssrows[0] == 0 && nrows>0) {
		srows++;
		ssrows++;
		nrows--;
	}
	
	/* make at least one row have nonzero first bit */
	i = 0;
	while ((srows[i] & 1) == 0) {
		for (i = 0; (srows[i] & 1) == 0 && i < nrows; i++) { } 
		if (i == nrows) {
			for (i = 0; i < nrows; i++) {
				srows[i] >>= 1;
				if (ssrows[i] & 1) srows[i] |= (1<<31);
				ssrows[i] >>= 1;
			}
			i = 0;
		}
	}
	
	/* compute width */
	/* note for diag, even if ssrows!=0, max may occur in srows! so always do both loops */
	swidth = 0;
	for (i = 0; i < nrows; i++)
		while (ssrows[i] >> (swidth - diagonal*i))
			swidth++;
	if (swidth) swidth += 32;
	for (i = 0; i < nrows; i++)
		while (srows[i] >> (swidth - diagonal*i))
			swidth++;

	/* compute margin on other side of width */
	if (diagonal) {
		margin = 2*MAXWIDTH;
		if (margin >= 32) margin = 31;
		for (i = 0; i < nrows; i++)
			while (margin > i && (srows[i] & ((1 << (margin - i))-1)))
				margin--;
	} else margin = 0;
	
	/* make sure we didn't just output the exact same pattern (happens a lot for puffer) */
	if (nrows == oldnrows) {
		int different = 0;
		for (i = 0; i < nrows && !different; i++)
			different = (srows[i] != oldsrows[i] || ssrows[i] != oldssrows[i]);
		if (!different) {
			free(drows);
			free(ddrows);
			return;
		}
	}
	if (olddrows != 0) free(olddrows);
	if (oldddrows != 0) free(oldddrows);
	oldsrows = srows;
	oldssrows = ssrows;
	olddrows = drows;
	oldddrows = ddrows;
	oldnrows = nrows;
	
	/* output it all */
	printf("\nx = %d, y = %d, rule = ", swidth - margin, nrows);
	printRule();
	putchar('\n');
	
	while (nrows-- > 0) {
		if (diagonal) {
			int i;
			for (i = 0; i < nrows - margin; i++) sendRLE('b');
		}
		if (margin > nrows) putRow(ssrows[nrows], srows[nrows], margin - nrows);
		else putRow(ssrows[nrows], srows[nrows], 0);
	}
	RLEchar = '!';
	sendRLE('\0');
	printf("\n\n");
	fflush(stdout);
	if (++nFound >= findLimit) aborting = 1;
}

/* Is this a node at which we can stop? */

int oddMirrorUnterm[1<<4];
void makeUnterm() {
	int i;
	for (i = 0; i < (1<<4); i++) {
		if (rule & (1 << (9 + (i & 3) + ((i&4)>>1)))) oddMirrorUnterm[i] = 1;
		else if (rule & (1 << (9 + ((i&2)>>1) + ((i&4)>>2) + ((i&010)>>3))))
			oddMirrorUnterm[i] = 1;
		else oddMirrorUnterm[i] = 0;
	}
}

int terminal(node n)
{
	int p;
	int extra = (sdrawkcab? offset : 0);	/* addl rows need to be zero in reverse search */

	if (params[P_BIRTHS] & 1) {	/* B0 rules require special terminal test */
		row blank1 = 0;
		row blank2 = (1<<width)-1;
		for (p = 0; p < 2*period; p++) {	/* check for quiescent alternation */
			if (ROW(n) != blank1 && ROW(n) != blank2) return 0;
			n = PARENT(n);
		}
		while (1) {	/* check for nontrivial content */
			if (PARENT(n) == n) return 0;
			if (ROW(n) != blank1 && ROW(n) != blank2) return 1;
			n = PARENT(n);
		}
	}

	if (params[P_PUFFER]) {
		int nonempty = 0;
		if (ROW(n) != 0) return 0;
		for (p = 0; p < period; p++) {
			n = PARENT(n);
			if ((ROW(n) & 3) == 3 ||
				 (ROW(n) & (ROW(n)>>1) & (ROW(n)>>2)) != 0) nonempty = 1;
		}
		if (!nonempty || ROW(n) != 0) return 0;
		for (p = 0; p < 2*period; p++) n = PARENT(n);
		if (n == 0) return 0;   /* too close to root */
		return 1;
	}

	for (p = 0; p < period + extra; p++) {	/* last row in each phase must be zero */
		if (ROW(n) != 0) return 0;
		n = PARENT(n);
	}
	for (p = 0; p < period - extra; p++) {	/* 2nd last row must not cause any births */
		row r = ROW(n);
		if (mode == diagMirror) {
			if (oddMirrorUnterm[r&017]) return 0;
			r &=~ 3;		/* remaining code only safe far enough away from corner */
		} else if (mode == diagGlide && p < (period>>1) && r != 0) return 0;
		else if (mode == diagGutter && (rule & 020000) != 0 && (r & 3) == 3) return 0;
		else if (diagonal == 0 && (mode == odd || mode == even)) {
			if ((rule & (1 << (2 + 9))) == 0) {
				if ((r & 03) == 03) return 0;
			} else if (mode == odd) {
				if ((r & 03) == 02) return 0;
			} else
				if ((r & 03) == 01) return 0;
		}
		if ((rule & (1 << (2 + 9))) == 0)
			r &= (r>>1) & (r>>2);	/* rule w/b3 get tripled live cells */
		else r &= (r>>1) | (r>>2); /* w/b2 get paired cells (and some triples but thats ok */
		if (r != 0) return 0;
		n = PARENT(n);
	}
	return 1;
}

/* ========================================================== */
/*  Preprocess tables needed for successor graph computation  */
/* ========================================================== */
   
unsigned short edge00[MAXWIDTH], edge01[MAXWIDTH], edge10[MAXWIDTH], edge11[MAXWIDTH];

/* main edge sets */
#define ETABL ((1<<13)+(1<<10)+(1<<6))
#define SDRAWKCAB (1<<13)
#define PHOTON ((1<<13)+(1<<10))
unsigned short e00tab[ETABL],e01tab[ETABL],e10tab[ETABL],e11tab[ETABL];
int ruleTab[1<<9];


#define ETABXF(a,b,c,d,e) ((a&7) | ((b&7)<<3) | ((c&7)<<6) | ((d&7)<<9) | ((e&2)<<11))
#define ETABXR(a,b,c,d) (SDRAWKCAB + (((a&2)<<6) | ((b&2)<<5) | ((c&7)<<3) | (d&7)))
#define ETABXP(c,d) (PHOTON + ((c&7)<<3) + (d&7))
#define ETABX(a,b,c,d,e) (sdrawkcab? ETABXR(a,b,c,d):(period==1? ETABXP(c,d):ETABXF(a,b,c,d,e)))

/* double-period lookahead filter */
#define LTABL (1<<13)
unsigned short l00tab[LTABL],l01tab[LTABL],l10tab[LTABL],l11tab[LTABL];
#define LTABX(b,f,g) (((b&7)<<10) | ((f&037)<<5) | (g&037))

/* NONrecursive reversed search for blocks usable for forward c/2 search.
   My mac blows up if I try to do a recursive depth first search - stack too deep.
   Format for block index is fffffgggggyyyyyxxxxx where each block has a successor
   eeeeefffffgggggyyyyy whenever rows egx can evolve to form y. */

#define LTAB2L (1<<10)
unsigned short l00tab2[LTAB2L],l01tab2[LTAB2L],l10tab2[LTAB2L],l11tab2[LTAB2L];
#define LTAB2X(f,g) (((f&037)<<5) | (g&037))

#define L2BIT(i) ((long *)rows)[i]
#define L2E(i,j) ((i>>5) | (j<<15))

unsigned long l2t[1<<15];

void searchL2() {
	long q = 0;		/* initialize stack top pointer */
	long i,j,e,g;
	for (i = 0; i < (1<<20); i++) L2BIT(i) = 0;	/* mark all nodes unvisited */
	
	/* build table of successors for each gggggyyyyyxxxxx */
	for (i = 0; i < (1<<15); i++) l2t[i] = 0;
	for (e = 0; e < (1<<7); e++)
		for (g = 0; g < (1<<7); g++)
			for (i = 0; i < (1<<5); i++) {
				int x = (i<<1) | (g & 0101);	/* copy bits from g so only 4 poss. for outer 3 bits */
				int y = 0;
				for (j = 0; j < 5; j++)			/* try setting each bit in y */
					y |= ruleTab[(((e>>j)&7)<<6) | (((g>>j)&7)<<3) | ((x>>j)&7)] << j;
				if (y >= 0) l2t[((g & 076) << 9) | (y<<5) | i] |= (1 << ((e & 076) >> 1));
				NICE(L2NICENESS);
			}

	L2BIT(q) = -1;	/* except first one, which gets flag to mark stack bottom */
	for (;;) {		/* while stack nonempty */
		unsigned long sux;
		i = q;		/* pop next node to be processed into i */
		q = L2BIT(q);
		if (i == -1) return;
		sux = l2t[i & 077777];
		for (j = 0; j < (1<<5); j++) if (sux & (1<<j)) { /* for each successor of i */
			node k = L2E(i,j);
			if (!L2BIT(k)) {
				L2BIT(k) = q;	/* found another reachable node, push onto stack */
				q = k;
			}
			NICE(L2NICENESS);
		}
	}
}

/* left and right shift operators on bitmasks representing sets of 2x2 cell blocks.
   The "col" arg should be in range 0-3 and represents the cells being shifted in/out */

#define FROM4X(x,col) (((x) & (1<<col) ? 010421 : 0) | \
	((x) & (020<<col) ? 010421<<1 : 0) | \
	((x) & (0400<<col) ? 010421<<2 : 0) | \
	((x) & (010000<<col) ? 010421<<3 : 0))

/*
The following mysterious equivalent line is about 10% faster overall on my G3:
#define FROM4X(x,col) (((((((x)>>col)&010421)*01111)>>9)&0xf)*010421)
*/

#define TO4X(x,col) (((x) & 010421 ? 1<<col : 0) | \
	((x) & (010421<<1) ? 020<<col : 0) | \
	((x) & (010421<<2) ? 0400<<col : 0) | \
	((x) & (010421<<3) ? 010000<<col : 0))


/* auxiliary arrays used in successor computation */

/* it turns out to save 10% total time to look these values up in an array.
   This came as a surprise to me; I thought they would blow out the cache... */
unsigned short to4x[1<<16];
unsigned short from4x[1<<16];

void set4x() {
	int i;
	for (i = 0; i < (1<<16); i++) {
		to4x[i] = TO4X(i,0);
		from4x[i] = FROM4X(i,0);
	}
	
	/* make table for looking up result of CA rule on 3x3 block of bits */
	for (i = 0; i < (1<<9); i++) {
		int n = (i & 1) + ((i>>1) & 1) + ((i>>2) & 1) +
				  ((i>>3) & 1) + ((i>>5) & 1) +
				  ((i>>6) & 1) + ((i>>7) & 1) + ((i>>8) & 1);
		if (((i>>4)&1) == 0) n += 9;	/* if (birth) use bit 9+nbrs instead of bit nbrs */
		if (badRuleBits & (1<<n)) ruleTab[i] = -1;	/* flag unusable combo */
		else ruleTab[i] = ((rule & (1<<n))? 1 : 0);
	}
	
	/* make bigger table of what edge should look like for each value of ETABXF
		Format for bits in i: cccdddyyyaaabbbxxx
		Where y is row being added, cdy generate row e
		And x is supposed extension row such that abx generate row y */

	for (i = 0; i < ETABL; i++) e00tab[i] = e01tab[i] = e10tab[i] = e11tab[i] = 0;
	for (i = 0; i < (1<<18); i++) {
		if (ruleTab[i & 0777] == ((i>>10) & 1) && ruleTab[i>>9] >= 0) {
			int idx = ETABXF((i>>6)&7, (i>>3)&7, (i>>15)&7, (i>>12)&7, ruleTab[i>>9]<<1);
			int bit = ((i&04000)>>8) | (i&4) | ((i&02000)>>9) | ((i&2)>>1);
			bit = 1<<bit;
			if (!(i&01000) && !(i&1)) e00tab[idx] |= bit;
			else if (!(i&01000) && (i&1)) e01tab[idx] |= bit;
			else if ((i&01000) && !(i&1)) e10tab[idx] |= bit;
			else e11tab[idx] |= bit;
		}
	}
	
	/* ditto ETABXP. Format for bits in i: cccdddyyyxxx, where cdy->y, dyx->x */
	for (i = 0; i < (1<<12); i++) {
		if (ruleTab[i>>3] == ((i>>4)&1) && ruleTab[i&0777] == ((i>>1)&1)) {
			int idx = PHOTON + (i>>6);
			int bit = ((i&040)>>2) | (i&4) | ((i&020)>>3) | ((i&2)>>1);
			bit = 1<<bit;
			if (!(i&010) && !(i&1)) e00tab[idx] |= bit;
			else if (!(i&010) && (i&1)) e01tab[idx] |= bit;
			else if ((i&010) && !(i&1)) e10tab[idx] |= bit;
			else e11tab[idx] |= bit;
		}
	}
	
	/* ditto ETABXR. Format for bits in i: cccdddyyyxxx, where cdy->a, dyx->b */
	for (i = 0; i < (1<<12); i++) {
		int a = ruleTab[i>>3];
		int b = ruleTab[i & 0777];
		if (a >= 0 && b >= 0) {
			int idx = SDRAWKCAB + ((a<<7) | (b<<6) | (i>>6));
			int bit = ((i&040)>>2) | (i&4) | ((i&020)>>3) | ((i&2)>>1);
			bit = 1<<bit;
			if (!(i&010) && !(i&1)) e00tab[idx] |= bit;
			else if (!(i&010) && (i&1)) e01tab[idx] |= bit;
			else if ((i&010) && !(i&1)) e10tab[idx] |= bit;
			else e11tab[idx] |= bit;
		}
	}
	
	/* init general-purpose 2*period lookahead edge filter tables */
	for (i = 0; i < LTABL; i++) l00tab[i] = l01tab[i] = l10tab[i] = l11tab[i] = 0;
	for (i = 0; i < (1<<16); i++) {
		/* 
		   i represents three bits of x (the lookahead row found simultaneously
		   with the row y being added to the current pattern), three bits of b
		   (the last row in the current pattern with the same phase as x),
		   and five consecutive bits of f and g (two rows in the current pattern
		   one phase prior to x). We wish to know whether there exist two rows
		   u and v such that vgf generate b and uvg generate x; if so, we set
		   the appropriate bits in the lookahead filter table (lxxtab) so that
		   we can use the de Bruijn graph edges involving the three bits of x.
		   To test for the existence of u and v, we do a (short) de Bruijn
		   graph calculation with the ETABXR tables that we just built above
		   and that are also used in the main search in rear-to-front mode.
		*/
		   
		unsigned short r = -1;
		int idx;
		idx = ETABXR(i>>9, i>>12, i>>5, i);
		r = (from4x[r] & e00tab[idx]) | (from4x[r>>1] & e01tab[idx]) |
			(from4x[r>>2] & e10tab[idx]) | (from4x[r>>3] & e11tab[idx]);
		idx = ETABXR(i>>10, i>>13, i>>6, i>>1);
		r = (from4x[r] & e00tab[idx]) | (from4x[r>>1] & e01tab[idx]) |
			(from4x[r>>2] & e10tab[idx]) | (from4x[r>>3] & e11tab[idx]);
		idx = ETABXR(i>>11, i>>14, i>>7, i>>2);
		r = (from4x[r] & e00tab[idx]) | (from4x[r>>1] & e01tab[idx]) |
			(from4x[r>>2] & e10tab[idx]) | (from4x[r>>3] & e11tab[idx]);
		if (r) { /* r is nonzero here iff u and v exist */
			int bit = ((i & 0100000)>>13) | ((i & 040000) >> 14);
			bit = (1<<bit) | (1<<(bit+2)) | (1<<(bit+8)) | (1<<(bit+10));
			idx = (i & 017777);
			if (i & 020000) {
				l01tab[idx] |= bit;
				l11tab[idx] |= bit;
			} else {
				l00tab[idx] |= bit;
				l10tab[idx] |= bit;
			}
		}
	}
	
	/* init special c/2 orthogonal infinite lookahead using rows[] as scratch */
	if ((params[P_ORTHOG] & 4) != 0 && (params[P_NUMERATORS] & 2) != 0 &&
		(params[P_BIRTHS] & 1) == 0 &&
		params[P_MODES] != M_GLIDE && (rule & ~badRuleBits & 02036) != 0)
	{
		if (QSIZE*sizeof(row) < (1<<22)) {	/* can we store all 2^20 longs? */
			for (i = 0; i < LTAB2L; i++)	/* no, disable look2 */
				l00tab2[i] = l01tab2[i] = l10tab2[i] = l11tab2[i] = -1;
		} else {
			int n = 0;
			printf("Constructing c/2 edge filters...");
			fflush(stdout);
			searchL2();						/* do mainwork of reverse search */
			for (i = 0; i < (1<<20); i++) if (L2BIT(i))
			{								/* compress results into filter */
				int idx = i >> 10;
				int bit = ((i&0400)>>5) | ((i&010)>>1) | ((i&0200)>>6) | (i&4)>>2;
				bit = 1<<bit;
				if (!(i&0100) && !(i&2)) l00tab2[idx] |= bit;
				else if (!(i&0100) && (i&2)) l01tab2[idx] |= bit;
				else if ((i&0100) && !(i&2)) l10tab2[idx] |= bit;
				else l11tab2[idx] |= bit;
				NICE(L2NICENESS);
			}
			for (i = 0; i < LTAB2L; i++) {	/* find stats on filter size */
				int j;
				for (j = 0; j < 16; j++) {
					if ((l00tab2[i] & (1<<j)) == 0) n++;
					if ((l01tab2[i] & (1<<j)) == 0) n++;
					if ((l10tab2[i] & (1<<j)) == 0) n++;
					if ((l11tab2[i] & (1<<j)) == 0) n++;
				}
			}
			printf(" found %d/%d patterns\n",n,LTAB2L*64);
		}
	}
}

void makePhases() {
	int i;
	for (i = 0; i < period; i++) backOff[i] = -1;
	i = 0;
	parity[i] = 0;
	if (offset == period) backOff[0] = 1; /* multiperiod photon not yet working */
	else for (;;) {
		int j = offset;
		while (backOff[(i+j)%period] >= 0 && j < period) j++;
		if (j == period) {
			backOff[i] = period-i;
			break;
		}
		backOff[i] = j;
		j = (i+j)%period;
		parity[j] = !parity[i];
		i = j;
	}
	for (i = 0; i < period; i++)
		fwdOff[(i+backOff[i])%period] = backOff[i];
	for (i = 0; i < period; i++) {
		int j = (i - fwdOff[i]);
		if (j < 0) j += period;
		doubleOff[i] = fwdOff[i] + fwdOff[j];
	}
}


/* ========================================================================== */
/*  Find successors of current node by representing them as paths in a graph  */
/* ========================================================================== */

/* Recursively search backwards thru successor graph for rows that match paths
   in the graph.  theNode is the search node we're looking for successors of;
   theRow is the set of cells we've found so far in the recursive search;
   remainingWidth counts how many more cells we need to add to theRow; and
   vertexSet gives the set of successor graph vertices in the current column
   that can reach the final vertices by a path matching theRow. */

void findPaths(node theNode, row theRow, int vertexSet, int remainingWidth)
{
	int previousColumn;

	/* if path reached all the way through, make and test new node */
	if (--remainingWidth < 0) {
		if (!isVisited(theNode, theRow)) {
			enqueue(theNode, theRow);
			if (aborting) return;
			NICE(PQNICENESS);
			if (terminal(qTail-1)) {
				success(qTail-1);
				if (params[P_PUFFER]) pop();
				else setVisited(qTail - 1);
			} else setVisited(qTail - 1);
		} else if (params[P_TRACING])
		    fprintf(stderr, "Duplicate node: %lo\n",
		        (long unsigned int) theRow);
		return;
	}
	
	/* try concatenating a zero to r */
	previousColumn = to4x[edge00[remainingWidth] & vertexSet] |
		 				  (to4x[edge01[remainingWidth] & vertexSet] << 1);
	if (previousColumn) findPaths(theNode, theRow<<1, previousColumn, remainingWidth);
		
	/* try concatenating a one to r */
	if (mode != bigMirror || remainingWidth < width-1) {
		previousColumn = (to4x[edge10[remainingWidth] & vertexSet] << 2) |
							  (to4x[edge11[remainingWidth] & vertexSet] << 3);
		if (previousColumn) findPaths(theNode, (theRow<<1)+1, previousColumn, remainingWidth);
	}
}

/* initialize successor graph and find bitmasks of reachable vertices
   factored out from process() so we can call it from depth=1 in deepening phase
   without actually generating all children */

int reachable(node x) {
	row a,b,c,d,e,f,g,aa;
	int ph,i,p2;
	row rr[MAXPERIOD<<2];
	node theNode = x;
	
	int look2 = (!diagonal && period==2 && (params[P_BIRTHS] & 1) == 0 &&
				 mode != mirror && mode != bigMirror && !sdrawkcab);
	int looking = (!sdrawkcab && (offset+offset < period || look2) && (params[P_BIRTHS] & 1) == 0);
	
	unsigned short vertexSet = 1;		 /* start vertex represents 0000 2x2 block of cells */
	unsigned short finalVertices = 1;	 /* end vertex ditto */
	if (diagonal) finalVertices = 3;	 /* but diag allow one live cell at end of extension */
	if ((params[P_BIRTHS] & 1) != 0)
		vertexSet = finalVertices = 1 << (5 << !parity[phase]);

	NICE(PQNICENESS);

	for (ph = 1; ph <= nRowsInState; ph++) {	/* base of phase = 0 = row to be added */
		rr[ph] = ROW(x);
		x = PARENT(x);
	}

	a = rr[period + fwdOff[phase]];
	b = rr[fwdOff[phase]];
	c = rr[2*period];
	d = rr[period];
	e = rr[period - backOff[phase]];
	if ((params[P_BIRTHS] & 1) != 0) {
		/* in B0 rules, complement appropriate high order bits of rows */
		if (!parity[phase]) {
			c ^= -1 << width;
			d ^= -1 << width;
		} else {
			a ^= -1 << width;
			b ^= -1 << width;
			e ^= -1 << width;
		}
	}
	if (mode == mirror || mode == bigMirror) {
		if (offset & 01) {
			a = REVERSE(a);
			d = REVERSE(d);
			e = REVERSE(e);
		} else {
			a = REVERSE(a);
			b = REVERSE(b);
			e = REVERSE(e);
		}
	}
	a <<= (2-diagonal);
	b <<= 2;
	c <<= 2 - 2*diagonal;
	d <<= (2-diagonal);
	e <<= (2-diagonal);
	if ((params[P_BIRTHS] & 1) != 0 && (mode == asymmetric || mode == mirror || mode == bigMirror)) {
		/* in B0 rules, complement appropriate low order bits of rows */
		if (!parity[phase]) {
			c ^= (1 << (2 - 2*diagonal)) - 1;
			d ^= (1 << (2 - diagonal)) - 1;
		} else {
			a ^= (1 << (2 - diagonal)) - 1;
			b ^= (1 << 2) - 1;
			e ^= (1 << (2 - diagonal)) - 1;
		}
	}
	
	/* set up extra lookahead info (also modified later in first switch(mode)) */
	if (looking) {
		if (look2) {
			g = rr[1]<<1;
			f = rr[2]<<1;
		} else {
			f = rr[period+doubleOff[phase]];
			if ((mode == mirror || mode == bigMirror) && (offset & 01)) f = REVERSE(f);
			f <<= (1-diagonal);
			g = rr[doubleOff[phase]] << 1;
		}
	}
	
	/* find start vertices for graph reachability, part 1:
	   determine vertices matching boundary conditions from symmetry type
	   and not causing the pattern to grow beyond its set width */ 

	switch(mode) {
		case skew:
			if (rule & 010000) {	/* B3 double-row skew */
				a |= rr[3*period+fwdOff[phase]] & 1;
				b |= rr[2*period+fwdOff[phase]] & 1;
				c |= rr[4*period] & 1;
				d |= rr[3*period] & 1;
				vertexSet = (c & 4? 014: 3);
			} else {					/* B2 single-row skew */
				a |= rr[2*period+fwdOff[phase]] & 1;
				b |= (a & 4) >> 2;
				c |= rr[3*period] & 1;
				d |= (c & 4) >> 2;
				vertexSet = (d & 4? 014: 3);
			}
			i = ETABX(a,b,c,d,e);
			vertexSet =
				(from4x[vertexSet] & e00tab[i]) |
				(from4x[vertexSet>>1] & e01tab[i]) |
				(from4x[vertexSet>>2] & e10tab[i]) |
				(from4x[vertexSet>>3] & e11tab[i]);
			break;

		case gutter:
			vertexSet = 010421;	/* 010421=from4x[01] */
			break;

		case even:
			vertexSet = 0102041; /* 0102041=vertices w/repeated bits */
			a |= ((a>>1)&2);				/* repeat bits on other rows too */
			b |= ((b>>1)&2);
			c |= ((c>>1)&2);
			d |= ((d>>1)&2);
			e |= ((e>>1)&2);
			f |= (f&2)>>1;
			g |= (g&2)>>1;
			break;

		case odd:
			a |= ((a>>2)&2);				/* repeat bits on other rows */
			b |= ((b>>2)&2);
			c |= ((c>>2)&2);
			d |= ((d>>2)&2);
			e |= ((e>>2)&2);
			f |= (f&4)>>2;
			g |= (g&4)>>2;
			break;

		case diagSkew:
			vertexSet = 2;
		case asymmetric:
		case mirror:
		case bigMirror:
			i = ETABX(a,b,c,d,e);
			vertexSet =
				(from4x[vertexSet] & e00tab[i]) |
				(from4x[vertexSet>>1] & e01tab[i]) |
				(from4x[vertexSet>>2] & e10tab[i]) |
				(from4x[vertexSet>>3] & e11tab[i]);

			if (diagonal) vertexSet &= 07417;
				/* force second bit of extension row to be zero */
			break;

		case diagMirror:
			aa = rr[2*period + fwdOff[phase]];	/* need aa to be something consistent */
			a |= (aa & 2) >> 1;
			b |= (aa & 4) >> 2;
			if (aa & 010) vertexSet <<= 1;	/* set first bit of extension */
			b |= (a & 4) >> 1;
			if (a & 010) vertexSet <<= 4;	/* set second bit of extension */
			d |= (c & 2) >> 1;
			if (c & 4) vertexSet <<= 2;	/* set first... */
			if (d & 4) vertexSet <<= 8;	/* and second bit of main row */
			g |= (f&2)>>1;
			i = ETABX(a,b,c,d,e);

			vertexSet =
				(from4x[vertexSet] & e00tab[i]) |
				(from4x[vertexSet>>1] & e01tab[i]) |
				(from4x[vertexSet>>2] & e10tab[i]) |
				(from4x[vertexSet>>3] & e11tab[i]);

			/* force second bit of extension to match b */		
			if (b & 010) vertexSet &= 0170360;	
			else vertexSet &= 07417;
			break;

		case diagGutter:
			b |= (a & 2) >> 1;
			if (a & 4) vertexSet <<= 1;	/* set first bit of extension */
			if (b & 4) vertexSet <<= 4;	/* set second bit of extension */
			if (d & 2) vertexSet <<= 2;	/* set first bit of main row */
			i = ETABX(a,b,c,d,e);
			vertexSet =
				(from4x[vertexSet] & e00tab[i]) |
				(from4x[vertexSet>>1] & e01tab[i]) |
				(from4x[vertexSet>>2] & e10tab[i]) |
				(from4x[vertexSet>>3] & e11tab[i]);

			vertexSet &= 07417; /* force second bit of ext to zero */		
			break;
			
		case diagGlide:
			p2 = period>>1;
			d |= rr[period+p2]&1;
			if (rr[period+p2]&2) vertexSet <<= 2;
			if (rr[p2]&1) vertexSet <<= 8;
			a |= rr[period+p2+fwdOff[phase]]&1;
			b |= (rr[period+p2+fwdOff[phase]]&2)>>1;
			if (rr[period+p2+fwdOff[phase]]&4) vertexSet <<= 1;
			b |= (rr[p2+fwdOff[phase]]&1)<<1;
			if (rr[p2+fwdOff[phase]]&2) vertexSet <<= 4;
			g |= rr[doubleOff[phase]+(period>>1)]&1;
			i = ETABX(a,b,c,d,e);
			vertexSet =
				(from4x[vertexSet] & e00tab[i]) |
				(from4x[vertexSet>>1] & e01tab[i]) |
				(from4x[vertexSet>>2] & e10tab[i]) |
				(from4x[vertexSet>>3] & e11tab[i]);
			break;

		default:
			printf("initSuccessorGraph: unimplemented mode\n");
			return 0;
	}


	/* find start vertices for graph reachability, part 2:
	   match evolution rule for outside row of pattern */ 

	a >>= 1;
	b >>= 1;
	c >>= 1;
	d >>= 1;
	e >>= 1;
	i = ETABX(a,b,c,d,e);
	if (mode == odd)
		vertexSet =
			(017 & e00tab[i]) |			/* match outgoing and incoming bits */
			(0360 & e01tab[i]) |
			(07400 & e10tab[i]) |
			(0170000 & e11tab[i]);
	else
		vertexSet =
			(from4x[vertexSet] & e00tab[i]) |
			(from4x[vertexSet>>1] & e01tab[i]) |
			(from4x[vertexSet>>2] & e10tab[i]) |
			(from4x[vertexSet>>3] & e11tab[i]);


	/* main loop forward through columns of graph setting edges between each column */
	for (ph = 0; ph < width; ph++) {
		a >>= 1;
		b >>= 1;
		c >>= 1;
		d >>= 1;
		e >>= 1;
		i = ETABX(a,b,c,d,e);

		edge00[ph] = from4x[vertexSet] & e00tab[i];
		edge01[ph] = from4x[vertexSet >> 1] & e01tab[i];
		edge10[ph] = from4x[vertexSet >> 2] & e10tab[i];
		edge11[ph] = from4x[vertexSet >> 3] & e11tab[i];
		
		/* filter edges according to double-period lookahead tables */
		if (looking) {
			if (look2) {
				i = LTAB2X(f,g);
				edge00[ph] &= l00tab2[i];
				edge01[ph] &= l01tab2[i];
				edge10[ph] &= l10tab2[i];
				edge11[ph] &= l11tab2[i];
			} else {
				i = LTABX(b,f,g);
				edge00[ph] &= l00tab[i];
				edge01[ph] &= l01tab[i];
				edge10[ph] &= l10tab[i];
				edge11[ph] &= l11tab[i];
			}
			f >>= 1;
			g >>= 1;
		}
		
		/* use newly found edges to test which vertices in next col are reachable from start */
		vertexSet = edge00[ph] | edge01[ph] | edge10[ph] | edge11[ph];
			
		/* apply width reduction */
		if (widthReduction && ph >= width - widthReduction - 1) {
			vertexSet &= finalVertices;
			finalVertices = 1;
		}
		
		/* test for early termination */
		if (vertexSet == 0) break;
	}
	
	finalVertices &= vertexSet;

	return finalVertices;
}

void process(node theNode)
{
	int finalVertices = reachable(theNode);
	if (finalVertices) findPaths(theNode,0,finalVertices,width);
}

/* ======================================================================= */
/*  Depth first iterated deepening from active nodes in current BFS queue  */
/* ======================================================================= */

/* search given node to given test depth, return true if found any long lines */

static int depthFirst(node theNode, long howDeep)
{
	long oldQ = qTail;
	int oldPhase = phase;

	if (howDeep <= 1) return reachable(theNode);	/* current node is past search depth limit */
	howDeep--;

	process(theNode);					/* find children */
	if (perdidor > 1) {				/* one would have been successful? */
		perdidor = 1;
		qTail = oldQ;
		return 1;
	}
	phase++;
	if (phase == period) phase = 0;
	while (qTail > oldQ) {			/* and process each one */
		if (depthFirst(qTail - 1, howDeep)) {
			qTail = oldQ;
			phase = oldPhase;
			return 1;
		}
		if (aborting) {
			qTail = oldQ;
			phase = oldPhase;
			return 0;
		}
		pop();
	}
	phase = oldPhase;
	return 0;
}

/* Here with too much stuff in the queue, run a pass of depth-first */
static void deepen()
{
	node i;
	node * savedHash = hash;

	hash = 0;	/* disable hash while deepening */
	if (findLimit > 1) perdidor = 1;	/* also disable success if want mult pattern output */
	
	/* compute amount to deepen, apply reduction if too deep */
	printf("Queue full");
	i = currentDepth();
	if (i >= lastdeep) deepeningAmount = period;
	else deepeningAmount = lastdeep + period - i;	/* go at least one period deeper */

	if (params[P_REDLEVEL] > 0 && deepeningAmount >= params[P_REDLEVEL]) {
		printf(", shrinking");
		widthReduction++;
		deepeningAmount = period;
	}
	lastdeep = i + deepeningAmount;

	/* start report of what's happening */
	printf(", depth %ld, deepening %d, ", (long int) i, deepeningAmount);
	putnum(qTail - qHead);
	printf("/");
	putnum(qTail);
	fflush(stdout);
	
	/* go through queue, deepening each one */
	for (i = qHead; i < qTail; i++) {
		phase = peekPhase(i);
		if (!EMPTY(i) && !depthFirst(i, deepeningAmount))
			MAKEEMPTY(i);
		if (aborting) return;
	}
	if (deepeningAmount > period) deepeningAmount--; /* allow for gradual depth reduction */

	/* before reporting new queue size, shrink tree back down */
	printf(" -> ");
	fflush(stdout);
	hash = savedHash;
	perdidor = 0;
	doCompact();
	
	/* now finish report */
	putnum(qTail - qHead);
	printf("/");
	putnum(qTail);
	printf("\n");
	fflush(stdout);
}

/* ======================================================================= */
/*  Main breadth first search through nodes representing partial patterns  */
/* ======================================================================= */


int gcd(int a, int b) {
	if (a > b) return gcd(b,a);
	else if (a == 0) return b;
	else return gcd(b-a,a);
}

int anythingSearched = 0;

static void breadthfirst()
{
	while (!aborting && !qIsEmpty()) {
		if (qTail - qHead >= (1<<params[P_DEPTHLIMIT]) || qTail >= QSIZE - QSIZE/16 ||
			 qTail >= QSIZE - (deepeningAmount << 2)) deepen();
		else process(dequeue());
	}
}

void search(int per, int off, int wid, int diag, enum mode mod) {
	if (aborting) return;
	anythingSearched = 1;
	period = per;
	offset = off;
	width = wid;
	widthReduction = 0;
	deepeningAmount = per;
	lastdeep = 0;
	diagonal = diag;
	mode = mod;
	makePhases();
	hashPhase = (gcd(period,offset)>1);

	nRowsInState = period+period;	/* how many rows needed to compute successor graph? */
	if (mode == skew || mode == diagMirror) { /* usually 2*period, but some modes need more */
		nRowsInState += period;
		if (rule & 010000) nRowsInState += period;
	}

	resetQ();
	resetHash();
	if (period == 1 && offset == 0) printf("Searching for still life");
	else {
		printf("Searching for speed ");
		if (offset == 1) printf("c/%d", period);
		else printf("%dc/%d", offset, period);
	}
	printf(", width %d", modeWidth());
	if (diagonal) printf(", diagonal");
	switch(mode) {
		case asymmetric:
			break;

		case skew:
		case diagSkew:
			printf(", skew gutter");
			break;

		case odd: case even: case diagMirror:
			printf(", bilateral symmetry");
			break;

		case gutter:
		case diagGutter:
			printf(", bilateral symmetry, gutter");
			break;

		case mirror: case bigMirror: case diagGlide:
			printf(", glide-reflect symmetry");
			break;

		default:
			printf(", unknown mode!");
			break;
	}
	printf(".\n");
	fflush(stdout);

	enqueue(0,0);
	rephase();
	if (params[P_BIRTHS] & 1) {
		/* set alternating state for B0 rules */
		int i;
		for (i = 0; i < 2*period; i++)
			enqueue(dequeue(), (parity[i%period]? 0 : (1<<width) - 1));
	}
	breadthfirst();
}

/* ======================================================================= */
/*  Use cmd-line parameters to determine which modes and widths to search  */
/* ======================================================================= */

void searchWidth(int per, int off, int wid, int diag) {
	if (wid < 4) return;
	else if (diag) {
		if (params[P_MODES] & M_ASYM) search(per,off,wid,1,asymmetric);
		if (params[P_MODES] & M_ODD) search(per,off,wid,1,diagMirror);
		if ((params[P_MODES] & M_GLIDE) && (per & 01) == 0) search(per,off,wid,1,diagGlide);
		if ((params[P_MODES] & M_EVEN) && ((rule|badRuleBits) & 014000) == 010000)
			search(per,off,wid,1,diagGutter);	/* only useful for B3 w/o B2 */
		if ((params[P_MODES] & M_GUTTER) && ((rule|badRuleBits) & 034000) == 010000)
			search(per,off,wid,1,diagSkew);	/* only useful for B3 w/o B24 */
	} else {
		if (params[P_MODES] & M_ASYM) search(per,off,wid,0,asymmetric);
		if ((params[P_MODES] & M_GLIDE) && per > 1 && ((per|off)&1) != 0) {
			if (wid == MAXWIDTH) search(per,off,wid-1,0,mirror);
			search(per,off,wid,0,mirror);
			if (wid < MAXWIDTH) search(per,off,wid+1,0,bigMirror);
		}
		if ((params[P_MODES] & M_ODD) && (per != off || per != 1)) /* no good for per=1 off=1 */
			search(per,off,wid,0,odd);
		if (params[P_MODES] & M_EVEN) search(per,off,wid,0,even);
		if (params[P_MODES] & M_GUTTER && (params[P_BIRTHS] & 1) == 0) {
			if (((rule|badRuleBits) & 0134000) == 010000)
				search(per,off,wid,0,gutter); /* only useful for B3 w/o B246 */
			else if (((rule|badRuleBits) & 014000) == 04000 &&
					   ((rule|badRuleBits) & 060000) != 060000)
				search(per,off,wid,0,skew);	/* only useful for B2 w/o B4 or w/o B5 */
			else if (((rule|badRuleBits) & 034000) == 010000)
				search(per,off,wid,0,skew);	/* or B3 w/B6 but w/o B24 */
		}
	}
}

void searchGroup(int per, int off, int diag) {
	int wid;
	aborting = 0;
	nFound = 0;
	if (searchLimit <= 0) searchLimit = SEARCHLIMIT;
	wid = searchLimit / (2 * per);
	if (wid > MAXWIDTH) wid = MAXWIDTH;
	searchWidth(per, off, wid, diag);
}

/* test if speed (i/per)*c is slow enough to be possible in given rules */
int smallOffset(int per, int diag, int i) {
	if ((rule & 01000) != 0) {			    /* B0 rules: no limit */
		return (i <= per);
	}
	if ((rule & 04000) == 0) {				/* B3 rules: */
		if (diag) {
			if (((rule&~badRuleBits) & 060) == 0)
				return (4*i <= per);			/* diagonal without one of S45: c/4 */
			else if (((rule&~badRuleBits) & 036) == 0)
				return (3*i < per);			/* diagonal without one of S1234: < c/3 */
			else return (3*i <= per);		/* other diagonal: c/3 */
		} else if (((rule&~badRuleBits) & 036) == 0)
			return (2*i < per);				/* orthogonal without one of S1234: < c/2 */
		else return (2*i <= per);			/* other orthogonal: c/2 */
	} else {										/* B2 rules: */
		if (diag) return (2*i <= per);	/* diagonal: c/2 */
		else return (i <= per);				/* orthogonal: c */
	}
}

void searchOff(int per, int diag) {
	int i;
	if (per & params[P_BIRTHS] & 1) return; /* no odd period for B0 rules */
	sdrawkcab = (params[P_REVERSE] != 0);
	for (i = 1; smallOffset(per,diag,i); i++) {
		int p = per / gcd(i,per);
		if ((params[diag? P_DIAG : P_ORTHOG] & (1<<p)) != 0 &&
			 (params[P_NUMERATORS] & (1<<i)) != 0 && (i<per || per==1))
			searchGroup(per,i,diag);
	}
}

/* =========================================== */
/*  Main entry point and command line parsing  */
/* =========================================== */

/* long message about available cmd line options */
void usage() {
	printf("usage: gfind rule/options\n");
	printf("  e.g. gfind B3/S23/D4/O2 finds c/4 diagonal gliders\n");
	printf("  and c/2 orthogonal spaceships in Conway's life.\n");
	printf("\n");
	printf("available options:\n");
	printf("  /dNN searches for diagonal gliders with periods in NN\n");
	printf("  /oNN searches for orthogonal gliders with periods in NN\n");
	printf("  /nNN searches for gliders that move steps in NN every period\n");
	printf("\n");
	printf("  /xNN disallows patterns with live NN-neighbor cells\n");
	printf("  /zNN disallows patterns with dead NN-neighbor cells\n");
	printf("\n");
	printf("  /lNN limits the search to graphs of 2^NN vertices, i.e.\n");
	printf("       to widths for which period*width*2 <= NN (default %d)\n\n",SEARCHLIMIT);
	printf("  /fNN stop after NN gliders found (best in combination with /h0)\n");
	printf("  /hNN sets the hash table size to 2^NN (default %d)\n",HASHBITS);
	printf("       Use /h0 to disable duplicate elimination.\n");
	printf("  /qNN sets the BFS queue size to 2^NN (default %d)\n",QBITS);
	printf("  /iNN groups 2^NN queue entries to an index node (default 4)\n");
	printf("  /*NN performs depth first iterated deepening when 2^NN leaves in queue\n");
	printf("  /-NN reduces width when iterated deepening level reaches NN\n");
	printf("  /r   reverses search order of pattern rows\n");
	printf("  /+   attempts to find puffers instead of spaceships\n");
	printf("       (best in combination with /f since most output won't work)\n");
	printf("\n");
	printf("  /a   searches for asymmetric patterns\n");
	printf("  /g   searches for glide-reflect patterns only\n");
	printf("  /u   searches for odd bilaterally symmetric patterns\n");
	printf("  /v   searches for even bilaterally symmetric patterns\n");
	printf("  /w   searches for symmetric or skew-symmetric patterns with gutters\n");
	exit(0);
}


/* finish complaining about problem in cmd line */
void badRule() {
	printf("For command line options, type 'gfind c'.\n");
	exit(0);
}

/* parse cmd line */
void parseRule(char *s) {
	int param;
	for (param = 0; param < NUM_PARAMS; param++) params[param] = 0;
	params[P_HASHBITS] = params[P_DEPTHLIMIT] = -1;
	param = -1;

	while (*s != 0) {
		switch(*s) {
			case 'c': case 'C': usage();

			case 'b': case 'B': param = P_BIRTHS; break;
			case 's': case 'S': param = P_SURVIVES; break;
			case 'x': case 'X': param = P_NODEATHS; break;
			case 'z': case 'Z': param = P_NOBIRTHS; break;
			case 'n': case 'N': param = P_NUMERATORS; break;
			case 'o': case 'O': param = P_ORTHOG; break;
			case 'd': case 'D': param = P_DIAG; break;
			case 'i': case 'I': param = P_BASEBITS; break;

			case 'l': case 'L': param = P_SEARCHLIMIT; break;
			case 'q': case 'Q': param = P_QBITS; break;
			case 'h': case 'H': param = P_HASHBITS; break;
			case 'f': case 'F': param = P_FINDLIMIT; break;
			case '-': param = P_REDLEVEL; break;
			case '*': param = P_DEPTHLIMIT; params[P_DEPTHLIMIT] = 0; break;

			case 'g': case 'G': params[P_MODES] |= M_GLIDE; param = -1; break;
			case 'u': case 'U': params[P_MODES] |= M_ODD; param = -1; break;
			case 'v': case 'V': params[P_MODES] |= M_EVEN; param = -1; break;
			case 'w': case 'W': params[P_MODES] |= M_GUTTER; param = -1; break;
			case 'a': case 'A': params[P_MODES] |= M_ASYM; param = -1; break;
			case 'r': case 'R': params[P_REVERSE] = 1; param = -1; break;
			case 't': case 'T': params[P_TRACING] = 1; param = -1; break;

			case '/': param = -1; break;
			
			case '+': params[P_PUFFER] = 1; param = -1; break;

			case '0': case '1': case '2': case '3': case '4':
			case '5': case '6': case '7': case '8': case '9':
				if (param < 0) {
					printf("Unexpected digit in command line.\n");
					badRule();
				} else if (PARAM_IS_BITMASK(param)) {
					/* 1 in o or d means 10+next digit; to specify spead c/1
					   put the 1 last! */
					if (*s == '1' && s[1] >= '0' && s[1] <= '9' &&
						 (param == P_ORTHOG || param == P_DIAG))
						params[param] |= 1 << (10 + *++s - '0');
					else params[param] |= 1 << (*s - '0');
				} else {
					if (params[param] < 0) params[param] = 0;
					params[param] = 10 * params[param] + *s - '0';
				}
				break;

			default:
				printf("Unexpected character '%c' in command line.\n", *s);
				badRule();
		}
		s++;
	}
	rule = (params[P_BIRTHS] << 9) + params[P_SURVIVES];
	badRuleBits = (params[P_NOBIRTHS] << 9) + params[P_NODEATHS];
	if (rule == 0) {
		printf("No rule specified.\n");
		badRule();
	} else if ((params[P_BIRTHS] & 03) == 02) {
		printf("With B1, no such patterns exist.\n");
		exit(0);
	}
	if (params[P_ORTHOG] == 0 && params[P_DIAG] == 0)
		params[P_ORTHOG] = params[P_DIAG] = -1;
	if (params[P_NUMERATORS] == 0) params[P_NUMERATORS] = -1 &~ 1;
	if (params[P_MODES] == 0) params[P_MODES] = -1;
	if (params[P_HASHBITS] < 0) params[P_HASHBITS] = HASHBITS;
	if (params[P_QBITS] <= 0) params[P_QBITS] = QBITS;
	if (params[P_BASEBITS] <= 0) params[P_BASEBITS] = 5;
	if (params[P_DEPTHLIMIT] == 0) params[P_DEPTHLIMIT] = qBits;
	else if (params[P_DEPTHLIMIT] < 0) params[P_DEPTHLIMIT] = DEFAULT_DEPTHLIMIT;
}

/* read cmd line from stdin (e.g. for SIOUX on Mac where there is no real cmd line) */
char * readString() {
	static char buf[1024];
	char *s = buf;
	int i = 0;
	char c;
	
	fprintf(stderr,"Rule (return for help): ");
	while ((c = getchar()) != '\n')
		if (i++ < 1023) *s++ = c;
	*s++ = '\0';
	return buf;
}

/* count bits of 3-bit word */
#define NBITS(x) ((x) - ((x)>>1) - ((x)>>2))

/* main program */
int main(int ac, char **av) {
	int i;
	
	printf("%s\n", BANNER);

	if (ac < 2) parseRule(readString());
	else if (ac == 2) {
		printf("Rule: %s\n", av[1]);
		parseRule(av[1]);
	} else usage();

	base = malloc((QSIZE>>BASEBITS)*sizeof(node));
	rows = malloc(QSIZE*sizeof(row));
	if (base == 0 || rows == 0) {
		printf("Unable to allocate BFS queue!\n");
		exit(0);
	}
	
	if (hashBits == 0) hash = 0;
	else {
		hash = malloc(HASHSIZE*sizeof(node));
		if (hash == 0) printf("Unable to allocate hash table, duplicate elimination disabled\n");
	}
	if (findLimit <= 0) findLimit = 1;

	makeReversals();
	makeUnterm();
	set4x();
	
	for (i = 1; i <= MAXPERIOD; i++) {
		searchOff(i,0);
		searchOff(i,1);
	}
	if (!anythingSearched) {
		printf("No searches match those parameters.\n");
		badRule();
	}
	printf("Search complete.\n");
	return 0;
}

/*
 * Programming Project #1 : 2D Resource Allocation Problem with NR
 *
 * Approach:
 *   1. For every user, precompute "options": a bit threshold b gives the
 *      usable rows (bits >= b) and the number of RBs k = ceil(D / (S*b)).
 *      Dominated options are dropped, so options are sorted by k ascending.
 *   2. Placement of one user: for the cheapest feasible option, place its k
 *      RBs one by one.  Columns are scanned from the arrival time using a
 *      per-shape "free spot exists" bitset; after the first fit the scan
 *      looks ahead a bounded distance and keeps the corner position with the
 *      highest contact ratio (touching occupied cells / borders);
 *      all RBs of one request use the same shape (safe numerology rule).
 *      A dry first-fit run (nothing marked) first drops the shapes that
 *      cannot hold all k RBs, so few placements fail half way.
 *      Cheap mode (used when the work budget cannot afford the lookahead for
 *      every request): first fit found by a dry run that does not touch the
 *      grid, and the request's RBs merged into a few rectangles that are
 *      marked once each.  Masks of shapes this mode rarely uses are not kept
 *      up to date meanwhile; they are rebuilt from the occupancy when needed.
 *   3. Initial solution: greedy over several priority orders
 *      (profit / area^alpha), keep the best.  When the demand is several
 *      times the grid, the leading requests that fill it get a long
 *      lookahead (they decide the profit; the rest mostly fail).  Options
 *      needing more than MAX_RB RBs are separate items: each is tried (cheap
 *      mode) when the greedy reaches its own profit per area.
 *   4. Improvement: ruin-and-recreate.  All users inside a region (time strip
 *      x row band) are removed and the region is refilled by priority
 *      (removed + unassigned users).  A move is kept if profit increases, or
 *      stays equal with less used area.  Region shapes are swept with one
 *      cursor each, and short segments of work are shared out among the
 *      shapes in proportion to their recent gain.  Once the sweep stalls, each
 *      refill also tries leaving out one of the requests it placed (one
 *      discrepancy); when that stalls too, a threshold phase follows: refill
 *      orders are enumerated in a fixed cycle and a refill losing at most a
 *      threshold (falling to zero) is kept; the best solution is the answer.
 *   Fully deterministic: no randomness, no clock.  All work is bounded by an
 *   operation counter whose costs follow the measured run time.
 *   No input range is assumed: every array is sized from the input.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned long long u64;

#define NVAR 9                      /* number of priority orders          */
#define MAXSH 32                    /* shapes kept (bitmask in unsigned)  */
#ifndef OPS_LIMITV
#define OPS_LIMITV 52000000000LL
#endif
#ifndef WIDE_LIMITV
#define WIDE_LIMITV 15000000000LL   /* the wider-lookahead construction may run up to here */
#endif
#ifndef NORM_LIMITV
#define NORM_LIMITV 24000000000LL
#endif
#define BUDGET(v) (v)
#define NORM_LIMIT BUDGET(NORM_LIMITV)
#define OPS_LIMIT BUDGET(OPS_LIMITV)      /* soft work budget                   */
#define OPS_HARD  (OPS_LIMIT + BUDGET(1100000000LL))      /* hard work budget                   */
#define MEM_GRID  900000000.0
#define MAX_COLS  30000000LL        /* most columns the grid keeps */      /* bytes allowed for the grid levels  */
#ifndef MAX_RB
#define MAX_RB    64                 /* max RBs per user in the normal passes */
#endif
#ifndef BIG_RB
#define BIG_RB    1048576            /* requests needing more: separate items, at their own profit per area */
#endif
#ifndef SETUP_PER_BYTE
#define SETUP_PER_BYTE 24           /* charged work per input byte (parse + options) */
#endif
#ifndef MARK_COST
#define MARK_COST 600
#define USER_COST 250
#define UNDO_COST 100
#ifndef UNION_RB_COST
#define UNION_RB_COST 700           /* each RB merged into a bigger rectangle */
#endif
#ifndef STALE_DIV
#define STALE_DIV 32                /* stale-shape retries: at most 1/STALE_DIV of the cheap work */
#endif
#ifndef LEAN_MUL4
#define LEAN_MUL4 5                 /* cheap-mode work is charged LEAN_MUL4/4 times */
#endif
#define MARK_ON_COST 1500           /* same fixed charge for marking (calibrate later) */               /* cache-miss cost of one RB (un)marking */
#endif
#ifndef LONG_LOOK
#define LONG_LOOK 128               /* the first construction starts the core with this lookahead */
#endif
#ifndef LONG_MIN
#define LONG_MIN 16                 /* ...halved down to this while it would not reach the end of the core */
#endif
#ifndef LONG_LOAD
#define LONG_LOAD 2                 /* ...only when the demand is at least this many times the grid */
#endif
#ifndef LONG_CORE100
#define LONG_CORE100 100            /* ...for the leading requests whose smallest areas fill this % of the grid */
#endif
#ifndef LONG_FRAC100
#define LONG_FRAC100 75             /* ...while it has used at most this % of the budget */
#endif
#ifndef LOOK_MULV
#define LOOK_MULV 2
#endif
#define LOOK_MUL  LOOK_MULV                /* lookahead (in RB widths) after the first fit */
#ifndef LNS_LOOK
#define LNS_LOOK 4           /* lookahead of the local search refills */
#endif
static long long lookMul = LOOK_MUL;
#define MEM_OWN   500000000.0       /* bytes allowed for the owner grid   */
#define MEM_ROW   300000000.0       /* bytes allowed for row-major occupancy */
#define MEM_OPT   300000000.0       /* bytes allowed for option masks     */

typedef struct {
    int h, w;       /* frequency size, time size */
    int s;          /* shape index               */
    int y, x;       /* bottom-left position      */
} RB;

typedef struct {
    long long id, dem, profit;
    int arr, dl;
    int nopt, nbig;         /* options with <= MAX_RB RBs, then up to 2 with more */
    int *optK;              /* RBs needed for each option            */
    u64 *optMask;           /* usable rows for each option (W words) */
    unsigned *optShapes;    /* shapes that can fit for each option   */
    long long minArea;
    int assigned, nrb, cap;
    RB *rbs;
} User;

static int Y, X, S, N, W;
static int nsh, shH[MAXSH], shW[MAXSH];
static int shLj[MAXSH], shOff[MAXSH];   /* log2(w) and w - 2^log2(w) per shape */
static int shStep[MAXSH][40], shNStep[MAXSH];   /* shift sequence of runs() for h */
static User *U;
static u64 *lev[32];        /* lev[j][x] = OR of columns x..x+2^j-1   */
static int nlev;
static unsigned usedSh = ~0U;
static long long levSpan; static int levCnt;   /* charge-only stand-in for the old OR levels */  /* shapes some request can use (others need no masks) */
static u64 *col;            /* occupancy, column-major: X * W words   */
static RB *tmpRB;
static u64 *fz[MAXSH];      /* fz[s] bit x: some h*w free spot starts at column x */
static u64 *fzs[MAXSH];     /* fzs[s] bit i: word i of fz[s] is non-zero (skips empty stretches) */
static int fzsWords;
static void fzs_fix(int s, int w0, int w1);

/*
 * Journal of the derived words (free-start masks, their column flags and
 * summary) changed while one request is being placed.  Taking back RBs of
 * an unfinished placement restores these words instead of recomputing them.
 */
static u64 **jPtr, *jVal;
static long long jLen, jCap, *tmpJ;
static int jOn, jOk;

static void jpush(u64 *p)
{
    if (jLen < jCap) { jPtr[jLen] = p; jVal[jLen] = *p; jLen++; }
    else jOk = 0;
}

static u64 *fm[MAXSH];      /* fm[s][x]: rows y where an h*w block at (x, y) is free */
static int fzWords;
static long long *fen;      /* Fenwick tree: occupied cells per column        */
static int *own;            /* owner user of each cell (x*Y+y), or -1         */
static int useOwn, ownLive = 1, ownValid = 1;   /* ownLive = 0: owner grid rebuilt later */
static u64 *scAll, *scMp, *scMn, *scMm, *scGs;
static int curOwner = -1;   /* user whose RBs are being marked               */
static u64 *rowOcc;         /* row-major occupancy: rowOcc[y*fzWords + x/64] */
static int useRow;
static long long ops;
static long long hardLimit = 9000000000000000000LL;  /* abort placements past this */
static long long opsEnd;    /* end of the local search budget */
static long long curProfit, curArea;
static int *order[NVAR], *rankv[NVAR];
static int nVar = NVAR;     /* priority orders actually used (fewer for huge N) */
static double *keyBuf;
static int maxOpt;

/* scratch row masks (W words each) */
static u64 *scT, *scRm1, *scRm2, *scOcc, *scFr, *scSl, *scSr, *scCand, *scG, *scM, *scPend, *scTail, *scBig1, *scBig2;

/* ---------- fast input ---------- */

/* input is parsed straight from a fixed-size buffer (no copy of the whole file) */
#define IBUF (1 << 22)
static char ibuf[IBUF + 1];
static size_t ilen, ipos;
static long long inTotal;
static int ieof;

/* at least 64 unread bytes in the buffer, unless the input has ended */
static void iensure(void)
{
    if (ilen - ipos >= 64 || ieof) return;
    memmove(ibuf, ibuf + ipos, ilen - ipos);
    ilen -= ipos; ipos = 0;
    while (ilen < 64 && !ieof) {
        size_t n = fread(ibuf + ilen, 1, IBUF - ilen, stdin);
        if (n == 0) ieof = 1;
        ilen += n; inTotal += (long long)n;
    }
    ibuf[ilen] = 0;
}

static int read_ll(long long *out)
{
    const char *p;
    int neg = 0;
    long long v = 0;
    for (;;) {
        iensure();
        p = ibuf + ipos;
        while (*p == ' ' || *p == '\n' || *p == '\r' || *p == '\t') p++;
        ipos = (size_t)(p - ibuf);
        if (*p == '-' || (*p >= '0' && *p <= '9')) break;
        if (ipos >= ilen) { if (ieof) return 0; continue; }
        ipos++;                             /* any other character: skip */
    }
    iensure();
    p = ibuf + ipos;
    if (*p == '-') { neg = 1; p++; }
    while (*p >= '0' && *p <= '9') {
        if (v < 922337203685477580LL) v = v * 10 + (*p - '0');   /* saturate */
        p++;
    }
    ipos = (size_t)(p - ibuf);
    *out = neg ? -v : v;
    return 1;
}

static int clamp_int(long long v)
{
    if (v > 2000000000LL) return 2000000000;
    if (v < -2000000000LL) return -2000000000;
    return (int)v;
}

static int ilog2(long long v)
{
    int r = 0;
    while (v > 1) { v >>= 1; r++; }
    return r;
}

/* ---------- multi-word row-mask helpers ---------- */


static const int debruijnTab[64] = {
    0, 1, 48, 2, 57, 49, 28, 3, 61, 58, 50, 42, 38, 29, 17, 4,
    62, 55, 59, 36, 53, 51, 43, 22, 45, 39, 33, 30, 24, 18, 12, 5,
    63, 47, 56, 27, 60, 41, 37, 16, 54, 35, 52, 21, 44, 32, 23, 11,
    46, 26, 40, 15, 34, 20, 31, 10, 25, 14, 19, 9, 13, 8, 7, 6
};
static int ctz64(u64 v)     /* index of lowest set bit, v != 0 */
{
    return debruijnTab[((v & (0 - v)) * 0x03F79D71B4CB0A89ULL) >> 58];
}

static int popc(u64 v)      /* number of set bits (portable) */
{
    v = v - ((v >> 1) & 0x5555555555555555ULL);
    v = (v & 0x3333333333333333ULL) + ((v >> 2) & 0x3333333333333333ULL);
    v = (v + (v >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((v * 0x0101010101010101ULL) >> 56);
}

static void shr_k(u64 *d, const u64 *s, int k)   /* bit y of d = bit y+k of s */
{
    int ws = k >> 6, bs = k & 63, i;
    for (i = 0; i < W; i++) {
        int j = i + ws;
        u64 v = 0;
        if (j < W) {
            v = s[j] >> bs;
            if (bs && j + 1 < W) v |= s[j + 1] << (64 - bs);
        }
        d[i] = v;
    }
}


/* d = rows y such that rows y..y+h-1 are all set in f */
static void runs(u64 *d, const u64 *f, int h)
{
    int len = 1, i;
    for (i = 0; i < W; i++) d[i] = f[i];
    while (len < h) {
        int step = (len < h - len) ? len : h - len;
        shr_k(scT, d, step);
        for (i = 0; i < W; i++) d[i] &= scT[i];
        len += step;
    }
}

/* runs() for the height of shape s (one word: the precomputed shifts) */
static void runs_s(u64 *d, const u64 *f, int s)
{
    if (W == 1) {
        u64 v = f[0];
        int t;
        for (t = 0; t < shNStep[s]; t++) v &= v >> shStep[s][t];
        d[0] = v;
        return;
    }
    runs(d, f, shH[s]);
}

static int is_zero(const u64 *a)
{
    int i;
    for (i = 0; i < W; i++) if (a[i]) return 0;
    return 1;
}

/* fills only words (y>>6) .. ((y+h-1)>>6) of d */
static void row_mask(u64 *d, int y, int h)
{
    int i, i1 = (int)(((long long)y + h - 1) >> 6);
    for (i = y >> 6; i <= i1; i++) {
        long long lo = (long long)y - (long long)i * 64, hi = (long long)y + h - (long long)i * 64;
        if (lo < 0) lo = 0;
        if (hi > 64) hi = 64;
        if (lo >= hi) { d[i] = 0; continue; }
        d[i] = (hi == 64 ? ~0ULL : ((1ULL << hi) - 1)) & ~((1ULL << lo) - 1);
    }
}

static int bit_at(int x, int y)
{
    return (int)((col[(size_t)x * W + (size_t)(y >> 6)] >> (y & 63)) & 1ULL);
}

/* ---------- Fenwick tree over columns ---------- */

static int nBlk;             /* number of 64-column blocks */

static void fen_add(int x, long long v)
{
    for (x++; x <= nBlk; x += x & (-x)) fen[x] += v;
}

static long long fen_pref(int x)        /* sum of columns 0..x-1 */
{
    long long r = 0;
    for (; x > 0; x -= x & (-x)) r += fen[x];
    return r;
}

/*
 * Recompute the free-start masks of shape s for columns lo..hi (after cells
 * were freed).  The OR of the w columns x..x+w-1 comes from a sliding-window
 * OR over the occupancy (prefix/suffix ORs inside blocks of w columns), so no
 * per-level OR tables have to be kept up to date.
 */
static u64 *vhP, *vhS;      /* scratch, (3 * maxShW + 64) * W words each */

static void fz_update(int s, long long lo, long long hi)
{
    int x, xm = X - shW[s], ws = shW[s], n, span, i, k, t;
    if (lo < 0) lo = 0;
    if (hi > xm) hi = xm;
    if (lo > hi) return;
    n = (int)(hi - lo + 1);
    span = n + ws - 1;
    if (W == 1) {
        const u64 *cl = col + lo, all = scAll[0];
        u64 *f = fm[s], *z = fz[s], *P = vhP, *Sx = vhS;
        const int *st = shStep[s], ns = shNStep[s];
        if (ws == 1) {
            for (x = 0; x < n; x++) {
                u64 v = ~cl[x] & all;
                for (t = 0; t < ns; t++) v &= v >> st[t];
                f[lo + x] = v;
                if (v) z[(lo + x) >> 6] |= 1ULL << ((lo + x) & 63);
                else z[(lo + x) >> 6] &= ~(1ULL << ((lo + x) & 63));
            }
        } else {
            for (i = 0, k = 0; i < span; i++) {          /* prefix ORs inside blocks */
                P[i] = k == 0 ? cl[i] : (P[i - 1] | cl[i]);
                if (++k == ws) k = 0;
            }
            k = (span - 1) % ws;
            for (i = span - 1; i >= 0; i--) {            /* suffix ORs inside blocks */
                Sx[i] = (i == span - 1 || k == ws - 1) ? cl[i] : (Sx[i + 1] | cl[i]);
                if (--k < 0) k = ws - 1;
            }
            for (x = 0; x < n; x++) {
                u64 v = ~(Sx[x] | P[x + ws - 1]) & all;
                for (t = 0; t < ns; t++) v &= v >> st[t];
                f[lo + x] = v;
                if (v) z[(lo + x) >> 6] |= 1ULL << ((lo + x) & 63);
                else z[(lo + x) >> 6] &= ~(1ULL << ((lo + x) & 63));
            }
        }
        ops += 3LL * span + 4LL * n;
    } else {
        const u64 *cl = col + (size_t)lo * W;
        u64 *P = vhP, *Sx = vhS;
        int c;
        for (i = 0, k = 0; i < span; i++) {
            for (c = 0; c < W; c++) P[(size_t)i * W + c] = k == 0 ? cl[(size_t)i * W + c] : (P[(size_t)(i - 1) * W + c] | cl[(size_t)i * W + c]);
            if (++k == ws) k = 0;
        }
        k = (span - 1) % ws;
        for (i = span - 1; i >= 0; i--) {
            int fresh = i == span - 1 || k == ws - 1;
            for (c = 0; c < W; c++) Sx[(size_t)i * W + c] = fresh ? cl[(size_t)i * W + c] : (Sx[(size_t)(i + 1) * W + c] | cl[(size_t)i * W + c]);
            if (--k < 0) k = ws - 1;
        }
        for (x = 0; x < n; x++) {
            u64 *out = fm[s] + (size_t)(lo + x) * W;
            int nz = 0;
            for (c = 0; c < W; c++) scFr[c] = ~(Sx[(size_t)x * W + c] | P[(size_t)(x + ws - 1) * W + c]) & scAll[c];
            runs(out, scFr, shH[s]);
            for (c = 0; c < W; c++) nz |= out[c] != 0;
            if (nz) fz[s][(lo + x) >> 6] |= 1ULL << ((lo + x) & 63);
            else fz[s][(lo + x) >> 6] &= ~(1ULL << ((lo + x) & 63));
        }
        ops += (6LL * span + (long long)(ilog2(shH[s]) + 3) * n * 2) * W;
    }
    fzs_fix(s, (int)(lo >> 6), (int)(hi >> 6));
}

/* refresh the summary bits of fz[s] words w0..w1 */
static void fzs_fix(int s, int w0, int w1)
{
    const u64 *z = fz[s];
    u64 *q = fzs[s];
    int i;
    for (i = w0; i <= w1; i++) {
        u64 *qw = q + (i >> 6), nv = z[i] ? (*qw | (1ULL << (i & 63))) : (*qw & ~(1ULL << (i & 63)));
        if (nv != *qw) { if (jOn) jpush(qw); *qw = nv; }
    }
}


/* bits [x0, x1] of a row bitset: set (on=1), clear (on=0) */
static void row_range(u64 *rw, int x0, int x1, int on)
{
    int wi;
    for (wi = x0 >> 6; wi <= (x1 >> 6); wi++) {
        int lo = wi == (x0 >> 6) ? (x0 & 63) : 0, hi = wi == (x1 >> 6) ? (x1 & 63) : 63;
        u64 m = (hi == 63 ? ~0ULL : ((1ULL << (hi + 1)) - 1)) & ~((1ULL << lo) - 1);
        if (on) rw[wi] |= m; else rw[wi] &= ~m;
    }
}

static int row_count(const u64 *rw, int x0, int x1)
{
    int wi, c = 0;
    if ((x0 >> 6) == (x1 >> 6))
        return popc(rw[x0 >> 6] & (~0ULL << (x0 & 63)) & (~0ULL >> (63 - (x1 & 63))));
    for (wi = x0 >> 6; wi <= (x1 >> 6); wi++) {
        int lo = wi == (x0 >> 6) ? (x0 & 63) : 0, hi = wi == (x1 >> 6) ? (x1 & 63) : 63;
        u64 m = (hi == 63 ? ~0ULL : ((1ULL << (hi + 1)) - 1)) & ~((1ULL << lo) - 1);
        c += popc(rw[wi] & m);
    }
    return c;
}

static u64 *scSm;   /* scratch: start-row mask */
static int markOnly = -1;   /* >= 0: marking updates only this shape's masks */



/*
 * Mark (on=1) or clear (on=0) one RB in every structure.
 * Marking only removes free space, so the OR levels and the free-start
 * masks are updated with a single OR / AND-NOT per column; clearing has to
 * rebuild them from the occupancy below.
 */
/* occupancy, owners, block counts and row bits of one RB (no derived masks) */
static void mark_raw(const RB *r, int on)
{
    int c, i;
    int w0 = r->y >> 6, w1 = (r->y + r->h - 1) >> 6;
    row_mask(scRm2, r->y, r->h);
    for (c = r->x; c < r->x + r->w; c++) {
        u64 *p = col + (size_t)c * W;
        for (i = w0; i <= w1; i++) p[i] = on ? (p[i] | scRm2[i]) : (p[i] & ~scRm2[i]);
        if (useOwn && ownLive) {
            int *o = own + (size_t)c * Y + r->y, v = on ? curOwner : -1;
            for (i = 0; i < r->h; i++) o[i] = v;
        }
    }
    {
        int b0 = r->x >> 6, b1 = (r->x + r->w - 1) >> 6, bb;
        for (bb = b0; bb <= b1; bb++) {
            int lo2 = bb == b0 ? r->x : bb << 6, hi2 = bb == b1 ? r->x + r->w - 1 : (bb << 6) + 63;
            fen_add(bb, (long long)(hi2 - lo2 + 1) * (on ? r->h : -r->h));
        }
    }
    if (useRow) for (i = 0; i < r->h; i++) row_range(rowOcc + (size_t)(r->y + i) * fzWords, r->x, r->x + r->w - 1, on);
}

/* free-start masks of shape s after RB r was marked; returns the columns touched */
static long long mark_shape_on(const RB *r, int s)
{
    int c, i;
    long long lo = (long long)r->x - shW[s] + 1, hi = (long long)r->x + r->w - 1, y0;
        int xm = X - shW[s], hs = shH[s];
        u64 *F = fm[s], *Z = fz[s];
        if (lo < 0) lo = 0;
        if (hi > xm) hi = xm;
        if (lo > hi) return 0;
        y0 = (long long)r->y - hs + 1;
        if (y0 < 0) y0 = 0;
        row_mask(scSm, (int)y0, (int)((long long)r->y + r->h - y0));
        {
            int s0 = (int)(y0 >> 6), s1 = (r->y + r->h - 1) >> 6;
            if (W == 1) {
                u64 m = ~scSm[0];
                if (jOn) {
                    for (c = (int)lo; c <= (int)hi; c++) {
                        u64 v = F[c] & m;
                        if (v != F[c]) {
                            jpush(F + c);
                            F[c] = v;
                            if (!v) { jpush(Z + (c >> 6)); Z[c >> 6] &= ~(1ULL << (c & 63)); }
                        }
                    }
                } else {
                    for (c = (int)lo; c <= (int)hi; c++) {
                        u64 v = F[c] & m;
                        F[c] = v;
                        if (!v) Z[c >> 6] &= ~(1ULL << (c & 63));
                    }
                }
            } else {
                for (c = (int)lo; c <= (int)hi; c++) {
                    u64 *f = F + (size_t)c * W, nz = 0, ch = 0;
                    for (i = s0; i <= s1; i++) {
                        u64 v = f[i] & ~scSm[i];
                        if (v != f[i]) { if (jOn) jpush(f + i); f[i] = v; ch = 1; }
                    }
                    if (ch) {
                        for (i = 0; i < W; i++) nz |= f[i];
                        if (!nz && ((Z[c >> 6] >> (c & 63)) & 1ULL)) {
                            if (jOn) jpush(Z + (c >> 6));
                            Z[c >> 6] &= ~(1ULL << (c & 63));
                        }
                    }
                }
            }
        }
        fzs_fix(s, (int)(lo >> 6), (int)(hi >> 6));
        return hi - lo + 1;
}

static void mark_rb(const RB *r, int on)
{
    int c, i, j, s;
    int w0 = r->y >> 6, w1 = (r->y + r->h - 1) >> 6;
    row_mask(scRm2, r->y, r->h);
    for (c = r->x; c < r->x + r->w; c++) {
        u64 *p = col + (size_t)c * W;
        for (i = w0; i <= w1; i++) p[i] = on ? (p[i] | scRm2[i]) : (p[i] & ~scRm2[i]);
        if (useOwn && ownLive) {
            int *o = own + (size_t)c * Y + r->y, v = on ? curOwner : -1;
            for (i = 0; i < r->h; i++) o[i] = v;
        }
    }
    {   /* occupied cells per 64-column block */
        int b0 = r->x >> 6, b1 = (r->x + r->w - 1) >> 6, bb;
        for (bb = b0; bb <= b1; bb++) {
            int lo2 = bb == b0 ? r->x : bb << 6, hi2 = bb == b1 ? r->x + r->w - 1 : (bb << 6) + 63;
            fen_add(bb, (long long)(hi2 - lo2 + 1) * (on ? r->h : -r->h));
        }
    }
    if (useRow) for (i = 0; i < r->h; i++) row_range(rowOcc + (size_t)(r->y + i) * fzWords, r->x, r->x + r->w - 1, on);
    if (on) {
        long long span = 0;
        for (j = 1; j < nlev; j++) {
            long long lo = (long long)r->x - (1LL << j) + 1, hi = (long long)r->x + r->w - 1;
            if (lo < 0) lo = 0;
            if (W == 1) {
                u64 m = scRm2[0], *L = lev[j];
                for (c = (int)lo; c <= (int)hi; c++) L[c] |= m;
            } else {
                for (c = (int)lo; c <= (int)hi; c++) {
                    u64 *dst = lev[j] + (size_t)c * W;
                    for (i = w0; i <= w1; i++) dst[i] |= scRm2[i];
                }
            }
            span += hi - lo + 1;
        }
        for (s = 0; s < nsh; s++) {
            if (!((usedSh >> s) & 1U)) continue;
            if (markOnly >= 0 && s != markOnly) continue;   /* other shapes: applied later */
            span += mark_shape_on(r, s);
        }
        /* charged as before the OR-level tables were dropped (keeps the time scale) */
        span += levSpan + (long long)levCnt * r->w;
        ops += (long long)r->w * (4 + (useOwn && ownLive ? r->h : 0)) + span * (W == 1 ? 5 : 2 * W + 3) + W + MARK_ON_COST;
        return;
    }
    for (j = 1; j < nlev; j++) {
        int half = 1 << (j - 1);
        long long lo = (long long)r->x - (1LL << j) + 1, hi = (long long)r->x + r->w - 1;
        if (lo < 0) lo = 0;
        if (hi > X - 1) hi = X - 1;
        for (c = (int)lo; c <= (int)hi; c++) {
            u64 *dst = lev[j] + (size_t)c * W;
            const u64 *s1 = lev[j - 1] + (size_t)c * W;
            if ((long long)c + half < X) {
                const u64 *s2 = lev[j - 1] + (size_t)(c + half) * W;
                for (i = 0; i < W; i++) dst[i] = s1[i] | s2[i];
            } else {
                for (i = 0; i < W; i++) dst[i] = s1[i];
            }
        }
    }
    for (s = 0; s < nsh; s++)
        if ((usedSh >> s) & 1U) fz_update(s, (long long)r->x - shW[s] + 1, (long long)r->x + r->w - 1);
    ops += (long long)r->w * (nlev * W + 4 + (useOwn && ownLive ? r->h : 0)) + W + MARK_COST;
}

/* ---------- placement of one request ---------- */

static int contact(int x, int y, int h, int w)
{
    int c = 0, i, t, w0 = y >> 6, w1 = (y + h - 1) >> 6;
    row_mask(scRm1, y, h);
    if (x == 0) c += h;
    else for (i = w0; i <= w1; i++) c += popc(col[(size_t)(x - 1) * W + i] & scRm1[i]);
    if ((long long)x + w == X) c += h;
    else for (i = w0; i <= w1; i++) c += popc(col[(size_t)(x + w) * W + i] & scRm1[i]);
    if (useRow) {
        c += y == 0 ? w : row_count(rowOcc + (size_t)(y - 1) * fzWords, x, x + w - 1);
        c += (long long)y + h == Y ? w : row_count(rowOcc + (size_t)(y + h) * fzWords, x, x + w - 1);
        (void)t;
        return c;
    }
    if (y == 0) c += w;
    else for (t = x; t < x + w; t++) c += bit_at(t, y - 1);
    if ((long long)y + h == Y) c += w;
    else for (t = x; t < x + w; t++) c += bit_at(t, y + h);
    return c;
}

/* take back tentative RBs from..placed-1 (the most recent ones) */
static void undo_range(int from, int placed)
{
    int i;
    if (placed <= from) return;
    if (jOn && jOk) {
        long long target = tmpJ[from], n = jLen - target;
        while (jLen > target) { jLen--; *jPtr[jLen] = jVal[jLen]; }
        for (i = placed - 1; i >= from; i--) mark_raw(&tmpRB[i], 0);
        ops += 2 * n + (long long)(placed - from) * (UNDO_COST + 4 * tmpRB[from].w);
    } else {
        int on = jOn;
        jOn = 0;                            /* journal incomplete: recompute */
        for (i = from; i < placed; i++) mark_rb(&tmpRB[i], 0);
        jOn = on;
        if (jOn) { jLen = tmpJ[from]; jOk = 1; }
    }
}

static void undo_tmp(int placed)
{
    undo_range(0, placed);
}

typedef struct { int x, y, s, c, p; } Best;

static void consider(Best *b, int xx, int y, int s)
{
    int h = shH[s], w = shW[s], cc = contact(xx, y, h, w);
    ops += (h + w + 2 * W + 4) / 2;
    /* maximise cc/(h+w); ties: earlier x, lower y */
    if (b->s < 0 || (long long)cc * b->p > (long long)b->c * (h + w) ||
        ((long long)cc * b->p == (long long)b->c * (h + w) &&
         (xx < b->x || (xx == b->x && y < b->y)))) {
        b->c = cc; b->p = h + w; b->x = xx; b->y = y; b->s = s;
    }
}

/*
 * Scan shape s over the window [a, d] (only columns flagged in fz[s]),
 * from the earliest column on.  Once a valid spot is found, the scan goes
 * on for LOOK more columns and keeps the corner spot with the best contact.
 */
static void scan_shape_core(int s, const u64 *good, int a, int a0, int d, Best *b, int *firstOut);

/*
 * Within one placement attempt the grid only fills up, so a column that had
 * no valid spot for shape s stays without one: later RBs of the same request
 * resume the scan at the first valid column found before (same result).
 */
static int scanFrom[MAXSH];

static void scan_shape(int s, const u64 *good, int a, int d, Best *b)
{
    int first = -1, from = scanFrom[s] > a ? scanFrom[s] : a;
    if (from > d) return;
    scan_shape_core(s, good, a, from, d, b, &first);
    scanFrom[s] = first >= 0 ? first : d + 1;
}

/*
 * Candidates v of column x (single word): the left/right neighbour columns
 * are read once for all of them.  Same scores and tie-breaks as consider().
 */
static void consider_col1(Best *b, int x, u64 v, int s)
{
    int h = shH[s], w = shW[s], hw = h + w;
    u64 hm = h >= 64 ? ~0ULL : ((1ULL << h) - 1);
    int lb = x == 0, rb = (long long)x + w == X;
    u64 Lw = lb ? 0 : col[x - 1], Rw = rb ? 0 : col[x + w];
    while (v) {
        int y = ctz64(v), cc;
        u64 rm = hm << y;
        v &= v - 1;
        cc = (lb ? h : popc(Lw & rm)) + (rb ? h : popc(Rw & rm));
        cc += y == 0 ? w : row_count(rowOcc + (size_t)(y - 1) * fzWords, x, x + w - 1);
        cc += (long long)y + h == Y ? w : row_count(rowOcc + (size_t)(y + h) * fzWords, x, x + w - 1);
        ops += (hw + 2 * W + 4) / 2;
        if (b->s < 0 || (long long)cc * b->p > (long long)b->c * hw ||
            ((long long)cc * b->p == (long long)b->c * hw && (x < b->x || (x == b->x && y < b->y)))) {
            b->c = cc; b->p = hw; b->x = x; b->y = y; b->s = s;
        }
    }
}

/*
 * Next word index >= wi (and <= we) of fz[s] that is non-zero, or -1.
 * Uses the summary bits; charges the summary words it reads.
 */
static int next_word(int s, int wi, int we)
{
    int si, se;
    u64 v;
    if (wi > we) return -1;
    if (fz[s][wi]) return wi;
    if (++wi > we) return -1;
    si = wi >> 6; se = we >> 6;
    v = fzs[s][si] & (~0ULL << (wi & 63));
    while (!v) {
        if (++si > se) return -1;
        v = fzs[s][si];
        ops += 2;
    }
    wi = (si << 6) + ctz64(v);
    return wi <= we ? wi : -1;
}

static void scan_shape_core(int s, const u64 *good, int a, int a0, int d, Best *b, int *firstOut)
{
    int w = shW[s], xmax = d - w + 1, first = -1, x, i, wi, we;
    long long look = (long long)lookMul * w, lim = xmax, visits = 0;
    u64 z;
    runs_s(scGs, good, s);                  /* user's row pattern for this shape */
    if (is_zero(scGs) || a0 > xmax) { *firstOut = first; return; }
    wi = a0 >> 6; we = xmax >> 6;
    z = fz[s][wi] & (~0ULL << (a0 & 63));
    if (W == 1) {                           /* single-word fast path */
        const u64 G = scGs[0], *F = fm[s];
        for (;;) {
            while (z) {
                u64 m;
                x = (wi << 6) + ctz64(z);
                z &= z - 1;
                if (x > lim) goto done1;
                m = F[x] & G;
                visits++;
                if (m) {
                    u64 mp = 0, mn = 0, v;
                    if (first < 0) { first = x; if (first + look < lim) lim = first + look; }
                    if (x - 1 >= a) mp = F[x - 1] & G;
                    if (x + 1 <= xmax) mn = F[x + 1] & G;
                    v = ((m & ~mp) | (m & ~mn)) & ((m & ~(m << 1)) | (m & ~(m >> 1)));
                    if (!v && b->s < 0) v = m & (0 - m);
                    if (v) {                    /* columns without candidates cost nothing more */
                        if (useRow) consider_col1(b, x, v, s);
                        else while (v) { consider(b, x, ctz64(v), s); v &= v - 1; }
                    }
                    ops += 8;
                }
            }
            wi = next_word(s, wi + 1, we);
            if (wi < 0) break;
            z = fz[s][wi];
        }
    done1:
        ops += visits * 4 + 2;
        *firstOut = first;
        return;
    }
    {                                       /* multi-word path */
        const u64 *G = scGs, *F = fm[s];
        for (;;) {
            while (z) {
                const u64 *f;
                int nz = 0;
                x = (wi << 6) + ctz64(z);
                z &= z - 1;
                if (x > lim) goto doneW;
                f = F + (size_t)x * W;
                for (i = 0; i < W; i++) { scM[i] = f[i] & G[i]; nz |= scM[i] != 0; }
                visits++;
                if (nz) {
                    if (first < 0) { first = x; if (first + look < lim) lim = first + look; }
                    if (x - 1 >= a) {
                        const u64 *fp = F + (size_t)(x - 1) * W;
                        for (i = 0; i < W; i++) scMp[i] = fp[i] & G[i];
                        ops += 1 + W;
                    } else for (i = 0; i < W; i++) scMp[i] = 0;
                    if (x + 1 <= xmax) {
                        const u64 *fn = F + (size_t)(x + 1) * W;
                        for (i = 0; i < W; i++) scMn[i] = fn[i] & G[i];
                        ops += 1 + W;
                    } else for (i = 0; i < W; i++) scMn[i] = 0;
                    for (i = 0; i < W; i++) {
                        u64 m = scM[i], v;
                        u64 sl = (m << 1) | (i ? scM[i - 1] >> 63 : 0);
                        u64 sr = (m >> 1) | (i + 1 < W ? scM[i + 1] << 63 : 0);
                        u64 lr = (m & ~scMp[i]) | (m & ~scMn[i]);
                        v = lr & ((m & ~sl) | (m & ~sr));
                        if (!v && b->s < 0 && m) v = m & (0 - m);
                        while (v) {
                            consider(b, x, i * 64 + ctz64(v), s);
                            v &= v - 1;
                        }
                    }
                    ops += 4 * W;
                }
            }
            wi = next_word(s, wi + 1, we);
            if (wi < 0) break;
            z = fz[s][wi];
        }
    doneW:
        ops += visits * (3 + W) + 2;
        *firstOut = first;
        return;
    }
}

/*
 * Dry run: how many disjoint RBs of shape s first fit (earliest column, then
 * lowest row) finds for rows `good` in [a, d], without touching the grid.
 * Stops at k; the positions are left in dryRB.  Returns k as well when the
 * queue of own RBs would overflow (then dryRB is not usable: *exact = 0).
 */
static RB *dryRB;
#ifdef LEAN_STATS
static long long dryOps;            /* statistics: work charged by dry runs */
#endif
static int *dryQx, dryCap;          /* columns of own RBs still blocking (queue) */
static u64 *dryQ, *dryB;            /* their blocked start rows (W words each)   */

static int dry_count(int s, const u64 *good, int a, int d, int k, int *exact)
{
    int w = shW[s], h = shH[s], xmax = d - w + 1, cnt = 0, wi, we, x, qh = 0, qt = 0, i;
    long long visits = 0, work = 0;
    u64 z;
    *exact = 1;
    runs_s(scGs, good, s);
    ops += (long long)(ilog2(h) + 2) * W + 8;
#ifdef LEAN_STATS
    dryOps += (long long)(ilog2(h) + 2) * W + 8;
#endif
    if (a > xmax || is_zero(scGs)) return 0;
    wi = a >> 6; we = xmax >> 6;
    z = fz[s][wi] & (~0ULL << (a & 63));
    if (W == 1) {
        const u64 G = scGs[0], *F = fm[s];
        for (;;) {
            while (z) {
                u64 m, blk = 0;
                x = (wi << 6) + ctz64(z);
                z &= z - 1;
                if (x > xmax) goto done;
                visits++;
                m = F[x] & G;
                if (!m) continue;
                while (qh < qt && dryQx[qh] + w - 1 < x) qh++;
                for (i = qh; i < qt; i++) m &= ~dryQ[i];
                work += qt - qh;
                if (!m) continue;
                if (qt >= dryCap) { *exact = 0; cnt = k; goto done; }
                while (m && cnt < k) {
                    int y = ctz64(m), lo = y - h + 1 < 0 ? 0 : y - h + 1, hi = y + h - 1 > 63 ? 63 : y + h - 1;
                    u64 bm = (hi == 63 ? ~0ULL : ((1ULL << (hi + 1)) - 1)) & ~((1ULL << lo) - 1);
                    dryRB[cnt].h = h; dryRB[cnt].w = w; dryRB[cnt].s = s;
                    dryRB[cnt].y = y; dryRB[cnt].x = x;
                    cnt++;
                    blk |= bm;
                    m &= ~bm;
                    work += 3;
                }
                dryQx[qt] = x; dryQ[qt] = blk; qt++;
                if (cnt >= k) goto done;
            }
            wi = next_word(s, wi + 1, we);
            if (wi < 0) break;
            z = fz[s][wi];
        }
    } else {
        const u64 *G = scGs, *F = fm[s];
        for (;;) {
            while (z) {
                const u64 *f;
                int nz = 0, c;
                x = (wi << 6) + ctz64(z);
                z &= z - 1;
                if (x > xmax) goto done;
                visits++;
                f = F + (size_t)x * W;
                for (c = 0; c < W; c++) { scM[c] = f[c] & G[c]; nz |= scM[c] != 0; }
                if (!nz) continue;
                while (qh < qt && dryQx[qh] + w - 1 < x) qh++;
                for (i = qh; i < qt; i++) {
                    const u64 *q = dryQ + (size_t)i * W;
                    for (c = 0; c < W; c++) scM[c] &= ~q[c];
                }
                work += (long long)(qt - qh) * W;
                if (qt >= dryCap) { *exact = 0; cnt = k; goto done; }
                for (c = 0; c < W; c++) dryB[c] = 0;
                c = 0;
                while (cnt < k) {
                    int y, lo, hi, c2;
                    while (c < W && !scM[c]) c++;
                    if (c >= W) break;
                    y = c * 64 + ctz64(scM[c]);
                    lo = y - h + 1 < 0 ? 0 : y - h + 1;
                    hi = y + h - 1 > Y - 1 ? Y - 1 : y + h - 1;
                    row_mask(scT, lo, hi - lo + 1);   /* fills words lo>>6 .. hi>>6 */
                    for (c2 = lo >> 6; c2 <= (hi >> 6); c2++) { dryB[c2] |= scT[c2]; scM[c2] &= ~scT[c2]; }
                    dryRB[cnt].h = h; dryRB[cnt].w = w; dryRB[cnt].s = s;
                    dryRB[cnt].y = y; dryRB[cnt].x = x;
                    cnt++;
                    work += 6 + (hi >> 6) - (lo >> 6);
                }
                memcpy(dryQ + (size_t)qt * W, dryB, sizeof(u64) * (size_t)W);
                dryQx[qt] = x; qt++;
                work += W;
                if (cnt >= k) goto done;
            }
            wi = next_word(s, wi + 1, we);
            if (wi < 0) break;
            z = fz[s][wi];
        }
    }
done:
    ops += visits * (W == 1 ? 3 : 3 + W) + work + 4;
#ifdef LEAN_STATS
    dryOps += visits * (W == 1 ? 3 : 3 + W) + work + 4;
#endif
    return cnt;
}

#ifdef LEAN_STATS
static long long leanTry, leanMerged, leanRB;   /* statistics of the cheap mode */
#endif
static int leanMode;
static unsigned shDirty;        /* shapes whose masks are stale (cheap mode skips them) */
static unsigned leanKeep = ~0U; /* shapes the cheap mode keeps up to date */
static long long leanUse[MAXSH], leanUseTot;   /* cheap-mode placements per shape (this pass) */
static long long leanWork, staleWork;           /* cheap-mode work, and the part spent on stale shapes */
static int maxShW = 1;          /* widest shape */
static void refresh_shape(int s, long long lo, long long hi);            /* 1: first fit by dry runs only (cheap construction) */
static RB *tmpUn;               /* RBs merged into rectangles (marked once each) */
static int nUn, unionPlaced;

/* merge the k RBs of one shape into rectangles: runs along time in each row
   band first, then equal runs in adjacent row bands */
/*
 * Same for RBs in first-fit order (column by column, rows ascending), in one
 * pass: equal-shape RBs stacked in a column first, then runs that continue the
 * open rectangle starting on the same row.  Used for big requests.
 */
static int *unOpen, *unStamp, unCur;    /* per row: open rectangle, and when set */
static u64 *scRowsU;                    /* rows used by a request's RBs */

static void build_unions_cm(int k, int s)
{
    int i, h = shH[s], w = shW[s];
    nUn = 0;
    unCur++;
    for (i = 0; i < k;) {
        RB t = tmpRB[i];
        int j = i + 1, o;
        while (j < k && tmpRB[j].x == t.x && tmpRB[j].y == t.y + t.h) { t.h += h; j++; }
        i = j;
        o = unStamp[t.y] == unCur ? unOpen[t.y] : -1;
        if (o >= 0 && tmpUn[o].x + tmpUn[o].w == t.x && tmpUn[o].h == t.h) { tmpUn[o].w += w; continue; }
        tmpUn[nUn] = t;
        unOpen[t.y] = nUn++;
        unStamp[t.y] = unCur;
    }
}

static void build_unions(int k, int s)
{
    int i, j, m, h = shH[s];
    RB t;
    for (i = 0; i < k; i++) tmpUn[i] = tmpRB[i];
    for (i = 1; i < k; i++) {               /* insertion sort by (y, x) */
        t = tmpUn[i];
        j = i - 1;
        while (j >= 0 && (tmpUn[j].y > t.y || (tmpUn[j].y == t.y && tmpUn[j].x > t.x))) { tmpUn[j + 1] = tmpUn[j]; j--; }
        tmpUn[j + 1] = t;
    }
    nUn = 0;
    for (i = 0; i < k; i++) {                /* time runs */
        t = tmpUn[i];
        if (nUn > 0) {
            RB *p = &tmpUn[nUn - 1];
            if (p->y == t.y && p->h == t.h && p->x + p->w == t.x) { p->w += t.w; continue; }
        }
        tmpUn[nUn++] = t;
    }
    k = nUn; nUn = 0;
    for (i = 0; i < k; i++) {                /* stack equal runs of adjacent bands */
        t = tmpUn[i];
        for (m = nUn - 1; m >= 0; m--) {
            RB *p = &tmpUn[m];
            if (p->x == t.x && p->w == t.w && p->y + p->h == t.y) { p->h += h; break; }
        }
        if (m < 0) tmpUn[nUn++] = t;
    }
}

/*
 * Two shapes in turn: the first j RBs of shape sa (its first fit, columns up
 * to e), then the other k - j RBs of another shape in columns after e, by
 * first fit.  RBs of different shapes never overlap in time, so the
 * numerology rule holds.  j is the most RBs sa holds, then one fewer.
 */
static RB *mixA;                    /* first-fit RBs of the first shape */

static int try_mixed(User *u, int oi, unsigned allowed, int sa, int ca, int k)
{
    const u64 *good = u->optMask + (size_t)oi * W;
    int a = u->arr, d = u->dl, j, sb, ex, i;
    if (dry_count(sa, good, a, d, ca, &ex) < ca || !ex) return 0;
    memcpy(mixA, dryRB, sizeof(RB) * (size_t)ca);
    for (j = ca; j >= 1 && j >= ca - 1; j--) {
        long long e = (long long)mixA[j - 1].x + shW[sa] - 1;   /* columns are in order */
        for (sb = 0; sb < nsh; sb++) {
            if (sb == sa || !((allowed >> sb) & 1U) || e + shW[sb] > d) continue;
            if (dry_count(sb, good, (int)e + 1, d, k - j, &ex) < k - j || !ex) continue;
            memcpy(tmpRB, mixA, sizeof(RB) * (size_t)j);
            memcpy(tmpRB + j, dryRB, sizeof(RB) * (size_t)(k - j));
            for (i = 0; i < k; i++) {
                tmpJ[i] = jLen;
                markOnly = -1;
                mark_rb(&tmpRB[i], 1);
            }
            return 1;
        }
    }
    return 0;
}

/*
 * Try to place all RBs of option oi using a single shape for the whole
 * request (always satisfies the numerology rule, whatever "overlap" means).
 * The first RB picks the best shape among `allowed`; the rest are locked to
 * it.  Returns 1 on success (grid keeps the RBs), 0 if even the first RB
 * cannot be placed, 2 if a later RB failed (*used = the locked shape).
 */
static int try_option_shapes(User *u, int oi, unsigned allowed, int *used)
{
    const u64 *good = u->optMask + (size_t)oi * W;
    int k = u->optK[oi], a = u->arr, d = u->dl, j, s, placed = 0;
    long long need = (long long)k * S, freeCells;
    /* upper bound on free cells: whole 64-column blocks overlapping the window */
    {
        int b0 = a >> 6, b1 = d >> 6;
        long long cols = (long long)(b1 - b0 + 1) * 64;
        if (((long long)b1 << 6) + 63 > X - 1) cols -= ((long long)b1 << 6) + 63 - (X - 1);
        freeCells = cols * Y - (fen_pref(b1 + 1) - fen_pref(b0));
    }

    ops += 12 * ilog2(X + 1) + 24;
    if (freeCells < need) return 0;
    if (leanMode) {
        /* first fit without contact scoring (dry runs only): the first shape,
           in index order, that holds all k RBs */
        int ex, c, i, bs = -1;
#ifdef LEAN_STATS
        leanTry++;
#endif
        for (s = 0; s < nsh; s++) {
            if (!((allowed >> s) & 1U)) continue;
            if ((shDirty >> s) & 1U) continue;   /* rarely used by this mode: not kept */
            c = dry_count(s, good, a, d, k, &ex);
            if (c >= k && ex) { bs = s; break; }
        }
#ifndef NO_STALE_TRY
        /* the shapes not kept up to date: rebuild their masks over this window
           first, while that stays a small share of the cheap mode's work */
        for (s = 0; bs < 0 && s < nsh && staleWork * STALE_DIV < leanWork; s++) {
            long long o1 = ops;
            if (!((allowed >> s) & 1U) || !((shDirty >> s) & 1U)) continue;
            refresh_shape(s, a, (long long)d - shW[s] + 1);
            c = dry_count(s, good, a, d, k, &ex);
            staleWork += ops - o1;
            if (c >= k && ex) bs = s;
        }
#endif
        if (bs < 0) return 0;
        s = bs;
        leanUse[s]++; leanUseTot++;
        if (oi > 0) {   /* fewer RBs suffice if they all lie on rows of a cheaper option */
            int jo, r, ok, w0, w1, q;
            for (q = 0; q < W; q++) scRowsU[q] = 0;
            for (r = 0; r < k; r++) {
                w0 = dryRB[r].y >> 6; w1 = (dryRB[r].y + dryRB[r].h - 1) >> 6;
                row_mask(scRm1, dryRB[r].y, dryRB[r].h);
                for (q = w0; q <= w1; q++) scRowsU[q] |= scRm1[q];
            }
            for (jo = 0; jo < oi; jo++) {
                const u64 *gm = u->optMask + (size_t)jo * W;
                ok = 1;
                for (q = 0; q < W; q++) if (scRowsU[q] & ~gm[q]) { ok = 0; break; }
                if (ok) { k = u->optK[jo]; break; }
            }
        }
        for (i = 0; i < k; i++) tmpRB[i] = dryRB[i];
        if (k > MAX_RB) build_unions_cm(k, s);
        else build_unions(k, s);
        tmpJ[0] = jLen;
        for (i = 0; i < nUn; i++) {
            markOnly = s;
            mark_rb(&tmpUn[i], 1);
        }
        ops += (long long)(k - nUn) * UNION_RB_COST;   /* merged RBs still cost time */
#ifdef LEAN_STATS
        leanMerged += k - nUn; leanRB += k;
#endif
        unionPlaced = k;
        *used = s;
        return 1;
    }
#ifndef DRY_FILTER
#define DRY_FILTER 1
#endif
    if (DRY_FILTER && k > 1) {
        /* shapes whose first fit (dry run, nothing marked) cannot hold all k
           RBs are left out: a failed placement costs far more than this test */
        unsigned keep = 0;
        int ex, c, bestC = 0, bestS = -1;
        for (s = 0; s < nsh; s++) {
            if (!((allowed >> s) & 1U)) continue;
            c = dry_count(s, good, a, d, k, &ex);
            if (c >= k) keep |= 1U << s;
            else if (ex && c > bestC) { bestC = c; bestS = s; }
        }
        if (!keep) {
            /* no single shape holds all k RBs: two shapes in turn, if the best
               one is at most one RB short */
            if (bestS >= 0 && bestC >= k - 1 && try_mixed(u, oi, allowed, bestS, bestC, k)) {
                *used = -1;
                return 1;
            }
            return 0;
        }
        allowed = keep;
    }
    for (s = 0; s < nsh; s++) scanFrom[s] = a;

    for (j = 0; j < k; j++) {
        Best b;
        b.x = b.y = b.s = -1; b.c = -1; b.p = 1;
        if (ops > hardLimit) { undo_tmp(placed); return 0; }
        for (s = 0; s < nsh; s++)
            if ((allowed >> s) & 1U) scan_shape(s, good, a, d, &b);
        if (b.s < 0) { undo_tmp(placed); return placed ? 2 : 0; }
        tmpRB[placed].h = shH[b.s];
        tmpRB[placed].w = shW[b.s];
        tmpRB[placed].s = b.s;
        tmpRB[placed].y = b.y;
        tmpRB[placed].x = b.x;
        tmpJ[placed] = jLen;
        markOnly = b.s;                     /* other shapes' masks: once the request fits */
        mark_rb(&tmpRB[placed], 1);
        if (placed == 0) { allowed = 1U << b.s; *used = b.s; }
        placed++;
    }
    return 1;
}

static int try_option(User *u, int oi)
{
    unsigned allowed = u->optShapes[oi];
    while (allowed) {
        int used = -1, r = try_option_shapes(u, oi, allowed, &used);
        if (r == 1) return 1;
        if (r == 0 || used < 0) return 0;
        allowed &= ~(1U << used);       /* that shape could not hold all RBs */
    }
    return 0;
}

/*
 * Can at least one RB of option oi be placed anywhere in the window?
 * (stops at the first valid column; no scoring)
 */
static int probe_option(const User *u, int oi)
{
    const u64 *good = u->optMask + (size_t)oi * W;
    int s, i, x, a = u->arr, d = u->dl;
    for (s = 0; s < nsh; s++) {
        int xmax = d - shW[s] + 1, wi, we;
        const u64 *F = fm[s];
        u64 z;
        if (!((u->optShapes[oi] >> s) & 1U)) continue;
        if ((shDirty >> s) & 1U) continue;      /* stale: the cheap mode does not use it */
        if (a > xmax) continue;
        runs_s(scGs, good, s);
        ops += W * 2 + 2;
        wi = a >> 6; we = xmax >> 6;
        z = fz[s][wi] & (~0ULL << (a & 63));
        for (;;) {
            while (z) {
                const u64 *f;
                x = (wi << 6) + ctz64(z);
                z &= z - 1;
                if (x > xmax) goto nexts;
                f = F + (size_t)x * W;
                ops += 3 + W;
                for (i = 0; i < W; i++) if (f[i] & scGs[i]) return 1;
            }
            wi = next_word(s, wi + 1, we);
            if (wi < 0) break;
            z = fz[s][wi];
        }
    nexts:;
    }
    return 0;
}

static int place_user_j(User *u);
static int bigPhase;            /* 1: only the options with more than MAX_RB RBs */
static int *bigIdx, nBig;       /* requests with such options, best profit per area first */
static double *bigKeyV;         /* their profit per area (descending) */
typedef struct { double key; int id; } BigKey;
static int cmp_bigkey(const void *p, const void *q)
{
    const BigKey *a = (const BigKey *)p, *b = (const BigKey *)q;
    if (a->key != b->key) return a->key > b->key ? -1 : 1;
    return (a->id > b->id) - (a->id < b->id);
}

static int place_user(User *u)
{
    int r;
    jLen = 0; jOk = jCap > 0; jOn = jOk;
    r = place_user_j(u);
    jOn = 0; jLen = 0; markOnly = -1;
    return r;
}

/* the request fits: bring the other shapes' masks up to date for its RBs */
static void apply_deferred(int k)
{
    long long span = 0;
    int s2, r2, locked = tmpRB[0].s;
    const RB *rr = unionPlaced ? tmpUn : tmpRB;
    int nr = unionPlaced ? nUn : k;
    jOn = 0;
    markOnly = -1;
    for (s2 = 0; s2 < nsh; s2++) {
        if (!((usedSh >> s2) & 1U) || s2 == locked) continue;
        if (leanMode && !((leanKeep >> s2) & 1U)) { shDirty |= 1U << s2; continue; }
        if ((shDirty >> s2) & 1U) continue;     /* rebuilt from the occupancy when needed */
        for (r2 = 0; r2 < nr; r2++) span += mark_shape_on(&rr[r2], s2);
    }
    ops += span * (W == 1 ? 5 : 2 * W + 3);
}

static int place_user_j(User *u)
{
    int oi, o0 = bigPhase ? u->nopt : 0, o1 = bigPhase ? u->nopt + u->nbig : u->nopt;
    ops += USER_COST;                   /* per-request overhead (cache misses on its data) */
    curOwner = (int)(u - U);
    /* options are nested (later ones use a superset of rows): if not even one RB
       of the last option fits, no option can succeed */
    if (o1 - o0 > 1 && !probe_option(u, o1 - 1)) return 0;
    unionPlaced = 0;
    for (oi = o0; oi < o1; oi++) {
        if (try_option(u, oi)) {
            int k = u->optK[oi], jo, r, i;
            if (unionPlaced) k = unionPlaced;
            /* if every placed RB happens to lie on rows of a cheaper option,
               fewer RBs already satisfy the demand: drop the extra ones */
            for (jo = 0; jo < oi && !unionPlaced; jo++) {
                const u64 *gm = u->optMask + (size_t)jo * W;
                int ok = 1;
                for (r = 0; r < k && ok; r++) {
                    int w0 = tmpRB[r].y >> 6, w1 = (tmpRB[r].y + tmpRB[r].h - 1) >> 6;
                    row_mask(scRm1, tmpRB[r].y, tmpRB[r].h);
                    for (i = w0; i <= w1; i++) if (scRm1[i] & ~gm[i]) { ok = 0; break; }
                }
                if (ok) {
                    undo_range(u->optK[jo], k);
                    k = u->optK[jo];
                    break;
                }
            }
            if (u->cap < k) {
                RB *nr = (RB *)realloc(u->rbs, sizeof(RB) * (size_t)k);
                if (!nr) { undo_tmp(k); return 0; }
                u->rbs = nr;
                u->cap = k;
            }
            apply_deferred(k);
            memcpy(u->rbs, tmpRB, sizeof(RB) * (size_t)k);
            u->nrb = k;
            u->assigned = 1;
            curProfit += u->profit;
            curArea += (long long)k * S;
            return 1;
        }
    }
    return 0;
}

static void unassign(User *u)
{
    int i;
    for (i = 0; i < u->nrb; i++) mark_rb(&u->rbs[i], 0);
    u->assigned = 0;
    curProfit -= u->profit;
    curArea -= (long long)u->nrb * S;
}

/*
 * Take back every RB of the requests ids[0..n-1] at once: the cells are
 * cleared first, then the free-start masks are rebuilt once per merged
 * column span (instead of once per RB and shape).
 */
static long long *spanLo, *spanHi;
static size_t spanCap;

static void unassign_batch(const int *ids, int n)
{
    size_t ns = 0, a, m;
    int i, r, s;
    for (i = 0; i < n; i++) ns += (size_t)U[ids[i]].nrb;
    if (ns > spanCap) {
        size_t nc = ns * 2 + 64;
        long long *p1 = (long long *)realloc(spanLo, sizeof(long long) * nc);
        long long *p2 = p1 ? (long long *)realloc(spanHi, sizeof(long long) * nc) : NULL;
        if (p1) spanLo = p1;
        if (!p1 || !p2) { for (i = 0; i < n; i++) unassign(&U[ids[i]]); return; }
        spanHi = p2;
        spanCap = nc;
    }
    ns = 0;
    for (i = 0; i < n; i++) {
        User *u = &U[ids[i]];
        for (r = 0; r < u->nrb; r++) {
            const RB *b = &u->rbs[r];
            long long lo = b->x, hi = (long long)b->x + b->w - 1;
            size_t q = ns++;
            mark_raw(b, 0);
            ops += (long long)b->w * (4 + W + (useOwn && ownLive ? b->h : 0)) + W + MARK_COST;
            while (q > 0 && spanLo[q - 1] > lo) {       /* insertion sort by start */
                spanLo[q] = spanLo[q - 1]; spanHi[q] = spanHi[q - 1]; q--;
                ops++;
            }
            spanLo[q] = lo; spanHi[q] = hi;
        }
        u->assigned = 0;
        curProfit -= u->profit;
        curArea -= (long long)u->nrb * S;
    }
    for (a = 0; a < ns; a = m) {
        long long lo = spanLo[a], hi = spanHi[a];
        for (m = a + 1; m < ns && spanLo[m] <= hi + 8; m++) if (spanHi[m] > hi) hi = spanHi[m];
        for (s = 0; s < nsh; s++)
            if ((usedSh >> s) & 1U) refresh_shape(s, lo - shW[s] + 1, hi);
    }
}

/* ---------- options ---------- */

static const long long *curBits;
static int *scIdx;
static int *tK;
static u64 *tMask;
static unsigned *tSh;
static u64 *sortA, *sortB;      /* scratch for sorting rows */

static int cmp_bits_desc(const void *p, const void *q)
{
    long long a = curBits[*(const int *)p], b = curBits[*(const int *)q];
    if (a != b) return a > b ? -1 : 1;
    return *(const int *)p - *(const int *)q;
}

/* longest run of ones in one word */
static int run_len64(u64 v)
{
    u64 r[7], cur = ~0ULL;
    int j, len = 0;
    if (!v) return 0;
    if (v == ~0ULL) return 64;
    r[0] = v;
    for (j = 1; j < 7; j++) r[j] = r[j - 1] & (r[j - 1] >> (1 << (j - 1)));
    /* r[j]: positions starting a run of at least 2^j ones */
    for (j = 5; j >= 0; j--) {
        u64 cand = cur & (r[j] >> len);
        if (cand) { cur = cand; len += 1 << j; }
    }
    return len;
}

/* shapes that fit: h <= longest run of usable rows, w <= window length */
static unsigned shapes_fit(const u64 *g, int L)
{
    unsigned sm = 0;
    int s, i, carry = 0, best = 0;
    for (i = 0; i < W; i++) {
        u64 v = g[i];
        int lead, top, in;
        if (v == ~0ULL) { carry += 64; if (carry > best) best = carry; continue; }
        if (!v) { carry = 0; continue; }
        lead = ctz64(~v);                   /* ones continuing the previous word */
        if (carry + lead > best) best = carry + lead;
        in = run_len64(v);
        if (in > best) best = in;
        top = 0;                            /* ones reaching the top bit */
        while (top < 64 && ((v >> (63 - top)) & 1ULL)) top++;
        carry = top;
    }
    for (s = 0; s < nsh; s++)
        if (shW[s] <= L && shH[s] <= best) sm |= 1U << s;
    return sm;
}

/* store an option into slot o of the temporary arrays */
static void keep_option(int o, int k, const u64 *g, unsigned sm)
{
    tK[o] = k;
    memcpy(tMask + (size_t)o * W, g, sizeof(u64) * (size_t)W);
    tSh[o] = sm;
}

/* chunked bump allocator for the many small per-user arrays (pointers stay valid) */
static char *arenaCur;
static size_t arenaLeft;

static void *arena_alloc(size_t n)
{
    void *p;
    n = (n + 7) & ~(size_t)7;
    if (n > arenaLeft) {
        size_t chunk = n > ((size_t)1 << 24) ? n : ((size_t)1 << 24);
        arenaCur = (char *)malloc(chunk);
        if (!arenaCur) { arenaLeft = 0; return NULL; }
        arenaLeft = chunk;
    }
    p = arenaCur;
    arenaCur += n;
    arenaLeft -= n;
    return p;
}

/* store the kept options of one user (nkeep > 0) */
static void store_options(User *u, int nkeep, int nbig)
{
    int nt = nkeep + nbig;
    char *mem = (char *)arena_alloc((sizeof(int) + sizeof(unsigned)) * (size_t)nt + 8 + sizeof(u64) * (size_t)nt * W);
    if (!mem) return;
    u->optMask = (u64 *)mem;
    u->optK = (int *)(mem + sizeof(u64) * (size_t)nt * W);
    u->optShapes = (unsigned *)(mem + sizeof(u64) * (size_t)nt * W + sizeof(int) * (size_t)nt);
    memcpy(u->optK, tK, sizeof(int) * (size_t)nt);
    memcpy(u->optMask, tMask, sizeof(u64) * (size_t)nt * W);
    memcpy(u->optShapes, tSh, sizeof(unsigned) * (size_t)nt);
    u->nopt = nkeep;
    u->nbig = nbig;
    u->minArea = nkeep ? (long long)u->optK[0] * S : 0;
}

/* shapes that fit rows v (one word) and window length L */
static unsigned shapes_fit1(u64 v, int L)
{
    unsigned sm = 0;
    int s, best = run_len64(v);
    for (s = 0; s < nsh; s++)
        if (shW[s] <= L && shH[s] <= best) sm |= 1U << s;
    return sm;
}

/*
 * build_options for Y <= 64: same options as the general code, with the rows
 * kept in one word and the thresholds taken from packed (bits, row) keys.
 * Returns 0 if some value is too large to pack (the general code is used).
 */
static u64 valRows[64];         /* rows per small bit value (kept all-zero between calls) */

static int build_options1(User *u, const long long *bits, int L)
{
    u64 key[64], g = 0, pendM = 0, tailM = 0, present = 0, bigM1 = 0, bigM2 = 0;
    int n = 0, y, a2, p, nkeep = 0, pend = 0, tailValid = 0, small = 1, nb = 0;
    long long q, pendK = 0, tailK = 0, bigK1 = 0, bigK2 = 0;
    for (y = 0; y < Y; y++) {
        long long b = bits[y];
        if (b <= 0) continue;
        if (b >= (1LL << 56)) return 0;
        if (b > 63) small = 0;
        key[n++] = ((u64)b << 6) | (u64)(63 - y);
    }
    if (!n) return 1;
    if (small) {
        /* bucket by value: only the groups matter, not the order inside them */
        for (a2 = 0; a2 < n; a2++) {
            int b = (int)(key[a2] >> 6);
            valRows[b] |= 1ULL << (63 - (int)(key[a2] & 63));
            present |= 1ULL << b;
        }
        {
            int vals[64], nv = 0;
            while (present) { vals[nv++] = ctz64(present); present &= present - 1; }
            n = 0;
            while (nv > 0) {                            /* highest value first */
                int b = vals[--nv];
                u64 r = valRows[b];
                valRows[b] = 0;
                while (r) {
                    int t = ctz64(r);
                    r &= r - 1;
                    key[n++] = ((u64)b << 6) | (u64)(63 - t);
                }
            }
        }
    } else {
        for (a2 = 1; a2 < n; a2++) {          /* insertion sort, descending */
            u64 v = key[a2];
            int b2 = a2 - 1;
            while (b2 >= 0 && key[b2] < v) { key[b2 + 1] = key[b2]; b2--; }
            key[b2 + 1] = v;
        }
    }
    q = u->dem <= 0 ? 1 : u->dem / S + (u->dem % S != 0);   /* ceil(D/S) */
    for (p = 0; p <= n;) {
        long long b, k;
        int last = (p == n);
        if (!last) {
            b = (long long)(key[p] >> 6);
            while (p < n && (long long)(key[p] >> 6) == b) {
                g |= 1ULL << (63 - (int)(key[p] & 63));
                p++;
            }
            if (q < (1LL << 50) && b < (1LL << 50)) {     /* ceil(q/b) without a 64-bit divide */
                k = (long long)((double)q / (double)b);
                while (k * b < q) k++;
                while (k > 0 && (k - 1) * b >= q) k--;
            } else k = q / b + (q % b != 0);
            if (k < 1) k = 1;
            if (k > MAX_RB && k <= BIG_RB && k * S <= (long long)L * p) {
                /* more RBs than the normal passes allow: the first such k (fewest
                   RBs) and the last one (most rows), each with its widest rows */
                if (nb == 0 || k == bigK1) { bigK1 = k; bigM1 = g; nb = 1; }
                else { bigK2 = k; bigM2 = g; nb = 2; }
            }
            if (k > MAX_RB || k * S > (long long)L * p) continue;
        } else {
            k = -1;
            p++;
        }
        if (pend && k != pendK) {
            if (nkeep < maxOpt - 1) {
                unsigned sm = shapes_fit1(pendM, L);
                if (sm) { tK[nkeep] = (int)pendK; tMask[nkeep] = pendM; tSh[nkeep] = sm; nkeep++; }
            } else {
                tailValid = 1;
                tailK = pendK;
                tailM = pendM;
            }
        }
        if (last) break;
        pendK = k;
        pend = 1;
        pendM = g;
    }
    if (tailValid) {
        unsigned sm = shapes_fit1(tailM, L);
        if (sm && (nkeep == 0 || tailK > tK[nkeep - 1])) { tK[nkeep] = (int)tailK; tMask[nkeep] = tailM; tSh[nkeep] = sm; nkeep++; }
    }
    {
        int nbk = 0;
        unsigned sm;
        if (nb >= 1 && (sm = shapes_fit1(bigM1, L)) != 0) { tK[nkeep] = (int)bigK1; tMask[nkeep] = bigM1; tSh[nkeep] = sm; nbk++; }
        if (nb >= 2 && (sm = shapes_fit1(bigM2, L)) != 0) { tK[nkeep + nbk] = (int)bigK2; tMask[nkeep + nbk] = bigM2; tSh[nkeep + nbk] = sm; nbk++; }
        if (nkeep || nbk) store_options(u, nkeep, nbk);
    }
    return 1;
}

static void build_options(User *u, const long long *bits)
{
    int L, cnt = 0, p, y, nkeep = 0, pend = 0, tailValid = 0, i, nb = 0;
    long long q, pendK = 0, tailK = 0, bigK1 = 0, bigK2 = 0;

    u->nopt = 0;
    u->nbig = 0;
    if (u->profit <= 0 || nsh == 0 || u->arr > u->dl) return;
    L = u->dl - u->arr + 1;
    if (W == 1 && build_options1(u, bits, L)) return;
    for (y = 0; y < Y; y++) if (bits[y] > 0) scIdx[cnt++] = y;
    if (!cnt) return;
    curBits = bits;
    if (cnt <= 64) {                    /* insertion sort: same order, no call overhead */
        int a2, b2;
        for (a2 = 1; a2 < cnt; a2++) {
            int v2 = scIdx[a2];
            b2 = a2 - 1;
            while (b2 >= 0 && (bits[scIdx[b2]] < bits[v2] || (bits[scIdx[b2]] == bits[v2] && scIdx[b2] > v2))) {
                scIdx[b2 + 1] = scIdx[b2];
                b2--;
            }
            scIdx[b2 + 1] = v2;
        }
    } else {
        /* many rows: sort packed keys (bits desc, row asc) unless bits are huge */
        int a2, big = Y >= (1 << 20);
        for (a2 = 0; a2 < cnt && !big; a2++) if (bits[scIdx[a2]] >= (1LL << 42)) big = 1;
        if (big) qsort(scIdx, (size_t)cnt, sizeof(int), cmp_bits_desc);
        else {
            u64 *ka = sortA, *kb = sortB, *kt;
            int width;
            for (a2 = 0; a2 < cnt; a2++)
                ka[a2] = ((u64)bits[scIdx[a2]] << 20) | (u64)(0xFFFFF - scIdx[a2]);
            for (width = 1; width < cnt; width *= 2) {
                int i0;
                for (i0 = 0; i0 < cnt; i0 += 2 * width) {
                    int mid = i0 + width < cnt ? i0 + width : cnt;
                    int hi = i0 + 2 * width < cnt ? i0 + 2 * width : cnt;
                    int p = i0, q = mid, k = i0;
                    while (p < mid && q < hi) kb[k++] = ka[p] > ka[q] ? ka[p++] : ka[q++];
                    while (p < mid) kb[k++] = ka[p++];
                    while (q < hi) kb[k++] = ka[q++];
                }
                kt = ka; ka = kb; kb = kt;
            }
            for (a2 = 0; a2 < cnt; a2++) scIdx[a2] = 0xFFFFF - (int)(ka[a2] & 0xFFFFF);
        }
    }
    q = u->dem <= 0 ? 1 : u->dem / S + (u->dem % S != 0);   /* ceil(D/S) */
    for (i = 0; i < W; i++) scG[i] = 0;

    /* sweep thresholds from high to low: rows only grow, k only grows */
    for (p = 0; p <= cnt;) {
        long long b, k, rows;
        int last = (p == cnt);
        if (!last) {
            b = bits[scIdx[p]];
            while (p < cnt && bits[scIdx[p]] == b) {
                y = scIdx[p];
                scG[y >> 6] |= 1ULL << (y & 63);
                p++;
            }
            rows = p;
            k = q / b + (q % b != 0);
            if (k < 1) k = 1;
            if (k > MAX_RB && k <= BIG_RB && k <= ((long long)L * rows) / S) {
                if (nb == 0 || k == bigK1) { bigK1 = k; memcpy(scBig1, scG, sizeof(u64) * (size_t)W); nb = 1; }
                else { bigK2 = k; memcpy(scBig2, scG, sizeof(u64) * (size_t)W); nb = 2; }
            }
            if (k > ((long long)L * rows) / S || k > MAX_RB) continue;
        } else {
            k = -1;
            p++;
        }
        if (pend && k != pendK) {
            /* finalise the previous group: the largest row set for its k */
            if (nkeep < maxOpt - 1) {
                unsigned sm = shapes_fit(scPend, L);
                if (sm) keep_option(nkeep++, (int)pendK, scPend, sm);
            } else {
                tailValid = 1;          /* candidate for the last slot */
                tailK = pendK;
                memcpy(scTail, scPend, sizeof(u64) * (size_t)W);
            }
        }
        if (last) break;
        pendK = k;
        pend = 1;
        memcpy(scPend, scG, sizeof(u64) * (size_t)W);
    }
    if (tailValid) {
        unsigned sm = shapes_fit(scTail, L);
        if (sm && (nkeep == 0 || tailK > tK[nkeep - 1])) keep_option(nkeep++, (int)tailK, scTail, sm);
    }
    {
        int nbk = 0;
        unsigned sm;
        if (nb >= 1 && (sm = shapes_fit(scBig1, L)) != 0) keep_option(nkeep + nbk++, (int)bigK1, scBig1, sm);
        if (nb >= 2 && (sm = shapes_fit(scBig2, L)) != 0) keep_option(nkeep + nbk++, (int)bigK2, scBig2, sm);
        if (!nkeep && !nbk) return;
        store_options(u, nkeep, nbk);
    }
}

/* ---------- priorities ---------- */

static const double alphaV[NVAR] = {1.0, 0.8, 1.25, 0.6, 1.6, 1.0, 1.0, 1.0, 1.0};
#define NVAR_LNS 6                  /* orders 6..8 are construction-only */

/* natural log for x > 0, without libm */
static double my_log(double x)
{
    double k = 0.0, t, t2, sum = 0.0, term;
    int n;
    while (x > 2.0) { x *= 0.5; k += 1.0; }
    while (x < 1.0) { x *= 2.0; k -= 1.0; }
    t = (x - 1.0) / (x + 1.0);          /* ln x = 2 atanh(t) */
    t2 = t * t;
    term = t;
    for (n = 1; n < 40; n += 2) { sum += term / n; term *= t2; }
    return 2.0 * sum + k * 0.69314718055994530942;
}

/* e^x without libm */
static double my_exp(double x)
{
    double r = 1.0, term = 1.0;
    int n, k = 0;
    while (x > 0.5) { x *= 0.5; k++; }
    while (x < -0.5) { x *= 0.5; k++; }
    for (n = 1; n < 30; n++) { term *= x / n; r += term; }
    while (k-- > 0) r *= r;
    return r;
}

static double user_key(const User *u, int v)
{
    double base;
    if (u->nopt <= 0 || u->minArea <= 0) return -1.0;   /* never assignable */
    if (alphaV[v] == 1.0) base = (double)u->profit / (double)u->minArea;
    else base = (double)u->profit / my_exp(alphaV[v] * my_log((double)u->minArea));
    if (v == 6) return 4e9 - (double)u->dl + base / (1.0 + base);    /* earliest deadline first */
    if (v == 7) return 4e9 - (double)u->arr + base / (1.0 + base);   /* earliest arrival first */
    if (v == 8) return (double)u->profit + base / (1.0 + base);      /* highest profit first */
    if (v == 5) {   /* density, favouring tight windows */
        double L = (double)u->dl - u->arr + 1;
        base *= 1.0 + (double)u->minArea / (L * Y);
    }
    return base;
}

#if 0
static int cmp_order(const void *p, const void *q)
{
    int a = *(const int *)p, b = *(const int *)q;
    double ka = keyBuf[a], kb = keyBuf[b];
    if (ka > kb) return -1;
    if (ka < kb) return 1;
    if (U[a].dl != U[b].dl) return U[a].dl < U[b].dl ? -1 : 1;
    return (a > b) - (a < b);
}
#endif

/*
 * Same order as cmp_order (key descending, then deadline ascending, then index
 * ascending), computed with stable LSD radix sorts instead of qsort: sequential
 * passes are far cheaper than a comparator chasing scattered memory.
 */
typedef struct { u64 k; int id; } KeyId;
static KeyId *rsA, *rsB;

static void radix_pass(KeyId *src, KeyId *dst, int n, int shift)
{
    int cnt[257], i;
    memset(cnt, 0, sizeof(cnt));
    for (i = 0; i < n; i++) cnt[((src[i].k >> shift) & 255) + 1]++;
    for (i = 0; i < 256; i++) cnt[i + 1] += cnt[i];
    for (i = 0; i < n; i++) dst[cnt[(src[i].k >> shift) & 255]++] = src[i];
}

static u64 desc_bits(double d)          /* larger double -> smaller key */
{
    u64 b;
    memcpy(&b, &d, sizeof(b));
    b = (b >> 63) ? ~b : (b | 0x8000000000000000ULL);   /* ascending-sortable */
    return ~b;
}

static void radix_order(int *out)
{
    int i, p;
    KeyId *a = rsA, *b = rsB, *t;
    for (i = 0; i < N; i++) { a[i].k = (u64)((long long)U[i].dl + 2147483648LL); a[i].id = i; }
    for (p = 0; p < 32; p += 8) { radix_pass(a, b, N, p); t = a; a = b; b = t; }
    for (i = 0; i < N; i++) a[i].k = desc_bits(keyBuf[a[i].id]);
    for (p = 0; p < 64; p += 8) { radix_pass(a, b, N, p); t = a; a = b; b = t; }
    for (i = 0; i < N; i++) out[i] = a[i].id;
}

/* ---------- local search ---------- */

static int *candList, *addList, *remList, *remStart, *remCnt;
static char *inRem;
static RB *pool;
static size_t poolCap;
static int curVar;
static int unsortedArr;     /* 1 if arrival is not nondecreasing by index */
static int ry0, ry1;        /* row range of the current ruin region       */

static int cmp_rank(const void *p, const void *q)
{
    int a = rankv[curVar][*(const int *)p], b = rankv[curVar][*(const int *)q];
    return (a > b) - (a < b);
}

static int intersects(const User *u, int t0, int t1)
{
    int i;
    for (i = 0; i < u->nrb; i++) {
        const RB *r = &u->rbs[i];
        if (r->x <= t1 && (long long)r->x + r->w - 1 >= t0 &&
            r->y <= ry1 && (long long)r->y + r->h - 1 >= ry0) return 1;
    }
    return 0;
}

/* returns 1 if a strictly better state was reached */
static int *ulist[NVAR], ulen[NVAR];   /* unassigned users per priority order */
static long long maxWin, lnsLavg = 1;   /* longest / average request window */
static long long lnsSteps;

#ifndef ULIST_AGE
#define ULIST_AGE (512 + N / 200)        /* refills between rebuilds of an unassigned list */
#endif
static long long ulistAgeV[NVAR];
static int ulistInit;

/* unassigned users of priority order v (rebuilt lazily, one order at a time) */
static void rebuild_ulist(int v)
{
    int i;
    ulen[v] = 0;
    for (i = 0; i < N; i++) {
        int id = order[v][i];
        if (U[id].nopt <= 0) break;
        if (!U[id].assigned) ulist[v][ulen[v]++] = id;
    }
    ops += (long long)i * 24 + 16;      /* scattered reads of U: cache misses */
}
#ifndef REG_USERS
#define REG_USERS 256               /* largest region: about this many average requests */
#endif
#ifndef LNS_EXTRA
#define LNS_EXTRA 24                /* refill candidates: the removed requests and this many more */
#endif
#ifndef SA_EXTRA
#define SA_EXTRA 24                 /* the same in the threshold phase */
#endif
#ifndef LDS_STALL
#define LDS_STALL 10                /* no gain for 1/LDS_STALL of the search budget: stalled */
#endif
#ifndef LDS_MAX
#define LDS_MAX 48                  /* refills of at most this many requests try one discrepancy */
#endif
static int skipIds[LDS_MAX + 1];
static long long ldsHits;
static int ldsOn;               /* the plain search has stalled: refills try a discrepancy */
static long long lastImpOps;    /* when the local search last improved */
static long long lnsStart, lnsStall;    /* start of the local search; no gain this long = stalled */
static long long lastImpStep, passSteps = -1;   /* steps: at the last gain, in one pass of every class */

static long long allProfit = -1;    /* profit of every request that has an option */

/* after every local search step: nothing is left to gain once everybody is served */
static void lns_check(void)
{
    if (curProfit >= allProfit && allProfit >= 0) opsEnd = ops;
}

/*
 * Threshold phase, entered once the sweep (with one discrepancy) has stalled.
 * Everything is deterministic:
 *   - the sweep goes on over the same regions,
 *   - refill orders are enumerated in a fixed cycle: log(profit) -
 *     alpha * log(smallest area) for a table of alpha values, with the j-th
 *     candidate moved to the front (j = 0, 1, 2, ... in turn),
 *   - a refill that loses at most the current threshold is kept (threshold
 *     accepting); the threshold falls to zero by the end of the budget.  The
 *     best solution seen is kept aside and is the answer.
 */
static int saOn;                    /* threshold phase active                */
static double saThr;                /* largest profit loss kept now          */
static double saAlpha = 1.0;        /* refill order of this step             */
static long long saPromote;         /* candidate moved to the front          */
static float *lpU, *laU;            /* log profit, log smallest area         */
static long long bestP = -1, bestA; /* best solution of the threshold phase  */
static int bestIsCur = 1;           /* the current solution is the best one  */
typedef struct { double k; int id; } SaKey;
static SaKey *saBuf;

static int cmp_sakey(const void *p, const void *q)
{
    const SaKey *a = (const SaKey *)p, *b = (const SaKey *)q;
    if (a->k != b->k) return a->k > b->k ? -1 : 1;
    return (a->id > b->id) - (a->id < b->id);
}

#ifndef SA_ALLOW
#define SA_ALLOW 1
#endif
static int sa_keep_worse(long long oldP, long long oldA, int nr, int na);
static int saAllowed = SA_ALLOW;

/* no gain for a long share of the budget, or for two full passes of the
   sweep over every region */
static int is_stalled(void)
{
    return ops - lastImpOps > lnsStall || (passSteps > 0 && lnsSteps - lastImpStep > 2 * passSteps);
}

/* the sweep has gone a while without gain: first try one discrepancy per
   refill, then (if that stalls too) the threshold phase */
static void stalled(void)
{
    if (!ldsOn) { ldsOn = 1; lastImpOps = ops; lastImpStep = lnsSteps; }
    else if (saAllowed) saOn = 1;
}

#ifdef DIAG
long long dgSteps, dgNr, dgNc, dgNa, dgImp, dgEq, dgWorse;
#endif
static int lns_step(int t0, int t1, int v)
{
    long long oldP = curProfit, oldA = curArea;
    int nr = 0, nc = 0, na = 0, i, j, lim, hi;
    size_t pu = 0;

    /* users with arrival <= t1 form a prefix when arrivals are sorted */
    {
        int lo = 0, h2 = N;
        while (lo < h2) { int md = lo + (h2 - lo) / 2; if (U[md].arr <= t1) lo = md + 1; else h2 = md; }
        hi = unsortedArr ? N : lo;
    }
    if (useOwn) {
        /* owners of the cells inside the region */
        int x, y;
        for (x = t0; x <= t1; x++) {
            const int *o = own + (size_t)x * Y;
            for (y = ry0; y <= ry1; y++) {
                int id = o[y];
                if (id >= 0 && !inRem[id]) { inRem[id] = 1; remList[nr++] = id; }
            }
        }
        ops += (long long)(t1 - t0 + 1) * (ry1 - ry0 + 1) / 2 + 16;
    } else {
        for (i = 0; i < hi; i++) {
            User *u = &U[i];
            if (u->assigned && u->dl >= t0 && intersects(u, t0, t1)) { remList[nr++] = i; inRem[i] = 1; }
        }
        ops += 6LL * hi;
    }
    for (i = 0; i < nr; i++) {
        User *u = &U[remList[i]];
        if (pu + (size_t)u->nrb > poolCap) {
            size_t nc2 = (pu + (size_t)u->nrb) * 2;
            RB *np = (RB *)realloc(pool, sizeof(RB) * nc2);
            if (!np) {              /* cannot back up: leave the region as it is */
                for (j = 0; j < nr; j++) inRem[remList[j]] = 0;
                return 0;
            }
            pool = np;
            poolCap = nc2;
        }
        memcpy(pool + pu, u->rbs, sizeof(RB) * (size_t)u->nrb);
        remStart[i] = (int)pu; remCnt[i] = u->nrb; pu += (size_t)u->nrb;
        candList[nc++] = remList[i];
    }
    unassign_batch(remList, nr);
    lim = nr + (saOn ? SA_EXTRA : LNS_EXTRA);
    if (!unsortedArr) {
        /* users that can intersect [t0, t1] have arrival in [t0 - maxWin, t1] */
        int lo = 0, h2 = N;
        long long from = (long long)t0 - maxWin;
        while (lo < h2) { int md = lo + (h2 - lo) / 2; if (U[md].arr < from) lo = md + 1; else h2 = md; }
        /* scan the arrival range (sequential) unless walking the unassigned list
           (scattered reads; about one in X / (region + window) entries fits) is cheaper */
        if ((double)(hi - lo) <= 8.0 * lim * (double)X / ((double)(t1 - t0 + 1) + (double)lnsLavg) + 2000.0) {
            int base = nc;
            for (i = lo; i < hi; i++) {
                User *u = &U[i];
                if (u->nopt <= 0 || u->assigned || inRem[i] || u->dl < t0) continue;
                candList[nc++] = i;
            }
            ops += 4LL * (hi - lo);
            if (nc - base > lim) {          /* keep the best `lim` by rank (heap selection) */
                int *hp = candList + base, n2 = nc - base, hn = 0, t, c, p2;
                const int *rk = rankv[v];
                for (t = 0; t < n2; t++) {
                    int id = hp[t];
                    if (hn < lim) {                     /* push into max-heap by rank */
                        c = hn++;
                        while (c > 0 && rk[hp[(p2 = (c - 1) / 2)]] < rk[id]) { hp[c] = hp[p2]; c = p2; }
                        hp[c] = id;
                    } else if (rk[id] < rk[hp[0]]) {    /* replace the worst kept */
                        c = 0;
                        for (;;) {
                            int l = 2 * c + 1, r = l + 1, m = c, mr = rk[id];
                            if (l < hn && rk[hp[l]] > mr) { m = l; mr = rk[hp[l]]; }
                            if (r < hn && rk[hp[r]] > mr) m = r;
                            if (m == c) break;
                            hp[c] = hp[m]; c = m;
                        }
                        hp[c] = id;
                    }
                }
                ops += (long long)n2 * 3;
                nc = base + hn;
            }
            lim = 0;
        }
    }
    if (lim > 0) {
        /* walk the cached unassigned list of this priority order */
        int *ul;
        if (!ulistInit) { int v2; for (v2 = 0; v2 < NVAR; v2++) ulistAgeV[v2] = -1; ulistInit = 1; }
        if (ulistAgeV[v] < 0 || lnsSteps - ulistAgeV[v] >= ULIST_AGE) { rebuild_ulist(v); ulistAgeV[v] = lnsSteps; }
        ul = ulist[v];
        for (i = 0; i < ulen[v] && lim > 0; i++) {
            int id = ul[i];
            User *u = &U[id];
            ops += 8;
            if (u->assigned || inRem[id]) continue;
            if (u->arr > t1 || u->dl < t0) continue;
            candList[nc++] = id;
            lim--;
        }
    }
    ops += 64;
    lnsSteps++;
    for (i = 0; i < nr; i++) inRem[remList[i]] = 0;
    curVar = v;
    if (saOn && saBuf) {
        for (i = 0; i < nc; i++) {
            int id = candList[i];
            saBuf[i].k = (double)lpU[id] - saAlpha * (double)laU[id];
            saBuf[i].id = id;
        }
        qsort(saBuf, (size_t)nc, sizeof(SaKey), cmp_sakey);
        if (nc > 1 && saPromote % nc) {        /* candidate j first, the others keep their order */
            SaKey t = saBuf[saPromote % nc];
            for (j = (int)(saPromote % nc); j > 0; j--) saBuf[j] = saBuf[j - 1];
            saBuf[0] = t;
        }
        for (i = 0; i < nc; i++) candList[i] = saBuf[i].id;
        ops += 20LL * nc;
    } else qsort(candList, (size_t)nc, sizeof(int), cmp_rank);
    for (i = 0; i < nc && ops <= hardLimit; i++)
        if (place_user(&U[candList[i]])) addList[na++] = candList[i];

#ifdef DIAG
    {
        extern long long dgSteps, dgNr, dgNc, dgNa, dgImp, dgEq;
        dgSteps++; dgNr += nr; dgNc += nc; dgNa += na;
        if (curProfit > oldP || (curProfit == oldP && curArea < oldA)) dgImp++;
        else if (curProfit == oldP && curArea == oldA) dgEq++;
    }
#endif
    /* keep: more profit, or equal profit with no more area */
    if (curProfit > oldP || (curProfit == oldP && curArea <= oldA)) {
        if (curProfit > oldP || curArea < oldA) { lastImpOps = ops; lastImpStep = lnsSteps; }
        if (saOn && (curProfit > bestP || (curProfit == bestP && curArea < bestA))) {
            bestP = curProfit; bestA = curArea; bestIsCur = 1;
        }
        return curProfit > oldP || curArea < oldA;
    }
    if (saOn && sa_keep_worse(oldP, oldA, nr, na)) return 0;
#ifdef LDS_MAX
    /* one discrepancy: leave out one of the requests the refill placed, so
       that others may fit instead; the first strict improvement is kept */
#ifndef SA_LDS
#define SA_LDS 0
#endif
    if (ldsOn && (SA_LDS || !saOn) && nc <= LDS_MAX) {
        int na0 = na, q;
        for (q = 0; q < na0; q++) skipIds[q] = addList[q];
        for (q = 0; q < na0 && ops <= hardLimit; q++) {
            unassign_batch(addList, na);
            na = 0;
            for (i = 0; i < nc && ops <= hardLimit; i++) {
                if (candList[i] == skipIds[q]) continue;
                if (place_user(&U[candList[i]])) addList[na++] = candList[i];
            }
            if (curProfit > oldP || (curProfit == oldP && curArea < oldA)) { ldsHits++; lastImpOps = ops; lastImpStep = lnsSteps; return 1; }
        }
    }
#endif

    unassign_batch(addList, na);
    for (i = 0; i < nr; i++) {
        User *u = &U[remList[i]];
        memcpy(u->rbs, pool + remStart[i], sizeof(RB) * (size_t)remCnt[i]);
        u->nrb = remCnt[i];
        u->assigned = 1;
        curProfit += u->profit;
        curArea += (long long)u->nrb * S;
        curOwner = remList[i];
        for (j = 0; j < u->nrb; j++) mark_rb(&u->rbs[j], 1);
    }
    return 0;
}

/*
 * Masks of shape s for start columns lo..hi, recomputed from the occupancy
 * (in pieces that fit the scratch buffers).
 */
static void refresh_shape(int s, long long lo, long long hi)
{
    long long step = 2LL * maxShW + 64, x;
    int j0 = jOn;
    if (lo < 0) lo = 0;
    if (hi > (long long)X - shW[s]) hi = (long long)X - shW[s];
    jOn = 0;                            /* never undone */
    for (x = lo; x <= hi; x += step) fz_update(s, x, x + step - 1 > hi ? hi : x + step - 1);
    jOn = j0;
}

/* bring every stale mask up to date (before anything but the cheap mode reads them) */
static void refresh_dirty(void)
{
    int s;
    for (s = 0; s < nsh; s++)
        if ((shDirty >> s) & 1U) refresh_shape(s, 0, (long long)X - 1);
    shDirty = 0;
}

/* shapes the cheap mode keeps up to date: those it used for at least 2% of its
   placements in this pass (all of them until it has placed 1/16 of the requests:
   the leading requests are the most valuable ones) */
static void update_lean_keep(int nAss)
{
    unsigned keep = 0;
    int s;
    if (leanUseTot < 256 || leanUseTot < nAss / 16) return;
    for (s = 0; s < nsh; s++)
        if (leanUse[s] * 50 >= leanUseTot) keep |= 1U << s;
    for (s = 0; s < nsh; s++)
        if (((keep & shDirty) >> s) & 1U) {   /* needed again: rebuild it */
            refresh_shape(s, 0, (long long)X - 1);
            shDirty &= ~(1U << s);
        }
    leanKeep = keep;
}

static void clear_all(void)
{
    int i;
    for (i = 0; i < N; i++) U[i].assigned = 0;
    shDirty = 0;
    for (i = 0; i < nlev; i++) memset(lev[i], 0, sizeof(u64) * (size_t)X * W);
    memset(fen, 0, sizeof(long long) * ((size_t)nBlk + 1));
    if (useRow) memset(rowOcc, 0, sizeof(u64) * (size_t)Y * fzWords);
    if (useOwn && ownLive) { size_t c2, nc2 = (size_t)X * Y; for (c2 = 0; c2 < nc2; c2++) own[c2] = -1; }
    ops += (long long)X * W * 2 + (long long)N;
    for (i = 0; i < nsh; i++) {
        int x;
        if (!((usedSh >> i) & 1U)) continue;
        ops += (long long)X * W;
        {
            int xm = X - shW[i], c;       /* starts 0..xm are free on an empty grid */
            u64 *F = fm[i];
            memset(fz[i], 0, sizeof(u64) * (size_t)fzWords);
            runs(scMm, scAll, shH[i]);
            if (W == 1) {
                u64 v = scMm[0];
                for (x = 0; x <= xm; x++) F[x] = v;
                for (; x <= X; x++) F[x] = 0;
            } else {
                for (x = 0; x <= xm; x++)
                    for (c = 0; c < W; c++) F[(size_t)x * W + c] = scMm[c];
                memset(F + (size_t)(xm + 1) * W, 0, sizeof(u64) * (size_t)(X - xm) * W);
            }
            for (x = 0; x + 63 <= xm; x += 64) fz[i][x >> 6] = ~0ULL;
            for (; x <= xm; x++) fz[i][x >> 6] |= 1ULL << (x & 63);
        }
        memset(fzs[i], 0, sizeof(u64) * (size_t)fzsWords);
        fzs_fix(i, 0, fzWords - 1);
    }
    curProfit = 0; curArea = 0;
}

/* owner grid from the users' RBs */
static void rebuild_owner(void)
{
    size_t c2, nc2 = (size_t)X * Y;
    int i, r, c, yy;
    for (c2 = 0; c2 < nc2; c2++) own[c2] = -1;
    for (i = 0; i < N; i++) {
        const User *u = &U[i];
        if (!u->assigned) continue;
        for (r = 0; r < u->nrb; r++) {
            const RB *rb = &u->rbs[r];
            for (c = rb->x; c < rb->x + rb->w; c++) {
                int *o = own + (size_t)c * Y + rb->y;
                for (yy = 0; yy < rb->h; yy++) o[yy] = i;
            }
        }
    }
    ops += (long long)(nc2 / 4) + (long long)N;
}

/* ---------- solution snapshot ---------- */

static char *snapA;
static int *snapCnt;
static size_t *snapStart;
static RB *snapPool;
static size_t snapCap, snapUsed;
static long long snapP = -1, snapArea;
static int snapOut;          /* 1: the answer is the snapshot (grid not restored) */

static void save_snapshot(void)
{
    size_t used = 0;
    int i;
    snapP = -1;
    if (!snapA) {                   /* allocated on first use; failure = no snapshot */
        snapA = (char *)malloc((size_t)N + 1);
        snapCnt = (int *)malloc(sizeof(int) * ((size_t)N + 1));
        snapStart = (size_t *)malloc(sizeof(size_t) * ((size_t)N + 1));
        if (!snapA || !snapCnt || !snapStart) {
            free(snapA); free(snapCnt); free(snapStart);
            snapA = 0; snapCnt = 0; snapStart = 0;
            return;
        }
    }
    for (i = 0; i < N; i++) {
        User *u = &U[i];
        snapA[i] = (char)u->assigned;
        if (!u->assigned) continue;
        if (used + (size_t)u->nrb > snapCap) {
            size_t nc = (used + (size_t)u->nrb) * 2 + 64;
            RB *np = (RB *)realloc(snapPool, sizeof(RB) * nc);
            if (!np) { snapP = -1; return; }
            snapPool = np; snapCap = nc;
        }
        memcpy(snapPool + used, u->rbs, sizeof(RB) * (size_t)u->nrb);
        snapStart[i] = used; snapCnt[i] = u->nrb; used += (size_t)u->nrb;
    }
    snapP = curProfit; snapArea = curArea;
    snapUsed = used;
    ops += N + (long long)used * 2;
}

/*
 * Threshold phase: keep the refill just made although it lost profit (or kept
 * the profit with more area) if the loss is at most the threshold.  If the
 * state before it was the best one, that state is saved first: the current
 * solution, with the refill's requests taken out and the removed requests put
 * back.
 */
static int sa_keep_worse(long long oldP, long long oldA, int nr, int na)
{
    double loss = (double)(oldP - curProfit);
    int i;
    if (saThr <= 0 || loss > saThr) return 0;
    if (bestIsCur) {
        size_t used;
        save_snapshot();
        if (snapP < 0) return 0;
        used = snapUsed;
        for (i = 0; i < na; i++) snapA[addList[i]] = 0;
        for (i = 0; i < nr; i++) {
            int id = remList[i];
            if (used + (size_t)remCnt[i] > snapCap) {
                size_t nc = (used + (size_t)remCnt[i]) * 2 + 64;
                RB *np = (RB *)realloc(snapPool, sizeof(RB) * nc);
                if (!np) { snapP = -1; return 0; }
                snapPool = np; snapCap = nc;
            }
            memcpy(snapPool + used, pool + remStart[i], sizeof(RB) * (size_t)remCnt[i]);
            snapA[id] = 1; snapStart[id] = used; snapCnt[id] = remCnt[i];
            used += (size_t)remCnt[i];
        }
        snapP = oldP; snapArea = oldA;
        ops += 4LL * (nr + na);
        bestIsCur = 0;
    }
#ifdef DIAG
    dgWorse++;
#endif
    return 1;
}

static void restore_snapshot(void)
{
    int i, r;
    clear_all();
    for (i = 0; i < N; i++) {
        User *u = &U[i];
        if (!snapA[i]) continue;
        if (u->cap < snapCnt[i]) {
            RB *nr = (RB *)realloc(u->rbs, sizeof(RB) * (size_t)snapCnt[i]);
            if (!nr) continue;
            u->rbs = nr; u->cap = snapCnt[i];
        }
        memcpy(u->rbs, snapPool + snapStart[i], sizeof(RB) * (size_t)snapCnt[i]);
        u->nrb = snapCnt[i];
        u->assigned = 1;
        curProfit += u->profit;
        curArea += (long long)u->nrb * S;
        curOwner = i;
        for (r = 0; r < u->nrb; r++) mark_rb(&u->rbs[r], 1);
    }
}

/* greedy in priority order v, limited to `budget` operations (deterministic) */
/*
 * Construction modes.
 *   GR_PLAIN  : fixed lookahead.
 *   GR_RECORD : fixed lookahead, records the cumulative cost at 512 checkpoints.
 *   GR_PLANNED: uses the recorded first-fit cost profile to place as many of the
 *               leading (most valuable) requests as possible with the wide
 *               lookahead, while keeping enough budget to reach every request
 *               with first fit.  A request that is never reached is lost, so
 *               reaching all of them comes first.
 * Returns 1 if every request was processed.
 */
#define GR_PLAIN 0
#define GR_RECORD 1
#define GR_PLANNED 2
#define GR_TRY 3      /* fixed lookahead, gives up early if it cannot reach everybody */
#define NCP 512
static long long cpOps[NCP + 2], cpTot;
static char cpLean[NCP + 2];                 /* segment ran in the cheap mode */
static double cpWide[NCP + 2], cpLeanRest[NCP + 3];
static int cpStep, cpValid, greedySwitched;

/* one request with only its options of more than MAX_RB RBs, in the cheap mode
   (all masks stay exact when called between wide placements) */
static int place_big(User *u)
{
    int r, lm = leanMode;
    unsigned keep = leanKeep;
    long long o0 = ops;
    if (u->assigned) return 0;
    if (!lm) leanKeep = ~0U;
    leanMode = 1;
    bigPhase = 1;
    r = place_user(u);
    bigPhase = 0;
    ops += (ops - o0) * (LEAN_MUL4 - 4) / 4;
    leanMode = lm;
    leanKeep = keep;
    return r;
}

static int longWhole;           /* the last first construction kept the long lookahead to the end */
/*
 * Measured: on large inputs a construction takes more time per counted unit
 * than the local search (it walks every request once, missing the cache), the
 * more so with many requests and with many rows.  Its work is charged
 * (1 + consExtra) times.
 */
#ifndef CONS_N
#define CONS_N 0.5                  /* extra share at 200000 requests and more */
#endif
#ifndef CONS_W
#define CONS_W 0.1                  /* extra share per doubling of the row words */
#endif
static double consExtra;
static double loadRatio;        /* total smallest area of the requests / grid area */

static int greedy(int v, long long budget, int mode)
{
    int i, nAss = 0, j, everSwitched = 0, overCnt = 0, firstFitUsers = 0, bj = 0, longOn = 0, longEnd = 0, segI = 0, longI = 0;
    long long start = ops, wide = lookMul, segOps = ops, segPlaced = 0, placedNow = 0, longCap = 0, longOps = 0;
    long long wOps = 0, wUsers = 0, fOps = 0, fUsers = 0;   /* cost by mode (GR_TRY) */
    double rateW = 0, rateF = 0, ratioWF = 0;
    clear_all();
    leanKeep = ~0U; leanUseTot = 0; leanWork = staleWork = 0;
    for (j = 0; j < nsh; j++) leanUse[j] = 0;
    while (nAss < N && U[order[v][nAss]].nopt > 0) nAss++;
    if (mode == GR_RECORD || mode == GR_TRY) { cpStep = nAss / NCP > 0 ? nAss / NCP : 1; cpValid = 0; }
    greedySwitched = 0;
    /* oversubscribed grid: the leading requests whose smallest areas fill the
       grid (the "core") decide the profit, so they get a long lookahead,
       halved while the rest of the core would not fit in a share of the budget */
    if (mode == GR_TRY && LONG_LOOK > wide && wide > 0 && loadRatio >= LONG_LOAD) {
        double cap = (double)X * Y * LONG_CORE100 / 100.0, acc = 0;
        for (longEnd = 0; longEnd < nAss && acc <= cap; longEnd++) acc += (double)U[order[v][longEnd]].minArea;
        ops += longEnd;
        longCap = budget / 100 * LONG_FRAC100;
        lookMul = LONG_LOOK; longOn = 1; longOps = ops; longI = 0;
    }
    for (i = 0; i < nAss && ops - start <= budget; i++) {
        if (longOn && i < longEnd && (i & 63) == 0 && i - longI >= 256 && lookMul > LONG_MIN) {
            /* halve the lookahead while the rest of the core would not fit in the cap */
            double rate = (double)(ops - longOps) / (double)(i - longI);
            if ((double)(ops - start) + rate * (double)(longEnd - i) > (double)longCap) {
                lookMul /= 2;
                longOps = ops; longI = i;
#ifdef DIAG
                fprintf(stderr, "  long L->%lld at %d\n", lookMul, i);
#endif
            }
        }
        if (longOn && (i >= longEnd || ((i & 63) == 0 && ops - start > longCap))) {
#ifdef DIAG
            fprintf(stderr, "  long off at %d/%d (end %d): used %.3g cap %.3g\n", i, nAss, longEnd, (double)(ops - start), (double)longCap);
#endif
            longOn = 0;
            lookMul = wide;
            segOps = ops; segPlaced = placedNow; segI = i;
        }
        if (mode == GR_TRY && nAss >= 128 && i > 0 && i % (nAss / 64) == 0) {
            /* keep the wide lookahead for the next stretch only if first fit can
               still reach every later request afterwards (projected from the cost
               of the last stretch; later requests tend to be cheaper) */
            long long seg = nAss / 64, rem = nAss - i;
            double rate, r4, r0, need;
            int fits;
            if (longOn || i - segI < seg / 4) goto cp_done;    /* not measured yet */
            rate = (double)(ops - segOps) / (double)(i - segI);
            /* most of the last stretch placed: the cheap mode loses little, so
               reaching every request matters more than the lookahead */
            fits = (placedNow - segPlaced) * 10 >= (i - segI) * 3;
            if (!leanMode) rateW = rate; else rateF = rate;
            if (rateF <= 0) {
                /* cheap mode not measured yet: same projection as before */
                r4 = rateW; r0 = rateW * 0.65;
                need = (double)(ops - start) + 1.0 * (r4 * (double)seg + r0 * (double)(rem - seg));
            } else {
                r4 = rateW > 0 ? rateW : rateF / 0.65;
                r0 = rateF;
                need = (double)(ops - start) + r4 * (double)seg + (fits ? 1.0 : 0.85) * r0 * (double)(rem - seg);
            }
            /* a single expensive stretch (often the first ones) is not enough
               evidence: switch to the cheap mode after two over-budget checkpoints */
            overCnt = need > (double)budget ? overCnt + 1 : 0;
#ifdef FORCE_LEAN
            leanMode = 1;
#else
            if (!leanMode) { if (overCnt >= 1) leanMode = 1; }
            else if (need <= (fits ? 0.9 : 1.0) * (double)budget) { leanMode = 0; refresh_dirty(); }
#endif
            if (leanMode) update_lean_keep(nAss);
            segOps = ops;
            segPlaced = placedNow;
            segI = i;
        }
    cp_done:
        if (mode != GR_PLAIN && cpStep > 0 && i % cpStep == 0 && (j = i / cpStep) <= NCP) {
            if (mode == GR_RECORD || mode == GR_TRY) { cpOps[j] = ops - start; cpLean[j] = (char)leanMode; }
            else if (mode == GR_PLANNED) {
                /* wide lookahead for the next segment only if the cheap mode can
                   still reach every later request afterwards */
                double need = (double)(ops - start) + 1.15 * cpWide[j] + 1.1 * cpLeanRest[j + 1];
                leanMode = need <= (double)budget ? 0 : 1;
                if (!leanMode && shDirty) refresh_dirty();
                if (leanMode && (j & 7) == 0) update_lean_keep(nAss);
            }
        }
        if (mode == GR_TRY && leanMode) firstFitUsers++;
#ifdef FORCE_LEAN
        leanMode = 1;
#endif
        if (v == 0 && bigKeyV) {
            /* options with more than MAX_RB RBs go at their own profit per area */
            const User *uu = &U[order[v][i]];
            double ku = (double)uu->profit / (double)uu->minArea;
            while (bj < nBig && bigKeyV[bj] > ku && ops - start <= budget) placedNow += place_big(&U[bigIdx[bj++]]);
        }
        {
            long long o0 = ops;
            placedNow += place_user(&U[order[v][i]]);
            ops += (long long)((double)(ops - o0) * consExtra);   /* cache misses of large inputs */
            if (leanMode) {
                /* measured: the cheap mode takes more time per counted unit */
                ops += (ops - o0) * (LEAN_MUL4 - 4) / 4;
                fOps += ops - o0; fUsers++;
                leanWork += ops - o0;
            } else { wOps += ops - o0; wUsers++; }
        }
    }
    /* the requests needing more than MAX_RB RBs not reached yet: in the space left */
    if (nBig > 0 && ops - start <= budget) {
        if (shDirty) refresh_dirty();
        leanMode = 0;
        for (; bj < nBig && ops - start <= budget; bj++) placedNow += place_big(&U[bigIdx[bj]]);
    }
    /* the planned pass pays off only if a real share went without lookahead */
    greedySwitched = firstFitUsers * 20 >= nAss;
    if (mode == GR_TRY) longWhole = longOn;
    (void)everSwitched; (void)rateW; (void)rateF;
    lookMul = wide;
    leanMode = 0;
    if (mode == GR_RECORD || mode == GR_TRY) {
        int last = i / cpStep;
        cpValid = i == nAss;
        cpTot = ops - start;
        for (j = last + 1; j <= NCP; j++) { cpOps[j] = cpTot; cpLean[j] = 0; }
        /* cost of each recorded segment in either mode: measured per-user cost
           ratio of the wide mode to the cheap mode */
        if (wUsers > 0 && fUsers > 0) ratioWF = ((double)wOps / wUsers) / ((double)fOps / fUsers);
#ifdef DIAG
        fprintf(stderr, "  modes: wide %lld users %.3g ops | cheap %lld users %.3g ops | ratio %.2f\n", wUsers, (double)wOps, fUsers, (double)fOps, ratioWF);
#endif
        if (ratioWF < 1.0) ratioWF = 1.0;
        cpLeanRest[NCP + 1] = 0;
        for (j = NCP; j >= 0; j--) {
            long long segEnd = (j + 1 <= NCP && (long long)(j + 1) * cpStep < nAss) ? cpOps[j + 1] : cpTot;
            double c = (double)(segEnd - cpOps[j]);
            if (c < 0) c = 0;
            if (j > last) c = 0;
            cpWide[j] = cpLean[j] ? c * (ratioWF > 0 ? ratioWF : 1.0 / 0.65) : c;
            cpLeanRest[j] = cpLeanRest[j + 1] + (cpLean[j] ? c : c / (ratioWF > 0 ? ratioWF : 1.0 / 0.65));
        }
    }
    return i == nAss;
}

static int cmp_int(const void *p, const void *q)
{
    int a = *(const int *)p, b = *(const int *)q;
    return (a > b) - (a < b);
}

static int cmp_by_id(const void *p, const void *q)
{
    int a = *(const int *)p, b = *(const int *)q;
    if (U[a].id != U[b].id) return U[a].id < U[b].id ? -1 : 1;
    return (a > b) - (a < b);
}

static void print_empty(void)
{
    printf("0 0\n");
}

static void *xmalloc(size_t n)
{
    void *p = malloc(n ? n : 1);
    if (!p) { print_empty(); exit(0); }
    return p;
}

static void *xcalloc(size_t n, size_t sz)
{
    void *p = calloc(n ? n : 1, sz ? sz : 1);
    if (!p) { print_empty(); exit(0); }
    return p;
}

/* ---------- buffered output ---------- */

#define OUT_CAP (1 << 20)
static char *outBuf;
static size_t outLen;

static void out_flush(void)
{
    if (outLen) fwrite(outBuf, 1, outLen, stdout);
    outLen = 0;
}

static void out_room(size_t n)              /* make room for n more bytes */
{
    if (outLen + n > OUT_CAP) out_flush();
}

static void out_c(char c)
{
    if (outLen + 1 > OUT_CAP) out_flush();
    outBuf[outLen++] = c;
}

static void out_ll(long long v)
{
    char tmp[24];
    int n = 0;
    unsigned long long u;
    if (outLen + 24 > OUT_CAP) out_flush();
    if (v < 0) { outBuf[outLen++] = '-'; u = (unsigned long long)(-(v + 1)) + 1ULL; }
    else u = (unsigned long long)v;
    do { tmp[n++] = (char)('0' + (int)(u % 10)); u /= 10; } while (u);
    while (n) outBuf[outLen++] = tmp[--n];
}

/* ---------- time-axis compression ---------- */

/*
 * Only columns inside some request's window can ever hold an RB, so the time
 * axis is rebuilt from the merged windows ("segments") with one free column
 * between segments (and before / after them where the original had room).
 * Contacts and every rule are unchanged by this.  If even that is too long
 * for memory, windows are cut to their first `cap` columns (cap >= widest shape).
 */
static int nSeg, *segC, *segL;
static long long *segO;          /* original start of each segment */
static long long Xorig;
static int *cmpIdx;
static long long *oA, *oD;       /* original windows when X does not fit an int */

static long long win_a(int i) { return oA ? oA[i] : U[i].arr; }
static long long win_d(int i) { return oA ? oD[i] : U[i].dl; }

static int cmp_arr_idx(const void *p, const void *q)
{
    int a = *(const int *)p, b = *(const int *)q;
    if (win_a(a) != win_a(b)) return win_a(a) < win_a(b) ? -1 : 1;
    return (a > b) - (a < b);
}

/* compressed length for a window cap; fills the segment arrays if build */
static long long comp_len(int nIdx, long long cap, int build)
{
    long long tot = 0, cs = -1, ce = -2;
    int i, ns = 0;
    for (i = 0; i < nIdx; i++) {
        long long a = win_a(cmpIdx[i]), e = win_d(cmpIdx[i]);
        if (e - a + 1 > cap) e = a + cap - 1;
        if (a > ce + 1) {
            if (ce >= cs && cs >= 0) {
                if (build) { segO[ns] = cs; segL[ns] = (int)(ce - cs + 1); }
                ns++; tot += ce - cs + 1;
            }
            cs = a; ce = e;
        } else if (e > ce) ce = e;
    }
    if (cs >= 0) {
        if (build) { segO[ns] = cs; segL[ns] = (int)(ce - cs + 1); }
        ns++; tot += ce - cs + 1;
    }
    if (build) nSeg = ns;
    if (ns == 0) return 1;
    {
        long long gaps = ns - 1;
        if (build) {
            /* gaps: one separator before the first / after the last segment if room */
            int k;
            segC[0] = segO[0] > 0 ? 1 : 0;
            for (k = 1; k < ns; k++) segC[k] = segC[k - 1] + segL[k - 1] + 1;
            return (long long)segC[ns - 1] + segL[ns - 1] +
                   (segO[ns - 1] + segL[ns - 1] < Xorig ? 1 : 0);
        }
        return tot + gaps + 2;
    }
}

/* monotone map of an original column into the compressed axis */
static int comp_map(long long x)
{
    int lo = 0, hi = nSeg - 1, k = -1;
    while (lo <= hi) {
        int md = (lo + hi) / 2;
        if (segO[md] <= x) { k = md; lo = md + 1; } else hi = md - 1;
    }
    if (k < 0) return 0;
    if (x < segO[k] + segL[k]) return segC[k] + (int)(x - segO[k]);
    return segC[k] + segL[k];                       /* separator after segment k */
}

/* original column of a compressed column inside a segment */
static long long comp_unmap(int x)
{
    int lo = 0, hi = nSeg - 1, k = 0;
    if (!nSeg) return x;
    while (lo <= hi) {
        int md = (lo + hi) / 2;
        if (segC[md] <= x) { k = md; lo = md + 1; } else hi = md - 1;
    }
    return segO[k] + (x - segC[k]);
}

/* windows that cannot be represented: serve nobody rather than misplace */
static void comp_fail(void)
{
    int i;
    if (!oA) return;
    for (i = 0; i < N; i++) U[i].nopt = U[i].nbig = 0;
    free(oA); free(oD); oA = oD = 0;
    X = 1;
}

/*
 * Even windows cut to the widest shape do not fit in memory (very wide
 * shapes): keep the requests with the best profit per area while their
 * windows fit; the others cannot be served.  Returns the new count of
 * cmpIdx (still in arrival order).
 */
static double *keepKey;

static int cmp_keep(const void *p, const void *q)
{
    int a = *(const int *)p, b = *(const int *)q;
    if (keepKey[a] != keepKey[b]) return keepKey[a] > keepKey[b] ? -1 : 1;
    return (a > b) - (a < b);
}

static int comp_keep_best(int nIdx, long long cap, long long xlim)
{
    int *byKey = (int *)malloc(sizeof(int) * ((size_t)nIdx + 1)), i, n2 = 0;
    char *keep = (char *)calloc((size_t)N + 1, 1);
    long long tot = 0;
    keepKey = (double *)malloc(sizeof(double) * ((size_t)N + 1));
    if (!byKey || !keep || !keepKey) {          /* no memory: serve nobody */
        for (i = 0; i < nIdx; i++) U[cmpIdx[i]].nopt = U[cmpIdx[i]].nbig = 0;
        free(byKey); free(keep); free(keepKey); keepKey = 0;
        return 0;
    }
    for (i = 0; i < nIdx; i++) {
        const User *u = &U[cmpIdx[i]];
        long long area = u->nopt > 0 ? u->minArea : (long long)u->optK[u->nopt] * S;
        keepKey[cmpIdx[i]] = (double)u->profit / (double)(area > 0 ? area : 1);
        byKey[i] = cmpIdx[i];
    }
    qsort(byKey, (size_t)nIdx, sizeof(int), cmp_keep);
    for (i = 0; i < nIdx; i++) {
        long long len = win_d(byKey[i]) - win_a(byKey[i]) + 1;
        if (len > cap) len = cap;
        if (tot + len + 1 > xlim) break;
        tot += len + 1;
        keep[byKey[i]] = 1;
    }
    for (i = 0; i < nIdx; i++) {
        int id = cmpIdx[i];
        if (keep[id]) cmpIdx[n2++] = id;
        else U[id].nopt = U[id].nbig = 0;
    }
    free(byKey); free(keep); free(keepKey); keepKey = 0;
    ops += (long long)nIdx * 40;
    return n2;
}

static void compress_time(void)
{
    int i, nIdx = 0, sorted = 1, maxW2 = 1, nUsed = 0;
    long long full, cap, xlim;
    unsigned used = 0;
    if (!oA) Xorig = X;
    for (i = 0; i < nsh; i++) if (shW[i] > maxW2) maxW2 = shW[i];
    for (i = 0; i < N; i++) {
        int o2;
        for (o2 = 0; o2 < U[i].nopt + U[i].nbig; o2++) used |= U[i].optShapes[o2];
    }
    for (i = 0; i < nsh; i++) if ((used >> i) & 1U) nUsed++;
    /* columns the grid may have: memory for the occupancy and the free-start masks */
    xlim = (long long)(MEM_GRID / ((double)(1 + nUsed) * W * 8.0)) - 4;
    if (xlim > MAX_COLS) xlim = MAX_COLS;
    cmpIdx = (int *)malloc(sizeof(int) * ((size_t)N + 1));
    if (!cmpIdx) { comp_fail(); return; }
    for (i = 0; i < N; i++) if (U[i].nopt + U[i].nbig > 0 && win_a(i) <= win_d(i)) cmpIdx[nIdx++] = i;
    for (i = 1; i < nIdx; i++) if (win_a(cmpIdx[i]) < win_a(cmpIdx[i - 1])) sorted = 0;
    if (!sorted) qsort(cmpIdx, (size_t)nIdx, sizeof(int), cmp_arr_idx);
    full = comp_len(nIdx, Xorig + 1, 0);
    cap = Xorig + 1;
    if (full > xlim) {
        long long lo = maxW2, hi = Xorig;       /* largest cap that fits */
        while (lo < hi) {
            long long md = lo + (hi - lo + 1) / 2;
            if (comp_len(nIdx, md, 0) <= xlim) lo = md; else hi = md - 1;
        }
        cap = lo;
        if (comp_len(nIdx, cap, 0) > xlim) nIdx = comp_keep_best(nIdx, cap, xlim);
    } else if (!oA && full * 2 > X) {           /* little to gain: keep the axis */
        free(cmpIdx); cmpIdx = 0;
        return;
    }
    segO = (long long *)malloc(sizeof(long long) * ((size_t)nIdx + 1));
    segC = (int *)malloc(sizeof(int) * ((size_t)nIdx + 1));
    segL = (int *)malloc(sizeof(int) * ((size_t)nIdx + 1));
    if (!segO || !segC || !segL) {
        free(segO); free(segC); free(segL); segO = 0; segC = segL = 0; free(cmpIdx); cmpIdx = 0;
        comp_fail();
        return;
    }
    {
        long long newX = comp_len(nIdx, cap, 1);
        for (i = 0; i < N; i++) {
            User *u = &U[i];
            long long a = win_a(i), e = win_d(i);
            if (u->nopt + u->nbig > 0 && a <= e && e - a + 1 > cap) e = a + cap - 1;
            u->arr = comp_map(a);
            u->dl = comp_map(e);
        }
        free(oA); free(oD); oA = oD = 0;
        X = (int)(newX < 1 ? 1 : newX);
    }
    free(cmpIdx); cmpIdx = 0;
    ops += (long long)N * 40;
}

/* ---------- setup ---------- */

static void build_shapes(void)
{
    int hs[MAXSH * 4], nh = 0, i, j;
    long long d;
    nsh = 0;
    if (S <= 0) return;
    for (d = 1; d * d <= S; d++) {
        if (S % d) continue;
        if (nh < MAXSH * 4) hs[nh++] = (int)d;
        if (d * d != S && nh < MAXSH * 4) hs[nh++] = (int)(S / d);
    }
    qsort(hs, (size_t)nh, sizeof(int), cmp_int);
    for (i = 0; i < nh && nsh < MAXSH; i++) {
        int h = hs[i], w = S / h;
        if (h > Y || w > X) continue;
        shH[nsh] = h; shW[nsh] = w; nsh++;
    }
    {
        int mw = 1;
        for (i = 0; i < nsh; i++) if (shW[i] > mw) mw = shW[i];
        levCnt = ilog2(mw);                 /* former OR levels 1..log2(max width) */
        levSpan = (1LL << (levCnt + 1)) - 2;
        nlev = 1;                           /* occupancy only: no OR-level tables */
    }
    (void)j;
    for (i = 0; i < nsh; i++) {
        int len = 1;
        shLj[i] = ilog2(shW[i]); shOff[i] = shW[i] - (1 << shLj[i]);
        shNStep[i] = 0;
        while (len < shH[i] && shNStep[i] < 40) {
            int step = (len < shH[i] - len) ? len : shH[i] - len;
            shStep[i][shNStep[i]++] = step;
            len += step;
        }
    }
}

#ifdef DIAG
static void lns_trace(long long lnsStart, int cycle)
{
    static int nextTr = 1;
    if ((ops - lnsStart) * 20 >= (opsEnd - lnsStart) * nextTr) {
        fprintf(stderr, "  lns %2d/20 profit=%lld area=%lld best=%lld steps=%lld lds=%d ta=%d thr=%.3g pass=%d | avg nr=%.1f nc=%.1f na=%.1f imp=%lld eq=%lld worse=%lld\n",
                nextTr, curProfit, curArea, saOn ? bestP : curProfit, lnsSteps, ldsOn, saOn, saThr, cycle,
                (double)dgNr / (dgSteps + 1e-9), (double)dgNc / (dgSteps + 1e-9), (double)dgNa / (dgSteps + 1e-9), dgImp, dgEq, dgWorse);
        nextTr++;
    }
}
#endif

#ifndef TA_T0
#define TA_T0 0.05      /* first threshold, in average profits of an accepted request */
#endif
static long long saStart, saStep;   /* start of the threshold phase, its steps */
static double saThr0;
static const double saAlphaTab[7] = {1.0, 0.6, 1.4, 0.8, 1.2, 0.7, 1.6};

/* start of the threshold phase; returns 0 if it cannot start (no memory) */
static int sa_begin(void)
{
    long long nAss = 0;
    int i;
    lpU = (float *)malloc(sizeof(float) * ((size_t)N + 1));
    laU = (float *)malloc(sizeof(float) * ((size_t)N + 1));
    saBuf = (SaKey *)malloc(sizeof(SaKey) * ((size_t)N + 64));
    if (!lpU || !laU || !saBuf) {
        free(lpU); free(laU); free(saBuf); lpU = laU = 0; saBuf = 0;
        return 0;
    }
    for (i = 0; i < N; i++) {
        const User *u = &U[i];
        if (u->nopt > 0 && u->profit > 0 && u->minArea > 0) {
            lpU[i] = (float)my_log((double)u->profit);
            laU[i] = (float)my_log((double)u->minArea);
        } else lpU[i] = laU[i] = 0;
        nAss += u->assigned;
    }
    ops += 80LL * N;
    saThr0 = TA_T0 * (double)(curProfit > 0 ? curProfit : 1) / (double)(nAss > 0 ? nAss : 1);
    saStart = ops;
    saStep = 0;
    bestP = curProfit; bestA = curArea; bestIsCur = 1;
    return 1;
}

/* before each refill of the threshold phase: threshold (falling linearly to
   zero over the rest of the budget) and the next refill order in the cycle */
static void sa_next(void)
{
    double left = opsEnd > saStart ? (double)(opsEnd - ops) / (double)(opsEnd - saStart) : 0;
    saThr = left > 0 ? saThr0 * left : 0;
    saAlpha = saAlphaTab[saStep % 7];
    saPromote = saStep;
    saStep++;
}

/* end of the threshold phase: the answer is the best solution seen */
static void sa_end(void)
{
    if (!bestIsCur && snapP >= 0) snapOut = 1;
#ifdef DIAG
    fprintf(stderr, "  threshold phase end: current %lld best %lld snapOut %d\n", curProfit, bestP, snapOut);
#endif
}

/*
 * Adaptive sweep.  A class is a region shape (row band height, strip width);
 * each class sweeps the grid with its own cursor (time strips, then row
 * bands, shifted on every new pass).  The work is cut into short segments and
 * the segments are shared out among the classes in proportion to the profit
 * each gained per unit of work recently (smooth weighted round-robin; every
 * class keeps a small share).
 */
#ifndef SEG_DIV
#define SEG_DIV 800                 /* a segment is about 1/SEG_DIV of the search budget */
#endif
#define NCLS 64
#ifndef NARROW
#define NARROW 1
#endif
#ifndef MIN_BAND
#define MIN_BAND 8                  /* thinnest extra row band */
#endif
#ifndef CLS_FLOOR
#define CLS_FLOOR 0.05
#endif
typedef struct {
    int mode, hb, rstep, pass, seen;
    long long wd, step, t0, r0;
    double rate;                    /* recent profit gained per unit of work */
    double credit;                  /* round-robin credit */
} Cls;
static Cls cls[NCLS];
static int ncls;

static void cls_init(const int *widths, int nw)
{
    int mode, wi;
    ncls = 0;
    /* row bands Y, Y/2, Y/4, and on tall grids thinner ones down to MIN_BAND rows */
    for (mode = 0; mode < 8; mode++) {
        int hb = (int)(((long long)Y + (1LL << mode) - 1) >> mode);
        if (mode >= 3 && hb < MIN_BAND) break;
        if (mode > 0 && hb >= Y) continue;
        for (wi = 0; wi < nw && ncls < NCLS; wi++) {
            Cls *c = &cls[ncls++];
            long long wd = (long long)widths[wi] * (mode ? 2 : 1);
            if (wd > X) wd = X;
            c->mode = mode; c->hb = hb; c->rstep = hb / 2 > 0 ? hb / 2 : 1;
            c->wd = wd; c->step = wd / 2 > 0 ? wd / 2 : 1;
            c->pass = 0; c->seen = 0; c->rate = 0; c->credit = 0;
            c->t0 = -c->step; c->r0 = 0;
        }
    }
    passSteps = 0;
    for (wi = 0; wi < ncls; wi++) {
        const Cls *c = &cls[wi];
        long long bands = c->mode ? (Y - c->hb + c->rstep - 1) / c->rstep + 1 : 1;
        passSteps += ((long long)X + c->step - 1) / c->step * bands;
    }
}

/* one refill at the cursor of class c, then move the cursor */
static void cls_step(Cls *c, int v)
{
    long long s0 = c->t0 < 0 ? 0 : c->t0, s1 = c->t0 + c->wd - 1;
    if (s1 > X - 1) s1 = X - 1;
    if (s1 >= s0) {
        ry0 = c->mode ? (int)c->r0 : 0;
        ry1 = c->mode ? (int)(c->r0 + c->hb - 1 < Y - 1 ? c->r0 + c->hb - 1 : Y - 1) : Y - 1;
        lns_step((int)s0, (int)s1, v);
    }
    if (c->mode && c->r0 + c->hb < Y) { c->r0 += c->rstep; return; }
    c->r0 = 0;
    c->t0 += c->step;
    if (c->t0 >= X) {                   /* new pass, shifted by a third of a step */
        c->pass++;
        c->t0 = ((long long)c->pass * c->step / 3) % c->step - c->step;
    }
}

static int cls_pick(void)
{
    double tot = 0, mx = 0;
    int i, best = 0;
    for (i = 0; i < ncls; i++) if (!cls[i].seen) return i;     /* every class once, in order */
    for (i = 0; i < ncls; i++) if (cls[i].rate > mx) mx = cls[i].rate;
    for (i = 0; i < ncls; i++) {
        double w = (cls[i].rate > 0 ? cls[i].rate : 0) + CLS_FLOOR * mx + 1e-12;
        cls[i].credit += w;
        tot += w;
    }
    for (i = 1; i < ncls; i++) if (cls[i].credit > cls[best].credit) best = i;
    cls[best].credit -= tot;
    return best;
}

/* the sweep until the budget ends (the threshold phase starts on the way) */
static void lns_sweep(void)
{
    int nv = nVar < NVAR_LNS ? nVar : NVAR_LNS;
    long long vc = 0;
    while (ops < opsEnd) {
        int ci = cls_pick();
        Cls *c = &cls[ci];
        long long o0 = ops, p0 = curProfit, seg = (opsEnd - lnsStart) / SEG_DIV;
        double r;
        if (seg < 2000000) seg = 2000000;
        do {
            if (saOn) sa_next();
            cls_step(c, (int)(vc++ % nv));
            lns_check();
#ifdef DIAG
            lns_trace(lnsStart, c->pass);
#endif
            if (!saOn && is_stalled()) {
                stalled();
                if (saOn && !sa_begin()) { saOn = 0; saAllowed = 0; }   /* no memory: plain sweep */
            }
        } while (ops - o0 < seg && ops < opsEnd);
        r = (double)(curProfit - p0) / (double)(ops - o0 + 1);
        c->rate = c->seen ? 0.6 * c->rate + 0.4 * r : r;
        c->seen = 1;
    }
}

int main(void)
{
    long long t, hdr[4];
    int i, y, v, maxK = 1;
    long long *bits;

    for (i = 0; i < 4; i++) if (!read_ll(&hdr[i])) { print_empty(); return 0; }
    if (hdr[0] <= 0 || hdr[1] <= 0 || hdr[2] <= 0 || hdr[3] <= 0 ||
        hdr[0] > 2000000000LL || hdr[2] > 2000000000LL) {
        /* still consume nothing more: no user can be served */
        print_empty();
        return 0;
    }
    Y = (int)hdr[0]; S = (int)hdr[2];
    Xorig = hdr[1];
    X = hdr[1] > 2000000000LL ? 2000000000 : (int)hdr[1];   /* longer axes are compressed */
    N = hdr[3] > 100000000LL ? 100000000 : (int)hdr[3];
    W = (int)(((long long)Y + 63) / 64);

    scT = (u64 *)xcalloc((size_t)W, sizeof(u64));
    scRm1 = (u64 *)xcalloc((size_t)W, sizeof(u64));
    scRm2 = (u64 *)xcalloc((size_t)W, sizeof(u64));
    scOcc = (u64 *)xcalloc((size_t)W, sizeof(u64));
    scFr = (u64 *)xcalloc((size_t)W, sizeof(u64));
    scSl = (u64 *)xcalloc((size_t)W, sizeof(u64));
    scSr = (u64 *)xcalloc((size_t)W, sizeof(u64));
    scCand = (u64 *)xcalloc((size_t)W, sizeof(u64));
    scG = (u64 *)xcalloc((size_t)W, sizeof(u64));
    scM = (u64 *)xcalloc((size_t)W, sizeof(u64));
    scPend = (u64 *)xcalloc((size_t)W, sizeof(u64));
    scTail = (u64 *)xcalloc((size_t)W, sizeof(u64));
    scBig1 = (u64 *)xcalloc((size_t)W, sizeof(u64));
    scBig2 = (u64 *)xcalloc((size_t)W, sizeof(u64));
    scSm = (u64 *)xcalloc((size_t)W, sizeof(u64));

    build_shapes();

    {
        double per = ((double)N + 1.0) * W * 8.0;
        double mo = MEM_OPT / per;
        maxOpt = mo >= 8.0 ? 8 : (mo < 2.0 ? 2 : (int)mo);
    }
    tK = (int *)xmalloc(sizeof(int) * (size_t)(maxOpt + 3));
    tMask = (u64 *)xcalloc((size_t)(maxOpt + 3) * W, sizeof(u64));
    tSh = (unsigned *)xcalloc((size_t)(maxOpt + 3), sizeof(unsigned));
    scIdx = (int *)xmalloc(sizeof(int) * (size_t)Y);
    sortA = (u64 *)xmalloc(sizeof(u64) * (size_t)Y);
    sortB = (u64 *)xmalloc(sizeof(u64) * (size_t)Y);

    U = (User *)xcalloc((size_t)N + 1, sizeof(User));
    bits = (long long *)xmalloc(sizeof(long long) * (size_t)Y);
    for (i = 0; i < N; i++) {
        User *u = &U[i];
        long long f[5];
        int ok = 1, k2;
        for (k2 = 0; k2 < 5; k2++) if (!read_ll(&f[k2])) { ok = 0; break; }
        if (!ok) { N = i; break; }
        for (y = 0; y < Y; y++) if (!read_ll(&bits[y])) bits[y] = 0;
        u->id = f[0]; u->dem = f[1]; u->profit = f[4];
        if (Xorig > X) {                    /* original window kept aside, compressed later */
            long long a2 = f[2] < 0 ? 0 : f[2], d2 = f[3] > Xorig - 1 ? Xorig - 1 : f[3];
            if (!oA) {
                oA = (long long *)xmalloc(sizeof(long long) * ((size_t)N + 1));
                oD = (long long *)xmalloc(sizeof(long long) * ((size_t)N + 1));
            }
            oA[i] = a2; oD[i] = d2;
            u->arr = 0;
            u->dl = d2 < a2 ? -1 : (d2 - a2 >= 2000000000LL ? 1999999999 : (int)(d2 - a2));
        } else {
            t = f[2] < 0 ? 0 : f[2];
            u->arr = clamp_int(t);
            t = f[3] > (long long)X - 1 ? (long long)X - 1 : f[3];
            u->dl = clamp_int(t);
        }
        build_options(u, bits);
        for (v = 0; v < u->nopt + u->nbig; v++) if (u->optK[v] > maxK) maxK = u->optK[v];
    }
    compress_time();
    unsortedArr = 0;
    for (i = 1; i < N; i++) if (U[i].arr < U[i - 1].arr) unsortedArr = 1;

    if (nsh > 0) {
        for (i = 0; i < nlev; i++) lev[i] = (u64 *)xcalloc((size_t)X * W + 1, sizeof(u64));
        col = lev[0];
        for (i = 0; i < nsh; i++) if (shW[i] > maxShW) maxShW = shW[i];
{
            /* journal bound: every free-start word, column flag and summary word
               one RB can change, times the most RBs one request can hold */
            double per = 0, tot;
            int q;
            for (q = 0; q < nsh; q++) per += ((double)shW[q] + maxShW) * (W + 1) + ((double)shW[q] + maxShW) / 64.0 + 4;
            tot = per * (MAX_RB + 1);       /* bigger requests: undo by recomputing */
            if (tot * 16.0 <= 256e6) {
                jCap = (long long)tot + 64;
                jPtr = (u64 **)malloc(sizeof(u64 *) * (size_t)jCap);
                jVal = (u64 *)malloc(sizeof(u64) * (size_t)jCap);
                if (!jPtr || !jVal) { free(jPtr); free(jVal); jPtr = 0; jVal = 0; jCap = 0; }
            }
        }
        vhP = (u64 *)xcalloc((size_t)(3 * maxShW + 64) * W, sizeof(u64));
        vhS = (u64 *)xcalloc((size_t)(3 * maxShW + 64) * W, sizeof(u64));
        fzWords = X / 64 + 2;
        usedSh = 0;
        for (i = 0; i < N; i++) {
            int o2;
            for (o2 = 0; o2 < U[i].nopt + U[i].nbig; o2++) usedSh |= U[i].optShapes[o2];
        }
        for (;;) {                              /* masks must fit in memory */
            int q, nU = 0;
            for (q = 0; q < nsh; q++) if ((usedSh >> q) & 1U) nU++;
            if ((double)(1 + nU) * ((double)X + 2) * W * 8.0 <= MEM_GRID || nU <= 1) break;
            for (q = 0; q < nsh; q++) if ((usedSh >> q) & 1U) { usedSh &= ~(1U << q); break; }   /* widest */
        }
        for (i = 0; i < N; i++) {
            int o2;
            for (o2 = 0; o2 < U[i].nopt + U[i].nbig; o2++) U[i].optShapes[o2] &= usedSh;
        }
        for (i = 0; i < nsh; i++) fz[i] = (u64 *)xcalloc(((usedSh >> i) & 1U) ? (size_t)fzWords : 1, sizeof(u64));
        fzsWords = fzWords / 64 + 2;
        for (i = 0; i < nsh; i++) fzs[i] = (u64 *)xcalloc(((usedSh >> i) & 1U) ? (size_t)fzsWords : 1, sizeof(u64));
        for (i = 0; i < nsh; i++) fm[i] = (u64 *)xcalloc(((usedSh >> i) & 1U) ? ((size_t)X + 1) * W : 1, sizeof(u64));
        scGs = (u64 *)xcalloc((size_t)W, sizeof(u64));
        nBlk = X / 64 + 1;
        fen = (long long *)xcalloc((size_t)nBlk + 2, sizeof(long long));
        useRow = (double)Y * fzWords * 8.0 <= MEM_ROW;
        if (useRow) rowOcc = (u64 *)xcalloc((size_t)Y * fzWords, sizeof(u64));
        useOwn = (double)X * Y * 4.0 <= MEM_OWN;
        if (useOwn) own = (int *)xmalloc(sizeof(int) * (size_t)X * Y);
        scAll = (u64 *)xcalloc((size_t)W, sizeof(u64));
        scMp = (u64 *)xcalloc((size_t)W, sizeof(u64));
        scMn = (u64 *)xcalloc((size_t)W, sizeof(u64));
        scMm = (u64 *)xcalloc((size_t)W, sizeof(u64));
        row_mask(scAll, 0, Y);
    }
    tmpRB = (RB *)xmalloc(sizeof(RB) * (size_t)maxK);
    tmpJ = (long long *)xmalloc(sizeof(long long) * ((size_t)maxK + 2));
    dryRB = (RB *)xmalloc(sizeof(RB) * (size_t)maxK);
    mixA = (RB *)xmalloc(sizeof(RB) * (size_t)maxK);
    tmpUn = (RB *)xmalloc(sizeof(RB) * (size_t)maxK);
    unOpen = (int *)xmalloc(sizeof(int) * ((size_t)Y + 1));
    unStamp = (int *)xcalloc((size_t)Y + 1, sizeof(int));
    scRowsU = (u64 *)xcalloc((size_t)W, sizeof(u64));
    dryCap = maxK + 1;
    if ((double)dryCap * W > 4e6) dryCap = (int)(4e6 / W) + 1;
    dryQx = (int *)xmalloc(sizeof(int) * (size_t)dryCap);
    dryQ = (u64 *)xmalloc(sizeof(u64) * (size_t)dryCap * W);
    dryB = (u64 *)xcalloc((size_t)W, sizeof(u64));
    keyBuf = (double *)xmalloc(sizeof(double) * ((size_t)N + 1));
    rsA = (KeyId *)xmalloc(sizeof(KeyId) * ((size_t)N + 1));
    rsB = (KeyId *)xmalloc(sizeof(KeyId) * ((size_t)N + 1));


    nVar = N > 300000 ? 1 : NVAR;   /* sorting several orders of a huge input costs too much */
    for (i = 0; i < N; i++) if (U[i].nopt && U[i].dl - U[i].arr + 1 > maxWin) maxWin = U[i].dl - U[i].arr + 1;
    for (v = 0; v < nVar; v++) {
        order[v] = (int *)xmalloc(sizeof(int) * ((size_t)N + 1));
        for (i = 0; i < N; i++) { order[v][i] = i; keyBuf[i] = user_key(&U[i], v); }
        radix_order(order[v]);
    }
    free(keyBuf); free(rsA); free(rsB); keyBuf = 0; rsA = rsB = 0;
    /* requests that can only use more than MAX_RB RBs (or whose normal options
       all fail): tried last, by profit per area of their smallest such option */
    for (i = 0; i < N; i++) if (U[i].nbig > 0) nBig++;
    if (nBig > 0) {
        BigKey *bk = (BigKey *)malloc(sizeof(BigKey) * (size_t)nBig);
        bigIdx = (int *)malloc(sizeof(int) * (size_t)nBig);
        if (!bk || !bigIdx) { free(bk); free(bigIdx); bigIdx = 0; nBig = 0; }
        else {
            int nb2 = 0;
            for (i = 0; i < N; i++) {
                User *u = &U[i];
                if (u->nbig <= 0) continue;
                bk[nb2].key = (double)u->profit / ((double)u->optK[u->nopt] * S);
                bk[nb2].id = i;
                nb2++;
            }
            qsort(bk, (size_t)nBig, sizeof(BigKey), cmp_bigkey);
            bigKeyV = (double *)malloc(sizeof(double) * (size_t)nBig);
            for (i = 0; i < nBig; i++) bigIdx[i] = bk[i].id;
            if (bigKeyV) for (i = 0; i < nBig; i++) bigKeyV[i] = bk[i].key;
            free(bk);
            ops += (long long)nBig * 40;
        }
    }
    {   /* how oversubscribed the grid is */
        double dem = 0;
        for (i = 0; i < N; i++) if (U[i].nopt > 0) dem += (double)U[i].minArea;
        loadRatio = dem / ((double)X * Y);
    }
    consExtra = CONS_N * (N < 200000 ? (double)N / 200000.0 : 1.0) + CONS_W * ilog2(W);
    /* account for reading, option building and sorting */
    ops += inTotal * SETUP_PER_BYTE + (long long)N * nVar * 60;

    if (nsh > 0) {
        /* 1. initial greedy with each priority order */
        /* budgets are counted from here, so a costly setup never starves the search */
        long long opsLimit = OPS_LIMIT, normLimit = NORM_LIMIT, wideLimit = BUDGET(WIDE_LIMITV);
        long long base = ops, rest = opsLimit - ops, gBudget, normRest, normEnd, cost0 = 0, wideRest, wideEnd;
        /* portfolio of constructions: (priority order, lookahead); extra ones only while cheap */
        /* constructions:
             1. wide lookahead; if it is projected not to reach every request, the
                remaining requests use first fit (cost profile recorded);
             2. if it had to switch and budget is left: the planned pass (wide
                lookahead for the leading requests while first fit can still reach
                all the others, from the recorded profile);
             3. wider lookaheads while the normal budget allows.
           The best construction is kept. */
        static const int cfgL[] = {LOOK_MUL, LOOK_MUL, 32, 96};
        static const int cfgMode[] = {GR_TRY, GR_PLANNED, GR_PLAIN, GR_PLAIN};
        int nCfg = (int)(sizeof(cfgL) / sizeof(cfgL[0])), ci, bestC = -1, lastC = -1, r, switched = 0, wideLook = 32, lnsWill;
        long long gP = -1, gA = 0, gEnd, prevCost = 0;
        if (rest < opsLimit / 3) rest = opsLimit / 3;   /* the greedy always gets a share */
        gBudget = rest * 97 / 100;
        gEnd = base + gBudget;
        /* extra constructions and the local search stay within the normal budget */
        normRest = normLimit - ops;
        if (normRest < normLimit / 3) normRest = normLimit / 3;
        if (normRest > rest) normRest = rest;
        normEnd = base + normRest;
        /* a wider lookahead usually gains far more than the local search: it may
           use a little more than the normal budget */
        wideRest = wideLimit - ops;
        if (wideRest < normRest) wideRest = normRest;
        if (wideRest > rest) wideRest = rest;
        wideEnd = base + wideRest;
        hardLimit = base + rest + (OPS_HARD - OPS_LIMIT);
        allProfit = 0;
        for (i = 0; i < N; i++) if (U[i].nopt + U[i].nbig > 0) allProfit += U[i].profit;
        ownLive = 0;                            /* only the local search needs owners */
        ownValid = 0;
        for (ci = 0; ci < nCfg; ci++) {
            long long st = ops;
            if (ci == 1 && (!switched || !cpValid || ops + cpTot * 12 / 10 > gEnd)) continue;
            if (ci == 2 && longWhole) continue;   /* the first one already had the long lookahead */
#ifdef NO_WIDE
            if (ci >= 2) break;
#endif
            if (ci == 2) {
                /* the widest lookahead whose cost (measured ratios to lookahead 4,
                   with a margin) still fits */
                static const int wl[] = {32, 16, 8};
                static const int wf[] = {26, 19, 15};      /* tenths of the last cost */
                int q, pick = -1;
                if (switched) { if (ops + prevCost * 35 / 10 <= normEnd) pick = 0; }
                else for (q = 0; q < 3 && pick < 0; q++) if (ops + prevCost * wf[q] / 10 <= wideEnd) pick = q;
                if (pick < 0) break;
                wideLook = wl[pick];
            }
            if (ci == 3 && ops + prevCost * 2 > normEnd) break;
            lookMul = ci == 2 ? wideLook : cfgL[ci];
            r = greedy(0, (ci == 2 ? wideEnd : ci == 3 ? normEnd : gEnd) - ops, cfgMode[ci]);
            if (ci == 0) switched = greedySwitched;
#ifdef DIAG
            fprintf(stderr, "  config %d look=%d mode=%d complete=%d switched=%d profit=%lld cost=%.3g ops=%.3g\n", ci, cfgL[ci], cfgMode[ci], r, greedySwitched, curProfit, (double)(ops - st), (double)ops);
#endif
            prevCost = ops - st;
            lastC = ci;
            if (curProfit > gP || (curProfit == gP && curArea < gA)) {
                gP = curProfit; gA = curArea; bestC = ci;
                if (ci + 1 < nCfg) save_snapshot();
            }
            if (!r) break;                      /* out of budget */
            if (curProfit >= allProfit) break;  /* everybody is served */
        }
        lnsWill = ops < normEnd;                /* a local search follows */
        if (bestC >= 0 && bestC != lastC) {
            if (snapP >= 0 && !lnsWill) snapOut = 1;           /* no local search follows */
            else if (snapP >= 0) restore_snapshot();
            else { lookMul = bestC == 2 ? wideLook : cfgL[bestC]; greedy(0, gBudget, GR_PLAIN); }
        }
        ownLive = 1;
        if (useOwn && !snapOut && lnsWill) { rebuild_owner(); ownValid = 1; }
        lookMul = LNS_LOOK;
        opsEnd = normEnd;
        hardLimit = normEnd + (OPS_HARD - OPS_LIMIT) / 4;
        if (hardLimit < ops) hardLimit = ops;
        (void)cost0;

        /* 2. ruin and recreate over systematic strips / bands */
        if (ops < opsEnd && shDirty) refresh_dirty();
        if (ops < opsEnd) {
            int ok = 1;
            candList = (int *)malloc(sizeof(int) * ((size_t)N + 64));
            addList = (int *)malloc(sizeof(int) * ((size_t)N + 64));
            remList = (int *)malloc(sizeof(int) * ((size_t)N + 1));
            remStart = (int *)malloc(sizeof(int) * ((size_t)N + 1));
            remCnt = (int *)malloc(sizeof(int) * ((size_t)N + 1));
            inRem = (char *)calloc((size_t)N + 1, 1);
            if (!candList || !addList || !remList || !remStart || !remCnt || !inRem) ok = 0;
            for (v = 0; v < nVar && ok; v++) {
                ulist[v] = (int *)malloc(sizeof(int) * ((size_t)N + 1));
                rankv[v] = (int *)malloc(sizeof(int) * ((size_t)N + 1));
                if (!ulist[v] || !rankv[v]) ok = 0;
                else for (i = 0; i < N; i++) rankv[v][order[v][i]] = i;
            }
            if (!ok) opsEnd = ops;                  /* not enough memory: no local search */
        }
        if (ops < opsEnd)
        {
            int widths[12], nw = 0;
            long long sumL = 0, cntL = 0, Lavg;
            for (i = 0; i < N; i++) if (U[i].nopt) { sumL += U[i].dl - U[i].arr + 1; cntL++; }
            Lavg = cntL ? sumL / cntL : X;
            lnsLavg = Lavg > 0 ? Lavg : 1;
            {
                long long cand[10], nAs = 0, maxW;
                int c, nc0;
                /* a full-height strip holds at most about REG_USERS average requests */
                for (i = 0; i < N; i++) nAs += U[i].assigned;
                maxW = nAs > 0 ? (long long)((double)REG_USERS * ((double)curArea / (double)nAs) / (double)Y) : X;
                if (maxW < 2LL * S) maxW = 2LL * S;
                ops += N;
                cand[0] = Lavg / 8; cand[1] = Lavg / 4; cand[2] = Lavg / 2;
                cand[3] = Lavg; cand[4] = 2LL * S; cand[5] = S;
                cand[6] = maxW / 4; cand[7] = maxW / 2;     /* only if some width was cut */
                nc0 = 6;
                for (c = 0; c < 6; c++) if (cand[c] > maxW) { cand[c] = maxW; nc0 = 8; }
                if (NARROW) { cand[nc0++] = S / 2; cand[nc0++] = S / 4; }   /* narrow strips */
                for (c = 0; c < nc0; c++) {
                    long long w = cand[c];
                    int dup = 0, q2;
                    if (w < 2) w = 2;
                    if (w > X) w = X;
                    for (q2 = 0; q2 < nw; q2++) if (widths[q2] == w) dup = 1;
                    if (!dup) widths[nw++] = (int)w;
                }
                qsort(widths, (size_t)nw, sizeof(int), cmp_int);
            }
            lnsStart = ops;
            lastImpOps = ops; lastImpStep = lnsSteps;
            lnsStall = (opsEnd - lnsStart) / LDS_STALL;
            cls_init(widths, nw);
            lns_sweep();
            if (saOn) sa_end();
        }
    }

    /* 3. output (sorted by user id; hand-formatted, buffered) */
    {
        int na = 0, sorted = 1;
        long long tot = 0;
        if (!remList) remList = (int *)xmalloc(sizeof(int) * ((size_t)N + 1));
        if (snapOut) {                      /* answer = kept construction */
            for (i = 0; i < N; i++) {
                U[i].assigned = snapA[i];
                if (snapA[i]) { U[i].rbs = snapPool + snapStart[i]; U[i].nrb = snapCnt[i]; }
            }
        }
        for (i = 0; i < N; i++) if (U[i].assigned) {
            if (na > 0 && U[i].id <= U[remList[na - 1]].id) sorted = 0;
            remList[na++] = i; tot += U[i].profit;
        }
        if (!sorted) qsort(remList, (size_t)na, sizeof(int), cmp_by_id);
        outBuf = (char *)malloc(OUT_CAP);
        if (!outBuf) {
            printf("%lld %d\n", tot, na);
            for (i = 0; i < na; i++) {
                User *u = &U[remList[i]];
                int r;
                printf("%lld %d", u->id, u->nrb);
                for (r = 0; r < u->nrb; r++)
                    printf(" %d %d %d %lld", u->rbs[r].h, u->rbs[r].w, u->rbs[r].y, segO ? comp_unmap(u->rbs[r].x) : (long long)u->rbs[r].x);
                printf("\n");
            }
        } else {
            out_ll(tot); out_c(' '); out_ll(na); out_c('\n');
            for (i = 0; i < na; i++) {
                User *u = &U[remList[i]];
                int r;
                out_room(48);
                out_ll(u->id); out_c(' '); out_ll(u->nrb);
                for (r = 0; r < u->nrb; r++) {
                    out_room(64);
                    out_c(' '); out_ll(u->rbs[r].h); out_c(' '); out_ll(u->rbs[r].w);
                    out_c(' '); out_ll(u->rbs[r].y); out_c(' '); out_ll(segO ? comp_unmap(u->rbs[r].x) : u->rbs[r].x);
                }
                out_c('\n');
            }
            out_flush();
        }
    }
    return 0;
}
/*
 * Data Structures Programming Project #1
 * 2D Resource Allocation Problem with NR (multi-numerology)
 *
 * Grid: Y rows (frequency) x X columns (time).  A resource block (RB) is an
 * h x w rectangle with h * w = S.  A user u with threshold b may use only the
 * rows whose bits are >= b, and then needs k = ceil(D / (S * b)) RBs inside
 * its time window [arr, dl].  All RBs of one user have the same shape here,
 * so the "same shape when overlapping in time" rule always holds.
 *
 * Method
 *   1. Options: for every user, the useful thresholds b (fewest RBs first).
 *   2. Placement of one user: for every option and every shape, RBs are put
 *      one by one at the earliest feasible column; within a short lookahead
 *      the spot touching the most occupied cells / borders is taken.  The
 *      shape with the best contact ratio wins; the first option that fits
 *      is used.
 *   3. Greedy construction: users by profit per area, best first.
 *   4. Local search (ruin and recreate): a time strip is emptied, the removed
 *      users and the best unserved users overlapping it are re-inserted
 *      greedily; the change is kept if the profit does not drop.
 *
 * The program is deterministic: no random numbers and no clock.  Run time is
 * bounded by a counter of elementary work steps (ops).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned long long u64;
typedef long long ll;

#define MAXSH   64              /* most shapes (divisors of S)            */
#ifndef MAXOPT
#define MAXOPT  6               /* most options kept per user             */
#endif
#ifndef OPT_NUM                 /* options need at most NUM/DEN * kmin + ADD RBs */
#define OPT_NUM 3
#define OPT_DEN 2
#define OPT_ADD 1
#endif
#ifndef WORK_LIMIT
#define WORK_LIMIT 80000000000LL   /* total work budget (0.1 ns units)        */
#endif
#ifndef MAXEVAL
#define MAXEVAL 1000000         /* most spots scored per RB               */
#endif
#ifndef LA_MIN
#define LA_MIN 32               /* ...but at least this many columns       */
#endif
#ifndef LA_MUL
#define LA_MUL 8                /* lookahead after the first fit, in RB widths */
#endif

/* ------------------------------------------------------------------ */
/* Input                                                              */
/* ------------------------------------------------------------------ */
static char ibuf[1 << 16];
static int ipos, ilen;
static long long ibytes;            /* input bytes read so far */

static int read_char(void) {
    if (ipos == ilen) {
        ilen = (int)fread(ibuf, 1, sizeof ibuf, stdin);
        ipos = 0;
        if (ilen > 0) ibytes += ilen;
        if (ilen <= 0) return -1;
    }
    return ibuf[ipos++];
}

static ll read_int(void) {
    int c = read_char(), neg = 0;
    ll v = 0;
    while (c != '-' && (c < '0' || c > '9')) {
        if (c < 0) return 0;
        c = read_char();
    }
    if (c == '-') { neg = 1; c = read_char(); }
    while (c >= '0' && c <= '9') { v = v * 10 + (c - '0'); c = read_char(); }
    return neg ? -v : v;
}

/* ------------------------------------------------------------------ */
/* Data                                                               */
/* ------------------------------------------------------------------ */
typedef struct {
    ll id, dem, prof;
    int arr, dl;        /* window, inclusive (compressed columns later) */
    int o0, no;         /* options [o0, o0 + no)                        */
    int first;          /* first RB node of the placement, -1 if none   */
    int nrb;
    int asg;            /* 1 if served                                  */
    int uOpt, uShape;   /* option and shape of the placement            */
    int stamp;
    double key;         /* priority: profit per BU of the cheapest option */
    double lp, la;      /* log(profit), log(smallest area)              */
} User;

static int Y, X, S, N, W, Xc;
static int nsh, shH[MAXSH], shW[MAXSH];
static int minW;                    /* narrowest shape width */
static User *U;

static int nOpt, capOpt;            /* options of all users */
static int *oK, *oRun;
static u64 *oMask;                  /* W words per option */

static u64 *occ;                    /* occupancy, column-major: Xc * W words */
static unsigned char *wallL;        /* wallL[c]: column c - 1 is not usable */

/*
 * Work counter.  A step of kind k is charged opW[k] units (0.1 ns each).
 * The weights are fitted to measured run times, separately for the input,
 * construction and local search phases; steps with random memory access
 * cost more when the working set is large (factor g, see set_weights()).
 */
static ll ops;
static ll opW[15];
enum { K_MARK, K_CAND, K_CONTACT, K_SPOT, K_SCAN, K_PLACE, K_BYTE, K_TREE,
       K_RUIN, K_NODE, K_CANDW, K_SPOTW, K_SETUP, K_FEN, K_TRIAL };
/* ns per step: base and per unit of g, for construction and local search */
static const double wCons[15][2] = {
    {0.83, 1.26}, {0.3, 0}, {1.41, 0}, {0.34, 0}, {0.49, 0}, {1.0, 116},
    {1.0, 0}, {4.8, 0}, {2.1, 0}, {515, 0}, {0.61, 0}, {0.35, 0},
    {20, 1.4}, {0.5, 0}, {137, 0}
};
static const double wLs[15][2] = {
    {9.2, 0.48}, {0.3, 0}, {1.19, 0}, {0.39, 0}, {0.1, 0}, {1.0, 18.4},
    {1.0, 0}, {4.8, 0}, {2.1, 0}, {10, 0}, {0.82, 0}, {0.17, 0},
    {20, 1.4}, {0.5, 0.16}, {44.6, 0}
};
static double memG;                 /* log2(working set / 8 MB), >= 0 */

static void set_weights(const double w[15][2]) {
    int k;
    for (k = 0; k < 15; k++) {
        opW[k] = (ll)(10.0 * (w[k][0] + w[k][1] * memG) + 0.5);
        if (opW[k] < 1) opW[k] = 1;
    }
}
#ifdef CALIB
#include <time.h>
static ll cnt[16];
static void calib_mark(const char *ph) {
    int k;
    fprintf(stderr, "PH %s %.4f", ph, (double)clock() / CLOCKS_PER_SEC);
    fprintf(stderr, " %d %d %d %d", N, Xc, W, nOpt);
    for (k = 0; k < 15; k++) fprintf(stderr, " %lld", cnt[k]);
    fprintf(stderr, "\n");
}
#define CALIB_MARK(ph) calib_mark(ph)
#else
#define CALIB_MARK(ph)
#endif
#ifdef CALIB
#define OPS(k, v) do { ll v_ = (v); ops += v_ * opW[k]; cnt[k] += v_; } while (0)
#else
#define OPS(k, v) (ops += (v) * opW[k])
#endif
static ll totalProfit;
static ll usedArea;

/* RB nodes: per-user chain and per-start-column doubly linked list */
static int *nY, *nX, *nS, *nU, *nNext, *cNext, *cPrev;
static int nodeCap, nodeTop, freeNode = -1;
static int *cHead;

/* scratch bit rows */
static u64 *tA, *tP, *tT, *tQ, *tO, *tN;

/* ------------------------------------------------------------------ */
/* Bit helpers                                                        */
/* ------------------------------------------------------------------ */
static int popcount64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static const int debruijn[64] = {
    0, 1, 48, 2, 57, 49, 28, 3, 61, 58, 50, 42, 38, 29, 17, 4,
    62, 55, 59, 36, 53, 51, 43, 22, 45, 39, 33, 30, 24, 18, 12, 5,
    63, 47, 56, 27, 60, 41, 37, 16, 54, 35, 52, 21, 44, 32, 23, 11,
    46, 26, 40, 15, 34, 20, 31, 10, 25, 14, 19, 9, 13, 8, 7, 6
};

static int lowest_bit(u64 x) {
    return debruijn[((x & (~x + 1)) * 0x03f79d71b4cb0a89ULL) >> 58];
}

/* mask of rows [y, y + h) inside word j */
static u64 row_mask(int j, int y, int h) {
    int lo = y - 64 * j, hi = y + h - 64 * j;   /* [lo, hi) relative */
    u64 m;
    if (lo < 0) lo = 0;
    if (hi > 64) hi = 64;
    if (lo >= hi) return 0;
    m = (hi == 64) ? ~0ULL : ((1ULL << hi) - 1);
    return m & ~((1ULL << lo) - 1);
}

/* dst = src >> s over W words */
static void shr_words(const u64 *src, int s, u64 *dst) {
    int q = s >> 6, r = s & 63, j;
    for (j = 0; j < W; j++) {
        u64 lo = (j + q < W) ? src[j + q] : 0;
        u64 hi = (j + q + 1 < W) ? src[j + q + 1] : 0;
        dst[j] = r ? ((lo >> r) | (hi << (64 - r))) : lo;
    }
}

/* P = rows y such that A has rows y .. y + h - 1 all set */
static void runs_words(const u64 *A, int h, u64 *P) {
    int len = 1, j;
    for (j = 0; j < W; j++) P[j] = A[j];
    while (len < h) {
        int st = (len < h - len) ? len : h - len;
        shr_words(P, st, tT);
        for (j = 0; j < W; j++) P[j] &= tT[j];
        len += st;
        OPS(10, 2 * (W + 2));
    }
}

static u64 runs1(u64 a, int h) {
    int len = 1;
    while (len < h && a) {
        int st = (len < h - len) ? len : h - len;
        a &= a >> st;
        len += st;
    }
    return a;
}

/* ------------------------------------------------------------------ */
/* Occupancy                                                          */
/* ------------------------------------------------------------------ */
static void set_rect(int y, int x, int s, int on) {
    int h = shH[s], w = shW[s], j, c;
    int j0 = y >> 6, j1 = (y + h - 1) >> 6;
    for (j = j0; j <= j1; j++) {
        u64 m = row_mask(j, y, h);
        u64 *p = occ + (size_t)x * W + j;
        if (on) for (c = 0; c < w; c++, p += W) *p |= m;
        else    for (c = 0; c < w; c++, p += W) *p &= ~m;
    }
    OPS(0, w * (j1 - j0 + 1) + 4);
}

/* Fenwick tree over columns: free cells (committed placements only) */
static ll *fen;

static void fen_add(int x, ll v) {
    for (x++; x <= Xc; x += x & -x) { fen[x] += v; OPS(13, 1); }
}

static ll fen_sum(int x) {          /* free cells in columns [0, x) */
    ll r = 0;
    for (; x > 0; x -= x & -x) { r += fen[x]; OPS(13, 1); }
    return r;
}

static void fen_init(void) {
    int x;
    fen = calloc(Xc + 1, sizeof(ll));
    if (!fen) exit(1);
    for (x = 1; x <= Xc; x++) {
        fen[x] += Y;
        if (x + (x & -x) <= Xc) fen[x + (x & -x)] += fen[x];
    }
}

static void fen_rect(int x, int s, int sign) {
    int c;
    for (c = 0; c < shW[s]; c++) fen_add(x + c, (ll)sign * shH[s]);
    OPS(0, shW[s]);
}

/* number of occupied cells in rows [y, y + h) of column c */
static int col_count(int c, int y, int h) {
    const u64 *p = occ + (size_t)c * W;
    int j = y >> 6, r = y & 63, n = 0;
    if (h <= 64) {
        u64 v = p[j] >> r;
        if (r + h > 64) v |= p[j + 1] << (64 - r);
        if (h < 64) v &= (1ULL << h) - 1;
        return popcount64(v);
    }
    for (j = y >> 6; j <= (y + h - 1) >> 6; j++) n += popcount64(p[j] & row_mask(j, y, h));
    return n;
}

static int cell(int c, int y) {
    return (int)((occ[(size_t)c * W + (y >> 6)] >> (y & 63)) & 1);
}

/*
 * Candidate start rows for an h x w block at column x, rows limited to M:
 * fills tA (free rows over the w columns), tP (feasible start rows that sit
 * at the bottom or the top of a free run), tO / tN (OR / AND of the w
 * occupancy columns, used by contact()).  Returns 0 if there is none.
 */
static int candidates(int x, int h, int w, const u64 *M) {
    int j, c;
    u64 any = 0;
    if (W == 1) {
        u64 a = M[0], p, o = 0, n = ~0ULL;
        const u64 *q = occ + x;
        for (c = 0; c < w; c++) {
            o |= q[c]; n &= q[c];
            a &= ~q[c];
            if (!a) break;
        }
        OPS(1, c + 1);
        if (!a) return 0;
        p = runs1(a, h);
        if (!p) return 0;
        tA[0] = a; tO[0] = o; tN[0] = n;
        tP[0] = p & (~(a << 1) | ~(h < 64 ? a >> h : 0));
        return 1;
    }
    for (j = 0; j < W; j++) { tA[j] = M[j]; tO[j] = 0; tN[j] = ~0ULL; }
    for (c = 0; c < w; c++) {
        const u64 *q = occ + (size_t)(x + c) * W;
        any = 0;
        for (j = 0; j < W; j++) {
            tO[j] |= q[j]; tN[j] &= q[j];
            tA[j] &= ~q[j]; any |= tA[j];
        }
        if (!any) break;
    }
    OPS(10, (c + 1) * (W + 2));
    if (!any) return 0;
    runs_words(tA, h, tP);
    any = 0;
    for (j = 0; j < W; j++) any |= tP[j];
    if (!any) return 0;
    /* bottom aligned: row y - 1 not free; top aligned: row y + h not free */
    shr_words(tA, h, tQ);
    for (j = 0; j < W; j++) {
        u64 up = (tA[j] << 1) | (j ? tA[j - 1] >> 63 : 0);
        tP[j] &= ~up | ~tQ[j];
    }
    OPS(10, 4 * (W + 2));
    return 1;
}

/* occupied cells of row r over the w columns starting at x (tO / tN known) */
static int row_contact(int r, int x, int w) {
    int c, n = 0;
    u64 b = 1ULL << (r & 63);
    if (tN[r >> 6] & b) return w;
    if (!(tO[r >> 6] & b)) return 0;
    for (c = 0; c < w; c++) n += cell(x + c, r);
    OPS(2, w);
    return n;
}

/* occupied cells / borders around an h x w block at (y, x) */
static int contact(int y, int x, int h, int w) {
    int n = 0;
    n += (x == 0 || wallL[x]) ? h : col_count(x - 1, y, h);
    n += (x + w == Xc || wallL[x + w]) ? h : col_count(x + w, y, h);
    n += (y == 0) ? w : row_contact(y - 1, x, w);
    n += (y + h == Y) ? w : row_contact(y + h, x, w);
    OPS(2, 6);
    return n;
}

/* ------------------------------------------------------------------ */
/* Free-spot bitsets: spot[s] bit x = some h x w block of shape s is     */
/* free (on any rows) starting at column x.  A necessary condition used  */
/* to skip columns; kept exact for the committed placements.             */
/* ------------------------------------------------------------------ */
static u64 *spot[MAXSH];
static int spotWords;

static int spot_at(int s, int x) {
    int h = shH[s], w = shW[s], c, j;
    if (W == 1) {
        u64 a = (Y == 64) ? ~0ULL : ((1ULL << Y) - 1);
        const u64 *q = occ + x;
        for (c = 0; c < w && a; c++) a &= ~q[c];
        OPS(3, c + 2);
        return runs1(a, h) != 0;
    }
    for (j = 0; j < W; j++) tA[j] = row_mask(j, 0, Y);
    for (c = 0; c < w; c++) {
        const u64 *q = occ + (size_t)(x + c) * W;
        u64 any = 0;
        for (j = 0; j < W; j++) { tA[j] &= ~q[j]; any |= tA[j]; }
        if (!any) { OPS(11, (c + 1) * (W + 2)); return 0; }
    }
    OPS(11, (w + 4) * (W + 2));
    runs_words(tA, h, tQ);
    for (j = 0; j < W; j++) if (tQ[j]) return 1;
    return 0;
}

/*
 * Recomputes the spot bits of all shapes that cover columns [x0, x1].
 * how = 1: cells were occupied (only set bits can change), 0: cells were
 * freed (only clear bits can change), 2: everything.
 */
static void spot_update(int x0, int x1, int how) {
    int s, x;
    for (s = 0; s < nsh; s++) {
        int lo = x0 - shW[s] + 1, hi = x1;
        if (lo < 0) lo = 0;
        if (hi > Xc - shW[s]) hi = Xc - shW[s];
        for (x = lo; x <= hi; x++) {
            u64 b = 1ULL << (x & 63), *wd = &spot[s][x >> 6];
            if (how == 1 && !(*wd & b)) continue;
            if (how == 0 && (*wd & b)) continue;
            if (spot_at(s, x)) *wd |= b;
            else *wd &= ~b;
        }
        OPS(4, hi - lo + 1);
    }
}

/* first column >= x (and <= last) where shape s may start, or last + 1 */
static int next_spot(int s, int x, int last) {
    int i, e;
    u64 m;
    if (x > last) return last + 1;
    i = x >> 6; e = last >> 6;
    m = spot[s][i] & (~0ULL << (x & 63));
    while (!m) {
        if (++i > e) return last + 1;
        m = spot[s][i];
        OPS(4, 1);
    }
    x = 64 * i + lowest_bit(m);
    return x <= last ? x : last + 1;
}

static void spot_init(void) {
    int s;
    spotWords = (Xc + 63) / 64 + 1;
    for (s = 0; s < nsh; s++) {
        spot[s] = calloc(spotWords, sizeof(u64));
        if (!spot[s]) exit(1);
    }
    if (Xc > 0) spot_update(0, Xc - 1, 2);
}

/* ------------------------------------------------------------------ */
/* RB nodes                                                           */
/* ------------------------------------------------------------------ */
static void grow_nodes(void) {
    int nc = nodeCap ? nodeCap * 2 : 1024;
    nY = realloc(nY, sizeof(int) * nc);
    nX = realloc(nX, sizeof(int) * nc);
    nS = realloc(nS, sizeof(int) * nc);
    nU = realloc(nU, sizeof(int) * nc);
    nNext = realloc(nNext, sizeof(int) * nc);
    cNext = realloc(cNext, sizeof(int) * nc);
    cPrev = realloc(cPrev, sizeof(int) * nc);
    if (!nY || !nX || !nS || !nU || !nNext || !cNext || !cPrev) exit(1);
    nodeCap = nc;
}

static void add_rb(int u, int y, int x, int s) {
    int id;
    if (freeNode >= 0) { id = freeNode; freeNode = nNext[id]; }
    else { if (nodeTop == nodeCap) grow_nodes(); id = nodeTop++; }
    nY[id] = y; nX[id] = x; nS[id] = s; nU[id] = u;
    nNext[id] = U[u].first; U[u].first = id; U[u].nrb++;
    OPS(9, 1);
    cPrev[id] = -1; cNext[id] = cHead[x];
    if (cHead[x] >= 0) cPrev[cHead[x]] = id;
    cHead[x] = id;
    set_rect(y, x, s, 1);
    fen_rect(x, s, -1);
    spot_update(x, x + shW[s] - 1, 1);
}

static void tree_set(int u);

static void assign_done(int u) {
    U[u].asg = 1;
    totalProfit += U[u].prof;
    usedArea += (ll)U[u].nrb * S;
    tree_set(u);
}

static void remove_user(int u) {
    int id = U[u].first;
    while (id >= 0) {
        int nx = nNext[id];
        set_rect(nY[id], nX[id], nS[id], 0);
        fen_rect(nX[id], nS[id], 1);
        spot_update(nX[id], nX[id] + shW[nS[id]] - 1, 0);
        if (cPrev[id] >= 0) cNext[cPrev[id]] = cNext[id];
        else cHead[nX[id]] = cNext[id];
        if (cNext[id] >= 0) cPrev[cNext[id]] = cPrev[id];
        nNext[id] = freeNode; freeNode = id;
        OPS(9, 1);
        id = nx;
    }
    U[u].first = -1;
    if (U[u].asg) {
        totalProfit -= U[u].prof;
        usedArea -= (ll)U[u].nrb * S;
        U[u].nrb = 0; U[u].asg = 0;
        tree_set(u);
    }
    U[u].nrb = 0;
}

/* ------------------------------------------------------------------ */
/* Placement of one user                                              */
/* ------------------------------------------------------------------ */
static int *trY, *trX, *bsY, *bsX;  /* trial / best positions */
/* placement effort: lookahead (RB widths), spots scored per RB, options and
   whether the first shape that fits is taken */
static int lookMul = LA_MUL, maxEval = MAXEVAL, maxOpt = MAXOPT, firstShape = 0;
static int posCap;

static void ensure_pos(int k) {
    if (k <= posCap) return;
    while (posCap < k) posCap = posCap ? posCap * 2 : 64;
    trY = realloc(trY, sizeof(int) * posCap);
    trX = realloc(trX, sizeof(int) * posCap);
    bsY = realloc(bsY, sizeof(int) * posCap);
    bsX = realloc(bsX, sizeof(int) * posCap);
    if (!trY || !trX || !bsY || !bsX) exit(1);
}

/*
 * Puts k blocks of shape s in columns [ca, cb] on rows M, one by one.
 * Returns the summed contact, or -1 if they do not all fit.  The blocks are
 * removed again before returning.
 */
static ll trial(int s, int k, const u64 *M, int ca, int cb) {
    int h = shH[s], w = shW[s], last = cb - w + 1, x = ca, r, j;
    ll sum = 0;
    for (r = 0; r < k; r++) {
        int xf, xe, xx, bestC = -1, by = 0, bx = 0, ne = 0;
        x = next_spot(s, x, last);
        while (x <= last && !candidates(x, h, w, M)) x = next_spot(s, x + 1, last);
        if (x > last) break;
        xf = x;
        xe = xf + (lookMul ? (lookMul * w > LA_MIN ? lookMul * w : LA_MIN) : 0);
        if (xe > last) xe = last;
        for (xx = xf; xx <= xe && ne < maxEval; xx++) {
            if (xx > xf) {
                xx = next_spot(s, xx, xe);
                if (xx > xe) break;
                if (!candidates(xx, h, w, M)) continue;
            }
            for (j = 0; j < W && ne < maxEval; j++) {
                u64 p = tP[j];
                while (p && ne++ < maxEval) {
                    int y = 64 * j + lowest_bit(p), c;
                    p &= p - 1;
                    c = contact(y, xx, h, w);
                    if (c > bestC) { bestC = c; by = y; bx = xx; }
                }
            }
        }
        trY[r] = by; trX[r] = bx;
        set_rect(by, bx, s, 1);
        sum += bestC;
    }
    for (j = 0; j < r; j++) set_rect(trY[j], trX[j], s, 0);
    return r == k ? sum : -1;
}

/* Places user u inside columns [ca, cb] (already within its window). */
static int place_user(int u, int ca, int cb) {
    User *p = &U[u];
    int o, s, L = cb - ca + 1;
    ll freeCells;
    if (L < minW) return 0;
    freeCells = fen_sum(cb + 1) - fen_sum(ca);
    OPS(5, 1);
    for (o = p->o0; o < p->o0 + p->no && o < p->o0 + maxOpt; o++) {
        int k = oK[o], bestS = -1, r;
        ll bestNum = 0, bestDen = 1;
        const u64 *M = oMask + (size_t)o * W;
        if ((ll)k * S > freeCells) break;   /* later options need even more */
        ensure_pos(k);
        for (s = 0; s < nsh && !(firstShape && bestS >= 0); s++) {
            ll c, den;
            if (shW[s] > L || shH[s] > oRun[o]) continue;
            OPS(14, 1);
            c = trial(s, k, M, ca, cb);
            if (c < 0) continue;
            den = (ll)k * 2 * (shH[s] + shW[s]);
            if (bestS < 0 || c * bestDen > bestNum * den) {
                bestS = s; bestNum = c; bestDen = den;
                memcpy(bsY, trY, sizeof(int) * k);
                memcpy(bsX, trX, sizeof(int) * k);
            }
        }
        if (bestS >= 0) {
            for (r = 0; r < k; r++) add_rb(u, bsY[r], bsX[r], bestS);
            p->uOpt = o; p->uShape = bestS;
            assign_done(u);
            return 1;
        }
    }
    return 0;
}

/* ------------------------------------------------------------------ */
/* x^a for x > 0 without the math library                              */
/* ------------------------------------------------------------------ */
static double my_log(double x) {
    double r = 0, t, t2, sum;
    int i;
    if (x <= 0) return -1e300;
    while (x > 2) { x /= 2; r += 0.69314718055994531; }
    while (x < 1) { x *= 2; r -= 0.69314718055994531; }
    t = (x - 1) / (x + 1); t2 = t * t; sum = 0;
    for (i = 39; i >= 1; i -= 2) sum = sum * t2 + 1.0 / i;
    return r + 2 * t * sum;
}

static double my_exp(double x) {
    double r = 1, term = 1;
    int i, n = 0;
    while (x > 0.5) { x /= 2; n++; }
    while (x < -0.5) { x /= 2; n++; }
    for (i = 1; i < 20; i++) { term *= x / i; r += term; }
    while (n--) r *= r;
    return r;
}

#ifndef KEY_ALPHA
#define KEY_ALPHA 1.0
#endif

/* ------------------------------------------------------------------ */
/* Setup                                                              */
/* ------------------------------------------------------------------ */
static int cntVal[65536];

static void grow_options(void) {
    int nc = capOpt ? capOpt * 2 : 4096;
    oK = realloc(oK, sizeof(int) * nc);
    oRun = realloc(oRun, sizeof(int) * nc);
    oMask = realloc(oMask, sizeof(u64) * (size_t)nc * W);
    if (!oK || !oRun || !oMask) exit(1);
    capOpt = nc;
}

static int cmp_desc_int(const void *a, const void *b) {
    return *(const int *)b - *(const int *)a;
}

/* smallest shape height usable in a window of L columns */
static int min_height(int L) {
    int s, best = 1 << 30;
    for (s = 0; s < nsh; s++) if (shW[s] <= L && shH[s] < best) best = shH[s];
    return best;
}

/* Builds the options of user u from its bits (one value per row). */
static void build_options(int u, const int *bits, int *vals) {
    User *p = &U[u];
    int nv = 0, y, i, L = p->dl - p->arr + 1, hmin, kmin = -1;
    ll dem = p->dem > 0 ? p->dem : 1;
    p->o0 = nOpt; p->no = 0;
    if (L <= 0 || p->prof <= 0) return;
    hmin = min_height(L);
    if (hmin > Y) return;
    for (y = 0; y < Y; y++) {
        int v = bits[y];
        if (v <= 0) continue;
        if (cntVal[v]++ == 0) vals[nv++] = v;
    }
    qsort(vals, nv, sizeof(int), cmp_desc_int);
    {
        int rows = 0;
        for (i = 0; i < nv; i++) {
            int v = vals[i], run = 0, cur = 0, j;
            ll k, kNext;
            rows += cntVal[v];
            k = (dem + (ll)S * v - 1) / ((ll)S * v);
            if (i + 1 < nv) {
                ll sv = (ll)S * vals[i + 1];
                kNext = (dem + sv - 1) / sv;
                if (kNext == k) continue;           /* lower threshold: same k, more rows */
            }
            if (kmin > 0 && k * OPT_DEN > (ll)kmin * OPT_NUM + OPT_ADD * OPT_DEN) break;
            if (p->no >= MAXOPT) break;
            if (k * S > (ll)rows * L) continue;      /* cannot fit at all */
            for (y = 0; y < Y; y++) {
                if (bits[y] >= v) { if (++cur > run) run = cur; }
                else cur = 0;
            }
            if (run < hmin) continue;
            if (nOpt == capOpt) grow_options();
            oK[nOpt] = (int)k;
            oRun[nOpt] = run;
            {
                u64 *m = oMask + (size_t)nOpt * W;
                for (j = 0; j < W; j++) m[j] = 0;
                for (y = 0; y < Y; y++) if (bits[y] >= v) m[y >> 6] |= 1ULL << (y & 63);
            }
            nOpt++;
            p->no++;
            if (kmin < 0) kmin = (int)k;
        }
    }
    for (i = 0; i < nv; i++) cntVal[vals[i]] = 0;
    if (p->no) {
        p->lp = my_log((double)p->prof);
        p->la = my_log((double)kmin * S);
        p->key = my_exp(p->lp - KEY_ALPHA * p->la);
    }
}

typedef struct { int a, b; } Iv;

static int cmp_iv(const void *a, const void *b) {
    const Iv *p = a, *q = b;
    return p->a != q->a ? (p->a < q->a ? -1 : 1) : (p->b < q->b ? -1 : p->b > q->b);
}

static Iv *ivs;         /* merged covered intervals (original columns) */
static int *ivStart;    /* compressed start of each interval */
static int nIv;

static int map_col(int x) {
    int lo = 0, hi = nIv - 1;
    while (lo < hi) {
        int mid = (lo + hi + 1) / 2;
        if (ivs[mid].a <= x) lo = mid; else hi = mid - 1;
    }
    return ivStart[lo] + (x - ivs[lo].a);
}

static int unmap_col(int c) {
    int lo = 0, hi = nIv - 1;
    while (lo < hi) {
        int mid = (lo + hi + 1) / 2;
        if (ivStart[mid] <= c) lo = mid; else hi = mid - 1;
    }
    return ivs[lo].a + (c - ivStart[lo]);
}

/* Removes the columns no window covers. */
static void compress_time(void) {
    int i, n = 0, c = 0;
    Iv *t = malloc(sizeof(Iv) * (N + 1));
    if (!t) exit(1);
    for (i = 0; i < N; i++) if (U[i].no) { t[n].a = U[i].arr; t[n].b = U[i].dl; n++; }
    qsort(t, n, sizeof(Iv), cmp_iv);
    ivs = malloc(sizeof(Iv) * (n + 1));
    ivStart = malloc(sizeof(int) * (n + 1));
    if (!ivs || !ivStart) exit(1);
    nIv = 0;
    for (i = 0; i < n; i++) {
        if (nIv && t[i].a <= ivs[nIv - 1].b + 1) {
            if (t[i].b > ivs[nIv - 1].b) ivs[nIv - 1].b = t[i].b;
        } else ivs[nIv++] = t[i];
    }
    for (i = 0; i < nIv; i++) { ivStart[i] = c; c += ivs[i].b - ivs[i].a + 1; }
    Xc = c;
    wallL = calloc(Xc + 1, 1);
    if (!wallL) exit(1);
    for (i = 1; i < nIv; i++) wallL[ivStart[i]] = 1;
    for (i = 0; i < N; i++) if (U[i].no) { U[i].arr = map_col(U[i].arr); U[i].dl = map_col(U[i].dl); }
    free(t);
}

static void read_input(void) {
    int i, y, s, *bits, *vals;
    ll lastBytes = 0;
    Y = (int)read_int(); X = (int)read_int(); S = (int)read_int(); N = (int)read_int();
    W = (Y + 63) / 64;
    nsh = 0; minW = 1 << 30;
    for (s = 1; s <= S && nsh < MAXSH; s++) {
        if (S % s) continue;
        if (s <= Y && S / s <= X) {
            shH[nsh] = s; shW[nsh] = S / s;
            if (S / s < minW) minW = S / s;
            nsh++;
        }
    }
    U = calloc(N > 0 ? N : 1, sizeof(User));
    bits = malloc(sizeof(int) * (Y + 1));
    vals = malloc(sizeof(int) * (Y + 1));
    if (!U || !bits || !vals) exit(1);
    for (i = 0; i < N; i++) {
        User *p = &U[i];
        p->id = read_int(); p->dem = read_int();
        p->arr = (int)read_int(); p->dl = (int)read_int();
        p->prof = read_int();
        for (y = 0; y < Y; y++) {
            ll v = read_int();
            bits[y] = v > 65535 ? 65535 : (int)v;
        }
        if (p->arr < 0) p->arr = 0;
        if (p->dl > X - 1) p->dl = X - 1;
        p->first = -1;
        if (nsh) build_options(i, bits, vals);
        if (p->prof <= 0) p->no = 0;
        OPS(6, ibytes - lastBytes);
        lastBytes = ibytes;
        OPS(12, Y + 10);
    }
    free(bits); free(vals);
}

/* ------------------------------------------------------------------ */
/* Greedy construction                                                */
/* ------------------------------------------------------------------ */
static int *order;

#ifndef CONS_FRAC
#define CONS_FRAC 0.6               /* share of the budget for the construction */
#endif
#define NMODE 4
/* relative cost of the placement modes (measured) */
static const double modeCost[NMODE] = { 1.0, 0.45, 0.2, 0.08 };
static int curMode;

static void set_mode(int m) {
    curMode = m;
    lookMul = m == 0 ? LA_MUL : 0;
    maxEval = m <= 1 ? MAXEVAL : (m == 2 ? 16 : 2);
    maxOpt = m <= 1 ? MAXOPT : (m == 2 ? 3 : 1);
    firstShape = m == 3;
}

/*
 * Places the users order[0 .. n-1] greedily within `budget` ops.  At
 * checkpoints the cost per user of the recent segment is projected over
 * the remaining users and the cheapest sufficient mode is chosen.
 */
#ifndef LA_CORE
#define LA_CORE 8                   /* lookahead for the users that fill the grid */
#endif
#ifndef CORE_FRAC
#define CORE_FRAC 1.0
#endif
static void build_pass(int n, ll budget) {
    ll start = ops, segOps = ops;
    int i, seg = n / 256 + 1, segI = 0;
    double area = 0, core = CORE_FRAC * Y * (double)Xc;
    set_mode(0);
    for (i = 0; i < n; i++) {
        int u = order[i];
        if (curMode == 0) lookMul = area < core ? LA_CORE : LA_MUL;
        area += (double)oK[U[u].o0] * S;
        if (i - segI >= seg) {
            double per = (double)(ops - segOps) / (i - segI) / modeCost[curMode];
            double left = (double)(budget - (ops - start));
            int m = 0;
            while (m < NMODE - 1 && per * modeCost[m] * (n - i) > left) m++;
            set_mode(m);
            segOps = ops; segI = i;
        }
        if (ops - start > budget + budget / 10) break;   /* hard stop */
        place_user(u, U[u].arr, U[u].dl);
    }
#ifdef DEBUG
    fprintf(stderr, "mode %d at %d/%d ", curMode, i, n);
#endif
    set_mode(0);
}

#ifndef MULTI_FRAC
#define MULTI_FRAC 0.3              /* extra constructions while under this share */
#endif
static const double consAlpha[] = { 1.0, 0.85, 1.15, 0.7, 1.3, 0.55 };
static double curAlpha = 1.0;       /* order: profit / area^curAlpha */
static int cmp_cand(const void *a, const void *b);
static void snap_alloc(void);
static void save_best(void);
static void restore_best(void);
static ll snapP = -1;               /* profit of the saved best solution */

static double *prio;                /* construction priorities */

static int cmp_prio(const void *a, const void *b) {
    int i = *(const int *)a, j = *(const int *)b;
    if (prio[i] != prio[j]) return prio[i] > prio[j] ? -1 : 1;
    return i - j;
}

#ifndef SWO_FRAC
#define SWO_FRAC 0.4                /* squeaky-wheel rounds while under this share */
#endif
#ifndef SWO_STALL
#define SWO_STALL 15                /* rounds without a better solution */
#endif
#ifndef SWO_LOG
#define SWO_LOG 0.18                /* log of the priority boost per round */
#endif

/*
 * Greedy constructions.  First with different exponents of the profit /
 * area order, then "squeaky wheel" rounds: starting from the best order,
 * every user left out gets a higher priority and the greedy is run again.
 * The best solution is kept.
 */
static void construct(void) {
    int i, n = 0, v, bestV = 0, vBest = 0;
    ll budget = (ll)(WORK_LIMIT * CONS_FRAC), start = ops, first = 0, last;
    order = malloc(sizeof(int) * (N + 1));
    prio = malloc(sizeof(double) * (N + 1));
    if (!order || !prio) exit(1);
    snap_alloc();
    for (i = 0; i < N; i++) if (U[i].no) order[n++] = i;
    for (v = 0; v < (int)(sizeof consAlpha / sizeof consAlpha[0]); v++) {
        ll t0 = ops;
        if (v > 0) {
            if (ops - start + first + first / 4 > (ll)(WORK_LIMIT * MULTI_FRAC)) break;
            for (i = 0; i < N; i++) if (U[i].first >= 0) remove_user(i);
        }
        curAlpha = consAlpha[v];
        qsort(order, n, sizeof(int), cmp_cand);
        OPS(K_RUIN, 20LL * n);
        build_pass(n, budget - (ops - start));
        if (v == 0) first = ops - t0;
#ifdef DEBUG
        fprintf(stderr, "c%d=%lld ", v, totalProfit);
#endif
        if (totalProfit > snapP) { save_best(); bestV = v; }
    }
    /* squeaky wheel from the best exponent */
    for (i = 0; i < N; i++) prio[i] = U[i].lp - consAlpha[bestV] * U[i].la;
    last = first;
    for (v = 0; ops - start + last + last / 4 <= (ll)(WORK_LIMIT * SWO_FRAC) && v - vBest <= SWO_STALL; v++) {
        ll t0 = ops;
        int left = 0;
        if (v == 0) restore_best();         /* continue from the best solution */
        for (i = 0; i < n; i++) if (!U[order[i]].asg) { prio[order[i]] += SWO_LOG; left++; }
        if (!left) break;                   /* everybody is served */
        for (i = 0; i < N; i++) if (U[i].first >= 0) remove_user(i);
        qsort(order, n, sizeof(int), cmp_prio);
        OPS(K_RUIN, 20LL * n);
        build_pass(n, budget - (ops - start));
        last = ops - t0;
#ifdef DEBUG
        if (totalProfit > snapP) fprintf(stderr, "s%d=%lld ", v, totalProfit);
#endif
        if (totalProfit > snapP) { save_best(); vBest = v; }
    }
#ifdef DEBUG
    fprintf(stderr, "swo %d ", v);
#endif
    if (snapP > totalProfit) restore_best();
    curAlpha = 1.0;
}

/* ------------------------------------------------------------------ */
/* Local search: ruin and recreate over time strips                   */
/* ------------------------------------------------------------------ */
#define NCLS 256
static int *clsUsers[NCLS], clsN[NCLS];   /* users by window-length class, sorted by arrival */
static int clsMaxL[NCLS];                 /* longest window in each class */
static int stampNow;

static int cmp_arr(const void *a, const void *b) {
    const User *p = &U[*(const int *)a], *q = &U[*(const int *)b];
    if (p->arr != q->arr) return p->arr < q->arr ? -1 : 1;
    return *(const int *)a - *(const int *)b;
}

/* eight classes per doubling of the window length */
static int len_class(int L) {
    int e = 0;
    while ((2LL << e) <= L && e < 30) e++;
    return 8 * e + (int)(((ll)(L - (1LL << e)) * 8) >> e);
}

static void build_classes(void) {
    int i, c;
    for (i = 0; i < N; i++) if (U[i].no) clsN[len_class(U[i].dl - U[i].arr + 1)]++;
    for (c = 0; c < NCLS; c++) {
        clsUsers[c] = malloc(sizeof(int) * (clsN[c] + 1));
        if (!clsUsers[c]) exit(1);
        clsN[c] = 0;
    }
    for (i = 0; i < N; i++) if (U[i].no) {
        int L = U[i].dl - U[i].arr + 1;
        c = len_class(L);
        clsUsers[c][clsN[c]++] = i;
        if (L > clsMaxL[c]) clsMaxL[c] = L;
    }
    for (c = 0; c < NCLS; c++) qsort(clsUsers[c], clsN[c], sizeof(int), cmp_arr);
}

static int *candList, candCap, nCand;
static int *remList, nRem;
static int *insList, nIns;
static int *svOff, *svY, *svX, *svS, svCap, nSv;
static int *svOpt, *svShape, *need;

static void push_cand(int u) {
    if (nCand == candCap) {
        candCap = candCap ? candCap * 2 : 1024;
        candList = realloc(candList, sizeof(int) * candCap);
        if (!candList) exit(1);
    }
    candList[nCand++] = u;
}

static void save_rb(int y, int x, int s) {
    if (nSv == svCap) {
        svCap = svCap ? svCap * 2 : 1024;
        svY = realloc(svY, sizeof(int) * svCap);
        svX = realloc(svX, sizeof(int) * svCap);
        svS = realloc(svS, sizeof(int) * svCap);
        if (!svY || !svX || !svS) exit(1);
    }
    svY[nSv] = y; svX[nSv] = x; svS[nSv] = s; nSv++;
}

/* unserved users whose window meets columns [x0, x1] */
/*
 * Unserved users by window class: a max-tree over each class (sorted by
 * arrival) holds the key of every unserved user, so the best unserved
 * users overlapping a strip are found best-first.
 */
static double *trV[NCLS];
static int trP[NCLS], treeOn;
static int *posIn;                  /* position of a user in its class */
static double *hV; static int *hC, *hN, hCap, hLen;

static void tree_set(int u) {
    int c, i;
    double v;
    if (!treeOn || !U[u].no) return;
    c = len_class(U[u].dl - U[u].arr + 1);
    i = trP[c] + posIn[u];
    v = U[u].asg ? -1.0 : U[u].key;
    trV[c][i] = v;
    for (i >>= 1; i; i >>= 1) {
        double m = trV[c][2 * i] > trV[c][2 * i + 1] ? trV[c][2 * i] : trV[c][2 * i + 1];
        OPS(7, 1);
        if (trV[c][i] == m) break;
        trV[c][i] = m;
    }
}

static void build_trees(void) {
    int c, i;
    posIn = malloc(sizeof(int) * (N + 1));
    if (!posIn) exit(1);
    for (c = 0; c < NCLS; c++) {
        int P = 1;
        while (P < clsN[c]) P *= 2;
        trP[c] = P;
        trV[c] = malloc(sizeof(double) * 2 * P);
        if (!trV[c]) exit(1);
        for (i = 0; i < 2 * P; i++) trV[c][i] = -1.0;
        for (i = 0; i < clsN[c]; i++) {
            int u = clsUsers[c][i];
            posIn[u] = i;
            trV[c][P + i] = U[u].asg ? -1.0 : U[u].key;
        }
        for (i = P - 1; i >= 1; i--)
            trV[c][i] = trV[c][2 * i] > trV[c][2 * i + 1] ? trV[c][2 * i] : trV[c][2 * i + 1];
    }
    treeOn = 1;
}

static void heap_push(double v, int c, int n) {
    int i;
    if (hLen == hCap) {
        hCap = hCap ? 2 * hCap : 1024;
        hV = realloc(hV, sizeof(double) * hCap);
        hC = realloc(hC, sizeof(int) * hCap);
        hN = realloc(hN, sizeof(int) * hCap);
        if (!hV || !hC || !hN) exit(1);
    }
    i = hLen++;
    while (i > 0 && hV[(i - 1) / 2] < v) {
        int p = (i - 1) / 2;
        hV[i] = hV[p]; hC[i] = hC[p]; hN[i] = hN[p];
        i = p;
    }
    hV[i] = v; hC[i] = c; hN[i] = n;
    OPS(7, 4);
}

static void heap_pop(void) {
    double v;
    int c, n, i = 0;
    hLen--;
    v = hV[hLen]; c = hC[hLen]; n = hN[hLen];
    for (;;) {
        int l = 2 * i + 1, b;
        if (l >= hLen) break;
        b = (l + 1 < hLen && hV[l + 1] > hV[l]) ? l + 1 : l;
        if (hV[b] <= v) break;
        hV[i] = hV[b]; hC[i] = hC[b]; hN[i] = hN[b];
        i = b;
    }
    hV[i] = v; hC[i] = c; hN[i] = n;
    OPS(7, 4);
}

/* adds up to `want` of the best unserved users whose window meets [x0, x1] */
static void collect_unserved(int x0, int x1, int want) {
    int c, got = 0;
    hLen = 0;
    for (c = 0; c < NCLS; c++) {
        int *a = clsUsers[c], n = clsN[c], lo = 0, hi = n, lim = x0 - clsMaxL[c] + 1, l, r;
        if (!n) continue;
        while (lo < hi) {
            int mid = (lo + hi) / 2;
            if (U[a[mid]].arr < lim) lo = mid + 1; else hi = mid;
        }
        l = lo; hi = n;
        while (l < hi) {
            int mid = (l + hi) / 2;
            if (U[a[mid]].arr <= x1) l = mid + 1; else hi = mid;
        }
        OPS(7, 40);
        for (l = lo + trP[c], r = hi + trP[c]; l < r; l >>= 1, r >>= 1) {
            if (l & 1) { if (trV[c][l] > 0) heap_push(trV[c][l], c, l); l++; }
            if (r & 1) { --r; if (trV[c][r] > 0) heap_push(trV[c][r], c, r); }
        }
    }
    while (hLen > 0 && got < want) {
        int cc = hC[0], nd = hN[0];
        heap_pop();
        if (nd >= trP[cc]) {
            int u = clsUsers[cc][nd - trP[cc]];
            if (!U[u].asg && U[u].dl >= x0 && U[u].stamp != stampNow) {
                U[u].stamp = stampNow;
                need[u] = 0;
                push_cand(u);
                got++;
            }
        } else {
            if (trV[cc][2 * nd] > 0) heap_push(trV[cc][2 * nd], cc, 2 * nd);
            if (trV[cc][2 * nd + 1] > 0) heap_push(trV[cc][2 * nd + 1], cc, 2 * nd + 1);
        }
    }
}

static int cmp_cand(const void *a, const void *b) {
    int i = *(const int *)a, j = *(const int *)b;
    double ki = U[i].lp - curAlpha * U[i].la, kj = U[j].lp - curAlpha * U[j].la;
    if (ki != kj) return ki > kj ? -1 : 1;
    return i - j;
}

static ll stIt, stAcc, stRem, stCand, stImp;

/*
 * One ruin-and-recreate step on the rectangle columns [x0, x1] x rows
 * [y0, y1].  Every RB inside it is taken out.  A user that lost all its RBs
 * is placed again from scratch; a user that lost only some of them must put
 * that many RBs back (same shape and rows) near the rectangle, or it is
 * dropped.  The best unserved users overlapping the strip are tried too.
 * The change is kept if the profit does not drop.  Returns the number of
 * users touched.
 */
static int needSave;
#ifndef SPAN_MUL
#define SPAN_MUL 4
#endif
static int ruin_recreate(int x0, int x1, int y0, int y1, int maxCand, ll thr) {
    int c, i, rx0, rx1, wmax = 0, spanLim;
    ll oldP = totalProfit, oldA = usedArea;
    for (i = 0; i < nsh; i++) if (shW[i] > wmax) wmax = shW[i];
    rx0 = x0 - wmax + 1; if (rx0 < 0) rx0 = 0;
    rx1 = x1 + wmax - 1; if (rx1 > Xc - 1) rx1 = Xc - 1;
    spanLim = SPAN_MUL * (x1 - x0 + 1 + wmax);
    stampNow++;
    nRem = 0; nCand = 0; nSv = 0;
    for (c = x0 - wmax + 1; c <= x1; c++) {
        int id;
        if (c < 0) continue;
        for (id = cHead[c]; id >= 0; id = cNext[id]) {
            int u = nU[id];
            OPS(8, 1);
            if (nX[id] + shW[nS[id]] - 1 < x0) continue;
            if (nY[id] > y1 || nY[id] + shH[nS[id]] - 1 < y0) continue;
            if (U[u].stamp != stampNow) {
                U[u].stamp = stampNow;
                need[u] = 0;
                remList[nRem++] = u;
            }
            need[u]++;
        }
        OPS(8, 2);
    }
    /* save every touched user, then take out its RBs inside the rectangle */
    for (i = 0; i < nRem; i++) {
        int u = remList[i], id, t, lo = Xc, hi = -1;
        svOff[i] = nSv;
        svOpt[i] = U[u].uOpt; svShape[i] = U[u].uShape;
        for (id = U[u].first; id >= 0; id = nNext[id]) {
            save_rb(nY[id], nX[id], nS[id]);
            if (nX[id] < lo) lo = nX[id];
            if (nX[id] + shW[nS[id]] - 1 > hi) hi = nX[id] + shW[nS[id]] - 1;
        }
        remove_user(u);
        if (hi - lo + 1 <= spanLim) {       /* compact: placed again from scratch */
            need[u] = 0;
            if (lo < rx0) rx0 = lo;
            if (hi > rx1) rx1 = hi;
        } else if (need[u] < nSv - svOff[i]) {     /* partial: keep the RBs outside */
            for (t = svOff[i]; t < nSv; t++) {
                int s = svS[t];
                if (svX[t] + shW[s] - 1 < x0 || svX[t] > x1 || svY[t] > y1 || svY[t] + shH[s] - 1 < y0)
                    add_rb(u, svY[t], svX[t], s);
            }
        } else need[u] = 0;                 /* placed again from scratch */
        push_cand(u);
    }
    svOff[nRem] = nSv;
    /* touched users always; the best unserved ones up to maxCand in all */
    collect_unserved(x0, x1, maxCand - nRem > 4 ? maxCand - nRem : 4);
    qsort(candList, nCand, sizeof(int), cmp_cand);
    OPS(8, 8LL * nCand);
    stIt++; stRem += nRem; stCand += nCand;
    nIns = 0;
    for (i = 0; i < nCand; i++) {
        int u = candList[i];
        int ca = U[u].arr > rx0 ? U[u].arr : rx0;
        int cb = U[u].dl < rx1 ? U[u].dl : rx1;
        if (U[u].stamp == stampNow && need[u] > 0) {
            int s = U[u].uShape, o = U[u].uOpt, k = need[u], r;
            ll got = -1;
            ensure_pos(k);
            if (cb - ca + 1 >= shW[s]) got = trial(s, k, oMask + (size_t)o * W, ca, cb);
            if (got >= 0) {
                for (r = 0; r < k; r++) add_rb(u, trY[r], trX[r], s);
                assign_done(u);
            } else remove_user(u);           /* dropped */
            continue;
        }
        if (cb < ca) continue;
        if (place_user(u, ca, cb)) insList[nIns++] = u;
    }
    if (totalProfit > oldP || (totalProfit == oldP && usedArea <= oldA)) {
        stAcc++;
        if (totalProfit > oldP) stImp++;
        return nRem;
    }
    if (thr > 0 && totalProfit >= oldP - thr && oldP <= snapP) {
        stAcc++;
        return nRem;                        /* worse, accepted */
    }
    needSave = thr > 0 && totalProfit >= oldP - thr;    /* accept after saving */
    /* revert */
    for (i = 0; i < nIns; i++) remove_user(insList[i]);
    for (i = 0; i < nRem; i++) remove_user(remList[i]);
    for (i = 0; i < nRem; i++) {
        int u = remList[i], t;
        for (t = svOff[i]; t < svOff[i + 1]; t++) add_rb(u, svY[t], svX[t], svS[t]);
        U[u].uOpt = svOpt[i]; U[u].uShape = svShape[i];
        assign_done(u);
    }
    if (needSave) {             /* the current solution is the best: keep it */
        save_best();
        return -1 - nRem;       /* caller repeats the step */
    }
    return nRem;
}

#define NLEV 4
#ifndef BAND0
#define BAND0 16
#endif
#ifndef TARGET
#define TARGET 10
#endif
/* best solution snapshot */
static int *bAsg, *bOpt, *bShape, *bOff, *bY, *bX, *bS, bCap;

static void snap_alloc(void) {
    bAsg = malloc(sizeof(int) * (N + 1)); bOpt = malloc(sizeof(int) * (N + 1));
    bShape = malloc(sizeof(int) * (N + 1)); bOff = malloc(sizeof(int) * (N + 1));
    if (!bAsg || !bOpt || !bShape || !bOff) exit(1);
}

static void save_best(void) {
    int u, n = 0, id;
    for (u = 0; u < N; u++) {
        bAsg[u] = U[u].asg; bOpt[u] = U[u].uOpt; bShape[u] = U[u].uShape;
        bOff[u] = n;
        for (id = U[u].first; id >= 0; id = nNext[id]) {
            if (n == bCap) {
                bCap = bCap ? 2 * bCap : 4096;
                bY = realloc(bY, sizeof(int) * bCap);
                bX = realloc(bX, sizeof(int) * bCap);
                bS = realloc(bS, sizeof(int) * bCap);
                if (!bY || !bX || !bS) exit(1);
            }
            bY[n] = nY[id]; bX[n] = nX[id]; bS[n] = nS[id]; n++;
        }
    }
    bOff[N] = n;
    snapP = totalProfit;
    OPS(8, 4LL * (N + n));
}

static void restore_best(void) {
    int u, t;
    for (u = 0; u < N; u++) if (U[u].first >= 0) remove_user(u);
    for (u = 0; u < N; u++) {
        if (!bAsg[u]) continue;
        for (t = bOff[u]; t < bOff[u + 1]; t++) add_rb(u, bY[t], bX[t], bS[t]);
        U[u].uOpt = bOpt[u]; U[u].uShape = bShape[u];
        assign_done(u);
    }
}

#ifndef THR_MUL
#define THR_MUL 0.5
#endif
#ifndef THR_SWEEPS
#define THR_SWEEPS 10
#endif
static const double alphas[5] = { 1.0, 0.85, 1.15, 0.7, 1.3 };

static void local_search(void) {
    int target = TARGET, pass, nLev = 0, l, tw[NLEV], hb[NLEV], u, nAsg = 0;
    ll start = ops, span = WORK_LIMIT - ops, thr0;
    if (Xc <= 0 || span <= 0) return;
    build_classes();
    build_trees();
    remList = malloc(sizeof(int) * (N + 1));
    insList = malloc(sizeof(int) * (N + 1));
    svOff = malloc(sizeof(int) * (N + 2));
    svOpt = malloc(sizeof(int) * (N + 1));
    svShape = malloc(sizeof(int) * (N + 1));
    need = malloc(sizeof(int) * (N + 1));
    if (!remList || !insList || !svOff || !svOpt || !svShape || !need) exit(1);
    for (u = 0; u < N; u++) nAsg += U[u].asg;
    thr0 = (ll)(THR_MUL * (double)totalProfit / (nAsg ? nAsg : 1));
    for (l = 0; l < NLEV; l++) {        /* row bands of 16, 32, ... rows, up to Y */
        int h = BAND0 << l;
        if (l > 0 && hb[l - 1] >= Y) break;
        hb[l] = h < Y ? h : Y; tw[l] = 4 * minW;
        if (tw[l] > Xc) tw[l] = Xc;
        nLev++;
    }
    for (pass = 0; ops < WORK_LIMIT; pass++) {
        int lv = pass % nLev, h = hb[lv], left = 0;
        for (u = 0; u < N; u++) if (U[u].no && !U[u].asg) left++;
        OPS(8, N);
        if (!left) break;                   /* everybody is served */
        if (pass == nLev) {     /* threshold accepting only with many sweeps ahead */
            double sweeps = (double)span / (ops - start + 1) * nLev;
            thr0 = sweeps >= THR_SWEEPS ? thr0 : 0;
        }
        int yoff = ((pass / nLev) & 1) ? h / 2 : 0;
        int y0, x0;
        curAlpha = alphas[(pass / nLev) % 5];
        for (y0 = (yoff ? -yoff : 0); y0 < Y && ops < WORK_LIMIT; y0 += h) {
            int ya = y0 < 0 ? 0 : y0, yb = y0 + h - 1 < Y ? y0 + h - 1 : Y - 1;
            for (x0 = 0; x0 < Xc && ops < WORK_LIMIT; ) {
                int x1 = x0 + tw[lv] - 1, r;
                double left = 1.0 - (double)(ops - start) / span;
                ll thr = pass < nLev ? 0 : (ll)(thr0 * (left - 0.2) / 0.8);
                if (x1 >= Xc) x1 = Xc - 1;
                r = ruin_recreate(x0, x1, ya, yb, 3 * target + 10, thr);
                if (r < 0) r = ruin_recreate(x0, x1, ya, yb, 3 * target + 10, thr);
                if (r < 0) r = -1 - r;
                if (r > 2 * target && tw[lv] > 1) tw[lv] = tw[lv] * 3 / 4;
                else if (r < target / 2 && tw[lv] < Xc) tw[lv] = tw[lv] * 5 / 4 + 1;
                if (tw[lv] < 1) tw[lv] = 1;
                if (tw[lv] > Xc) tw[lv] = Xc;
                x0 += (tw[lv] + 1) / 2;
            }
        }
    }
    if (snapP > totalProfit) restore_best();
}

/* ------------------------------------------------------------------ */
/* Output                                                             */
/* ------------------------------------------------------------------ */
static void write_output(void) {
    int i, cnt = 0;
    for (i = 0; i < N; i++) if (U[i].asg) cnt++;
    printf("%lld %d\n", totalProfit, cnt);
    for (i = 0; i < N; i++) {
        int id;
        if (!U[i].asg) continue;
        printf("%lld %d", U[i].id, U[i].nrb);
        for (id = U[i].first; id >= 0; id = nNext[id])
            printf(" %d %d %d %d", shH[nS[id]], shW[nS[id]], nY[id], unmap_col(nX[id]));
        printf("\n");
    }
}

int main(void) {
    int c;
    set_weights(wCons);
    read_input();
    compress_time();
    CALIB_MARK("read");
    occ = calloc((size_t)(Xc > 0 ? Xc : 1) * W, sizeof(u64));
    cHead = malloc(sizeof(int) * (Xc + 1));
    tA = malloc(sizeof(u64) * W); tP = malloc(sizeof(u64) * W);
    tT = malloc(sizeof(u64) * W); tQ = malloc(sizeof(u64) * W);
    tO = malloc(sizeof(u64) * W); tN = malloc(sizeof(u64) * W);
    if (!occ || !cHead || !tA || !tP || !tT || !tQ) exit(1);
    for (c = 0; c <= Xc; c++) cHead[c] = -1;
    spot_init();
    fen_init();
    {   /* working set in bytes -> memory factor of the weights */
        double mem = (double)Xc * (W * 8 + 16) + (double)N * 112 + (double)nOpt * (8 * W + 8);
        memG = mem > 8e6 ? my_log(mem / 8e6) / 0.69314718055994531 : 0;
    }
    set_weights(wCons);
    construct();
    CALIB_MARK("cons");
#ifdef DEBUG
    fprintf(stderr, "construct %lld util %.3f ops %lld\n", totalProfit, (double)usedArea / ((double)Y * Xc), ops);
#endif
    set_weights(wLs);
    local_search();
#ifdef DEBUG
    fprintf(stderr, "it %lld acc %lld imp %lld rem %.1f cand %.1f ", stIt, stAcc, stImp, (double)stRem / (stIt + 1), (double)stCand / (stIt + 1));
    fprintf(stderr, "final %lld util %.3f ops %lld\n", totalProfit, (double)usedArea / ((double)Y * Xc), ops);
#endif
    CALIB_MARK("ls");
    write_output();
    CALIB_MARK("out");
#ifdef CALIB
    { int k; fprintf(stderr, "CNT"); for (k = 0; k < 15; k++) fprintf(stderr, " %lld", cnt[k]); fprintf(stderr, "\n"); }
#endif
    return 0;
}

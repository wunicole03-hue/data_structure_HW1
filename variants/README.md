# Variants for judge testing

Each file is HW1.c (commit 35961f1, judge total 2,352,756) with exactly one change.
All pass the checker on own tests; run times are close to the base version.

| File | Change | Affects |
|---|---|---|
| A_look8.c | first-construction lookahead 4 -> 8 (local search stays 4) | construction |
| B_look6.c | first-construction lookahead 4 -> 6 | construction |
| C_look2.c | first-construction lookahead 4 -> 2 | construction |
| D_longload1.c | long-lookahead core from demand >= 1x grid (was 2x) | construction |
| E_longmin8.c | long-lookahead floor 16 -> 8 | construction |
| F_maxrb1024.c | normal passes handle requests of up to 1024 RBs (was 64) | construction + search |
| G_longlook256.c | long-lookahead core starts at 256 (was 128) | construction |
| H_mixed.c | two shapes in turn (time-disjoint) when one shape is one RB short | construction + search |

Judge totals (round 1): A 2,349,388 · B 2,351,848 · C 2,354,790 · D 2,346,294 ·
E 2,352,756 · F 1,789,122 · G 2,352,756 · H 2,357,582 (best).

## Round 2 (all built on H_mixed.c)

| File | Change on top of H |
|---|---|
| I_mixed_look2.c | + first-construction lookahead 2 (C) |
| J_mixed_wide.c | mixing when the best shape holds at least half of the RBs; split points up to 3 RBs earlier |
| K_mixed_lean.c | mixing also in the cheap (over-budget) construction mode |
| L_mixed_look3.c | + first-construction lookahead 3 |
| M_mixed_look1.c | + first-construction lookahead 1 |
| N_mixed_look2_wide_lean.c | I + J + K together |

Judge totals (round 2): I 2,359,084 (best) · J 2,349,412 · K 2,356,962 · L 2,358,493 ·
M 2,355,083 · N 2,352,428.  Lookahead 2 is best (3 close, 1 worse); wider mixing hurts;
mixing in the cheap mode slightly hurts.

## Round 3 (all built on I_mixed_look2.c)

| File | Change on top of I |
|---|---|
| O_lnslook2.c | local-search lookahead 4 -> 2 |
| P_lnslook8.c | local-search lookahead 4 -> 8 |
| Q_lean_early.c | cheap mode after one over-budget checkpoint (was two) |
| R_lean_late.c | cheap mode after three over-budget checkpoints |
| T_ops52.c | OPS_LIMITV 50e9 -> 52e9 (about +0.5 s on the slowest test) |

Judge totals (round 3): O 2,359,084 · P 2,359,084 · Q 2,360,158 · R 2,357,611 ·
T 2,363,342 (max time under 13.6 s).  The local-search lookahead changes nothing
(the judge's score comes from the construction); switching to the cheap mode
earlier helps, later hurts; more budget helps.

## Round 4 (built on I)

| File | Change |
|---|---|
| U_lean1_ops52.c | Q + T: cheap mode after one over-budget checkpoint, OPS_LIMITV 52e9 |
| V_noback.c | U + never leaves the cheap mode once in it |
| W_need100.c | U + the first budget projection without the 0.85 discount (switches earlier) |
| X_leanmul4.c | U + cheap-mode work charged 1x (was 1.25x): more requests reached, more time |
| Y_ops54.c | U + OPS_LIMITV 54e9 (more time) |

## Pacing (built on the tidied T_ops52.c)

| File | Change |
|---|---|
| P_pace.c | budget projection of the first construction counts successful placements (they carry the cost and stop once the grid is full) instead of a flat rate per user |

Own budget-bound runs (no long lookahead, no local search): +4% to +10% where the
budget is short, unchanged elsewhere; a few extreme cases -0.2% to -0.7%.

## Option limits (built on the tidied T_ops52.c)

| File | Change |
|---|---|
| R_ratio48.c | users needing more than 64 RBs keep up to 6 options (was 2: fewest RBs and most rows); when the demand exceeds the grid, an option needing more than 1.5x the RBs of the user's cheapest one is not used; OPS_LIMITV 48e9 (real time per counted unit is up to ~9% higher) |
| R_ratio50.c | the same with OPS_LIMITV 50e9 (riskier on time) |

Own tests: oversubscribed large inputs +4% to +16%, inputs with many big users +8% to +30%,
budget-bound runs never worse; small inputs mean +0.7% to +1.0% (a few -1% to -6%).

## Faster setup (built on R_ratio50.c)

| File | Change |
|---|---|
| S_fast50.c | rows grouped by bit value without sorting (small values), fewer buffer checks in the parser; same output as R_ratio50.c, setup 2x-4x faster on tall grids |
| S_fast52.c | the same with OPS_LIMITV 52e9 |
| S_fast50_r12.c | S_fast50 with options limited to 1.2x the fewest RBs |
| S_fast50_r20.c | S_fast50 with options limited to 2x the fewest RBs |

## Submission

HW1.c is now T_ops52.c (best judge total so far, 2,363,342; max time under 13.6 s).
It follows the rules: builds with the default options alone (`gcc HW1.c`, no warnings
with -Wall -Wextra -pedantic, no -lm needed), has no #pragma, no compiler-specific code,
no #ifdef / #ifndef knobs, no random numbers, no clock or time calls and no hand-written
generator: every choice comes from the input and a fixed operation counter.

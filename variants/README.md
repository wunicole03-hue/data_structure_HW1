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

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

# Knowledge-debt readouts

## Coordination share per day

| day | docs LoC | lean LoC | docs:lean | doc-commits | feat+fix |
|---|---|---|---|---|---|
| 2026-06-20 | 4,943 | 3,361 | 1.47 | 54 | 17 |
| 2026-06-21 | 13,469 | 9,486 | 1.42 | 36 | 70 |
| 2026-06-22 | 8,970 | 5,901 | 1.52 | 50 | 6 |
| 2026-06-23 | 19,538 | 10,796 | 1.81 | 28 | 9 |
| 2026-06-24 | 14,390 | 7,368 | 1.95 | 53 | 33 |
| 2026-06-25 | 19,413 | 11,603 | 1.67 | 75 | 35 |
| 2026-06-26 | 39,179 | 6,123 | 6.40 | 25 | 23 |
| 2026-06-27 | 9,573 | 7,545 | 1.27 | 58 | 17 |
| 2026-06-28 | 9,558 | 20,633 | 0.46 | 235 | 81 |
| 2026-06-29 | 5,147 | 15,806 | 0.33 | 128 | 89 |
| 2026-06-30 | 7,692 | 16,869 | 0.46 | 140 | 34 |
| 2026-07-01 | 781 | 2,021 | 0.39 | 26 | 8 |
| 2026-07-02 | 670 | 8,250 | 0.08 | 28 | 4 |
| 2026-07-03 | 2,382 | 7,276 | 0.33 | 20 | 18 |
| 2026-07-06 | 21,579 | 3,687 | 5.85 | 39 | 22 |
| 2026-07-07 | 21,294 | 7,306 | 2.91 | 77 | 48 |
| 2026-07-08 | 9,884 | 11,583 | 0.85 | 90 | 91 |
| 2026-07-09 | 3,783 | 2,991 | 1.26 | 59 | 22 |
| 2026-07-10 | 36,364 | 3,898 | 9.33 | 63 | 23 |
| 2026-07-11 | 20,097 | 5,054 | 3.98 | 108 | 21 |
| 2026-07-12 | 13,167 | 3,225 | 4.08 | 74 | 8 |
| 2026-07-13 | 13,242 | 4,739 | 2.79 | 83 | 15 |
| 2026-07-14 | 1,394 | 0 | inf | 22 | 0 |

**Cumulative**: docs 296,509 vs lean 175,521 → ratio 1.69

## Time-to-rediscovery (found-already-banked events)

| artifact | banked | rediscovered | debt (h) | note |
|---|---|---|---|---|
| `routeMBoxThresholdFinite_mnp` | 2026-06-30T06:39 | 2026-07-13T14:06 | **319** | mnp base case, 1st rediscovery (endgame parallelization) |
| `routeMBoxThresholdFinite_mnp` | 2026-06-30T06:39 | 2026-07-14T00:58 | **330** | mnp base case, 2nd rediscovery (waist L=0, different lane) |
| `sjGoodChartLoss_endpoint_lt_top` | 2026-07-10T13:44 | 2026-07-11T08:54 | **19** | native inner slice (UPDATE-883, casting detour abandoned) |
| `minAdm_eq_frontPeel` | 2026-07-08T14:05 | 2026-07-11T21:13 | **79** | α-unlock scoped as fresh build, was banked identity (UPDATE-933) |

Debt hours = the artifact sat in the tree, needed and unfound. The duplicated mnp row is
the sharpest datum: the SAME theorem was independently rediscovered twice, ~11h apart,
by different lanes — an index failure repeating after it was already once exposed.


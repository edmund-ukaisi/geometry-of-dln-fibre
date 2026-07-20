# Realization-gap scope — exact scan counts

Raw counts from `battery/realization-battery.py` + `scope-scan.py` / `clearable-characterization.py`
(exact recursion, runmin/FIX-A, original validated sim as ground truth). Reproduce with those scripts.

| scan | instances | P⊊Adm (gap) | P⊆Adm (0 extra) | min P = minAdm | gap ⟺ interior bottleneck |
|---|---|---|---|---|---|
| widths {1,2,3}, L≤4 | 351 | 84 | 351/351 | 351/351 | 351/351 |
| widths {2,3}, L≤4 | 56 | 8 | 56/56 | 56/56 | 56/56 |
| widths {1,2,3,4}, L≤3 | 320 | 56 | 320/320 | 320/320 | 320/320 |
| widths {1,2}, L≤5 | 120 | 22 | 120/120 | 120/120 | 120/120 |

Interpretation:
- **P⊊Adm (gap):** number of width vectors where at least one admissible profile is stranded (⊇ Adm FALSE).
- **P⊆Adm:** the ⊆ half (`leaf_mem_Adm`) holds everywhere — 0 realized profiles outside Adm.
- **min P = minAdm:** the strict need `minAdm ∈ terminalExponents` — holds at EVERY instance (K2 never fires).
- **gap ⟺ interior bottleneck:** the gap-set equals `{M : ∃ 3≤S≤L, min(M¹..M^S) < min(M¹,M²)}` EXACTLY
  (cert-compchain-o4 Part-1 scope). 0 mismatches / 791 across all scans.

Characterization checks (`clearable-characterization.py`, same scans):
- `P(M) == { a∈Adm : Clearable(a) }` EXACT: 0 counterexamples.
- steering rule `R(a)` (1(1) iff target level ℓ > a^S) realizes EXACTLY the clearable profiles: 0 counterexamples.
- every Mval-minimizer is Clearable: 0 counterexamples.

Minimizer-clearability proof check (`env_splice`, non-clearable profiles only):
- envelope-splice ∈ Adm: 356/356.
- envelope-splice Mval strictly smaller: 356/356.
- envelope prefix Mval-contribution == 0: 356/356.

The six pre-committed instances `(2,2,2),(3,3,4),(2,2,2,2),(2,2,3,2),(2,2,3,3,2),(3,2,4,2)` are ALL
bottleneck-free (P == Adm) — which is exactly why the o5-IN gate never fired before this scan. Confound
lesson: pre-committed battery sets MUST include the known failure mechanism (here: an interior
width-drop, `min(M¹..M^S) < min(M¹,M²)` at `3≤S≤L`), e.g. `(3,3,4,2,3)`, `(2,2,1,1)`, `(3,3,2,2)`.

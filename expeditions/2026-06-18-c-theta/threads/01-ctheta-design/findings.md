# ctheta-design — (C,θ) ladder recon

## Numerics (exact integer, sympy) — direct KP-min vs QIP vs explicit
| d | r | direct (C,θ)[#KP] | QIP | explicit (reduction) | paper |
|---|---|---|---|---|---|
| (2,2,2) | 0 | (3,1)[6] | (3,1) | (3,1) | C=3,θ=1 ✓ |
| (2,3,2) | 0 | (4,2)[8] | (4,2) | (4,2) | — |
| (2,2,3) | 0 | (4,2)[6] | (4,2) | (4,2) | Ex6.2 C=4,θ=2 ✓ |
| (3,2,2) | 0 | (4,2)[6] | (4,2) | (4,2) | — |
| (2,4,2) | 0 | (4,1)[9] | (4,1) | (4,1) | — |
| (8,8,11,11,11,13,13,13,15) | 0 | — | (55,4) | (55,4) | Ex6.3 (55,4) ✓ |
| (2,4,2) | 1 | (1,1) | (1,1) | reduction (1,1); LITERAL Thm7.10 (1,**2**) ✗ |

PERMUTATION INVARIANCE numerically confirmed: (2,2,3),(2,3,2),(3,2,2) all give (C,θ)=(4,2)
while #KP and total irred-comp count differ (paper remark: 3 vs 2 vs 3 components).

## QIP substitution (Thm 6.1) — exact
e ↦ m(e):  M = Σ_i e_i(I_{0,i-1}+I_{iN}) + Σ_j f_j I_{jN}, f_j=d'_j−d'_{j-1}.
For weakly-increasing d': m(e) is a valid Kostant partition of d' with m_{0N}=0, AND
codim(m(e)) = G_d(e) = Σ_{1≤j≤i≤N} e_i(e_j+d'_j−d'_{j-1}) EXACTLY (checked all e, 8 dim vectors).
BUT e-image ⊊ all KP (3 of 6 for (2,2,2)). So Thm 6.1 is min-equality + minimizers∈e-image,
NOT a feasible-set bijection. Hard step = converse (minimizers are horizontal-lace, Lemma 6.4/6.7).

## Thm 7.10 literal rank-r — CONDITIONALLY CORRECT
Stress: 400 random (d,r). Reduction route (sort d−r, recompute m, apply r=0 formula) = direct in 400/400.
Literal route (tildeS=S−(m+1)r, m from d') mismatches in 107/400 — EXACTLY when m(d')≠m((d−r)').
⇒ Honest Lean target reduces rank-r to rank-0 on d−r FIRST (Lemma 4.5), then the r=0 closed form.
Codex (decorrelated, xhigh) independently flagged the same conditional-correctness.

## Mathlib coverage
PRESENT: Finset.min'/min'_mem/min'_le; card_filter; Nat.choose; Finset.piAntidiag / finAntidiagonal
(= QIP feasible set {e∈ℕ^N:Σe=d'_0}); Multiset.sort/sort_eq (weakly-incr rearrangement); Int.fract+floor;
MonovaryOn/Rearrangement.
ABSENT (replace w/ direct integer rounding-exchange lemma, NOT a black box): Conway-Sloane closest-vector,
lattice-point enumeration in simplices, affine A_n closest-point.

## Recommended Lean ordering (Codex-concurred)
1. Define KP-Finset(d,r) [m_{0N}=r], codim form, C:=Finset.min', θ:=card filter. (2,2,2)→(3,1) witness.
2. Rank shift C(d,r)=C(d−r,0), same θ (add/remove r copies of M_{0N}; uses M_{0N} proj-inj, Thm 3.7).
3. QIP (sorted, r=0): e-image+codim identity (EASY, have it) → minimizers∈e-image (HARDEST, Lemma 6.4).
4. Explicit closed form via direct rounding/exchange lemmas (own substantial arithmetic tide).
5. θ = Nat.choose m |δ| on sorted d−r.
6. Permutation invariance LAST: no established KP-only route (paper says so). Either corollary of (4)+(5),
   or independent adjacent-swap — flagged as not-established. Avoid Poincaré series.
SINGLE HARDEST STEP: step 3 converse (minimizers = horizontal-lace e-image, Lemma 6.4) — interval
bookkeeping + strict-inequality combinatorics from the proven codim form.

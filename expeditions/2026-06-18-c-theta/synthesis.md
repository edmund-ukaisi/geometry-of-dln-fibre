# synthesis.md — controller's integrative read (c-theta)

## OPEN (2026-06-18)
Compute (C,θ) = (min, #minimisers) of the proven quadratic form Σ m_{i-1,j-1} m_{uv} over Kostant
partitions of d with m_{0N}=r (LR §§5–7). Pure ℕ-combinatorics on ext-codimension's output; no AG. Ladder:
define C,θ (L1) → QIP Thm 6.1 (L2) → explicit formula Thm 7.10 (L3) → permutation invariance Cor 5.10 (L4).
Design recon (01) + Layer-1 formaliser (02) dispatched. Geometric "C = codim Σ^r" rides on hVoigt; the
combinatorial C,θ do not.

## DESIGN RECON VERDICT + LAYER 1 (2026-06-18)

**Numerics (3 routes agree, sympy):** direct KP-min = QIP = explicit (via rank-0 reduction) on (2,2,2)→(3,1),
(2,2,3)→(4,2) [Ex6.2], Ex6.3 (8,8,11,11,11,13,13,13,15)→(55,4). Permutation invariance confirmed:
(2,2,3)/(2,3,2)/(3,2,2) all →(4,2) despite differing #KP / total component counts.

**PRECISION FINDING — Thm 7.10 printed rank-r form is CONDITIONALLY correct.** Fails 107/400 random cases,
exactly when m(d') ≠ m((d−r)') (rank shift changes the truncated simplex prefix). Honest Lean target: reduce
rank-r → rank-0 on d−r FIRST (Lemma 4.5), recompute, apply the r=0 closed form — formalise THROUGH the
reduction, NOT the literal S̃ = S−(m+1)r substitution. Codex concurred independently. (Name what's true.)

**QIP (Thm 6.1):** substitution e↦m(e) gives codim(m(e)) = G_d(e) EXACTLY and a valid m_{0N}=0 KP [easy
half]; but e-image ⊊ all KP. Load-bearing converse = **every minimiser is a horizontal-lace module**
(Lemma 6.4/6.7) — the single hardest step in the ladder.

**Mathlib:** PRESENT — Finset.min'/argmin, piAntidiag/finAntidiagonal (the QIP feasible set {e:Σe=d'_0}),
Multiset.sort, Int.fract/floor, Rearrangement. ABSENT — Conway–Sloane closest-vector ⇒ replace with a
direct integer rounding-exchange lemma (NOT a black box; Codex concurs).

**Target ladder:**
- L1 — define KP-Finset, codimForm, C:=min', θ:=#minimisers. **DONE** (Core.CTheta, reviewed; witness
  (2,2,2)→(3,1)). Tightening the brute-force decide witness (3^9→3^6) before commit.
- L2 — rank-shift C(d,r)=C(d−r,0), same θ (add/remove r copies of M_{0N}; proj-inj, Thm 3.7). Reachable.
- L3 — QIP sorted r=0: e-image+identity [easy] + minimisers∈e-image [HARD, Lemma 6.4 = the wall].
- L4 — explicit closed form via rounding/exchange lemmas (own tide; conceptually easier than L3, long).
- L5 — θ = Nat.choose m |δ| on sorted d−r.
- L6 — permutation invariance LAST: falls out of L4+L5 (no KP-only route; avoid the Poincaré series).

Geometric "C = codim Σ^r" rides on hVoigt (deferred); the combinatorial C,θ do not.

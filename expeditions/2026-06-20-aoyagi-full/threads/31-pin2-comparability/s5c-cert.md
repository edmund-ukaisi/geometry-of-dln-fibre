# S5c — the `Rcore ↔ coreAbsorb` core identification (adjudicated)

The S5 sub-obligation flagged as the genuine open geometry: that the global Schur complement
`Rcore = P11 − P10·⅟P00·P01` (of the telescoped/normalized full product) is comparability-equivalent to
`deepestCoreF (deepestCoreAbsorb … (split w)).2.1 = ‖∏ S_s‖²`, the per-layer cutoff-Schur shear core
(`S_s = T_s − Z_s(1+X_s)⁻¹Y_s`, `schurCorrection`). Adjudicated WITNESS — the identity is exact and
clean. All r=1 algebra exact (sympy + decorrelated Codex xhigh, `codex/s5c-*`, by-hand re-derivation
AGREEING); matrix-r MC-supported and flagged.

## STEP 1 — is it already banked? NO

Searched `DeepestSchurShift`, `DeepestGaugeBlocks`, `DeepestRegAbsorbIFT`, the g156 lane. Present:
`schur_P11_decomp` (`P11 = leak + Rcore` entrywise), `core_comparability_squeeze` (the comparability
GIVEN the split + leak bound), `schurCorrection`/`schurShiftRaw` (the per-layer shear def). **Absent:**
any lemma relating `Rcore` (global) to `deepestCoreF(coreAbsorb)` (per-layer). The g156 docstring
(`DeepestGaugeBlocks.lean:126`) ASSERTS `R − ∏S_s ∈ ideal(reg)` in PROSE — and that prose claim is
**FALSE** (Groebner: `num(R−∏S) mod ideal(A−1,P12,P21) = −Y1·Z0 ≠ 0`). So this needed adjudication;
the true statement is cleaner than the prose.

## THE WITNESS — an exact unit-rescaling identity (r=1, all L)

The rank-1 determinant identity (both Codex and I, independently):
- `A·Rcore = det(C0)·det(C1)·…·det(C_{L-1})` (Schur complement of the product = ∏ layer-dets / the
  global pivot `A = P00` scalar). For `L=2`: `A·Rcore = Δ0·Δ1`, `Δ_s = (1+X_s)T_s − Y_s Z_s = det(C_s)`.
- `∏S_s = (∏ det C_s) / ∏(1+X_s)` (per-layer Schur = layer-det / layer-pivot).

Hence the **EXACT multiplicative relation** (verified `Rglobal − ∏S·u = 0` at L=2 AND L=3, r=1):

    Rcore = u · ∏S_s,    u := ∏_s (1+X_s) / A,    A = ∏_s(1+X_s) + (off-diag terms) → ∏(1+X_s) at 0.

`u` is a **bounded UNIT** (`u → 1` at the deepest point; `Rcore/∏S → 1` along all-ε). So:

    Rcore² = u² · (∏S_s)²,   u² ∈ [m², M²]  on any nbhd where each (1+X_s) and A are units.

This is a **STANDALONE two-sided comparability** `∑Rcore² ≍ ∑(∏S_s)²` — NO `∑E²` charge needed (Codex
Q2/Q4 concur). The reg-variety counterexample (`A−1=P12=P21=0`, `Y1Z0≠0`: `Rcore = −T0T1/(Y0Z1−1)`,
`∏S = T0T1/(Y0Z1−1)²`) shows it is NOT an ideal membership — but it IS the unit rescaling (`u =
1/(Y0Z1−1)` there, bounded away from 0 near the origin where `Y0Z1−1 → −1`).

## THE BUILD-READY STATEMENT + the squeeze wiring (Codex Q3 — the load-bearing ordering)

Feed `core_comparability_squeeze` the **GLOBAL Schur `Rcore`, NOT `∏S`** — then bridge to `deepestCoreF`
by the unit comparability. The exact chain:

    (i)  P22block = leak + Rcore   with leak = P21·⅟P00·P01   [schur_P11_decomp, BANKED, exact split]
    (ii) ∑leak² ≤ t²·∑E²           [the S5b neighborhood Cauchy-Schwarz: ⅟P00 bounded, P01,P10 → 0]
    ⇒ core_comparability_squeeze:  ∑E² + ∑Rcore²  ≍  ∑E² + ∑P22²   [= the LOSS, BANKED]
    (iii) STANDALONE unit comparability:  ∑Rcore² ≍ ∑(∏S_s)² = deepestCoreF(coreAbsorb)   [THE NEW ATOM]
    ⇒  ∑E² + ∑P22²  ≍  ∑E² + deepestCoreF(coreAbsorb)   [the squeeze conjuncts (d,e)]

**Build-ready new atom (the S5c deliverable):**

    theorem schur_core_unit_comparability (H) (r) (hr) (hL) (J) (Pf Qf) (w ∈ U') :
      ∃ m M, 0 < m ∧ 0 < M ∧
        m * deepestCoreF H r (deepestCoreAbsorb H r hr hL (split w)).2.1
          ≤ ∑ i, ∑ j, ((P11 - P10 * ⅟P00 * P01) i j) ^ 2
        ∧ ∑ i, ∑ j, ((P11 - P10 * ⅟P00 * P01) i j) ^ 2
          ≤ M * deepestCoreF H r (deepestCoreAbsorb H r hr hL (split w)).2.1

via `Rcore = u·∏S` (`u` the bounded unit). For the cert's `(d,e)` conjuncts the constants fold into
`γ₁ := M`, `γ₂ := 1/m` (or absorb into the existing `c₁/c₂`).

**WHY feed `Rcore` not `∏S`:** if you split `P22 = leak' + ∏S`, the new `leak' = leak + (Rcore − ∏S)`,
and `Rcore − ∏S = −(Y0Z1/A)·∏S` is NOT `E`-controlled (the reg-variety point has `E=0`, `Rcore−∏S≠0`).
The clean route splits with the GLOBAL `Rcore` (`E`-controllable leak), then transfers to `∏S` by the
UNIT factor — never charging `Rcore−∏S` to `E`.

## SCOPE (honest)

- **r = 1: EXACT, all L.** The determinant identity `Schur(∏C) = ∏det/A`, `∏S = ∏det/∏pivot` is the
  rank-1 mechanism; proven at L=2 and L=3 symbolically. The unit `u = ∏(1+X_s)/A` is the L-fold pivot
  ratio.
- **r ≥ 2 / matrix core (M > 1): MC-supported, FLAGGED.** The scalar `u` becomes a bounded invertible
  SIMILARITY factor (`Rcore = (matrix unit)·∏S·(matrix unit)` modulo the non-commutative Schur algebra).
  MC (`H=[3,3,3]`, r=1, 2×2 core): `∑Rcore²/∑(∏S)² → [0.99, 1.02]` at scale 1e-2 → the standalone
  comparability survives. NOT exact-proven for matrix cores — if the build targets general `(C,θ)` this
  is a separate (probably routine, sub-multiplicativity) lemma. For the L2 headline (the rank-`r`
  reduced-core RLCT) the matrix case IS needed; flag for the formaliser / a follow-on r≥2 cert.

## Files
- `/tmp/s5c_exact.py`, `s5c_tests.py`, `s5c_divergence.py`, `s5c_decisive.py`, `s5c_clean.py`,
  `s5c_generalL.py`, `s5c_generalr.py` (one-off; algebra reproduced here).
- `codex/s5c-{prompt,answer}.md` — decorrelated consult (by-hand re-derivation, agrees).

## Net
S5c is **TRUE standalone** (not an ideal membership — the g156 prose was wrong on the mechanism, right
on the conclusion). The build-ready atom is the unit-comparability `∑Rcore² ≍ deepestCoreF(coreAbsorb)`,
fed AFTER the `schur_P11_decomp` split with the GLOBAL `Rcore`. r=1 exact; matrix-r MC-supported, flagged
as a follow-on. With S5c adjudicated, all of S5 (a–e) is spec'd: S5a (`P00` unit/shrink), S5b (leak
Cauchy-Schwarz), S5c (this unit comparability) → the cert body is fully decomposed.

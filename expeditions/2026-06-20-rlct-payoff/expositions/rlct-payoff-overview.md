# The RLCT payoff and the geometry of `Σ^r` — expedition overview

`status: draft`

This expedition formalises, in honest Lean (zero-cited geometric content), the **destination** of the
Lehalleur–Rimányi programme — *deep linear networks are mildly singular* — together with the geometry of
the rank-`r` product locus on which it rests. Everything below is green, sorry-free, and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

## The objects

For a dimension vector `d = (d_0,…,d_N)` and a rank bound `r`, the **rank-`r` product locus** is
`Σ̄^r = { (A_1,…,A_N) ∈ Rep_d : rank(A_N⋯A_1) ≤ r }` (the closure of the rank-exactly-`r` tuples). For a
target matrix `B`, the **square-Frobenius loss** is `K^DLN_B(A) = ‖A_N⋯A_1 − B‖²_F`; its zero-set is the
fibre `mult⁻¹(B)`.

## What is proved

1. **Orbit stratification (`Core.SigmaStratification`).**
   `Σ̄^r = ⋃_{m} Ō_m`, the union of orbit closures over the Kostant partitions `m` with corner `≤ r`.

2. **Irreducible components (`Core.SigmaComponents`).** The irreducible components of `Σ̄^r` are exactly the
   **maximal** orbit closures `Ō_m`; on `PrimeSpectrum` they are the minimal primes of the intersection ideal.

3. **The component count `θ` (`Core.ThetaComponentCount`, `Core.CCodimZeroStrict`).** The number of
   **top-dimensional** irreducible components of `Σ̄^r` equals the combinatorial minimiser count `numTop`:
   `numTop d r = (topComponents d r).ncard` — **unconditional**. The load-bearing combinatorial input is the
   strict dimension-monotonicity of the codimension form (`cCodim_zero_strict`), proved via an extremal
   shortest-covering reduction (no external citation — an internal fact about the type-A `Ext` form).

4. **The RLCT payoff (`DLNFibre.DLN.RlctPayoff`, `…General`).**
   `rlct(K^DLN_B) = (C_r + r·(d_0 + d_N − r)) / 2` for a target `B` of rank `r`, where `C_r = cCodim d r` is
   the geometric codimension (proved zero-cited, via Voigt's lemma from the prior expedition). At `r = 0`
   (the zero-product locus, the load-bearing case) this is `rlct(K^DLN_0) = C/2`.

## The Cited boundary (name = content)

The geometric content — the stratification, the components, `θ`, and the codimension `C` — is **proved**,
zero-cited. Two established external results are **Cited**, each as a *named, carried interface* (visible in
the type, `via_aoyagi` in the theorem names — never a smuggled axiom):
- **Aoyagi / Watanabe** — the analytic equality `rlct(K^DLN_B) = codim(fibre)/2` (`RlctInterface.cited_aoyagi_dln`).
  The real-log-canonical-threshold *definition* and this analytic bridge are out of scope for a from-scratch
  Lean development (no SLT machinery in Mathlib); they are interfaced, not built.
- **Lemma 4.5 + Lemma 4.6** — the bundle shift `codim(fibre B) = codim(Σ̄^r) + r(d_0+d_N−r)`
  (`BundleShiftInterface.cited_bundle_shift`, guarded `0 < N`). The shift itself is Lemma 4.6 (stated for
  the exact-rank `Σ^r`); the closed-locus form folds in `codim Σ̄^r = codim Σ^r` (Cor 4.4 + Lemma 4.5). Its
  fibre-dimension drop needs general Chevalley fibre-dimension theory, absent in Mathlib; interfaced for the
  general-`r` case (the `r=0` case is bundle-free).

`θ` is the **geometric component count**, not the RLCT multiplicity — the paper records no simple relation
between the two.

## Worked example `(2,2,2)`

`Σ̄^0 = {(A_1,A_2) : A_2 A_1 = 0}` has codimension form values `{3,4,4,5,5,8}` over its 6 corner-0 Kostant
partitions: minimum `C = 3` attained once, so `θ = 1` (one top-dimensional component), and `rlct(K^DLN_0) = 3/2`.
At `r = 1`: `C_1 = 1`, shift `1·(2+2−1) = 3`, fibre codimension `4`, `rlct = 2`. All matched in-Lean.

## Scope and roadmap

- Hypotheses `[IsAlgClosed k] [CharZero k]` (the over-ℂ setting); the loss is over ℝ, bridged to the complex
  geometry by the Aoyagi interface.
- Roadmap (genuinely separate, not gaps in the above): a from-scratch RLCT *definition* + the general
  fibre-dimension theory would let the two Cited interfaces be discharged in-engine; both are sizeable
  analytic/AG sub-libraries Mathlib currently lacks.

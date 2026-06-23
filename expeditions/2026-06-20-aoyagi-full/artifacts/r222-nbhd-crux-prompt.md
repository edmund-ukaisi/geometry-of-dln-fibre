# Consultation: the nbhd-quantifier crux for the (2,2,2) RLCT cover (Lean 4 / Mathlib)

## Context

I'm formalizing the RLCT (real log-canonical threshold) of a deep-linear-network loss
`F = ‖A·B‖²` at the origin, via a resolution-of-singularities chart cover. The RLCT is defined
(Aoyagi Def 1, integral-supremum form) as:

```
rlctAtOn F w0 = sSup { c : ℝ≥0∞ | ∃ c' : NNReal, c = c' ∧
                  ∃ Ω : Set M, IsOpen Ω ∧ {w0} ⊆ Ω ∧
                    IntegrableOn (fun w => |F w|^(-c') * 1) Ω volume }
```

i.e. the sup of exponents `c'` such that `|F|^{-c'}` is integrable on SOME open neighbourhood of `w0`.

## What I have (the g5 chart cover)

A measure cover lemma `g5_pivotNode` that, for ANY open set `U` covered (up to a null set) by a
finite family of "argmax cells" `argmaxCellOn active p` (a max-region tiling of `Fin N → ℝ`, overlaps
are null hyperplanes), rewrites a lintegral over `U` as a finite sum over chart leaves:

```
∫⁻_U g dvol = Σ_{p ∈ active} ∫⁻_{chartDomOn p \ pivotZeroOn p}  ofReal|det φ_p'| · g(φ_p)  dvol
```

where `φ_p = pivotBlowupOn active p` is a pivot blow-up `(x) ↦ (x_p, x_p·x_j for j≠p)`,
det `(x_p)^{card-1}`. Composing 3 of these (one per matrix-product "level") plus a polynomial
change-of-vars (Lemma-2, a measure-preserving homeomorph, det ±1) gives a 24-leaf resolution: each
leaf has integrand `monomialIntegrand d k h c · |unit|^{-c}` on a localized leaf box, where `unit`
is a smooth nonvanishing factor and `monomialIntegrand = (∏|u_j|^{h_j})·(∏|u_j|^{2k_j})^{-c}`.

I've PROVEN the per-leaf threshold-invariance bridge:
`integrableOn_monomial_mul_unit_iff` — on a set where `|unit| ∈ [a,b]` with `0<a`, the leaf integrand
is integrable iff the bare `monomialIntegrand` is (the bounded `|unit|^{±c}` factor doesn't move the
threshold). And each leaf's `monomialThreshold d k h` is known (= 3/2 for all 24, fm's #68).

## The two halves I built (S1Cover.lean)

```
rlctAtOn_ge_of_integral_lt  -- ≥: if ∫⁻_U |F|^{-c'} < ⊤ for all c'<t, on a FIXED open U∋0, then t ≤ rlctAtOn F 0
rlctAtOn_le_of_adm_le       -- ≤ reduction: rlctAtOn F 0 ≤ t IF every admissible c' (integrable on SOME Ω∋0) has c'≤t
```

## The crux question

The `≥` direction is clean: having ONE witness nbhd `U` (the full chart domain) lower-bounds the
`sSup`. **No gap.**

The `≤` direction has the nbhd quantifier: I must show that for EVERY open `Ω ∋ 0` and every `c' > t`,
`|F|^{-c'}` is NON-integrable on `Ω`. The cover gives me divergence of a leaf integral over a FIXED
`U`; I need to localize: the divergence must persist on every nbhd `Ω`, however small.

**Q1.** What is the cleanest argument that the leaf divergence "localizes at the origin"? My current
thinking: the divergent leaf's monomial singularity is AT a coordinate hyperplane through the origin,
so for any open `Ω ∋ 0`, `Ω` contains a small box around 0, on which the chart-image of the divergent
leaf still has positive measure arbitrarily close to the singular locus — so `∫⁻_Ω` over that leaf's
contribution is still `⊤`. Is the right Lean formulation: apply `g5_pivotNode` to `Ω` itself (any
open set is covered up to null by the argmax cells), get `∫⁻_Ω = Σ_leaves`, and show the divergent
leaf's contribution over `Ω`'s preimage is still `⊤` because `Ω`'s preimage under the chart still
contains a neighbourhood of the singular hyperplane segment through 0?

**Q2.** A possible SIMPLER route: define `t := ⨅ leaf-threshold` and prove the cover-form equality
`rlctAtOn F 0 = ⨅_i monomialThreshold (d i)(k i)(h i)` by sandwiching, but route BOTH directions
through the SAME fixed `U` (the full chart domain that IS a nbhd of 0) and an EXISTING transport
lemma. Specifically: is `rlctAtOn F 0` already equal to `rlctAtOn (F restricted-to / transported-to
the chart domain)` via the homeomorph transport `rlctAtOn_comp_homeomorph` — so the nbhd quantifier
on the SOURCE side is matched by the nbhd quantifier on the TARGET side, and I never have to localize
divergence by hand? In other words: does composing with the resolution map (which is a homeomorph
onto the chart domain, a nbhd of 0) AUTOMATICALLY handle the nbhd quantifier, the way it did for the
(2,1,2) seam? Or does the resolution map being a blow-up (NOT a global homeomorph — it collapses the
exceptional divisor) break that, forcing the hand localization of Q1?

**Q3.** Standard RLCT theory (Watanabe, Lin): after resolution, `λ = min_charts (h_j+1)/(2k_j)` and
this is a LOCAL invariant at the point — the proof that the min over charts equals the RLCT is
usually stated as "the integral `∫_{nbhd} |F|^{-c}` converges iff `c < min_j (h_j+1)/(2k_j)`", with
the nbhd-independence folded into the normal-crossing local form. Is there a clean way to state the
`≤` direction that mirrors this — i.e. a single lemma "for a normal-crossing monomial `∏|u_j|^{k_j}`
on a box `[0,ε]^d`, `∫|monomial|^{-c}` diverges for `c ≥ threshold` INDEPENDENT of `ε`" — that I can
prove once and apply per-leaf, so the per-leaf divergence is manifestly `ε`-independent (hence
nbhd-independent)?

Please assess: (a) is the nbhd crux NEW work or does an existing homeomorph-transport discharge it
(Q2)? (b) the cleanest sound `≤`-direction argument (Q1 vs Q3). Flag any soundness hole in routing
both directions through a fixed `U`. Be concrete about Mathlib lemma names where you can.

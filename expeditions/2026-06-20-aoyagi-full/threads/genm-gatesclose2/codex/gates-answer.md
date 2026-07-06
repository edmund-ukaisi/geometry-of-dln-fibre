1. **GATE 1 VERDICT** — `TRUE-only-with-extra-hyp`.

Proved: your `q ≡ 0` counterexample is correct. Then `f(s,z)=∑ s_i^2`, so `rlctAtOn f (0,t0)=m/2`, while `R(z)≡0`, so the a.e.-nonzero conclusion fails.

Exact missing hypothesis: `rlctAt v > m/2` (equivalently by (iii), `rlctAtOn f (0,t0) > m/2`). With that added, one new lemma suffices: `slice_zero_set_caps_rlct_half` = “if `R` vanishes on a positive-measure set in every nbhd of `t0`, then `rlctAtOn f (0,t0) ≤ m/2`.” Difficulty: `moderate`.

Inference: nondegenerate reduced core `H-r` does **not** by itself repair Gate 1; it helps only if you already have an independent lower bound forcing `rlctAt v > m/2`.

2. **THE CAPPING LEMMA**

Proved: your capping claim is true, and in fact only `C^1` in the `s`-variables is needed.

Proof sketch: shrink to a product neighborhood `B_s(ρ) × U_z`. Continuity of `D_s q` gives a uniform `L` with
`|q(s,z)-q(0,z)| ≤ L|s|`.
On any positive-measure `E ⊂ U_z` with `q(0,z)=0`, we get `|q(s,z)| ≤ L|s|`, hence
`f(s,z)=|s|^2+|q(s,z)|^2 ≤ (1+L^2)|s|^2`
on `B_s(ρ) × E`. Therefore for every `c ≥ m/2`,
`∫_{B_s×E} f^{-c} ≥ (1+L^2)^{-c} μ(E) ∫_{B_s} |s|^{-2c} ds = ∞`.
Since such `E` exists in every nbhd of `t0`, every sufficiently small nbhd of `(0,t0)` has divergent integral, so `rlctAtOn f (0,t0) ≤ m/2`.

Formalization difficulty: `moderate`.

3. **GATE 2 VERDICT** — `FALSE-as-stated`.

Proved: part (b) cannot come from the current `∀ C² q` hypotheses, nor from the R1 polynomial resolution alone. Abstract counterexample to the second-peel implication: take
`R(x,u)=x^2+u^4 = x^2 + (u^2)^2`.
Peeling the `x`-square gives built residual `q₂(x,u)=u^2`, so the slice is `R₂(u)=u^4` and
`rlctAtOn R₂ = 1/4`,
which has no reason to equal the fixed DLN value `lambdaCore(M')`. So the abstract `C²` interface is too weak.

Proved: part (a) also needs a strict-half cap; at threshold `e/2`, the pure quadratic case gives `q₂ ≡ 0`, so a.e.-nonzero fails.

Exact missing hypothesis: a local model-identification of the built degraded slice, e.g.
`R₂ = u · (dlnLoss M' 0) ∘ φ`
near `t0₂`, with `u` bounded away from `0` and `φ` a local `C^1` diffeomorphism. Then:
- (b) follows from R1 plus bounded-unit/diffeo RLCT invariance.
- (a) follows from transport of the polynomial zero-set-nullity (or, alternatively, from the capping lemma once a strict `> e/2` lower bound is known).

Difficulty: `hard-new-analysis` if this identification must be proved from the present abstraction; only `bounded-bookkeeping` once that identification is assumed.

4. **BOTTOM LINE**

Proved: this is **not** a mechanical plug. Gate 1 needs a real new analytic cap lemma; Gate 2 needs a stronger structural interface than “arbitrary `C²` residual with matching RLCT”.

Next lemmas to build:
1. `slice_zero_set_caps_rlct_half`
2. `slice_ae_nonzero_of_rlct_gt_half`
3. `degraded_slice_is_core_up_to_bounded_unit_local_diffeo`
4. `degraded_slice_rlct_eq_lambdaCore`
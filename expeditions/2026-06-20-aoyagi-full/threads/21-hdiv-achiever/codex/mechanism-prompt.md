<task>
You are red-teaming a Lean 4 + Mathlib formalisation TACTIC decision. I withhold my own
conclusion. I want your independent judgement on ONE question: can the target lemma be
proven HONESTLY from the banked machinery I list, and if not, what is the minimal missing
ingredient. Frame-in and facts-in follow; do not assume facts I have not stated.

## SETTING (RLCT / resolution of singularities for deep linear networks)

We have a flat-coordinate loss `F := routeMCore M : (Fin N → ℝ) → ℝ`, where `N = flatDim M`,
`M : Fin (L+1) → ℕ` is a layer-width vector, and `F x = dlnLoss M 0 ((paramsEquivFlat M).symm x)`
(the square-Frobenius loss of the matrix product, in flat coords, at the deepest/all-zero point).
`F ≥ 0`, continuous, `F(0) = 0`.

`rlctAtOn F 0 = sSup { c' : NNReal | |F|^(-c') integrable on some open Ω ∋ 0 }` (the real
log-canonical threshold at the origin).

`monomialThreshold d k h` is the RLCT threshold of a normal-crossing monomial
`∏ⱼ |uⱼ|^{hⱼ - 2 kⱼ c}` data; `minAdm M : ℕ` is a combinatorial quantity (the codimension).
The value lane PROVES: there is a chart family (combinatorial: each leaf carries only exponent
data `(d,k,h)`, NO geometric map) with `⨅ᵢ monomialThreshold(leaf i) = (minAdm M)/2`, and an
ACHIEVER leaf `i⋆` with `monomialThreshold(i⋆) = (minAdm M)/2` (the minimum), every other leaf ≥.

## TARGET LEMMA (the atom `hdiv_achiever`)

For every `c' : NNReal` with `(minAdm M)/2 ≤ (c' : ℝ≥0∞)` and every `ε > 0`:

    ∫⁻ x in cubeBox N ε, ENNReal.ofReal (|F x| ^ (-(c':ℝ))) = ⊤

i.e. the box integral of the threshold density DIVERGES at-and-above the threshold value, in the
FLAT ambient coordinates, over the cube `[-ε,ε]^N`. (This is the lower-bound `cover_ge_div` leg:
it gives `rlctAtOn F 0 ≤ (minAdm M)/2`.) Divergence is required NON-STRICT (at `c' = (minAdm M)/2`,
the boundary), because the monomial threshold is sharp (the test integral ∫₀^ε u^{-1} du = ⊤).

## BANKED MACHINERY (what is PROVEN and available; treat as given)

1. `monomialIntegrand_lintegral_box_eq_top (d k h) (hk : ∃ j, k j ≠ 0) (c') (hc' : monomialThreshold d k h ≤ ofReal c') (hc'0 : 0 < c') (hε : 0 < ε)` :
   `∫⁻ u in [0,ε]^d, ofReal |monomialIntegrand d k h c' u| = ⊤`.
   This is divergence of the MONOMIAL integrand in the CHART coordinates `u`, sharp at threshold.

2. `rlctAtOn_squeeze (F Φ) (wstar) (... measurable, c₁,c₂>0) (hsq : near wstar, c₁·Φ ≤ F ≤ c₂·Φ)` :
   `rlctAtOn F wstar = rlctAtOn Φ wstar`. (A two-sided pointwise squeeze ⟹ equal POINT RLCTs.
   NO change of variables, NO box integral; it equates the sSup-defined point thresholds.)

3. `rlctAtOn_mono`, `rlctAtOn_germ_local` : monotonicity + germ-locality of the POINT RLCT.

4. `schur_recursion_step_squeeze` : per-node `rlctAtOn flatCore (0) = nReg/2 + rlctAtOn(child) 0`
   (an ADDITIVE recursion on the POINT rlct, via the squeeze + a smooth-block split).

5. `rlctAtOn_le_of_box_diverges (F t) (hdiv : ∀ c', t < c' → ∀ ε>0, ∫_{cubeBox ε}|F|^{-c'} = ⊤) : rlctAtOn F 0 ≤ t`.
   (Box divergence STRICTLY above t ⟹ rlctAtOn ≤ t. NOTE the strict `<`.)

6. The (2,2,2) precedent `routeM222_box_diverges`: it proved EXACTLY this atom shape for the single
   case M=(2,2,2), but via an EXPLICIT geometric blow-up chart `phiUnit : box → flat` with a
   change-of-variables `phiUnit_cov` and an integrand-match `F∘phiUnit = monomial · unit`. It then
   dominated cubeBox by `phiUnit '' P` and pushed `monomialIntegrand_lintegral_box_eq_top` through.
   The (2,2,2) chart factorisation is documented as a "depth-2 miracle" that does NOT generalise:
   for L > 1 the Jacobian tower ceases to be triangular after the first pivot, so `F∘φ` does NOT
   factor as `monomial · unit` for a single global chart.

7. There is NO banked geometric chart `φ_{i⋆} : box → flat` for the achiever leaf at general M
   (the chart family is purely combinatorial exponent-data).

## THE QUESTIONS

Q1. Does `rlctAtOn F 0 ≤ (minAdm M)/2` (the point-RLCT upper bound, obtainable from the additive
    squeeze recursion #4 along the achiever path) IMPLY the target box-divergence atom
    `∫_{cubeBox ε} |F|^{-c'} = ⊤` for `c' ≥ (minAdm M)/2`? Be precise about the boundary (`c' = (minAdm M)/2`,
    non-strict) and about whether `rlctAtOn ≤ t` is equivalent to / weaker than the box `=⊤` at the
    threshold. (I suspect it does NOT, because rlctAtOn ≤ t is an sSup statement constraining only
    c' STRICTLY above t, and the boundary divergence is strictly stronger. Confirm or refute.)

Q2. Given the squeeze (#2,#3,#4) equates POINT RLCTs (not box integrals), and there is no achiever
    geometric chart (#7), is the target atom provable HONESTLY from the banked list, or does it
    REQUIRE constructing a general-M geometric achiever chart `φ_{i⋆}` (analog of `phiUnit`) with a
    change-of-variables and an `F∘φ = monomial·unit` (or `monomial·measurable-bounded-below-unit`)
    integrand match? If a chart is required, is the "depth-2 miracle" obstruction (#6) fatal to a
    SINGLE global chart, or can a SEQUENCE of blow-ups (one per achiever-path node) compose into a
    chart whose pulled-back loss is `monomial · (bounded-away-from-0 unit on the box)` — sufficient
    for divergence (only a LOWER bound on |F∘φ| is needed: |F∘φ| ≥ c·monomial gives
    |F∘φ|^{-c'} ≤ c^{-c'}·monomial^{-c'}... wait, divergence needs |F∘φ|^{-c'} LARGE i.e.
    |F∘φ| SMALL, so we need |F∘φ| ≤ C·monomial, an UPPER bound on the loss along the chart)?

Q3. For DIVERGENCE specifically (the loss must vanish FAST ENOUGH along one path), what is the
    minimal honest ingredient? Options: (a) a one-parameter or low-dim achiever curve/wedge
    γ(t) → 0 with F(γ(t)) ≲ t^{minAdm} and a tubular box around it where Fubini gives the divergent
    1-D test integral; (b) a full general-M achiever chart; (c) something using the squeeze's
    UPPER bound F ≤ c₂·Φ to dominate F by the smooth-block form Φ whose box integral is computable.
    Rank by tractability for a Lean formalisation and name the single load-bearing sub-lemma each needs.

Q4. Is there a SOUNDNESS TRAP where one might "prove" the atom by asserting `=⊤` from
    `rlctAtOn ≤ t` without the genuine boundary divergence (value-correct but germ-degenerate)?
    Describe the trap concretely so I can avoid it.

<output_contract>
Answer Q1–Q4 in order, each ≤ 8 sentences. For Q1 give a definite YES/NO with the precise reason
(boundary/sSup logic). For Q2 give REQUIRES-CHART or PROVABLE-WITHOUT, and if requires-chart, state
whether single-global is fatal and whether a composed blow-up sequence escapes it. For Q3 rank
(a)/(b)/(c) by Lean tractability and name each one's load-bearing sub-lemma. For Q4 one concrete
trap description. End with a 2-line bottom-line: the single most honest, most tractable route.
Flag every claim as DERIVED (from the facts I gave) vs GENERAL-KNOWLEDGE (RLCT/resolution theory).
</output_contract>

<grounding_rules>
Do not assume any geometric chart exists beyond what I stated (#6 is the only one, M=(2,2,2)-specific).
Do not assume Mathlib has a general resolution-of-singularities API. If you invoke a standard RLCT
fact (e.g. "the RLCT is attained / the threshold density diverges at the boundary for a normal-crossing
monomial"), mark it GENERAL-KNOWLEDGE and say whether it transfers to F (a non-monomial loss) WITHOUT
a chart. Distinguish "rlctAtOn ≤ t" (proven point bound) from the box `=⊤` atom rigorously.
</grounding_rules>
</task>

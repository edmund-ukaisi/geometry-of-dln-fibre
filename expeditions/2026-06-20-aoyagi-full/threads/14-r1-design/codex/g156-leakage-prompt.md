<task>
DLN deep-linear-network loss at the deepest point. I need to derive (on paper, for later Lean
transcription) a TWO-SIDED comparability between two notions of "reduced core", agreeing modulo a
"regular-leakage" ideal. This is the #80 cert's part (4).

SETUP. A deep linear network: layers `A_1, …, A_L` (matrices), product `∏A = A_L···A_1`, target `B`,
square-Frobenius loss `‖∏A − B‖²`. Near the deepest critical point `w*` (a rank-`r` point of the
fibre `∏A = B`), after endpoint-frame conjugation + reindexing to `r ⊕ M` block shape, the loss matrix
`N = ∏A − B` (conjugated) has the block form `fromBlocks (P00−1) P01 P10 P11` where `(P00,P01,P10,P11)`
are the blocks of the FRAMED PRODUCT `∏C` (C = the per-layer frame-conjugated layers), and the deepest
value is `blockdiag[I_r, 0]`. `P00` is invertible near `w*` (`P00 → I_r` as `w → w*`).

TWO "cores":
(A) the FULL-PRODUCT SCHUR CORE  `R := P11 − P10 · P00⁻¹ · P01`  (the Schur complement of the WHOLE
    framed product's block form). The loss splits (proven) as `‖E‖² + ‖P11‖²` with
    `E = (P00−1, P01, P10)` the regular residual, and `P11 = leak + R`, `leak = P10·P00⁻¹·P01 ∈
    ideal(P10,P01) ⊆ ideal(E)`. With `‖leak‖² ≤ t²‖E‖²` (t = ‖pivot‖ → 0), the squeeze
    `‖E‖²+‖R‖² ≍ ‖E‖²+‖P11‖²` is PROVEN (the #54 lemma).
(B) the ABSORBED PER-LAYER REDUCED CORE. Each framed layer `C_s` has block form
    `fromBlocks (I+X_s) Y_s Z_s T_s` (gauge blocks X,Y,Z + reduced core T_s). The "core absorption" is a
    det-1 shear: `coreAbsorb` shifts the core slot by `schurCutoffShift = −Z_s(I+X_s)⁻¹Y_s` (the
    per-layer Schur correction, cut off to be global). The absorbed reduced core is
    `(coreAbsorb q).core = q.core + schurCutoffShift`, and `deepestCoreF(absorbed core)` is the loss of
    the REDUCED chain `‖∏ S_s‖²` where `S_s = T_s − Z_s(I+X_s)⁻¹Y_s` is the PER-LAYER Schur complement
    (so the absorbed core is `∏ S_s`, the product of per-layer Schur complements).

THE FACT TO ESTABLISH (g156): `R` (Schur complement of the product) and `∏ S_s` (product of per-layer
Schur complements) are NOT equal in general (Schur-of-product ≠ product-of-Schur), BUT they differ by a
term in `ideal(E)` (the regular residual blocks). Concretely I need a TWO-SIDED comparability of the
SQUARED energies, near `w*`:
    ∃ γ₁ γ₂ > 0, ∃ nbhd U of w*, ∀ w ∈ U:
      ‖R(w)‖² ≤ γ₂ · ‖∏S_s(w)‖²   AND   ‖∏S_s(w)‖² ≤ γ₁ · ‖R(w)‖²
OR (likely the honest form, since both vanish at w* and differ by ideal(E)): the comparability holds
MODULO ‖E‖² — i.e. it's really `‖R‖² ≍ ‖∏S_s‖²` after the #54 squeeze has already charged the
ideal(E) part. State the cleanest precise form.

WHAT I NEED:
1. The precise relation `R − ∏S_s = ?` — express `R` (Schur complement of the L-fold product) in terms
   of the per-layer Schur complements `S_s` and the gauge blocks (X_s, Y_s, Z_s), and show the
   difference lies in `ideal(E)` (linear in the regular residual generators E = (P00−1, P01, P10), with
   bounded coefficients near w*). Do the L=2 case explicitly (two layers), then the general-L induction.
2. The cleanest TRUE statement of the comparability for the cert: is it (a) a direct two-sided
   ‖R‖²↔‖∏S_s‖² bound with γ₁,γ₂; or (b) a statement mod ‖E‖² (‖R−∏S_s‖² ≤ C·‖E‖²·(stuff)); or (c)
   both R and ∏S_s squeeze the SAME thing so the cert's γ₁/γ₂ comparability holds via transitivity
   through ‖E‖²+(common core)². Pick the form that (i) is TRUE, (ii) feeds the cert's
   `‖R‖² ≤ γ₂·deepestCoreF ∧ deepestCoreF ≤ γ₁·‖R‖²` conjuncts.
3. The KEY ESTIMATE making it two-sided near w*: as w→w*, X,Y,Z→0 and the per-layer Schur corrections
   → 0, so S_s → T_s and ∏S_s → ∏T_s; meanwhile R → P11(w*) ... pin down what both tend to and why the
   ratio stays bounded above AND below (the lower bound is the subtle one — why doesn't ∏S_s vanish
   faster than R, or vice versa). Flag any nondegeneracy assumption needed (e.g. germ-nonvanishing of
   the reduced core — is that the hGne/dlnLoss_deepest_core_ne_zero already-available fact?).
</task>

<output_contract>
1. The explicit `R − ∏S_s` relation (L=2 worked, then general-L), with the ideal(E) membership + bounded
   coefficients.
2. The cleanest TRUE cert-feeding statement (pick a/b/c), stated precisely.
3. The two-sided near-w* estimate + the nondegeneracy assumption (name it).
Concise, paper-math (you may use block-matrix algebra). Flag any step that is an ASSUMPTION vs a
derivation. This is for Lean transcription, so keep the algebra explicit and the ideal-membership
constructive (exact cofactors), not just "∈ ideal".
</output_contract>

<grounding_rules>
Pure math derivation; no repo. If a step needs a hypothesis (invertibility, nondegeneracy, t small),
state it explicitly. Be honest if the two-sided bound FAILS without an extra assumption — naming the
missing assumption is more valuable than a hand-wave.
</grounding_rules>

<task>
Lean 4 / Mathlib v4.29 (DLNFibre RLCT). I must build the HEAVIEST lemma of the spine —
`deepest_regular_core_normal_form` (~600-1500 lines per a prior estimate). ROUTE-FIRST (controller
directive): pin the EXACT chart-interface STATEMENT + the named SUB-LEMMA SKELETON before grinding any
lines. Give me the decomposition into ~4-8 named sub-obligations, each with its statement + which green
engine discharges it, so the grind is structured (not a monolith). This is the 2nd-pass design review.

THE TARGET:
  deepest_regular_core_normal_form (H : Fin (L+1)→ℕ) (r) (B) (hB : B.rank = r) (hr : ∀ s, r ≤ H s) (hL : 1≤L) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
      = (nReg:ℝ≥0∞)/2 + rlctAtOn (dlnLoss M 0) (0:Params M)   [M s = H s − r, nReg = r(H0+Hlast−r)]

THE MATH (Aoyagi 2013 Thm 3, the rank-r product reduction): at deepestPoint every layer C_s = w s has
rank EXACTLY r. The gauge-slice change of vars C_s = [[I_r+X_s, Y_s],[Z_s, T_s]] (block sizes r and
M_s=H_s−r) makes: the r "regular" gauge directions a nondegenerate quadratic block (the output residual
blocks P11−Ir, P12, P21 — nReg = r(H0+Hlast−r) of them, each +½ via the smooth-block split); the reduced
(M_s) blocks a smaller chain whose core ‖∏C'_s‖² = dlnLoss M 0. So rlct = nReg/2 + (reduced-core rlct).

GREEN ENGINES (verified signatures):
- rlctAtOn_unit_invariant_aux (F u wstar) (a b)(ha:0<a)(hmeas)(hu:∃U∈𝓝, a≤|u|≤b) : rlctAtOn (u·F) wstar = rlctAtOn F wstar  [the ψ-bump / unit cancel — the NON-MP route]
- rlct_additive_smooth_block {n} (G y0 ...) : rlctAtOn (fun p:(Fin n→ℝ)×Y => (∑ p.1²)+G(p.2)²) (0,y0) = n/2 + rlctAtOn (G²) y0  [the n/2 Fubini split]
- rlct_germ_local / rlctAtOn_germ_local (F=G near w0 ⟹ rlctAtOn F w0 = rlctAtOn G w0)  [germ-locality]
- rlctAtOn_comp_homeomorph (e MP homeo) : rlctAtOn(F∘e) w0 = rlctAtOn F (e w0)  [MP transport — but the gauge slice is NOT MP, so this is for the MP sub-parts only]
- block_elimination (H r B hB) : ∃ P Q units, P·B·Q = diag(E_r,0)  [L1, green]
- paramsEquivFlat (H) : Params H ≃ᵐ (Fin (flatDim H)→ℝ) MP+continuous  [Params↔flat]
- rlctAtOn_eq_rlctAt (on Params)
KEY SUBTLETY (controller-flagged): the gauge-slice chart C_s=[[I_r+X,Y],[Z,T]] → (residual blocks, reduced
C') is NOT measure-preserving (nonlinear triangular solve, unit Jacobian ≠ det±1). So the Jacobian unit
must be peeled by rlctAtOn_unit_invariant_aux (a positive unit on a nbhd), NOT rlctAtOn_comp_homeomorph.

r=0 case: B=0 (Matrix.rank_eq_zero), deepestPoint = all-zero, nReg=0, reduces directly to rlctAtOn(dlnLoss H 0) 0 = the core (M=H). Handle separately/first.
</task>

<output_contract>
  1. The SUB-LEMMA SKELETON: ~4-8 named sub-obligations decomposing deepest_regular_core_normal_form, IN
     DEPENDENCY ORDER. For each: a one-line Lean-ish statement + which green engine discharges it + est
     difficulty (S/M/L). The decomposition should isolate: (i) the r=0 base; (ii) the deepest-point layer
     structure (rank-r ⟹ the gauge-slice coords exist); (iii) the loss-in-gauge-coords form (regular
     quadratic ⊕ reduced core); (iv) the Jacobian-unit peel (rlctAtOn_unit_invariant_aux); (v) the n/2
     split (rlct_additive_smooth_block); (vi) the reduced-core identification (= dlnLoss M 0).
  2. The HARDEST sub-lemma + whether it itself needs further decomposition or a pp-hall exact-algebra
     certificate (the gauge-slice coordinate construction is the likely one).
  3. The EXACT chart-interface STATEMENT for the gauge-slice change of vars (the homeomorphism/embedding
     type + its domain + the unit-Jacobian fact), pinned so the grind has a fixed target.
  4. Is there a smaller-scope route (e.g. prove it for the deepest-point's SPECIFIC structure rather than
     a general gauge slice; or reduce to a 2-factor case + induction on L)? Anything that cuts the 600-1500.
  5. r=0 base: confirm the clean reduction (B=0 ⟹ ... ⟹ core).
  Under ~600 words. Mark inference vs fact; don't invent Mathlib names (flag "verify").
</output_contract>

<grounding_rules>
  Green engines (signatures as given) are FACT. The math (Aoyagi Thm 3 gauge-slice) is the target to
  formalise — flag where the Lean lift is non-obvious vs routine. The non-MP unit-Jacobian routing is
  load-bearing (the prior squeeze lane died by conflating MP with the loss split — keep the Jacobian peel
  explicit). Distinguish "composes from green engines" from "needs a new heavy sub-lemma".
</grounding_rules>

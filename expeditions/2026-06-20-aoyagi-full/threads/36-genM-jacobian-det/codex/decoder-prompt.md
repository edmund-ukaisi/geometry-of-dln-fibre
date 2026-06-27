# Lean 4 / Mathlib — design the cleanest DISJOINT-slot flat decoder + the item-3 map equality strategy

GOAL: prove `phiFlat_abs_det : |det (fderiv φ_flat u)| = ∏_j |u_j|^{leafH j}` for an achiever chart
φ_flat = paramsEquivFlat ∘ chartParamsGen ∘ genBlkFlat. I have BANKED (sorry-free):
- the conditional `phiFlat_abs_det_of_factored`: given (item-3) `composeFold fs = φ_flat` and
  (item-4) the per-factor det product = ∏|u_j|^{leafH j}, concludes the det. The det telescope is closed.
- the three conjugated factors `schurChartFactor`/`lduChartFactor`/`chainChartFactor : ChartFactor N`,
  each = conjBlockFactor E (factor map) (factor fderiv), with abs-det = banked monomial at (E u).1, for
  ANY CLE E : (Fin N → ℝ) ≃L[ℝ] Block × Rest.

THE DIAGNOSED FLAW: the current `genBlkFlat` decoder is a modular hash that collapses distinct block
entries to the same flat coord (so no block-extraction CLE matches it). I must redefine it with DISJOINT
slots, then prove `composeFold fs = φ_flat`.

KEY STRUCTURES (Mathlib v4.29, all dependent over opaque widths):
- `Wext M k = M k` (k≤L), `Text M t 0 = M 0`, `Text M t (k+1) = t k`. `N := routeMAmbient M = flatDim M
  = ∑_{s:Fin L} M_{s.castSucc}·M_{s.succ}`.
- `GenBlk M t` fields per k: `Bmat k : Matrix (Fin (Text k)) (Fin (Text (k+1)))`,
  `Nblk k : Matrix (Fin (Text (k+1))) (Fin (Wext k − Text (k+1)))`,
  `Wblk k : Matrix (Fin (Wext k − Text (k+1))) (Fin (Wext (k+1)))`,
  `Rmat k, Rfin k : Matrix (Fin (Text k)) (Fin (Wext k))`. (k=0 boundary: Bmat 0 = I, Rmat 0 = 0.)
- `chartParamsGen u M t B hle : Params M`, layer s = reindex (chainOfMt.A s.val), where
  A k = chainA(N_k)(W_k)(C(k+1)), C k = Bmat k · chainQ(N_k) + u • Rmat k (interior), C L = u • Rfin L.
- `chartParamsFlat = chartParamsGen (x ⟨0,_⟩) M t (genBlkFlat … x) hle` (the radial u IS x at pivot 0).
- `phiFlat x = paramsEquivFlat M (chartParamsFlat … x)`.
- The RATE `routeMCore_phiGen` consumes ONLY GenBlk/hle/hC0 (hC0 = identity-boundary C 0 · suffix =
  suffix). It is decoder-AGNOSTIC. So a redefined disjoint decoder keeps the rate IF hC0 still holds.
- `chartIdxEquiv M t … : Fin N ≃ ChartIdx M t`, ChartIdx = Σ k:Fin L, Fin(schurDim k) ⊕ Fin(liftDim k),
  schurDim k = t_k·M_{k+1}, liftDim k = (M_{k+1}−t_{k+1})·M_{k+2}.

THE TENSION I want adjudicated. The factored chart `composeFold fs` is a product of full-ambient flat
factors (radial, Schur_s, LDU_s, chain_s) conjugated by CLEs E_s. To match φ_flat ENTRY-WISE I must
reshape `composeFold fs` to `paramsEquivFlat ∘ chartParamsGen ∘ genBlkFlat`. That pipeline goes:
flat coords → genBlkFlat blocks → chainA/chainQ layers → Params → paramsEquivFlat flatten. Matching the
WHOLE pipeline is the multi-pass worry.

QUESTIONS (be concrete + skeptical):
1. What is the CLEANEST disjoint decoder? Option (a): an injective ℕ-valued slot offset per (k, role,
   i, j) with a proof of injectivity into Fin N (heavy: need ∑ of role sizes = N, a prefix-offset). 
   Option (b): decode directly from `chartIdxEquiv`-indexed coords: genBlkFlat reads block (k,role)
   entry (i,j) as `x (chartIdxEquiv.symm ⟨k, Sum.inl/inr (the (i,j)-th slot)⟩)`. Which makes item-3
   provable with least cast pain? Note ChartIdx only has schurDim/liftDim slots — but GenBlk has 5 roles
   (Bmat,Nblk,Wblk,Rmat,Rfin) with DIFFERENT widths; do these even fit ∑(schurDim+liftDim) = N? My
   worry: the role widths (Text k · Text(k+1) for Bmat, etc.) do NOT obviously sum to N the way
   schurDim+liftDim do. Is the GenBlk role-decomposition even dimension-consistent with N, or does the
   chart genuinely use FEWER than N independent block params (with the rest being the u-radial / spectator
   slots)? THIS is my core uncertainty — please check the dimension accounting.
2. Is matching the WHOLE pipeline (composeFold = paramsEquivFlat ∘ chartParamsGen ∘ genBlkFlat) the right
   target, or should I instead DEFINE composeFold's factors so the composition telescopes definitionally
   (e.g. make each E_s the paramsEquivFlat-layer-s reshape, so composeFold = paramsEquivFlat ∘ (chainA
   layer assembly) by construction)? I.e. is item-3 better as "build φ_flat AS composeFold" rather than
   "prove a pre-existing φ_flat equals composeFold"?
3. Given the dimension worry in Q1: is the HONEST move to NOT decode all of GenBlk from disjoint flat
   slots, but only the genuinely-free params (Schur K, LDU q, the residuals), with the chain/radial
   structure fixed — i.e. the chart is NOT a bijection onto all of Fin N but onto a sector? But the cov
   needs |det Dφ| which needs a SQUARE Jacobian (N×N)... so the chart MUST be N→N. Reconcile: does the
   achiever chart use exactly N free coords (so the GenBlk roles DO sum to N after accounting for the
   identity boundary k=0 collapsing Bmat 0 and Rmat 0)?

Give me a concrete recommended decoder + the item-3 target formulation + flag the dimension accounting.
The det side is done; I need the map equality to be provable, ideally by construction.

<task>
Lean 4 / Mathlib formalisation of a deep-linear-network RLCT result. I need a design review of the
crux construction `psiSplitRawGen` and its "move identity", to de-risk a large (~2000-line) build and
to check for a definitional mismatch BEFORE I write it. This is pure matrix/algebra design; no measure
theory here.

SETUP (all already BANKED, sorry-free):
- Abstract chain over ℕ-indexed block types: layer s is `C s : Matrix (r ⊕ m s) (r ⊕ m (s+1)) α`
  (α a CommRing). `partProd C k = C 0 * ... * C (k-1)` (a `r ⊕ ·`-blocked matrix). Blocks:
  A_s=(C s)₁₁ (pivot), Y_s=(C s)₁₂ (up), Z_s=(C s)₂₁ (down), T_s=(C s)₂₂ (core).
- `blockSchur (C s) = T_s − Z_s A_s⁻¹ Y_s`. `Kcoup C s = Z_s·(partProd..)⁻¹·Y_s`-style coupling.
- The abstract JOINT MOVE `movedC C Z0edit s = fromBlocks A_s Y'_s Z'_s T'_s` where:
    * pivots fixed: Â_s = A_s;
    * EVERY up-block edited: Y'_s = Y_s + ΔY_s, ΔY_s = N_s⁻¹ u_s (S_s − S̃_s),
      u_s = B_s⁻¹ R_s (B_s=(partProd C s)₁₁, R_s=(partProd C s)₁₂), N_s = 1 + u_s V_s (V_s=Z_s A_s⁻¹),
      S_s = blockSchur(C s), S̃_s = (1 − Kcoup C s)·S_s;
    * ONE down-block edited at layer 0: Z'_0 = Z0edit (concrete value `Z0edit0 C L = Z_0 + ΔV_0·A_0`,
      ΔV_0 = ∑_{j<L}(blockSchur(partProd C j) − Ŵ_j)·V_j·N_j⁻¹·B_j⁻¹); Z'_s = Z_s for s≥1;
    * cores reconstructed: T'_s = S̃_s + Z'_s A_s⁻¹ Y'_s.
  BANKED invariants (∀ CommRing, unit hyps on pivots/partial-pivots/N_s):
    (A) `regBlocks_movedC`: (partProd (movedC C (Z0edit0 C L)) L) agrees with (partProd C L) on the
        three blocks {11,12,21}; (B) `prodSchurCore_eq_blockSchur_partProd`: product of moved Schur
        cores = blockSchur(partProd C L).
- DLN side: `Params H = ∀ s:Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ`. `prod H A` folds
  the L factors (Fin widths). `deepestChain H r hr A s` reindexes DLN layer `A s` into the abstract
  `r ⊕ (H·−r)` block shape (cast-free ℕ chain). BANKED bridge:
  `reindex (rThr 0)(deepestChainCol L)(prod H A) = partProd (deepestChain H r hr A) L`.
- `DeepestSplit H r n = (Fin nReg → ℝ) × ((Fin (flatDim M) → ℝ) × (Fin n → ℝ))`  (reg × core × spectator).
- `framedParamsPivot H r hr hL J Pf Qf q : Params H` builds a framed DLN tuple from a DeepestSplit
  point `q`: each layer's blocks are read from `q` — pivot A_s = deepBlkA_s + gaugeReadX(q.reg,q.spec)_s,
  up Y_s = deepBlkY_s + gaugeReadY(...)_s, down Z_s = deepBlkZ_s + gaugeReadZ(...)_s, core
  T_s = (paramsEquivFlat M).symm(q.core) s  (the core slot stores the raw T-blocks directly).
  (The gauge slot stores READS: gaugeReadX/Y/Z; the core slot stores the raw core matrices.)
- The reg-energy `deepestEFull q` reads exactly the {11−1,12,21} residual blocks of
  `reindex (rThr 0)(pivotThr J)(prod H (framedParamsPivot ... q))`.
- I just PROVED (Item 1, banked): IF
  `deepestChain(framedParamsPivot q₁) = movedC (deepestChain(framedParamsPivot q₂)) (Z0edit0 (…) L)`
  (+ base-chain unit hyps), THEN `∑ deepestEFull(q₁)² = ∑ deepestEFull(q₂)²` (reg preservation, hsub3reg).

The L=2 template (BANKED, ~2700 lines) defines `psiSplitRawL2CoreConj q`: it edits ONLY the last
layer — sets the last-layer Y-read to `Y1'c` and the last-layer core block to `T1'c` (Wc⁻¹·Brc), all
other reads/cores fixed. For L=2 the only interior layer that needs a core/up edit is the single middle,
and Z₀ edit / interior up-edits collapse.

THE CRUX I must build for GENERAL L (Item 2):
Define `psiSplitRawGen q : DeepestSplit` that edits, via gauge-reads + core-slot updates, EVERY layer so
that `deepestChain(framedParamsPivot (psiSplitRawGen q)) = movedC (deepestChain(framedParamsPivot q)) (Z0edit0 …)`.
Concretely the edits per layer s:  Y-read_s ← (moved Y'_s − deepBlkY_s);  Z-read_0 ← (Z0edit0 − deepBlkZ_0);
core_s ← T'_s.  Pivots (X-reads) unchanged.
</task>

<output_contract>
Four sections, terse:
1. MISMATCH CHECK (the kill-condition). Does editing the gauge-READS (Y_s, Z_0) and core-slots of `q`,
   then re-framing via framedParamsPivot, actually realise the abstract `movedC` on `deepestChain`?
   Specifically: framedParamsPivot ADDS the deepest block (deepBlkY_s) to the read; movedC's Y'_s is
   an absolute block. Writing read ← Y'_s − deepBlkY_s makes the framed block = Y'_s. Confirm this is
   consistent for ALL blocks (pivot fixed since X-read unchanged ⟹ framed A_s = deepBlkA_s + X-read =
   same as base's A_s — but movedC also fixes A_s, GOOD). Flag any block where the reindex/frame
   (Pf/Qf, the pivotThr J vs rThr split, the finCongr width casts) breaks the "read-edit = abstract-edit"
   correspondence. Is there a genuine wall, or is it bounded plumbing?
2. psiSplitRawGen DEFINITION shape: the cleanest way to write it in DeepestSplit coords (a single
   `regGaugeSlotEquiv.symm` gauge edit writing all Y'_s reads + the Z₀ read, plus a `paramsEquivFlat`
   core-slot update writing all T'_s). Should the moved blocks (Y'_s, T'_s, Z0edit0) be defined as
   `deepestChain`-level abstract quantities pulled back, or recomputed in DLN coords?
3. MOVE-IDENTITY proof strategy: prove `deepestChain(framedParamsPivot(psiSplitRawGen q)) s = movedC(...) s`
   LAYER-BY-LAYER (funext s) by matching the four blocks. What is the induction/cast structure; which of
   the banked lemmas (reindex_decode_split_toBlocks, the block reads) carry over from L=2; where is the
   only genuinely new work vs the L=2 last-layer-only version?
4. RISK/SIZE estimate in Lean lines + the single most likely place it walls.
</output_contract>

<grounding_rules>
You are reviewing a DESIGN, not verifying Lean compiles. Flag clearly which claims are (i) forced by the
definitions as I described them vs (ii) your inference about what will be tractable in Lean. If you think
my read-edit ⟹ abstract-edit correspondence has a hidden inconsistency, say so explicitly and give the
minimal counterexample sketch. Do not invent Mathlib lemma names.
</grounding_rules>

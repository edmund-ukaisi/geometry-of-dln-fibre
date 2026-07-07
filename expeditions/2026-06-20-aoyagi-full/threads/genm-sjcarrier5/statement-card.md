# Statement card — `genm-sjcarrier5` (R1-UPPER Phase-2 piece 2: the per-chart block-reindex bridge)

Thread: `genm-sjcarrier5` (formalisation tide). Branch: `genm-sjcarrier5` (off
`expedition/aoyagi-full` @ `7ab9507e`). Module:
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJBlockReindex.lean`.

This tide builds **piece 2 of the general-`L` `(S,J)` resolution change-of-variables** — the bridge from
`gammaPeelIntegral`'s raw front-factor chart integral to the abstract block coordinates the banked Schur
machinery lives on. `sjJointResolution` (`RouteMSJResolution.lean:803`) is **UNTOUCHED** (still the named
sorry). This is honest-partial multi-tide progress: the algebraic core + the measure half of the block
reindex are landed; the Schur/shear/corank-peel + `(S,J)` descent are the remaining pieces.

---

> **Claim 1 (pointwise — the raw loss IS a block loss).** For a raw front factor `A₀ : Matrix (Fin p)
> (Fin n) ℝ`, a tail product `Q : Matrix (Fin n) (Fin q) ℝ`, and any row/column reindex equivs
> `er : Fin p ≃ α`, `ec : Fin n ≃ β`, the Frobenius loss `frobSq (rmatMul A₀ Q)` equals
> `frobSq ((A₀.reindex er ec) * (Q.submatrix ec.symm id))`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.frobSq_rmatMul_reindex`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJBlockReindex.lean` @ `genm-sjcarrier5`)
> - **Gloss.** The squared Frobenius norm of a raw matrix product is invariant under any bijective
>   relabelling of the output rows (`er`), and the contraction-index relabelling (`ec`) rides through
>   the product — so the loss can be read on the block-reindexed factor times the row-reindexed tail.
> - **Proved.** The equality, unconditionally, for arbitrary equivs (no invertibility, no measure theory).
>   Pure `Equiv.sum_comp` + `Matrix.mul_apply`.
> - **Assumed / Cited / Deferred.** none.
> - **Status.** sorry-free (axiom-clean `[propext, Classical.choice, Quot.sound]`).

> **Claim 2 (chart membership transfers to the block).** If `er, ec` extend the pivot embeddings
> (`er.symm (Sum.inl i) = ρ i`, `ec.symm (Sum.inl j) = κ j`), then the reindexed top-left block equals
> the `(ρ,κ)` minor (`pivotBlock_reindex_eq_submatrix_of_ext`), so `IsUnit (A₀.reindex er ec).toBlocks₁₁
> ↔ A₀ ∈ pivotChart ρ κ`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.isUnit_toBlocks₁₁_reindex_iff` (+ `pivotBlock_reindex_eq_submatrix_of_ext`)
> - **Gloss.** The abstract-chart condition "reindexed pivot block invertible" is literally the concrete
>   chart condition "the chosen `t × t` minor is a unit".
> - **Proved.** The block identity and the `IsUnit` equivalence, unconditionally.
> - **Assumed / Cited / Deferred.** none.
> - **Status.** sorry-free (clean-three).

> **Claim 3 (measure half — the inner chart integral transports).** For a fixed tail product `Q` and
> reindex equivs `er, ec` extending `ρ, κ`, the inner front-factor chart integral equals the
> block-coordinate integral over `genBox ∩ {IsUnit toBlocks₁₁}` of the block-matrix loss:
> `∫⁻ A₀ in matBox p n T ∩ pivotChart ρ κ, ofReal (frobSq (rmatMul A₀ Q))^{−c'}
>   = ∫⁻ B in genBox _ _ T ∩ {B | IsUnit (toBlocks₁₁ B)}, ofReal (frobSq (Matrix.of B · Q.submatrix ec.symm id))^{−c'}`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.chartInner_blockReindex_eq`
>   (built on `matReindexEquiv` (the MP block-reindex `arrowCongr'`), `measurePreserving_matReindexEquiv`,
>   `matReindexEquiv_preimage_chart`, and Claims 1–2)
> - **Gloss.** The measure-preserving block-reindex (`arrowCongr'` on rows and columns) carries the raw
>   box ∩ pivot chart onto the block box ∩ invertible-pivot locus, and the integrand becomes the
>   block-matrix loss — the exact form the banked `frobSq_schur_toBlocks_split` (invertible pivot on the
>   locus) consumes to expose the corank block `Γ`.
> - **Proved.** The integral equality, unconditionally, for any `c', T`, via
>   `MeasurePreserving.setLIntegral_comp_preimage_emb`. (Uses `matReindexEquiv` MP from
>   `volume_preserving_arrowCongr'`.)
> - **Assumed.** `er, ec` extend `ρ, κ` (`her`, `hec`) — supplied-equiv form. The `ρ,κ`-instantiated
>   form (no supplied equivs) is landed here too: `chartInner_blockReindex_eq_of_emb`, via the local
>   block-split equiv `blockSplitEquiv : Fin t ⊕ Fin (m−t) ≃ Fin m` (fronting the embedding's image;
>   `blockSplitEquiv_inl`, the name-clash-free analogue of the banked `sumSplit`). So the transport
>   applies directly to `gammaPeelIntegral`'s actual `(ρ, κ)`.
> - **Cited.** none.
> - **Deferred (named, the remaining mountain).** (i) the Schur split + measure-preserving shear
>   `D ↦ Γ` + corank-block radial peel (`corankStep` / `frobSq_schur_toBlocks_split` /
>   `measurePreserving_shearSub` / `matBox_corank_*` — all banked pointwise/per-step, not yet welded to
>   this transport); (ii) the `(S,J)` `Nat`-measure descent to the monomial terminal
>   (`sjLoss_terminal_lintegral_lt_top`); (iii) wiring the reduced coupling to the strong IH
>   (`redChain t M`); (iv) `gammaPeelIntegral < ⊤` (`sjJointResolution`) itself. These are pieces 2
>   (remainder) and 3 of the CoV+recursion.
> - **Structure & ideas observed.** The Matrix/function-synonym defeq is the dominant Lean-idiom friction
>   (not a math wall): `*` (HMul) and `.field` dot-notation resolve on the *syntactic* head before defeq,
>   so block-typed operands must be presented via `Matrix.of B` (head `Matrix.of`) or genuine
>   `Matrix`-typed binders; `arrowCongr'`-nested reindex is `Matrix.reindex` definitionally, and the
>   function-typed codomain `((Fin t ⊕ Fin a) → (Fin t ⊕ Fin b) → ℝ)` carries the Pi `volume`/`SigmaFinite`
>   instances directly (avoiding the `Matrix`-synonym `MeasureSpace` gap). The transport needs **no**
>   domain measurability (`setLIntegral_comp_preimage_emb` handles it; the integrand rewrite is
>   `lintegral_congr`, pointwise).
> - **Route.** (Codex xhigh, `codex/firstbrick-answer.md`, confirmed my analysis.) First brick =
>   supplied-equiv block-reindex transport (avoid the `ρ,κ`-complement construction); ordered sequence:
>   block-reindex transport → `ρ,κ` wrapper (`sumSplit`) → Schur-split rewrite on the reindexed chart →
>   block Fubini + `measurePreserving_shearSub` → pure R-blowup corank peel wired to `redChain` IH →
>   `(S,J)` descent assembly into `sjJointResolution`. Close-in-one-tide judged NOT realistic; this tide
>   banks the transport (piece 2, measure half) + the pointwise algebra.
> - **Status.** sorry-free (clean-three, forced `#print axioms` confirmed).

---

## Build / hygiene

- Isolated module builds green (`scripts/lb DLNFibre.DLN.RLCT.Validate.RouteMSJBlockReindex`).
- Forced `#print axioms` (olean-bypassing) on all five load-bearing results:
  `[propext, Classical.choice, Quot.sound]` — clean-three, no `sorryAx`, S2-free (no `monomial_rlct`).
- Wired into the aggregator `DLNFibre.lean` (import at end); no name clashes with siblings.
- `scripts/sorries`: 20 sorry / 0 #exit / 0 native_decide / 1 axiom — **unchanged from baseline**
  (this tide adds a sorry-free module; `sjJointResolution` untouched).
- LoC: +259 (`RouteMSJBlockReindex.lean`) + aggregator import.
- Full `scripts/lb DLNFibre`: 0 errors through 8450/8749 jobs, then the documented tail-stall under
  contention (timeout, not an error); isolated module green + `rg` name-clash check (0 clashes) confirm
  integration per `lean/CLAUDE.md`'s guidance.

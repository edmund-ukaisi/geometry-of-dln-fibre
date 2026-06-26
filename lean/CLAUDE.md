# Lean conventions (DLNFibre)

## Build
- **Multi-worktree / multi-session: build via `scripts/lb`, NOT bare `lake build`.** `lb` symlinks this
  worktree's `.lake/packages` to the shared rev-keyed mathlib store (mmap-shared, no per-worktree clone)
  and throttles total Lean workers across all sessions via a global semaphore. Full rationale + box
  sizing: [`../docs/policies/lean-build-workflow.md`](../docs/policies/lean-build-workflow.md). **Do NOT
  `lake exe cache get` in a worktree** — it re-clones ~7 GB and defeats the sharing; the shared store is
  built once by `scripts/lake-store-setup <mathlib-rev>` (detached; exceeds the 10-min cap).
- Fresh shells: `source ~/.elan/env` before any `lake` command.
- Build from this `lean/` directory: `scripts/lb DLNFibre.<Module>`, or `scripts/lb` for the whole
  library. (Bare `lake build`/`lake env lean` still work for one-off elaboration, but bypass the shared
  store + the global concurrency cap — fine for a single `#eval`, not for parallel builds.)
- Toolchain: Lean `v4.29.0` (`lean-toolchain`), Mathlib `v4.29.0` (`lakefile.toml`). Matches the `ai-research-assistant` harness one level up, so its v4.29 Mathlib idioms transfer.

## Library shape — engine vs application
- **`DLNFibre.Core.*`** is the network-free **engine** (quiver orbits, Kostant partitions / rank patterns, `Ext` codimension, `(C, θ)`). It **must never import `DLNFibre.DLN`**. The dependency arrows point `DLN → Core → Mathlib`.
- **`DLNFibre.DLN.*`** is the **application** (multiplication-map fibres, the square-Frobenius loss, the RLCT payoff); it depends on `Core`.
- State each result at the specificity its claim needs; lift a piece into shared `Core` API on its **second** use, not in anticipation of one. Good API (characterizations over predicates, weakest hypotheses, name = content) is the `bedrock`/`precision` discipline, not a folder layout.

## Aggregator
- `DLNFibre.lean` is single-writer. Add new module imports at the end; do not reorder existing imports.
- New modules live at `DLNFibre/<Core|DLN>/<Topic>/<File>.lean`; one substantive theorem family per file.

## Sorry gate
- Zero `sorry` / `axiom` / `native_decide` / `#exit` in committed files. Audit with `scripts/sorries` from `lean/` before every commit.
- A `sorry` with a correct statement is a building block; a `sorry` with a wrong statement misleads. Fix wrong statements first.
- **`lake build` / `scripts/lb` exit-0 can MASK a `sorryAx` via a stale olean cache.** If an edit does not
  invalidate a `.olean` (a downstream-only change, an edit Lean's incremental compiler deems irrelevant), a
  prior `sorry` / type-error can persist in the cached olean and the build still reports success. **Confirm
  any "sorry-free" / axiom-footprint claim with `#print axioms` (which FORCES elaboration), never the build's
  exit status alone** — or force-recompile (delete the `.olean` / `touch` the source). The aggregator's
  `AxCheck.lean` does this for the load-bearing results on every build; add new load-bearing results there, or
  run a force-rebuilt `#print axioms` scratch (delete its olean first). (Caught a persisted diagonal-`sorry` +
  an unreported type-error in `RouteMSchurFrameDet`, 2026-06-26.)

## Bedrock (the bar above the sorry gate)
A green, sorry-free build is the **floor**: it defeats *technical* slop, never *conceptual* slop —
"technically correct but subtly wrong, not The Way." Build each result as **bedrock**: something the next
theorem stands on without re-opening it. Where there's nothing to check against, **beauty is the guide** — a
vacuous, mis-scoped, or overclaiming theorem is *ugly*. In practice that recurrently means (not exhaustively):
name = content; non-vacuous, with the witness *shown* in-file; the weakest hypotheses that suffice, in usable
form; characterized (an `iff`) over asserted; every *cited*/*assumed* step named (never an `…rlct…`-style
theorem that secretly claims an unproved analytic interface — here the `rlct = ½·codim` reading rests on a
cited bound). The controller judges against this taste and holds precedence — full statement:
[`../docs/policies/bedrock.md`](../docs/policies/bedrock.md).

## Style
- `↦` not `=>` for lambda arrows.
- `decide +kernel`, not `native_decide`. Avoid `@[implemented_by]`, `@[extern]`, `unsafePerformIO`.
- One-line docstrings.
- Name a lemma for what it proves: a kernel/ideal *membership* fact is `…_mem_ker`, not `…_gen` (which reads as an ideal-generation claim).
- Confirm a Mathlib lemma exists before building a proof around it: `scripts/lean-search "..."`, or `rg` over `.lake/packages/mathlib/Mathlib/`.
- Pre-stage uncertain API with `example` blocks that pin lemma names/types; keep them as durable contracts.

## Mathlib gotchas (v4.29 pin)
Toolchain-generic notes that transfer at this pin. Accumulate new, DLN-specific ones here as they are found
(the ReLU programme's proof-specific notes were intentionally not ported — they were about a different theory).

- **`Basis` is `Module.Basis` at the v4.29 pin.** Bare `Basis` is unknown even with full Mathlib imports;
  ascribe `Module.Basis (Fin _) ℝ _` (e.g. from `Pi.basisFun`). Dot-notation (`b.tensorProduct b'`) is
  unaffected. Likely to recur in any `Matrix.rank` / column-span work.
- **`decide +kernel`, never `native_decide`.** Kernel `decide` is axiom-clean; `native_decide` trusts the
  compiler and breaks `#print axioms` hygiene. Kernel-reduction cost is **heartbeat-invisible** (a
  `maxHeartbeats` bump does not speed it), so a heartbeat timeout on a `decide` is not the symptom to chase.
- **Matrix-product identities over `ℤ` by `decide`, then cast.** An `ℝ` matrix-product identity is a
  `Matrix.ext` blow-up (per-entry `simp`, times out at scale). Write the matrices over `ℤ`
  (`DecidableEq` ⟹ `Matrix.mul` decides by kernel reduction, `by decide`), define the `ℝ` ones via
  `· .map (Int.castRingHom ℝ)`, and transfer products with `← Matrix.map_mul` (cast is a ring hom). No `ℝ`
  `Matrix.ext` at all.
- **`Fin`-vector `![…]` + `fin_cases` friction.** `fin_cases i` leaves the index as `⟨k, ⋯⟩` (a `Fin.mk`),
  so `Matrix.cons_val_one`/`_two`/… do not fire on the outer selection. Normalize first with
  `rw [show (⟨k, by omega⟩ : Fin n) = (k : Fin n) from rfl]`, then the `cons_val_*` simp set fires; or prove
  the components as separate `have`s and assemble with `funext i; fin_cases i`.
- **`φ` (U+03C6) as a binder name can hit a lexer reject** (`unexpected token 'φ'; expected identifier`)
  when an editing tool inserts a confusable/variant codepoint. If a `∃ φ …` / `obtain ⟨φ, …⟩` line fails
  to parse despite looking right, rename the binder to ASCII (`phi`) or `ψ`; capital `Φ` (U+03A6) has not
  shown the problem. Cost two build cycles on `NoetherMonicPositioning.lean`.
- **No off-the-shelf rank-normal-form / "equal rank ⟹ equivalent matrices" in v4.29.** Built at the
  linear-map level in `Core.FibreNormalForm` (`exists_conj`, `exists_baseChange_of_rank_eq`): for a
  rank-`r` `f : (Fin n → k) →ₗ (Fin m → k)`, restrict to `fU : U ≃ range f` (`U` a `ker`-complement,
  via `Submodule.quotientEquivOfIsCompl _.symm ≪≫ LinearMap.quotKerEquivRange`); two maps with equal
  ker+range finrank are conjugate (`prodEquivOfIsCompl` kernel/range decompositions glued by
  `LinearEquiv.ofFinrankEq`), transferred to matrices by `LinearMap.toMatrix'_comp` +
  `LinearMap.toMatrix'_toLin'`. Useful `rfl`s: `Matrix.rank A = finrank (range (toLin' A))` and
  `toLin' A = A.mulVecLin`. The `IsCompl` finrank lemma is `Submodule.finrank_add_eq_of_isCompl`.
- **`RingEquiv.height_comap` is the clean `Ideal.height` transport** (`(I.comap e).height = I.height`,
  any ideal, no `IsPrime`). For codim-invariance of a locus under a *linear* coordinate change, the
  set-level route `vanishingIdeal (shifted) = comap (algEquiv) (vanishingIdeal)` + `height_comap` is
  cleaner than re-deriving an `Ideal.map` identity. Used in `Core.FibreNormalForm.codimRep_baseChange_image`
  — this closes the linear-coordinate-invariance gap `Core.OrbitCodim`'s docstring flagged, for the
  base-change family of isos.
- **The end-factor (`GL_{d_N}×GL_{d_0}`) action is just `Core.BaseChange.baseChange` with inner units
  `= 1`.** No new action needed: mult-equivariance `mult (P•A) = P_N·(mult A)·(P_0)⁻¹` is
  `mult_eq_submult` + the LANDED `submult_smul` at the full interval `(0, last)`. Caveat: the
  same-rank ⟹ same-fibre-codim headline genuinely needs `N ≥ 1` (`hN : (0 : Fin (N+1)) ≠ Fin.last N`)
  — for `N = 0` `mult` is the constant `1`, the end vertices coincide, the action only conjugates, and
  the claim is false.

## θ-count discharge findings (`Core.CCodimCornerMono`, thread 06)
- **The θ-count headline reduces to ONE combinatorial inequality**: the dimension-monotonicity of
  `cCodim · 0` (`cCodim e 0 ≤ cCodim e' 0` for `e ≤ e'`, + a strict all-vertex version). Both gating
  bricks (`hLowerBound`, `hRecover`) discharge from it via the LANDED rank-shift `cCodim d t = cCodim
  (d−t) 0` + the Gabriel→Kostant bridge `gabrielPartition` (a tuple's `kostantArrayOfRank (rankFn ·)`
  recast into the `CTheta` `Fin × Fin → ℕ` encoding via `finArrayOfSupp`).
- **The right construction for the dimension-monotonicity is the SHORTEST-interval split** (at an
  over-covered vertex `k`, split the shortest `[i,j] ∋ k` into `[i,k−1]+[k+1,j]`): verified to never
  increase `codimForm` (199/199), whereas splitting a non-shortest interval CAN increase it. The
  merge-up route (raise the corner per-partition) is DEAD — corner-`s` partitions often admit no
  corner-raise with non-increasing `codimForm` (71/252).
- **Strict SINGLE-vertex dimension-mono is FALSE** (e.g. `cCodim [1,1,0] 0 = cCodim [1,2,0] 0 = 0`);
  only the strict ALL-vertex version holds (`d−r < d−s` everywhere when `r > s`). Strict corner-
  monotonicity (needed for `hRecover`'s "corner = r") rides on the all-vertex strict version.
- **`codimForm` is the type-A `Ext`-pairing form**: reindexed, `= ∑_{A=[a,b],B=[c,e]: a<c≤b+1, b<e}
  m̄(A) m̄(B)`. The split delta is `∑_B coeff(B) m̄(B)` with the positive-coeff `B` being the shorter
  intervals covering `k` (absent when `I` is shortest). `codimForm` is also corner-blind
  (`codimForm_update_corner`, LANDED) — it never reads `m_{0N}`.

## `cCodim·0` weak monotonicity LANDED (`Core.CCodimZeroMono`, thread 07)
- **`cCodim_zero_mono` is PROVED sorry-free** (`e ≤ e' ⟹ cCodim e 0 ≤ cCodim e' 0`), discharging the
  weak gating hypothesis `hMono`. The θ-count headline is now `numTop_eq_ncard_topComponents_of_strict`
  — UNCONDITIONAL except for the strict `hMonoStrict`. Axiom-clean `[propext, Classical.choice,
  Quot.sound]`. `hLowerBound` is fully unconditional.
- **Reusable infrastructure** (all in `CCodimZeroMono`, built on `CThetaQIPConverse`'s `codimBil`):
  `codimBil_extendℤ_boxℤ_right`/`_left` (univ-sum collapse of `codimBil` vs a single box, via the
  clamped `rrInd`/`llInd` indicators), `codimBil_boxℤ_boxℤ` (the box-pairing value), `codimForm_add`
  (reused), `codimForm_congr_onbox` (codimForm reads only on-box values).
- **Four atomic shortest-split moves**, each with delta / sign / `_le` / `_cover` / `_mem`: interior
  `redMove` (`c = b+2` gap kills the self-term), `leftShrink` (omit left endpoint; handles `a=0` and
  singleton-via-empty-piece), `rightShrink` (omit right endpoint; handles `d'=N`), `removeMove`
  (singleton removal; coefficient ALWAYS `≤ 0`). Boundary lesson: there is NO `Fin` `b` with `b+1 = 0`,
  so `k=0` left-endpoint and `k=N` right-endpoint genuinely need the dedicated shrink moves (the
  interior `redMove`'s empty-piece guard `a≤b` can't be made false when `a=0`). `reduceStep` dispatches
  by `k`'s position; `exists_le_codimForm` is the recursion (strong induction on `∑ e'`).
## `cCodim·0` strict monotonicity LANDED → θ UNCONDITIONAL (`Core.CCodimZeroStrict`, thread 08)
- **`cCodim_zero_strict` is PROVED sorry-free** (`(∀ v, e v < e' v) → cCodim e 0 < cCodim e' 0`),
  discharging `hMonoStrict`. **`numTop_eq_ncard_topComponents` is now UNCONDITIONAL** (`θ =
  #top-dimensional irreducible components of Σ̄^r`, no open hypothesis); axiom-clean `[propext,
  Classical.choice, Quot.sound]`.
- **Route B (the landed route), reusing the four atomic moves + their `_le` sign lemmas:**
  - **Double sum** `codimForm_extendℤ_eq_sum_pairs`: `codimForm (extendℤ m) = ∑_{A,B} m(A) m(B) ·
    [pairBox A B]` (built from `codimBil_sum_right` + `codimBil_const_mul_right` + the existing
    right-rectangle collapse; `rrInd (B.1)(B.2) A ↔ pairBox A B` on the box). Gives `∃ active pair ⟺
    codimForm ≥ 1` (`codimForm_extendℤ_pos_of_exists_pair` / `exists_pair_of_codimForm_pos`).
  - **Lemma Y** `codimForm_extendℤ_pos_of_fullCover`: full coverage ⟹ `codimForm ≥ 1`, via the
    extremal longest-`[0,b]` argument (`b<N` from corner-`0`; maximality forces `c≥1` so `[0,b]→[c,d]`
    pairs).
  - **Lemma X** `reduceStep_strict`: select the active pair minimising `min(ilen A, ilen B)`; split the
    shorter member at the partner-adjacent vertex. **ClaimA** (`claimA_left`/`claimA_right`) — that
    member is shortest *active* covering that vertex — is the one non-mechanical step (the `y<d` vs
    `d≤y` / `a<x` vs `x≤a` interval-arithmetic case split; minimality MUST be over the shorter member,
    Codex-confirmed). The partner sits at split-coefficient EXACTLY `−1` (`splitCoeff_partner_le` &c.,
    `omega` on indicators), and `sum_coeff_le_neg_one` upgrades the `_le` ("≤0") to `_lt` ("≤ −1").
    8-way dispatch (left/right member × interior/leftShrink/rightShrink/removeMove); each move has TWO
    partner orientations (the partner can sit left or right of the split source).
  - **Wiring** (`cCodim_zero_strict`): a minimiser `m'` of `cCodim e' 0` is full-coverage (Lemma Y ⟹
    `codimForm ≥ 1`); `reduceStep_strict` drops it `≥ 1` to a partition of `e'` decremented at `k`,
    which still dominates `e` (`e ≤ e''` since `e < e'` everywhere), so LANDED `exists_le_codimForm`
    gives `cCodim e 0 ≤ cCodim e' 0 − 1`. (No `+1`-step vector needed — the minimiser-of-`e'` route is
    cleaner and uses only the two given nonemptiness hypotheses.)
  - RULED OUT (don't re-explore): Route A (simple `Φ` with `codimForm ≥ Φ ≥ cCodim+1`) — the gap is
    often exactly 1, no simple `Φ` carries it; every deterministic LOCAL step-selection rule fails —
    the strict step's location is config-dependent (the "involved-in-a-pair + extremal-by-length"
    refinement is load-bearing).
- **Dependent-dimension matrix reassociation / cast handling — the kernel that cracked the `prodAux`
  front-peel (deferred twice).** For products over `Fin (M k)`-style dependent dimensions:
  (i) `rw [Matrix.mul_assoc]` / `simp` / `conv` will NOT match `(a*b)*c = a*(b*c)` through the dependent
  `HMul` instance (higher-order matching fails). Close it with a **fully-applied term** instead:
  `set X := …; set Y := …; exact Matrix.mul_assoc a X Y` (or state a generic
  `mul_three_reassoc {p q r s : Type*} [Fintype …] (a b c) : a*b*c = a*(b*c) := Matrix.mul_assoc a b c`
  once and reuse — cf. `RouteMFrontPeel.mul_three_reassoc`, generalising `DeepestTelescoping.mul_four_reassoc`).
  (ii) Do cast bookkeeping at the **equiv level, never entrywise** (`ext` into a cast-wrapped `∑ if…` is the
  trap that stalled two tides): `finCongr_refl` collapses `finCongr (rfl-true width eq)` to `Equiv.refl`,
  then `Matrix.reindex_refl_refl` (via `erw` — plain `rw`/`simp` won't match the dependent `Matrix.reindex`)
  collapses `reindex refl refl` to identity; `RouteMAchieverBridge.reindex_finCongr_mul` distributes a
  width-reindex over a product. (iii) Peel layer-products by **prefix-length induction reusing
  `prodAux_succ`**, not entrywise. This kernel transfers to any `prod`/`prodAux` reassociation (e.g. the
  L2/D1 `endpoint_telescoping`).

## General-`M` achiever-chain RATE engine LANDED (`Validate.RouteMChain*`, thread 35)
- **The full M-agnostic rate engine for `prod M (φ_M u) = u • H` is banked sorry-free** (no per-entry
  `ring` blow-up; the `(3,3,3,3)`/`(4,4,2,2)` instances did per-entry `ring`, this does NOT):
  - `RouteMChainFactor`: `step_of_factor` (`Ck=Bk·Qk+u•Rk`, `Qk·Ak=Cnext`, `Ek=Rk·Ak ⟹ Ck·Ak=Bk·Cnext+u•Ek`,
    generic) + `chain_block` (`[I|N]·[C−N·W;W]=C` on sum-blocks, `Fintype.sum_sum_type`).
  - `RouteMFactoredChain`: `FactoredChain` (factored per-level data + `hC`/`hQA`/`base`) → `toChain : Chain`
    (discharges `Chain.step` via `step_of_factor`); `telescope_zero` fires `C₀·suffix₀ = u•Hmat₀`.
  - `RouteMChainRate`: `prod_eq_reindex_suffix` (the banked suffix bridge restated on `FactoredChain`).
  - `RouteMChainBlock`: **the `hQA` on AMBIENT `Fin (M k)`** — `finSplit`/`chainQ`/`chainA` +
    `chainQ_mul_chainA : chainQ·chainA = C`, via `submatrix_mul_equiv` inner-equiv cancellation reducing to
    `chain_block`. This is the `S-hybrid` route (Codex-confirmed): do the block algebra on `Fin t ⊕ Fin c`,
    reindex onto `Fin (M k)` at the seam, ONE `submatrix_mul_equiv` cancels the inner equiv. **Closes the
    dependent-`Fin (M k)` block algebra** without entrywise `ext`.
- **The validated per-`M` instance DESIGN** (the remaining SUPPLY; `threads/35-…/thread.md` for the full
  spec): define `C` RECURSIVELY so `hC`/`hQA` are near-`rfl` — `C 0 := 1`, `C k := Bmat k·chainQ(N_k)+u•R̄_k`
  (interior, `hC k` is `rfl`), `C L := u•R` (`base` rfl), `A k := chainA (N_k)(W_k)(C(k+1))` (`hQA k :=
  chainQ_mul_chainA`). Off-by-one: `Twid 0 = M 0`, `Twid (k+1) = t_k` (achiever descent, `t_0 := M_0`), so
  the FIRST boundary is the identity boundary (`c_0=0`, `chainQ at c=0 = I`), genuine `chain_block` at
  `1≤k<L`, leaf at `k=L`. **Keep widths EXPLICIT** (not `![…].getD`/`Fin.cons`) or the `c=0` `chainQ=I`
  `isDefEq` blows the heartbeat budget.
- **The RATE identity is PATH-AGNOSTIC** (Codex + the telescope theorem): any chain with `C 0 = 1`,
  `step`, `base`, layer-match gives `prod = u•H`. The achiever profile is needed only for the DOWNSTREAM
  Jacobian det `|u|^{minAdm−1}` + the `½·minAdm` threshold — the chart-identity checkpoint can use achiever
  widths but prove only the rate.

## ∀M CHART IDENTITY LANDED (`Validate.RouteM{3333Chain,GenChain,GenChartId,GenChartId3333}`, thread 35)
- **`routeMCore_phiGen : routeMCore M (φ u) = u²·V` is PROVED for ARBITRARY `M` + descent `t`** (sorry-free,
  axiom-clean), via the rate engine — NO per-entry `ring`. The `(3,3,3,3)` `match`-fields lifted to an
  opaque-`t`-width recursion (`chainOfMt`); SPECIALIZES to `(3,3,3,3)` (`routeMCore_phiGen_3spec`).
- **The structural lift was CLEANER than feared** (Codex `S-hybrid` corroboration; my version simpler):
  uniform `dite`-guarded fields (`if k < L`), `hC`/`hQA` by `dif_pos` + `chainQ_mul_chainA`, `base` by
  `dif_neg`. The identity boundary `k=0` (`c_0 = 0`) needs NO special-casing — `chainQ`/`chainA` at `c=0` go
  through `chainQ_mul_chainA` directly. Widths: `Wext`/`Text` ℕ-indexed `dite` (NOT `getD`).
- **`chainQ_cZero` (`chainQ` at `c=0` is `I`, via `finSplit_refl` + `finSumFinEquiv_symm_apply_castAdd`)** is
  the identity-boundary fact making `C 0 = 1` reachable (`Bmat 0 = 1`, `Rmat 0 = 0`). Applied via
  `have hQ := chainQ_cZero _ _` (the `exact`/`have` accepts the defeq `c = Wext 0 − Text 1 = 0` that `rw`
  can NOT match — `rw [chainQ_cZero]` fails on the unreduced `Fin (Wext 0 − Text 1)`).
- **More dependent-HMul cast lessons:** (i) the `C 0 = 1` close needs a `show` at LITERAL `Fin n` types to
  force the opaque-width reduction before `rw [Matrix.one_mul, smul_zero, add_zero]`. (ii) `C 0 · suffix =
  suffix` from `hC0eq : C 0 = 1`: `rw [hC0eq]; exact Matrix.one_mul _` (do NOT write `1 · suffix` with a
  literal-`Fin` `1` — opaque `Wwid 0` blocks the HMul; let `rw` keep the dependent type).
- The ACHIEVER `t` (the `minAdm` minimiser) instantiates this for the DOWNSTREAM box-divergence atom
  (det `|u|^{minAdm−1}` + cov + `nodeChartGeneral` + `routeMCore_box_diverges_achiever ∀M`).

## Box-divergence atom ∀M — WALL on the general Jacobian det (thread 35, Codex-corroborated)
- **The `NodeAchieverChart M` `leaf_integrand` field is det-INDEPENDENT** — `RouteMGenLeafIntegrand.lean`'s
  `leaf_integrand_of_rate` (pure algebra in `F∘φ = u_p²·V`, ANY `leafH`) + `VvalGen_nonneg` are BANKED ∀M.
- **The WALL is the general Jacobian determinant `|det Dφ_{M,t}| = ∏|u_j|^{leafH j}`** (the headline-gate
  blocker; `RouteMLayerCoverGE:130` `sorry` stays). NOT a bounded build on the banked machinery:
  - The `(3,3,3,3)` `RouteM3333Atom` det is **hand-instance machinery** — the literal `frameB : Fin 27 → ℕ`
    SCC-grading, the hand-built 7×7 K/Kᵀ coupling-block det, the 27-coord triangular `injOn`. NONE lift
    mechanically (block sizes/grading/coupling all depend on `M`,`t`).
  - `general_composed_clm_abs_det` only telescopes a `List` of full-ambient CLM dets IF the factors+dets are
    given; it does NOT build the parametric frame. `chainOfMt` builds layers via the ABSTRACT `chainA`/`chainQ`
    (network-product algebra), not a flat-coord frame product — so even `(3,3,3,3)`'s `phiGen ≠ phi3333`;
    `phi3333_abs_det` does NOT transfer.
  - Bottleneck (decorrelated Codex xhigh, `threads/35-…/codex/genM-det-*`): a **parametric full-ambient
    Schur-frame/LDU determinant + pullback to source-monomial exponents** (math verified: `|det frame| =
    |det K|^{r+c}`, sympy). A MULTI-WEEK design pass, not a template lift. A focused matrix-indexed
    `SchurFrame` det theorem is the recommended next unit; forcing the per-instance method ∀M = fragile
    (anti-bedrock).
  - Also needed: **flat coordinatization** of `phiGen` (scalar-radial + opaque block data) as a full-ambient
    `(Fin N → ℝ) → (Fin N → ℝ)` map — a prerequisite for ALL chart fields.
- The atom IS banked for the three anchors (`routeMCore_box_diverges_achiever_{334,4422,3333}`); ∀M is gated.

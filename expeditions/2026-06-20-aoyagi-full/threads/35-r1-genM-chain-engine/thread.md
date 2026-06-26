# Thread 35 — the general-`M` achiever-chain RATE engine (formalisation tide)

**Seat:** formaliser (tide). **Date:** 2026-06-26. **Branch:** worktree `worktree-agent-ab65ad6d0ec4aad88`
off `expedition/aoyagi-full`.
**Goal:** the multi-pass crux of the R1-lower achiever chart — the per-`M` `Chain` instance + `step`/`base`,
then the chart identity `prod M (φ_M u) = u • H` via the banked telescope + suffix bridge.

## What landed (sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`)

The **complete M-agnostic RATE engine** — every reusable piece between the cert's per-boundary block data
and the chart-identity rate factor `prod M (φ_M u) = u • H`, with NO per-entry `ring` blow-up:

1. **`RouteMChainFactor.lean`**
   - `step_of_factor` — the generic telescope step (any matrix shapes): from `Ck = Bk·Qk + u•Rk`,
     `Qk·Ak = Cnext`, `Ek = Rk·Ak`, derive `Ck·Ak = Bk·Cnext + u•Ek`. The decorrelated-Codex
     factorization that isolates `Chain.step` from the block construction.
   - `chain_block` — the cert's chaining crux on sum-blocks: `[I | N]·[C − N·W ; W] = C`
     (`Fintype.sum_sum_type` + block multiply).

2. **`RouteMFactoredChain.lean`** — `FactoredChain n u` (the factored per-level data: widths +
   `A`/`C`/`Bmat`/`Qmat`/`Rmat` + `hC : C_k = B_k·Q_k + u•R̄_k` + `hQA : Q_k·A_k = C_{k+1}` + `base`) and
   `FactoredChain.toChain : Chain n u` (discharges `Chain.step` via `step_of_factor`, `E_k := R̄_k·A_k`).
   `telescope_zero` fires the keystone `C_0·suffix_0 = u•Hmat_0`.

3. **`RouteMChainRate.lean`** — `FactoredChain.prod_eq_reindex_suffix`: with the width match `hW` and the
   layer match `hA`, the banked suffix bridge gives `prod M A = reindex (suffix 0)`. The per-`M`
   construction simplifies `suffix 0` via its own `C 0 = 1` + `telescope_zero` to `prod M A = u • H`.

4. **`RouteMChainBlock.lean`** — the `hQA` block-assembly on the AMBIENT `Fin (M k)` (the `S-hybrid` route):
   - `finSplit` (canonical `Fin M ≃ Fin t ⊕ Fin (M−t)`), `chainQ` (`[I|N]` reindexed onto `Fin M'`),
     `chainA` (`[C−N·W;W]` reindexed onto `Fin M'`).
   - `chainQ_mul_chainA : chainQ·chainA = C` — proved M-agnostically via `submatrix_mul_equiv`
     inner-equiv cancellation reducing to `chain_block`. **This closes the dependent-`Fin (M k)` block
     algebra** that the project's notes flagged as the recurring stall.

5. Validation (sorry-free): `RouteMChainRateValid` (`(1,1,1)` `L=2` end-to-end: FactoredChain → toChain →
   telescope → bridge → genuine `prod`); `RouteMChainBlockValid` (`chain_block` with genuine nonzero
   `N:2×1, W:1×2, C:2×2` — the `r_s=1` boundary, non-vacuous beyond the `N=0` rank-stay case).

## The validated DESIGN for the per-`M` instance (the remaining work)

The decisive simplification, verified on the spike (`/tmp/spike_qa5.lean`, closed sorry-free) and confirmed
correct on the off-by-one: define the per-`M` `FactoredChain` with its compressed transition RECURSIVELY,
so both per-level obligations become near-definitional.

**Off-by-one (Codex-confirmed, verified).** Abstract `C k : Fin (Twid k) → Fin (Wwid k)`, `Wwid k = M k`.
The achiever descent `t_0 := M_0 ≥ t_1 ≥ … ≥ t_{L-1} ≥ t_L := 0` gives `Twid 0 = M 0`, `Twid (k+1) = t_k`.
So `Twid 0 = Twid 1 = M_0` (the FIRST boundary is the identity boundary, `c_0 = 0`); genuine rank drops
(`chain_block`, `c ≥ 1`) happen at `1 ≤ k < L`; the leaf is `C L = u·R_L : Fin (t_{L-1}) → Fin (M_L)`.

**The recursive-`C` shape (makes `hC`/`hQA` near-`rfl`):**
- `C 0 := 1` (the bridge boundary; `Twid 0 = Wwid 0 = M_0`).
- `C k := Bmat k · chainQ (N_k) + u • Rmat k`  for interior `0 < k < L`  ⟹ `hC k` is `rfl`.
- `C L := u • R`  ⟹ `base` is `rfl`.
- `A k := chainA (N_k) (W_k) (C (k+1))`  ⟹ `hQA k := chainQ_mul_chainA …` gives `chainQ·A k = C (k+1)`.
- `Bmat 0 := 1`, `Rmat 0 := 0` so `hC 0 : 1 = 1·chainQ(0:M_0×0) + u•0 = chainQ at c=0 = I_{M_0}`
  (the one non-`rfl` `hC`, a `chainQ`-at-`c=0`-is-identity fact — keep widths EXPLICIT, not `getD`/`Fin.cons`,
  or the `isDefEq` blows the heartbeat budget; the spike timed out only on `![…].getD`-shaped widths).

**Remaining work for the chart identity `prod M (φ_M u) = u • H` (the per-`M` SUPPLY):**
- (i) the achiever descent path `t : Fin (L+1) → ℕ` as a Lean object (the `Adm`/`Mval` minimiser; for a
  FIXED M it is `decide`-able, e.g. `(3,3,3,3) → (2,1,0)`; the GENERAL minimiser is `routeLayerAtlasAcc`'s
  achiever leaf, `RouteMLayerSplit.routeLayerAtlasAcc_achiever`).
- (ii) the per-slot block data `(N_k, W_k, Bmat k = P_k K_k, Rmat k)` parametrized by chart coords, with the
  widths from `t`. `r_s = t_{s-1}−t_s`, `c_s = M_s − t_s`. The LDU core `K_s` is the `(3,3,3,3)`-template's
  `Frame`/`Kparam` blocks lifted to `t_s × t_s`.
- (iii) the layer match `hA` (per-layer reindex of `chainA k` to the genuine `Params M` layer — width
  bookkeeping at the equiv level, the `reindex_finCongr_mul` kernel).
- (iv) `C 0 = 1` simplification of `suffix 0` to `u • Hmat 0`, then `prod_eq_reindex_suffix`.
- then the flat chart `φ_M := paramsEquivFlat M ∘ chartParams_M`, and `routeMCore M (φ_M u) = u²·V` exactly
  as `RouteM3333.routeMCore_phi3333` (`V := ‖reindex (Hmat 0)‖²`).

**Scope note.** The RATE identity is PATH-AGNOSTIC (Codex + telescope-theorem confirmed): any chain with
`C 0 = 1`, `step`, `base`, layer-match gives `prod = u•H`. The achiever profile is needed only DOWNSTREAM
for the Jacobian det `|u|^{minAdm−1}` (task #77) and the `½·minAdm` threshold — so the chart-identity
checkpoint can be built on the achiever widths but proves only the rate.

## CHECKPOINT REACHED — the `(3,3,3,3)` CHART IDENTITY via the engine (2026-06-26)

`RouteM3333Chain.lean` (sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`) — the decisive
multi-pivot witness built through the rate engine, reproducing `RouteM3333`'s identity WITHOUT the
per-entry `ring` blow-up:

- `chain3333 : FactoredChain 3 u` — the recursive-`C` construction (validated design): `C 0 = 1`,
  `C k = Bmat k · chainQ(N_k) + u • Rmat k` (interior, `hC` `rfl`), `C 3 = u • Rleaf` (`base` `rfl`),
  `A k = chainA(N_k)(W_k)(C(k+1))` (`hQA` = `chainQ_mul_chainA`). The identity boundary `k=0` uses
  `Qmat 0 = Bmat 0 = 1`, `Rmat 0 = 0` (so `hC 0`/`hQA 0` are `one_mul`, sidestepping `chainQ` at `c=0`);
  the genuine `chain_block` fires at `k=1` (`t=2,c=1`) and `k=2` (`t=1,c=2`). **Widths explicit ℕ-`match`**
  (`W3333`, `T3333w`), NOT `![…].getD` (the heartbeat caveat held — clean build).
- `prod_chartParams3333c_eq : prod M3333c (chartParams) = u • H` — the rate identity (bridge +
  recursive-`C 0=1` `telescope_zero`). `chartParams` = the chain's layers; `hW`/`hA` the `rfl`-3 matches
  (`hA` via `reindex_apply` + `Fin.cast_eq_self`, NOT the `finCongr_refl` `show`-rewrite which didn't fire).
- `dlnLoss_chartParams3333c : dlnLoss M3333c 0 (chartParams) = u²·V` (`V := ‖Hr‖²`, `Hr := reindex (Hmat 0)`).
- `routeMCore_phi3333c : routeMCore M3333c (φ u) = u²·V` — **the chart identity** (the soundness-critical
  `F∘φ = u²·V`), `φ := paramsEquivFlat M3333c ∘ chartParams`, the symm/apply cancel.

**Cast lessons (added to the kernel):** (i) the dependent-`HMul`/`HSMul` `rw [Matrix.one_mul]` /
`rw [Matrix.submatrix_smul]` higher-order match FAILS even fully-applied as a `rw` — use a fully-applied
TERM (`have h1 : C 0 * suffix 0 = suffix 0 := Matrix.one_mul (suffix 0)` then `rw [h1]`; `congrFun
(congrFun (Matrix.submatrix_smul u A) _) _` for the reindex-smul). (ii) `hA` (reindex of a layer to the
`rfl`-equal-width target) closes by `rw [Matrix.reindex_apply]; ext i j; simp [submatrix_apply,
finCongr_symm, finCongr_apply, Fin.cast_eq_self]; rfl`.

## The ∀M generalization (the remaining SUPPLY — well-scoped, template now concrete)

The `(3,3,3,3)` instance is the concrete template. The general ∀M version (path-AGNOSTIC rate, so
parametrize by ANY weakly-decreasing `t : Fin (L+1) → ℕ` with `t 0 = M 0`, `t last = 0`, `t k ≤ M k`):
- `Twid 0 := M 0`, `Twid (k+1) := t k`; `Wwid k := M k`. The recursion `C : (k:ℕ) → Matrix (Fin (Twid k))
  (Fin (Wwid k))` over OPAQUE `t`-widths (the `(3,3,3,3)` `match` becomes a structural recursion; the
  `chainQ`/`chainA` `t + c = M'` proofs are `omega` with `t = t k`, `c = M k − t k`).
- `chain_block`/`chainQ`/`chainA` are ALREADY M-agnostic (`{M' t c : ℕ}`), so the block algebra is free.
- The identity boundary `k=0` (`Twid 0 = Twid 1 = M 0`, `c_0 = 0`) uses `Qmat 0 = Bmat 0 = 1` as in `(3,3,3,3)`.
- The leaf `k = L` is `C L = u • R`, `base` `rfl`.
- `hW`/`hA`: `Wwid k = M ⟨k,_⟩` is `rfl` (`Wwid = M`); `hA` is the reindex-of-layer (the `(3,3,3,3)`
  `Fin.cast_eq_self` close).
- then `φ_M := paramsEquivFlat M ∘ chartParams_M`, `routeMCore M (φ_M u) = u²·V`.
The remaining genuine work is the opaque-`t`-width recursion for the chain fields (the `(3,3,3,3)` `match`
lifted to a general structural recursion). Downstream (Jacobian det / cov / atom) needs the achiever `t`
specifically (for the `minAdm−1` exponent); the rate identity does not.

## CHECKPOINT REACHED — the ∀M CHART IDENTITY (the structural lift, 2026-06-26)

The `(3,3,3,3)` `match`-defined fields lifted to arbitrary `M` + arbitrary weakly-decreasing descent `t`
(sorry-free, axiom-clean). The opaque-`t`-width recursion turned out CLEANER than feared (Codex-corroborated
`S-hybrid`; my construction is even simpler than Codex's proposed special-cased version):

- **`RouteMGenChain.lean`** — `Wext`/`Text` (ℕ-indexed `dite` width families, NOT `getD`), `GenBlk M t`
  (per-boundary block data at opaque widths), `chainOfMt : FactoredChain L u`. The fields are UNIFORM
  `dite`-guarded (`if k < L`): `C k = Bmat k · chainQ(N_k) + u • Rmat k`, `A k = chainA(N_k)(W_k)(C(k+1))`,
  leaf `C L = u • Rfin L`. `hC`/`hQA` discharged uniformly by `dif_pos` + `chainQ_mul_chainA`; `base` by
  `dif_neg`. **The identity boundary `k = 0` needs NO special-casing** — `chainQ`/`chainA` at `c_0 = 0` work
  via `chainQ_mul_chainA` directly (the engine is M-agnostic).
- **`RouteMChainBlock.lean`** (extended) — `finSplit_refl` (`finSplit (le_refl t) j = inl j`, via
  `finSumFinEquiv_symm_apply_castAdd`) + `chainQ_cZero` (`chainQ` at `c = 0` is `I`). The identity-boundary
  fact making `C 0 = 1` reachable from `Bmat 0 = 1`, `Rmat 0 = 0`.
- **`RouteMGenChartId.lean`** — `chartParamsGen` (chain layers reindexed to `M`), `hWgen`/`hAgen`,
  `prod_chartParamsGen_eq` (the ∀M rate identity, given `hC0 : C 0 · suffix = suffix`), and
  `routeMCore_phiGen : routeMCore M (φ u) = u²·V` — **the ∀M chart identity**. `hC0` is the suffix bridge's
  `C 0 = 1` requirement, carried as a hypothesis the achiever block data discharges.
- **`RouteMGenChartId3333.lean`** — `routeMCore_phiGen_3spec`: the general theorem SPECIALIZES to
  `M = (3,3,3,3)`, `t = (3,2,1,0)` (`Text = (3,3,2,1)`), discharging `hC0` via `chainQ_cZero` + the
  identity-boundary block data. Confirms the structural lift reproduces the concrete instance.

**Cast lessons (added):** (i) `hC0` (`C 0 = 1`) at the identity boundary: `chainOfMt_C_zero` + `have hQ :=
chainQ_cZero _ _` (the `exact` accepts the defeq `c = 0` that `rw` can't match) + a `show` at LITERAL
`Fin 3` types to force the width reduction, then `rw [Matrix.one_mul, smul_zero, add_zero]`. (ii)
`C 0 · suffix = suffix` from `C 0 = 1`: `rw [hC0eq]; exact Matrix.one_mul _` (do NOT write the `1 · suffix`
explicitly with a literal-`Fin` `1` — the opaque `Wwid 0` blocks the HMul; let `rw` keep the dependent type).

## What remains for the box-divergence atom ∀M (downstream of the chart identity)
The ACHIEVER `t` (the `minAdm`-realizing descent) instantiates `chainOfMt`; then the Jacobian det
`|u|^{minAdm−1}` (via `general_composed_clm_abs_det` + `leafH`), the unit `V` bound + a.e.-positivity, the
cov (`measure_biUnion_null_iff`), the `nodeChartGeneral` bundle, and the atom discharge
`routeMCore_box_diverges_achiever ∀M`. The rate identity (this checkpoint) is the soundness-critical
`F∘φ = u²·V`; the det needs the achiever `t` specifically (the rate is path-agnostic).

## Files (worktree branch)
`lean/DLNFibre/DLN/RLCT/Validate/RouteMChainFactor.lean`, `RouteMFactoredChain.lean`,
`RouteMChainRate.lean`, `RouteMChainBlock.lean`, `RouteMChainRateValid.lean`, `RouteMChainBlockValid.lean`,
`RouteM3333Chain.lean`, `RouteMGenChain.lean`, `RouteMGenChartId.lean`, `RouteMGenChartId3333.lean`.
NOT yet in the `DLNFibre.lean` aggregator (controller wires).

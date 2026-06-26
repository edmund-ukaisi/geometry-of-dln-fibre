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

## Files (worktree branch)
`lean/DLNFibre/DLN/RLCT/Validate/RouteMChainFactor.lean`, `RouteMFactoredChain.lean`,
`RouteMChainRate.lean`, `RouteMChainBlock.lean`, `RouteMChainRateValid.lean`, `RouteMChainBlockValid.lean`.
NOT yet in the `DLNFibre.lean` aggregator (controller wires).

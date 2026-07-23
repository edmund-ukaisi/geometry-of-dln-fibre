# Cap-escape — DEF-LEVEL CONFIRM (seat-L4D, against canonical tip)

**Charge (controller):** at `d = (2,3,2,2)`, does the `∃c` support-decomposition (`Deg1SupportedSlot`
conjunct-1) over `supportAt` at a DESCENDED child state fail exactly as pnp-transport's matrix trace
(banked `recoord-cap-escape-note.md` + `verify/recoord_cap_escape.py`) predicts — traced against the
BAKED defs, with the raw-`u`-vs-composed-through-shears bookkeeping explicit? **VERDICT: CONFIRMED-AT-DEF**
(not DODGED-BY-DEF-SHAPE), both write-side and residual-side.

## 0. Coordinate layout (verified against the baked defs)
`tupIdx d = ((layer i : Fin N, row : Fin d_{i.succ}), col : Fin d_{i.castSucc})` (`LearningCoefficient`
`tupIdx`/`tupIdxEquiv`; `blockEntryFlat` MonumentAtlas:832-838 reads `row < d i.succ`, `col < d i.castSucc`).
So a layer-`ℓ` flat coord has `row ∈ Fin d_{ℓ+1}`, `col ∈ Fin d_ℓ` — matrix `A_ℓ` is `d_{ℓ+1} × d_ℓ`.
`widthMinUpto M n = min(M i : i ≤ n)` (EngineDefs:154, `Finset.inf'`). For `d = ![2,3,2,2]`
(`d_0=2,d_1=3,d_2=2,d_3=2`, `N=3`): `widthMinUpto ℓ ≡ 2` (bottleneck `d_0 = 2`).
`blockCoords d ℓ = {q : (q.1.1)=ℓ ∧ (q.2) < widthMinUpto d ℓ}` (MonumentAtlas:556) — caps **col**, NOT row.

## 1. Write-side (the recoord's out-of-cap column)
`canonNormalizationOf` component (ii) (MonumentAtlas:877-882) fires at flat coord `k` when
`(q.1.1)=s.layer+1 ∧ (q.2)=(qp.1.2)` — i.e. it writes at layer `s.layer+1`, **col = the pivot's ROW
index** `qp.1.2`. `canonCenterOf` (case12/case2, MonumentAtlas:820-826) bounds the pivot ROW only from
BELOW (`cleared ≤ q.1.2`) — no `widthMinUpto` upper cap (only the COL gets `q.2 < widthMinUpto`); and
`IsRealBranch` rule (b) (MonumentAtlas:942-943) lets case12/case2 pick the pivot FREELY in `canonCenterOf`.
So a free pivot's row ∈ `[cleared, d_{s.layer+1})`, uncapped by `widthMinUpto`. Escape ⟺ pivot-row ≥
`widthMinUpto(s.layer+1)`, reachable ⟺ **`d_{s.layer+1} > widthMinUpto(s.layer+1)`** (a "wide" current layer).
(2,3,2,2): layer-0 clear, `d_1 = 3 > widthMinUpto(1) = 2`; free pivot of row 2 ⟹ recoord writes at
layer-1 col 2 ≥ `widthMinUpto(1) = 2` ⟹ OUTSIDE `blockCoords(1)`.

## 2. Residual-side, composed-through-shears (the sharpened check — CONFIRMED)
First clear off root (`ed`: case2/case12, δ=1 — parent = `conRoot`, layer 0, cleared 0), child state `ns`:
layer 0, cleared 1 ⟹ `supportLayerOf ns = 1`, and `supportAt(0,1) = blockCoords(1)` (MonumentAtlas:572,
`if 1=0` no; `if 0+1<3` yes). The out-of-cap coord `q₁₀₂` (layer 1, row 0, col 2) has col 2 ≥ 2 ⟹
`q₁₀₂ ∉ blockCoords(1)`.

`foldResid(child)` at δ=1 (MonumentAtlas:451-454) =
`coreGen[fun k ↦ blockBlowupCoordQuot(pivot, k, edgeShearRaw(cse, shearφ, u))]`.
- `blockBlowupCoordQuot p j w = if j=p then 1 else w j` (BlockDivision:30-31). `q₁₀₂ ≠ pivot` (pivot at
  layer 0) ⟹ the `k=q₁₀₂` slot passes through as `(blockShear shearφ u) q₁₀₂ = u(q₁₀₂) + shearφ(u)(q₁₀₂)`
  (`blockShear φ u = u + φ u`, PathAtoms:63). The RAW coord `u(q₁₀₂)` is present (the shear ADDS, it does
  not absorb) — plus the recoord displacement (component (ii) fires at col 2 = pivot-row when the pivot row
  is 2). So the argument slot at `q₁₀₂` reads the raw `u(q₁₀₂)`.
- `coreGen[i][j] = ∑_{a∈Fin d_2, b∈Fin d_1} A₂[i][a]·A₁[a][b]·A₀[b][j]` (`coreGen` = entries of the flat
  product, LearningCoefficient:50-53). The `b=2` term reads `A₁[·][2] = q₁₀₂` with coeff `A₂[i][0]·A₀[2][j]`
  — the wide remnant row `A₀`'s row 2 (`d_1=3`). For `(i,j)=(0,0)`: coeff `A₂[0][0]·A₀[2][0]` = pnp's
  banked witness `p₀₂₀·r₂₀₀ ≠ 0`.

⟹ `foldResid(child)` is degree-1 in `q₁₀₂ ∉ blockCoords(1)`, so `∃c` over `blockCoords(1)` (which forces
`foldResid(child)` to VANISH at `blockCoords(1) → 0`) is FALSE. **INHERENT** — the read is coreGen's
wide-remnant-row term (holds even with NO recoord; the recoord only adds on top), matching pnp's
"holds even with no recoord." seat-L3T2 confirmed the mechanism independently at the def level.

## 3. Verdict + scope
**CONFIRMED-AT-DEF, both sides.** The baked `Deg1SupportedSlot`/`FoldStepInvAt` conjunct-1 over
`supportAt = blockCoords(S+1)` at a descended state is FALSE on WIDE branches (`d_{S+1} > widthMinUpto(S+1)`)
— the 10th statement-class defect (support TOO TIGHT). The three standard N_p witnesses ((2,2,2,2),
(3,3,4), (3,3,2,2)) are non-wide (`d_{S+1} = widthMinUpto`) so never exercised it; every battery must now
carry a WIDE witness. (No full Lean kill-witness built: `#eval` is blocked by the noncomputable defs and
the real-branch `TreeEdge` construction is heavy; per the controller's "statement-truth, not a proof"
scoping the def-trace + pnp's banked numeric (re-run exit-0) + seat-L3T2's def-level agreement is decisive.)

SCOPE: this bites the DESCENDED (S+1) capped slot (case2/case12 δ=1 children) and seat-L3T2's clause-1
descent. It does NOT bite the case11 `realBranch_boostReady_case11` READ, which is same-layer (support
`blockCoords(p.layer)`, center `{reused-pivot (earlier layer)} ∪ partialBlock (p.layer)`). The b-chain
INTRODUCTION at the reused divisor's earlier DESCENDED clear IS coupled to this escape.

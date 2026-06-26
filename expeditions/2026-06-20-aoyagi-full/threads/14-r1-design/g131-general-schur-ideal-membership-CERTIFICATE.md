# General m×k reduced-node Schur ideal-membership — `flatCore − Φ ∈ ideal(E)` (pp-hall, 2026-06-22, #131)

**The last math content of the corrected per-node R1 interface (task #11).** State + certify, exact and
dimension-free, the general reduced-node ideal-membership underpinning the #129 squeeze: the lower rows of
`Â·A2` decompose via the Schur complement, giving `flatCore − Φ ∈ ideal(E)` with explicit cofactors. This
is the **existence-proof content** that produces the squeeze `c₁·Φ ≤ flatCore ≤ c₂·Φ` (crux2's datum
carries the inequality; this lemma is *why* it holds). Feeds the g128-chain per-node rlct.

## Setup (general, dimension-free)
A reduced node after one blow-up: `Â : m×k` real matrix with `Â[0,0] = 1` a **hard** constant (the
post-blow-up pivot); `A2 : k×n` real. The loss `flatCore = F = ‖Â·A2‖²_F` (= `dlnLoss M 0` at this node).
Block-partition with the pivot split off:

    Â = [[1,  a],     A2 = [[β],     a = Â[0,1:]  (1×(k−1)),   b = Â[1:,0]  ((m−1)×1),
         [b,  D]]           [Γ]]     D = Â[1:,1:] ((m−1)×(k−1)), β = A2[0,:] (1×n), Γ = A2[1:,:] ((k−1)×n).

Define:
- **Regular generators** `E_j := (Â·A2)[0,j]`, `j = 0..n−1` (the pivot **row** of the product); `E_row = (E_0,…,E_{n−1})`.
- **Schur complement** `S := D − b·a`  ((m−1)×(k−1)).
- **Reduced second factor** `A2red := Γ = A2[1:,:]`  ((k−1)×n).
- **Comparison object** `Φ := Σ_j E_j² + ‖S·A2red‖²_F`. (The E-free part `‖S·A2red‖²` is the next node's
  zero-core `dlnLoss S.red 0` — the reduced matrix-chain product.)

## The theorem (proved dimension-free)

### (1) The Schur row-decomposition — a pure block identity, all `m,k,n ≥ 1`
    Â·A2 = [[1, a],[b, D]]·[[β],[Γ]] = [[ β + a·Γ ],[ b·β + D·Γ ]],   so
      E_row  = (Â·A2)[0,:]  = β + a·Γ                         (pivot row, β has UNIT coeff — the hard 1)
      lower  = (Â·A2)[1:,:] = b·β + D·Γ.
    Substitute β = E_row − a·Γ (invert the E_row equation — legitimate because the pivot is the hard 1):
      lower = b·(E_row − a·Γ) + D·Γ = b·E_row + (D − b·a)·Γ = **b·E_row + S·A2red**.   ∎

This is the `(uᵢ,ψᵢ)` adapted-basis / `L·A·R = blockdiag[1, D−ba]` content of #127, now read **not** as a
loss-value identity (which is false, #129) but as the **row decomposition** of the product matrix. The only
structural input is the hard pivot `Â[0,0]=1` (it lets `β` be solved for from `E_row` with unit coefficient).
Verified block-generically (`g131-scripts/g131_blockproof.py`, 4 block-dim instances) and on 6 full shapes
(`g131_general_ideal.py`: `(3,3,3),(4,3,2),(2,4,3),(3,2,2),(5,4,3),(2,2,1)` — square, tall, wide, minimal,
larger, single-column — all HOLD).

### (2) The ideal-membership with EXPLICIT cofactors
Since `F = ‖(Â·A2)[0,:]‖² + ‖lower‖² = Σ_j E_j² + ‖lower‖²` (row split) and `Φ = Σ_j E_j² + ‖S·A2red‖²`:

    F − Φ = ‖lower‖² − ‖S·A2red‖².

Substituting (1), `lower[i,j] = b_i·E_j + (S·A2red)[i,j]`, so

    F − Φ = Σ_{i,j} [ (b_i E_j)² + 2 b_i E_j (S·A2red)[i,j] ]
          = **Σ_j E_j · g_j**,   with   **g_j := Σ_i b_i·( b_i·E_j + 2·(S·A2red)[i,j] )**.

Every term carries a factor `E_j`, so **`F − Φ ∈ ideal(E_0,…,E_{n−1})`** — verified exact:
`F − Φ − Σ_j E_j·g_j = 0` (`g131_general_ideal.py`/`g131_blockproof.py`). The cofactors `g_j` are explicit
polynomials in the node's coordinates (`b_i = Â[1:,0]` the pivot column, `S·A2red` the reduced product).
Equivalently, the bare ideal-membership `(F − Φ)│{E=0} = 0` holds on all 6 shapes.

## The squeeze it produces (the bridge to the datum)
The perturbation `lower − S·A2red = b·E_row` is **linear in `E`** with coefficients = entries of `b = Â[1:,0]`
(bounded, → 0 at the deepest point). Hence near 0:

    F = Σ_j E_j² + ‖S·A2red + b·E_row‖²   is a bounded-linear-perturbation of   Φ = Σ_j E_j² + ‖S·A2red‖²,

so `∃ c₁,c₂ > 0 : c₁·Φ ≤ F ≤ c₂·Φ` near 0. Two structural facts make this **not** merely numerical:
- **Same zero-set:** `{F = 0} = {Â·A2 = 0} = {E = 0 ∧ lower = 0}`; on `{E=0}`, `lower = S·A2red` (from (1)),
  so `{F=0} = {E=0 ∧ S·A2red=0} = {Φ=0}`. Both `rlctAt_mono` legs are valid (`F=0 ⟺ Φ=0`).
- **Lower bound `c₁ > 0` is structural:** `F ≥ 0`, and the worst direction (lower block cancelled,
  `S·A2red = −b·E_row` ⟹ `lower = 0`) gives `F/Φ = ΣE²/(ΣE² + ‖b·E_row‖²) = 1/(1+‖b‖²) → 1` as `b → 0` (a
  coordinate → 0 at the deepest point). So `inf F/Φ → 1` on shrinking balls, bounded below by
  `1/(1+sup‖b‖²) > 0`. Numerics confirm `F/Φ → 1` (e.g. (3,3,3): `[0.707,1.474]` at scale 0.3 →
  `[0.999,1.000]` at 0.003; `g131_lowerbound.py`).

## Edge / terminator cases (the recursion boundary)
- **`m = 1`** (single-row `Â`, no lower rows): `lower` is `0×n`, `F = Σ_j E_j²` exactly (pure regular
  block), `Φ = Σ_j E_j²` (empty Schur core). `F − Φ = 0` — the **recursion terminator** (`dlnLoss_one_layer_deepest`
  pattern: all-smooth, nothing to pivot). Verified `(1,3,2),(1,1,4)`.
- **`k = 1`** (single-column inner, `Â = [[1],[b]]`): `a` is `1×0` (empty), `S = D` is `(m−1)×0` (empty),
  `‖S·A2red‖² = 0`, `lower = b·β` (rank-1 outer product). `F − Φ = Σ_{i,j} b_i² β_j² = (Σ_i b_i²)·Σ_j E_j²
  ∈ ideal(E)`. Verified `(3,1,2)`: `(F−Φ)│{E=0} = 0`.
- **`n = 1`** (single-column target): `E` is a single generator `E_0`; identity unchanged. Verified `(2,2,1)`.

## Net for crux2's interface (the existence-proof content)
The corrected per-node R1 interface, with the levels kept separate:
- **Datum (what `schur_recursion_step_squeeze` consumes):** the squeeze inequality `c₁·Φ ≤ flatCore ≤ c₂·Φ`
  (`c₁,c₂ > 0`) at the deepest-point basepoint, `Φ = (Σ_j E_j²) + dlnLoss S.red 0 (…)`. [crux2's 4 fields,
  confirmed faithful.]
- **Existence-proof content (THIS cert):** the squeeze exists because `flatCore − Φ = Σ_j E_j · g_j ∈
  ideal(E)` (explicit cofactors `g_j = Σ_i b_i(b_i E_j + 2(S·A2red)[i,j])`), via the dimension-free Schur
  row-decomposition `lower = b·E_row + S·A2red`, with same-zero-set `{F=0}={Φ=0}` and structural `c₁>0`.
- **Reduced core:** `‖S·A2red‖² = dlnLoss S.red 0` is the next node's loss — `S` an `(m−1)×(k−1)` Schur
  factor, `A2red` restricted to the matching `(k−1)` rows. `ΣM` strictly drops (the pivot row+col are
  resolved), closing the recursion (#127 field-6, #123).

The Schur complement `S = D − b·a` is the **only** mechanism (a single hard-pivot elimination); the ideal-
membership and the squeeze follow from the one block identity (1). No constant rank, no measure Jacobian,
no clean-MP factor.

## Most likely thing to break this
The block identity (1) needs the pivot to be a **genuine unit** to invert `β = E_row − a·Γ`. With the hard
`1` (post-blow-up) this is exact (coefficient literally 1). If a downstream node's pivot were only a unit
`≈1` (not exactly 1), `β`'s coefficient would be that unit `w`, and the decomposition would read
`lower = b·E_row + S·A2red` with `S`, `E_row` carrying `w`-factors — still an ideal-membership, but the
`g_j` cofactors and `c₁,c₂` would pick up the unit. The hard-1 interface (#127, every blow-up chart
normalizes its pivot coordinate to exactly 1) is what keeps (1) clean — confirming blow-up-first is the
correct order.

## Next
crux2 consumes this as the construction lemma behind the squeeze field; the Lean statement is the
matrix-level `(Â·A2)[1:,:] = Â[1:,0]·(Â·A2)[0,:] + (Â[1:,1:] − Â[1:,0]·Â[0,1:])·A2[1:,:]` (a `Matrix`
identity, provable by `Matrix.mul`/block algebra in Mathlib) ⟹ `F − Φ ∈ Ideal.span {E_j}` ⟹ the squeeze.
Decorrelation: pp-hall exact (4 scripts `g131-...`, dimension-free block proof + 6 shapes + edges + the
structural lower bound). The Codex leg is the one unavailable in #129/#130 (CLI hangs on a cargo rebuild,
not auth) — re-run when reachable as belt-and-suspenders (not blocking; the block identity (1) is a
one-line algebra check anyone can re-verify).

Builds on #129 (squeeze verdict — this is its existence content), #130 (fidelity fields), #127 (the
block/`L·A·R` content, now read as a row decomposition not a value identity). Scripts: `g131_general_ideal.py`,
`g131_blockproof.py`, `g131_edges.py`, `g131_lowerbound.py` (all in `g129-scripts/`).

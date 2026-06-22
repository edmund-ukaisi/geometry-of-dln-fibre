# Statement card — (3) MP-of-transvection (the det-1 Schur straighten is measure-preserving)

- **Status:** `sorry-free` (awaiting fidelity review). Branch `origin/fm2/mp-transvection` @f1dbdbd
  (Lean @0749d27), single clean commit on consolidate base @d82b381. File
  `lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean`.
- **Seat:** fm2 (formaliser, crux lane). Build GREEN (2675 jobs, 0 sorry in file). All three decls axiom
  clean-three `[propext, Classical.choice, Quot.sound]`.
- **Gate-independence:** reusable bedrock for the chart-existence lane, INDEPENDENT of the disputed
  chart-existence FORM (clean-MP-c-o-v vs two-sided squeeze, held for pp2 2b). It states the (A)-lane fact
  that the det-1 straightening carries NO Jacobian weight, whatever form the chart takes.

## The three lemmas

```text
mp_mulVec_of_det_one {ι} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : M.det = 1) :
    MeasurePreserving (fun v : ι → ℝ => M *ᵥ v) volume volume

mp_schur_transvection_vec {ρ κ} [Fintype ρ] [Fintype κ] [DecidableEq ρ] [DecidableEq κ]
    (L : Matrix ρ ρ ℝ) (R : Matrix κ κ ℝ) (hL : L.det = 1) (hR : R.det = 1) :
    MeasurePreserving (fun v : (κ × ρ) → ℝ => (Rᵀ ⊗ₖ L) *ᵥ v) volume volume

vec_schur_transvection {ρ κ} [Fintype ρ] [Fintype κ]
    (L : Matrix ρ ρ ℝ) (R : Matrix κ κ ℝ) (A : Matrix ρ κ ℝ) :
    Matrix.vec (L * A * R) = (Rᵀ ⊗ₖ L) *ᵥ Matrix.vec A
```

## English gloss

The det-1 two-sided Schur straightening `A ↦ L · A · R` (with `L, R` the unipotent block transvections of
`hardPivot_schur_blockId`) is measure-preserving for Lebesgue volume. In vectorized coordinates the map is
`v ↦ (Rᵀ ⊗ₖ L) *ᵥ v` (`vec_schur_transvection`), the big matrix has determinant
`det L^|κ| · det R^|ρ| = 1`, and a det-1 matrix action preserves volume. So the (A)-lane straightening
contributes no Jacobian weight — the monomial comes only from fm's (B) blow-up.

## Route (Codex g129, decorrelated)

Route B1 (Kronecker-det) chosen over Route A (per-entry shear composition via `measurePreserving_shearAt`):
Codex ranked B1 cheapest because the vec identity is a Mathlib FACT (`kronecker_mulVec_vec`) not a new
proof, and the det lift is `det_kronecker` + `simp` — avoiding the Fin-indexing friction that the shear
route's flattening/order bookkeeping would impose. Artefact
`threads/14-r1-design/codex/g129-mp-transvection-route-{prompt,answer}.md`.

Mathlib lemmas used (all verified present in v4.29):
- `Real.map_matrix_volume_pi_eq_smul_volume_pi` (Lebesgue/Basic.lean:411) — `det≠0 ⟹` volume scales by `|det|⁻¹`.
- `Matrix.det_kronecker` (Kronecker.lean:383), `Matrix.det_transpose`.
- `Matrix.kronecker_mulVec_vec` (Vec.lean:136): `(B ⊗ₖ A) *ᵥ vec X = vec (A * X * Bᵀ)`.
- `Matrix.toLin'`, `ContinuousLinearMap`-free measurability via `continuous_of_finiteDimensional`.

## Honest scope / what is NOT here

- Stated on the **vectorized** parameter space `(κ × ρ) → ℝ` (which carries `volume`; the `Matrix ρ κ ℝ`
  wrapper does NOT have a `MeasureSpace` instance). The `vec`-transport identity bridges to the matrix-level
  straightening `A ↦ L·A·R`.
- This is the MEASURE fact only. WIRING it into the chart `χ` of `schur_straighten_of_data` (composing the
  vec equiv + the reduced-coordinate split + the residual factorisation `hfactor`) is the held
  chart-existence lane, pending pp2's 2b verdict on the FORM. (3) supplies the MP ingredient that lane needs.

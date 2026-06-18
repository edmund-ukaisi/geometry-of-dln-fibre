---
title: "Thread 09 — G_d base-change action + rank-pattern invariance (rung 4c)"
status: sorry-free
topics: [base-change, G_d-action, telescoping-conjugation, rank-invariance, rung-4]
created: "2026-06-12"
updated: "2026-06-12"
---

# Thread 09 — `G_d` base change, telescoping conjugation, rank-pattern invariance (rung 4c)

Module: `lean/DLNFibre/Core/BaseChange.lean` (namespace `DLNFibre.Core`), network-free, ~180 lines;
imports `DLNFibre.Core.Submult` only. **All parts landed**, green + sorry-free (committed `720d298`).
Started from a non-building draft already on the branch (the `↑`/ascription coercion spellings did not
elaborate — see Friction); fixed to a clean build.

## Landed

1. **The group `G_d = ∏_v GL_{d_v}`** — `BaseChangeGroup d := ∀ v : Fin (N+1), (Matrix (Fin (d v)) (Fin (d v)) k)ˣ`
   (units of the square matrix ring = `GL`). It is a `Group` for free via the Pi/`Units` instances.

2. **The action** — `baseChange P A : Tuple d`, `(baseChange P A) i = P_{i+1} · A_i · P_i⁻¹` with the
   target-vertex unit `P i.succ` on the left and the source-vertex unit inverse `(P i.castSucc)⁻¹` on
   the right (index orientation verified against `Submult`/`submult_succ`). Registered as a
   `MulAction (BaseChangeGroup d) (Tuple d)` (`smul := baseChange`, `one_smul = baseChange_one`,
   `mul_smul = baseChange_mul`), so `P • A` is available and `smul_eq_baseChange : P • A = baseChange P A`
   is definitional.

3. **Telescoping conjugation** (the engine of 4c) — `submult_baseChange` /
   `submult_smul`:
   `submult d (P • A) i j hij = Units.val (P j) · submult d A i j hij · Units.val ((P i)⁻¹)`.
   Proof: `Fin.induction` on the upper index `j` (after `revert hij`), mirroring `submult_succ`.
   - base `j = i` (zero case `i = 0` via `Fin.le_zero_iff`; diagonal case `i = p.succ` via the
     `eq_or_lt_of_le` split): empty sub-product `= 1`, boundary units cancel `P_x · 1 · P_x⁻¹ = 1`
     (`submult_self`, `Matrix.mul_one`, `Units.mul_inv`).
   - active edge `i ≤ p.castSucc` (from `Fin.le_castSucc_iff.mpr` on `i < p.succ`): peel the top factor
     with `submult_succ`, apply the IH, and the inner pair `P_{p.castSucc}⁻¹ · P_{p.castSucc} = 1`
     cancels (`Units.inv_mul`) after right-associating with `Matrix.mul_assoc`.

4. **Rank-pattern base-change invariance** (the headline) — `rankPattern_baseChange` /
   `rankPattern_smul`: `rankPattern d (P • A) i j hij = rankPattern d A i j hij`. From the conjugation,
   `(P_j · C · P_i⁻¹).rank = C.rank` because each boundary factor is a unit matrix: a one-liner via
   `Matrix.rank_mul_eq_left_of_isUnit_det` (drop the right unit) and `…_right_…` (drop the left unit),
   discharging `IsUnit (↑u).det` with `Matrix.isUnits_det_units`.

## Levers used (verbatim, v4.29)

- `Matrix.rank_mul_eq_left_of_isUnit_det (A : Matrix n n R)(B : Matrix m n R)(hA : IsUnit A.det) : (B*A).rank = B.rank`
- `Matrix.rank_mul_eq_right_of_isUnit_det (A : Matrix m m R)(B : Matrix m n R)(hA : IsUnit A.det) : (A*B).rank = B.rank`
  — **both in the `CommRing` section** of `LinearAlgebra/Matrix/Rank.lean`; need only `Fintype`/`DecidableEq`
  on the `Fin (d·)` index types, which are automatic. **No `Field`.**
- `Matrix.isUnits_det_units (A : (Matrix n n α)ˣ) : IsUnit (↑A).det` (`@[simp]`) — discharges the unit-det side goals.
- `Matrix.isUnit_iff_isUnit_det`, `Matrix.rank_of_isUnit` (witness only; `Nontrivial`).
- `Units.inv_mul`, `Units.mul_inv`, `Units.val_one`, `Units.val_mul`, `inv_one`, `_root_.mul_inv_rev`.
- `Fin.le_zero_iff`, `Fin.le_castSucc_iff : i ≤ j.castSucc ↔ i < j.succ`, `eq_or_lt_of_le`.
- `Matrix.mul_assoc`, `Matrix.one_mul`, `Matrix.mul_one`.

## Typeclass

**`CommRing k` throughout** — the two rank levers are `CommRing` (not `Field`). The non-vacuity witness
additionally uses `Nontrivial ℤ` (only via `Matrix.rank_of_isUnit`). This is a *weaker* hypothesis than
the 4b block-rank-additivity lever (`Field`); 4c is field-free.

## Witness (non-vacuity)

Conjugate the landed `(2,2,2)` `Setup.tupleWitness` by the `GL₂(ℤ)` element `witnessUnit = !![1,1;0,1]`
(determinant `1`, explicit inverse `!![1,-1;0,1]` so the unit is **computable**, `val*inv = inv*val = 1`
by `decide`) at every vertex (`witnessBaseChange`). Two `example`s: the headline applies to this genuine
non-identity base change for all `(i,j)`; and `r_{02} = rank(A₂A₁) = 2` is preserved by the conjugation
(reduced to the existing full-rank computation via `exact`, defeq-tolerant because `dWitness 2 ≡ 2`).

## Build / audit

`lake build DLNFibre.Core.BaseChange` green (1790 jobs); `scripts/sorries` → 0 sorry / 0 #exit / 0
native_decide / 0 axiom; `#print axioms` on `submult_baseChange`, `rankPattern_baseChange`, `witnessUnit`
→ only `[propext, Classical.choice, Quot.sound]`. **Not wired into the aggregator `DLNFibre.lean`** (per
brief — controller merges + wires). Did not edit any other committed module.

## Scope / precision

Orbit-side input to **Prop 3.1b ONLY**: the rank pattern is a base-change invariant (constant on
`G_d`-orbits). This is *not* the completeness direction — it does **not** claim the rank pattern is a
*complete* invariant (that two tuples with equal rank pattern are in the same orbit), which is rung 4d
(barcode-basis existence). Nothing here is named as if it asserted completeness or the Gabriel decomposition.

## Friction (for the next session)

- **Coercion spelling matters.** `↑(P j) * X` fails `HMul` synthesis in statement position (the coercion
  target is not forced through heterogeneous `*`), and `((P i)⁻¹ : Matrix ..)` parses as `(↑(P i))⁻¹`
  (the **matrix** nonsingular inverse), not `↑((P i)⁻¹)` (the coerced **unit** inverse) — so the rank
  levers and `Units.inv_mul` no longer match. Use **`Units.val (P j)`** and **`Units.val ((P i)⁻¹)`**
  explicitly. (In the `def` body the `↑` form *looks* fine because the return type forces it, but it does
  not elaborate either — the prior committed draft did not build.)
- `mul_inv_rev` is ambiguous (`_root_` group vs `Matrix`); the unit-group one (`_root_.mul_inv_rev`) is wanted.
- Witness defeq: `submult … = !![…]`'s RHS lives at type `Matrix (Fin (dWitness 2)) (Fin (dWitness 0)) ℤ`,
  defeq but not syntactically `Matrix (Fin 2) (Fin 2) ℤ` — finish with `exact`, not `rw [rank_of_isUnit]`.

---

## Statement cards (draft, for the rung-4 review)

> **Claim (telescoping conjugation).** For `P : G_d` and `A : Tuple d`, the interval sub-product of the
> base-changed tuple is the sub-product conjugated by the two boundary units.
>
> - **Lean:** `DLNFibre.Core.submult_baseChange` (and `submult_smul`, the `•` form)
>   (`lean/DLNFibre/Core/BaseChange.lean` @ `720d298`)
> - **Gloss.** `submult d (P • A) i j hij = Units.val (P j) * submult d A i j hij * Units.val ((P i)⁻¹)`
>   — the sub-product `A_j⋯A_{i+1}` of `P • A` equals `P_j · (A_j⋯A_{i+1}) · P_i⁻¹`.
> - **Proved.** The identity, for every `0 ≤ i ≤ j ≤ N`, over any `CommRing k`, by induction on `j`.
> - **Assumed.** none beyond `CommRing k` and `i ≤ j`.
> - **Cited.** none (only Mathlib matrix-algebra and `Units` lemmas).
> - **Deferred.** none.
> - **Status.** sorry-free.

> **Claim (rank-pattern base-change invariance).** The rank pattern `r_{ij}` is invariant under the
> `G_d` base-change action — it is constant on `G_d`-orbits.
>
> - **Lean:** `DLNFibre.Core.rankPattern_baseChange` (and `rankPattern_smul`, the `•` form)
>   (`lean/DLNFibre/Core/BaseChange.lean` @ `720d298`)
> - **Gloss.** `rankPattern d (P • A) i j hij = rankPattern d A i j hij` for all `i ≤ j`.
> - **Proved.** The equality, for every `0 ≤ i ≤ j ≤ N`, over any `CommRing k`.
> - **Assumed.** none beyond `CommRing k` and `i ≤ j`.
> - **Cited.** rank-invariance under multiplication by a unit matrix
>   (`Matrix.rank_mul_eq_left_of_isUnit_det` / `…_right_…`, Mathlib).
> - **Deferred.** **Completeness** of the invariant (rank pattern determines the orbit) is rung 4d, NOT
>   established here.
> - **Status.** sorry-free.

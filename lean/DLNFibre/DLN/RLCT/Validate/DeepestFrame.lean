import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.Core.Matrix.RankNormalForm

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestFrame` — the per-layer gauge frame at the deepest point

The gauge frame `(P_s, Q_s)` cobuild-sub34's `gaugeDecode` applies to put the deepest point at the
block-normal form `(X_s, Y_s, Z_s, T_s) = 0` (shape (ii), g164 verified). For each layer `s`, constant
invertible `P_s : H_s × H_s`, `Q_s : H_{s+1} × H_{s+1}` with
`P_s · (deepestPoint s) · Q_s = blockdiag[I_r, 0]`.

**The frame derives from the RANK property, not the construction.** `deepestPoint` is a
`Classical.choice` witness (`deepestPoint = (Classical.choice deepestPoint_exists).1`), so the frame
cannot be read off the internal `wLayers` construction (choice-opaque). But `deepestPoint_isDeep` gives
`(deepestPoint s).rank = r` for every layer (the `IsDeepLayers` rank-exactly-`r` clause), and a rank-`r`
matrix ALWAYS admits a rank-normal-form frame (`rank_normal_form_exists`, the generic version of the
DLN `block_elimination`). So the per-layer frame is the rank-normal-form of each layer — a clean
consequence of the deepest point being rank-exactly-`r` per layer, needing nothing from the witness.

The block-normal RHS is the `corM`-shape `fun i j => if i = j ∧ i < r then 1 else 0` (= `blockdiag[I_r,
0]`), matching `block_elimination` / `rank_normal_form_exists` verbatim so it composes with the chart.
The interior frames are trivial (interior deepest layers are already block-normal), only the two
boundary frames carry the `block_elimination` units — but `deepestPoint_frame_exists` states the
uniform per-layer existence (the rank-normal-form holds at every layer regardless), which is what
`gaugeDecode` consumes.
-/

open Matrix
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The per-layer gauge frame at the deepest point** (#77, shape (ii)). For each layer `s`, constant
invertible `P_s, Q_s` carry the deepest layer to the block-normal form `blockdiag[I_r, 0]`:
`P_s · (deepestPoint s) · Q_s = (fun i j => if i = j ∧ i < r then 1 else 0)`. The frame `gaugeDecode`
applies to read the gauge slots `(X_s, Y_s, Z_s, T_s)` (all `0` at the deepest point). Proven from
`(deepestPoint s).rank = r` (`deepestPoint_isDeep`) via the generic rank-normal-form
`rank_normal_form_exists` — NOT from the choice-opaque `wLayers` witness. -/
theorem deepestPoint_frame_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ∀ s : Fin L,
      ∃ (P : Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
        (Q : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ),
        IsUnit P ∧ IsUnit Q ∧
          P * (deepestPoint H r B hB hr hL s) * Q
            = Matrix.of (fun (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) =>
                if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) := by
  intro s
  have hrank : (deepestPoint H r B hB hr hL s).rank = r :=
    (deepestPoint_isDeep H r B hB hr hL).2.1 s
  exact Core.Matrix.rank_normal_form_exists (deepestPoint H r B hB hr hL s) hrank

/-- **Interior layers ARE the block-normal corner** (#95, the (iii) fix). On every strict-interior
layer (`0 < s ∧ s+1 < L`), the constructed deepest point equals the corner block `diag(I_r, 0)`
verbatim — the strengthened `IsDeepLayers.2.2.1`, carried through `Classical.choice` by
`deepestPoint_isDeep`. This is sharper than `deepestPoint_frame_exists` on the interior: there the
frame `(P_s, Q_s)` is a generic rank-normal-form, here `deepestPoint s` is ALREADY the corner, so the
interior frame is the IDENTITY (`deepestPoint_interior_frame_id`). -/
theorem deepestPoint_interior_eq_corM (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ∀ s : Fin L, 0 < (s : ℕ) → (s : ℕ) + 1 < L →
      deepestPoint H r B hB hr hL s
        = Matrix.of (fun (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) =>
            if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) :=
  (deepestPoint_isDeep H r B hB hr hL).2.2.1

/-- **The interior gauge frame is the identity** (#95). On every strict-interior layer, the trivial
frame `P = Q = 1` carries the deepest layer to the block-normal corner — because the layer IS the
corner (`deepestPoint_interior_eq_corM`). So in the framed product `∏ Aˢ`, the interior frames cancel
to identity and only the two boundary frames carry `block_elimination`'s units (light-(iii)
telescoping). The uniform existential `deepestPoint_frame_exists` still holds; this names the interior
witness explicitly. -/
theorem deepestPoint_interior_frame_id (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ∀ s : Fin L, 0 < (s : ℕ) → (s : ℕ) + 1 < L →
      (1 : Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
          * (deepestPoint H r B hB hr hL s)
          * (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
        = Matrix.of (fun (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) =>
            if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) := by
  intro s hpos hlt
  rw [Matrix.one_mul, Matrix.mul_one]
  exact deepestPoint_interior_eq_corM H r B hB hr hL s hpos hlt

/-- **Layer-0 RIGHT-frame = I** (#95, condition (I), `L ≥ 2`). The deepest point's layer 0 has its
last `H_1 − r` columns zero (`IsDeepLayers.2.2.2.1`): so layer 0's gauge frame fixes the RIGHT side
(`Q_0 = I`), and in the framed product only `P_0` survives on the left boundary. -/
theorem deepestPoint_layer0_cols_vanish (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ∀ s : Fin L, 2 ≤ L → (s : ℕ) = 0 → ∀ (i : Fin (H s.castSucc)) (j : Fin (H s.succ)),
      r ≤ (j : ℕ) → deepestPoint H r B hB hr hL s i j = 0 :=
  (deepestPoint_isDeep H r B hB hr hL).2.2.2.1

/-- **Layer-(L−1) LEFT-frame = I** (#95, condition (I), `L ≥ 2`). The deepest point's layer `L−1` has
its last `H_{L−1} − r` rows zero (`IsDeepLayers.2.2.2.2`): so layer `L−1`'s gauge frame fixes the LEFT
side (`P_{L−1} = I`), and only `Q_{L−1}` survives on the right boundary. Together with
`deepestPoint_layer0_cols_vanish` + `deepestPoint_interior_eq_corM`, the framed product is
`∏ Aˢ = P_0⁻¹ · (∏ corM) · Q_{L−1}⁻¹` — only the two endpoint frames. -/
theorem deepestPoint_layerLast_rows_vanish (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ∀ s : Fin L, 2 ≤ L → (s : ℕ) + 1 = L → ∀ (i : Fin (H s.castSucc)) (j : Fin (H s.succ)),
      r ≤ (i : ℕ) → deepestPoint H r B hB hr hL s i j = 0 :=
  (deepestPoint_isDeep H r B hB hr hL).2.2.2.2

/-! ## The frame as DATA (function form, for `gaugeDecode`)

`deepestPoint_frame_exists` states `∃ P Q, …` per layer; `gaugeDecode` needs the frame as a *definable
function* to build a continuous map and prove its basepoint. `deepestPoint_frame` extracts the
`(P_s, Q_s)` pair via `Classical.choose`; `_normal` / `_invertible` are the two projections. The frame
is CONSTANT (evaluated at the fixed deepest point, independent of the chart point `w`), so it has a unit
constant Jacobian — `gaugeDecode = roleSplit ∘ frame ∘ (split.symm − deepestFlat)` is a unit-Jac map. -/

/-- **The per-layer gauge frame at the deepest point, as a function** (the `(P_s, Q_s)` pair).
`Classical.choose` of `deepestPoint_frame_exists`. Constant in the chart point. -/
noncomputable def deepestPoint_frame (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) :
    Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ
      × Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ :=
  (Classical.choose (deepestPoint_frame_exists H r B hB hr hL s),
    Classical.choose (Classical.choose_spec (deepestPoint_frame_exists H r B hB hr hL s)))

/-- `(P_s, Q_s)` carry the deepest layer to the block-normal corner: `P_s·(deepestPoint s)·Q_s = corM`. -/
theorem deepestPoint_frame_normal (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) :
    (deepestPoint_frame H r B hB hr hL s).1 * (deepestPoint H r B hB hr hL s)
        * (deepestPoint_frame H r B hB hr hL s).2
      = Matrix.of (fun (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) =>
          if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) :=
  (Classical.choose_spec (Classical.choose_spec (deepestPoint_frame_exists H r B hB hr hL s))).2.2

/-- Both frame units `P_s, Q_s` are invertible (`IsUnit`). -/
theorem deepestPoint_frame_invertible (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) :
    IsUnit (deepestPoint_frame H r B hB hr hL s).1
      ∧ IsUnit (deepestPoint_frame H r B hB hr hL s).2 := by
  have h := Classical.choose_spec (Classical.choose_spec (deepestPoint_frame_exists H r B hB hr hL s))
  exact ⟨h.1, h.2.1⟩

end DLNFibre.DLN.RLCT

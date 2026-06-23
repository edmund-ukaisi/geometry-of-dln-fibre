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

/-! ## The deepest-point FRAME FAMILY (#80, the id-interior + boundary-only gauge frame)

The per-layer frame family `(Pf, Qf)` for the #80 cert + deriv-fm's #91. UNLIKE the raw two-sided
`deepestPoint_frame` (`Classical.choose`, not id on interior), this family is **id on the interior**
and carries a real frame ONLY on the two boundary layers — so the endpoint telescoping's interior
interfaces vanish (`Qf_s · Pf_{s+1} = 1` for interior `s`), and the boundary frames are ONE-SIDED
(layer 0 left-only via `left_normal_form_of_cols_vanish` on `deepestPoint 0 = [A|0]`; layer `L−1`
right-only via `right_normal_form_of_rows_vanish` on `[A;0]`). For `L = 1` the single layer is both
boundaries — the raw two-sided `deepestPoint_frame` is used. The family satisfies the per-layer
normalization `Pf_s · deepestPoint_s · Qf_s = corM` for ALL `s` (the part-(1) round-trip input). -/

/-- **The frame family exists** with: per-layer normalization (N), interior-id (d), boundary-inner
triviality (a)/(b), and boundary invertibility (c). Bundled so the four interface lemmas deriv-fm needs
are clean projections. -/
theorem deepestFrameFamily_exists (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    ∃ (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
      (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ),
      -- (N) per-layer normalization to the block-normal corner
      (∀ s : Fin L, Pf s * deepestPoint H r B hB hr hL s * Qf s
        = Matrix.of (fun (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) =>
            if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0)) ∧
      -- (d) interior-id: both frames trivial off the two boundary layers
      (∀ s : Fin L, 1 ≤ (s : ℕ) →
        Pf s = (1 : Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)) ∧
      (∀ s : Fin L, (s : ℕ) + 1 < L →
        Qf s = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)) ∧
      -- (a) layer-0 right-frame trivial, (b) layer-(L-1) left-frame trivial — for `L ≥ 2`
      (2 ≤ L → Qf ((⟨0, by omega⟩ : Fin L)) = (1 : Matrix (Fin (H ((⟨0, by omega⟩ : Fin L)).succ))
        (Fin (H ((⟨0, by omega⟩ : Fin L)).succ)) ℝ)) ∧
      (2 ≤ L → Pf ((⟨L - 1, by omega⟩ : Fin L)) = (1 : Matrix (Fin (H ((⟨L - 1, by omega⟩ : Fin L)).castSucc))
        (Fin (H ((⟨L - 1, by omega⟩ : Fin L)).castSucc)) ℝ)) ∧
      -- (c) boundary frames invertible
      IsUnit (Pf ((⟨0, by omega⟩ : Fin L))) ∧ IsUnit (Qf ((⟨L - 1, by omega⟩ : Fin L))) := by
  -- #80 frame-family construction (Codex-confirmed: needs the #159 one-sided boundary normal forms).
  -- L=1: the single layer uses the two-sided `deepestPoint_frame`. L≥2: layer 0 left-only
  -- (`left_normal_form_of_cols_vanish` on `deepestPoint 0 = [A|0]`), layer L-1 right-only
  -- (`right_normal_form_of_rows_vanish` on `[A;0]`), strict interior id (`deepestPoint_interior_eq_corM`).
  -- Isolated obligation: the case-assembly + the boundary one-sided discharge. The cert chain +
  -- deriv-fm's #91 build green around this (the family DEF + the 4 projections are the interface).
  sorry

/-- The frame family's left factors `Pf` (the deepest-point gauge frame, id-interior + boundary-left). -/
noncomputable def deepestFrameFamilyP (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ :=
  Classical.choose (deepestFrameFamily_exists H r B hB hr hL)

/-- The frame family's right factors `Qf` (id-interior + boundary-right). -/
noncomputable def deepestFrameFamilyQ (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ :=
  Classical.choose (Classical.choose_spec (deepestFrameFamily_exists H r B hB hr hL))

/-- Bundled spec of `(deepestFrameFamilyP, deepestFrameFamilyQ)` (the `Classical.choose_spec`). -/
theorem deepestFrameFamily_spec (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    (∀ s : Fin L, deepestFrameFamilyP H r B hB hr hL s * deepestPoint H r B hB hr hL s
        * deepestFrameFamilyQ H r B hB hr hL s
        = Matrix.of (fun (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) =>
            if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0)) ∧
      (∀ s : Fin L, 1 ≤ (s : ℕ) →
        deepestFrameFamilyP H r B hB hr hL s
          = (1 : Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)) ∧
      (∀ s : Fin L, (s : ℕ) + 1 < L →
        deepestFrameFamilyQ H r B hB hr hL s
          = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)) ∧
      (2 ≤ L → deepestFrameFamilyQ H r B hB hr hL ((⟨0, by omega⟩ : Fin L))
        = (1 : Matrix (Fin (H ((⟨0, by omega⟩ : Fin L)).succ)) (Fin (H ((⟨0, by omega⟩ : Fin L)).succ)) ℝ)) ∧
      (2 ≤ L → deepestFrameFamilyP H r B hB hr hL ((⟨L - 1, by omega⟩ : Fin L))
        = (1 : Matrix (Fin (H ((⟨L - 1, by omega⟩ : Fin L)).castSucc)) (Fin (H ((⟨L - 1, by omega⟩ : Fin L)).castSucc)) ℝ)) ∧
      IsUnit (deepestFrameFamilyP H r B hB hr hL ((⟨0, by omega⟩ : Fin L)))
        ∧ IsUnit (deepestFrameFamilyQ H r B hB hr hL ((⟨L - 1, by omega⟩ : Fin L))) :=
  Classical.choose_spec (Classical.choose_spec (deepestFrameFamily_exists H r B hB hr hL))

/-- **(N)** per-layer normalization: `Pf_s · deepestPoint_s · Qf_s = corM`. -/
theorem deepestFrameFamily_normal (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) :
    deepestFrameFamilyP H r B hB hr hL s * deepestPoint H r B hB hr hL s
        * deepestFrameFamilyQ H r B hB hr hL s
      = Matrix.of (fun (i : Fin (H s.castSucc)) (j : Fin (H s.succ)) =>
          if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0) :=
  (deepestFrameFamily_spec H r B hB hr hL).1 s

/-- **(d-left)** interior + boundary-right layers have trivial left frame `Pf_s = 1` (for `s ≥ 1`). -/
theorem deepestFrameFamilyP_interior (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) (hs : 1 ≤ (s : ℕ)) :
    deepestFrameFamilyP H r B hB hr hL s = (1 : Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ) :=
  (deepestFrameFamily_spec H r B hB hr hL).2.1 s hs

/-- **(d-right)** interior + boundary-left layers have trivial right frame `Qf_s = 1` (for `s+1 < L`). -/
theorem deepestFrameFamilyQ_interior (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (s : Fin L) (hs : (s : ℕ) + 1 < L) :
    deepestFrameFamilyQ H r B hB hr hL s = (1 : Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ) :=
  (deepestFrameFamily_spec H r B hB hr hL).2.2.1 s hs

/-- **(a)** layer-0 RIGHT-frame trivial: `Qf (firstLayer) = 1` (`L ≥ 2`). -/
theorem deepestFrameFamilyQ_firstLayer (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L) :
    deepestFrameFamilyQ H r B hB hr hL ((⟨0, by omega⟩ : Fin L))
      = (1 : Matrix (Fin (H ((⟨0, by omega⟩ : Fin L)).succ)) (Fin (H ((⟨0, by omega⟩ : Fin L)).succ)) ℝ) :=
  (deepestFrameFamily_spec H r B hB hr hL).2.2.2.1 hL2

/-- **(b)** layer-(L−1) LEFT-frame trivial: `Pf (lastLayer) = 1` (`L ≥ 2`). -/
theorem deepestFrameFamilyP_lastLayer (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : 2 ≤ L) :
    deepestFrameFamilyP H r B hB hr hL ((⟨L - 1, by omega⟩ : Fin L))
      = (1 : Matrix (Fin (H ((⟨L - 1, by omega⟩ : Fin L)).castSucc)) (Fin (H ((⟨L - 1, by omega⟩ : Fin L)).castSucc)) ℝ) :=
  (deepestFrameFamily_spec H r B hB hr hL).2.2.2.2.1 hL2

/-- **(c)** boundary frames invertible: `IsUnit (Pf firstLayer)`, `IsUnit (Qf lastLayer)`. -/
theorem deepestFrameFamily_boundary_isUnit (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    IsUnit (deepestFrameFamilyP H r B hB hr hL ((⟨0, by omega⟩ : Fin L)))
      ∧ IsUnit (deepestFrameFamilyQ H r B hB hr hL ((⟨L - 1, by omega⟩ : Fin L))) :=
  (deepestFrameFamily_spec H r B hB hr hL).2.2.2.2.2

end DLNFibre.DLN.RLCT

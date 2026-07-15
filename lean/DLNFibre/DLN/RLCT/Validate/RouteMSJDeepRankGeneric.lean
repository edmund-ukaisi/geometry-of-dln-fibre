import DLNFibre.DLN.RLCT.Validate.RouteMSJDeeperFlagCore
import DLNFibre.Core.RankLocusClosed
import Mathlib.MeasureTheory.Measure.Prod

set_option linter.style.longLine false

/-!
# `RouteMSJDeepRankGeneric` — the deep-factor generic rank (hGae input (c1))

**Thread `genm-sj5-c1` (aoyagi-full Stage 2), the rankgen hGae-discharge chain.** This module lands the
one genuinely-AG input the coupled-incidence route otherwise avoids: the deep-layer PRODUCT
`deeperFlagZdeep M u z` (the product of the deep chain `M₂ × M_last`) has rank AT LEAST its generic value —
the minimum deep width `deepTailMin M = ⨅_{i} M i.succ.succ` — for a.e. `z`. (Only this `≥` half is proved
here; the always-true `≤` half is the standard `rank_mul_le`, so a.e. the rank equals `deepTailMin M`.)

    (c1)   ∀ᵐ z ∂(vol.restrict (paramsBoxM (redChain u M) 1)),  deepTailMin M ≤ (deeperFlagZdeep M u z).rank

This is `hZrank`, the input `hGae_from_deepRank` (`RouteMSJCorankGeneric`) consumes: composed with the
banked Nat bound `M 1 - u ≤ deepTailMin M` (binding cut) it gives the `M 1 - u ≤ rank` the corank-Gram
survival needs. The statement here uses the raw `⨅` form of `deepTailMin M`
(`= (Finset.univ : Finset (Fin (L+1))).inf' ⟨0,_⟩ (fun i => M i.succ.succ)`, DEFINITIONALLY `deepTailMin M`),
so the caller connects it by `rw [deepTailMin]` / defeq.

## The engine (network-free): a generic chain product attains its min-width rank

`prod_rank_ge_chainInf_ae` — for ANY chain `C : Fin (n+1) → ℕ`, a.e. `p ∂(volume : Params C)`,
`⨅_s C s ≤ (prod C p).rank`. (Generic rank of a layer product = min width; the a.e. is over the exceptional
measure-zero set where a minor drops.) Route, mirroring `corank_survival_ae` / the `corePoly` encoding:

* the STAIRCASE witness `stairWitness C` (each layer `= 1_{(i:ℕ)=(j:ℕ)}`) makes the top-left `ρ×ρ` block of
  `prod C stairWitness` the identity (`prodAux_stairWitness_diag`), so its `ρ×ρ` minor determinant is `1 ≠ 0`;
* hence the minor polynomial `Q = det((prodPolyAux C (coreXmat C) n).submatrix er ec)` (banked
  `prodPolyAux`/`coreXmat`, `DeepestCoreNonvanishing`) is a NONZERO `MvPolynomial (Fin (flatDim C)) ℝ`;
* `MvPolynomial.ae_eval_ne_zero` (Core) + `measurePreserving_paramsEquivFlat C` ⟹ the minor is a.e. nonzero
  in `p`, hence `rank ≥ ρ` a.e. (`Core.submatrix_det_eq_zero_of_rank_le`, contrapositive).

## The transport to `deeperFlagZdeep`

`deeperFlagZdeep M u z = prod (dropHead (redChain u M)) (paramsHeadSplit (redChain u M) z).2`, and
`z ↦ (paramsHeadSplit (redChain u M) z).2` is quasi-measure-preserving (`paramsHeadSplit_mp` measure-preserving
∘ `Measure.quasiMeasurePreserving_snd`), so the chain lemma transports; `⨅_s (dropHead (redChain u M)) s
= deepTailMin M`. Then `ae_restrict_of_ae` to the box.

Sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory MvPolynomial
open scoped BigOperators ENNReal

/-! ## The staircase witness and its identity diagonal block -/

/-- A dimension-cast of an `of`-matrix pushes through to entries: `(cast h (of f)) i j = f (cast i) (cast j)`.
Local twin of `DeepestCoreNonvanishing`'s private `cast_e00_entry`, stated for a general entry function. -/
private theorem cast_of_entry {a a' b b' : ℕ} (ha : a = a') (hb : b = b')
    (h : Matrix (Fin a) (Fin b) ℝ = Matrix (Fin a') (Fin b') ℝ)
    (f : Fin a → Fin b → ℝ) (i : Fin a') (j : Fin b') :
    (cast h (Matrix.of f)) i j = f (Fin.cast ha.symm i) (Fin.cast hb.symm j) := by
  subst ha; subst hb; rfl

/-- **The staircase witness.** Every layer is the partial-identity `1_{(i:ℕ)=(j:ℕ)}` — a `1` on the
diagonal (as naturals), `0` elsewhere. Its layer product's top-left `ρ×ρ` block (`ρ = min width`) is the
identity, giving a nonzero `ρ×ρ` minor. -/
noncomputable def stairWitness {n : ℕ} (C : Fin (n + 1) → ℕ) : Params C :=
  fun _ => Matrix.of (fun i j => if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0)

/-- **The staircase diagonal block.** With `ρ ≤ C s` for all vertices `s`, the partial product
`prodAux C stairWitness k` restricted to indices `< ρ` is the identity: `= 1_{(i:ℕ)=(j:ℕ)}`. Induction on
`k` (the layer product picks up exactly the `l = ⟨(j:ℕ)⟩` term of the staircase layer). -/
theorem prodAux_stairWitness_diag {n : ℕ} (C : Fin (n + 1) → ℕ) (ρ : ℕ) (hρ : ∀ s, ρ ≤ C s) :
    ∀ (k : ℕ) (hk : k < n + 1) (i : Fin (C 0)) (j : Fin (C ⟨k, hk⟩)),
      (i : ℕ) < ρ → (j : ℕ) < ρ →
      prodAux C (stairWitness C) k hk i j = if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0 := by
  intro k
  induction k with
  | zero =>
      intro hk i j _ _
      change (1 : Matrix (Fin (C 0)) (Fin (C 0)) ℝ) i j = _
      rw [Matrix.one_apply]
      by_cases hij : (i : ℕ) = (j : ℕ)
      · rw [if_pos hij, if_pos (Fin.ext hij)]
      · rw [if_neg hij, if_neg (fun h => hij (congrArg Fin.val h))]
  | succ k ih =>
      intro hk i j hi hj
      have hk' : k < n + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < n := Nat.lt_of_succ_lt_succ hk
      have e1 : (⟨k, hk'⟩ : Fin (n + 1)) = (⟨k, hkL⟩ : Fin n).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (n + 1)) = (⟨k, hkL⟩ : Fin n).succ := by
        apply Fin.ext; simp [Fin.succ]
      set Lyr : Matrix (Fin (C ⟨k, hk'⟩)) (Fin (C ⟨k + 1, hk⟩)) ℝ :=
        (by rw [e1, e2]; exact stairWitness C ⟨k, hkL⟩) with hLyr
      have hLyr_entry : ∀ (a : Fin (C ⟨k, hk'⟩)) (b : Fin (C ⟨k + 1, hk⟩)),
          Lyr a b = if (a : ℕ) = (b : ℕ) then (1 : ℝ) else 0 := by
        intro a b
        simp only [hLyr, stairWitness, eq_mpr_eq_cast, cast_cast]
        exact (cast_of_entry (congrArg C e1) (congrArg C e2) (by rw [e1, e2]) _ a b).trans (by simp)
      change (prodAux C (stairWitness C) k hk' * Lyr) i j = _
      rw [Matrix.mul_apply]
      have hjlt : (j : ℕ) < C ⟨k, hk'⟩ := lt_of_lt_of_le hj (hρ _)
      rw [Finset.sum_eq_single (⟨(j : ℕ), hjlt⟩ : Fin (C ⟨k, hk'⟩))]
      · rw [hLyr_entry, ih hk' i ⟨(j : ℕ), hjlt⟩ hi hj]
        simp
      · intro l _ hl
        rw [hLyr_entry, if_neg (fun h => hl (Fin.ext h)), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h

/-! ## The generic chain-product rank lemma (network-free) -/

/-- **The minor polynomial** `Q = det((prodPolyAux C (coreXmat C) n).submatrix er ec)` and its evaluation:
`eval z Q = det((prod C (flatSymm z)).submatrix er ec)` (mirrors `eval_corePoly`). Stated inline in the
main proof; this helper is the `Q ≠ 0` witness plus the a.e.-transport. -/
theorem prod_rank_ge_chainInf_ae {n : ℕ} (C : Fin (n + 1) → ℕ) :
    ∀ᵐ p ∂(volume : Measure (Params C)),
      (Finset.univ : Finset (Fin (n + 1))).inf' ⟨0, Finset.mem_univ 0⟩ C ≤ (prod C p).rank := by
  classical
  by_cases hρ0 : (Finset.univ : Finset (Fin (n + 1))).inf' ⟨0, Finset.mem_univ 0⟩ C = 0
  · filter_upwards with p; rw [hρ0]; exact Nat.zero_le _
  · obtain ⟨c, hc⟩ := Nat.exists_eq_succ_of_ne_zero hρ0
    have hρall : ∀ s, c + 1 ≤ C s := by
      intro s
      have h := Finset.inf'_le (s := (Finset.univ : Finset (Fin (n + 1)))) C (Finset.mem_univ s)
      rwa [hc] at h
    have hρ0le : c + 1 ≤ C 0 := hρall 0
    have hρlast : c + 1 ≤ C (Fin.last n) := hρall (Fin.last n)
    rw [hc]
    set er : Fin (c + 1) → Fin (C 0) := Fin.castLE hρ0le with her
    set ec : Fin (c + 1) → Fin (C (Fin.last n)) := Fin.castLE hρlast with hec
    -- the `(er, ec)`-minor polynomial `Q`, and its evaluation `= det((prod C (flatSymm z)).submatrix er ec)`
    set Q : MvPolynomial (Fin (flatDim C)) ℝ :=
      ((prodPolyAux C (coreXmat C) n (Nat.lt_succ_self n)).submatrix er ec).det with hQ
    have hevalQ : ∀ z : Fin (flatDim C) → ℝ,
        MvPolynomial.eval z Q
          = ((prod C ((paramsEquivFlat C).symm z)).submatrix er ec).det := by
      intro z
      have hmapfull :
          (prodPolyAux C (coreXmat C) n (Nat.lt_succ_self n)).map (MvPolynomial.eval z)
            = prod C ((paramsEquivFlat C).symm z) := by
        rw [prodPolyAux_map (MvPolynomial.eval z) C (coreXmat C)
            (fun s => ((paramsEquivFlat C).symm z) s) (coreXmat_map_eval C z) n
            (Nat.lt_succ_self n), prodPolyAux_eq_prodAux]
        rfl
      have hsub :
          ((prodPolyAux C (coreXmat C) n (Nat.lt_succ_self n)).submatrix er ec).map
              (MvPolynomial.eval z)
            = (prod C ((paramsEquivFlat C).symm z)).submatrix er ec :=
        congrArg (fun N => N.submatrix er ec) hmapfull
      rw [hQ, RingHom.map_det]
      exact congrArg Matrix.det hsub
    -- `Q ≠ 0`: the staircase witness makes the `(c+1)`-minor the identity, det `= 1`
    have hQne : Q ≠ 0 := by
      intro h0
      have hval := hevalQ (paramsEquivFlat C (stairWitness C))
      rw [h0, map_zero,
        show (paramsEquivFlat C).symm (paramsEquivFlat C (stairWitness C)) = stairWitness C from
          by simp] at hval
      have hminor : (prod C (stairWitness C)).submatrix er ec
          = (1 : Matrix (Fin (c + 1)) (Fin (c + 1)) ℝ) := by
        ext a b
        rw [Matrix.submatrix_apply, Matrix.one_apply]
        change prodAux C (stairWitness C) n (Nat.lt_succ_self n) (er a) (ec b) = _
        rw [prodAux_stairWitness_diag C (c + 1) hρall n (Nat.lt_succ_self n) (er a) (ec b)
            (by rw [her]; simpa using a.2) (by rw [hec]; simpa using b.2)]
        simp only [her, hec, Fin.val_castLE]
        by_cases hab : (a : ℕ) = (b : ℕ)
        · rw [if_pos hab, if_pos (Fin.ext hab)]
        · rw [if_neg hab, if_neg (fun h => hab (congrArg Fin.val h))]
      rw [hminor, Matrix.det_one] at hval
      exact one_ne_zero hval.symm
    -- a.e. the minor is nonzero, hence `rank ≥ c+1`
    have hae := MvPolynomial.ae_eval_ne_zero Q hQne
    have hpull := (measurePreserving_paramsEquivFlat C).quasiMeasurePreserving.ae hae
    filter_upwards [hpull] with p hp
    rw [hevalQ, show (paramsEquivFlat C).symm (paramsEquivFlat C p) = p from by simp] at hp
    by_contra hlt
    rw [not_le] at hlt
    exact hp (Core.submatrix_det_eq_zero_of_rank_le (A := prod C p) (r := c) (by omega) er ec)

/-! ## The deep-factor generic rank (c1) -/

/-- **(c1) — the deep-factor generic rank (lower bound).** For a.e. `z` in the reduced-params box, the
deep-layer product `deeperFlagZdeep M u z` has rank at least `deepTailMin M = ⨅_i M i.succ.succ` (its generic
value; stated in the raw `⨅` form, DEFINITIONALLY `deepTailMin M`). Only the `≥` half is asserted — that is
what the discharge needs; the `≤` half is the always-true `rank_mul_le`. This is `hZrank`, the input
`hGae_from_deepRank` consumes (composed with the binding-cut Nat bound `M 1 - u ≤ deepTailMin M`). -/
theorem deeperFlagZdeep_rank_ge_min_ae {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) :
    ∀ᵐ z ∂(volume.restrict (paramsBoxM (redChain u M) 1)),
      (Finset.univ : Finset (Fin (L + 1))).inf' ⟨0, Finset.mem_univ 0⟩ (fun i => M i.succ.succ)
        ≤ (deeperFlagZdeep M u z).rank := by
  -- the chain lemma over the deep chain `dropHead (redChain u M)`
  have hchain := prod_rank_ge_chainInf_ae (dropHead (redChain u M))
  -- `⨅_s (dropHead (redChain u M)) s = ⨅_i M i.succ.succ`
  have hfe : (dropHead (redChain u M)) = (fun i => M i.succ.succ) := by
    funext i; exact redChain_succ u M i
  have hinf : (Finset.univ : Finset (Fin (L + 1))).inf' ⟨0, Finset.mem_univ 0⟩
        (dropHead (redChain u M))
      = (Finset.univ : Finset (Fin (L + 1))).inf' ⟨0, Finset.mem_univ 0⟩ (fun i => M i.succ.succ) := by
    rw [hfe]
  rw [hinf] at hchain
  -- transport `p ↦ (headSplit z).2` (quasi-measure-preserving: MP head split ∘ snd)
  have hg : Measure.QuasiMeasurePreserving
      (fun z : Params (redChain u M) => (paramsHeadSplit (redChain u M) z).2)
      (volume : Measure (Params (redChain u M)))
      (volume : Measure (Params (dropHead (redChain u M)))) := by
    have hsnd : Measure.QuasiMeasurePreserving Prod.snd
        (volume : Measure ((Fin (redChain u M 0) → Fin (redChain u M 1) → ℝ)
          × Params (dropHead (redChain u M))))
        (volume : Measure (Params (dropHead (redChain u M)))) := by
      rw [Measure.volume_eq_prod]
      exact Measure.quasiMeasurePreserving_snd
    exact hsnd.comp (paramsHeadSplit_mp (redChain u M)).quasiMeasurePreserving
  refine ae_restrict_of_ae ?_
  filter_upwards [hg.ae hchain] with z hz
  exact hz

end DLNFibre.DLN.RLCT

import DLNFibre.Core.Aoyagi.IdealInvariance

/-!
# `Core.Aoyagi.Corank2MaintenanceProto` — GATE-3 (L-B): the maintenance step is two-sided (the b-chain
absorbs the REVERSE)

The sharpest honest test of the render's L-B claim ("the b-chain absorbs the reverse general", Phase-3a) —
the claim the gate flags as a possible 7th over-claim. The `(S,J)` recursion maintains the ideal identity
through a **non-unit** left factor `diag(b')`: the generators are `Gᵢ = b'ᵢ·Xᵢ` (`Xᵢ` the residual
`(D''·C')ᵢ`, `b'ᵢ` the accumulated exceptional monomials), and a block-elimination row-clears the unit
pivot at index `p` (whose monomial `b'_p` is the SMALLEST in the chain, `b'_p ∣ b'ᵢ`). The gate question:
does the REVERSE `⟨cleared⟩ ⊆ ⟨original⟩` close with CONTINUOUS cofactors, or need `1/(monomial)` (a wall)?

## The result

`maintenance_step_two_sided`: writing `b'ᵢ = b_p·rᵢ` (so `rᵢ = b'ᵢ/b'_p` is the chain quotient, a
monomial), and the row-clear `Xᵢ ↦ Xᵢ − cᵢ·Xₚ` (so `Gᵢ ↦ Gᵢ − cᵢ·b'ᵢ·Xₚ = Gᵢ − (cᵢ·rᵢ)·Gₚ`), BOTH ideal
inclusions hold on `V`, with cofactors `±cᵢ·rᵢ` — continuous whenever `rᵢ` is (i.e. whenever the b-chain
`b'_p ∣ b'ᵢ` holds, making `rᵢ = b'ᵢ/b'_p` a genuine monomial).

**The gate reading:** the reverse cofactor is `cᵢ·rᵢ` — the SAME as the forward. It is continuous **iff
`rᵢ` is**, i.e. iff the b-chain holds. The coupling enters ONLY through `cᵢ` (the residual clearing
coefficient, arbitrary here — `hc` places no structure on it) and does NOT obstruct the reverse. So "the
b-chain absorbs the reverse" is **confirmed, not an over-claim**: the chain is EXACTLY the hypothesis
(`hr`: `rᵢ` continuous) that makes the reverse cofactor continuous, whatever the coupling. Were the chain
to fail, `rᵢ = b'ᵢ/b'_p` would be `1/(monomial)`, discontinuous on the coordinate hyperplane — the wall.
The chain holds by construction (`b'ᵢ = (∏u)·b'_p`), so the reverse is cheap. Combined with `terminal_bezout`
(the L-C terminal reverse, `1/unit`) and the L-A block-elim (`-PROTO`), all three recursion mechanisms are
two-sided with continuous reverse cofactors.
-/

open DLNFibre.Core.Aoyagi

namespace DLNFibre.Core.Aoyagi.Corank2MaintenanceProto

variable {n D : ℕ}

/-- Delta-sum: `∑ⱼ (if j=i then 1 else 0)·f j = f i`. -/
private lemma delta_one_sum (i : Fin n) (f : Fin n → ℝ) :
    ∑ j, (if j = i then (1:ℝ) else 0) * f j = f i := by
  rw [Finset.sum_congr rfl (fun j _ ↦ by rw [ite_mul, one_mul, zero_mul])]
  simp [Finset.sum_ite_eq']

/-- Scaled delta-sum: `∑ⱼ (if j=p then k else 0)·f j = k·f p`. -/
private lemma delta_scaled_sum (p : Fin n) (k : ℝ) (f : Fin n → ℝ) :
    ∑ j, (if j = p then k else 0) * f j = k * f p := by
  rw [Finset.sum_congr rfl (fun j _ ↦ by rw [ite_mul, zero_mul])]
  simp [Finset.sum_ite_eq']

/-- The **original** generators `Gᵢ = b_p·rᵢ·Xᵢ` (`b'ᵢ = b_p·rᵢ`, `rᵢ = b'ᵢ/b'_p` the chain quotient). -/
def Gorig (bp : (Fin D → ℝ) → ℝ) (r X : Fin n → (Fin D → ℝ) → ℝ) :
    Fin n → (Fin D → ℝ) → ℝ :=
  fun i u ↦ bp u * r i u * X i u

/-- The **cleared** generators `G'ᵢ = Gᵢ − [i≠p]·(cᵢ·rᵢ)·Gₚ` (subtract `cᵢ ×` the pivot from row `i` of
the residual system; the generator picks up the `b'ᵢ = b_p·rᵢ` weight, giving the `cᵢ·rᵢ` coefficient).
`cᵢ` is the residual clearing coefficient `(D'')ᵢₚ` — the COUPLING lives here, and is arbitrary. -/
def Gclear (bp : (Fin D → ℝ) → ℝ) (r c X : Fin n → (Fin D → ℝ) → ℝ) (p : Fin n) :
    Fin n → (Fin D → ℝ) → ℝ :=
  fun i u ↦ bp u * r i u * X i u
    - (if i = p then 0 else c i u * r i u * (bp u * r p u * X p u))

/-- **GATE-3 (L-B) — the maintenance row-clear is TWO-SIDED, reverse cofactor `cᵢ·rᵢ`.** Both ideal
inclusions hold on `V` with continuous cofactors; the reverse `⟨Gclear⟩ ⊆ ⟨Gorig⟩` (the direction the
gate stresses) has cofactor `cᵢ·rᵢ` at the pivot — continuous because `rᵢ = b'ᵢ/b'_p` is (the b-chain).
The coupling `cᵢ` never obstructs it. -/
theorem maintenance_step_two_sided
    (bp : (Fin D → ℝ) → ℝ) (r c X : Fin n → (Fin D → ℝ) → ℝ) (p : Fin n)
    (V : Set (Fin D → ℝ))
    (hr : ∀ i, ContinuousOn (r i) V) (hc : ∀ i, ContinuousOn (c i) V) :
    RegionRepresents (Gclear bp r c X p) (Gorig bp r X) V ∧
      RegionRepresents (Gorig bp r X) (Gclear bp r c X p) V := by
  classical
  constructor
  · -- forward `⟨Gclear⟩ ⊆ ⟨Gorig⟩`: `G'ᵢ = 1·Gᵢ − [i≠p]·(cᵢ·rᵢ)·Gₚ`
    refine ⟨fun i j u ↦ (if j = i then (1:ℝ) else 0)
        - (if i = p then 0 else if j = p then c i u * r i u else 0), ?_, ?_⟩
    · intro i j
      refine ContinuousOn.sub (by split_ifs <;> exact continuousOn_const) ?_
      split_ifs with hip hjp
      · exact continuousOn_const
      · exact (hc i).mul (hr i)
      · exact continuousOn_const
    · intro u _ i
      simp only [Gclear, Gorig]
      rw [Finset.sum_congr rfl (fun j _ ↦ sub_mul _ _ _), Finset.sum_sub_distrib,
        delta_one_sum i (fun j ↦ bp u * r j u * X j u)]
      by_cases hip : i = p
      · simp [hip]
      · simp only [hip, if_false]
        rw [delta_scaled_sum p (c i u * r i u) (fun j ↦ bp u * r j u * X j u)]
  · -- reverse `⟨Gorig⟩ ⊆ ⟨Gclear⟩`: `Gᵢ = 1·G'ᵢ + [i≠p]·(cᵢ·rᵢ)·G'ₚ`  (`G'ₚ = Gₚ`)
    refine ⟨fun i j u ↦ (if j = i then (1:ℝ) else 0)
        + (if i = p then 0 else if j = p then c i u * r i u else 0), ?_, ?_⟩
    · intro i j
      refine ContinuousOn.add (by split_ifs <;> exact continuousOn_const) ?_
      split_ifs with hip hjp
      · exact continuousOn_const
      · exact (hc i).mul (hr i)
      · exact continuousOn_const
    · intro u _ i
      simp only [Gorig, Gclear]
      rw [Finset.sum_congr rfl (fun j _ ↦ add_mul _ _ _), Finset.sum_add_distrib,
        delta_one_sum i (fun j ↦ bp u * r j u * X j u
          - (if j = p then 0 else c j u * r j u * (bp u * r p u * X p u)))]
      by_cases hip : i = p
      · simp [hip]
      · simp only [if_neg hip]
        rw [delta_scaled_sum p (c i u * r i u) (fun j ↦ bp u * r j u * X j u
            - (if j = p then 0 else c j u * r j u * (bp u * r p u * X p u)))]
        rw [if_pos rfl, sub_zero]
        ring

end DLNFibre.Core.Aoyagi.Corank2MaintenanceProto

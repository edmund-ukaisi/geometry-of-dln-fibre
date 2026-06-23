import DLNFibre.Core.OrbitSmooth

/-!
# `DLNFibre.Core.FibreNormalForm` — same-rank ⟹ same fibre codimension (G1)

The first concrete rung of the Lehalleur–Rimányi Lemma-4.6 fibre-codimension build: the geometric
codimension of the multiplication-map fibre `mult⁻¹(B)` depends on `B` **only through its rank**. So
the whole problem reduces to a single normal-form fibre.

**Mechanism (over any infinite field — no `IsAlgClosed`).** The `G_d` base-change action
(`Core.BaseChange.baseChange`) specialised to the **two end vertices** `0` and `N` acts on `Rep_d`,
fixing the inner factors and multiplying `A_last` by `P_N` on the left, `A_0` by `P_0⁻¹` on the
right. Two facts chain:

1. **mult-equivariance** (`mult_smul`): `mult d (P • A) = P_N · (mult d A) · P_0⁻¹` — the inner
   units telescope away (`Core.BaseChange.submult_smul` at the full interval `(0, last)`, through
   `mult_eq_submult`). Hence the linear automorphism `A ↦ P • A` carries `fibre d B` bijectively
   onto `fibre d (P_N · B · P_0⁻¹)` (`image_smul_fibre`).
2. **codim-invariance** (`codimRep_baseChange_image`): a base change is a *linear* change of the
   matrix-entry coordinates, so it induces the `k`-algebra automorphism `baseChangeAlgEquiv P` of
   the coordinate ring (`Core.OrbitSmooth`); `Ideal.height` of a vanishing ideal is invariant under
   it (`RingEquiv.height_comap`). This fills the gap that `Core.OrbitCodim`'s docstring flagged
   ("linear-coordinate invariance is NOT proved here") for the base-change family of linear isos.

Chaining (1)+(2): `codimRepCanonical (fibre d (P_N · B · P_0⁻¹)) = codimRepCanonical (fibre d B)`
(`codimRepCanonical_fibre_baseChange`). With the rank-normal-form fact that any two matrices of the
same rank are `GL × GL`-equivalent (`exists_baseChange_of_rank_eq`), this gives the headline
`codimRepCanonical_fibre_eq_of_rank_eq`: same rank ⟹ same fibre codimension.

**Typeclass.** `[Field k] [Infinite k]` — `Infinite` carries `baseChangeAlgEquiv` (the
`MvPolynomial.funext` step); the rank-normal-form needs only `Field`. An algebraically closed `k` is
infinite, so the DLN application (`k = ℂ`) satisfies it. **Dependency rule:** `Core` only — never import
`DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## API contracts (durable, pre-staged) -/

section Contracts

/-- `mult` is the full interval sub-product `submult … 0 (last)`. -/
example (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
    mult d A = submult d A 0 (Fin.last N) (Fin.zero_le _) := mult_eq_submult d A

/-- The end-factor telescoping: `submult (P • A) 0 (last) = P_last · submult A 0 last · P_0⁻¹`. -/
example (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
    submult d (P • A) 0 (Fin.last N) (Fin.zero_le _)
      = Units.val (P (Fin.last N)) * submult d A 0 (Fin.last N) (Fin.zero_le _)
        * Units.val ((P 0)⁻¹) :=
  submult_smul P A 0 (Fin.last N) (Fin.zero_le _)

/-- `RingEquiv.height_comap`: comap along a ring equiv preserves height. -/
example {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (I : Ideal S) :
    (I.comap e).height = I.height := RingEquiv.height_comap e I

/-- `eval_baseChangePullback`: pullback evaluates as the `G_d`-shift. -/
example [Infinite k] (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
    (x : RepCoord d → k) (f : MvPolynomial (RepCoord d) k) :
    MvPolynomial.eval x (baseChangePullback P f)
      = MvPolynomial.eval (canonicalCoord d (P • (canonicalCoord d).symm x)) f :=
  eval_baseChangePullback P x f

end Contracts

/-! ## mult-equivariance under the base-change action -/

/-- **mult-equivariance.** `mult d (P • A) = P_N · (mult d A) · P_0⁻¹`: the inner units of the base
change telescope away, leaving only the two end-vertex units (`submult_smul` at the full interval
`(0, last)`, through `mult_eq_submult`). -/
theorem mult_smul (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
    mult d (P • A)
      = Units.val (P (Fin.last N)) * mult d A * Units.val ((P 0)⁻¹) := by
  rw [mult_eq_submult, mult_eq_submult, submult_smul]

/-! ## The fibre under the base-change action -/

/-- **The base-change image of a fibre is a fibre.** The linear automorphism `A ↦ P • A` carries
`fibre d B` onto `fibre d (P_N · B · P_0⁻¹)`: by mult-equivariance, `mult (P • A) = P_N · B · P_0⁻¹`
iff `mult A = B`. -/
theorem image_smul_fibre (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := k) d)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    (fun A ↦ P • A) '' (fibre d B)
      = fibre d (Units.val (P (Fin.last N)) * B * Units.val ((P 0)⁻¹)) := by
  ext A
  constructor
  · rintro ⟨A₀, hA₀, rfl⟩
    rw [mem_fibre, mult_smul]
    rw [mem_fibre] at hA₀
    rw [hA₀]
  · intro hA
    refine ⟨P⁻¹ • A, ?_, smul_inv_smul P A⟩
    rw [mem_fibre] at hA
    rw [mem_fibre, mult_smul, hA]
    simp only [Pi.inv_apply, inv_inv]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
      Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

/-! ## Codim-invariance under the base-change action -/

/-- **The vanishing-ideal transport for a base change.** The vanishing ideal of the image of
`(P • ·) '' Z` is the `comap` of the vanishing ideal of `Z` along `baseChangePullback P`: a
polynomial vanishes on the shifted set iff its pullback vanishes on the original
(`eval_baseChangePullback`). -/
theorem vanishingIdeal_image_smul [Infinite k] (d : Fin (N + 1) → ℕ)
    (P : BaseChangeGroup (k := k) d) (Z : Set (Tuple (k := k) d)) :
    vanishingIdeal k (canonicalCoord d '' ((fun A ↦ P • A) '' Z))
      = (vanishingIdeal k (canonicalCoord d '' Z)).comap
          (baseChangePullback P : MvPolynomial (RepCoord d) k →+* _) := by
  ext f
  rw [Ideal.mem_comap, MvPolynomial.mem_vanishingIdeal_iff, MvPolynomial.mem_vanishingIdeal_iff]
  constructor
  · intro hf x hx
    obtain ⟨A, hA, rfl⟩ := hx
    rw [MvPolynomial.aeval_eq_eval]
    show MvPolynomial.eval (canonicalCoord d A) (baseChangePullback P f) = 0
    rw [eval_baseChangePullback, Equiv.symm_apply_apply, ← MvPolynomial.aeval_eq_eval]
    exact hf _ ⟨P • A, ⟨A, hA, rfl⟩, rfl⟩
  · intro hf x hx
    obtain ⟨y, ⟨A, hA, rfl⟩, rfl⟩ := hx
    have hval := hf (canonicalCoord d A) ⟨A, hA, rfl⟩
    rw [MvPolynomial.aeval_eq_eval] at hval ⊢
    show MvPolynomial.eval (canonicalCoord d (P • A)) f = 0
    rw [show canonicalCoord d (P • A)
        = canonicalCoord d (P • (canonicalCoord d).symm (canonicalCoord d A)) from by
        rw [Equiv.symm_apply_apply],
      ← eval_baseChangePullback P (canonicalCoord d A) f]
    exact hval

/-- **Codim-invariance under a base change.** The geometric codimension at the canonical flattening
is invariant under the linear automorphism `A ↦ P • A`: `codimRep (canonicalCoord) ((P•·) '' Z) =
codimRep (canonicalCoord) Z`. The transport `vanishingIdeal_image_smul` reads the shifted vanishing
ideal as a `comap` along `baseChangeAlgEquiv P` (a ring equiv), and `RingEquiv.height_comap`
preserves height. -/
theorem codimRep_baseChange_image [Infinite k] (d : Fin (N + 1) → ℕ)
    (P : BaseChangeGroup (k := k) d) (Z : Set (Tuple (k := k) d)) :
    codimRep (canonicalCoord d) ((fun A ↦ P • A) '' Z) = codimRep (canonicalCoord d) Z := by
  rw [codimRep, codimRep, vanishingIdeal_image_smul]
  have he : (baseChangePullback P : MvPolynomial (RepCoord d) k →+* _)
      = ((baseChangeAlgEquiv P).toRingEquiv.toRingHom) := rfl
  rw [he]
  exact RingEquiv.height_comap (baseChangeAlgEquiv P).toRingEquiv _

/-- **Codim-invariance of a fibre under the end-factor base change.** Combining `image_smul_fibre`
and `codimRep_baseChange_image`: `codimRepCanonical (fibre d (P_N · B · P_0⁻¹)) = codimRepCanonical
(fibre d B)`. -/
theorem codimRepCanonical_fibre_baseChange [Infinite k] (d : Fin (N + 1) → ℕ)
    (P : BaseChangeGroup (k := k) d) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    codimRepCanonical (fibre d (Units.val (P (Fin.last N)) * B * Units.val ((P 0)⁻¹)))
      = codimRepCanonical (fibre d B) := by
  rw [codimRepCanonical, codimRepCanonical, ← image_smul_fibre, codimRep_baseChange_image]

/-! ## Rank normal form: equal rank ⟹ end-factor base-change equivalent

The classical fact "two matrices over a field of equal rank are `GL × GL`-equivalent" — there is no
off-the-shelf Mathlib v4.29 lemma, so it is built here at the linear-map level: a rank-`r` map
`f : (Fin n → k) →ₗ (Fin m → k)` restricts to an isomorphism `U ≃ range f` for `U` a complement of
`ker f` (`fU`), and two maps with equal `ker`/`range` finrank are conjugate by linear automorphisms
(`exists_conj`), assembled from the kernel/range complement decompositions and the equal-dimension
isos `LinearEquiv.ofFinrankEq`. -/

/-- The restriction isomorphism `U ≃ range f` for `U` a complement of `ker f`: through the quotient
`U ≃ (Fin n → k) ⧸ ker f` (`quotientEquivOfIsCompl`) and `(Fin n → k) ⧸ ker f ≃ range f`
(`quotKerEquivRange`). -/
noncomputable def fU (f : (Fin n → k) →ₗ[k] (Fin m → k)) (U : Submodule k (Fin n → k))
    (h : IsCompl (LinearMap.ker f) U) : U ≃ₗ[k] (LinearMap.range f) :=
  (Submodule.quotientEquivOfIsCompl _ U h).symm.trans (LinearMap.quotKerEquivRange f)

/-- The restriction iso `fU` agrees with `f` on `U`: `↑(fU u) = f u`. -/
theorem fU_coe (f : (Fin n → k) →ₗ[k] (Fin m → k)) (U : Submodule k (Fin n → k))
    (h : IsCompl (LinearMap.ker f) U) (u : U) :
    ((fU f U h u : LinearMap.range f) : Fin m → k) = f (u : Fin n → k) := by
  unfold fU
  rw [LinearEquiv.trans_apply, Submodule.quotientEquivOfIsCompl_symm_apply,
    LinearMap.quotKerEquivRange_apply_mk]

/-- **Equal ker/range finrank ⟹ conjugate by linear automorphisms.** Two linear maps `f, f' :
(Fin n → k) →ₗ (Fin m → k)` with `finrank (ker f) = finrank (ker f')` and `finrank (range f) =
finrank (range f')` satisfy `f' = eL ∘ f ∘ eR` for linear automorphisms `eL, eR`. Built from the
kernel/range complement decompositions (`prodEquivOfIsCompl`) and the equal-dimension piece-isos
(`LinearEquiv.ofFinrankEq`): `eR` matches the `f'`-decomposition of the domain to the
`f`-decomposition, `eL` the range decompositions, threaded through `fU` so the maps intertwine. -/
theorem exists_conj (f f' : (Fin n → k) →ₗ[k] (Fin m → k))
    (hker : Module.finrank k (LinearMap.ker f) = Module.finrank k (LinearMap.ker f'))
    (hran : Module.finrank k (LinearMap.range f) = Module.finrank k (LinearMap.range f')) :
    ∃ (eL : (Fin m → k) ≃ₗ[k] (Fin m → k)) (eR : (Fin n → k) ≃ₗ[k] (Fin n → k)),
      f' = (eL : (Fin m → k) →ₗ[k] _) ∘ₗ f ∘ₗ (eR : (Fin n → k) →ₗ[k] _) := by
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl (LinearMap.ker f)
  obtain ⟨U', hU'⟩ := Submodule.exists_isCompl (LinearMap.ker f')
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range f)
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl (LinearMap.range f')
  have hUdim : Module.finrank k U = Module.finrank k U' := by
    have a := Submodule.finrank_add_eq_of_isCompl hU
    have b := Submodule.finrank_add_eq_of_isCompl hU'
    rw [Module.finrank_fin_fun] at a b; omega
  have hWdim : Module.finrank k W = Module.finrank k W' := by
    have a := Submodule.finrank_add_eq_of_isCompl hW
    have b := Submodule.finrank_add_eq_of_isCompl hW'
    rw [Module.finrank_fin_fun] at a b; omega
  set eKer : (LinearMap.ker f) ≃ₗ[k] (LinearMap.ker f') := LinearEquiv.ofFinrankEq _ _ hker
  set eU : U ≃ₗ[k] U' := LinearEquiv.ofFinrankEq U U' hUdim
  set eWc : W ≃ₗ[k] W' := LinearEquiv.ofFinrankEq W W' hWdim
  set rf := fU f U hU with hrf
  set rf' := fU f' U' hU' with hrf'
  set dRf := Submodule.prodEquivOfIsCompl _ U hU with hdRf
  set dRf' := Submodule.prodEquivOfIsCompl _ U' hU' with hdRf'
  set dLf := Submodule.prodEquivOfIsCompl _ W hW with hdLf
  set dLf' := Submodule.prodEquivOfIsCompl _ W' hW' with hdLf'
  set eRange : (LinearMap.range f) ≃ₗ[k] (LinearMap.range f') := rf.symm.trans (eU.trans rf')
    with heRange
  set eR : (Fin n → k) ≃ₗ[k] (Fin n → k) :=
    dRf'.symm.trans ((eKer.symm.prodCongr eU.symm).trans dRf) with heR
  set eL : (Fin m → k) ≃ₗ[k] (Fin m → k) :=
    dLf.symm.trans ((eRange.prodCongr eWc).trans dLf') with heL
  refine ⟨eL, eR, ?_⟩
  apply LinearMap.ext
  intro x
  show f' x = eL (f (eR x))
  set c := (dRf'.symm x).1 with hc
  set e := (dRf'.symm x).2 with he
  have hfx : f' x = ((rf' e : LinearMap.range f') : Fin m → k) := by
    have hxe : x = (c : Fin n → k) + (e : Fin n → k) := by
      conv_lhs => rw [← dRf'.apply_symm_apply x]
      rfl
    rw [hxe, map_add, LinearMap.mem_ker.mp c.2, zero_add, fU_coe]
  have heRx : eR x = (eKer.symm c : Fin n → k) + (eU.symm e : Fin n → k) := by
    rw [heR, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
    show (dRf ((eKer.symm.prodCongr eU.symm) (dRf'.symm x))) = _
    rfl
  have hfeRx : f (eR x) = ((rf (eU.symm e) : LinearMap.range f) : Fin m → k) := by
    rw [heRx, map_add, LinearMap.mem_ker.mp (eKer.symm c).2, zero_add, fU_coe]
  rw [hfx, hfeRx]
  have key : eL ((rf (eU.symm e) : LinearMap.range f) : Fin m → k)
      = ((rf' e : LinearMap.range f') : Fin m → k) := by
    rw [heL, LinearEquiv.trans_apply, LinearEquiv.trans_apply]
    have hsub : dLf.symm ((rf (eU.symm e) : LinearMap.range f) : Fin m → k)
        = (rf (eU.symm e), 0) := by
      rw [hdLf, Submodule.prodEquivOfIsCompl_symm_apply_left]
    rw [hsub]
    show dLf' ((eRange.prodCongr eWc) (rf (eU.symm e), 0)) = _
    rw [LinearEquiv.prodCongr_apply]
    simp only [map_zero]
    rw [hdLf', Submodule.coe_prodEquivOfIsCompl']
    simp only [ZeroMemClass.coe_zero, add_zero]
    congr 1
    rw [heRange, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.apply_symm_apply]
  rw [key]

/-- The unit matrix `toMatrix' e` of a linear automorphism `e` of `(Fin p → k)`, with inverse
`toMatrix' e.symm` (composition of inverse equivs is the identity, whose matrix is `1`). -/
noncomputable def equivUnitMatrix {p : ℕ} (e : (Fin p → k) ≃ₗ[k] (Fin p → k)) :
    (Matrix (Fin p) (Fin p) k)ˣ where
  val := LinearMap.toMatrix' (e : (Fin p → k) →ₗ[k] _)
  inv := LinearMap.toMatrix' (e.symm : (Fin p → k) →ₗ[k] _)
  val_inv := by
    rw [← LinearMap.toMatrix'_comp,
      show (e : (Fin p → k) →ₗ[k] _) ∘ₗ (e.symm : (Fin p → k) →ₗ[k] _) = LinearMap.id from by
        ext x; simp]
    exact LinearMap.toMatrix'_id
  inv_val := by
    rw [← LinearMap.toMatrix'_comp,
      show (e.symm : (Fin p → k) →ₗ[k] _) ∘ₗ (e : (Fin p → k) →ₗ[k] _) = LinearMap.id from by
        ext x; simp]
    exact LinearMap.toMatrix'_id

/-- **Equal rank ⟹ end-factor equivalent.** Two matrices `B, B'` of the same rank are related by an
end-factor base change: `∃ P, B' = P_N · B · P_0⁻¹` (the rank normal form / "matrices of equal rank
are equivalent"). Needs the two end vertices distinct (`hN : 0 ≠ Fin.last N`, i.e. `N ≥ 1`) — for
`N = 0` the multiplication map is constant `1` and the claim is false. Built from `exists_conj` at
`f = toLin' B`, `f' = toLin' B'`, transferred to matrices via `LinearMap.toMatrix'`, with the two
end units `equivUnitMatrix eL` (at `last N`) and `(equivUnitMatrix eR)⁻¹` (at `0`). -/
theorem exists_baseChange_of_rank_eq (d : Fin (N + 1) → ℕ)
    (hN : (0 : Fin (N + 1)) ≠ Fin.last N)
    (B B' : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (h : B.rank = B'.rank) :
    ∃ P : BaseChangeGroup (k := k) d,
      B' = Units.val (P (Fin.last N)) * B * Units.val ((P 0)⁻¹) := by
  have hran : Module.finrank k (LinearMap.range (toLin' B))
      = Module.finrank k (LinearMap.range (toLin' B')) := h
  have hker : Module.finrank k (LinearMap.ker (toLin' B))
      = Module.finrank k (LinearMap.ker (toLin' B')) := by
    have e1 := LinearMap.finrank_range_add_finrank_ker (toLin' B)
    have e2 := LinearMap.finrank_range_add_finrank_ker (toLin' B')
    omega
  obtain ⟨eL, eR, hconj⟩ := exists_conj (toLin' B) (toLin' B') hker hran
  -- transfer the conjugation to matrices: B' = (toMatrix' eL) * B * (toMatrix' eR)
  have hmat : B' = (equivUnitMatrix eL).val * B * (equivUnitMatrix eR).val := by
    have hc := congrArg LinearMap.toMatrix' hconj
    rw [LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp,
      LinearMap.toMatrix'_toLin', ← Matrix.mul_assoc] at hc
    exact hc
  -- assemble the BaseChangeGroup: `last N ↦ equivUnitMatrix eL`, `0 ↦ (equivUnitMatrix eR)⁻¹`
  set P : BaseChangeGroup (k := k) d :=
    fun v ↦ if hv : v = Fin.last N then (by rw [hv]; exact equivUnitMatrix eL)
      else if hv0 : v = 0 then (by rw [hv0]; exact (equivUnitMatrix eR)⁻¹) else 1 with hP
  refine ⟨P, ?_⟩
  have hPL : P (Fin.last N) = equivUnitMatrix eL := by rw [hP]; simp
  have hP0 : P 0 = (equivUnitMatrix eR)⁻¹ := by
    rw [hP]
    show (if hv : (0 : Fin (N + 1)) = Fin.last N then (by rw [hv]; exact equivUnitMatrix eL)
      else if hv0 : (0 : Fin (N + 1)) = 0 then (by rw [hv0]; exact (equivUnitMatrix eR)⁻¹)
      else 1) = (equivUnitMatrix eR)⁻¹
    rw [dif_neg hN, dif_pos rfl]
    rfl
  rw [hPL, hP0, inv_inv]
  exact hmat

/-! ## The headline: same rank ⟹ same fibre codimension -/

/-- **Same rank ⟹ same fibre codimension.** The geometric codimension of the multiplication-map
fibre depends on the target `B` only through its rank: for `B.rank = B'.rank`,
`codimRepCanonical (fibre d B) = codimRepCanonical (fibre d B')`. Reduces the Lemma-4.6 problem (all
rank-`r` targets) to a single fibre. Needs `N ≥ 1` (`hN : 0 ≠ Fin.last N`): for `N = 0` the
multiplication map is the constant `1`, so the fibre over `1` is everything but the fibre over a
different same-rank `B'` is empty — the claim is genuinely false there. -/
theorem codimRepCanonical_fibre_eq_of_rank_eq [Infinite k] (d : Fin (N + 1) → ℕ)
    (hN : (0 : Fin (N + 1)) ≠ Fin.last N)
    (B B' : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (h : B.rank = B'.rank) :
    codimRepCanonical (fibre d B) = codimRepCanonical (fibre d B') := by
  obtain ⟨P, hP⟩ := exists_baseChange_of_rank_eq d hN B B' h
  rw [hP, codimRepCanonical_fibre_baseChange]

/-! ## Non-vacuity witness

On the `(2,2,2)` dimension vector over `ℚ` (a `Field` that is `Infinite`), the two distinct rank-1
targets `!![1,0;0,0]` and `!![0,0;1,0]` have equal fibre codimension — the headline applied to a
genuine instance (the two matrices differ; equal rank because the second is a unit-multiple of the
first). The end vertices `0` and `2` are distinct, so `hN` holds. -/

section Witness

/-- The two `(2,2,2)`-witness rank-1 targets have equal fibre codimension. -/
example :
    codimRepCanonical (k := ℚ) (fibre dWitness (!![1, 0; 0, 0]))
      = codimRepCanonical (k := ℚ) (fibre dWitness (!![0, 0; 1, 0])) := by
  have hrank : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ).rank
      = (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ).rank := by
    have hP : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ) * !![1, 0; 0, 0] = !![0, 0; 1, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hu : IsUnit (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ).det := by
      rw [Matrix.det_fin_two_of]; norm_num
    rw [← hP, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hu]
  have hN : (0 : Fin (2 + 1)) ≠ Fin.last 2 := by decide
  exact codimRepCanonical_fibre_eq_of_rank_eq dWitness hN _ _ hrank

end Witness

end DLNFibre.Core

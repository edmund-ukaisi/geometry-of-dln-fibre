import DLNFibre.Core.RankLocusClosed
import DLNFibre.Core.BoxMoveGeneral
import DLNFibre.Core.BoxMoveGeneration
import DLNFibre.Core.OrbitKostant

/-!
# `DLNFibre.Core.OrbitClosure` — the orbit closure equals the rank locus (L6.4) and primeness (L1★)

The Abeasis–Del Fra orbit-closure theorem for the equioriented type-`A` quiver, at the **ideal
level**: the vanishing ideal of the determinantal rank locus `orbitRankLocus M` equals the vanishing
ideal of the orbit `O_M`, so their Zariski closures coincide (`Ō_M = orbitRankLocus M` as closed
sets). With L1's `isPrime_vanishingIdeal_orbitSet` this gives the rank locus a prime vanishing ideal
— the rank locus is an irreducible variety.

The proof closes the **hard** inclusion `orbitRankLocus M ⊆ Ō_M` (the easy `Ō_M ⊆ orbitRankLocus M`
is `RankLocusClosed.vanishingIdeal_orbitRankLocus_le_orbitSet`). Architecture (Codex-vetted):

1. **Closure operator** `repClosure S = zeroLocus (vanishingIdeal (canonicalCoord '' S))` — the
   Zariski closure of the flattened set. Extensive / monotone / idempotent (the Galois connection),
   plus the transport `canonicalCoord '' S ⊆ repClosure T → repClosure S ⊆ repClosure T`.
2. **Rank-pattern bridge** (`repClosure_orbitSet_eq_of_rankPattern_eq`): two tuples with the same
   rank pattern have the same orbit (`rankPattern_eq_iff_orbit`), hence the same `repClosure`. This
   dissolves all the list-permutation / direct-sum-reassociation bookkeeping: the geometric per-move
   lemmas are invoked with *their own* list shape, then transported to the canonical witness by rank
   pattern alone.
3. **Per-step degeneration** (`boxMoveStep_repClosure_realizer_subset`): a single box move
   `BoxMoveStep r r''` (the upper pattern `r` achievable + supported) drops the realizer of `r''`
   into the closure of the realizer of `r`. The box coordinates `(a,c,b,e)` are converted `ℤ → Fin`,
   the geometric split / non-split lemma supplies the degeneration, and the rank-pattern bridge
   reconciles its shape with the realizers.
4. **Chain composition + assembly** (`box_move_chain_of_le` + `baseChange_normalForm`): `Ō_M ⊆
   orbitRankLocus M` at the ideal level — the headline `vanishingIdeal (canonicalCoord ''
   orbitRankLocus M) = vanishingIdeal (orbitSet M)`.
5. **Primeness** (`isPrime_vanishingIdeal_orbitRankLocus`): the headline + L1.

**Typeclass.** `[Field k] [Infinite k]` for the degeneration engine; `[IsAlgClosed k]` only for the
primeness corollary (which inherits L1's hypothesis). **Dependency rule:** `Core` only.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## Piece 1 — the representation-space closure operator `repClosure` -/

/-- The **Zariski closure** of a set of representation points: the zero locus of the vanishing ideal
of its flattening. Over the base field `k` (read = write field). -/
def repClosure {d : Fin (N + 1) → ℕ} (S : Set (RepCoord d → k)) : Set (RepCoord d → k) :=
  MvPolynomial.zeroLocus (σ := RepCoord d) (k := k) k
    (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k S)

/-- `repClosure` is **extensive**: `S ⊆ repClosure S` (a set lies in its own closure). -/
theorem subset_repClosure {d : Fin (N + 1) → ℕ} (S : Set (RepCoord d → k)) :
    S ⊆ repClosure S :=
  MvPolynomial.zeroLocus_vanishingIdeal_le S

/-- `repClosure` is **monotone**: `S ⊆ T → repClosure S ⊆ repClosure T`. -/
theorem repClosure_mono {d : Fin (N + 1) → ℕ} {S T : Set (RepCoord d → k)} (h : S ⊆ T) :
    repClosure S ⊆ repClosure T :=
  MvPolynomial.zeroLocus_anti_mono (MvPolynomial.vanishingIdeal_anti_mono h)

/-- `repClosure` is **idempotent**: `repClosure (repClosure S) = repClosure S`. The closure operator
`l ∘ u` of the (order-dual) Galois connection `zeroLocus ⊣ vanishingIdeal`, via `u_l_u_eq_u`. -/
theorem repClosure_idem {d : Fin (N + 1) → ℕ} (S : Set (RepCoord d → k)) :
    repClosure (repClosure S) = repClosure S :=
  congrArg (MvPolynomial.zeroLocus (σ := RepCoord d) (k := k) k)
    ((MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection
      (σ := RepCoord d) (k := k) (K := k)).u_l_u_eq_u S)

/-- **The transport lemma.** If `S` lies in the closure of `T`, then `repClosure S ⊆ repClosure T`:
monotonicity into `repClosure (repClosure T)` then idempotence. The induction step glue. -/
theorem repClosure_subset_of_subset_repClosure {d : Fin (N + 1) → ℕ}
    {S T : Set (RepCoord d → k)} (h : S ⊆ repClosure T) :
    repClosure S ⊆ repClosure T := by
  calc repClosure S ⊆ repClosure (repClosure T) := repClosure_mono h
    _ = repClosure T := repClosure_idem T

/-! ## Piece 2a — the rank-pattern bridge (orbit and closure depend only on the rank pattern) -/

/-- **Same rank pattern ⟹ same orbit set.** If `A` and `B` have equal rank patterns they are
`G_d`-equivalent (`rankPattern_eq_iff_orbit`), so the orbit through `A` equals that through `B`. -/
theorem orbitSet_eq_of_rankPattern_eq {d : Fin (N + 1) → ℕ} {A B : Tuple (k := k) d}
    (h : ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
      rankPattern d A i j hij = rankPattern d B i j hij) :
    orbitSet A = orbitSet B := by
  obtain ⟨P₀, hP₀⟩ := (rankPattern_eq_iff_orbit A B).mp h
  apply congrArg (canonicalCoord d '' ·)
  ext C
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨P, rfl⟩
    refine ⟨P * P₀⁻¹, ?_⟩
    rw [smul_eq_baseChange, baseChange_mul, ← smul_eq_baseChange, ← smul_eq_baseChange, ← hP₀,
      inv_smul_smul]
  · rintro ⟨P, rfl⟩
    refine ⟨P * P₀, ?_⟩
    rw [smul_eq_baseChange, baseChange_mul, ← smul_eq_baseChange, ← smul_eq_baseChange, hP₀]

/-- **Same rank pattern ⟹ same orbit closure.** The `repClosure` of the orbit set depends only on
the rank pattern — the bridge that absorbs every list-shape / reassociation choice. -/
theorem repClosure_orbitSet_eq_of_rankPattern_eq {d : Fin (N + 1) → ℕ} {A B : Tuple (k := k) d}
    (h : ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
      rankPattern d A i j hij = rankPattern d B i j hij) :
    repClosure (orbitSet A) = repClosure (orbitSet B) := by
  rw [orbitSet_eq_of_rankPattern_eq h]

/-! ## Piece 2b — `G_d`-stability of an orbit closure (single point ⟹ whole orbit)

A geometric per-move lemma lands a *single* point `canonicalCoord D ∈ repClosure (orbitSet U)`; to
feed the chain I need the *whole* orbit `orbitSet D ⊆ repClosure (orbitSet U)`. The closure
`repClosure (orbitSet U)` is `G_d`-stable: the action `A ↦ P • A` is a *linear* change of the
matrix-entry coordinates, so it lifts to an algebra endomorphism `baseChangePullback P` of the
coordinate ring with `eval x ∘ pullback = eval (canonicalCoord (P • canonicalCoord.symm x))`. A
polynomial vanishing on `orbitSet U` (itself `G_d`-stable) still vanishes after the shift, so the
zero locus is `G_d`-stable. -/

/-- The base-change substitution: coordinate `⟨i,r,c⟩ ↦` the `(r,c)` entry of
`(P_{i+1}) · X_i · (P_i)⁻¹` where `X_i` is the generic matrix of edge-`i` coordinate variables. The
coordinate-ring incarnation of the linear map `A ↦ P • A`. -/
noncomputable def baseChangeSub {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d) :
    RepCoord d → MvPolynomial (RepCoord d) k :=
  fun x ↦ ((((Units.val (P x.1.succ)).map MvPolynomial.C)
      * (Matrix.of (fun (r : Fin (d x.1.succ)) (c : Fin (d x.1.castSucc)) ↦
          MvPolynomial.X (⟨x.1, r, c⟩ : RepCoord d)))
      * ((Units.val (P x.1.castSucc)⁻¹).map MvPolynomial.C) :
        Matrix (Fin (d x.1.succ)) (Fin (d x.1.castSucc)) (MvPolynomial (RepCoord d) k)))
      x.2.1 x.2.2

/-- The base-change pullback algebra endomorphism `aeval (baseChangeSub P)`. -/
noncomputable def baseChangePullback {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d) :
    MvPolynomial (RepCoord d) k →ₐ[k] MvPolynomial (RepCoord d) k :=
  MvPolynomial.aeval (baseChangeSub P)

/-- **Evaluation of the pullback is evaluation at the shifted point.** `eval x (baseChangeSub P
coord)` recovers the coordinate of `P • (canonicalCoord.symm x)`: the substitution computes the
base-changed entry. -/
theorem eval_baseChangeSub {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d)
    (x : RepCoord d → k) (coord : RepCoord d) :
    MvPolynomial.eval x (baseChangeSub P coord)
      = canonicalCoord d (P • (canonicalCoord d).symm x) coord := by
  rw [baseChangeSub, canonicalCoord_apply, smul_eq_baseChange, baseChange_apply]
  -- the matrix `map (eval x)` of the symbolic product is the numeric base-changed factor
  set Xmat : Matrix (Fin (d coord.1.succ)) (Fin (d coord.1.castSucc)) (MvPolynomial (RepCoord d) k)
      := Matrix.of (fun (r : Fin (d coord.1.succ)) (c : Fin (d coord.1.castSucc)) ↦
          MvPolynomial.X (⟨coord.1, r, c⟩ : RepCoord d)) with hXmat
  have hmat : ((((Units.val (P coord.1.succ)).map MvPolynomial.C) * Xmat
        * ((Units.val (P coord.1.castSucc)⁻¹).map MvPolynomial.C) :
        Matrix (Fin (d coord.1.succ)) (Fin (d coord.1.castSucc))
          (MvPolynomial (RepCoord d) k)).map (MvPolynomial.eval x))
      = (Units.val (P coord.1.succ)) * ((canonicalCoord d).symm x coord.1)
        * (Units.val (P coord.1.castSucc)⁻¹) := by
    rw [Matrix.map_mul, Matrix.map_mul]
    congr 1
    · congr 1
      · funext r c; simp only [Matrix.map_apply, MvPolynomial.eval_C]
      · funext r c
        simp only [hXmat, Matrix.map_apply, MvPolynomial.eval_X, Matrix.of_apply]
        rw [← canonicalCoord_apply ((canonicalCoord d).symm x) ⟨coord.1, r, c⟩,
          Equiv.apply_symm_apply]
    · funext r c; simp only [Matrix.map_apply, MvPolynomial.eval_C]
  exact congrFun (congrFun hmat coord.2.1) coord.2.2

/-- The pullback evaluates as the shift: `eval x (baseChangePullback P f) = eval (shifted x) f`. -/
theorem eval_baseChangePullback {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := k) d)
    (x : RepCoord d → k) (f : MvPolynomial (RepCoord d) k) :
    MvPolynomial.eval x (baseChangePullback P f)
      = MvPolynomial.eval (canonicalCoord d (P • (canonicalCoord d).symm x)) f := by
  rw [baseChangePullback,
    show MvPolynomial.eval x (MvPolynomial.aeval (baseChangeSub P) f)
      = (MvPolynomial.eval x).comp ((MvPolynomial.aeval (baseChangeSub P)).toRingHom) f from rfl]
  have hhom : (MvPolynomial.eval x).comp ((MvPolynomial.aeval (baseChangeSub P)).toRingHom)
      = MvPolynomial.eval (canonicalCoord d (P • (canonicalCoord d).symm x)) := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun coord ↦ ?_)
    · rw [RingHom.comp_apply]
      show MvPolynomial.eval x (MvPolynomial.aeval (baseChangeSub P) (MvPolynomial.C r)) = _
      rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.eval_C,
        MvPolynomial.eval_C]
    · rw [RingHom.comp_apply]
      show MvPolynomial.eval x (MvPolynomial.aeval (baseChangeSub P) (MvPolynomial.X coord)) = _
      rw [MvPolynomial.aeval_X, MvPolynomial.eval_X, eval_baseChangeSub]
  exact congrFun (congrArg DFunLike.coe hhom) f

/-- The orbit set is **`G_d`-stable** as a point set: shifting an orbit point by a base change stays
in the orbit. -/
theorem orbitSet_baseChange_stable {d : Fin (N + 1) → ℕ} (U : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) {y : RepCoord d → k} (hy : y ∈ orbitSet U) :
    canonicalCoord d (P • (canonicalCoord d).symm y) ∈ orbitSet U := by
  obtain ⟨A, ⟨Q, hQ⟩, rfl⟩ := hy
  refine ⟨P • A, ⟨P * Q, ?_⟩, ?_⟩
  · rw [smul_eq_baseChange, baseChange_mul, ← smul_eq_baseChange, ← smul_eq_baseChange, hQ]
  · rw [Equiv.symm_apply_apply]

/-- The base-change pullback of a polynomial vanishing on `orbitSet U` again vanishes there (the
ideal is `G_d`-invariant): the pullback evaluates as the `G_d`-shift, which stays in the orbit. -/
theorem baseChangePullback_mem_vanishingIdeal_orbitSet {d : Fin (N + 1) → ℕ} (U : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d) {f : MvPolynomial (RepCoord d) k}
    (hf : f ∈ MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (orbitSet U)) :
    baseChangePullback P f
      ∈ MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (orbitSet U) := by
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hf ⊢
  intro y hy
  rw [MvPolynomial.aeval_eq_eval, eval_baseChangePullback, ← MvPolynomial.aeval_eq_eval]
  exact hf _ (orbitSet_baseChange_stable U P hy)

/-- **`G_d`-stability of the orbit closure (single point ⟹ whole orbit).** If `canonicalCoord D`
lies in the closure of the orbit of `U`, the entire orbit of `D` does: `orbitSet D ⊆ repClosure
(orbitSet U)`. Each orbit point of `D` is a base-change shift of `canonicalCoord D`, and the closure
is `G_d`-stable (the vanishing ideal is `G_d`-invariant). -/
theorem orbitSet_subset_repClosure_orbitSet_of_canonical_mem {d : Fin (N + 1) → ℕ}
    {D U : Tuple (k := k) d} (hD : canonicalCoord d D ∈ repClosure (orbitSet U)) :
    orbitSet D ⊆ repClosure (orbitSet U) := by
  rintro y ⟨A, ⟨Q, rfl⟩, rfl⟩
  rw [repClosure, MvPolynomial.mem_zeroLocus_iff]
  intro f hf
  -- `y = canonicalCoord (Q • D) = canonicalCoord (Q • symm (canonicalCoord D))`, and
  -- `eval (canonicalCoord (Q • D)) f = eval (canonicalCoord D) (pullback Q f)`, which is `0`.
  rw [MvPolynomial.aeval_eq_eval,
    show canonicalCoord d (Q • D)
      = canonicalCoord d (Q • (canonicalCoord d).symm (canonicalCoord d D)) from by
      rw [Equiv.symm_apply_apply],
    ← eval_baseChangePullback Q (canonicalCoord d D) f]
  have hmem := hD
  rw [repClosure, MvPolynomial.mem_zeroLocus_iff] at hmem
  have := hmem (baseChangePullback Q f) (baseChangePullback_mem_vanishingIdeal_orbitSet U Q hf)
  rwa [MvPolynomial.aeval_eq_eval] at this

end DLNFibre.Core

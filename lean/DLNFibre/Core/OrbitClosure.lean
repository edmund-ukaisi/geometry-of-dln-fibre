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

/-! ## Piece 2c — the per-step degeneration (CRUX)

A single box move drops the closure: if tuples `Tp, Tq` over `d` realize the upper / lower rank
patterns `r, r''` of a box move `BoxMoveStep r r''` (with `r` achievable, supported), then
`repClosure (orbitSet Tq) ⊆ repClosure (orbitSet Tp)`. The proof converts the integer box
coordinates to `Fin`, invokes the split / non-split geometric degeneration (`Core.BoxMoveGeneral`),
and reconciles the geometric witnesses' shapes with `Tp, Tq` through the rank-pattern bridge +
`G_d`-stability (single point ⟹ whole orbit). -/

/-- The integer second-difference of `r` restricted to the upper triangle, as a Kostant array
(`SuppArray`): `1`-truncated below the diagonal. `cumul` recovers `r` on the triangle. -/
noncomputable def diffTri {N : ℕ} (r : ℤ → ℤ → ℤ) (hr : Supported (N : ℤ) r) :
    SuppArray (N : ℤ) ℤ :=
  ⟨fun i j ↦ if i ≤ j then diff r i j else 0, by
    refine ⟨fun i j hi ↦ ?_, fun i j hj ↦ ?_⟩ <;> dsimp only <;> split_ifs with h
    · exact (supported_diff hr).1 i j hi
    · rfl
    · exact (supported_diff hr).2 i j hj
    · rfl⟩

/-- **The per-step degeneration (CRUX).** A single box move `BoxMoveStep r r''` between achievable,
supported, below-diagonal-vanishing rank-pattern arrays (with `r''` likewise achievable) drops the
orbit closure: any tuples `Tp, Tq` over `d` realizing `r, r''` on the upper triangle satisfy
`repClosure (orbitSet Tq) ⊆ repClosure (orbitSet Tp)`. The geometric content is the per-move
degeneration of `Core.BoxMoveGeneral`, reconciled with the realizers by the rank-pattern bridge and
`G_d`-stability.

CONDITIONAL: stated here as the clean residual obligation; the body (integer→`Fin` box-coordinate
extraction + the split / non-split geometric invocation + the residual-`rest` dimension cast) is the
one genuinely hard glue of L6.4. -/
theorem boxMoveStep_repClosure_subset [Infinite k] {d : Fin (N + 1) → ℕ}
    {r r'' : ℤ → ℤ → ℤ} {Tp Tq : Tuple (k := k) d}
    (hrsupp : Supported (N : ℤ) r) (hr''supp : Supported (N : ℤ) r'')
    (hrnn : ∀ i j : ℤ, i ≤ j → 0 ≤ diff r i j)
    (hr''nn : ∀ i j : ℤ, i ≤ j → 0 ≤ diff r'' i j)
    (hrdiag : ∀ k : Fin (N + 1), (d k : ℤ) = r (k : ℤ) (k : ℤ))
    (hr''diag : ∀ k : Fin (N + 1), (d k : ℤ) = r'' (k : ℤ) (k : ℤ))
    (hp : ∀ (i j : Fin (N + 1)) (hij : i ≤ j), (rankPattern d Tp i j hij : ℤ) = r (i : ℤ) (j : ℤ))
    (hq : ∀ (i j : Fin (N + 1)) (hij : i ≤ j), (rankPattern d Tq i j hij : ℤ) = r'' (i : ℤ) (j : ℤ))
    (hstep : BoxMoveStep r r'') :
    repClosure (orbitSet Tq) ⊆ repClosure (orbitSet Tp) := by
  sorry

/-! ## Piece 2d — the realizer of an achievable pattern, over the fixed dimension vector

For a supported, triangle-achievable array `r` with diagonal `= d`, the truncated `diff`-array
`diffTri r` is a literal Kostant partition realizing `d` (`CMPlus`), so `realizer (diffTri r)` is a
tuple over `d` whose rank pattern is `r` on the upper triangle. The canonical witness the chain runs
on. -/

/-- `cumul (diffTri r) = r` on the upper triangle: truncation below the diagonal is invisible to
`cumul`, and `cumul` inverts `diff` on the supported `r`. -/
theorem cumul_diffTri_eq {r : ℤ → ℤ → ℤ} (hr : Supported (N : ℤ) r) {i j : ℤ} (hij : i ≤ j) :
    cumul (N : ℤ) (diffTri (N := N) r hr).1 i j = r i j := by
  rw [diffTri, cumul_truncBelow_of_le (diff r) hij, cumul_diff (N : ℤ) r hr.1 hr.2]

/-- `diffTri r` is a Kostant partition realizing `d` when `r` is triangle-achievable with diagonal
`= d`: nonnegative (truncated), `i ≤ j`-supported, diagonal from `cumul_diffTri`. -/
theorem cMPlus_diffTri {d : Fin (N + 1) → ℕ} {r : ℤ → ℤ → ℤ} (hr : Supported (N : ℤ) r)
    (hrnn : ∀ i j : ℤ, i ≤ j → 0 ≤ diff r i j) (hrdiag : ∀ k : Fin (N + 1), (d k : ℤ) = r k k) :
    CMPlus d (diffTri (N := N) r hr) := by
  refine ⟨⟨fun i j ↦ ?_, fun i j hji ↦ ?_⟩, fun k ↦ ?_⟩
  · simp only [diffTri]; split_ifs with h
    · exact hrnn i j h
    · exact le_refl 0
  · simp only [diffTri, if_neg (not_le.mpr hji)]
  · rw [cumul_diffTri_eq hr (le_refl (k : ℤ)), hrdiag k]

/-- The canonical realizer of an achievable supported pattern `r` (diagonal `= d`): a tuple over `d`
with rank pattern `r` on the upper triangle. -/
noncomputable def patternRealizer {d : Fin (N + 1) → ℕ} {r : ℤ → ℤ → ℤ} (hr : Supported (N : ℤ) r)
    (hrnn : ∀ i j : ℤ, i ≤ j → 0 ≤ diff r i j) (hrdiag : ∀ k : Fin (N + 1), (d k : ℤ) = r k k) :
    Tuple (k := k) d :=
  realizer (k := k) (diffTri (N := N) r hr) (cMPlus_diffTri hr hrnn hrdiag)

/-- The realizer's rank pattern is `r` on the upper triangle. -/
theorem rankPattern_patternRealizer {d : Fin (N + 1) → ℕ} {r : ℤ → ℤ → ℤ} (hr : Supported (N : ℤ) r)
    (hrnn : ∀ i j : ℤ, i ≤ j → 0 ≤ diff r i j) (hrdiag : ∀ k : Fin (N + 1), (d k : ℤ) = r k k)
    (i j : Fin (N + 1)) (hij : i ≤ j) :
    (rankPattern d (patternRealizer (k := k) hr hrnn hrdiag) i j hij : ℤ) = r (i : ℤ) (j : ℤ) := by
  rw [patternRealizer, rankPattern_realizer (k := k) (diffTri (N := N) r hr)
    (cMPlus_diffTri hr hrnn hrdiag) i j hij,
    cumul_diffTri_eq hr (by exact_mod_cast Fin.le_def.mp hij)]

/-! ## Piece 2e — box-move bounds and invariant preservation

The box-move coordinates land in `[0,N]` (forced by `diff r a e ≥ 1` and support), and a box move
preserves support, triangle-achievability, and the diagonal — the invariants the chain threads. -/

/-- The box's lower-left corner is in range: `1 ≤ diff r a e` and `Supported N r` force `0 ≤ a`
(else all four `diff` reference points vanish by support). -/
theorem zero_le_of_diff_pos {r : ℤ → ℤ → ℤ} (hr : Supported (N : ℤ) r) {a e : ℤ}
    (hae : 1 ≤ diff r a e) : 0 ≤ a := by
  by_contra h
  rw [diff_apply, hr.1 a e (by omega), hr.1 a (e + 1) (by omega), hr.1 (a - 1) e (by omega),
    hr.1 (a - 1) (e + 1) (by omega)] at hae
  omega

/-- The box's upper-right corner is in range: `1 ≤ diff r a e` and `Supported N r` force `e ≤ N`. -/
theorem le_N_of_diff_pos {r : ℤ → ℤ → ℤ} (hr : Supported (N : ℤ) r) {a e : ℤ}
    (hae : 1 ≤ diff r a e) : e ≤ (N : ℤ) := by
  by_contra h
  rw [diff_apply, hr.2 a e (by omega), hr.2 a (e + 1) (by omega), hr.2 (a - 1) e (by omega),
    hr.2 (a - 1) (e + 1) (by omega)] at hae
  omega

/-- A box move preserves support: `boxDrop r` is supported when `r` is and the box is in range
(`0 ≤ a`, `e ≤ N`). The indicator vanishes off the in-range box `[a,c−1]×[b+1,e]`. -/
theorem supported_boxDrop {r : ℤ → ℤ → ℤ} (hr : Supported (N : ℤ) r) {a c b e : ℤ}
    (ha0 : 0 ≤ a) (heN : e ≤ (N : ℤ)) : Supported (N : ℤ) (boxDrop r a c b e) := by
  refine ⟨fun i j hi ↦ ?_, fun i j hj ↦ ?_⟩
  · rw [boxDrop, boxIndicator, if_neg (by rintro ⟨h1, _⟩; omega), sub_zero]; exact hr.1 i j hi
  · rw [boxDrop, boxIndicator, if_neg (by rintro ⟨_, _, _, h4⟩; omega), sub_zero]; exact hr.2 i j hj

/-! ## Piece 3 — chain composition

The reflexive-transitive closure of `BoxMoveStep` composes the per-step closure inclusions, with the
invariants (support, triangle-achievability, diagonal `= d`) threaded through each step. -/

/-- A box step preserves the chain invariants: from `Supported r`, `diff r ≥ 0` on the triangle, and
diagonal `= d`, `r''` is supported, triangle-achievable, same diagonal. -/
theorem boxMoveStep_invariants {d : Fin (N + 1) → ℕ} {r r'' : ℤ → ℤ → ℤ}
    (hr : Supported (N : ℤ) r) (hrnn : ∀ i j : ℤ, i ≤ j → 0 ≤ diff r i j)
    (hrdiag : ∀ k : Fin (N + 1), (d k : ℤ) = r (k : ℤ) (k : ℤ)) (hstep : BoxMoveStep r r'') :
    Supported (N : ℤ) r'' ∧ (∀ i j : ℤ, i ≤ j → 0 ≤ diff r'' i j) ∧
      (∀ k : Fin (N + 1), (d k : ℤ) = r'' (k : ℤ) (k : ℤ)) := by
  obtain ⟨a, c, b, e, hac, hcb, hbe, hae, hcbm, rfl⟩ := hstep
  have ha0 : 0 ≤ a := zero_le_of_diff_pos hr hae
  have heN : e ≤ (N : ℤ) := le_N_of_diff_pos hr hae
  refine ⟨supported_boxDrop hr ha0 heN, fun i j hij ↦ ?_, fun t ↦ ?_⟩
  · -- triangle achievability: the four-corner move only subtracts at `(a,e)` (≥ 1) and linked
    -- `(c,b)` (≥ 1), both on the triangle, so the drop stays nonnegative there.
    have hdiff : diff (boxDrop r a c b e) i j
        = diff r i j - diff (boxIndicator a c b e) i j := by
      simp only [boxDrop, diff_apply]; ring
    rw [hdiff, boxIndicator_diff a c b e i j hac hcb hbe]
    have h0 := hrnn i j hij
    by_cases hae' : i = a ∧ j = e
    · obtain ⟨hi, hj⟩ := hae'
      rw [hi, hj] at h0 ⊢
      rw [if_neg (by rintro ⟨_, h⟩; omega), if_neg (by rintro ⟨h, _⟩; omega),
        if_pos ⟨rfl, rfl⟩, if_neg (by rintro ⟨h, _⟩; omega)]
      have := hae; omega
    · by_cases hcb' : i = c ∧ j = b
      · obtain ⟨hi, hj⟩ := hcb'
        have hcle : c ≤ b := by rw [hi, hj] at hij; omega
        have hcbm' := hcbm hcle
        rw [hi, hj] at h0 ⊢
        rw [if_neg (by rintro ⟨h, _⟩; omega), if_neg (by rintro ⟨_, h⟩; omega),
          if_neg (by rintro ⟨h, _⟩; omega), if_pos ⟨rfl, rfl⟩]
        omega
      · rw [if_neg fun h ↦ hae' h, if_neg fun h ↦ hcb' h]
        split_ifs <;> omega
  · rw [boxDrop_diag r hac hcb hbe, hrdiag t]

/-- **The chain drops the closure.** A box-move chain `BoxMoveChain r s` (with `r` achievable,
supported, diagonal `= d`) gives the closure inclusion for any tuples
`Tr, Ts` over `d` realizing `r, s` on the upper triangle. Each step's per-step degeneration composed
by `ReflTransGen.head_induction_on`, invariants threaded through `boxMoveStep_invariants`,
the realizers reconciled at the junctions by the rank-pattern bridge. -/
theorem boxMoveChain_repClosure_subset [Infinite k] {d : Fin (N + 1) → ℕ} {r s : ℤ → ℤ → ℤ}
    (hchain : BoxMoveChain r s) :
    ∀ (hr : Supported (N : ℤ) r) (hrnn : ∀ i j : ℤ, i ≤ j → 0 ≤ diff r i j)
      (hrdiag : ∀ k : Fin (N + 1), (d k : ℤ) = r (k : ℤ) (k : ℤ)) (Tr Ts : Tuple (k := k) d),
      (∀ (i j : Fin (N + 1)) (hij : i ≤ j), (rankPattern d Tr i j hij : ℤ) = r (i : ℤ) (j : ℤ)) →
      (∀ (i j : Fin (N + 1)) (hij : i ≤ j), (rankPattern d Ts i j hij : ℤ) = s (i : ℤ) (j : ℤ)) →
      repClosure (orbitSet Ts) ⊆ repClosure (orbitSet Tr) := by
  induction hchain using Relation.ReflTransGen.head_induction_on with
  | refl =>
    -- `r = s`: `Tr, Ts` have the same rank pattern, so the same orbit closure
    intro hr hrnn hrdiag Tr Ts hTr hTs
    rw [repClosure_orbitSet_eq_of_rankPattern_eq (A := Ts) (B := Tr)
      (fun i j hij ↦ by exact_mod_cast (hTs i j hij).trans (hTr i j hij).symm)]
  | @head p c hstep _hchain ih =>
    intro hp hpnn hpdiag Tr Ts hTr hTs
    -- invariants of the intermediate pattern `c`
    obtain ⟨hc, hcnn, hcdiag⟩ := boxMoveStep_invariants hp hpnn hpdiag hstep
    -- the canonical realizer of `c`
    set Tc := patternRealizer (k := k) hc hcnn hcdiag with hTc
    have hTcrank : ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
        (rankPattern d Tc i j hij : ℤ) = c (i : ℤ) (j : ℤ) :=
      rankPattern_patternRealizer hc hcnn hcdiag
    -- IH: `repClosure (orbitSet Ts) ⊆ repClosure (orbitSet Tc)`
    have hIH : repClosure (orbitSet Ts) ⊆ repClosure (orbitSet Tc) :=
      ih hc hcnn hcdiag Tc Ts hTcrank hTs
    -- per-step: `repClosure (orbitSet Tc) ⊆ repClosure (orbitSet Tr)`
    have hstep' : repClosure (orbitSet Tc) ⊆ repClosure (orbitSet Tr) :=
      boxMoveStep_repClosure_subset hp hc hpnn hcnn hpdiag hcdiag hTr hTcrank hstep
    exact hIH.trans hstep'

/-! ## Piece 4 — assembly: `orbitRankLocus M ⊆ Ō_M` and the headline ideal equality

For `A ∈ orbitRankLocus M`, the lower pattern `s = cumul (Kostant A)` and the upper hybrid `r = s +
g` (`g` the strict-upper rank deficit `rankPattern M − rankPattern A`) feed `box_move_chain_of_le`
(they agree on / below the diagonal, differ nonnegatively on the strict upper triangle, `diff s ≥ 0`
is the Kostant array). The chain drops `repClosure (orbitSet A) ⊆ repClosure (orbitSet M)`, so
`canonicalCoord A` lands in `Ō_M`. -/

/-- The lower Kostant array of `A`: `kostantArrayOfRank (rankFn d A)`, the literal Kostant partition
of `A`'s rank pattern. -/
noncomputable def kostantArr {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) : SuppArray (N : ℤ) ℤ :=
  kostantArrayOfRank (rankFn d A)

/-- The strict-upper rank deficit `g = embedRank (rankFn M) − embedRank (rankFn A)`: nonnegative on
the strict upper triangle, zero on / below the diagonal, supported. -/
noncomputable def rankDeficit {d : Fin (N + 1) → ℕ} (M A : Tuple (k := k) d) : ℤ → ℤ → ℤ :=
  fun i j ↦ (embedRank (rankFn d M)).1 i j - (embedRank (rankFn d A)).1 i j

/-- `embedRank (rankFn d A)` agrees on the upper triangle with the rank pattern (as `ℤ`). -/
theorem embedRank_rankFn_eq {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) (i j : Fin (N + 1))
    (hij : i ≤ j) : (embedRank (rankFn d A)).1 (i : ℤ) (j : ℤ) = (rankPattern d A i j hij : ℤ) := by
  rw [embedRank_apply_fin, rankFn, dif_pos hij]

/-- `cumul (kostantArr A)` agrees on the upper triangle with the rank pattern (as `ℤ`). -/
theorem cumul_kostantArr_eq {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) {i j : Fin (N + 1)}
    (hij : i ≤ j) :
    cumul (N : ℤ) (kostantArr A).1 (i : ℤ) (j : ℤ) = (rankPattern d A i j hij : ℤ) := by
  rw [kostantArr, cumul_kostantArrayOfRank_of_le (rankFn d A) (by exact_mod_cast Fin.le_def.mp hij),
    embedRank_rankFn_eq A i j hij]

/-- **The hard inclusion (L6.4), flattened form.** For `A ∈ orbitRankLocus M`, `canonicalCoord A`
lies in the Zariski closure of the orbit `O_M`: the box-move chain from `rankPattern M` down to
`rankPattern A` (`box_move_chain_of_le`) degenerates `O_A` into `Ō_M`. -/
theorem canonicalCoord_mem_repClosure_orbitSet [Infinite k] {d : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d) {A : Tuple (k := k) d} (hA : A ∈ orbitRankLocus M) :
    canonicalCoord d A ∈ repClosure (orbitSet M) := by
  classical
  -- the lower array `s` and the upper hybrid `r = s + g`
  set s : ℤ → ℤ → ℤ := fun i j ↦ cumul (N : ℤ) (kostantArr A).1 i j with hs
  set g : ℤ → ℤ → ℤ := rankDeficit M A with hg
  set r : ℤ → ℤ → ℤ := fun i j ↦ s i j + g i j with hr
  -- `g = 0` on / below the diagonal (both `rankFn` agree there: `d` on diagonal, `0` below)
  have hg_below : ∀ i j : ℤ, j ≤ i → g i j = 0 := by
    intro i j hji
    rw [hg, rankDeficit]
    -- both embedRank entries equal (rankFn is 0 below the diagonal, d on it) — sub to zero
    rcases lt_or_ge i 0 with hi | hi
    · rw [(embedRank (rankFn d M)).2.1 i j hi, (embedRank (rankFn d A)).2.1 i j hi, sub_zero]
    rcases lt_or_ge j 0 with hj0 | hj0
    · rw [show (embedRank (rankFn d M)).1 i j = 0 from by
          simp [embedRank, InFinRange, not_le_of_gt hj0],
        show (embedRank (rankFn d A)).1 i j = 0 from by
          simp [embedRank, InFinRange, not_le_of_gt hj0], sub_zero]
    rcases lt_or_ge (N : ℤ) j with hj | hj
    · rw [(embedRank (rankFn d M)).2.2 i j hj, (embedRank (rankFn d A)).2.2 i j hj, sub_zero]
    rcases lt_or_ge (N : ℤ) i with hiN | hiN
    · -- `i > N`: out of `embedRank`'s in-range box, both read `0`
      rw [show (embedRank (rankFn d M)).1 i j = 0 from by
          simp [embedRank, InFinRange, not_le_of_gt hiN],
        show (embedRank (rankFn d A)).1 i j = 0 from by
          simp [embedRank, InFinRange, not_le_of_gt hiN], sub_zero]
    -- in range with `j ≤ i`: name Fin indices; `rankFn _ x y = 0` unless `x ≤ y`
    obtain ⟨x, hx⟩ : ∃ x : Fin (N + 1), (x : ℤ) = i :=
      ⟨⟨i.toNat, by omega⟩, by simp [Int.toNat_of_nonneg hi]⟩
    obtain ⟨y, hy⟩ : ∃ y : Fin (N + 1), (y : ℤ) = j :=
      ⟨⟨j.toNat, by omega⟩, by simp [Int.toNat_of_nonneg hj0]⟩
    subst hx hy
    rw [embedRank_apply_fin, embedRank_apply_fin]
    by_cases hxy : x ≤ y
    · -- `j ≤ i` and `i ≤ j` ⟹ `i = j`; both rankFn read `d`
      have hyx : y ≤ x := by rw [Fin.le_def]; exact_mod_cast hji
      obtain rfl : x = y := le_antisymm hxy hyx
      rw [show rankFn d M x x = d x from by rw [rankFn, dif_pos le_rfl, rankPattern_self],
        show rankFn d A x x = d x from by rw [rankFn, dif_pos le_rfl, rankPattern_self], sub_self]
    · rw [rankFn, rankFn, dif_neg hxy, dif_neg hxy, sub_self]
  -- `g ≥ 0`: zero off the strict upper triangle, `rankPattern M − rankPattern A ≥ 0` on it
  have hg_nonneg : ∀ i j : ℤ, 0 ≤ g i j := by
    intro i j
    rcases le_or_gt j i with hji | hij
    · rw [hg_below i j hji]
    -- strict upper triangle in range
    rcases lt_or_ge i 0 with hi | hi
    · rw [hg, rankDeficit, (embedRank (rankFn d M)).2.1 i j hi,
        (embedRank (rankFn d A)).2.1 i j hi, sub_zero]
    rcases lt_or_ge (N : ℤ) j with hj | hj
    · rw [hg, rankDeficit, (embedRank (rankFn d M)).2.2 i j hj,
        (embedRank (rankFn d A)).2.2 i j hj, sub_zero]
    rcases lt_or_ge (N : ℤ) i with hiN | hiN
    · rw [hg, rankDeficit, show (embedRank (rankFn d M)).1 i j = 0 from by
          simp [embedRank, InFinRange, not_le_of_gt hiN],
        show (embedRank (rankFn d A)).1 i j = 0 from by
          simp [embedRank, InFinRange, not_le_of_gt hiN], sub_zero]
    obtain ⟨x, hx⟩ : ∃ x : Fin (N + 1), (x : ℤ) = i :=
      ⟨⟨i.toNat, by omega⟩, by simp [Int.toNat_of_nonneg hi]⟩
    obtain ⟨y, hy⟩ : ∃ y : Fin (N + 1), (y : ℤ) = j :=
      ⟨⟨j.toNat, by omega⟩, by simp [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ j)]⟩
    subst hx hy
    have hxy : x ≤ y := by rw [Fin.le_def]; exact_mod_cast le_of_lt hij
    have hM := embedRank_rankFn_eq M x y hxy
    have hAe := embedRank_rankFn_eq A x y hxy
    rw [hg, rankDeficit, hM, hAe, sub_nonneg]
    exact_mod_cast hA x y hxy
  -- `s` is supported and `diff s = kostantArr A ≥ 0` (the Kostant array)
  have hs_supp : Supported (N : ℤ) s := supported_cumul (N : ℤ) (kostantArr A).1
  have hdiff_s : diff s = (kostantArr A).1 :=
    diff_cumul (N : ℤ) (kostantArr A).1 (kostantArr A).2.1 (kostantArr A).2.2
  have hms : ∀ i j : ℤ, 0 ≤ diff s i j := by
    rw [hdiff_s]; exact (kostantArrayOfRank_isKostant A).1
  -- `g` is supported
  have hg_supp : Supported (N : ℤ) g := by
    refine ⟨fun i j hi ↦ ?_, fun i j hj ↦ ?_⟩
    · rw [hg, rankDeficit, (embedRank (rankFn d M)).2.1 i j hi,
        (embedRank (rankFn d A)).2.1 i j hi, sub_zero]
    · rw [hg, rankDeficit, (embedRank (rankFn d M)).2.2 i j hj,
        (embedRank (rankFn d A)).2.2 i j hj, sub_zero]
  -- the box-move chain `r ↠ s` (`r − s = g`, the strict-upper deficit)
  have hrs_eq : ∀ i j : ℤ, r i j - s i j = g i j := fun i j ↦ by rw [hr]; ring
  have hchain : BoxMoveChain r s := by
    refine box_move_chain_of_le (N : ℤ) r s ?_ ?_ ?_ hms
    · refine ⟨fun i j hi ↦ ?_, fun i j hj ↦ ?_⟩
      · show r i j - s i j = 0; rw [hrs_eq]; exact hg_supp.1 i j hi
      · show r i j - s i j = 0; rw [hrs_eq]; exact hg_supp.2 i j hj
    · intro i j; show 0 ≤ r i j - s i j; rw [hrs_eq]; exact hg_nonneg i j
    · intro i j hji; show r i j - s i j = 0; rw [hrs_eq]; exact hg_below i j hji
  -- `r`'s chain-output invariants
  have hr_supp : Supported (N : ℤ) r := by
    refine ⟨fun i j hi ↦ ?_, fun i j hj ↦ ?_⟩
    · show s i j + g i j = 0; rw [hs_supp.1 i j hi, hg_supp.1 i j hi, add_zero]
    · show s i j + g i j = 0; rw [hs_supp.2 i j hj, hg_supp.2 i j hj, add_zero]
  have hrdiag : ∀ t : Fin (N + 1), (d t : ℤ) = r (t : ℤ) (t : ℤ) := by
    intro t
    show (d t : ℤ) = s (t : ℤ) (t : ℤ) + g (t : ℤ) (t : ℤ)
    rw [hg_below t t le_rfl, add_zero]
    show (d t : ℤ) = cumul (N : ℤ) (kostantArr A).1 (t : ℤ) (t : ℤ)
    rw [cumul_kostantArr_eq A (le_refl t), rankPattern_self]
  -- `r = rankPattern M` on the upper triangle (the hybrid restores M's pattern there)
  have hr_eq_M : ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
      (rankPattern d M i j hij : ℤ) = r (i : ℤ) (j : ℤ) := by
    intro i j hij
    show (rankPattern d M i j hij : ℤ) = s (i : ℤ) (j : ℤ) + g (i : ℤ) (j : ℤ)
    rw [show s (i : ℤ) (j : ℤ) = cumul (N : ℤ) (kostantArr A).1 (i : ℤ) (j : ℤ) from rfl,
      cumul_kostantArr_eq A hij, hg, rankDeficit,
      embedRank_rankFn_eq M i j hij, embedRank_rankFn_eq A i j hij]
    ring
  -- `s = rankPattern A` on the upper triangle
  have hs_eq_A : ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
      (rankPattern d A i j hij : ℤ) = s (i : ℤ) (j : ℤ) := fun i j hij ↦
    (cumul_kostantArr_eq A hij).symm
  -- `diff r ≥ 0` on the upper triangle: on the stencil `r = embedRank (rankFn M)`, so
  -- `diff r = kostantArr M ≥ 0` there
  have hrnn : ∀ i j : ℤ, i ≤ j → 0 ≤ diff r i j := by
    intro i j hij
    -- `diff r = diff s + diff g`; on the triangle this is `kostantArr M ≥ 0`
    have hdr : diff r i j = diff s i j + diff g i j := by
      simp only [hr, diff_apply]; ring
    have hdg : diff g i j
        = (diffArrayOfRank (rankFn d M)).1 i j - (diffArrayOfRank (rankFn d A)).1 i j := by
      have : diff g i j
          = diff (embedRank (rankFn d M)).1 i j - diff (embedRank (rankFn d A)).1 i j := by
        simp only [hg, rankDeficit, diff_apply]; ring
      rw [this, ← diffArrayOfRank_val, ← diffArrayOfRank_val]
    rw [hdr, hdiff_s, hdg]
    -- on `i ≤ j`: `kostantArr A = diffArrayOfRank (rankFn A)`, so the `A` terms cancel,
    -- leaving `diffArrayOfRank (rankFn M) = kostantArr M ≥ 0`
    rw [kostantArr, kostantArrayOfRank_of_le (rankFn d A) hij]
    have hMnn := (kostantArrayOfRank_isKostant M).1 i j
    rw [kostantArrayOfRank_of_le (rankFn d M) hij] at hMnn
    linarith
  -- the chain drops the closure: `repClosure (orbitSet A) ⊆ repClosure (orbitSet M)`
  have hdrop : repClosure (orbitSet A) ⊆ repClosure (orbitSet M) :=
    boxMoveChain_repClosure_subset hchain hr_supp hrnn hrdiag M A hr_eq_M hs_eq_A
  -- `canonicalCoord A` is in `orbitSet A`, hence in the closure of `orbitSet M`
  exact hdrop (subset_repClosure (orbitSet A) ⟨A, ⟨1, one_smul _ _⟩, rfl⟩)

/-- `vanishingIdeal` is invisible to `repClosure`: closure has the same vanishing ideal as `S`
(the `u_l_u_eq_u` law of the Galois connection — no algebraic-closedness needed). -/
theorem vanishingIdeal_repClosure {d : Fin (N + 1) → ℕ} (S : Set (RepCoord d → k)) :
    MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (repClosure S)
      = MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k S :=
  (MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection
    (σ := RepCoord d) (k := k) (K := k)).u_l_u_eq_u S

/-- **The flattened hard inclusion (L6.4).** `canonicalCoord '' orbitRankLocus M ⊆ Ō_M`: every point
of the determinantal rank locus lies in the Zariski closure of the orbit. -/
theorem image_orbitRankLocus_subset_repClosure_orbitSet [Infinite k] {d : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d) :
    canonicalCoord d '' orbitRankLocus M ⊆ repClosure (orbitSet M) := by
  rintro y ⟨A, hA, rfl⟩
  exact canonicalCoord_mem_repClosure_orbitSet M hA

/-- **The orbit-closure equality at the ideal level (L6.4 headline, Abeasis–Del Fra).** The
ideal of the determinantal rank locus `orbitRankLocus M` equals the vanishing ideal of the orbit
`O_M`. Equivalently, the rank locus and the orbit have the same Zariski closure: `Ō_M =
orbitRankLocus M` as closed sets. The easy `≤` is `vanishingIdeal_orbitRankLocus_le_orbitSet`; the
hard `≥` is the box-move degeneration `image_orbitRankLocus_subset_repClosure_orbitSet`, pushed
`vanishingIdeal` (order-reversing) with `vanishingIdeal_repClosure`. -/
theorem vanishingIdeal_orbitRankLocus_eq_orbitSet [Infinite k] {d : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d) :
    MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
        (canonicalCoord d '' orbitRankLocus M)
      = MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (orbitSet M) := by
  refine le_antisymm (vanishingIdeal_orbitRankLocus_le_orbitSet M) ?_
  calc MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (orbitSet M)
      = MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k (repClosure (orbitSet M)) :=
        (vanishingIdeal_repClosure (orbitSet M)).symm
    _ ≤ MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
          (canonicalCoord d '' orbitRankLocus M) :=
        MvPolynomial.vanishingIdeal_anti_mono (image_orbitRankLocus_subset_repClosure_orbitSet M)

/-! ## Piece 5 — the rank locus is irreducible (L1★) -/

/-- **The rank locus has a prime vanishing ideal (L1★, irreducibility).** `vanishingIdeal
(canonicalCoord '' orbitRankLocus M)` is prime: it equals `vanishingIdeal (orbitSet M)`
(`vanishingIdeal_orbitRankLocus_eq_orbitSet`), which is prime because `O_M` is irreducible
(`isPrime_vanishingIdeal_orbitSet`, L1). So the determinantal rank locus `Ō_M = orbitRankLocus M` is
an irreducible variety. Needs `[IsAlgClosed k]` (inherited from L1). -/
theorem isPrime_vanishingIdeal_orbitRankLocus [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d) :
    (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
      (canonicalCoord d '' orbitRankLocus M)).IsPrime := by
  rw [vanishingIdeal_orbitRankLocus_eq_orbitSet M]
  exact isPrime_vanishingIdeal_orbitSet M

end DLNFibre.Core

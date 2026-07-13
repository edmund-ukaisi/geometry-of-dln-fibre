import DLNFibre.DLN.RLCT.Validate.RouteMSJDecorated
import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedCharge
import DLNFibre.DLN.RLCT.Validate.RouteMSJAdmEncoding
import DLNFibre.DLN.RLCT.Validate.RouteMSJTailProd
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJAdm` — the A2 admissibility predicate `adm` (fork (B))

**Threads `genm-sj5-desc3` (Piece #3) + `genm-sj5-desc4` (FaithfulSJAt strengthen).** The admissibility
predicate (fork (B), OPT-A; `faithfulsj-design §★★★`) the `DecoratedDescent` spine
(`RouteMSJDecoratedRec`) quantifies over:

    adm n M D  :=  genuineCarrier D  ∧  FaithfulSJAt D

(the earlier `a = 0 ∨ b = 0 ∨ …` corank disjunct was REMOVED as UNSOUND — it bypassed FaithfulSJAt's β
threshold on a degenerate binding cut, admitting a divergent `jac ≡ 0` decoration; `genm-admfix`, 2026-07-13.)
`FaithfulSJAt` is the `(S,J)` resolution-state base-invariant (below): either the smooth free-block leaf
(`d = 0` and the carrier loss IS the Frobenius sum-of-squares — the HEq-free OBSERVABLE form) or a
resolved corner (`1 ≤ d`) with a dehomogenised generator `i₀` carrying (α) `pSimultaneous`,
(β) `½·minAdm M ≤ monomialThreshold`, (γ') the clean route-A LEAF FORM (`decLoss = commonDivisor(u)² ·
frobSq (Γ·Z)`, `Z·Zᵀ ≽ c·1`, `minAdm M ≤ a·n`). `#4` (`DecoratedBaseHyp`) CONSUMES it
(`RouteMSJBaseHyp.decoratedBaseHyp_faithful`, sorry-free); `#5` PRESERVES it.

## Fidelity status

* **Q3 (α / valuation) — LOCKED.** `admValuation` = `d = 0`-carrier vacuity OR `pSimultaneous` on
  `D.carrier.supp` (= `FaithfulSJAt`'s α); the two regression tests exercise the `pSimultaneous` disjunct.
* **Q2 (a, b) — LOCKED.** `a, b` are `M`'s binding-cut corank widths (`t★ = bindingCut M`, banked
  `exists_binding_cut`).
* **Q1 (`genuineCarrier`) — LOCKED, form (i) + `MeasurePreserving`.** Stores `Params M` via a
  MEASURE-PRESERVING equiv `e : D.Z ≃ᵐ Params M` (MP needed for the base CoV), `ctx`/`dom` reading
  `prod M (e z)`.
* **FaithfulSJAt (OPT-A, S2-settled §★★★) — LANDED (def + htriv + `#4`).** The `d = 0` disjunct is the
  HEq-free observable-loss form (extractable, `#4` reads it via `genuineCarrier` + `eqRec_fun_apply_eqRec`);
  the `d ≥ 1` disjunct carries the clean route-A leaf-form γ' (the weighted-`δ` form is transient within a
  peel, not in the stable carrier). The bare units bound alone is dropped (vacuous). `#5`-preservability of
  γ' + `minAdm M ≤ a·n` = cover's Q1.

`htriv` (`adm_trivial`) proved (trivial = the `d = 0` observable disjunct, `loss_ofMatrix`). `genm-sj5-cover`
audits `#5` preservation. Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators ENNReal Matrix
open MeasureTheory

variable {L : ℕ}

/-! ## Q1 — the genuine-carrier clause (LOCKED, form (i), cover-decided) -/

/-- **The genuine-carrier clause (form (i), cover-decided UPDATE-937).** The decoration's deeper parameter
space is the honest FULL layer-product tuple of the EXACT chain `M`: there is a measure-equiv
`e : D.Z ≃ᵐ Params M`, the domain is the pulled-back parameter box, and the carrier's active inputs read
off the layer product `prod M (e z)` entry-by-entry. The deeper TAIL product (which `#144`/`#2`/the leaf
consume) is DERIVED from `A = e z`, not stored. Uses a **measure-equiv** (not a type-equality) to dodge
`HEq`; the `ν`-alignment (`D.ν = Fin (M 0) × Fin (M (last))`, the product index type) is what lets the
`ctx` clause be stated. Trivial (`e = id`, `ν` literal) satisfies it (`genuineCarrier_trivial`), pinning
`M`'s EXACT dims (intermediates `= M`'s values, not a free product). -/
def genuineCarrier {M : Fin (L + 1) → ℕ} (D : SJDecoration M) : Prop :=
  letI := D.mZ
  D.ζ = Unit ∧
  ∃ (hν : D.ν = (Fin (M 0) × Fin (M (Fin.last L)))) (e : D.Z ≃ᵐ Params M),
    MeasurePreserving e ∧
    D.dom = e ⁻¹' (paramsBoxM M 1) ∧
    ∀ z : D.Z, (hν ▸ (D.ctx z).2) = fun ik => prod M (e z) ik.1 ik.2

/-! ## Q3 — the valuation clause (`pSimultaneous`, LOCKED) -/

/-- **The valuation clause (`p = 0`, the (T) simultaneous form).** Either the decoration is the
FULLY-UNRESOLVED free block (`d = 0` AND the carrier is the identity `ofMatrix` at the layer product —
the only `d = 0` decoration the descent produces, `trivial`), or some generator `i₀` attains the shared
divisor minimum at EVERY exceptional divisor `ℓ` — i.e. `i₀` is a unit at every critical divisor. The
second disjunct is `pSimultaneous` on the carrier support (`admValuation_iff_pSimultaneous`), the
hypothesis the terminal `sjLoss_terminal_lintegral_lt_top` consumes, and the faithful encoding of
"`Crit(D)` including intersection rays ⟹ (T)" (cert §6-C1). The `d = 0 ∧ carrier = ofMatrix` disjunct
(vs a bare `d = 0`) EXCLUDES the divergent degenerate-`coeff` `d = 0` carriers (FLAG-1 fix): the base
must genuinely prove finiteness, so `d = 0` admissibility is pinned to the free-block `ofMatrix` form
(whose loss is `frobSq (prod M)`). -/
def admValuation {M : Fin (L + 1) → ℕ} (D : SJDecoration M) : Prop :=
  (D.d = 0 ∧ HEq D.carrier (SJLinGenState.ofMatrix (M 0) (M (Fin.last L)))) ∨
    ∃ i₀ : D.ι, ∀ (j : D.ι) (ℓ : Fin D.d), D.carrier.supp i₀ ℓ ≤ D.carrier.supp j ℓ

/-- **`admValuation` is the free-block base OR `pSimultaneous` on the carrier support** (given
`Nonempty D.ι`): the total `≤`-at-every-`ℓ` disjunct is equivalent to "`i₀` attains the shared min
`sharedDivisorExp` everywhere". The bridge to the banked `RouteMSJAdmEncoding` (P)/(T) machinery. -/
theorem admValuation_iff_pSimultaneous {M : Fin (L + 1) → ℕ} (D : SJDecoration M)
    [Nonempty D.ι] :
    letI := D.fι
    admValuation D ↔
      ((D.d = 0 ∧ HEq D.carrier (SJLinGenState.ofMatrix (M 0) (M (Fin.last L)))) ∨
        pSimultaneous D.carrier.supp) := by
  letI := D.fι
  unfold admValuation pSimultaneous
  refine or_congr_right ?_
  constructor
  · rintro ⟨i₀, hi₀⟩
    refine ⟨i₀, fun ℓ => le_antisymm ?_ (sharedDivisorExp_le _ i₀ ℓ)⟩
    unfold sharedDivisorExp
    exact Finset.le_inf' _ _ (fun j _ => hi₀ j ℓ)
  · rintro ⟨i₀, hi₀⟩
    refine ⟨i₀, fun j ℓ => ?_⟩
    rw [hi₀ ℓ]
    exact sharedDivisorExp_le _ j ℓ

/-! ## Q2 — the binding-cut corank widths `a, b` (LOCKED) -/

/-- **`M`'s canonical binding cut** `t★` — the least legal cut `u ≤ min(M₀,M₁)` achieving the `minAdm`
peel-fold `minAdm M = peelCharge M u + minAdm (redChain u M)` (banked `exists_binding_cut`). Defined for
`≥ 3`-width chains; `0` for the degenerate one/two-width chains (which carry no corank-peel). -/
def bindingCut : {n : ℕ} → (M : Fin (n + 1) → ℕ) → ℕ
  | 0, _ => 0
  | 1, _ => 0
  | (_ + 2), M => Nat.find (exists_binding_cut M)

/-- **The front-block row-rise `a = M₀ − t★`** at `M`'s binding cut (`0` iff the peel is a no-op there). -/
def admCorankA {n : ℕ} (M : Fin (n + 1) → ℕ) : ℕ := M 0 - bindingCut M

/-- **The front-block column-rise `b = M₁ − t★`** at `M`'s binding cut. -/
def admCorankB {n : ℕ} (M : Fin (n + 1) → ℕ) : ℕ := M 1 - bindingCut M

/-! ## The carried γ' provenance clause — the units-FREE Γ×tail split (`gammaPrimeClause`)

The `d ≥ 1` provenance clause of `FaithfulSJAt`, in the units-FREE form (P0 cert, units DROPPED). The
deeper space splits `Z ≃ᵐ (front block : Fin a → Fin (M 1) → ℝ) × Params (dropHead M)` — a front free
block over `Params (dropHead M)`, the head-dropped **tail** parameter space (`RouteMSJTailProd`). The
tail matrix is `Z_tail := prod (dropHead M)`, the genuine suffix layer product, and each residual is the
`ρ`-indexed entry of `Γ(z) · Z_tail(r)`. The **tie** `Z_tail = prod (dropHead M)` is what forces
`Z_tail ≡ 1` (invertible) at the width-2 base (`tailProd_width2`), so the DROPPED units bound is DERIVED
there (`c = 1`) — the literal free-`R` untied form is UNSOUND (decorrelated-confirmed, `genm-sj4-base`
`codex/ztail-tie-answer.md`: it admits a divergent `Z_tail = diag(1,0)` witness). Matched on `L` so
`dropHead` (defined for width `≥ 2`) type-checks: the `L = 0` (width-1) arm is `False` — a width-1 chain
has no layers, hence no resolved corner (never consumed; the driver's `n = 0` case is vacuous). -/
def gammaPrimeClause : {L : ℕ} → {M : Fin (L + 1) → ℕ} → (D : SJDecoration M) → D.ι → Prop
  | 0, _, _, _ => False
  | L + 1, M, D, i₀ =>
      letI := D.mZ; letI := D.fν; letI := D.fι; letI : Nonempty D.ι := ⟨i₀⟩
      ∃ (a : ℕ) (eΓ : D.Z ≃ᵐ (Fin a → Fin (M 1) → ℝ) × Params (dropHead M))
        (ρ : D.ι ≃ (Fin a × Fin (M (Fin.last (L + 1))))),
        MeasurePreserving eΓ ∧
        D.dom = eΓ ⁻¹' (matBox a (M 1) 1 ×ˢ paramsBoxM (dropHead M) 1) ∧
        minAdm M ≤ a * M 1 ∧
        ∀ (z : D.Z) (i : D.ι),
          D.carrier.residual (D.ctx z).1 (D.ctx z).2 i
            = rmatMul (eΓ z).1 (prod (dropHead M) (eΓ z).2) (ρ i).1 (ρ i).2

/-! ## `FaithfulSJAt` — the `(S,J)` resolution-state base-invariant (OPT-A, cover `faithfulsj-design`) -/

/-- **The `(S,J)` resolution-state base-invariant `FaithfulSJAt`** (OPT-A; cover `faithfulsj-design §★★★`,
S2-settled, decorrelated-EARNED). Either the smooth free-block leaf (`d = 0`, and the carrier loss IS the
Frobenius sum-of-squares of the active variables — the HEq-free OBSERVABLE form, so `#4` reads it without
type-constructor injectivity), or a resolved corner (`1 ≤ D.d`) with a dehomogenised generator `i₀`
satisfying: **(α)** `i₀` attains the shared-divisor minimum at every `ℓ` (`pSimultaneous`); **(β)** the
monomial threshold dominates `½·minAdm M`; **(γ')** the ROUTE-A LEAF FORM (the stable CLEAN identity, S2
uniform-support): a free active block via a measure iso `eΓ : D.Z ≃ᵐ (Fin a → Fin n → ℝ)` with
`dom = eΓ ⁻¹' matBox a n 1`, a deeper tail `Z` with `Z·Zᵀ ≽ c·1` (`c > 0` — the units-sector interface,
derived-trivial `Z = I` at width-2), the free-block dimension bound `minAdm M ≤ a·n` (width-general `≤`,
NOT the width-2-only `=`), and the CLEAN loss decomposition `decLoss u z = commonDivisor(u)² ·
frobSq ((eΓ z)·Z)`. The weighted-`δ` form is only transient within a peel; the STABLE carrier is clean
(§★★★). `DecoratedBaseHyp` (#4) CONSUMES γ' via `decoratedBase_routeA_of_leafForm`; the peel (#5)
PRESERVES it (`Z` z-dependence + preservability = cover's Q1). -/
def FaithfulSJAt {M : Fin (L + 1) → ℕ} (D : SJDecoration M) : Prop :=
  (D.d = 0 ∧ (letI := D.fν; letI := D.fι;
      ∀ (z : D.ζ) (x : D.ν → ℝ) (u : Fin D.d → ℝ), D.carrier.loss u z x = ∑ v, (x v) ^ 2)) ∨
    (1 ≤ D.d ∧ ∃ i₀ : D.ι,
      -- (α) `pSimultaneous`: `i₀` attains the shared-divisor minimum everywhere.
      (letI := D.fι; ∀ (j : D.ι) (ℓ : Fin D.d), D.carrier.supp i₀ ℓ ≤ D.carrier.supp j ℓ) ∧
      -- (β) the monomial threshold dominates `½·minAdm M`.
      (letI := D.fι; letI : Nonempty D.ι := ⟨i₀⟩;
        (minAdm M : ℝ≥0∞) / 2 ≤ monomialThreshold D.d (sharedDivisorExp D.carrier.supp) D.jac) ∧
      -- (δ≡0) UNIFORM support (`residualSupport ≡ 0`): a CARRIED support property (#5 establishes it via
      -- per-peel corank integration; #4 consumes it). NOT a `genuineCarrier` consequence (that gives only
      -- spanning; the δ=0 SUBFAMILY spanning needs `residualSupport ≡ 0`). §★★★ / UPDATE-953.
      (letI := D.fι; letI : Nonempty D.ι := ⟨i₀⟩;
        ∀ (i : D.ι) (ℓ : Fin D.d), D.carrier.supp i ℓ = sharedDivisorExp D.carrier.supp ℓ) ∧
      -- (γ') route-A leaf form, PROVENANCE (units-FREE Γ×tail split, `gammaPrimeClause`): the residuals
      -- ARE the `ρ`-indexed entries of the front free block `Γ(z) = (eΓ z).1` times the deeper tail
      -- `Z_tail(r) = prod (dropHead M) r`. NO units bound (DROPPED, P0); #4 DERIVES it at width-2 via the
      -- tie `Z_tail = prod (dropHead M) ≡ 1` (`tailProd_width2`). #4 then DERIVES the clean loss
      -- `decLoss = commonDivisor² · frobSq (Γ·Z_tail)` from this + δ≡0 (`decLoss_commonDivisor_factor`).
      gammaPrimeClause D i₀)

/-! ## The admissibility predicate `adm` (fork (B), OPT-A) -/

/-- **The A2 admissibility predicate (fork (B), OPT-A).** `adm n M D` iff the carrier is genuine
(`genuineCarrier`, form (i)) AND the resolution-state base-invariant `FaithfulSJAt D` holds (which
STRENGTHENS `admValuation`: its α clause IS `admValuation`'s `pSimultaneous`, plus the β threshold + γ
residual-coercivity the coupled base RLCT needs). (An earlier `a = 0 ∨ b = 0` corank disjunct was REMOVED
as UNSOUND — it bypassed the β threshold on a degenerate binding cut; `genm-admfix`.) This is the predicate
`DecoratedDescent` (`RouteMSJDecoratedRec`) quantifies over: `htriv`
(trivial admissible, `adm_trivial`), `DecoratedStepHyp` (peel-closure PRESERVES `FaithfulSJAt`, `#5`), and
`DecoratedBaseHyp` (leaf finiteness CONSUMES `FaithfulSJAt`, `#4`). -/
def adm (n : ℕ) (M : Fin (n + 1) → ℕ) (D : SJDecoration M) : Prop :=
  genuineCarrier D ∧ FaithfulSJAt D

/-! ## `htriv` — the trivial decoration is admissible -/

/-- **The trivial decoration is genuine (form (i), `e = id`).** Its deeper space IS `Params M`
literally, `ν` is the product index type, and `ctx` reads the layer product `prod M z`. -/
theorem genuineCarrier_trivial (M : Fin (L + 1) → ℕ) :
    genuineCarrier (SJDecoration.trivial M) := by
  refine ⟨rfl, rfl, MeasurableEquiv.refl (Params M), ?_, ?_, fun z => rfl⟩
  · exact MeasurePreserving.id (volume : Measure (Params M))
  · ext x; rfl

/-- **`htriv` — the trivial decoration is admissible for every chain.** The genuine-carrier clause holds
(`genuineCarrier_trivial`); `FaithfulSJAt` holds via the `d = 0` observable-loss disjunct — the trivial
`ofMatrix` carrier's loss IS the Frobenius sum-of-squares of the active variables (`loss_ofMatrix` +
`Fintype.sum_prod_type`). This is the `DecoratedDescent` leg `∀ n M, adm n M (trivial M)`. -/
theorem adm_trivial (n : ℕ) (M : Fin (n + 1) → ℕ) : adm n M (SJDecoration.trivial M) := by
  have key : ∀ (u : Fin 0 → ℝ) (Y : Fin (M 0) × Fin (M (Fin.last n)) → ℝ),
      (SJLinGenState.ofMatrix (M 0) (M (Fin.last n))).loss u () Y = ∑ v, (Y v) ^ 2 := by
    intro u Y
    rw [SJLinGenState.loss_ofMatrix]
    simp only [frobSq]
    rw [Fintype.sum_prod_type]
  refine ⟨genuineCarrier_trivial M, Or.inl ⟨rfl, fun z x u => ?_⟩⟩
  obtain ⟨⟩ := z
  exact key u x

/-! ## Regression test 1 — the rank-1 `(3,3,2,2) →_{t=2} (2,2,2)` carrier is ADMITTED (`p = 0`)

The reduced `(2,2,2)` top component at `rank Zdeep = 1` carries a SURVIVING corank unit (`ρ = b = 1`,
`p = 0`): after the peel there is one exceptional divisor `u₀`, and the corank generator is a unit at it
(support `0`) while the pivot generator carries `u₀`. The valuation clause ADMITS such a carrier. -/

/-- A minimal decoration realizing a chosen carrier support (dummy deeper data: no active variables, so
the residual is `≡ 0` and trivially measurable). Used only to exercise the valuation clause. -/
noncomputable def suppDecoration {L : ℕ} (M : Fin (L + 1) → ℕ) {J : Type} [Fintype J] {d : ℕ}
    (s : SJSupport J d) (jc : Fin d → ℕ) : SJDecoration M where
  d := d
  ζ := Unit
  ν := Fin 0
  ι := J
  fν := inferInstance
  fι := inferInstance
  carrier := ({ supp := s, coeff := fun _ _ _ => (0 : ℝ) } : SJLinGenState Unit (Fin 0) J d)
  jac := jc
  Z := Params M
  mZ := inferInstance
  ctx := fun _ => ((), fun _ => (0 : ℝ))
  dom := Set.univ
  residualMeas := by
    intro i
    simp only [SJLinGenState.residual, Finset.univ_eq_empty, Finset.sum_empty]
    exact measurable_const

/-- The rank-1 corank-survival support: one exceptional divisor `u₀`; generator `0` (the surviving corank
row) is a unit (`supp = 0`), generator `1` (the pivot) carries `u₀` (`supp = 1`). The `(2,2,2)` `p = 0`
witness. -/
def suppRank1 : SJSupport (Fin 2) 1 := ![![0], ![1]]

/-- **REGRESSION TEST 1 — the rank-1 `(2,2,2)` carrier is ADMITTED by the valuation clause.** The surviving
corank generator (`0`) is a unit at the exceptional divisor, so it attains the shared min everywhere. -/
theorem regression_rank1_admitted :
    admValuation (suppDecoration (![2, 2, 2] : Fin 3 → ℕ) suppRank1 ![3]) := by
  refine Or.inr ?_
  change ∃ i₀ : Fin 2, ∀ (j : Fin 2) (ℓ : Fin 1), suppRank1 i₀ ℓ ≤ suppRank1 j ℓ
  exact ⟨0, by decide⟩

/-! ## Regression test 2 — the fresh-disjoint `x² + y²` carrier is REJECTED (`(P) ⇏ (T)`)

The support `{(1,0),(0,1)}` (`suppFreshTwo`, banked) has NO single generator that is a unit at both
divisors — the `(P) ⇏ (T)` gap (cert §6-C1). The valuation clause REJECTS it (as a terminal), so it is
inadmissible unless the intersection `{x = y = 0}` is refined. Below `admValuation` fails on any decoration
carrying `suppFreshTwo`. -/

/-- **REGRESSION TEST 2 — the `x² + y²` carrier is REJECTED by the valuation clause.** No generator is a
unit at BOTH divisors: this is `¬ pSimultaneous suppFreshTwo` (banked `suppFreshTwo_not_pSimultaneous`),
transported to `¬ admValuation`. So the fresh-disjoint terminal is inadmissible until refined. -/
theorem regression_freshTwo_rejected :
    ¬ admValuation (suppDecoration (![2, 2, 2] : Fin 3 → ℕ) suppFreshTwo ![0, 0]) := by
  rintro (⟨h2, _⟩ | h)
  · exact absurd h2 (by decide)
  · revert h
    change ¬ ∃ i₀ : Fin 2, ∀ (j : Fin 2) (ℓ : Fin 2), suppFreshTwo i₀ ℓ ≤ suppFreshTwo j ℓ
    decide

end DLNFibre.DLN.RLCT

import DLNFibre.DLN.RLCT.Validate.RouteMSJDecorated
import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedCharge
import DLNFibre.DLN.RLCT.Validate.RouteMSJAdmEncoding

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJAdm` — the A2 admissibility predicate `adm` (fork (B))

**Thread `genm-sj5-desc3`, Piece #3 (the `adm` DEF).** The valuation-predicate admissibility (fork (B),
cert §10/§10.1, controller UPDATE-936) the `DecoratedDescent` spine (`RouteMSJDecoratedRec`) quantifies over:

    adm n M D  :=  genuineCarrier D  ∧  (a = 0 ∨ b = 0 ∨ admValuation D)

with `a = M₀ − t★`, `b = M₁ − t★` the front-block corank widths at `M`'s binding cut `t★`, and

    admValuation D  :=  ∃ i₀, ∀ j ℓ, D.carrier.supp i₀ ℓ ≤ D.carrier.supp j ℓ

the **(T) simultaneous** condition (`pSimultaneous` on the carrier support): ONE generator is a unit at
every critical divisor — the `p = 0` transversality condition, faithful to "`Crit(D)` incl. intersection
rays ⟹ (T)" (cert §6-C1). It correctly REJECTS the fresh-disjoint `x²+y²` carrier (the `(P) ⇏ (T)` gap,
banked `suppFreshTwo_not_pSimultaneous`); the weaker `pDivisorwise` would wrongly ADMIT it.

## Fidelity status (per controller answers)

* **Q3 (valuation clause) — LOCKED.** `admValuation` = empty-`Crit` vacuity (`d = 0`) OR `pSimultaneous` on
  `D.carrier.supp`; the two regression tests exercise the `pSimultaneous` disjunct.
* **Q2 (a, b) — LOCKED.** `a, b` are `M`'s binding-cut corank widths (`t★ = bindingCut M`, the least binding
  cut, banked `exists_binding_cut`). Functions of `M` alone.
* **Q1 (`genuineCarrier`) — LOCKED, form (i)** (cover-decided). Stores the FULL `Params M` via a measure-equiv
  `e : D.Z ≃ᵐ Params M` (NOT type-equality — dodges `HEq`), with `ctx`/`dom` reading the layer product
  `prod M (e z)`; the deeper TAIL that `#144`/`#2`/the leaf consume is DERIVED from `A = e z`, not stored.
  `htriv` (`adm_trivial`) is proved (trivial: `e = id`, `d = 0`).

`genm-sj5-cover` audits the fidelity. Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators
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
    D.dom = e ⁻¹' (paramsBoxM M 1) ∧
    ∀ z : D.Z, (hν ▸ (D.ctx z).2) = fun ik => prod M (e z) ik.1 ik.2

/-! ## Q3 — the valuation clause (`pSimultaneous`, LOCKED) -/

/-- **The valuation clause (`p = 0`, the (T) simultaneous form).** Either there are NO exceptional
divisors (`d = 0`, so `Crit D = ∅` and "`∀ η ∈ Crit`" is vacuously true), or some generator `i₀` attains
the shared divisor minimum at EVERY exceptional divisor `ℓ` — i.e. `i₀` is a unit at every critical
divisor. The second disjunct is `pSimultaneous` on the carrier support
(`admValuation_iff_pSimultaneous`). It is the hypothesis the terminal `sjLoss_terminal_lintegral_lt_top`
consumes, and the faithful encoding of "`Crit(D)` including intersection rays ⟹ (T)" (cert §6-C1); the
`d = 0` disjunct is the empty-`Crit` vacuity (a free block carries no critical divisor). -/
def admValuation {M : Fin (L + 1) → ℕ} (D : SJDecoration M) : Prop :=
  D.d = 0 ∨ ∃ i₀ : D.ι, ∀ (j : D.ι) (ℓ : Fin D.d), D.carrier.supp i₀ ℓ ≤ D.carrier.supp j ℓ

/-- **`admValuation` is the empty-`Crit` vacuity OR `pSimultaneous` on the carrier support** (given
`Nonempty D.ι`): the total `≤`-at-every-`ℓ` disjunct is equivalent to "`i₀` attains the shared min
`sharedDivisorExp` everywhere". The bridge to the banked `RouteMSJAdmEncoding` (P)/(T) machinery. -/
theorem admValuation_iff_pSimultaneous {M : Fin (L + 1) → ℕ} (D : SJDecoration M)
    [Nonempty D.ι] :
    letI := D.fι
    admValuation D ↔ (D.d = 0 ∨ pSimultaneous D.carrier.supp) := by
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

/-! ## The admissibility predicate `adm` (fork (B)) -/

/-- **The A2 admissibility predicate (fork (B), the valuation-predicate).** `adm n M D` iff the carrier is
genuine (`genuineCarrier`, form (i)) AND either the binding-cut front block is degenerate
(`a = 0 ∨ b = 0`, the no-op peel) or the `p = 0` valuation holds (`admValuation`). This is the predicate
`DecoratedDescent` (`RouteMSJDecoratedRec`) quantifies over: `htriv` (trivial admissible, `adm_trivial`),
`DecoratedStepHyp` (peel-closure `= #144`), and `DecoratedBaseHyp` (leaf finiteness `= route A`). -/
def adm (n : ℕ) (M : Fin (n + 1) → ℕ) (D : SJDecoration M) : Prop :=
  genuineCarrier D ∧ (admCorankA M = 0 ∨ admCorankB M = 0 ∨ admValuation D)

/-! ## `htriv` — the trivial decoration is admissible -/

/-- **The trivial decoration is genuine (form (i), `e = id`).** Its deeper space IS `Params M`
literally, `ν` is the product index type, and `ctx` reads the layer product `prod M z`. -/
theorem genuineCarrier_trivial (M : Fin (L + 1) → ℕ) :
    genuineCarrier (SJDecoration.trivial M) := by
  refine ⟨rfl, rfl, MeasurableEquiv.refl (Params M), ?_, fun z => rfl⟩
  ext x; rfl

/-- **`htriv` — the trivial decoration is admissible for every chain.** The genuine-carrier clause holds
(`genuineCarrier_trivial`); the valuation clause holds vacuously (`d = 0`: no exceptional divisors, empty
`Crit`). This is the `DecoratedDescent` leg `∀ n M, adm n M (SJDecoration.trivial M)`. -/
theorem adm_trivial (n : ℕ) (M : Fin (n + 1) → ℕ) : adm n M (SJDecoration.trivial M) :=
  ⟨genuineCarrier_trivial M, Or.inr (Or.inr (Or.inl rfl))⟩

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
  show (1 : ℕ) = 0 ∨ ∃ i₀ : Fin 2, ∀ (j : Fin 2) (ℓ : Fin 1), suppRank1 i₀ ℓ ≤ suppRank1 j ℓ
  exact Or.inr ⟨0, by decide⟩

/-! ## Regression test 2 — the fresh-disjoint `x² + y²` carrier is REJECTED (`(P) ⇏ (T)`)

The support `{(1,0),(0,1)}` (`suppFreshTwo`, banked) has NO single generator that is a unit at both
divisors — the `(P) ⇏ (T)` gap (cert §6-C1). The valuation clause REJECTS it (as a terminal), so it is
inadmissible unless the intersection `{x = y = 0}` is refined (`a = 0 ∨ b = 0` does not fire on a genuine
`a, b > 0` peel). Below `admValuation` fails on any decoration carrying `suppFreshTwo`. -/

/-- **REGRESSION TEST 2 — the `x² + y²` carrier is REJECTED by the valuation clause.** No generator is a
unit at BOTH divisors: this is `¬ pSimultaneous suppFreshTwo` (banked `suppFreshTwo_not_pSimultaneous`),
transported to `¬ admValuation`. So the fresh-disjoint terminal is inadmissible until refined. -/
theorem regression_freshTwo_rejected :
    ¬ admValuation (suppDecoration (![2, 2, 2] : Fin 3 → ℕ) suppFreshTwo ![0, 0]) := by
  show ¬ ((2 : ℕ) = 0 ∨ ∃ i₀ : Fin 2, ∀ (j : Fin 2) (ℓ : Fin 2),
    suppFreshTwo i₀ ℓ ≤ suppFreshTwo j ℓ)
  decide

end DLNFibre.DLN.RLCT

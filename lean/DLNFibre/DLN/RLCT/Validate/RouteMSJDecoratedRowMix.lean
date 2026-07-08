import DLNFibre.DLN.RLCT.Validate.RouteMSJDecorated

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedRowMix` — the clear-first row-mix at the decoration level

**Thread `genm-sjbuild3`, R1-UPPER.** The (a) half of the decorated peel `decorated_peel_step` — the
clear-first scalar Schur elimination lifted from the generator carrier (`RouteMSJLinGen`) to a whole
`SJDecoration` (`RouteMSJDecorated`), sitting beside the already-banked (b) `radialAttach` half.

## What lands here

* **`SJDecoration.rowMix`** — the decoration transform: mix the generators by a matrix `R : ι' → ι → ℝ`
  onto a fresh (constant) target support `s`, changing ONLY the generator index type (`ι ↦ ι'`) and the
  carrier (`carrier ↦ carrier.rowMix R (fun _ ↦ s)`, banked `SJLinGenState.rowMix`); the resolution
  state — the exceptional count `d`, the accumulated Jacobian `jac`, the deeper space `Z`, the context
  `ctx`, and the chart domain `dom` — is UNCHANGED. This is the `Z`-independent det-1 unit
  block-elimination (`step3_blockFactor`, `RouteMSJStep3`) acting on the generators.

* **`SJDecoration.rowMix_decLoss`** — the decorated loss under the row-mix, at a FRESH block (constant
  support `hconst : ∀ i, carrier.supp i = s`): `(D.rowMix R s).decLoss u z = ∑ⱼ (∑ᵢ Rⱼᵢ · genᵢ)²`, the
  mixed quadratic form of the old generators. At a fresh block the support-homogeneity side condition
  `hsh` of `SJLinGenState.loss_rowMix` is discharged FOR FREE (every generator shares support `s`), so
  the identity is unconditional in `R`. Faithful: it states the generators MIX (with the monomial prefix
  factoring cleanly out), NOT that the loss is preserved — only the specific det-1 absorbing units
  preserve it (`frobSq_step3_absorb`), which this does not assert.

* **`rowMix_d` / `rowMix_jac` / `rowMix_dom`** — the resolution-state invariants (`rfl`): the row-mix
  touches only the generator basis, so the descended coordinates (`d`, `jac`), integration domain
  (`dom`), and hence the carrier threshold `carrierThreshold M = ½·minAdm M` are all preserved.

## What is NOT here (the standing mountain)

This is the ALGEBRAIC (a) half of one peel. It does NOT discharge the support-homogeneity `hsh` for the
ACTUAL analytic Schur matrix `R = invSchurLeft`/`invSchurRight` at a non-fresh block (that
synchronisation is the `(S,J)` recursion), does NOT compose (a)+(b)+block-split+regime into
`decorated_peel_step`, and does NOT reach `RouteMBoxThresholdFinite M`. Closing `sjJointResolution`
reduces (via `RouteMSJJointReduce.sjJointResolution_of_boxThresholdFinite`) to standalone
`RouteMBoxThresholdFinite M`, whose only route is the full decorated recursion — the multi-module
resolution-of-singularities SIZE barrier (~65–75% genuinely-new; decorrelated Codex, the design cert,
the `RouteMSJFreedPeel` header). `sjJointResolution` stays the single named analytic sorry, UNTOUCHED.

S2-FREE: pure carrier algebra (banked `SJLinGenState.loss_rowMix`, constant-support `hsh` discharge).
Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {L : ℕ}

/-- **The clear-first row-mix on a decoration.** Mix the generators by `R : ι' → ι → ℝ` onto a fresh
constant target support `s : Fin d → ℕ`, via the banked `SJLinGenState.rowMix`. Only the generator index
type (`ι ↦ ι'`) and the carrier change; the resolution state (`d`, `jac`, `Z`, `mZ`, `ctx`, `dom`) is
carried unchanged — the (a) clear-first scalar Schur half of one decorated peel. -/
noncomputable def SJDecoration.rowMix {M : Fin (L + 1) → ℕ} (D : SJDecoration M)
    {ι' : Type} [Fintype ι'] (R : ι' → D.ι → ℝ) (s : Fin D.d → ℕ) : SJDecoration M :=
  letI := D.fι
  { d := D.d
    ζ := D.ζ
    ν := D.ν
    ι := ι'
    fν := D.fν
    fι := inferInstance
    carrier := D.carrier.rowMix R (fun _ => s)
    jac := D.jac
    Z := D.Z
    mZ := D.mZ
    ctx := D.ctx
    dom := D.dom
    residualMeas := by
      intro j
      simp only [SJLinGenState.residual_rowMix]
      exact Finset.measurable_sum Finset.univ
        (fun i _ => (D.residualMeas i).const_mul (R j i)) }

/-- **The row-mix preserves the exceptional count.** `(D.rowMix R s).d = D.d`. -/
@[simp] theorem SJDecoration.rowMix_d {M : Fin (L + 1) → ℕ} (D : SJDecoration M)
    {ι' : Type} [Fintype ι'] (R : ι' → D.ι → ℝ) (s : Fin D.d → ℕ) :
    (D.rowMix R s).d = D.d := rfl

/-- **The row-mix preserves the accumulated Jacobian.** `(D.rowMix R s).jac = D.jac`. -/
@[simp] theorem SJDecoration.rowMix_jac {M : Fin (L + 1) → ℕ} (D : SJDecoration M)
    {ι' : Type} [Fintype ι'] (R : ι' → D.ι → ℝ) (s : Fin D.d → ℕ) :
    (D.rowMix R s).jac = D.jac := rfl

/-- **The row-mix preserves the chart domain.** `(D.rowMix R s).dom = D.dom`. -/
@[simp] theorem SJDecoration.rowMix_dom {M : Fin (L + 1) → ℕ} (D : SJDecoration M)
    {ι' : Type} [Fintype ι'] (R : ι' → D.ι → ℝ) (s : Fin D.d → ℕ) :
    (D.rowMix R s).dom = D.dom := rfl

/-- **The decorated loss under a fresh-block clear-first row-mix.** When every generator carries the
same accumulated support `s` (`hconst`, the state right after a shared radial step — the only
configuration Aoyagi's block-elimination is applied to), the row-mixed decoration's loss is the mixed
quadratic form of the old generators: `(D.rowMix R s).decLoss u z = ∑ⱼ (∑ᵢ Rⱼᵢ · genᵢ)²`. The
support-homogeneity side condition of `SJLinGenState.loss_rowMix` is discharged FOR FREE by `hconst`, so
the identity holds unconditionally in `R`. The monomial prefix factors cleanly out of each mix (the
mixed generators share support `s`); this is the generator-mixing content of one clear-first
elimination, faithful — it does NOT assert the loss is preserved. -/
theorem SJDecoration.rowMix_decLoss {M : Fin (L + 1) → ℕ} (D : SJDecoration M)
    {ι' : Type} [Fintype ι'] (R : ι' → D.ι → ℝ) (s : Fin D.d → ℕ)
    (hconst : ∀ i, D.carrier.supp i = s) (u : Fin D.d → ℝ) (z : D.Z) :
    letI := D.fν; letI := D.fι
    (D.rowMix R s).decLoss u z
      = ∑ j : ι', (∑ i : D.ι, R j i * D.carrier.gen u (D.ctx z).1 (D.ctx z).2 i) ^ 2 := by
  letI := D.fν; letI := D.fι
  unfold SJDecoration.decLoss SJDecoration.rowMix
  exact D.carrier.loss_rowMix R (fun _ => s)
    (fun _ i _ ℓ => congrFun (hconst i) ℓ) u (D.ctx z).1 (D.ctx z).2

/-! ## Non-vacuity — the row-mix on the trivial `(3,3,4)` decoration by a genuine shear -/

/-- **Non-vacuity of the decoration row-mix.** On the trivial `(3,3,4)` decoration (`d = 0`, so the
constant support is the empty `s = ![]`, `hconst` holds since `ofMatrix` has `supp ≡ 0`; the generator
index is `ι = Fin (M 0) × Fin (M (Fin.last L)) = Fin 3 × Fin 4`), mixing the generators by a matrix `R`
gives the decorated loss `∑ⱼ (∑ᵢ Rⱼᵢ · genᵢ)²` — a genuine generator mix exercising the machinery on
the STEP-0 anchor. -/
example (R : (Fin 3 × Fin 4) → (Fin 3 × Fin 4) → ℝ) (u : Fin 0 → ℝ)
    (A : Params (![3, 3, 4] : Fin 3 → ℕ)) :
    letI := (SJDecoration.trivial (![3, 3, 4] : Fin 3 → ℕ)).fν
    letI := (SJDecoration.trivial (![3, 3, 4] : Fin 3 → ℕ)).fι
    ((SJDecoration.trivial (![3, 3, 4] : Fin 3 → ℕ)).rowMix R ![]).decLoss u A
      = ∑ j : Fin 3 × Fin 4,
          (∑ i : Fin 3 × Fin 4, R j i
            * (SJDecoration.trivial (![3, 3, 4] : Fin 3 → ℕ)).carrier.gen u
                (((SJDecoration.trivial (![3, 3, 4] : Fin 3 → ℕ)).ctx A).1)
                (((SJDecoration.trivial (![3, 3, 4] : Fin 3 → ℕ)).ctx A).2) i) ^ 2 :=
  SJDecoration.rowMix_decLoss (SJDecoration.trivial (![3, 3, 4] : Fin 3 → ℕ)) R ![]
    (fun _ => funext (fun i => i.elim0)) u A

end DLNFibre.DLN.RLCT

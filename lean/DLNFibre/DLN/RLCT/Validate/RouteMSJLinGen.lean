import DLNFibre.DLN.RLCT.Validate.RouteMSJLedger
import DLNFibre.DLN.RLCT.Validate.MatMulFibre

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJLinGen` — the non-terminal linear-generator carrier (Phase-2, piece 1)

**STEP-3 of the `SJState` recursion carrier** (thread `genm-sjcarrier4`; the R1-UPPER final gate →
`sjJointResolution`). The prior tide (`genm-sjcarrier3`, `RouteMSJLedger`) built the TERMINAL
normal-crossing carrier — the shared-divisor support map `SJSupport` and its finiteness endpoint
`sjLoss_terminal_lintegral_lt_top` — plus the Case-2 radial ledger step (`prependColumn`,
`sjLoss_prependColumn_one`). Decorrelated Codex (`genm-sjcarrier3/codex`) flagged the sharp risk: the
banked `frobSq`-level bricks (`corankStep_prefactor` : `pref·frobSq = pref·u²·residual`,
`RouteMSJCorankStep`) are **too coarse to recover the support matrix** — a sum-of-squares equality does
NOT certify *which* generators share a divisor. Shared-divisor faithfulness must be tracked
**generator-by-generator**.

## The non-terminal carrier

The `SJSupport` ledger is TERMINAL data: it describes generators that are already pure monomials in the
exceptional divisors `u`. The `(S,J)` recursion, however, operates on generators that are still **linear
forms** in the active (unresolved) block coordinates. This module supplies the intermediate carrier
(decorrelated Codex `genm-sjcarrier4/codex/scope-answer.md`, Q2):

    structure SJLinGenState (ζ ν ι) (d) where
      supp  : SJSupport ι d          -- accumulated exceptional-divisor exponents (monomial prefix)
      coeff : ζ → ι → ν → ℝ          -- generator i (in spectator context z) as a linear form in the
                                     -- active variables x : ν → ℝ

with `residual G z x i = ∑ᵥ coeff z i v · x v`, `gen G u z x i = genMonomial supp i u · residual z x i`
(a MONOMIAL prefix `∏_ℓ |u_ℓ|^{supp i ℓ}` times a LINEAR residual), and `loss G u z x = ∑ᵢ (gen …)²`.
`ζ` are spectator/unit parameters (the downstream product, absorbed gauge), `ν` the still-active linear
variables, `ι` the generators.

## What lands here (this module — piece 1, the block-elimination generator map)

* **`loss_ofProduct`** — the base: the matrix loss `frobSq (rmatMul A₀ Q)` IS the carrier loss of the
  fresh state `ofProduct Q` (support `≡ 0`, residual `= (A₀·Q)ᵢₖ`), at active variable `x = A₀`. The
  entry point connecting the honest matrix object to the carrier.
* **`radialStep` / `loss_radialStep`** — the Case-2 single radial at the carrier level: prepending a
  fresh fully-shared divisor `u₀` multiplies the loss by `u₀²` and records the sharing
  (`supp ↦ prependColumn (fun _ ↦ 1) supp`). The generator-level form of `corankStep`'s
  `frobSq((u•Δ)·Q) = u²·frobSq(Δ·Q)`, now with the divisor visible per-generator — generalises the
  ledger's `sjLoss_prependColumn_one`.
* **`gen_rowMix` / `sharedDivisorExp_rowMix`** — the **support-faithful row-mix** (the faithfulness core
  Codex named): under the `Z`-independent det-1 unit block-elimination the generators are linearly mixed
  by a matrix `R`; IF the mix is *support-homogeneous* (each new generator combines only old generators
  sharing its support vector — the passive-prefactor invariant), then `gen G' j = ∑ᵢ R j i · gen G i`
  row-by-row and the shared-divisor exponents are PRESERVED. This is exactly what `pref·frobSq = …` cannot
  see; the monomial factors out of the mix cleanly because the mixed generators share a monomial.
* **`loss_blockSplit`** — the corank decrement at the loss level: partitioning the generators over a
  sum-type index `ι_p ⊕ ι_c` splits the carrier loss additively (`= loss_pivot + loss_corank`), the
  generator-level shadow of `frobSq_blockDiag_split` (`RouteMSJStep3`). The pivot block is the freed
  Morse directions; the corank block recurses.

## What is NOT here (Phase 2/3 — the remaining mountain, reported precisely)

This module supplies the **generator-level algebra** of one `(S,J)` step (piece 1). It does NOT build
(pieces 2–3): the `(S,J)` RECURSION iterating the step down to the terminal, nor — decisively — the
**change-of-variables / resolution map** transporting the matrix-box `∫⁻ frobSq(A₀·Q)^{−c'}` to the
ledger's `∫⁻ (∑bᵢ²)^{−c'}·Jac` over the exceptional coordinates. That CoV (the explicit iterated
blow-up chart maps, each measure-preserving up to a monomial Jacobian, the finite chart cover, the
per-chart `lintegral` transport) is unbanked and — decorrelated Codex, `scope-answer.md` Q1 — is
~65–75% genuinely-new construction that no pointwise brick shortcuts. `sjJointResolution`
(`RouteMSJResolution`) stays the single named sorry, UNTOUCHED.

S2-FREE: pure algebra (`genMonomial`, `frobSq`, finite sums); axiom-clean
`[propext, Classical.choice, Quot.sound]`. No `monomial_rlct`, no measure theory.
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

/-- **`genMonomial` depends only on the support ROW `e i`.** If two supports agree at their respective
indices (`∀ ℓ, e i ℓ = e' i' ℓ`), the generator monomials coincide. The generator-level faithfulness
primitive: a monomial is determined by its exponent row — the datum a `frobSq` equality cannot read. -/
theorem genMonomial_congr_supp {ι ι' : Type*} {d : ℕ} {e : SJSupport ι d} {e' : SJSupport ι' d}
    {i : ι} {i' : ι'} (h : ∀ ℓ, e i ℓ = e' i' ℓ) (u : Fin d → ℝ) :
    genMonomial e i u = genMonomial e' i' u := by
  unfold genMonomial
  exact Finset.prod_congr rfl (fun ℓ _ => by rw [h ℓ])

/-- **The shared-divisor exponent of a constant support is that support.** If every generator carries
the same support row `s` (`∀ i, e i = s`), then `sharedDivisorExp e ℓ = s ℓ` — the `⨅ᵢ` of a constant.
The passive-prefactor invariant in its cleanest form: a common monomial is its own shared divisor. -/
theorem sharedDivisorExp_const {ι : Type*} [Fintype ι] [Nonempty ι] {d : ℕ} {e : SJSupport ι d}
    {s : Fin d → ℕ} (h : ∀ i, e i = s) (ℓ : Fin d) : sharedDivisorExp e ℓ = s ℓ := by
  unfold sharedDivisorExp
  rw [show (fun i => e i ℓ) = (fun _ : ι => s ℓ) from funext (fun i => by rw [h i])]
  simp only [Finset.inf'_const]

/-- **The non-terminal linear-generator state.** `supp i ℓ` is the accumulated order to which the
exceptional divisor `u_ℓ` divides generator `i` (the monomial prefix); `coeff z i v` is the
coefficient of active variable `v` in generator `i`'s residual linear form, in spectator context `z`. -/
structure SJLinGenState (ζ ν ι : Type*) (d : ℕ) where
  /-- The accumulated exceptional-divisor support (monomial prefix of each generator). -/
  supp : SJSupport ι d
  /-- The linear-form coefficients: generator `i` in context `z` is `∑ᵥ coeff z i v · x v`. -/
  coeff : ζ → ι → ν → ℝ

namespace SJLinGenState

variable {ζ ν ι ι' : Type*} [Fintype ν] [Fintype ι] {d : ℕ}

/-- **The linear residual** of generator `i`: `∑ᵥ coeff z i v · x v` (a linear form in the active
variables `x`, in spectator context `z`). -/
def residual (G : SJLinGenState ζ ν ι d) (z : ζ) (x : ν → ℝ) (i : ι) : ℝ :=
  ∑ v, G.coeff z i v * x v

/-- **The full generator** `bᵢ = (monomial prefix in u) · (linear residual in x)`. -/
noncomputable def gen (G : SJLinGenState ζ ν ι d) (u : Fin d → ℝ) (z : ζ) (x : ν → ℝ) (i : ι) : ℝ :=
  genMonomial G.supp i u * G.residual z x i

/-- **The carrier loss** `∑ᵢ bᵢ²` — the intermediate normal-crossing-in-progress loss. -/
noncomputable def loss (G : SJLinGenState ζ ν ι d) (u : Fin d → ℝ) (z : ζ) (x : ν → ℝ) : ℝ :=
  ∑ i, (G.gen u z x i) ^ 2

omit [Fintype ι] in
/-- The generator unfolds to `monomial · residual` (definitional). -/
theorem gen_eq (G : SJLinGenState ζ ν ι d) (u : Fin d → ℝ) (z : ζ) (x : ν → ℝ) (i : ι) :
    G.gen u z x i = genMonomial G.supp i u * G.residual z x i := rfl

/-- **The carrier loss is nonnegative** (a sum of squares). -/
theorem loss_nonneg (G : SJLinGenState ζ ν ι d) (u : Fin d → ℝ) (z : ζ) (x : ν → ℝ) :
    0 ≤ G.loss u z x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-! ## The base — the matrix loss IS a carrier loss (the entry point) -/

/-- **The base state** whose generators are the entries of a `p × q` matrix: active variables are the
entries themselves, the selection coefficients pick out one entry each, support `≡ 0` (no exceptional
divisors yet). The fresh state at the start of the `(S,J)` recursion. -/
def ofMatrix (p q : ℕ) : SJLinGenState Unit (Fin p × Fin q) (Fin p × Fin q) 0 where
  supp := fun _ _ => 0
  coeff := fun _ ik i'k' => if i'k' = ik then 1 else 0

/-- The base state's residual is the matrix entry (the selection coefficient reads off `Y ik`). -/
theorem residual_ofMatrix (p q : ℕ) (Y : Fin p × Fin q → ℝ) (ik : Fin p × Fin q) :
    (ofMatrix p q).residual () Y ik = Y ik := by
  unfold residual ofMatrix
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **The base connection.** The carrier loss of `ofMatrix` at active variable `Y` is `∑ᵢₖ Yᵢₖ²`, i.e.
`frobSq` of the matrix `Y`. Support `≡ 0` makes every generator monomial `1`, so the loss is the raw
sum of squares. -/
theorem loss_ofMatrix (p q : ℕ) (u : Fin 0 → ℝ) (Y : Fin p × Fin q → ℝ) :
    (ofMatrix p q).loss u () Y = frobSq (fun i k => Y (i, k)) := by
  unfold loss
  have hgen : ∀ ik, (ofMatrix p q).gen u () Y ik = Y ik := by
    intro ik
    rw [gen_eq, residual_ofMatrix,
      show genMonomial (ofMatrix p q).supp ik u = 1 by simp [genMonomial], one_mul]
  simp only [hgen]
  unfold frobSq
  rw [Fintype.sum_prod_type]

/-- **The base connection at a matrix PRODUCT** — the honest entry point. The matrix-box loss
`frobSq (A₀ · Q)` IS the carrier loss of `ofMatrix` at the active variable `Y = A₀·Q` (the product
entries). This is the object `gammaPeelIntegral` integrates; the carrier now holds it, ready for the
`(S,J)` radial/block-elimination steps. -/
theorem loss_ofMatrix_product {p n q : ℕ} (u : Fin 0 → ℝ) (A0 : Fin p → Fin n → ℝ)
    (Q : Fin n → Fin q → ℝ) :
    (ofMatrix p q).loss u () (fun ik => rmatMul A0 Q ik.1 ik.2) = frobSq (rmatMul A0 Q) := by
  rw [loss_ofMatrix]

/-! ## The Case-2 single radial step (generator-level; generalises `sjLoss_prependColumn_one`) -/

/-- **The Case-2 single radial step** at the carrier level: prepend a fresh fully-shared exceptional
divisor `u₀` (new index `0`) dividing EVERY generator to order `1`. The support gains the shared
column (`prependColumn (fun _ ↦ 1)`); the residuals (linear forms) are untouched. -/
def radialStep (G : SJLinGenState ζ ν ι d) : SJLinGenState ζ ν ι (d + 1) where
  supp := prependColumn (fun _ => 1) G.supp
  coeff := G.coeff

omit [Fintype ι] in
/-- Each generator picks up the fresh radial factor `|u₀|` (shared by all — Case-2 full block). -/
theorem gen_radialStep (G : SJLinGenState ζ ν ι d) (u₀ : ℝ) (u : Fin d → ℝ) (z : ζ) (x : ν → ℝ)
    (i : ι) : (radialStep G).gen (Fin.cons u₀ u) z x i = |u₀| * G.gen u z x i := by
  unfold gen radialStep residual
  rw [genMonomial_prependColumn]
  simp only [pow_one]
  ring

/-- **The radial factors as `u₀²`** at the carrier loss level: `loss (radialStep G) (u₀ ::: u) = u₀²·
loss G u`. The generator-level form of `corankStep`'s `frobSq((u•Δ)·Q) = u²·frobSq(Δ·Q)`, with the
divisor now visible per generator (the sharing recorded in the support, not merely in a scalar). -/
theorem loss_radialStep (G : SJLinGenState ζ ν ι d) (u₀ : ℝ) (u : Fin d → ℝ) (z : ζ) (x : ν → ℝ) :
    (radialStep G).loss (Fin.cons u₀ u) z x = u₀ ^ 2 * G.loss u z x := by
  unfold loss
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [gen_radialStep, mul_pow, sq_abs]

/-! ## The support-faithful block-elimination row-mix (the faithfulness core) -/

/-- **The row-mix of the generators** by a matrix `R : ι' → ι → ℝ`, targeting the support `s'`. The
`Z`-independent det-1 unit block-elimination (`step3_blockFactor`, `RouteMSJStep3`) acts on the
generators as such a linear mix; the target support `s'` records the (unchanged) monomial prefixes. -/
def rowMix (R : ι' → ι → ℝ) (s' : SJSupport ι' d) (G : SJLinGenState ζ ν ι d) :
    SJLinGenState ζ ν ι' d where
  supp := s'
  coeff := fun z j v => ∑ i, R j i * G.coeff z i v

/-- **The residual mixes linearly** (support-agnostic): `residual (rowMix R s' G) j = ∑ᵢ R j i ·
residual G i`. The linear part of the block-elimination is a plain matrix mix of the residual forms. -/
theorem residual_rowMix (R : ι' → ι → ℝ) (s' : SJSupport ι' d) (G : SJLinGenState ζ ν ι d)
    (z : ζ) (x : ν → ℝ) (j : ι') :
    (rowMix R s' G).residual z x j = ∑ i, R j i * G.residual z x i := by
  unfold residual rowMix
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun v _ => by ring)

/-- **The support-faithful row-mix (the faithfulness core).** IF the mix is *support-homogeneous* —
each new generator `j` combines only old generators `i` whose support row equals `j`'s target support
(`R j i ≠ 0 → G.supp i = s' j`) — THEN the generators mix row-by-row: `gen (rowMix R s' G) j = ∑ᵢ
R j i · gen G i`. This is what `pref·frobSq = pref·u²·residual` (`corankStep_prefactor`) CANNOT
certify: the monomial prefix factors cleanly out of the mix precisely because the mixed generators
share a monomial (decorrelated Codex, `genm-sjcarrier3/codex`: "shared-divisor faithfulness must be
proved row-by-row for generators"). -/
theorem gen_rowMix (R : ι' → ι → ℝ) (s' : SJSupport ι' d) (G : SJLinGenState ζ ν ι d)
    (hsh : ∀ j i, R j i ≠ 0 → ∀ ℓ, G.supp i ℓ = s' j ℓ)
    (u : Fin d → ℝ) (z : ζ) (x : ν → ℝ) (j : ι') :
    (rowMix R s' G).gen u z x j = ∑ i, R j i * G.gen u z x i := by
  rw [gen_eq, residual_rowMix, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [gen_eq]
  by_cases h : R j i = 0
  · rw [h]; ring
  · have hsupp : genMonomial (rowMix R s' G).supp j u = genMonomial G.supp i u :=
      genMonomial_congr_supp (fun ℓ => (hsh j i h ℓ).symm) u
    rw [hsupp]; ring

/-- **The carrier loss under a support-faithful row-mix** is the mixed quadratic form `∑ⱼ (∑ᵢ R j i ·
genᵢ)²`. The honest statement of the block-elimination at the loss level — it is NOT claimed to equal
the old loss for arbitrary `R` (only the specific det-1 absorbing units preserve it, via
`frobSq_step3_absorb`), but the generators mix faithfully with the support tracked. -/
theorem loss_rowMix [Fintype ι'] (R : ι' → ι → ℝ) (s' : SJSupport ι' d) (G : SJLinGenState ζ ν ι d)
    (hsh : ∀ j i, R j i ≠ 0 → ∀ ℓ, G.supp i ℓ = s' j ℓ)
    (u : Fin d → ℝ) (z : ζ) (x : ν → ℝ) :
    (rowMix R s' G).loss u z x = ∑ j, (∑ i, R j i * G.gen u z x i) ^ 2 := by
  unfold loss
  exact Finset.sum_congr rfl (fun j _ => by rw [gen_rowMix R s' G hsh u z x j])

/-- **The shared-divisor exponents are PRESERVED by a constant-support row-mix** (the passive-prefactor
invariant). At a fresh block every generator carries the same accumulated support `s`; the
block-elimination keeps `supp ≡ s`, so `sharedDivisorExp` is unchanged. This is the ledger datum the
recursion needs to keep faithful across the `(S,J)` step — the generator-level
`sharedDivisorExp_prependColumn_succ`. -/
theorem sharedDivisorExp_rowMix_const [Nonempty ι] [Nonempty ι'] [Fintype ι']
    (R : ι' → ι → ℝ) (s : Fin d → ℕ) (G : SJLinGenState ζ ν ι d) (hconst : ∀ i, G.supp i = s)
    (ℓ : Fin d) :
    sharedDivisorExp (rowMix R (fun _ => s) G).supp ℓ = sharedDivisorExp G.supp ℓ := by
  rw [sharedDivisorExp_const (e := (rowMix R (fun _ => s) G).supp) (fun _ => rfl) ℓ,
    sharedDivisorExp_const hconst ℓ]

/-! ## The corank decrement at the loss level (block split) -/

/-- **The corank decrement splits the loss additively.** Partitioning the generators over a sum-type
index `ι_p ⊕ ι_c` (pivot block ⊕ corank block) splits the carrier loss into the pivot energy and the
corank residual — the generator-level shadow of `frobSq_blockDiag_split` (`RouteMSJStep3`). The pivot
block is the freed Morse directions (dehomogenised units); the corank block, dimension decremented,
recurses. -/
theorem loss_blockSplit {ιp ιc : Type*} [Fintype ιp] [Fintype ιc]
    (G : SJLinGenState ζ ν (ιp ⊕ ιc) d) (u : Fin d → ℝ) (z : ζ) (x : ν → ℝ) :
    G.loss u z x
      = (∑ i : ιp, (G.gen u z x (Sum.inl i)) ^ 2)
        + (∑ i : ιc, (G.gen u z x (Sum.inr i)) ^ 2) := by
  unfold loss
  rw [Fintype.sum_sum_type]

/-! ## Non-vacuity — the row-mix at a genuine shear (the `(2,2,2)` Case-2 unit factor) -/

/-- **Non-vacuity of the support-faithful row-mix.** Two generators sharing a common support `s`,
mixed by the unit-triangular shear `R = [[1,0],[c,1]]` (a det-1 `(2,2,2)` Case-2 factor): the new
generator `gen'₁ = c·gen₀ + gen₁` is a genuine non-trivial mix, and the shared-divisor exponents are
PRESERVED. Witnesses that the faithfulness core fires on the actual `(2,2,2)` mechanism. -/
example (c : ℝ) (s : Fin 1 → ℕ) (G : SJLinGenState Unit Unit (Fin 2) 1)
    (hconst : ∀ i, G.supp i = s) (u : Fin 1 → ℝ) (x : Unit → ℝ) (ℓ : Fin 1) :
    (rowMix (![![1, 0], ![c, 1]] : Fin 2 → Fin 2 → ℝ) (fun _ => s) G).gen u () x 1
        = c * G.gen u () x 0 + G.gen u () x 1
      ∧ sharedDivisorExp (rowMix (![![1, 0], ![c, 1]] : Fin 2 → Fin 2 → ℝ) (fun _ => s) G).supp ℓ
          = sharedDivisorExp G.supp ℓ := by
  refine ⟨?_, sharedDivisorExp_rowMix_const _ s G hconst ℓ⟩
  rw [gen_rowMix _ _ G (fun _ i _ ℓ => congrFun (hconst i) ℓ) u () x 1]
  simp [Fin.sum_univ_two]

end SJLinGenState

end DLNFibre.DLN.RLCT

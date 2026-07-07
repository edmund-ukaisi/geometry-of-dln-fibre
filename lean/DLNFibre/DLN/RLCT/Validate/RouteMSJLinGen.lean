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
* **`gen_rowMix` / `gen_rowMix_const` / `sharedDivisorExp_rowMix_const`** — the row-mix generator
  identity. Under the `Z`-independent det-1 unit block-elimination the generators are linearly mixed by a
  matrix `R`; `gen_rowMix` is the CONDITIONAL identity `gen G' j = ∑ᵢ R j i · gen G i` under the
  support-homogeneity side condition `hsh` (each new generator combines only old generators sharing its
  target support). **The content is entirely inside `hsh`** — this is the honest reduction
  "block-elimination faithfulness ⟺ `hsh` on the step matrix", NOT a proof that a real Step-3 matrix
  satisfies `hsh` (deferred to the recursion; it fails for arbitrary `R`). `gen_rowMix_const` discharges
  `hsh` UNCONDITIONALLY at a fresh block (common support — the post-radial state the elimination acts on).
  This is the datum `pref·frobSq = …` (`corankStep_prefactor`) cannot express (it never reads which
  generators share a divisor); `sharedDivisorExp_rowMix_const` is the constant-support consistency read-back.
* **`loss_blockSplit`** — the loss under a generator index-partition: partitioning over a sum-type index
  `ι_p ⊕ ι_c` splits the carrier loss additively (`= ∑ pivot² + ∑ corank²`). This is the SHAPE of
  `frobSq_blockDiag_split` (`RouteMSJStep3`) — an additive split over a sum-type index, holding for any
  sum-indexed state; it carries none of that lemma's Schur-complement content (the actual reindexing into
  pivot/corank blocks is the deferred recursion). The shape the corank decrement lands on.

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

/-- **The row-mix generator identity, CONDITIONAL on support-homogeneity.** IF the mix is
*support-homogeneous* — each new generator `j` combines only old generators `i` whose support row
equals `j`'s declared target support (`hsh : R j i ≠ 0 → G.supp i = s' j`) — THEN the generators mix
row-by-row: `gen (rowMix R s' G) j = ∑ᵢ R j i · gen G i`, the monomial prefix factoring cleanly out of
the mix (because the mixed generators share a monomial). **The content is entirely inside `hsh`**: this
lemma is the elementary packaging (factor one asserted-equal monomial scalar out of a finite linear
combination), not a proof that a real block-elimination matrix `R` (`invSchurLeft`/`invSchurRight`,
`RouteMSJStep3`) satisfies `hsh`. That discharge — showing the actual `Z`-independent unit reduction
mixes only same-support generators — is deferred to the `(S,J)` recursion (which synchronises supports
per fresh block); it is the substantive obligation, and it does NOT hold for an arbitrary `R`. What is
established here is the honest reduction: block-elimination faithfulness ⟺ `hsh` on the step matrix. -/
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

/-- **The row-mix at a FRESH block is UNCONDITIONALLY faithful.** When every generator carries the same
accumulated support `s` (`hconst : ∀ i, G.supp i = s` — the state right after a shared radial step, the
only configuration Aoyagi's block-elimination is applied to), `hsh` holds for FREE for any `R`, so the
generators mix row-by-row with no side condition: `gen (rowMix R (fun _ ↦ s) G) j = ∑ᵢ R j i · gen G i`.
This is the genuinely-usable form for the recursion — the passive-prefactor invariant at the generator
level, discharging `gen_rowMix`'s `hsh` at the constant-support step. -/
theorem gen_rowMix_const (R : ι' → ι → ℝ) (s : Fin d → ℕ) (G : SJLinGenState ζ ν ι d)
    (hconst : ∀ i, G.supp i = s) (u : Fin d → ℝ) (z : ζ) (x : ν → ℝ) (j : ι') :
    (rowMix R (fun _ => s) G).gen u z x j = ∑ i, R j i * G.gen u z x i :=
  gen_rowMix R (fun _ => s) G (fun _ i _ ℓ => congrFun (hconst i) ℓ) u z x j

/-- **The carrier loss under a support-homogeneous row-mix** is the mixed quadratic form `∑ⱼ (∑ᵢ R j i ·
genᵢ)²`. NOT claimed to equal the old loss for arbitrary `R` (only the specific det-1 absorbing units
preserve it, via `frobSq_step3_absorb`, once absorbed into adjacent factors); the statement is that the
generators mix, with the support tracked. Content conditional on `hsh` (see `gen_rowMix`). -/
theorem loss_rowMix [Fintype ι'] (R : ι' → ι → ℝ) (s' : SJSupport ι' d) (G : SJLinGenState ζ ν ι d)
    (hsh : ∀ j i, R j i ≠ 0 → ∀ ℓ, G.supp i ℓ = s' j ℓ)
    (u : Fin d → ℝ) (z : ζ) (x : ν → ℝ) :
    (rowMix R s' G).loss u z x = ∑ j, (∑ i, R j i * G.gen u z x i) ^ 2 := by
  unfold loss
  exact Finset.sum_congr rfl (fun j _ => by rw [gen_rowMix R s' G hsh u z x j])

/-- **Constant-support consistency of `sharedDivisorExp` across the row-mix.** At a fresh block (common
support `s`) the row-mix targets the same constant support (`fun _ ↦ s`), so both sides reduce to `s ℓ`:
`sharedDivisorExp (rowMix R (fun _ ↦ s) G).supp ℓ = sharedDivisorExp G.supp ℓ`. This is a consistency
read-back on the CONSTANT target field (it does not inspect `R`) — the generator-level statement that a
constant monomial prefix is its own shared divisor, in the `sharedDivisorExp_prependColumn_succ` family.
It does NOT by itself prove a general block-elimination preserves the support (that is the deferred
`hsh` discharge of `gen_rowMix`). -/
theorem sharedDivisorExp_rowMix_const [Nonempty ι] [Nonempty ι'] [Fintype ι']
    (R : ι' → ι → ℝ) (s : Fin d → ℕ) (G : SJLinGenState ζ ν ι d) (hconst : ∀ i, G.supp i = s)
    (ℓ : Fin d) :
    sharedDivisorExp (rowMix R (fun _ => s) G).supp ℓ = sharedDivisorExp G.supp ℓ := by
  rw [sharedDivisorExp_const (e := (rowMix R (fun _ => s) G).supp) (fun _ => rfl) ℓ,
    sharedDivisorExp_const hconst ℓ]

/-! ## The loss under a generator index-partition (the block-split shape) -/

/-- **The carrier loss splits additively over a sum-type generator index.** Partitioning the generators
over `ι_p ⊕ ι_c` (pivot block ⊕ corank block) splits the loss into `∑ pivot² + ∑ corank²`. This is the
index-partition shape of `frobSq_blockDiag_split` (`RouteMSJStep3`) — an additive split of a
sum-of-squares over a sum-type index; it holds for ANY sum-indexed state and carries none of
`frobSq_blockDiag_split`'s Schur-complement content (the zero off-diagonal, the corank block `Γ`). Its
role: the SHAPE the corank decrement lands on once the generators have been reindexed into pivot/corank
blocks (that reindexing, from the actual block-diagonalisation, is the deferred recursion). -/
theorem loss_blockSplit {ιp ιc : Type*} [Fintype ιp] [Fintype ιc]
    (G : SJLinGenState ζ ν (ιp ⊕ ιc) d) (u : Fin d → ℝ) (z : ζ) (x : ν → ℝ) :
    G.loss u z x
      = (∑ i : ιp, (G.gen u z x (Sum.inl i)) ^ 2)
        + (∑ i : ιc, (G.gen u z x (Sum.inr i)) ^ 2) := by
  unfold loss
  rw [Fintype.sum_sum_type]

/-! ## Non-vacuity — the row-mix at a genuine shear (the `(2,2,2)` Case-2 unit factor) -/

/-- **Non-vacuity of the fresh-block row-mix.** Two generators sharing a common support `s`, mixed by
the unit-triangular shear `R = [[1,0],[c,1]]` (a det-1 `(2,2,2)` Case-2 factor): the new generator
`gen'₁ = c·gen₀ + gen₁` is a genuine non-trivial mix, and the constant-support consistency holds. A
concrete witness that the row-mix identity fires unconditionally on a fresh block (`gen_rowMix_const`
would apply directly); the shear here mixes DIFFERENT-index generators, so `R` is genuinely off-diagonal. -/
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

import DLNFibre.DLN.Aoyagi.ChartTransport

/-!
# `DLN.Aoyagi.GateRouteB222` — the route-B de-risk GATE at `d = (2,2,2)`

**Gate artifact (go/no-go measurement), NOT a monument brick.** This module makes the route-B
matched-gauge transport concrete and inspectable at the minimal intermediate-node witness
`d = (2,2,2)`, `N = 2`. It delivers the ONE green milestone (Milestone 1a: the matched-gauge
`hequiv` on `coreGen`) and pins, in Lean, the exact algebraic content of the O1 obstruction the
gate walls on. The WALL itself (Milestones 2/3 — the ancestor-pivot bookkeeping / the structural
chart↔tree-leaf coherence) is DOCUMENTED in the gate report, not claimed resolved here.

## The setting

`coreGen` at `(2,2,2)` = the 4 entries of the product `P = A₁·A₀` (`A₀, A₁` each `2×2`) viewed as
functions of the 8 ambient matrix-entry coordinates `Fin 8`:

* `A₀ u = !![u 0, u 1; u 2, u 3]` — rows = middle index `m` (`d₁`), cols = input index `j` (`d₀`);
* `A₁ u = !![u 4, u 5; u 6, u 7]` — rows = output index `i` (`d₂`), cols = middle index `m` (`d₁`).

## What is GREEN here (Milestone 1a)

`sigma222 = (0 2)(1 3)(4 5)(6 7)` is the **matched gauge on the middle/shared index** `m`: it swaps
`A₀`'s rows AND `A₁`'s cols simultaneously (`sigma222_touches_A0`, `sigma222_touches_A1` — it moves
a coordinate in BOTH adjacent layers, so it is genuinely matched, NOT a single-layer swap; gate
acceptance #1, #5). Under it `coreGen` is **INVARIANT** (`coreGen222_permOf_sigma222`, `τ = id`), so
`transportChart` applies (`transport_valid_matchedGauge`): the transported chart is a valid
`Chart` for the SAME `coreGen` at the same point. `hequiv` is stated on `coreGen` (the product
family), NOT the Schur stage family (gate acceptance #2).

## What WALLS (the O1/O2 crux — documented, not resolved)

* The matched gauge is the ONLY `coreGen` symmetry swapping the node's two center rows, and it
  **co-permutes the adjacent layer** — at `(2,2,2)` the middle index is ancestor-born, so it
  moves an ancestor pivot: the transported chart lands under a DIFFERENT parent branch (audit
  O1/F3). A *node-local sibling* coherence is therefore impossible (Codex xhigh, this gate).
* The fan COVER is swept by ENTRY-level coordinate swaps, which are NOT `coreGen` symmetries
  (`unmatched_not_symmetry222`: even the single-layer half of the matched gauge already breaks
  invariance). So the transport-valid permutation group and the cover-required permutation set are
  DISJOINT on the node's pivots: transport supplies no sibling certificate, and coverage comes from
  the fan, never from a symmetry orbit (gate acceptance #3, #4 fail).

Consequently route-B does not collapse the per-leaf certificate monument with the banked assets +
a bounded coherence lemma; it reduces to the full general-`d` L-A/L-B/L-C spine per fan leaf plus an
unbuilt leaf-indexed structural chart↔leaf assembly. See the gate report.
-/

open MeasureTheory Set Matrix
open DLNFibre.Core.Aoyagi

namespace DLNFibre.DLN.Aoyagi.GateRouteB222

/-! ## §0 — the ambient blocks and the `coreGen` family -/

/-- `A₀` (`2×2`): rows = middle index `m`, cols = input index `j`. -/
def A0 (u : Fin 8 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![u 0, u 1; u 2, u 3]

/-- `A₁` (`2×2`): rows = output index `i`, cols = middle index `m`. -/
def A1 (u : Fin 8 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![u 4, u 5; u 6, u 7]

/-- The product matrix `P = A₁·A₀` (the transposed multiplication map; entries = `coreGen`). -/
def Pmat (u : Fin 8 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := A1 u * A0 u

/-- **The `coreGen (2,2,2)` family** `Fin 4 → (Fin 8 → ℝ) → ℝ`: the 4 entries of `P = A₁·A₀`,
indexed via `finProdFinEquiv` (`k ↦ (i,j)`) — the product family `transportChart` consumes. -/
noncomputable def coreGen222 : Fin (2 * 2) → (Fin 8 → ℝ) → ℝ :=
  fun k u ↦ Pmat u (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-! ## §1 — the matched gauge `sigma222` on the middle/shared index -/

/-- `sigma222 = (0 2)(1 3)(4 5)(6 7)` as a function: swaps `A₀`'s rows (`0↔2, 1↔3`) AND `A₁`'s cols
(`4↔5, 6↔7`) — the matched gauge on the middle index `m`. -/
def sigmaFun : Fin 8 → Fin 8 := ![2, 3, 0, 1, 5, 4, 7, 6]

theorem sigmaFun_involutive : Function.Involutive sigmaFun := by intro x; fin_cases x <;> rfl

/-- **The matched-gauge coordinate permutation** on the middle/shared index. -/
def sigma222 : Equiv.Perm (Fin 8) := sigmaFun_involutive.toPerm

@[simp] theorem sigma222_apply (i : Fin 8) : sigma222 i = sigmaFun i := rfl

/-- `sigma222` moves a coordinate in the `A₀` block `{0,1,2,3}` (it touches the first layer). -/
theorem sigma222_touches_A0 : sigma222 0 = 2 := rfl

/-- `sigma222` moves a coordinate in the `A₁` block `{4,5,6,7}` (it touches the second, adjacent
layer): together with `sigma222_touches_A0` this is gate acceptance #1 — a genuine MATCHED gauge
across BOTH adjacent layers, not a single-layer swap. -/
theorem sigma222_touches_A1 : sigma222 4 = 5 := rfl

/-! ## §2 — the block reindexing under the matched gauge

The matched gauge swaps the middle index `m` in BOTH factors: `A₀`'s ROW index and `A₁`'s COL
index. Each block-swap fact is `rfl` (the coordinate reads reduce definitionally). -/

/-- `A₀`'s middle (row) index `0 ↦ 1` under the matched gauge. -/
theorem A0_permOf_sigma222_zero (u : Fin 8 → ℝ) (j : Fin 2) :
    A0 (permOf sigma222 u) 0 j = A0 u 1 j := by fin_cases j <;> rfl

/-- `A₀`'s middle (row) index `1 ↦ 0` under the matched gauge. -/
theorem A0_permOf_sigma222_one (u : Fin 8 → ℝ) (j : Fin 2) :
    A0 (permOf sigma222 u) 1 j = A0 u 0 j := by fin_cases j <;> rfl

/-- `A₁`'s middle (col) index `0 ↦ 1` under the matched gauge. -/
theorem A1_permOf_sigma222_zero (u : Fin 8 → ℝ) (i : Fin 2) :
    A1 (permOf sigma222 u) i 0 = A1 u i 1 := by fin_cases i <;> rfl

/-- `A₁`'s middle (col) index `1 ↦ 0` under the matched gauge. -/
theorem A1_permOf_sigma222_one (u : Fin 8 → ℝ) (i : Fin 2) :
    A1 (permOf sigma222 u) i 1 = A1 u i 0 := by fin_cases i <;> rfl

/-- **Product invariance** — the matched gauge on the middle index cancels in the contraction:
`P(permOf sigma222 u) = P u` entrywise (the shared-index swap reindexes the contraction away). -/
theorem Pmat_permOf_sigma222 (u : Fin 8 → ℝ) (i j : Fin 2) :
    Pmat (permOf sigma222 u) i j = Pmat u i j := by
  simp only [Pmat, Matrix.mul_apply, Fin.sum_univ_two, A0_permOf_sigma222_zero,
    A0_permOf_sigma222_one, A1_permOf_sigma222_zero, A1_permOf_sigma222_one]
  ring

/-! ## §3 — Milestone 1a: the matched-gauge `hequiv` on `coreGen`, and valid transport -/

/-- **Milestone 1a (GREEN): `coreGen (2,2,2)` is invariant under the matched gauge** (`τ = id`).
This is the `hequiv` on the PRODUCT family (gate acceptance #2) that `transportChart` consumes,
for the INTERMEDIATE/middle gauge (gate acceptance #5). -/
theorem coreGen222_permOf_sigma222 (k : Fin (2 * 2)) :
    coreGen222 k ∘ permOf sigma222 = coreGen222 (Equiv.refl _ k) := by
  funext u
  simp only [coreGen222, Function.comp_apply, Equiv.refl_apply]
  exact Pmat_permOf_sigma222 u _ _

/-- **Milestone 1a (GREEN): the matched-gauge transport is VALID.** Given ANY certified
`Chart coreGen222 x₀` (the from-scratch resolution the gate takes as INPUT), `transportChart`
produces a valid `Chart coreGen222 (permOf sigma222.symm x₀)` for the SAME family — the transport
interface closes on the middle matched gauge. (The gate INPUT chart is not built here; supplying
it — for EVERY fan leaf — is the monument the gate walls on.) -/
noncomputable def transport_valid_matchedGauge (x₀ : Fin 8 → ℝ) (chart : Chart coreGen222 x₀) :
    Chart coreGen222 (permOf sigma222.symm x₀) :=
  transportChart sigma222 (Equiv.refl _) coreGen222_permOf_sigma222 chart

/-! ## §4 — the O1/O2 crux, pinned in Lean (the WALL content — see the gate report)

The matched gauge above is coreGen-invariant, but it CO-PERMUTES the adjacent layer (it touches both
`A₀` and `A₁`, §1); at `(2,2,2)` the middle index is ancestor-born, so it moves an ancestor pivot
(audit O1/F3, tree-level, not re-derived here). The single-layer / entry swaps that the fan COVER
needs are NOT coreGen symmetries — pinned below — so transport supplies no sibling certificate and
the two permutation sets are disjoint on the node's pivots. -/

/-- The UNMATCHED half `(0 2)(1 3)` (permute `A₀`'s rows only, leave `A₁` fixed). -/
def sigmaUFun : Fin 8 → Fin 8 := ![2, 3, 0, 1, 4, 5, 6, 7]

theorem sigmaUFun_involutive : Function.Involutive sigmaUFun := by intro x; fin_cases x <;> rfl

/-- The unmatched single-layer coordinate permutation. -/
def sigmaU222 : Equiv.Perm (Fin 8) := sigmaUFun_involutive.toPerm

@[simp] theorem sigmaU222_apply (i : Fin 8) : sigmaU222 i = sigmaUFun i := rfl

/-- `A₀`'s row index `0 ↦ 1` under the unmatched swap. -/
theorem A0_permOf_sigmaU222_zero (u : Fin 8 → ℝ) (j : Fin 2) :
    A0 (permOf sigmaU222 u) 0 j = A0 u 1 j := by fin_cases j <;> rfl

/-- `A₀`'s row index `1 ↦ 0` under the unmatched swap. -/
theorem A0_permOf_sigmaU222_one (u : Fin 8 → ℝ) (j : Fin 2) :
    A0 (permOf sigmaU222 u) 1 j = A0 u 0 j := by fin_cases j <;> rfl

/-- `A₁` is UNCHANGED under the unmatched swap (it fixes coords `4,5,6,7`) — so the middle index is
NOT co-permuted in the adjacent layer: the product is not preserved. -/
theorem A1_permOf_sigmaU222 (u : Fin 8 → ℝ) (i m : Fin 2) :
    A1 (permOf sigmaU222 u) i m = A1 u i m := by fin_cases i <;> fin_cases m <;> rfl

/-- **The O1 crux, pinned: the unmatched single-layer swap is NOT a `coreGen` symmetry.** Swapping
`A₀`'s rows WITHOUT co-permuting `A₁`'s cols changes the product, so it has no valid
`transportChart`.
Witness `u = e₂ + e₄`: `P₀₀(u) = 0` but `P₀₀(permOf sigmaU222 u) = 1`. (Entry-level cover swaps are
even further from a symmetry — this is the mildest failure.) This is why the transport-valid
permutation group and the cover-required permutation set are DISJOINT on the node's pivots. -/
theorem unmatched_not_symmetry222 :
    ¬ (∀ (u : Fin 8 → ℝ) (i j : Fin 2), Pmat (permOf sigmaU222 u) i j = Pmat u i j) := by
  intro h
  have hcon := h ![0, 0, 1, 0, 1, 0, 0, 0] 0 0
  simp only [Pmat, Matrix.mul_apply, Fin.sum_univ_two, A0_permOf_sigmaU222_zero,
    A0_permOf_sigmaU222_one, A1_permOf_sigmaU222] at hcon
  simp [A0, A1] at hcon

end DLNFibre.DLN.Aoyagi.GateRouteB222

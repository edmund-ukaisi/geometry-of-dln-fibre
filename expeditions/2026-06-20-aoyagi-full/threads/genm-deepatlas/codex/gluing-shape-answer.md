Lock this shape: one flat finite CR-path index, exact-rank cells, one set-equality coverage theorem, then one invocation of the banked gluing lemma.

## 1. Index shape: flat dependent `Σ` tree

Use a recursively defined path type, but flatten the completed paths into one `Fintype` at the consumer. Suppressing only proof arguments for `Fin` bounds:

```lean
def CRPath (H : Fin (L + 1) → ℕ) (s : ℕ) :
    (j : ℕ) → (hj : j ≤ L) → ℕ → Type
  | 0,     _,  q => {_ : Unit // q ≤ s}
  | k + 1, hk, q =>
      Σ r : Fin (min (H ⟨k, by omega⟩) q + 1),
        (Fin r.1 ↪ Fin (H ⟨k, by omega⟩)) ×
        (Fin r.1 ↪ Fin q) ×
        CRPath H s k (by omega) r.1

def CRIndex (H) (s) :=
  CRPath H s L le_rfl (H (Fin.last L))
```

This records at every descent:

- the exact effective rank `r`,
- a row pivot `ρ`,
- a column pivot `κ`,
- the remaining lower-level path.

`CRIndex H s` has a structurally inferred noncomputable `Fintype`: `Fin`, embeddings, products, dependent `Σ`, and the terminal subtype are finite. `Function.Embedding.fintype` is **VERIFIED** in Mathlib v4.29.

For a path step and current state `Q`, define

```lean
M A  := effLayer H A k hk * Q A
U A  := (M A).submatrix ρ κ
Q' A := (M A).submatrix id κ * (U A)⁻¹
```

and recursively

```lean
cell (step r ρ κ tail) Q =
  {A | IsUnit (U A) ∧ (M A).rank ≤ r} ∩ cell tail Q'

cell terminal Q = Set.univ
```

The terminal index carries `q ≤ s`. The coverage induction carries the invariant `Q.rank = q` on the current prefix cell. After a step, `Q'.rank = r` follows cheaply from `generalPivot_reduce_rank` with `X = 1`.

Why this shape: it matches the banked descent directly and invokes gluing once. Nested gluing would require additional prefix-domain integral statements and repeated threading of the leaf `hfin`; it gains nothing.

## 2. `hcover`: trivial measure proof, nontrivial set theorem

Set

```lean
D H s := {A : Params H | (prod H A).rank ≤ s}
C i   := deepCell H s i
```

The required coverage theorem should be the exact equality

```lean
theorem deepRankLE_eq_iUnion_cells
    (H : Fin (L + 1) → ℕ) (s : ℕ) :
    {A : Params H | (prod H A).rank ≤ s}
      = ⋃ i : CRIndex H s, deepCell H s i
```

Its proof is induction on chain length:

1. Split the effective matrix by its actual rank.
2. Apply `rankEqLocus_eq_iUnion_pivot_inter`.
3. Descend using `prodAux_reduce_rank`.
4. At `j = 0`, `prodAux 0 = 1`; the carried full-column-rank invariant identifies the represented rank with terminal `q`, whose index contains `q ≤ s`.

Every branch condition is

```lean
pivotChart ρ κ ∩ {M | M.rank ≤ r}
```

not a bare pivot chart. Thus the pivot forces `r ≤ rank M`, and the cut forces equality. At `r = 0`, the condition is `rank M ≤ 0`, hence `M = 0`; the empty minor does not produce `univ`.

Consequently:

```lean
hcover : μ (D H s \ ⋃ i, C i) = 0
```

is proved by rewriting with `deepRankLE_eq_iUnion_cells` and `simp`. That proof is measure-theoretically trivial because the geometric set equality already did the work. The cells are not intended to cover a larger neighborhood.

The final wrapper should remain fully generic:

```lean
theorem deepRankLE_lintegral_lt_top
    {μ : Measure (Params H)}
    (f : Params H → ℝ≥0∞)
    (hfin : ∀ i : CRIndex H s,
      ∫⁻ A in deepCell H s i, f A ∂μ < ⊤) :
    ∫⁻ A in {A | (prod H A).rank ≤ s}, f A ∂μ < ⊤
```

It is one application of the banked theorem. The actual declaration has no measurability hypothesis on either `C` or `f`: **FACT**, see [RouteMSJIncidenceGluing.lean](/home/ubuntu/workspace/deepatlasA-wt/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJIncidenceGluing.lean:28).

Thus §3.3 is legitimately thin wiring. The nontrivial Tide-B work is §3.2’s finite exact-cell family, set equality, and measurability. Per-cell finiteness remains entirely Tide D.

## 3. Measurability

For a raw or continuously pulled-back pivot chart, the verified chain is:

```lean
continuous_apply
Continuous.matrix_reindex
Continuous.matrix_mul
Continuous.matrix_submatrix
Continuous.matrix_det
isOpen_ne.preimage
IsOpen.measurableSet
```

Together with

```lean
Matrix.isUnit_iff_isUnit_det
isUnit_iff_ne_zero
```

all are **VERIFIED** at v4.29. Hence a pivot chart is open, and its pullback along a continuous effective-layer map is open/measurable.

The rank locus should be proved genuinely:

\[
\{M:\operatorname{rank}M\le r\}^{c}
 =\{M:r+1\le\operatorname{rank}M\}
 =\bigcup_{\rho,\kappa}\operatorname{pivotChart}(\rho,\kappa).
\]

The second equality is the banked `pivotLocus_eq_iUnion`; the right side is open. Therefore `{rank ≤ r}` is closed and measurable. This maximally reuses the banked spine and avoids importing a separate minors theorem.

For deeper states, `Q'` contains totalized matrix inversion and is not globally continuous. Prove it measurable entrywise using:

- `Matrix.inv_def`, `Continuous.matrix_adjugate`, `Measurable.inv`: **VERIFIED**.
- `measurable_pi_lambda`, `measurable_pi_apply`: **VERIFIED**.
- Repository helper `measurable_matrixInv_entry`: **VERIFIED-repo**.
- Packaged `Measurable.matrix_inv`: **ABSENT** at this pin.
- Packaged Mathlib `MeasurableSet {M | M.rank ≤ r}`: **ABSENT**.
- `measurableSet_lt`: **VERIFIED**, but unnecessary here.

Then each deep cell is a finite intersection of measurable preimages. Do not claim deep branch predicates are globally open.

## 4. Cheapest genuine first green

Land the matrix-level package first:

```lean
isOpen_pivotChart
isClosed_rankLE
measurableSet_pivot_inter_rankLE
```

This tests exactly the non-vacuous leaf and the real topology API. Estimate: 30–55 proof LoC.

Whole tranche estimate:

- 300–550 executable definition/proof LoC;
- roughly 450–750 including documentation, examples, and axiom checks.

## 5. Trap check

- Loss leak: mentioning `dlnLoss`, `B`, or an exponent in `CRIndex`, `deepCell`, or the gluing theorem; keep only generic `f`.
- Vacuity: unioning raw pivot charts over ranks including `0`; every node must retain `rank M ≤ r`.
- Measurability hand-wave: claiming the rank map or totalized matrix inverse is continuous; use open nonzero-minor loci, closed rank loci, and entrywise measurable inversion.
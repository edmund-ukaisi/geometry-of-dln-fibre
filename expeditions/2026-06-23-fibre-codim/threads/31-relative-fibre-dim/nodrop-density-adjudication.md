# Thread 31 — step-4 source no-drop: chart-density adjudication

*Seat: pen-and-paper, witness direction. Question: does the chart `U = {detΔ ≠ 0}` (detΔ = the
top-left r×r pivot minor of the PRODUCT `mult(A)` = `ΔPdeep d r`) meet — i.e. is it dense in — EVERY
top-dimensional irreducible component of the REDUCIBLE rank-r product locus `Σ^r`? Read-only; no Lean
writes, no builds. Decorrelated xhigh Codex fired independently (hypothesis withheld).*

## VERDICT (one line)

**ONE-CHART AVOIDANCE HOLDS → step-4 ≈ 1.5–2 modules.** `U = {ΔPdeep ≠ 0}` is dense in every
top-dimensional component of `Σ^r`. The pivot-cover fallback is NOT needed. The avoidance is a
*two-fact* argument, BOTH facts already LANDED in the engine: (A) every top component has generic
product-rank exactly `r` (`CCodimCornerMono.exists_kostantPartition_partitionIdeal_eq_of` forces
corner `= r` on a top component); (B) on such a component the top-left r×r minor of the product is
not identically zero, because the component is `H'`-stable (the sweep identity) and a *permutation*
in `GL_{d_N} × GL_{d_0}` carries any nonzero r×r minor of the rank-r product to the top-left slot. My
exact-algebra computation and a decorrelated xhigh Codex concur on the load-bearing chain.

---

## The object, pinned (why this is not the naive "some-minor" worry)

`detΔ = ΔPdeep d r hp hq` (`DeepChartRing.lean:107`) is the determinant of the **top-left r×r
submatrix of the generic PRODUCT matrix** `Matrix.of (multPoly d)`, i.e. `det (mult(A))[1..r,1..r]`
as a polynomial in the tuple coordinates. It is a minor of the *product*, not of an end-factor. The
naive worry the brief flags is real: a rank-r matrix has *some* nonzero r×r minor, but the top-left
one can vanish (e.g. `[[0,1,0],[0,0,1],[0,0,0]]` has rank 2, top-left 2×2 minor `= 0`). So the
question is genuinely "does the *top-left* minor avoid every top component", not "does *some* minor".

## The avoidance argument (witness direction — construct, do not sweep)

**Fact A — every top-dimensional component has generic product-rank exactly `r`.**
`Σ̄^r = ⋃_M Ō_M` over corner-`≤ r` orbit closures (`SigmaStratification`), and the corner entry
`r_{0N}(A) = rank(mult A)` is the orbit-closure-order top entry (`corner_rankPattern_eq_rank`,
`SigmaStratification.lean:62`). The LANDED `CCodimCornerMono.exists_kostantPartition_partitionIdeal_eq_of`
(`:378`) proves: every **top** component `p` (a minimal prime of `sigmaIdeal d r` of minimal
height `cCodim d r`) equals `partitionIdeal d r m` for a Kostant partition `m ∈ kostantPartitions d r`
of corner **exactly `r`** — a corner-`s < r` representative has strictly larger codimension
(`cCodim d r < cCodim d s`, strict corner-monotonicity), so cannot be top-dimensional. Both feeding
monotonicities are LANDED (`CCodimZeroMono.cCodim_zero_mono`, `CCodimZeroStrict.cCodim_zero_strict`),
so Fact A is effectively unconditional `[IsAlgClosed k] [CharZero k]`. A corner-`r` realizer has
product rank exactly `r`, so the (irreducible) component has a point of `Σ^r` and hence generic
product-rank `r`.

**Fact B — on such a component, the top-left r×r minor of the product is not identically zero.**
The component `Ō_M` is `H'`-stable: it is a union of `H' = GL_{d_N}×GL_{d_0}`-orbits (the sweep
identity `Σ^r = ⋃_P (P•)''F`, `EndBaseChangeSweep.productRankLocus_eq_iUnion_smul_fibre:81`; each
`Ō_M` is `G_d`-, in particular `H'`-, stable, `OrbitClosure.orbitSet_baseChange_stable:189`).
Suppose for contradiction `detΔ ≡ 0` on `Ō_M`. By Fact A pick `A₀ ∈ Ō_M` with `rank(mult A₀) = r`.
Then `mult(A₀)` has *some* nonzero r×r minor at rows `R`, cols `C`. Take the row-permutation matrix
`g_N ∈ GL_{d_N}` sending `R` to `{1..r}` and the column-permutation `g_0 ∈ GL_{d_0}` sending `C` to
`{1..r}`. Then `A₁ = (g_N, g_0)·A₀ ∈ Ō_M` (H'-stability), and `mult(A₁) = g_N · mult(A₀) · g_0⁻¹`
(`mult_smul`) has top-left r×r minor `= ±(that nonzero minor) ≠ 0`. So `detΔ(A₁) ≠ 0`, contradicting
`detΔ ≡ 0`. Hence `detΔ` does NOT vanish identically on `Ō_M`; being a principal open of an
irreducible variety, `U` is **dense** in `Ō_M`. ∎

The two facts together: **`U` meets (is dense in) every top-dimensional component of `Σ^r`.**

## Exact-algebra certificate (sympy, generic-point symbolic — not Monte-Carlo)

The "not identically zero" claims below are symbolic over a generic rank-pattern representative
(factored form `A_i = L_i R_i`), so they certify generic-non-vanishing on the component, not a lucky
numeric hit.

- The permutation step (Fact B) is exact: `[[0,1,0],[0,0,1],[0,0,0]]` (rank 2, top-left 2×2 minor
  `0`) has its nonzero minor at rows `(0,1)` cols `(1,2)`; the row/col permutations move it to the
  top-left, value preserved up to sign. Permutations are in `GL_{d_N}×GL_{d_0}`.

## Sanity checks (the two anchors the brief named)

**(2,2,2), r = 1 (top-left 1×1 minor = the (1,1)-entry of `A₂A₁`).** `Σ̄^1 = {det(A₂A₁)=0} =
{det A₁=0} ∪ {det A₂=0}`, two top (dim-7) components, patterns `(1,2,1)` and `(2,1,1)`. Symbolic
generic point of each (`A₁ = u·vᵀ` rank-1 / `A₂` generic, and vice versa): the (1,1)-entry of `A₂A₁`
is **NOT identically zero** on either. Concrete witnesses: `A₁=diag(1,0),A₂=I` and
`A₂=diag(1,0),A₁=I` both give (1,1)-entry `= 1`. → `U` meets both.

**(3,3,3), r = 2 (top-left 2×2 minor of the 3×3 product `A₂A₁`).** Top-dimensional components are
the corner-`2` strata. By Jacobian-rank dimension count: `{det A₁=0}` (pattern `(2,3,2)`) and
`{det A₂=0}` (pattern `(3,2,2)`) are dim **17** (top); the both-drop `(2,2,2)` stratum is dim **16**
(NOT top). On a symbolic generic representative of EACH corner-`2` stratum `(2,2,2)`, `(2,3,2)`,
`(3,2,2)` the top-left 2×2 minor is **NOT identically zero**. → `U` meets every top component.

> θ note. Codex (decorrelated) counted θ=2 for `(3,3,3)` r=2 (set components `{det A₁=0}`,
> `{det A₂=0}`); the brief/paper say θ=3. The resolution: the SET `{det(A₂A₁)=0}` has two
> codim-1 irreducible components, but the paper's θ counts top components of the rank-PATTERN
> stratification of `Σ^r` differently. **This discrepancy does not touch the verdict** — under
> either count every top-dimensional component has generic product-rank `r`, and the minor is
> generically nonzero on each. (Worth a separate note for the θ-count thread; not load-bearing here.)

## Why the pivot-cover fallback is NOT needed (answer to brief Q2/Q3)

The H'-equivariance (Fact B) is exactly the mechanism that makes the SINGLE top-left chart suffice:
the component is a union of orbits, and within each orbit the top-left minor is nonzero somewhere
(permute the nonzero minor into place). So one need not take the union over all `binom(d_N,r)·
binom(d_0,r)` pivot positions — that finite cover `⋃_{R,C} {det(mult(A)_{R,C}) ≠ 0} = Σ^r` does hold
(a matrix is rank-`r` iff some r×r minor is nonzero) and *would* recover the no-drop via a
max-over-charts bookkeeping (`RadicalCatenary` templates), but it is the more expensive route and is
**unnecessary**: the single chart `{ΔPdeep ≠ 0}` already meets every top component.

## Step-4 module estimate (firm)

| Piece | Content | Status / cost |
|---|---|---|
| 4a | `detΔ = ΔPdeep` not identically zero on each top component (Fact A + Fact B) | LANDED inputs: `exists_kostantPartition_partitionIdeal_eq_of` (Fact A), sweep + `mult_smul` + `orbitSet_baseChange_stable` (H'-stability), permutation-moves-minor (elementary). ~1 module to assemble the "detΔ ∉ p" for each top minimal prime `p`. |
| 4b | localization no-drop: `ringKrullDim O(Σ^r) = ringKrullDim (Localization.Away detΔ O(Σ^r))`, from "detΔ avoids every top-dim minimal prime" | the avoidance (4a) feeds the closed-point / minimal-prime height bookkeeping (`RadicalCatenary` is the `dim = card − height` template; the localization-no-drop sublemma was already scoped REACHABLE ~1–2 modules in `set-level-trivialization-adjudication.md` Q3). ~0.5–1 module given 4a. |

**Step-4 cost ≈ 1.5–2 modules, ONE chart (no pivot-cover).** This sits at the low end of the
`set-level-trivialization-adjudication.md` rung-4 budget (which flagged density as "the one step to
size carefully / second-most-likely place the estimate slips"). The de-risk is now positive: density
is NOT a wall and NOT a pivot-cover blow-up — it is the cheap branch, because the H'-equivariance the
sweep route already supplies is exactly the avoidance mechanism.

## Engine handles VERIFIED (file:line)

- `DeepChartRing.ΔPdeep` (`:107`) — detΔ = top-left r×r minor of the generic product `Matrix.of
  (multPoly d)`. The chart function, confirmed to be a product-minor (not end-factor).
- `CCodimCornerMono.exists_kostantPartition_partitionIdeal_eq_of` (`:378`) — **Fact A**: every top
  component is a corner-exactly-`r` partition ideal. `[IsAlgClosed k] [CharZero k]`; both feeding
  monotonicities LANDED (`CCodimZeroMono`/`CCodimZeroStrict`).
- `SigmaStratification.corner_rankPattern_eq_rank` (`:62`) — corner entry `= rank(mult A)`.
- `EndBaseChangeSweep.productRankLocus_eq_iUnion_smul_fibre` (`:81`) + `rank_endpoint_conj` (`:45`) —
  the H'-sweep identity and rank-invariance under endpoint base change.
- `OrbitClosure.orbitSet_baseChange_stable` (`:189`) / `baseChangePullback_*` — H'-stability of an
  orbit (closure), the input that makes "permute the minor into place inside the same component" legal.
- `FibreNormalForm.mult_smul` — `mult((g_N,g_0)·A) = g_N · mult(A) · g_0⁻¹`, the equivariance that
  turns an endpoint permutation into a product row/column permutation.
- `SchurChartIff.rank_eq_iff_schur_eq` (`:81`) — the chart-membership iff already LANDED on `detΔ≠0`.

## Decorrelated Codex (xhigh, gpt-5.1-codex-max) — independent read

Fired with the hypothesis WITHHELD (the four Qs + the explicit "top-left minor is not special"
tension; I did NOT tell it my "avoidance holds" conclusion). Transcript:
`codex/nodrop-density-{prompt,answer}.md`. Codex independently reached the IDENTICAL load-bearing
chain: **Q1** — every top component has generic product-rank `r`, so `detΔ` cannot vanish identically
(FACT); **Q2** — for any rank-`r` matrix `∃ g_N,g_0` with `g_N M g_0⁻¹ = [[I_r,0],[0,0]]`, top-left
minor `= 1`, and the endpoint action stays in the same orbit (so the single chart suffices, the
failure case being only generic-rank-`<r` components which are not top-dim); **Q3** — the
all-pivot-position cover equals `Σ^r` (`binom(d_N,r)·binom(d_0,r)` charts) but is unnecessary; **Q4**
— the (2,2,2) and (3,3,3) minors are not identically zero on any top component, with explicit
diagonal witnesses. Convergence on every load-bearing point; **Codex's θ=2 for (3,3,3)** is the same
set-vs-pattern-stratification discrepancy I flag above — orthogonal to the verdict.

## Close

- **Firmest result (witness certificate):** `U = {ΔPdeep ≠ 0}` is dense in every top-dimensional
  component of `Σ^r`. Certificate: Fact A (LANDED `exists_kostantPartition_partitionIdeal_eq_of`
  forces corner `= r` on top components) + Fact B (H'-stability of the component + a permutation in
  `GL_{d_N}×GL_{d_0}` moving any nonzero product-minor to the top-left). Exact-algebra confirmed on
  (2,2,2) r=1 and (3,3,3) r=2 (symbolic generic points, all three corner-2 strata).
- **Most likely thing to break it:** (a) Fact A's `[CharZero k]` — `exists_kostantPartition_…` is
  stated `[CharZero k]`; if step-4's ambient field is only `[IsAlgClosed k]` the assembly must
  thread `CharZero` (the DLN application is over `ℝ`/`ℂ`-type fields, so this is benign). (b) the
  bookkeeping that turns "detΔ ∉ every top minimal prime" into the ring-level `ringKrullDim` no-drop
  for the REDUCIBLE `O(Σ^r)` — it is the `RadicalCatenary` max-over-minimal-primes pattern, present
  but needs the "localization inverts a non-zero-divisor-mod-each-top-prime element" step wired; ~0.5
  module, low risk.
- **Next construction/consult to settle the open part:** a focused SPECIFY on rung 4b — pin the exact
  `ringKrullDim`-no-drop lemma shape (`detΔ ∉ ⋃ topMinimalPrimes ⟹ ringKrullDim (Away detΔ R⧸I) =
  ringKrullDim (R⧸I)`) against the LANDED `RadicalCatenary` `height_add_ringKrullDim_quotient_…`, to
  confirm 4b is ~0.5–1 module and not a hidden reducible-localization wall. That single check fixes
  step-4 at ≈1.5–2 modules.

# (S-min) achiever CERTIFICATE — the precise binding path for `IsResolutionAtlas.achiever` (pp-hall, 2026-06-22, #147)

**The last value-side field, as a math blueprint for fm3 to transcribe.** Sharpens the g134 (S-min)
sketch into a PRECISE achiever certificate against fm3's `routeMIota` ι, landing on
`IsResolutionAtlas.achiever` (`ResolutionAtlas.lean:138`):
`achiever : ∃ i, monomialThreshold (d i)(k i)(h i) = (((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat : ℝ≥0∞)/2`,
equivalently the `of_mult_and_achiever` witness `(i₀, j₀)` with `k i₀ j₀ = 1`, `h i₀ j₀ = m₀ − 1`. fm3
transcribes; this is the math, not the Lean. Framing settled (monomial cover, no additive squeeze, #37
resolved).

## The achiever datum (encoding-independent)
Let `m₀ := ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat` (the min codim; `lambdaCore M = ½·m₀`). The
achiever is:
1. **the minimising stratum** `T* ∈ argmin_{T ∈ Adm M} Mval M T`, with `Mval M T* = m₀`;
2. **the binding path** `i₀ : routeMIota M` — the root-to-leaf path whose dispatcher choices resolve each
   factor to its `T*`-prescribed rank, terminating at the binding center over `S(T*)`;
3. **the binding divisor** `j₀ : Fin (d i₀)` on that path — the codim-`m₀` exceptional divisor, with
   `(k i₀ j₀, h i₀ j₀) = (1, m₀ − 1)`, ratio `axisRatio (m₀−1) 1 = m₀/2 = ½·m₀`.
Then `monomialThreshold (d i₀)(k i₀)(h i₀) = ⨅_j axisRatio (h i₀ j)(k i₀ j) = ½·m₀` (the binding divisor
is the `⨅`-minimiser; combined with `threshold_ge`'s `≥ ½·m₀`, equality). This is exactly `achiever`.

## The exact data per `M` (verified, `g147_achiever_cert.py`)
| `M` | `m₀ = min Mval` | `lambdaCore = ½·m₀` | `T*` (a minimiser) | binding divisor `(k,h)` |
|---|---|---|---|---|
| `(2,2,2)` | 3 | 3/2 | `(1,0)` (rank-1 incidence) | `(1, 2)` |
| `(3,3,3)` | 7 | 7/2 | `(1,0)` | `(1, 6)` |
| `(2,2,2,2)` | 3 | 3/2 | `(1,0,0)` | `(1, 2)` |
| `(4,3,2)` | 6 | 3 | `(2,0)` | `(1, 5)` |
| `(2,1,2)` | 2 | 1 | `(0,0)` | `(1, 1)` |
`T*` is the prefix-rank tuple `t_j = rank(C_1⋯C_j)`, `t_L = 0`. In every case the binding divisor is
`(1, Mval(T*)−1) = (1, m₀−1)`, threshold `m₀/2`. ✓

## The binding path in `routeMIota` terms (the (2,2,2) anchor, depth-2)
**`(2,2,2)`, `T* = (1,0)`** (`M = (2,2,2)` reduced-width core `‖A₁·A₂‖²`, 2×2 factors):
The minimiser is the **rank-1 incidence stratum** `{rk A₁ ≤ 1, rk A₂ ≤ 1, A₁A₂ = 0}`, codim `Mval(T*) = 3`
— NOT the generic rank-2 stratum (codim 4). So the binding path has genuine **depth** (#134): it is not
the trivial first chart. In `RouteMTree` terms (g140's inductive `{leaf, nodeC1, nodeC2, nodeC4, nodeC5}`):
- `node 0` (`M=(2,2,2)`): active factor `C₁` (2×2), `T*` wants `rank(C₁) = t_1 = 1` (a rank-1 coupled
  defect, `t_1 = 1 < 2 = M_0`) → **`nodeC1`** with the `PivotChoice` = the 1×1 pivot exposing the rank-1
  locus. (Step A `pivotBlowupOn` → `x_p²·Q`; step B the Schur-descent.)
- the binding center over the full `T*` stratum (codim 3) is resolved with the binding divisor
  `(k,h) = (1, 2)` — matching the banked (2,2,2) **`ρ`-chart** (`Case222`: `δ`-branch → `δ=ρ,u=ρξ,v=ρη`,
  `F = α²ρ²·[…]`, Jacobian `|ρ|²`, `(k,h)=(1,2)`, ratio `3/2 = ½·m₀`). The `ρ` divisor IS `j₀`.
So `i₀` = the `nodeC1` path resolving `C₁` to rank 1, terminating at the `ρ` binding divisor `j₀`; the
banked `Case222` `ρ`-chart is the concrete `i₀` for `M=(2,2,2)`.

**General `M`, `T* = (t_1,…,t_L)`:** `i₀` is the path whose dispatcher choice at each node `s` resolves
`C_s` to rank `t_s` (the `T*`-prescribed rank — a `nodeC1`/`nodeC5` pivot choice, or `nodeC2` pass-through
where `t_s = t_{s-1}`); the path terminates at the binding divisor over `S(T*)`, codim `Mval(T*) = m₀`,
`(k,h) = (1, m₀−1)`.

## Why the binding divisor is a SINGLE `(1, m₀−1)` (`of_mult_and_achiever`'s `j₀`, `hh₀`)
`monomialThreshold = ⨅_j axisRatio (h_j)(k_j)` is the MIN over the path's divisors, so the path's
threshold `= ½·(min codim over its divisors)`. For it to EQUAL `½·m₀`, the path's smallest-ratio
(binding) divisor must have `(h+1) = m₀`, i.e. **a single divisor `j₀` with `h = m₀−1`** (the others have
larger ratio, don't bind). This holds in both realisation forms (`g147_binding_single_divisor.py`):
- **(a) one-shot binding** (r1-design §2): after the regular pivot split exposes the residual block whose
  vanishing IS `S(T*)`, a SINGLE codim-`m₀` center blow-up gives `(1, m₀−1)` directly — the (2,2,2)
  `ρ`-chart (`h=2=m₀−1`). ✓
- **(b) incremental**: even if codim accrues over several per-factor divisors, the BINDING (min-ratio) one
  still has `h+1 = m₀` (`h = m₀−1`); the rest are larger-ratio and don't bind.
Either way `of_mult_and_achiever`'s `(i₀, j₀, hk₀: k i₀ j₀ = 1, hh₀: h i₀ j₀ = m₀−1)` is supplied. The
`k = 1` is the regular-sequence / multilinearity fact (#132: scaling one factor by `x` ⟹ `F` degree-2 in
`x` ⟹ `k=1`); `h = m₀−1` is the codim-`m₀` smooth-center blow-up Jacobian (`pivotBlowupOnDeriv_det =
x_p^{card−1}`, `card = m₀`).

## Realizability — the achiever path EXISTS (Core.RankPattern / `baseChange_normalForm`)
The achiever requires the minimising stratum `T*` to be REACHED by a path — the (S-min) obligation
(strictly weaker than full surjectivity; #134). This is the realizability of `T*`:
- `T* ∈ Adm M` is realizable: the **Gabriel normal form** `⊕ M^{m̄}` realizes the rank pattern whose
  prefix is `T*` (`Core.OrbitKostant`: `RealizableRank M = Set.range (rankFn M)`;
  `Orbit.baseChange_normalForm` builds the realizing tuple). The seam is
  `prefix : RealizableRank M → Adm M` (the first-row `r_{1,j}` of a realizable full rank pattern is an
  admissible prefix tuple).
- So the binding center `{rank pattern = T*}` is nonempty, its codim `= Mval(T*) = m₀` (thread-03 /
  `codim S(t) = Mval(t)`), and the dispatcher's pivot choices reach it (the `nodeC1`/`nodeC5` branch
  resolving each factor to its `T*`-rank). ⟹ `∃ i₀ : routeMIota M` reaching `T*`'s binding divisor.
This is precisely `IsResolutionAtlas.achiever`: `∃ i₀, monomialThreshold (d i₀)(k i₀)(h i₀) = ½·m₀`.

## Net for fm3 — what to transcribe into `achiever`
Build the witness `(i₀, j₀)` for `of_mult_and_achiever` (or `achiever` directly):
- **`i₀`** = the `routeMIota M` path whose dispatcher choices resolve each factor to its `T*`-rank
  (`T* = the inf' minimiser` — for the `(2,2,2)` anchor, the banked `Case222` `ρ`-chart path; for general
  `M`, the `nodeC1`/`nodeC5`/`nodeC2` sequence through `T*`'s binding center). Realizability =
  `Core.baseChange_normalForm` (the minimiser is hit by a tuple); the path reaches it via the dispatcher.
- **`j₀`** = the codim-`m₀` binding divisor on `i₀`, with `hk₀: k i₀ j₀ = 1` (regular sequence, #132
  multilinearity) and `hh₀: h i₀ j₀ = m₀−1` (codim-`m₀` blow-up Jacobian, `pivotBlowupOnDeriv_det`).
- then `monomialThreshold_eq_half_of_binding` (already in `of_mult_and_achiever`) gives `= ½·m₀`.
The `(2,2,2)` anchor is the concrete vertical check (#43): `i₀ = ρ`-chart, `j₀ = ρ`, `(1,2)`, `½·3 = 3/2`
matches `lambdaCore (2,2,2) = 3/2`. If fm3's `routeMIota` encodes paths differently (flat list / Σ-type
vs the inductive `RouteMTree` leaves), the achiever DATUM is the same — `i₀` is the path-through-`T*`,
`j₀` its binding divisor; just re-spell `i₀` in that encoding.

## Most likely thing to break this
The achiever's `i₀` must be a path the dispatcher actually PRODUCES (not just an abstract stratum). The
(S-min) realizability (`baseChange_normalForm` hits `T*`) gives the stratum is nonempty; the dispatcher
reaching it needs the `nodeC1`/`nodeC5` branch to select the `T*`-rank pivot at each node — which it does
by construction (the pivot choice = the resolved rank, g140). The one Lean-side check: that `routeMIota M`
is INHABITED at the `T*`-resolving choices (the dispatcher's branch for the rank-`t_s` pivot is a valid
`PivotChoice` — it is, since `t_s ≤ t_{s-1} ≤ M`-bounds make the rank-`t_s` minor selectable). For the
`(2,2,2)` anchor this is concrete (the `ρ`-chart is banked); for general `M` it rides the dispatcher's
totality (#39). If #39's dispatcher doesn't produce the `T*`-path for some `M`, that surfaces in the build
— but the (2,2,2) anchor + the realizability give high confidence.

## Provenance
Sharpens g134 ((S-min) witness sketch) against `IsResolutionAtlas`/`of_mult_and_achiever`
(`ResolutionAtlas.lean`, fm2/route-m-atlas). The achiever datum: `T*` = `inf' Mval` minimiser, binding
path through `T*`, binding divisor `(1, m₀−1)`. Realizability = `Core.OrbitKostant` /
`baseChange_normalForm` + the `prefix : RealizableRank → Adm` seam. The `(2,2,2)` `ρ`-chart anchor (#43)
is the concrete instance. Scripts: `g147_achiever_cert.py`, `g147_binding_path.py`,
`g147_binding_single_divisor.py` in `g129-scripts/`. Builds on #134, #131 (codim), #132 (`k=1`), r1-design
§2 (binding divisor), the #37-resolved monomial framing.

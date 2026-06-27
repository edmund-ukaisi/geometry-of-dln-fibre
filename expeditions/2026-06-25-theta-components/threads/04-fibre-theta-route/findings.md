# Thread 04 — fibre-θ route: the (A)-decoupling kill-condition (pen-and-paper) — certificate

**Persisted by the controller.** Exact algebra (Singular `primdecGTZ`/`radical` over ℚ) + a definitional
certificate + decorrelated Codex (xhigh, converged). 

## Verdict: kill-condition HOLDS in the strongest form — Route A open, reducedness wall OFF the θ path

**`detΔ ≡ 1` on the entire fibre scheme** (not just: no top component in `V(detΔ)`). So `detΔ` is a **unit**
in `O(fibre) = R/J` (not merely a non-zero-divisor); `(R/J)_{detΔ} ≅ R/J`; localization kills nothing.

### The load-bearing definitional fact (general — any `d`, any `r`, any ring)
`detΔ = ΔPdeep d r = det(top-left r×r block of multPoly)` (Lean: `DeepChartRing.lean:112`,
`DeterminantalChartRing.lean:233`, `SourceNoDrop.lean:88`) — a function of the **product `mult(A)` alone**.
The fibre ideal `J = (mult(A)_{ij} − E_{ij})` forces `mult(A) = E = diag(I_r,0)` in `R/J`, so its top-left
`r×r` block = `I_r`, hence **`detΔ = det(I_r) = 1`, i.e. `detΔ − 1 ∈ J`.** One-line definitional consequence;
no radicality / equidimensionality / `IsAlgClosed` / `CharZero` needed. (Cleaner general restatement of the
per-case `SourceNoDrop` Fact B.)

## Exact-algebra certificate (Singular primdec over ℚ) — fibre #top = cTheta(d−r) = C(m,|δ|)

Convention: `d=(d_0,…,d_N)` has `N` arrows = `N` matrix factors, `mult = A_N⋯A_1` (`Setup.lean:51`).

| case | factors | fibre dim | codim | #minprimes | **#top** | `cTheta(d−r)` | `detΔ≡1 on J` |
|---|---|---|---|---|---|---|---|
| (2,2,2) r=1 | 2 | 4 | 4 | 2 | **2** | C(2,1)=2 ✓ | NF(detΔ−1)=0 on J |
| (2,2,2,2) r=1 | 3 | 8 | 4 | 3 | **3** | C(3,1)=3 ✓ | NF=0 on J |
| (2,2,2,2,2) r=0 | 4 | 13 | 3 | 10 | **6** | C(4,2)=6 ✓ | r=0 ⟹ detΔ=det(∅)=1 |
| (2,2,3) r=1 | 2 | 5 | 5 | 2 | **1** | C(2,0)=1 ✓ | NF=0 (non-equidim: +codim-6 lower) |
| (3,3,3) r=2 | 2 | 9 | 9 | 2 | **2** | C(2,1)=2 ✓ | NF=0 |
| (2,1,2) r=0 | 2 | 2 | 2 | 2 | **2** | C(2,1)=2 ✓ | r=0 ⟹ detΔ=1 |

`C(m,|δ|)` counts **top** components only. `(2,2,3)` r=1 shows the kill-condition holds even when the fibre is
NOT equidimensional. `(2,2,2,2,2)` r=0: 10 minprimes = **6 top (codim 3)** + 4 lower (codim 4, "one factor=0",
C(4,1)=4) — the **6 is the top count** (matches QIP brute-force 6 + cTheta) — corrects an earlier 5-factor
mis-run. Level separation: θ matches `cTheta(d−r)`; codim does NOT match `cValue(d−r)` (expected — different claim).

## Mechanism (structure, as data — Codex-concurred)
Block-triangular on the chart: `A_i = [[I_r, H_i],[0, B_i]]`. A rank-`r` product forces a rank-`r`
through-line; quotienting leaves a residual representation of dim `(d_0−r,…,d_N−r)` with **zero product**
`B_N⋯B_1 = 0`, plus an affinely-solvable linear equation in the `H_i`. This is route-A transport in disguise,
and explains the shift identity component-preservingly (the affine `H`-stratum adds no components).

## Scope (name the theorem honestly)
- `detΔ−1 ∈ J`: any `d`, any `r`, any commutative ring. No `IsAlgClosed`/`CharZero`.
- Fibre nonemptiness needs `r ≤ min_i d_i` (every internal width); else vacuous.
- r=0: `detΔ = det(0×0) = 1` (`det_fin_zero`); chart = all of `Rep_d`.

## Open part / what would break it
Route A transports the **component count/bijection**, not a reduced bundle. Still needs: (1) `orderIsoOfPrime`
wiring (bijection of minimal primes through `e`); (2) the **shift-width identity** `numTop(fibre d E_r) =
cTheta(d−r)` — verified on 6 cases (non-square / valley / r=0,1,2) but **not proved in general here**; its
general form is LR Lemma 4.5 (cited). The `detΔ`-unit fact removes the reducedness blocker; it does not by
itself prove the count.

## Next step (controller-synthesized route for the formaliser)
1. `detΔ_unit_on_fibre` : `detΔ − 1 ∈ fibreGenIdeal` — one-liner from `mem_fibre` + `chartΔ_normalForm`.
2. Transport `bijOn_partitionIdeal_topComponents` (Σ̄^r, PROVED) through `e` via `IsLocalization.orderIsoOfPrime`
   (reducedness-free, since `detΔ` unit) → fibre top-components ↔ Σ^r top-components.
3. The shift-width identity → `cTheta(d−r)` (the substantive piece; check whether the engine already has a
   `numTop` rank-shift analogous to the proved `cCodim d r = cValue(d−r)`; if not, it's the named input).

## Artifacts
- `threads/04-fibre-theta-route/scripts/` — `fib222r1b.sing`, `fib2222r1.sing`, `fib22222r0_fixed.sing`,
  `fib223r1.sing`, `fib333r2.sing`, `fib212r0.sing` (run `Singular -q FILE < /dev/null`), `qip.py`, `ctheta.py`.
- `threads/04-fibre-theta-route/codex/killcond-{prompt,answer}.md` (decorrelated xhigh).

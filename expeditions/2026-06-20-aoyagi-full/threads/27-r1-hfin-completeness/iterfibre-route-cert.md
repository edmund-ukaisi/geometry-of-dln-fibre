# R1 hfin route — the iterated-fibre peel does NOT generalize to corank-≥2; it is a special-class method

**Seat:** `pen-and-paper` (route adjudication). **Date:** 2026-06-25. **Thread:** `27-r1-hfin-completeness`.
**Question (controller):** the hfin `(4,4,2,2)` build landed via an ITERATED-FIBRE route
(`MatMulFibre.fibre_lintegral_mul_le`, S2-free, avoids the r²-chart Δ-blow-up). Does it GENERALIZE to
`½·minAdm` for general `M` — handle the corank-≥2 BINDING core — or only a special class?
**Method:** exact-rational threshold accounting against `½·minAdm`, with the fibre lemma's intrinsic
per-peel threshold read from the Lean (`fibreConst`'s `Kbound`). Scripts `scripts/iterfibre_*.py`.

---

## VERDICT: the iterated-fibre route is STRICTLY WEAKER than `½·minAdm` for the corank-≥2 binding
## cases — it does NOT generalize. It is a clean **special-class** method (a `min`-of-widths ceiling);
## the corank-≥2 binding needs the rank-stratified `{V=0}` resolution (thread 27 main cert). USE BOTH:
## iterated-fibre where it matches, rank-stratified for the rest.

> The fibre lemma `∫_X frobSq(X·Y)^{−c'} ≤ const·frobSq(Y)^{−c'}` has intrinsic per-peel threshold
> `p/2` = ½·(rows of the LEFT factor `X`) — it extracts ONE max-entry column of `Y` and the `p`-dim
> per-row shear, seeing NONE of `Y`'s rank/coupling. Iterated, its ceiling is
>
>     best_iterfibre(M) = max_s min( {M_i/2 : i<s} ∪ {M_i/2 : i>s+1} ∪ {M_s·M_{s+1}/2} )
>
> (choose a terminal factor `A_s`, peel left factors by their rows, right factors by their cols,
> terminal = the factor's full Morse). This is `O(max single width)` — but `½·minAdm` is a SUM of block
> codims ALONG the descent. So iterated-fibre undershoots whenever the singularity ACCUMULATES across
> layers (the corank-≥2 binding, multi-layer coupling). EXACT (`scripts/iterfibre_class.py`,
> `iterfibre_criterion.py`):

| `M` | best-iterfibre | `½·minAdm` | verdict |
|---|---|---|---|
| `(2,1,2)` | 1 | 1 | MATCH |
| `(2,2,4)` | 2 | 2 | MATCH |
| `(4,4,2,2)` | 2 | 2 | MATCH (the build's case) |
| `(1,1,2)`, `(1,2,3)`, `(2,2,5)` | … | … | MATCH |
| **`(2,2,2)`** | **1** | **3/2** | **WEAKER** |
| **`(3,3,4)`** | **2** | **4** | **WEAKER (corank-2 binding)** |
| **`(3,3,3)`** | **3/2** | **7/2** | **WEAKER (corank-2 binding)** |
| **`(4,4,4)`** | **2** | **6** | **WEAKER** |
| `(3,3,3,3)` | 3/2 | 3 | WEAKER |
| `(5,3,4)` | 5/2 | 11/2 | WEAKER |
| `(2,3,4,2)`, `(2,4,2)`, `(2,2,3)`, `(3,2,3)`, `(2,2,2,2)` | … | … | WEAKER |

The route MATCHES only the special class (essentially `(2,1,2)`/`(2,2,4)`/`(4,4,2,2)`-like: where the
binding is a single clean leaf/Morse factor "seen" by one peel + terminal). It is WEAKER for **(2,2,2)
itself** (1 vs 3/2 — (2,2,2) is done in Lean via the OTHER `recStep` route, not this) and ALL the
corank-≥2 binding cores `(3,3,4)`, `(3,3,3)`, `(2,2,4-internal)`, etc.

---

## 1. Why the per-peel threshold is `p/2` and it does NOT see `Y`'s rank (the mechanism)

`fibre_lintegral_mul_le` (`MatMulFibre.lean:399`): `frobSq(X·Y) ≥ (Y_{ℓj})²·Σ_i u_i²` for the max-abs
entry `(ℓ,j)` of `Y` and the per-row shear `u_i` (det-1 MP in `X`); `(Y_{ℓj})² ≥ frobSq(Y)/(nq)`. So
`∫_X frobSq(X·Y)^{−c'} ≤ (nq)^{c'}·frobSq(Y)^{−c'}·∫_u (Σu_i²)^{−c'}`, and the `u`-fibre `∫(Σ_{i=1}^p
u_i²)^{−c'}` is a `p`-dim Euclidean Morse — finite iff `c' < p/2` (`fibreConst`'s `Kbound p c'`
factor, which GENUINELY blows up at `c' = p/2`, verified in the Lean). The bound uses ONLY one max
column of `Y`; it discards `Y`'s rank structure. So the peel's threshold is `p/2` = the left-factor
row count, full stop — independent of how singular `Y·(rest)` is.

**Consequence:** iterating peels MULTIPLIES the `Y`-independent constants but the binding threshold is
the MIN of the per-peel `M_s/2` and the terminal Morse. It cannot accumulate the descent's block-codim
sum. This is the intrinsic ceiling.

## 2. The exact closed-form ceiling + the match criterion (verified)

`best_iterfibre(M) = max_s min({M_i/2 : i<s} ∪ {M_i/2 : i>s+1} ∪ {M_s·M_{s+1}/2})`
(`scripts/iterfibre_class.py` via either-end peel; `best_via_terminal` closed form, both agree).
The route SUFFICES for `M` iff `best_iterfibre(M) = ½·minAdm(M)` — a decidable check. Structurally this
holds iff the singularity is **concentrated in a single factor** (one binding block, the rest clean/
full-rank), so that one terminal-Morse + clean peels reach `½·minAdm`. It FAILS (undershoots) whenever
`½·minAdm` exceeds the largest single-factor Morse reachable — i.e. the genuine multi-layer / corank-≥2
coupling, exactly the cases the rank-stratified `{V=0}` resolution was designed for.

**Direct answer to the controller's central question:** the corank-≥2 BINDING core `‖Δ·S‖²` (`(3,3,4)`,
`(3,3,3)`, …) gives `½·minAdm` STRICTLY ABOVE `best_iterfibre` — the iterated-fibre proves
`∫F^{−c'} < ⊤` only for `c' < best_iterfibre < ½·minAdm`, so it does NOT prove `rlctAtOn ≥ ½·minAdm`
there. It BREAKS at corank-≥2 binding. (The thread-27 main cert + the `{V=0}` recursion remain the
route for those.)

## 3. Can it be refined to `½·minAdm`? (the ceiling is intrinsic to single-column shear)

- **Peel order / either end:** already taken (the `max_s` over terminal choice + left/right peels);
  does NOT close the gap (the table is the BEST over orders).
- **Column-peel (transpose):** subsumed — peeling the right factor is `frobSq(P) = frobSq(Pᵀ)`, the
  left-peel of the transpose; the `max_s` formula already includes right-peels (cols).
- **A smarter fibre bound seeing >1 column of `Y`:** this is precisely where the single-column shear
  is the ceiling — to capture the residual's rank you must resolve `Y` (the coupled descent), i.e. you
  are back to the rank-stratified resolution. The fibre lemma's `Y`-as-black-box (one column) is what
  makes it clean AND what caps it.

So `best_iterfibre` is a genuine ceiling of the single-column-shear fibre method. Reaching `½·minAdm`
in general requires seeing the residual's rank — the rank-stratified `{V=0}` resolution.

## 4. Net recommendation (the hybrid route)

The iterated-fibre route is a valuable, S2-free, low-risk method **for the special class where
`best_iterfibre(M) = ½·minAdm`** (decidable; incl. the `(4,4,2,2)` build + `(2,2,4)` corank-2-NON-
binding + the leaf-dominated cases). For the rest — **all corank-≥2 BINDING cores** (`(3,3,4)`,
`(3,3,3)`, `(4,4,4)`, and even `(2,2,2)`) — use the **rank-stratified `{V=0}` recursion** (thread-27
main cert + the #54 recStep spec, S2-only-validated). HYBRID: dispatch per `M` by the decidable
`best_iterfibre(M) =?= ½·minAdm` check. The iterated-fibre does NOT supersede the rank-stratified spec;
it COMPLEMENTS it (handles the easy class cheaply, leaving the genuine corank-≥2 build to the
rank-stratified cover — which the #53 cert validated terminates S2-only).

This does NOT change the hero-task feasibility verdict (R1 fully provable from scratch, S2-only): the
rank-stratified cover handles every `M` including corank-≥2; the iterated-fibre is a cheaper shortcut
for the class it covers, reducing (not eliminating) the rank-stratified build's scope.

## 5. Scope / proved vs structural

- **Proved (exact rational):** the per-peel threshold `p/2` (intrinsic, from `fibreConst`'s `Kbound`);
  the closed-form ceiling `best_iterfibre`; the MATCH/WEAKER classification on the surveyed family
  (incl. all corank-≥2 binding cores WEAKER); the `(4,4,2,2)`/`(2,2,4)` MATCH (consistent with the
  build).
- **Structural:** the exact closed characterization of the MATCH-class as a set of `M` (it is the
  decidable predicate `best_iterfibre(M) = ½·minAdm`; a cleaner combinatorial description — "single-
  factor-concentrated binding" — is approximate, the `#nonzero-blocks ≤ 1` proxy fails on `(2,2,3)`/
  `(2,4,2)`, so the decidable check is the honest criterion).
- **What would change it:** a fibre bound that sees the residual's rank (not one column) — but that IS
  the rank-stratified resolution; the single-column shear's ceiling is intrinsic.
- **Decorrelated Codex consult:** fired (`codex/iterfibre-prompt.md`); fold the answer in when it lands.

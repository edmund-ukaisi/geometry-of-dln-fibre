# Cert #104b — the general per-node `hstep` as a TWO-STRATA weighted-cover (the SOUND uniform route)

**Seat.** pen-and-paper (witness), DLNFibre aoyagi-full, task #104 (R1 geometric heart), route (ii).
**Builds on** `cert-104-general-node-blowup.md` (the obstruction finding) + its sympy. **Method.**
exact symbolic algebra + exact-integer combinatorics + a fresh decorrelated xhigh Codex pass.
**Verification:** `sympy/node_blowup_cert_104.py` (checks V1–V9, all pass). **Codex:**
`codex/node-cover-104b-{prompt,answer}.md` (independent, confirms the cover sound).

> **Headline.** The general per-node `hstep` is realized SOUND and UNIFORMLY (all nodes, both
> regimes) as the RLCT of a **two-strata weighted cover** of one blow-up chart:
> $$\operatorname{rlctAtOn}(\texttt{dlnLoss}\,M\,0)(\text{deepest}) \;=\; \min\Big\{\;\tfrac{mk}{2}\;,\; \operatorname{rlctAtOn}(\texttt{core})(0)\;\Big\}, \qquad \operatorname{rlctAtOn}(\texttt{core})(0) = \tfrac{n}{2} + \operatorname{rlctAtOn}(\texttt{dlnLoss}(red M)\,0)(0).$$
> Composed: $\tfrac12\min\{mk,\,n+R\} = \tfrac12\operatorname{minAdm}(M) = \tfrac{nReg}{2} + \tfrac{R}{2}$
> (`R := minAdm(red M)`, `nReg := minAdm M − minAdm(red M)`). The min is between the **`D₀`
> exceptional divisor** (the `y₀` blow-up of `{A=0}`, ratio `mk/2`) and the **`Erow`-Morse + child
> stratum** (ratio `(n+R)/2`). In REGULAR nodes (`n ≤ nReg`) the core stratum binds; in WIDE-TAIL
> nodes (`n > nReg`) the `D₀` divisor binds. **One presentation, sound at both** — this resolves the
> `cert-104` obstruction (which was an artifact of dropping the outer `D₀` divisor and reading only
> the core stratum with `nReg := n`). No sub-obstruction found: the cross term does not cap `core`,
> the strata glue, and the cover reconciles exactly with the binding-spine `hstep`.

---

## 0. What the binding spine actually demands (the wiring fact that reframes #104)

`BindingSpine.binding_rlct_eq_lambdaCore_of_hstep'` instantiates `rlctOf := fun M => rlctAtOn
(dlnLoss M 0) (deepest)` and consumes (`BindingRecursion.lean:16-17`):

$$
\texttt{hstep}: \quad \operatorname{rlctAtOn}(\texttt{dlnLoss}\,M\,0)\,0 \;=\; \texttt{ofReal}\big(nReg(M)/2\big) + \operatorname{rlctAtOn}(\texttt{dlnLoss}(redOf\,M)\,0)\,0,
\qquad nReg(M) = \operatorname{minAdm} M - \operatorname{minAdm}(redOf\,M).
$$

The equation is at the **true loss `dlnLoss M 0`** level — NOT at the `flatCore`/`core` level. This is
exactly why the MP-chart route (#148, `dlnLoss_O1_descent`) was vacuous (its squeeze of `dlnLoss∘χ`
by `smoothBlockSplitForm` is unsatisfiable: the raw loss has a rank-0 Jacobian, not comparable to a
Morse form). And it is why `cert-104`'s single-pivot `flatCore`-with-`nReg=n` route over-counted in the
wide-tail regime: `descentStep` computes `rlctAtOn(flatCore)(0,0)`, which is `rlct(core) = n/2 + child`,
**not** `rlct(dlnLoss M 0)`. The bridge between them is the missing outer divisor.

---

## 1. The two-strata cover (one chart, two divisors via product + sum splits)

The single-pivot blow-up `φ₁` (`A = y₀·Â`, `Â` top-left `= 1`) gives, exact (V1, `cert-104` §1–2):

$$
\texttt{dlnLoss}\,M\,0 \circ \varphi_1 \;=\; y_0^2\cdot\texttt{core}, \qquad |\det J_{\varphi_1}| = y_0^{\,mk-1}, \qquad \texttt{core} = \|\hat A\cdot B\|^2.
$$

`core` is a function of `z = (u, v, W, B)` ONLY — it does **not** contain `y₀`. So in the blow-up
chart, `dlnLoss∘φ₁` is a **product** of two factors in **disjoint variable groups**:

- **Group `{y₀}`** (1-dimensional): the loss factor `y₀²` carrying the Jacobian weight `y₀^{mk−1}`.
- **Group `{u,v,W,B}`**: the residual `core`, weight `1`.

### 1a. OUTER step — the product-min (the `D₀` divisor) [VERIFIED, Fubini]

The weighted-cover transport (the SOUND route `RouteMO1Bridge` requires) keeps the Jacobian in the
integrand. By Fubini over the disjoint groups:

$$
\int |y_0^2\,\texttt{core}|^{-c}\, y_0^{\,mk-1}\,d\mathrm{vol} \;=\; \Big(\!\int_{0} |y_0|^{\,mk-1-2c}\,dy_0\Big)\cdot\Big(\!\int \texttt{core}^{\,-c}\,dz\Big).
$$

The `y₀`-integral converges near `0` iff `mk−1−2c > −1 ⇔ c < mk/2`. Hence the **outer combine is a MIN**:

$$
\operatorname{rlctAtOn}(\texttt{dlnLoss}\,M\,0)(\text{deepest}) \;=\; \min\Big\{\;\tfrac{mk}{2}\;,\; \operatorname{rlctAtOn}(\texttt{core})(0)\;\Big\}.
$$

The `D₀` divisor (the `{A=0}` blow-up exceptional divisor) has monomial data `(k_mon, h) = (1, mk−1)`,
ratio `(h+1)/(2k_mon) = mk/2`. (RLCT of a **product** in disjoint variables = **min** of the factor
thresholds; contrast a **sum**, which is **additive** — both rules are used here, at different levels.)

### 1b. INNER step — the sum-additive `core` (the Erow-Morse + child stratum) [VERIFIED]

Schur-eliminate `Â`'s unit pivot (`cert-104` §2): with `Erow = B[0,:] + u·Bred`, `S = W − v·u`,
`Bred = B[1:,:]`,

$$
\texttt{core} = \underbrace{\sum_{j=1}^{n} \texttt{Erow}_j^2}_{\text{n Morse squares}} + \sum_{i,j}\big(v_i\,\texttt{Erow}_j + (S\,Bred)_{ij}\big)^2.
$$

**No internal cap (the sub-obstruction the controller flagged — checked, absent).** Because `Â`'s
pivot is now a **unit** (`=1`), `core` is no longer at a rank-deficient origin: the `Erow` block is
`n` genuine clean smooth directions (`Erow_j = B[0,j] + (u·Bred)_j` is a det-1 affine shear of the
free top-row coordinate `B[0,j]`). The cross term `v_i·Erow_j` does **not** lower `rlct(core)`: for
`v` bounded near the deepest point,

$$
\big\|\,v\,\texttt{Erow} + S\,Bred\,\big\|^2 \;\asymp\; \|S\,Bred\|^2 \quad\Longrightarrow\quad \texttt{core} \;\asymp\; \sum_j \texttt{Erow}_j^2 + \|S\,Bred\|^2 \;=:\; H
$$

(two-sided, by triangle inequality both ways; comparable nonnegative analytic germs share the local
threshold — Codex-confirmed). `H` is a **sum in disjoint variable groups** (`{Erow_j}` vs the child's
`{S, Bred}`), so by the additive rule (Watanabe; the existing `rlct_additive_smooth_block`):

$$
\operatorname{rlctAtOn}(\texttt{core})(0) \;=\; \operatorname{rlctAtOn}(H)(0) \;=\; \tfrac{n}{2} + \operatorname{rlctAtOn}(\|S\,Bred\|^2)(0) \;=\; \tfrac{n}{2} + \tfrac{R}{2},
$$

since `‖S·Bred‖² = dlnLoss(red M) 0` (the child, `cert-104` §2, V3) has RLCT `R/2`. **The min happens
only at the OUTER `y₀` product; the inner core has no second min.**

### 1c. Composed [VERIFIED V7]

$$
\operatorname{rlctAtOn}(\texttt{dlnLoss}\,M\,0)(\text{deepest}) = \min\big\{\tfrac{mk}{2},\, \tfrac{n}{2}+\tfrac{R}{2}\big\} = \tfrac12\min\{mk,\, n+R\} = \tfrac12\operatorname{minAdm}(M),
$$

sympy-verified over `(m,k,n) ∈ 1..8 × 1..8 × 1..12` (V7), using `minAdm(m,k,n) = min{mk, n+R}` (V4).

---

## 2. Reconciliation with the spine `hstep` [VERIFIED V8]

The spine needs `rlct(F) = nReg/2 + child` with `nReg = minAdm M − minAdm(red M)` and `child = R/2`.
The cover gives `rlct(F) = min{mk/2, n/2 + R/2}`. These coincide because

$$
\min\{mk,\, n+R\} = nReg + R, \qquad nReg = \min\{mk-R,\, n\},
$$

so `min{mk/2, n/2+R/2} = (nReg + R)/2 = nReg/2 + R/2`. Verified exactly over the range (V8). **The
cover IS the spine `hstep`, uniformly.** Both regimes:

| node | `mk/2` (`D₀`) | `(n+R)/2` (core) | `min` = rlct | `nReg` | binder |
|---|---|---|---|---|---|
| (2,2,2) | 2 | 3/2 | **3/2** | 2 | Erow+child (REGULAR) |
| (3,3,3) | 9/2 | 7/2 | **7/2** | 3 | Erow+child (REGULAR) |
| (2,2,4) | 2 | 5/2 | **2** | 3 | `D₀`(y₀) (WIDE-TAIL) |
| (2,1,3) | 1 | 3/2 | **1** | 2 | `D₀`(y₀) (WIDE-TAIL) |
| (1,1,2) | 1/2 | 1 | **1/2** | 1 | `D₀`(y₀) (WIDE-TAIL) |

`(2,2,4)` is `cert-104`'s smallest obstruction node — now SOUND under the cover (`D₀` binds at `2`).

---

## 3. The resolution wording (Codex's one correction — recorded)

A single pivot chart + the displayed Schur split is **not by itself** a complete normal-crossing
resolution. The sound statement is **recursive**: after the first `{A=0}` blow-up, the `y₀` divisor
gives the `mk/2` candidate, and the unit-pivot `core` reduces to `n/2 +` the child RLCT, the child
being resolved by the SAME procedure on the smaller chain `red M`. The other pivot charts (different
`(i,j)` pivots) are equivalent by row/column permutations, so no residual lower stratum is missed. The
`min{mk/2, n/2+R/2}` IS the RLCT, computed by this recursion — which is exactly the binding-spine
recursion. (This matches the S2 normal-crossing reading: RLCT = min over the resolution's exceptional
divisors of `(ord(Jac)+1)/(2·ord(loss))`; here the binding divisor along the descent is whichever of
`D₀` or the deeper child-divisor has the smaller ratio.)

---

## 4. What the Lean cover datum must carry — for a formaliser

> **CORRECTION (2026-06-23, R1 transport-producer lane, decorrelated-Codex-confirmed).** The
> single-chart route in items 1–2 below — "define `φ₁`, feed it through `weightedThreshold_transport_aux`,
> then apply the outer product-min" — is **UNSOUND as a Lean producer**. `weightedThreshold_transport_aux`
> (`S1Transport.lean`) requires `Function.Surjective π`, and the single-pivot blow-up `φ₁` is **NOT
> surjective** as a self-map of the flat ambient `Fin N → ℝ`: with `A = y₀·Â`, `Â₀₀ = 1`, the A-block
> image is `{A₀₀ ≠ 0} ∪ {A = 0}`, missing the positive-measure stratum `{A₀₀ = 0, A ≠ 0}` which
> **accumulates at the origin** (e.g. `A = (0,0;t,0) → 0`). The transport-file header itself documents
> that the `≥` direction is FALSE without surjectivity. Consequences: (a) a single pivot chart cannot
> see the loss germ on the missing stratum, so it is INSUFFICIENT for the equality; (b) the
> surjectivity-free `weightedThreshold_le_transport` gives only the bound `rlctAtOn F 0 ≤ min{mk/2,
> rlctAtOn core 0}`, never the equality. **The SOUND route is the argmax/pivot COVER** — the `mk`
> pivot charts covering `{A ≠ 0}`, glued by a finite-cover-locality lemma so `rlctAtOn F 0 = ⨅_pivot`
> (per-chart threshold); by row/col-permutation symmetry the `⨅` collapses to `min{mk/2, rlctAtOn
> core 0}`. This is the SAME engine the existing `(2,2,2)` resolution uses (`Case222RouteMCover` +
> the `monomialThreshold = ⨅ axisRatio` machinery, built on `g5_flat_cover`, NOT on `transport_aux`);
> indeed `axisRatio (mk−1) 1 = mk/2` (`axisRatio_regularSeq`) is exactly the `(e+1)/2` y₀-side value of
> item 2's outer product-min — the cover already computes this divisor ratio. The outer product-min
> lemma `weightedProductMin_mono1D_of_ne` (proved, `S1WeightedProductMin.lean` @499ded2f) STANDS, but
> as the **per-chart** threshold computation inside a cover, not as a standalone true-loss producer.
> The pen-and-paper MIN-fact (`= ½·minAdm`) below is verified TRUTH; only the single-chart-Lean-route
> is corrected. Artifacts: `codex/transport-surjectivity-{prompt,answer}.md`.

The producer `RouteMNodeDescentExists M S` must emit, per non-leaf node, a datum that establishes
**at the true-loss level**:

$$
\operatorname{rlctAtOn}(\texttt{dlnLoss}\,M\,0)(\text{deepest}) = \min\big\{\tfrac{mk}{2},\, \operatorname{rlctAtOn}(\texttt{core})(\text{chart }0)\big\}, \qquad \operatorname{rlctAtOn}(\texttt{core})(0) = \tfrac{n}{2} + \operatorname{rlctAtOn}(\texttt{dlnLoss}(red M)\,0)\,0.
$$

Concretely, the datum (extending `RouteMNodeDescent`) carries:

1. **The blow-up chart `φ₁`** (NOT measure-preserving) with `dlnLoss M 0 ∘ φ₁ = y₀²·core` and
   `|Jac φ₁| = y₀^{mk−1}` (the V1 algebra; transcribable as a polynomial identity + a determinant).
2. **The OUTER product-min lemma** (NEW, the missing piece): for `g(y₀, z) = y₀²·K(z)` with weight
   `y₀^{mk−1}` (`K` not involving `y₀`), `rlctAtOn g (via weighted transport) = min{ (mk)/2,
   rlctAtOn K 0 }`. This is the weighted-cover Fubini fact — a clean general RLCT lemma
   (`weightedThreshold` of a separated product = min of the per-group thresholds), NOT in the current
   `GeneralR1Recursion`. It is the analog the `RouteMO1Bridge` caveat said was needed.
3. **The INNER core squeeze** (EXISTING, `schur_recursion_step_squeeze`): `core` squeezed by
   `Φ = ∑_{j=1}^n Erow_j² + G²`, `G² = dlnLoss(red M) 0`, giving `rlctAtOn core 0 = n/2 + rlctAtOn(G²)0`.
   **Use `nReg_struct = n` here** (the `Erow` count) — this is the SOUND count for `rlct(core)`, NOT
   for `rlct(F)`. The current `descentStep` is exactly this inner step; it is correct as-is once
   relabeled as computing `rlct(core)`, not `rlct(F)`.
4. **The `ReducedTransport`** (EXISTING): the det-1 MP `Erow`-shear reindex closing
   `rlctAtOn(G²)0 = rlctAtOn(dlnLoss(red M) 0) 0`.
5. **The arithmetic collapse** (PROVEN): `min{mk, n+R} = nReg + R` (`nReg = min{mk−R, n}` =
   `minAdm M − minAdm(red M)`), folding the cover's `min{mk/2, n/2+child}` into the spine's
   `nReg/2 + child`. The `minAdm_schurStateRed_add_nRegOf` identity is already in Lean; the
   `min{mk−R, n}` form is a small `omega`/`min` lemma on `minAdm`.

**The genuinely new Lean content is (2): the outer weighted product-min lemma.** Everything else exists
(the inner squeeze, the transport) or is proven (the arithmetic). The two-strata datum composes (2) ∘
(3) ∘ (4), then (5) reconciles to the spine `hstep`.

---

## 5. Sub-obstruction sweep (none found)

The controller flagged "if the two strata don't glue into a normal-crossing resolution, STOP". Checked:

- **Cross-term cap?** No — `v·Erow` is absorbed by comparability (`v` bounded near deepest), the unit
  pivot removes the rank-0 degeneracy, so `core ≍ ∑Erow² + ‖S·Bred‖²` and `rlct(core) = n/2 + R/2`
  with no internal min. (V7 consistency; Codex FACT.)
- **`y₀` not disjoint from `core`?** No — `core = ‖Â·B‖²` and `Â` has entries `1, u, v, W` (no `y₀`);
  the weight `y₀^{mk−1}` is in `y₀` alone. The Fubini factorization is exact. (V1; Codex FACT.)
- **Strata don't glue?** The single chart + recursive child IS the resolution (other pivot charts
  equivalent by permutation); no residual lower stratum. The only wording caveat (§3) is "recursive,
  not single-chart-complete" — a naming fix, not a math gap. (Codex.)
- **Regime split soundness?** The SAME `min{mk/2, n/2+R/2}` is the RLCT in BOTH regimes (V7, V9); no
  regime needs a different presentation. The `cert-104` obstruction was solely from dropping `D₀`.

**No sub-obstruction.** The two-strata cover is the sound uniform `hstep` for all non-leaf nodes.

---

## 6. Status

- **Proved/Verified (exact):** the outer product-min (Fubini), the inner core squeeze with no cap
  (unit pivot), `rlct(F) = min{mk/2, n/2+R/2} = ½·minAdm` (V7), the spine reconciliation
  `min{mk/2, n/2+child} = nReg/2 + child` (V8), both-regime anchors incl. the wide-tail `(2,2,4)` (V9)
  — `sympy/node_blowup_cert_104.py`, all pass; decorrelated xhigh Codex confirms sound, no flaw.
- **Resolves:** the `cert-104` obstruction — it was an artifact of reading only the core stratum
  (`nReg := n`) and dropping the `D₀` divisor; the two-strata `min` is sound and uniform.
- **New Lean content needed:** ONE general lemma — the **outer weighted product-min**
  (`weightedThreshold` of `y₀²·K(z)` with weight `y₀^{mk−1}` = `min{mk/2, rlctAtOn K}`). The inner
  squeeze, the `ReducedTransport`, and the arithmetic collapse already exist/are proven. Recommended:
  hand (2) to a formaliser as a standalone Core RLCT lemma; then assemble the per-node cover datum
  and re-wire `descentStep` to the true-loss level via the outer min.

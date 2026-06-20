# Statement card — Rung 0b: foundations + goal skeleton

The foundational definitions (`Params`, `prod`, `dlnLoss`, `optimalSet`, `rlctAt`, `rlctOrderAt`,
`aoyagiLambda`, `aoyagiTheta`), the single cited S2 `axiom`, and the named-`sorry` goal skeleton
(S1 / L1 / L2 / D1 / R1 / A1 / A2) culminating in the headline `aoyagi_learning_coefficient`.

- **Files:** `lean/DLNFibre/DLN/RLCT/Foundations/{Loss,Rlct,Lambda}.lean`,
  `lean/DLNFibre/DLN/RLCT/Skeleton.lean` (@ commit `<SHA-after-commit>`, branch `worktree-rung0-defs`).
- **Status.** sorry-free for all `def`s and the two proven lemmas (`optimalSet_eq_loss_zero`,
  `Adm_nonempty`/`zero_mem_Adm`); the 7 rung statements are named `sorry`s by design (statements-first);
  the single S2 `axiom` is the permitted citation. Awaiting fidelity review (Rung 0c).

## Definitions (the foundational, highest-care work)

> **`Params H`** — composable real matrix tuples: `∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ`.
>
> - **Gloss.** A network parameter is a tuple of layer matrices, layer `s` of size `H⁽ˢ⁾ × H⁽ˢ⁺¹⁾`.
> - **Measure substrate.** `Params H` is *definitionally* a `Pi` of function spaces, so it inherits
>   `TopologicalSpace` / `MeasurableSpace` / `MeasureSpace` (product Lebesgue `volume` on `ℝ^N`,
>   `N = Σ H⁽ˢ⁾H⁽ˢ⁺¹⁾`) by `inferInstanceAs` (`instMeasureSpaceParams`). No `EuclideanSpace` flatten needed.

> **`dlnLoss H B A = ∑ᵢⱼ ((prod H A − B)ᵢⱼ)²`** — the square-Frobenius loss `‖prod A − B‖²_F`.
> **`optimalSet H B = {A | prod A = B}`** — the fibre `mult⁻¹(B)`.
>
> - **Proved.** `optimalSet_eq_loss_zero : optimalSet H B = {A | dlnLoss H B A = 0}` (sum of squares).
> - **Gloss.** `prod` is the layer product `A⁽¹⁾·…·A⁽ᴸ⁾`, of size `H⁽¹⁾ × H⁽ᴸ⁺¹⁾ = H 0 × H (last)`.

> **`rlctAt H F w* : ℝ≥0∞`** — `sSup { c | ∃ c' ≥ 0, c = c' ∧ ∃ U ∈ 𝓝 w*, IntegrableOn |F|^(−c') U volume }`.
>
> - **Gloss.** Aoyagi Def 1, integral-supremum form (`|F|^{−c}`, `k=1` real); bump dropped via the
>   existential over neighbourhoods; value in `ℝ≥0∞` so the locally-nonvanishing case is `⊤`. The
>   threshold is generically not attained, so `sSup` (not a max) is faithful.
> - **Precondition (caveat).** Standard RLCT only for `F` real-analytic and `≢ 0` near `w*`; `dlnLoss`
>   is polynomial ⇒ holds. The equality to the bumped Def-1 value is an S1 lemma (not S0).

> **`rlctOrderAt H F w* : ℕ`** — the analytic pole order θ (opaque placeholder; no axiom).
>
> - **Cited / Seam.** Mathlib lacks the meromorphic continuation a direct analytic definition needs;
>   carried as `opaque` (total, axiom-free), its value pinned by the S2 citation. **Not** the naive
>   minimiser count of `M(T)` (design-spec §3). θ is the secondary, seam-flagged deliverable.

> **`aoyagiLambda H r : ℚ = [−r² + r(H⁽¹⁾+H⁽ᴸ⁺¹⁾)]/2 + lambdaCore (H · − r)`**, with
> **`lambdaCore M = ½·(Adm M).inf' _ (Mval M)`** the minimisation `½·min_{T∈Adm} M(T)`.
>
> - **Gloss.** `Mval` is Aoyagi's candidate value (design-spec §4.1, single-sum form with `t⁽⁰⁾ := M⁽¹⁾`);
>   `Adm` the finite admissible cone (weak-decrease, `t⁽ᴸ⁾=0`, block bounds). **Defined via the minimisation**
>   (total, Def-3-free — standing decision 3). `λ` is reserved in Lean, hence the name.
> - **Proved.** `Adm_nonempty` (all-zeros vector is admissible) ⇒ `inf'` total.
> - **Ground-truth (enforced at build via `#guard_msgs`/`#eval`).** `(2,2,2)→3/2`, `(2,1,2)→1`,
>   `(2,2,2,2)→3/2`, `(3,3,3,3)→3` — matches the design-spec §5 table.

> **`aoyagiTheta ℓ a : ℕ = a(ℓ−a)+1`** — Aoyagi's order θ, combinatorial form (total in `(ℓ,a)`).

## The one citation (S2)

> **`axiom monomial_rlct (d) (k h : Fin d → ℕ) : monomialThreshold d k h = ⨅ⱼ axisRatio (hⱼ) (kⱼ)`**
> **`∧ monomialOrderAnalytic d k h = monomialOrder d k h`**
>
> - **Cited.** The irreducible monomial-integral fact (Watanabe/Hironaka): the RLCT threshold of the
>   weighted monomial integral `∫ (∏uⱼ^{hⱼ})(∏uⱼ^{2kⱼ})^{−c}` is `minⱼ (hⱼ+1)/(2kⱼ)` (per axis
>   `∫₀^ε u^{h−2kc} < ∞ ⟺ c < (h+1)/(2k)`), and the analytic pole order is the binding-axis count.
> - **Where the line is drawn (Codex audit + standing decision 2).** The cover, change-of-variables,
>   properness, and bump-independence are **not** cited — they are S1/R1 obligations. The chart-level
>   formula `rlctAt F = ⨅ chart-thresholds` is a *derived theorem* (R1), not an axiom. `axisRatio` divides
>   in `ℝ≥0∞` (`kⱼ=0 ⇒ ⊤`, never binds). The order half equates an opaque `monomialOrderAnalytic` to the
>   combinatorial `monomialOrder` (the genuine analytic content of the citation).

## The named-`sorry` rungs (every statement; the contract)

| Rung | Lean name | Statement (gloss) | Form |
|---|---|---|---|
| S1 | `rlct_unit_invariant` | RLCT invariant under multiplying `F` by a unit `u` bounded in `[a,b]`, `a>0`, near `w*` | equality |
| S1 | `rlct_germ_local` | RLCT depends only on the germ: `F=G` on a nbhd ⇒ equal RLCT (φ-independence) | equality |
| L1 | `block_elimination` | rank-`r` `B` reduces to block-normal via invertible `P,Q` with `(P·B·Q).rank=r` | ∃ |
| L2 | `product_reduction` | local RLCT of loss at deepest point `= ofReal (aoyagiLambda H r)` | equality |
| D1 | `deepest_point_reduction` | `⨅_{optimalSet} rlctAt = rlctAt` at a deepest point `w*` | ∃ + equality |
| R1 | `resolution_charts` | `∃` chart-exponent data with `rlctAt F = ⨅ᵢ monomialThreshold` | ∃ |
| A1 | `lambdaCore_eq_clean` | `∃ ℓ m, lambdaCore M = cleanCore ℓ m` (the clean form `¼(Σqᵢ²−Σmₖ²)`) | ∃ |
| A1 | `clean_eq_printed` | `cleanCore ℓ m = printedCore ℓ m` (verified universal identity, 19600/19600) | equality |
| A2 | `aoyagiTheta_eq` | `∃ ℓ a d k h, monomialOrder d k h = aoyagiTheta ℓ a` (chart-count = a(ℓ−a)+1) | ∃ |

## Headline (the GOAL)

> **`aoyagi_learning_coefficient (H r B) (hB : B.rank = r) :`**
> **`(⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r)`**
>
> - **Gloss.** The global learning coefficient (infimum of the local RLCT over the fibre) equals Aoyagi's
>   closed form, for any rank-`r` target `B`. **Assembled** from `deepest_point_reduction` (D1) ▸
>   `product_reduction` (L2) — so the statement type-checks and the dependency is real.
> - **`#print axioms` (verbatim, rung 0b):** `[propext, sorryAx, Classical.choice, Quot.sound]`. The
>   `sorryAx` is the unproven D1/L2 route (expected at statements-first); `monomial_rlct` enters the trace
>   once L2's proof routes through R1+S2. The non-`sorry` standard axioms are Lean/Mathlib's.
> - **Cast caveat.** `ENNReal.ofReal` clamps negatives to 0; faithful because `aoyagiLambda ≥ 0` (a genuine
>   RLCT). To confirm in review.

## Build / audit

- `lake build DLNFibre` green; `scripts/sorries`: **9 sorry, 0 #exit, 0 native_decide, 1 axiom** — all
  the intended named rungs + the single S2 axiom, nothing stray.
- Two `opaque` placeholders (`rlctOrderAt`, `monomialOrderAnalytic`) introduce **no** axioms
  (`#print axioms` clean); they are the named analytic-order seam (design-spec §3 / §9).

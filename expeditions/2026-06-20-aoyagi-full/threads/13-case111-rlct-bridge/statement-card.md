# Statement card — `(1,1,1)` `rlctAt` bridge CLOSED (first axiom-free end-to-end RLCT)

The baby-S1.1 bridge `case111_rlct_eq_monomialThreshold` is now **proven sorry-free**, so the headline
`case111_rlct` (`rlctAt (1,1,1) (dlnLoss …) deepest111 = aoyagiLambda (1,1,1) 0 = 1/2`) is fully
**sorry-free AND axiom-free** — the first end-to-end `(1,1,1)` RLCT result resting on no `sorryAx`, no
`monomial_rlct` citation, no `native_decide`.

- **Files:** `lean/DLNFibre/DLN/RLCT/Validate/Case111.lean`,
  `lean/DLNFibre/DLN/RLCT/Validate/Case111Bridge.lean` (@ commit `b159ead`, branch
  `expedition/aoyagi-full`).
- **Status.** sorry-free. **Awaiting fidelity review.**

## The bridge (the result this thread closed)

> **`case111_rlct_eq_monomialThreshold :`**
> **`rlctAt (![1,1,1]) (dlnLoss (![1,1,1]) 0) deepest111 = monomialThreshold 2 (![1,1]) (![0,0])`**
>
> - **Gloss.** The local real-log-canonical threshold of the `(1,1,1)`, `B=0` deep-linear loss at the
>   deepest fibre point `deepest111 = fun _ ↦ 0` (the origin) equals the weighted-monomial-model
>   threshold for the resolution data `k=(1,1)`, `h=(0,0)`, `d=2`. Both sides are `1/2`.
> - **Proved.** The equality, unconditionally. `rlctAt` is `sSup` over the down-set of exponents
>   `c' ≥ 0` for which `|dlnLoss|^{−c'}` is integrable on *some* `Params`-neighbourhood of the origin;
>   `monomialThreshold` is `1/2` (`monomialThreshold_case111`). The proof characterises the
>   admissible-exponent set as the coerced `{c' : NNReal | c' < 1/2}` and computes its `sSup` as `1/2`.
> - **Mechanism (not a citation — proven here).** The loss `|dlnLoss A|^{−c'} = |c₁·c₂|^{−2c'}`
>   (`c₁ = A 0 0 0`, `c₂ = A 1 0 0`) depends only on the **product** of the two scalar entries. The
>   measure-preserving flattening `paramsEquivFlat` preserves the full coordinate product
>   (`prod_paramsEquivFlat`, re-index-invariant), so the integrand transports along the
>   measure-preserving **homeomorphism** `entryME : Params (1,1,1) ≃ᵐ ℝ²` (`paramsEquivFlat ≫
>   finTwoArrow`) to `|x·y|^{−2c'}` on `ℝ²`. Forward (`c' < 1/2`): the open box `entryME⁻¹((-1,1)²)`
>   is integrable by the two-sided box iff `prodBoxSymm_rpow_integrableOn_iff`. Reverse (`c' ≥ 1/2`):
>   any neighbourhood of `0` pushes forward to a `𝓝 (0,0)`, contains a box `[-ε,ε]²`, on which the
>   integral diverges (same iff). `sSup {<1/2} = 1/2`.
> - **Cited.** **none.** The threshold-half `monomialThreshold_case111` is itself axiom-free
>   (Fubini + Mathlib's `intervalIntegral.integrableOn_Ioo_rpow_iff`, `Case111Bridge`); `monomial_rlct`
>   is **not** used.
> - **Deferred.** none (sorry-free).
> - **`#print axioms case111_rlct_eq_monomialThreshold` (verbatim):**
>   `[propext, Classical.choice, Quot.sound]`.

## The headline (now axiom-free)

> **`case111_rlct :`**
> **`rlctAt (![1,1,1]) (dlnLoss (![1,1,1]) 0) deepest111 = ENNReal.ofReal (aoyagiLambda (![1,1,1]) 0)`**
>
> - **Gloss.** The local RLCT of the loss at the deepest fibre point equals Aoyagi's closed form,
>   both `= 1/2`.
> - **Proved.** `case111_rlct_eq_monomialThreshold ▸ case111_monomialThreshold` (both axiom-free).
> - **Cited / Deferred.** none.
> - **`#print axioms case111_rlct` (verbatim):** `[propext, Classical.choice, Quot.sound]` — no
>   `sorryAx`, no `monomial_rlct`. **The headline of this thread.**

## Reusable S1.1 infra (sorry-free, in `Case111Bridge.lean` unless noted)

> **`continuous_paramsEquivFlat` / `continuous_paramsEquivFlat_symm`** — the flattening `Params H ≃ᵐ
> (Fin N → ℝ)` is a **homeomorphism** (two `Sigma.curry`/`uncurry` steps + an evaluation re-index, each
> continuous). General in `H` — used to make `entryME⁻¹(box)` a `Params` neighbourhood and to push a
> `Params` neighbourhood forward.
>
> **`prod_paramsEquivFlat (H) (A) : ∏ i, paramsEquivFlat H A i = ∏ q : FlatIdx H, A q.1.1 q.1.2 q.2`**
> — the flattening preserves the full product of coordinates (the re-index is a bijection;
> `Equiv.prod_comp`). General in `H`; **re-index-invariant** (the opaque `Fintype.equivFin` is never
> computed). The crux that dissolved the parked obstruction.
>
> **`prodBoxSymm_rpow_integrableOn_iff (c ε) (0<ε) : IntegrableOn (|p.1·p.2|^{−2c}) ([-ε,ε]²) ⟺
> c < 1/2`** — the two-sided 2-D box integrability iff (the `𝓝 0`-shaped analogue of the one-sided
> `prodBox_rpow_integrableOn_iff`). Reusable for any neighbourhood-of-`0` weighted-monomial RLCT.
>
> **`prod_entries_case111` (`Case111.lean`)** — `∏ q : FlatIdx (1,1,1), A q.1.1 q.1.2 q.2 =
> A 0 0 0 · A 1 0 0` (two `Fintype.prod_sigma`, then the `Fin 1`-width per-layer products collapse).
> The `(1,1,1)`-specific instance of the product fact.

## Build / audit

- `lake build DLNFibre.DLN.RLCT.Validate.Case111` (module-scoped) green. `Case111.lean` and
  `Case111Bridge.lean`: **zero** `sorry` / `axiom` / `native_decide` (the only `sorry` matches under
  `grep` are in docstrings; `scripts/sorries` attributes all 9 remaining sorries to `Skeleton.lean`,
  owned by a parallel agent — Skeleton was not touched).
- Module-scoped build per controller instruction (a parallel agent has Skeleton WIP that would fail a
  whole-library build on their account); no `DLNFibre.lean` aggregator change needed (Case111 already
  wired).
- One added import: `Case111Bridge.lean` now imports `DLNFibre.DLN.RLCT.Foundations.ParamsFlat`
  (for `paramsEquivFlat` + `FlatIdx`); no cycle (`ParamsFlat` imports only `Rlct`).

# Thread 10 — Barcode-basis / interval normal form (rung 4d, THE CRUX) — formalisation

**Type:** formalisation (tide). **Module:** `lean/DLNFibre/Core/Barcode.lean` (new, network-free,
namespace `DLNFibre.Core`). **Branch:** `barcode/rung-4d` (worktree; not pushed). **Build:** green,
`0 sorry / 0 axiom / 0 native_decide`; gate theorems depend only on `[propext, Classical.choice,
Quot.sound]`. **Pinned at** `1d5a36c`.

## TL;DR (what landed)

The **load-bearing splitting fact** (the crux's heart) landed cleanly — in both an **ambient** and a
**relative** (recursion-ready) form — plus the *entire local content* of the barcode peel. A key
simplification over the design: with the abstract composite map's composition law, the design's
"single hardest formal step" (the indexed *downward* preimage construction `U_{t-1} = f_t⁻¹(U_t)`
threaded down the chain) collapses to a **pointwise** application of the splitting fact at each
interior vertex, with **no downward recursion**.

What is **not** yet done: the *global* assembly — index-finding (least-nonzero `s`, last-nonzero
`j`), the global subrepresentation + total-dimension strict-drop packaging, the strong-induction
recursion, the `Λ`-indexed-barcode / iso-to-`⊕ M_{ij}` output, and the transport to `Setup.Tuple`.
The geometric content of the inductive step is done; what remains is bookkeeping (see §"Remaining").

## 1. The splitting fact (`isCompl_span_singleton_comap`) — landed

> For `f : V →ₗ[k] W` (`k` a field), `v : V` with `f v ≠ 0`, and `IsCompl (k ∙ f v) U` (i.e.
> `W = k·(f v) ⊕ U`): `IsCompl (k ∙ v) (U.comap f)` (i.e. `V = k·v ⊕ f⁻¹(U)`).

Proof exactly per design §2.2 step 4:
- **Disjoint** (`Submodule.disjoint_def`): `x ∈ k·v ⟹ x = c·v`; `x ∈ f⁻¹U ⟹ c·(f v) ∈ U`; with
  `c·(f v) ∈ k·(f v)` and `Disjoint (k·f v) U`, get `c·(f v) = 0`, so `c = 0` (`smul_eq_zero` +
  `f v ≠ 0`, the one place the **field**/`NoZeroSMulDivisors` is used), hence `x = 0`.
- **Codisjoint** (`codisjoint_iff` + `Submodule.mem_sup`): for `x`, write `f x = a·(f v) + u`
  (`u ∈ U`); then `x = a·v + (x − a·v)` with `f(x − a·v) = u ∈ U`, so `x − a·v ∈ f⁻¹U`.

Companions landed on top of it:
- **`exists_isCompl_comap`** — over a field complements always exist, so the splitting fact applies
  to *every* `f, v` with `f v ≠ 0`: `∃ U, IsCompl (k·f v) U ∧ IsCompl (k·v) (f⁻¹U)`. This is the
  form the peel consumes (and the splitting fact's non-vacuity: the antecedent is always met).
- **`finrank_comap_add_one`** — the quantitative companion: `finrank (f⁻¹U) + 1 = finrank V`. The
  engine of termination (each peeled line drops the running dimension by one). Uses
  `Submodule.finrank_add_eq_of_isCompl` + `finrank_span_singleton`.
- **`relSplitting`** — the splitting fact **relative to an ambient pair `(P, Q)`**: if `f` restricts
  `P → Q` (`P.map f ≤ Q`), `v ∈ P` with `f v ≠ 0`, and `Q = k·(f v) ⊕ U` *inside `Q`*, then
  `P = k·v ⊕ (f⁻¹(U) ⊓ P)` *inside `P`*. The **recursion-ready** form (route a below): it peels a
  line off a *subrepresentation* `P_t`, not just the ambient space, keeping all types fixed. `P = Q
  = ⊤` recovers the ambient form (witnessed in-file). Same proof as the ambient case, intersecting
  with `P` in the codisjoint half.

In-file witnesses ground all of these on `ℚ` (identity at `1`).

## 2. The abstract-chain encoding (per design §1.1) — landed

A chain is a family `V : Fin (N+1) → Type v` of `k`-vector spaces (instances as genuine `variable`s,
so `f t : V t.castSucc →ₗ[k] V t.succ` typechecks with real instances — no structure-bundling) with
edge maps `f`.

- **`compMap f i j : V i →ₗ[k] V j`** (for `i ≤ j`) — the ordered composite `f_{j-1} ∘ ⋯ ∘ f_i`, the
  *cast-free* abstract analogue of `Setup.submult`. Defined by `Nat.leRec` on the **upper** index
  with a function-valued motive carrying the `< N+1` bound, holding `i` fixed — the exact pattern
  thread-06 used for `submult` to dodge the variable-lower-bound dependent cast. `compMap_self`
  (`= id`) and `compMap_succ` (`= f_p ∘ compMap …`) close by `Nat.leRec_self` / `Nat.leRec_succ`,
  transferring verbatim from `submult`'s proofs.
- **`compMap_trans`** — composition law: `compMap i j = compMap m j ∘ compMap i m` for `i ≤ m ≤ j`
  (induction on the upper index `j` via `compMap_succ`). *This is the lever that collapses the
  recursion* (see §3). The chain analogue of associativity of the ordered product.
- **`compMap_edge`** — `compMap e.castSucc e.succ = f e` (single-edge composite).

## 3. The peel — local content (pointwise) — landed

The **key simplification.** The design (§2.2 step 3+4) builds the complement chain by *downward
recursion* `U_{t-1} = f_t⁻¹(U_t)` and threads the `IsCompl` splitting down the chain — its named
"single hardest formal step." With `compMap` + `compMap_trans` this is unnecessary: define
`U_t := (compMap f t j)⁻¹(U_j)` **non-recursively**, and since `compMap f t j` sends `v_t ↦ v_j`
(by `compMap_trans`, as `v_t = compMap f s t v_s`), the splitting fact applies **directly at each
vertex** with `g := compMap f t j`. No threading, no per-step `IsCompl` induction.

- **`isCompl_interval_complement`** — for a trajectory `v_t = compMap f s t v_s` surviving to `j`
  (`compMap f s j v_s ≠ 0`) and a top complement `IsCompl (k·v_j) U_j`, the pullback
  `U_t := (compMap f t j)⁻¹(U_j)` satisfies `IsCompl (k·v_t) U_t` for **every** `t ∈ [s,j]`. One-line
  application of the splitting fact after `compMap_trans` rewrites `compMap t j (v_t) = v_j`.
- **`finrank_interval_complement`** — `finrank U_t + 1 = finrank V_t` at every interior vertex
  (the per-vertex termination engine; summed over `[s,j]` the bar removes `j − s + 1`).
- **`comap_compMap_edge`** — `U_{e.castSucc} = (f e)⁻¹(U_{e.succ})` for an interior edge
  (`e.succ ≤ j`): the complement chain is **forward-closed** (a subrepresentation along the bar).
  From `compMap_trans` + `compMap_edge` + `Submodule.comap_comp`.

Concrete 2-vertex identity-chain witness (`witnessV`/`witnessF`, `ℚ --id--> ℚ`) shows the trajectory
survives and `isCompl_interval_complement` fires — the peel antecedents are satisfiable.

## 4. Levers used (corrections to `mathlib-levers.md`)

All as listed in `mathlib-levers.md` **except**:
- **`Submodule.finrank_add_eq_of_isCompl`** (`LinearAlgebra/FiniteDimensional/Lemmas`,
  `[FiniteDimensional K V] (h : IsCompl U W) : finrank U + finrank W = finrank V`) — the levers doc
  marked "IsCompl finrank add" as **ABSENT (compose)**. It **EXISTS** at this pin (v4.29.0); no need
  to compose `quotientEquivOfIsCompl` + `finrank_quotient_add_finrank`. Used directly.
- `finrank_span_singleton (hv : v ≠ 0) : finrank K (K ∙ v) = 1` — used.
- `Submodule.comap_comp f g p : comap (g.comp f) p = comap f (comap g p)` — used (forward-closed).
- `Submodule.disjoint_def`, `Submodule.mem_span_singleton`(`_self`), `codisjoint_iff`,
  `Submodule.mem_sup`(`_left`/`_right`), `Submodule.exists_isCompl`, `smul_eq_zero` — used.
- `Nat.leRec` / `Nat.leRec_self` / `Nat.leRec_succ` — used (compMap, mirroring `submult`).

## 5. What remains + the obstacle (precise)

The geometric content of the inductive step is **done**; the rest is assembly. Remaining, in order:

1. **Index-finding** (`∃ s, j`). `s` = least vertex with `V_s ≠ 0` (`Nontrivial`/`⊤ ≠ ⊥`); `j` =
   last vertex with the trajectory `compMap f s t v_s ≠ 0`. Obstacle: `Fin` min/max over a filtered
   `Finset`, where the trajectory predicate `compMap f s t _ v_s ≠ 0` is **dependent** (`V t`-valued,
   and `compMap` needs the proof `s ≤ t` inside the filter) — the `Fin`/decidability/dependent-filter
   bookkeeping the design flagged. Tractable, not yet attempted.
2. **Global subrep + total-dimension strict drop.** Package `U_t := if s ≤ t ≤ j then
   (compMap f t j)⁻¹(U_j) else ⊤` into one family; prove it is a subrepresentation (3 edge cases:
   below `s` — uses `s`-minimality so `V_{e.castSucc}` is trivial; interior — `comap_compMap_edge`;
   above `j` — `U = ⊤` trivial) and `∑ finrank U_t < ∑ finrank V_t` (the per-vertex
   `finrank_interval_complement` drops summed over `[s,j]`; the off-interval `U_t = ⊤` contribute
   `finrank V_t`). Obstacle: the dependent-`if` (`dif`) unfolding + the `Finset.sum` split over the
   `[s,j]` subset of `Fin (N+1)`. Fiddly arithmetic, not yet attempted.
3. **The strong-induction recursion.** Induct on total dimension. The peel produces `U_*` as
   submodules of the **ambient** `V_t`; recursing means peeling **within** `U_*` — a
   sub-sub-representation. Route (a) (recommended): `Nat`-strong induction on `∑ finrank P_t` over
   subreps `P_* ≤ V_*`, with all types fixed as `Submodule k (V t)`. The relative splitting fact
   **`relSplitting`** (now landed, §1) is the per-vertex lever for this route — it splits a line off
   `P_t` directly. (Route (b), a `Chain` structure with the submodule types as the spaces, changes
   types each peel and needs `Submodule.subtype` transport — dispreferred.) Obstacle remaining for
   route (a): wiring the pointwise `relSplitting` along the bar (a relative analogue of
   `isCompl_interval_complement` — apply `relSplitting` to `g = compMap t j` restricted to `P`),
   then the `Nat.strong_induction` itself (generalising over the subrep). Not yet attempted.
4. **The barcode output / completeness.** Either the `Λ`-indexed basis or "chain `≅ ⊕ M_{s,j}`"
   (needs the abstract interval module as a chain + chain-iso). With existence, *uniqueness is free*
   via the already-landed `RankPattern.diff_cumul` (design §3).
5. **Transport to `Setup.Tuple`** (design §1.1): one change-of-basis lemma per vertex
   (`Matrix.toLin'`/`mulVecLin`). Localises all `Fin`/`Matrix` casts.

**Discarded routes** (design §2.4) were **not** re-tried: one-pass column reduction (fails),
Smith/staircase, full kernel/image filtration.

## 6. Recommended next step

A focused follow-up tide for the **global peel** (§5.1–2) + the **strong induction** (§5.3) — these
chain together. The reusable inputs all exist: the pointwise lemmas (§3), the ambient *and*
**relative** splitting facts, `finrank_comap_add_one`, and the `compMap` layer. What is left is
genuinely assembly — index-finding, the `Finset` sum drop, wiring `relSplitting` along the bar, the
`Nat.strong_induction`, the barcode output, the `Tuple` transport. Estimate: a substantial
module-sized effort, best done with fresh context; the crux mathematics is no longer the bottleneck.

---

## Draft statement cards

> **Claim (the splitting fact, crux heart).** For `f : V →ₗ[k] W` over a field `k`, a vector `v`
> with `f v ≠ 0`, and a complement decomposition `W = k·(f v) ⊕ U`, the preimage `f⁻¹(U)` is a
> complement of the source line `k·v`: `V = k·v ⊕ f⁻¹(U)`.
>
> - **Lean:** `DLNFibre.Core.isCompl_span_singleton_comap`
>   (`lean/DLNFibre/Core/Barcode.lean` @ `1d5a36c`)
> - **Gloss.** `IsCompl (k ∙ f v) U → IsCompl (k ∙ v) (U.comap f)`, given `f v ≠ 0`. Pulling back a
>   complement of the image line along `f` gives a complement of the source line.
> - **Proved.** Unconditionally (field `k`). The one geometric fact behind the barcode peel.
> - **Assumed.** `f v ≠ 0` (necessary — false for `f v = 0`); `IsCompl (k ∙ f v) U` (over a field
>   always satisfiable, witnessed by `exists_isCompl_comap`).
> - **Cited.** none (only Mathlib `Submodule`/`finrank` API).
> - **Deferred.** none for *this* statement. (The full barcode existence — peeling this down a chain
>   by total-dimension induction — is rung 4d's remaining work; see §5.)
> - **Status.** sorry-free.

> **Claim (relative splitting fact, recursion-ready).** If `f` restricts `P → Q` (`P.map f ≤ Q`),
> `v ∈ P` with `f v ≠ 0`, and `Q = k·(f v) ⊕ U` inside `Q`, then `P = k·v ⊕ (f⁻¹(U) ⊓ P)` inside
> `P`.
>
> - **Lean:** `DLNFibre.Core.relSplitting` (`lean/DLNFibre/Core/Barcode.lean` @ `943c13d`)
> - **Gloss.** `Disjoint (k∙v) (U.comap f ⊓ P) ∧ k∙v ⊔ (U.comap f ⊓ P) = P`, given `P.map f ≤ Q`,
>   `v ∈ P`, `f v ≠ 0`, `Disjoint (k∙f v) U`, `k∙(f v) ⊔ U = Q`. Splits a line off a
>   *subrepresentation*, types fixed — the lever for the recursion (route a).
> - **Proved.** Unconditionally (field). **Assumed.** the named hypotheses. **Cited.** none.
>   **Deferred.** none (`P=Q=⊤` recovers the ambient form, witnessed in-file). **Status.** sorry-free.

> **Claim (dimension drop).** Peeling the line `k·v` off `V` via the preimage complement drops
> `finrank` by exactly one.
>
> - **Lean:** `DLNFibre.Core.finrank_comap_add_one`
>   (`lean/DLNFibre/Core/Barcode.lean` @ `1d5a36c`)
> - **Gloss.** `[FiniteDimensional k V] → IsCompl (k ∙ f v) U → finrank (U.comap f) + 1 = finrank V`
>   (given `f v ≠ 0`).
> - **Proved.** Unconditionally. **Assumed.** finite-dimensional `V`; `f v ≠ 0`; the `IsCompl`.
>   **Cited.** none. **Deferred.** none. **Status.** sorry-free.

> **Claim (peel, local content — pointwise).** Along a trajectory `v_t = compMap f s t v_s`
> surviving to `j`, with a top complement `IsCompl (k·v_j) U_j`, the pullback
> `U_t := (compMap f t j)⁻¹(U_j)` is a complement of `k·v_t` at every `t ∈ [s,j]`, drops `finrank`
> by one there, and is forward-closed across interior edges.
>
> - **Lean:** `DLNFibre.Core.isCompl_interval_complement`, `…finrank_interval_complement`,
>   `…comap_compMap_edge` (with `compMap`, `compMap_trans`, `compMap_edge`)
>   (`lean/DLNFibre/Core/Barcode.lean` @ `1d5a36c`)
> - **Gloss.** The geometric content of the inductive step, *pointwise* (no downward recursion —
>   `compMap_trans` collapses it). See §3.
> - **Proved.** The local (per-vertex / per-edge) content, unconditionally. **Assumed.** the
>   trajectory-survival `compMap f s j v_s ≠ 0` and the top `IsCompl` (both witnessed on the identity
>   chain). **Cited.** none. **Deferred.** the *global* assembly — index-finding, the subrep +
>   total-dimension strict drop, the strong-induction recursion, the `Λ`-barcode/iso output, the
>   `Tuple` transport (§5). The name reflects this: it is *interval-complement* content, **not** the
>   full Gabriel decomposition. **Status.** sorry-free.

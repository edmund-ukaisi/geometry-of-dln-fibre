# Thread 10 — Barcode-basis / interval normal form (rung 4d, THE CRUX) — formalisation

**Type:** formalisation (tide). **Module:** `lean/DLNFibre/Core/Barcode.lean` (new, network-free,
namespace `DLNFibre.Core`, 722 lines). **Branch:** `barcode/rung-4d` (pushed to `origin`). **Build:**
green, `0 sorry / 0 axiom / 0 native_decide`; the headline `hasBarcode_of_isSubrep` depends only on
`[propext, Classical.choice, Quot.sound]`. **Pinned at** `ea5a334`.

## TL;DR (what landed) — THE FULL ABSTRACT-CHAIN EXISTENCE THEOREM

Rung 4d is **complete on abstract chains**. The headline `hasBarcode_of_isSubrep`: every
finite-dimensional subrepresentation of an abstract chain `V₀ --f₁--> ⋯ --f_N--> V_N` has a
**barcode** — a finite family of interval bars whose lines, at every vertex `t`, form an internal
direct sum (`iSupIndep` + `⨆ = P_t`) of interval-module lines, each bar a genuine interval module
(support + trajectory `f e (line) = line` inside + death `f e (line) = 0` past `death`). This is the
**existence** half of type-A Gabriel (Le Halleur–Rimányi 2024, Thm 2.5): every finite chain of f.d.
`k`-vector spaces is isomorphic to a direct sum of interval modules. Whole-chain form
`hasBarcode_top` (`P = ⊤`) + concrete identity-chain witness.

The proof, bottom-up: the **splitting fact** (crux heart, ambient + relative) → the abstract
**`compMap`** layer (composition law `compMap_trans`) → the **pointwise peel** (the splitting applied
vertex-wise via `compMap_trans` — collapsing the design's downward recursion) → the **peel**
`exists_peel` (one inductive step: bar + complementary subrep of strictly smaller total dimension) →
two **`Fin.cons` lattice combine** helpers → the **total-dimension strong induction**
(`Nat.strongRecOn`).

**Remaining (separate, sanctioned out-of-scope for this tide):** the transport to `Setup.Tuple`
(change-of-basis cast bookkeeping) and uniqueness of multiplicities (near-free downstream via
`RankPattern.diff_cumul` + 4b/4c). Neither is part of the existence headline.

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

## 4b. The induction (all LANDED)

- **`IsSubrep` / `compMap_mem` / `totalDim`** — the induction substrate (subreps `P_* ≤ V_*`,
  forward-closed; `compMap` preserves a subrep; the measure `∑ finrank P_t`).
- **`exists_least_nonzero` / `exists_last_nonzero`** — index-finding (`Finset.min'`/`max'`), the bar
  endpoints `s` (least nonzero vertex) and `j` (last vertex where the trajectory is nonzero).
- **`exists_peel`** — one inductive step: from a subrep with some `P_t ≠ ⊥`, peel a bar `(s,j,v)`
  and a complementary subrep `P'` with `P_t = k·v_t ⊕ P'_t` on `[s,j]`, `P'_t = P_t` off it,
  `totalDim P' < totalDim P`, plus the bar's trajectory + death. Splitting via `relSplitting`
  vertex-wise (`compMap_trans`); subrep of `P'` via `comap_compMap_edge` (interior edges) +
  `s`-minimality (bottom edge); strict drop via `finrank_sup_add_finrank_inf_eq` at `s` →
  `Finset.sum_lt_sum`.
- **`iSup_fin_cons` / `iSupIndep_fin_cons`** — the `Fin.cons` combine for the supremum and for
  `iSupIndep` (the latter proved *element-wise* for submodules: `Disjoint.sup_right` needs a
  *distributive* lattice but the submodule lattice is only *modular*). Neither in Mathlib at this pin.
- **`HasBarcode` / `hasBarcode_of_isSubrep` / `hasBarcode_top`** — the headline (total-dimension
  `Nat.strongRecOn`): consing the peeled bar onto the IH's barcode, each conjunct combining by
  `Fin.eq_zero_or_eq_succ` case-split (new bar from the peel, old from the IH; spanning via
  `iSup_fin_cons`, independence via `iSupIndep_fin_cons`).

## 5. What remains (separate; out of scope for this tide, by the controller's steer)

1. **Transport to `Setup.Tuple`** (design §1.1): a change-of-basis lemma per vertex
   (`Matrix.toLin'`/`mulVecLin`) turning the abstract barcode into a `G_d` base change `g · A =
   ⊕ M_{ij}^{m}`. Mostly `Fin`/`Matrix` cast bookkeeping; localised, no new mathematics.
2. **Uniqueness of the multiplicities** — near-free downstream from existence via the already-landed
   `RankPattern.diff_cumul` + 4b `rankPattern_intervalDirectSum_eq_cumul` + 4c rank-pattern
   invariance. Not part of the existence headline.

**Discarded routes** (design §2.4) were **not** re-tried: one-pass column reduction (fails),
Smith/staircase, full kernel/image filtration.

## 6. Note for the follow-up

The abstract existence is closed and sorry-free; the `Tuple` transport (§5.1) is the natural next
tide. The reusable assets for it: the `HasBarcode` predicate, `intervalModule`/`dirSum`/
`intervalDirectSum` (4b), and `submult`/`rankPattern` (4a/06). The crux mathematics is no longer the
bottleneck — what remains is matrix/`Fin` cast bookkeeping to read the abstract barcode off in
coordinates.

---

## Draft statement cards

> **Claim (THE headline — barcode-basis existence, rung 4d).** Every finite-dimensional
> subrepresentation `P` of an abstract chain `V₀ --f₁--> ⋯ --f_N--> V_N` of `k`-vector spaces (`k` a
> field) has a barcode: a finite family of interval bars (each an interval module — supported on
> `[birth,death]`, nonzero there, `f` acting as a trajectory inside and dying past `death`) whose
> lines form an internal direct sum equal to `P_t` at every vertex `t`. Equivalently, every finite
> chain of f.d. `k`-vector spaces is isomorphic to a direct sum of interval modules.
>
> - **Lean:** `DLNFibre.Core.hasBarcode_of_isSubrep` (and the `P = ⊤` form
>   `DLNFibre.Core.hasBarcode_top`), predicate `DLNFibre.Core.HasBarcode`
>   (`lean/DLNFibre/Core/Barcode.lean` @ `ea5a334`)
> - **Gloss.** `IsSubrep V f P → HasBarcode V f P`, where `HasBarcode P` packages: a finite
>   `birth death : Fin M → Fin (N+1)`, `line : Fin M → ∀ t, V t`, with `birth ≤ death`, support
>   (`line λ t = 0` off `[birth λ, death λ]`), nonzero-alive, trajectory
>   (`f e (line λ e.castSucc) = line λ e.succ` for `e` inside the bar), death
>   (`f e (line λ e.castSucc) = 0` once `death λ < e.succ`), and at each `t` the lines
>   `iSupIndep (fun λ => k ∙ line λ t)` with `⨆ λ, k ∙ line λ t = P t`.
> - **Proved.** Unconditionally (field `k`, f.d. spaces), by total-dimension strong induction. The
>   **existence** half of type-A Gabriel (Thm 2.5). Non-vacuity: the identity chain `ℚ → ℚ` (in-file).
> - **Assumed.** `P` a subrepresentation (the headline `hasBarcode_top` takes `P = ⊤`); finite
>   dimensionality of each `V t`.
> - **Cited.** none beyond Mathlib `Submodule`/`finrank` API.
> - **Deferred.** the transport to `Setup.Tuple` (a `G_d` base change `g · A = ⊕ M^m` — separate
>   change-of-basis lemma); uniqueness of the multiplicities (near-free downstream via
>   `RankPattern.diff_cumul`). Neither is claimed by the name (which says *existence*, not the full
>   Gabriel bijection).
> - **Form note (rung-4 audit, thread 12).** The deliverable is the internal-direct-sum *predicate*
>   `HasBarcode` (chosen ambient barcode-basis lines, f-stable + `iSupIndep` + `⨆=P_t`), which is
>   *logically equivalent* to — but not yet constructed as — an explicit Lean iso object
>   `P ≅ ⊕ M_{birth,death}`. The abstract iso is a near-free corollary; a downstream consumer (the
>   Tuple transport) that wants the iso as an object must construct it. Honest + correctly named
>   (docstring: "Equivalently … isomorphic to a direct sum of interval modules").
> - **Status.** sorry-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`); **reviewer-audited
>   (thread 12): SURVIVED — faithful, non-vacuous (adversarial in-Lean probe), no overclaim.**

> **Claim (the splitting fact, crux heart).** For `f : V →ₗ[k] W` over a field `k`, a vector `v`
> with `f v ≠ 0`, and a complement decomposition `W = k·(f v) ⊕ U`, the preimage `f⁻¹(U)` is a
> complement of the source line `k·v`: `V = k·v ⊕ f⁻¹(U)`.
>
> - **Lean:** `DLNFibre.Core.isCompl_span_singleton_comap`
>   (`lean/DLNFibre/Core/Barcode.lean` @ `ea5a334`)
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
> - **Lean:** `DLNFibre.Core.relSplitting` (`lean/DLNFibre/Core/Barcode.lean` @ `ea5a334`)
> - **Gloss.** `Disjoint (k∙v) (U.comap f ⊓ P) ∧ k∙v ⊔ (U.comap f ⊓ P) = P`, given `P.map f ≤ Q`,
>   `v ∈ P`, `f v ≠ 0`, `Disjoint (k∙f v) U`, `k∙(f v) ⊔ U = Q`. Splits a line off a
>   *subrepresentation*, types fixed — the lever for the recursion (route a).
> - **Proved.** Unconditionally (field). **Assumed.** the named hypotheses. **Cited.** none.
>   **Deferred.** none (`P=Q=⊤` recovers the ambient form, witnessed in-file). **Status.** sorry-free.

> **Claim (dimension drop).** Peeling the line `k·v` off `V` via the preimage complement drops
> `finrank` by exactly one.
>
> - **Lean:** `DLNFibre.Core.finrank_comap_add_one`
>   (`lean/DLNFibre/Core/Barcode.lean` @ `ea5a334`)
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
>   (`lean/DLNFibre/Core/Barcode.lean` @ `ea5a334`)
> - **Gloss.** The geometric content of the inductive step, *pointwise* (no downward recursion —
>   `compMap_trans` collapses it). See §3.
> - **Proved.** The local (per-vertex / per-edge) content, unconditionally. **Assumed.** the
>   trajectory-survival `compMap f s j v_s ≠ 0` and the top `IsCompl` (both witnessed on the identity
>   chain). **Cited.** none. **Deferred.** the *global* assembly — index-finding, the subrep +
>   total-dimension strict drop, the strong-induction recursion, the `Λ`-barcode/iso output, the
>   `Tuple` transport (§5). The name reflects this: it is *interval-complement* content, **not** the
>   full Gabriel decomposition. **Status.** sorry-free.

# Statement card — θ-invariants distinction (component count ≠ pole order)

Source claim: `docs/expositions/theta-invariants-distinction.md` (the "three invariants called θ"
exposition; the component count `θ = C(m,|δ|)` is L&R's, the pole order `a(ℓ−a)+1` is Aoyagi's,
and they separate at `(2,2,2,2,2)`, `r=0`).

Module: `lean/DLNFibre/DLN/Aoyagi/ThetaOrderDistinction.lean`.

---

## Capstone 1 — the concrete (live) mismatch

> **Claim.** For the five-layer constant-width-2 network `(2,2,2,2,2)` at true rank `r = 0`
> (so `m = 4`, `|δ| = 2`), the geometric component count of the fibre (`= C(4,2) = 6`) is **not
> equal** to Aoyagi's analytic pole order `a(ℓ−a)+1 = 2·2+1 = 5`.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.numTop_d22222_ne_aoyagiPoleOrder`
>   (`lean/DLNFibre/DLN/Aoyagi/ThetaOrderDistinction.lean` @ `4af0423dfc3f5cff2e384ba34d30ffff91a73e67`)
>   - signature: `numTop d22222 0 kostantPartitions_d22222_nonempty ≠ aoyagiPoleOrder 4 2`,
>     `d22222 : Fin 5 → ℕ := ![2,2,2,2,2]`, `aoyagiPoleOrder ell a := a*(ell-a)+1`.
> - **Gloss.** The *live* Kostant-side component count `numTop` of the dimension vector
>   `![2,2,2,2,2]` at corner `0` is `6` (proved via `numTop_d22222_zero`, routing through
>   `Core.numTop_zero_eq_cTheta` and `cTheta_d22222 : cTheta d22222 = 6` by `decide +kernel`), and
>   `6 ≠ 5 = aoyagiPoleOrder 4 2`. So the geometric component count of *this actual fibre* is not the
>   Aoyagi pole order. Abstract core also recorded: `choose_four_two_ne_aoyagiPoleOrder : choose 4 2 ≠
>   aoyagiPoleOrder 4 2` (axiom-free, `decide`).
> - **Proved.** `numTop ![2,2,2,2,2] 0 = 6 ≠ 5 = aoyagiPoleOrder 4 2`, with `6` tied to the live
>   `Core.numTop` / `Core.cTheta` (not just the abstract binomial).
> - **Assumed.** `kostantPartitions d22222 0` nonempty (`kostantPartitions_d22222_nonempty`, via the
>   QIP witness `![2,0,0,0]`); `d22222` monotone (`decide`). Both discharged in-file.
> - **Cited.** Aoyagi (2023) Thm 2 / equal-width Example for the *meaning* of `a(ℓ−a)+1` as the pole
>   order (the rlcm itself is not formalised here — only its closed-form value as a function of
>   `(ℓ,a)`). The component-count side is fully internal (`Core.numTop`/`cTheta`).
> - **Deferred.** Tying the `5` to a *live* `ClosedForm.ell`/`ClosedForm.residueA` evaluation
>   (those are `noncomputable` via `Tuple.sort` + `ediv`, so they do not `decide`-reduce; the
>   correspondence `(ℓ,a) = (4,2)` for this witness is documented, not Lean-evaluated). The rlcm as
>   an analytic pole order is not constructed.
> - **Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]` (no `sorryAx`,
>   no `native_decide`).

## Capstone 2 — the agreement regime

> **Claim.** For `a ≤ ℓ`, the geometric component count `C(ℓ,a)` equals the analytic pole order
> `a(ℓ−a)+1` **iff** `min a (ℓ−a) ≤ 1` — i.e. exactly on the four edge cases `a ∈ {0,1,ℓ−1,ℓ}`;
> outside them the binomial is strictly larger.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.choose_eq_aoyagiPoleOrder_iff`
>   (`lean/DLNFibre/DLN/Aoyagi/ThetaOrderDistinction.lean` @ `4af0423dfc3f5cff2e384ba34d30ffff91a73e67`)
>   - signature: `(haell : a ≤ ell) : Nat.choose ell a = aoyagiPoleOrder ell a ↔ min a (ell - a) ≤ 1`.
> - **Gloss.** `choose ℓ a = a(ℓ−a)+1` exactly when `a` or `ℓ−a` is `≤ 1`. The `⟸` direction is the
>   four computational edge cases; the `⟹` direction is the contrapositive of the genuine content
>   `choose_gt_aoyagiPoleOrder : (2 ≤ a) → (2 ≤ ell − a) → aoyagiPoleOrder ell a < Nat.choose ell a` (strict
>   divergence whenever `min a (ℓ−a) ≥ 2`).
> - **Proved.** The full iff, both directions, for all `a ≤ ℓ` — *no residual*. The strict
>   divergence half is proved by Pascal induction (fixed gap `g = ℓ−a`, induction on the base `b`,
>   `choose_succ_succ'` + the column lower bound `g ≤ choose (·) (·)` via `choose_symm` +
>   `choose_le_choose`).
> - **Assumed.** `a ≤ ℓ` (needed so `ℓ − a` is genuine subtraction).
> - **Cited.** Mathlib `Nat.choose` lemmas only (`choose_succ_succ'`, `choose_symm`,
>   `choose_le_choose`, `choose_one_right`, `choose_succ_self_right`). No external citation.
> - **Deferred.** none.
> - **Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]`.

---

## Honest-naming note (the point of the file)

`aoyagiPoleOrder` is named for what it is — an **analytic pole order** (real-log-canonical
multiplicity), NOT a component count. The geometric component count is the harness's
`Core.cTheta` / `Core.numTop`. The file proves the two are different (Capstone 1) and pins exactly
when they agree (Capstone 2); it does **not** assert any equality of the two θ's, which is false.

## Codex consult

`threads/28-theta-distinction/codex/strict-divergence-{prompt,answer}.md` — red-teamed the route
for the strict-inequality half (`choose_gt_aoyagiPoleOrder`). Codex recommended the fixed-gap +
induction-on-base Pascal route over the product/descFactorial alternatives; adopted (lemma names
all verified locally against Mathlib v4.29 before building).

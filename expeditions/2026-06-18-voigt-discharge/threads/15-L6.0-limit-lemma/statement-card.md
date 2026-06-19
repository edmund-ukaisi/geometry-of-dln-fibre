# Statement card — L6.0: the one-parameter polynomial-curve limit lemma

> **Claim.** Over an infinite field `k`, let `c : σ → k[X]` be a **polynomial curve** — coordinate
> `x` traces the univariate polynomial `c x`, so the curve's point at parameter `t` is
> `curvePoint c t : σ → k := fun x ↦ (c x).eval t`. If for every `t ≠ 0` the point `curvePoint c t`
> lies in a subset `Z ⊆ (σ → k)`, then the `t = 0` limit point `curvePoint c 0` lies in the **Zariski
> closure** of `Z`, i.e. in `zeroLocus (vanishingIdeal Z)`. Equivalently, every polynomial vanishing
> on `Z` also vanishes at `curvePoint c 0`.
>
> - **Lean:** `DLNFibre.Core.curvePoint_zero_mem_zeroLocus_vanishingIdeal`
>   (`lean/DLNFibre/Core/PolynomialCurveLimit.lean` @ `4256a0d6209a4a321a62b2a7979bb246e7cddbd6`)
> - **Gloss.** For `{k} [Field k] [Infinite k] {σ}`, a curve `c : σ → Polynomial k`, and a set
>   `Z : Set (σ → k)`, the hypothesis `hZ : ∀ t : k, t ≠ 0 → curvePoint c t ∈ Z` yields
>   `curvePoint c 0 ∈ MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k Z)`. Here
>   `curvePoint c t x = (c x).eval t` (def + `@[simp] curvePoint_apply`); `zeroLocus`/`vanishingIdeal`
>   are Mathlib's `MvPolynomial` Nullstellensatz pair (membership stated via `aeval`, same as
>   `Core.NullstellensatzCodim`). `σ` is **not** required finite; `k` need only be infinite (no
>   `IsAlgClosed`).
> - **Proved.**
>   - `curvePoint_zero_mem_zeroLocus_vanishingIdeal` — the headline, unconditionally within
>     `[Field k] [Infinite k]`.
>   - `eval_aeval_curve` — the evaluation-commutation:
>     `(aeval c g).eval t = MvPolynomial.eval (curvePoint c t) g`. Via `aeval_eq_eval₂Hom`,
>     `map_eval₂Hom`, and `evalRingHom t ∘ algebraMap k k[X] = RingHom.id k`.
>   - `aeval_curvePoint_zero_eq_zero_of_mem_vanishingIdeal` — the unfolded restatement: any
>     `g ∈ vanishingIdeal Z` satisfies `MvPolynomial.eval (curvePoint c 0) g = 0`.
>   - `curvePoint_zero_mem_of_isZariskiClosed` — when `Z = zeroLocus (vanishingIdeal Z)`
>     (Zariski-closed), the limit point lies in `Z` itself, not merely its closure.
>   - `curvePoint_const_zero` + in-file `example` (non-vacuity): the constant curve `t ↦ C (a x)` at a
>     point `a ∈ Z` has limit `a`, and the headline **fires** to place `a` in the closure of `Z` — the
>     conclusion is inhabited inside the green build.
> - **Assumed.** `[Field k]`, `[Infinite k]` (the weakest field hypothesis that makes the
>   infinite-root argument run; `[IsAlgClosed k]` would suffice but is strictly stronger and unneeded —
>   an alg-closed field is automatically infinite). No finiteness on `σ`.
> - **Cited.** none. Every step is a named Mathlib lemma applied here: `MvPolynomial.aeval_eq_eval₂Hom`,
>   `MvPolynomial.map_eval₂Hom`, `MvPolynomial.aeval_eq_eval`, `MvPolynomial.mem_vanishingIdeal_iff`,
>   `MvPolynomial.mem_zeroLocus_iff`, `Polynomial.coe_evalRingHom`, `Polynomial.eq_zero_of_infinite_isRoot`,
>   `Set.Finite.infinite_compl` + `Set.finite_singleton`. No external/analytic interface.
> - **Deferred.** none for this lemma. (Downstream L6.1 supplies an explicit polynomial family for `c`;
>   L6.2 the box-move chain; L6.4 assembles the ideal equality. L6.0 is the reusable brick beneath them.)
> - **Status.** sorry-free. Axioms `[propext, Classical.choice, Quot.sound]` (re-checked on all four
>   theorems). Whole library green. Awaiting reviewer fidelity check → `sorry-free + reviewed`.

## Route taken (what fought back, what came in bounded)

- **Curve encoding.** `c : σ → Polynomial k` (one univariate polynomial per coordinate), with the
  point `curvePoint c t = fun x ↦ (c x).eval t`. This is the recon's encoding and is exactly the shape
  L6.1 feeds in (substitute an explicit one-parameter family). No detour through `MvPolynomial σ (k[X])`
  or a `k[t]`-point was needed.
- **Evaluation-commutation (`eval_aeval_curve`) — the one piece to pin.** `P_g := aeval c g : k[X]`
  is the curve substituted into `g`. The identity `P_g.eval t = MvPolynomial.eval (curvePoint c t) g`
  came out of `aeval_eq_eval₂Hom` + `map_eval₂Hom (φ := evalRingHom t)`, leaving the goal
  `eval₂Hom ((evalRingHom t).comp (algebraMap k k[X])) (fun x ↦ evalRingHom t (c x)) g = eval (..) g`;
  the composite ring hom is `RingHom.id k` (eval of a constant), after which the two sides are `rfl`
  (`eval f = eval₂Hom (RingHom.id k) f` definitionally). `eval₂_comp_right` was tried first but routes
  through `map f`, which is the wrong shape; `map_eval₂Hom` is the clean one.
- **Roots lemma.** `Polynomial.eq_zero_of_infinite_isRoot` (needs `[CommRing k] [IsDomain k]`,
  supplied by `Field`). The infinite root set is `{0}ᶜ`, infinite via
  `Set.Finite.infinite_compl (Set.finite_singleton 0)` (needs `[Infinite k]`). This is the **only**
  place `Infinite k` enters — hence it is the right hypothesis, not `IsAlgClosed`.
- **`aeval` vs `eval` bookkeeping.** Mathlib's `zeroLocus`/`vanishingIdeal` state membership with
  `aeval x p`; the commutation lemma is in `eval` form. Bridged by `MvPolynomial.aeval_eq_eval`
  (a function-level `rfl`) at the two interface points.

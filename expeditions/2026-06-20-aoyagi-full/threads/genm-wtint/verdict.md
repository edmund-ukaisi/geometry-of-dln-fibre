# genm-wtint — the outer `det^{−a/2}` integrability verdict

**Seat:** pen-and-paper (obstruction, adjudicating one truth-value). **Task:** does the Route-M `(□)`
Regime-A good-stratum discharge integrate the emitted OUTER weight `det(Q_b Q_bᵀ)^{−a/2}` WITHOUT a
quantitative minor lower bound (Cauchy–Binet `det ≥ minor²`)? **NO Lean.** **Direction:** dispatched
adversarially toward the WALL (controller suspected ABSORBED). **Exact algebra:** `/tmp/wtint_localmodel.py`,
`/tmp/wtint_witness.py`, `/tmp/wtint_boundary.py`. **Decorrelated:** `/tmp/wtint_codex_prompt.md` +
`/tmp/wtint_codex_out.md` (gpt-5.1-codex-max, xhigh; my conclusion WITHHELD — asked open-ended "is `I`
finite; does the `h`-IH dominate or does the det weight need its own control" — it independently produced
the WALL verdict, the same `(B,T)` vs `(Y,T)` domination-failure mechanism, and the single-minor bound).

---

## VERDICT: **WALL** (Cauchy–Binet genuinely resurfaces; absorption does NOT close it)

The outer `det(Q_b Q_bᵀ)^{−a/2}` weight is **not** dominated/absorbed by the absorption CoV + the
reduced-chain IH. Its finiteness is an **independent determinantal-integrability obligation** on the Gram
weight, and certifying it requires a Cauchy–Binet **lower** bound `det(Q_b Q_bᵀ) ≥ (b×b minor)²`. The
"ABSORBED, no minor bound needed" reading is false — and it contradicts the peel-cert's own §B=2 COVER,
which already uses Cauchy–Binet (`det = Σ_S minor_S²`) to build the dominant-minor cover.

**Two scopes must not be conflated** (the first Codex `piece8-prereq` answered the first, flagged the second
as the trap; this adjudicates the second):

- **ENTERING** the good stratum `{rank Q_b = b}` — needs only `det > 0`, i.e. `PosDef` from `rank = b` via
  `posDef_iff_dotProduct_mulVec`. **No Cauchy–Binet.** (First Codex correct.)
- **INTEGRATING** the emitted `det^{−a/2}` over the outer variables — **WALL.** The weight blows up at the
  boundary `{rank Q_b < b}` of the (open) good stratum, and controlling that blow-up is the minor-bound
  obligation below.

This is **not** a wall to the *result* (the result is true — MC-confirmed, cited Aoyagi). Cauchy–Binet is
elementary and bankable. The verdict is that it is **load-bearing and NOT eliminable by absorption** — the
"reduced-chain IH dominates it" story is the analytic analogue of the codim-accounting shortcut the
controller warned against, and it fails for the same reason.

---

## The certifying argument (why absorption cannot dominate — exact)

The outer integrand factors as `det(Q_b Q_bᵀ)^{−a/2} · frobSq(B₀)^{−c′′}` with, from the peel-cert,
`Q_b = Y·A_{≥2}` (corank rows `Y`, `b×q`) and `B₀ = B·A_{≥2}` (absorbed pivot `B`, `t×q`). The two factors
depend on **disjoint leading blocks**:

- `frobSq(B₀) = frobSq(B·A_{≥2})` depends on `(B, A_{≥2})` — **identically independent of `Y`**.
- `det(Q_b Q_bᵀ)` depends on `(Y, A_{≥2})` — the singular direction is `Y`.

**Breaking sequence (domination-failure witness, `/tmp/wtint_witness.py`).** Symbolically, every partial
`∂ frobSq(B·T)/∂Y_{ij} = 0` (verified, all zero); `det(Q_b Q_bᵀ)` genuinely depends on `Y`. So fix `B, T`
generic (`frobSq(B·T) = c₀ > 0` fixed) and take `Y_n → Y_*` with `rank(Y_*·T) = b−1`, `rank(Y_n·T) = b`
(good stratum). Then along the sequence

    det(Q_b(Y_n) Q_b(Y_n)ᵀ) → 0,   det^{−a/2} → ∞,   frobSq(B₀) ≡ c₀ (PINNED).

Numeric instance `(b=2,q=2)`: `det = 5.2e−3, 5.2e−5, 5.2e−7, 5.2e−9` with weight `1.4e1 … 1.4e4` while
`frobSq(B·T) = 0.238` fixed. The reduced-chain IH controls the `∫ dB` integration; it says **nothing** about
the `∫ dY` blow-up, because the factor it bounds is **constant along the direction the weight diverges**. So
"absorbed by the reduced-chain IH" fails structurally, in every category.

**The Gram weight's own integrability (the real content, exact + decorrelated).** Near a smooth point of the
top rank-drop stratum `{rank Q_b = b−1}`, the determinantal normal form gives (`/tmp/wtint_localmodel.py`,
residual-0 for `b=2, q=2,3,4`):

    det(Q_b Q_bᵀ) = Σ_{|S|=b} minor_S(Q_b)²   (Cauchy–Binet)   ≍ |z|²,   z ∈ ℝ^{q−b+1} transverse,

so `∫ det^{−a/2} ~ ∫_{ℝ^{q−b+1}} |z|^{−a} dz`, **finite ⟺ `a < q−b+1` ⟺ `a + b ≤ q`** (sharp; log-divergent
at equality). MC boundary scan (`/tmp/wtint_boundary.py`, `(b,q) ∈ {(2,2),(2,3),(2,4),(3,4)}`) confirms the
line exactly — finite for `a < q−b+1`, blows up for `a ≥ q−b+1`. The product structure `Q_b = Y·A_{≥2}` does
**not** change the local model: where `A_{≥2}` has rank `≥ b`, `Y ↦ Y·A_{≥2}` is a submersion, so the
determinantal variety pulls back with the same codimension `q−b+1` and the same linear vanishing (Codex,
independent). This is the peel-cert's category split, now pinned as the *integrability boundary of the
emitted weight*: category I (`a+b ≤ q`) the weight is integrable over the whole chart; category II/III
(`a+b > q`, ≈25% of charts incl. `(2,2,1)`) it **diverges over the good stratum** — the whole-line Γ-peel
must not be used and the corner/Regime-B closes it instead.

**Deeper strata are non-binding for THIS weight.** For `{rank Q_b ≤ b−r}` (codim `r(q−b+r)`), `det` vanishes
to order `2r`, giving the condition `a < q−b+r`, which is *weaker* for `r ≥ 2`. So the top stratum `r = 1`
is the binding one and the single-minor bound suffices — the emitted-weight question does **not** hit the
`cornrev` deeper-strata `{rank ≤ b−2}` gap (that gap is a different obligation: the RLCT of the full corner
integral, not the integrability of this weight over the good stratum).

---

## Codex independent read (my conclusion withheld — quoted)

> **Role of the h-factor.** "`h(B,T)` is independent of `Y`, while the singular factor `det(GGᵀ)^{−a/2}`
> depends on `(Y,T)` via `YT`. The known finiteness of `∫ h(B,T) d(B,T)` therefore does **not** control the
> new singularity in `Y`. Even with `h` integrable, the integral over `Y` near `{rank YT = b−1}` can diverge
> unless the above condition `a < q−b+1` holds. Thus the determinant weight requires independent control."

> **Condition.** "`det(GGᵀ) ≍ t²` … integrability near `t=0` requires `a < codim = q − b + 1`. This is sharp:
> at `a = q−b+1` the integral diverges logarithmically… `G = Y·T` does not change this local model" (`Y ↦ YT`
> a submersion where `T` has rank ≥ b).

> **Minimal fact.** "Use Cauchy–Binet `det(GGᵀ) = Σ (minor_S)²`. Near a smooth rank-`b−1` point, exactly one
> `b×b` minor serves as a transverse coordinate and vanishes linearly; the sum-of-squares form implies
> `det(GGᵀ) ≥ (that minor)²`. This single-minor lower bound is sufficient to obtain `det^{−a/2} ≤ |minor|^{−a}`
> … the full sum or the 'max minor' bound is not stronger for integrability; one well-chosen minor that cuts
> the rank-drop divisor suffices, and this is sharp."

Fully decorrelated agreement: WALL, the `(B,T)`-vs-`(Y,T)` domination failure, the `a < q−b+1` boundary, the
submersion fact for the product, and the single-minor minimal bound.

---

## The MINIMAL minor bound actually needed

**Not** the full Cauchy–Binet `Σ`-identity, **not** specifically the `max`-minor form — the minimal
sufficient (and sharp) fact is the **single-minor lower bound**

> `det(Q_b Q_bᵀ) ≥ minor_{S₀}(Q_b)²`   for a minor `S₀` transverse to `{rank = b−1}`,

a one-line corollary of Cauchy–Binet (drop all but one nonnegative term). It yields the local upper bound
`det^{−a/2} ≤ |minor_{S₀}|^{−a}`, and integrability then reduces to a single polynomial's power over the
transverse `ℝ^{q−b+1}` (the `a < q−b+1` test). The extra ingredient is geometric, also elementary and
bankable: **that minor vanishes to order 1 on the rank-drop divisor** (it is a local defining equation / part
of a regular system of parameters for the determinantal ideal at a smooth point), so `minor_{S₀} ≍ |z|`.
Cauchy–Binet + this transversality are exactly what the peel-cert §B=2 COVER already invokes; the honest
statement is that they are *required*, not absorbable.

---

## CLOSE

- **Firmest.** WALL. The reduced-chain IH is *constant along* the `Y`-direction in which
  `det(Q_b Q_bᵀ)^{−a/2}` diverges (`∂ frobSq(B·T)/∂Y ≡ 0`, exact), so it cannot dominate the Gram weight.
  Certifying the weight's finiteness is an independent determinantal-integrability step: `det ≍ |z|²` over the
  codim-`q−b+1` top stratum (Cauchy–Binet `det = Σ minor²`, residual-0), giving the sharp `a < q−b+1` boundary
  and the minimal single-minor lower bound `det ≥ minor²`. Decorrelated Codex reached this independently.
- **Most likely to break / watch.** The WALL is scoped to the *top* stratum `{rank = b−1}` and the *emitted
  weight* (not the deeper-strata RLCT). If a formaliser tries to route category-II charts (`a+b > q`, e.g.
  `(2,2,1)`) through the whole-line Γ-peel, the emitted `det^{−a/2}` is genuinely NON-integrable there — the
  divergence is real, not a proof artifact; those charts MUST use the corner/Regime-B (as the cert already
  routes). Do not "absorb" the weight on a category-II chart.
- **Next.** Formaliser: bank the single-minor Cauchy–Binet corollary `det(Q_b Q_bᵀ) ≥ minor_{S₀}²` + the
  order-1 vanishing of `minor_{S₀}` on the rank-drop divisor as the good-stratum weight-control lemma
  (category I / top stratum); keep it *separate* from the deeper-strata resolution (`cornrev` gap), which this
  question does not touch. The dominant-minor cover of §B=2 COVER is the correct home for this bound.

# R1-UPPER sub-piece (a): arity-recursive shifted-exponent layer-peel — DESIGN CERTIFICATE

**Seat:** pen-and-paper WITNESS (aoyagi-full). **Target:** design the arity-recursive
shifted-exponent box-integral peel for `RouteMBoxThresholdFinite M`
(= `rlct ≥ ½·minAdm`, the general-L R1-UPPER long pole). Method: from-scratch derivation off
Aoyagi §5 + exact algebra (sympy/exact-rational, MC guide only) + decorrelated Codex xhigh
red-team. NO Lean edits.

## VERDICT (two parts, both load-bearing)

1. **The exponent-shift mechanism is REAL and the threshold it targets is EXACTLY `½·minAdm`.**
   The per-boundary charge composes additively via a genuine exponent shift `c' ↦ c' − ½·(M₀−t)(M₁−t)`,
   reproducing `minAdmRec` exactly (0/8000 chains, L≤5). It reaches `½·minAdm` on every chain the
   banked exponent-*preserving* fibre engine undershoots (`(3,3,3,3)`: 2×; `(4,4,4,4)`: 2.75×).

2. **The CLEAN arity recursion that sub-piece (a) hoped for — "peel boundary 0 to a single reduced
   tail chain `(t,M₂,…,M_L)` at the shifted exponent, with a benign spectator" — is UNSOUND.** The
   spectator factor the front-peel produces is **not** benign; decoupling it (reducing to a single
   tail chain) creates a *false* divergence. The honest per-step object is a **joint** two-norm
   integral, which at L=2 is exactly the built `SchurCore` corank recursion and at **L≥3 is Aoyagi's
   simultaneous rank-flag resolution** — the same "L-layer joint resolution that does not exist" wall
   (Items 57/97/116), now **independently re-derived from the arity route and sharply localized** to
   the spectator coupling. Codex (decorrelated, xhigh) independently returned **BROKEN as stated /
   not bounded labour in the present form**, with a concrete counterexample I verified exactly.

**Net:** the arity-recursive peel is not a shortcut past the wall. The exponent-shift is a correct
*ingredient* of the genuine (joint) construction; the *decomposition into independent per-boundary
1-D peels* is the part that fails. Escalation signal for the operator: sub-piece (a) as scoped does
not close R1-UPPER; the honest route is the joint resolution (Aoyagi's `(S,J)` double induction),
whose L≥3 form is the standing wall. The `½·minAdm` **value** is not in doubt (Aoyagi-established;
`cited_aoyagi_dln` remains the fallback for the headline).

---

## 1. Exact target (grounded against Lean, not re-derived)

`RouteMBoxThresholdFinite M := ∀ c' < ½·minAdm M, ∫_{A∈paramsBoxM M 1} frobSq(prod M A)^{−c'} < ⊤`
(`RouteMBoxReduction.lean:165`). `paramsBoxM M 1` = all entries in `[−1,1]`, **centered at the
origin** (`:56`); `prod M A = A₀·…·A_{L−1}`, `Aₛ : Mₛ×M_{s+1}` (`Loss.lean:29,48`);
`frobSq = ‖·‖²`. So the target is exactly the local integrability of `‖∏Aₛ‖^{−2c'}` at the origin —
i.e. Aoyagi's `λ₀⟨∏ C^{(s)}⟩ ≥ ½·minAdm` with all factors free near 0 (no Theorem-3 rank split
needed: the box already sits at the corank-zero-product locus).

Repo `Mval` (`Lambda.lean:41`) **is** Aoyagi's `M(T)=∑_{j=1}^L (t^{(j−1)}−t^{(j)})(M^{(j+1)}−t^{(j)})`,
`t^{(0)}:=M₀`; repo `Adm` **is** his admissible cone (weak-decrease, last-exponent-0, block bound);
`minAdm = min_{T∈Adm} Mval`, and `minAdmRec` (`RouteMLayerSplit.lean:58`) is the proven
layer-peeling recursion
`minAdm(M₀,…,M_L) = min_{t≤min(M₀,M₁)}[(M₀−t)(M₁−t)+minAdm(t,M₂,…,M_L)]`.
Exact-verified: `minAdmRec == min_T Mval`, 0/6000; anchors `(2,2,2)=3,(2,2,2,2)=3,(3,3,3,3)=6,
(3,3,4)=8,(4,4,2,2)=4`. Binding paths: `(3,3,3,3)`: `T*=(2,1,0)` per-boundary `[1,2,3]` (sum 6);
`(2,2,2,2)`: `T*=(1,0,0)` `[1,2,0]`. (`r1u_minadm.py`.)

## 2. The peel and the exponent shift (the correct ingredient)

Front factor `A₀ : M₀×M₁`, tail `Q := A₁⋯A_{L−1} : M₁×M_L`. On the pivot chart where a `t×t` block of
`A₀` is invertible, Aoyagi's Lemma-2 unit-triangular **Jacobian-1** change of variables `Q₁A₀Q₂ =
diag(A₀^{[t]}, Γ)` exposes the corank block `Γ : (M₀−t)×(M₁−t)` (`Γ = A₀^{(4)} − A₀^{(3)}(A₀^{[t]})^{−1}A₀^{(2)}`,
the Schur complement). Radially blow up `Γ = z·V` (`z≥0`, `V` on the unit sphere), Jacobian
`z^{a−1}dz dσ(V)`, `a := (M₀−t)(M₁−t)`. Block-diagonality gives, exactly (no cross terms; `A₀^{[t]}`,
`Q₁^{−1}` bounded on the box),

    ‖A₀Q‖²  ≍  ‖Q_top‖² + z²‖V Q_bot‖²  =:  g² + z²h²,

with `g = ‖Q_top‖` the top-`t` rows of the tail product = the tail **chain** of widths `(t,M₂,…,M_L)`
(an `(L−1)`-factor product), and `h = ‖V Q_bot‖` the bottom `(M₁−t)` rows (the spectator).

**The 1-D exponent-shift integral (exact, `r1u_shift2.py`).** For `c' > a/2`,

    ∫₀^∞ (g²+z²h²)^{−c'} z^{a−1} dz  =  ½·B(a/2, c'−a/2) · h^{−a} · g^{−2(c'−a/2)},

closed form matches quadrature to ratio 1.0. The `g`-exponent is `−2(c' − a/2)` = **shifted**
`c'' = c' − ½(M₀−t)(M₁−t)`, strictly `< c'` for `t < min(M₀,M₁)`. So the boundary-0 charge
`½·(M₀−t)(M₁−t)` is spent as a genuine reduction of the tail exponent budget.

**The recursion reproduces `minAdm` exactly (`r1u_recur.py`).** Chart-`t` supports
`c' < ½[(M₀−t)(M₁−t) + minAdm(t,M₂,…,M_L)]` (charge + shifted-tail recursion, base L=1 = free
`t×M_L` matrix, `c' < ½·t·M_L`). Box = ⋃ charts ⇒ converges to the **min over t** = `½·minAdm`.
Exact: `thr(M) == ½·minAdm(M)`, 0/8000, L≤5. The binding cut is often the *small*-charge one
(`(3,3,3,3)`: `t=2`, charge ½, tail `minAdm=5` → c'<3), which only the shift — not an
exponent-preserving peel — can reach. Undershoot table (`r1u_wall.py`): shifted reaches `½·minAdm`
on all; preserving undershoots `(2,2,2,2)` 1.5×, `(3,3,3,3)` 2×, `(4,4,4,4)` 2.75×.

## 3. Where it BREAKS — the spectator is not benign (Codex-found, exact-verified)

The design step "after the `z`-integral the tail integrand is `g^{−2c''}` with a benign `h^{−a}`" is
**wrong**. Two flaws, one root:

- **The `∞`-Beta discards the finite cutoff.** The box is compact (`z ∈ (0,R)`, `R=O(1)`). The
  honest integral is
  `∫₀^R (g²+z²h²)^{−c'} z^{a−1} dz = g^{a−2c'} h^{−a} Φ(Rh/g)`, `Φ(T)=∫₀^T u^{a−1}(1+u²)^{−c'}du`.
  For `h ≲ g` (`T→0`), `Φ(T) ≈ T^a/a`, and the residual collapses to `≈ g^{−2c'}·R^a/a` — **full
  exponent, NO `h^{−a}`**. The `∞`-Beta uses the `h ≳ g` branch everywhere, over-counting the
  spectator into a **false** singularity.

- **Counterexample (Codex; verified `r1u_codex_check.py`/`r1u_mc2.py`).** `M=(2,2,1)`, `t=1`, `a=1`,
  `minAdm=2`, `λ=1`. Tail `= (u,v)` (rows of the free `2×1` factor), `g=|u|`, `h=|v|`. The `∞`-Beta
  residual at `c'=¾` is `|u|^{−½}|v|^{−1}`, **non-integrable in v** (`∫₀¹|v|^{−1}dv = ∞`). But the
  honest finite integral `∫₀¹(u²+z²v²)^{−¾}dz`, integrated over `(u,v)`, is **finite** — and finite
  exactly for `c' < 1 = λ` (MC: stable 2.7/7.6/21/41 for c'=.5/.75/.9/.98; blows up 124/1997 past 1).
  The `∞`-Beta manufactures a divergence the true integral does not have.

The "spectator bounded-below" claim (`h ≥ σ_min(Q_bot) > 0`) fails because `Q_bot` is a *free*
variable ranging through 0: `h→0` on a positive-codimension locus, and `h^{−a}` alone is
non-integrable across it. The finite cutoff `Φ(Rh/g)` is exactly what cancels this — and it
**couples `g` and `h`**. The correct per-step object is therefore not a single reduced chain; it is
the **joint** `(g,h)` integral `∫_tail g^{a−2c'} h^{−a} Φ(Rh/g) d(tail)`.

## 4. Why the joint object is the wall at L≥3 (and is the built SchurCore at L=2)

- **L=2:** the tail `(t,M₂)` is a **single free matrix**; `g,h` are norms of disjoint row-blocks of
  it, the joint integral factors/decouples, and it is precisely the repo's `SchurCore` corank
  recursion — **built and proven ∀(r,r,p)** (`RouteMSchurGeneral.lean`, `RouteMBoxThresholdRRP.lean`).
  For `(2,2,1)` the honest analytic domain-split gives `∫₀¹ u^{1−2c'}[C+Φ(∞)ln(1/u)]du`, finite iff
  `c'<1`. Clean, tight.

- **L≥3:** the tail is a **product** `(t,M₂,…,M_L)`, so `g = ‖(top rows)·A₂⋯‖` and
  `h = ‖V·(bottom rows)·A₂⋯‖` share the deeper factors `A₂,…`. The finite-cutoff crossover
  `Φ(Rh/g)` couples them through the shared factors; `h→0` is a rank-drop of the tail at boundary 1,
  a deeper admissible stratum that must be resolved **simultaneously** with the top chain. This is
  Aoyagi's `diag(b)·[E_J | D_J]·∏_{s>S}C^{(s)}` double induction on `(S,J)` — it carries the *whole*
  partially-resolved block, not a reduced chain + scalar weight. It does **not** reduce to
  independent per-boundary 1-D peels. This is the `SchurCore`-is-intrinsically-two-matrix wall
  (Items 57/97/116), re-derived from the arity route and localized to: *the boundary-0 spectator
  `h = ‖V·tail-bottom-rows‖` couples to the tail chain `g` through the shared deeper factors, and the
  finite cutoff that makes their joint integral converge is exactly the simultaneous rank-flag
  resolution.*

## 5. Sub-pieces (b) and (c), re-scoped by this finding

- **(b) joint no-double-count** is now the **primary** content, not a follow-on: it is the claim that
  the joint `(g,h)` finite-cutoff integral converges to `½·minAdm` without the spectator's `h→0`
  locus double-charging the deeper strata. Verified true at L=2 (SchurCore) and as a *threshold* at
  L≤5 (`thr==½·minAdm`), but the L≥3 *integral-level* proof is the un-built joint resolution.
- **(c) cross-boundary measure handle** — the `Q₂(A₀)`-mixing into the tail measure — remains: after
  `Q₂^{−1}`, the tail is a product with an `A₀`-dependent left factor on `A₁`. At L=2 harmless (absorbed
  into the free tail matrix); at L≥3 it is part of what makes the tail a genuine (non-free) product,
  compounding (b).

## 6. Closing (firmest result / most-likely-to-break / next step)

- **Firmest:** the exponent-shift is exact and targets `½·minAdm` exactly (0/8000); the clean
  single-chain arity recursion is unsound (Codex counterexample, exact-verified); the genuine per-step
  object is the joint `(g,h)` finite-cutoff integral = SchurCore at L=2, the standing L≥3 joint-
  resolution wall above.
- **Most likely to overturn the negative:** a recursion that carries the spectator norm as a *scalar
  auxiliary weight* alongside a reduced chain (rather than the whole `D_J` block) and still converges
  to `½·minAdm`. I judge this unlikely — Aoyagi carries the whole block for a reason (the top/bottom
  coupling is matrix-valued, not scalar) — but it is the one un-probed escape and the cheapest thing
  to try before accepting the wall.
- **Next construction to settle it:** attempt the joint per-step lemma on the smallest L≥3 product
  tail — `(2,2,2,2)` binding `t=1`, tail `(1,2,2)` (a `1×2 · 2×2` product), spectator = the second
  row of `A₁'A₂` — and check whether `∫ min(g^{−2c'}, h^{−1}g^{−2(c'−½)}) d(A₁',A₂)` reduces to the
  tail chain's own resolution or genuinely needs the joint blow-up. That is the decisive L=2→L≥3
  discriminator.

## Files / reproduction
- Codex trail: `codex/exponent-shift-prompt.md`, `codex/exponent-shift-answer.md` (xhigh, BROKEN-as-stated).
- Exact algebra: `r1u_minadm.py` (minAdm==rec, binding paths), `r1u_shift2.py` (1-D shift, Beta),
  `r1u_recur.py` (thr==½minAdm 0/8000 + per-chart), `r1u_wall.py` (shift-vs-preserving undershoot),
  `r1u_spectator.py` (spectator flaw + L=2 factorization), `r1u_mc2.py` (honest (2,2,1) MC guide).
- Lean anchors: `RouteMBoxReduction.lean` (target), `RouteMLayerSplit.lean` (minAdmRec),
  `RouteMSchurGeneral.lean`/`RouteMBoxThresholdRRP.lean` (the L=2 joint object, built),
  `MatMulFibre.lean:399` (the exponent-preserving cap that undershoots).

## Instrument caveat
Exact algebra measures `minAdm` (the threshold value), the 1-D shift integral (closed form), the
recursion arithmetic, and the L=2 counterexample/factorization — all exact. The L≥3 box integral was
not numerically integrated (heavy-tailed); the negative verdict rests on (i) the exact `(2,2,1)`
counterexample showing the naive step is unsound, (ii) the exact identification of the honest per-step
object as the joint `(g,h)` integral, and (iii) its structural identity at L≥3 with the
already-adjudicated `SchurCore`-two-matrix wall. The `½·minAdm` value is Aoyagi-established, not in
question.

---

# ADDENDUM (2026-07-06): the L=2→L≥3 discriminator — JOINT (S,J) NEEDED, BOUNDED

**Dispatch:** run the discriminator on `(2,2,2,2)` binding `t=1`, tail `(1,2,2)` (a `1×2·2×2`
product), spectator = 2nd row of `A₁·A₂`: does the joint `(g,h)` finite-cutoff per-step lemma REDUCE
to the tail chain `(1,2,2)`'s own resolution, or genuinely need the simultaneous `(S,J)` blow-up? This
decides "commit the full `(S,J)` mountain" vs "a partial single-chain reduction exists."

## VERDICT: the peel does NOT reduce to a black-box single-chain call — the joint `(S,J)`
## resolution is required at every `L≥3`, `a>0` cut. It is BOUNDED labour (Aoyagi goes through),
## NOT a new obstruction. **Commit the `(S,J)` mountain build; do not hunt for a single-chain shortcut.**

Decorrelated Codex (xhigh) returned the SAME verdict independently, with a divisor-by-divisor proof.

## The exact per-step identity (the decisive new structural fact, 0 numerical error)

Doing the finite `z`-integral and using `g²+h² = ‖A₁·A₂···A_{L−1}‖²` **exactly** (`A₁ = [top rows;
bottom rows]` stacked), the boundary-0 peel at cut `t` collapses to

    J  ≍  P_tail^{−(c'−a/2)} · P_full^{−a/2},        a = (M₀−t)(M₁−t),

where **`P_tail = ‖(top t rows)·A₂···‖²`** is the reduced tail chain `(t,M₂,…,M_L)` loss, and
**`P_full = ‖A₁·A₂···A_{L−1}‖²`** is the **FULL remaining product** `(M₁,…,M_L)` loss — a coupling
factor **absent from the tail chain's resolution**. Nested loci `{P_full=0} ⊂ {P_tail=0}`,
`P_full = P_tail + ‖(bottom rows)·A₂···‖² ≥ P_tail`. (`r1u_identity.py`, `r1u_binding.py`, both cases
`(2,2,2,2)`/`(3,3,3,3)`, exact.) So the peel does **not** produce a single reduced chain; it produces a
*product* of the tail chain and the full-product norm.

## Why it does not reduce (exact + Codex-corroborated)

- **At every binding cut, `P_full` is subordinate** (`a/2 < RLCT(P_full)=½·minAdm(M₁,…,M_L)`, strict
  for `a>0`; verified over all cases incl. `L=4`, `r1u_binding.py`). So the *value* is exactly
  `½·minAdm` — the binding factor is `P_tail` and the exponent-shift threshold is correct. **No new
  obstruction to the value.**
- **But subordinate ≠ benign.** On a common resolution the convergence is divisor-by-divisor
  `(c'−a/2)·ord_E(P_tail) + (a/2)·ord_E(P_full) < jacThreshold_E`. A black-box tail-chain theorem checks
  only the first term. For `L≥3` the deeper factors `A₂,…,A_{L−1}` are **shared**, so there are
  exceptional divisors where **both** orders are positive and the exponents **add** — invisible to a
  single-chain call. The nesting `P_full ≥ P_tail` only gives the crude `J ≤ P_tail^{−c'}`, which
  undershoots to `c'<RLCT(P_tail)` (the factor-of-2-style loss again). (Codex, exact-corroborated.)
- **Accumulation strengthens it.** Each successive peel adds another `P_full^{(k)−a_k/2}` on the shared
  variables — exactly Aoyagi's `diag(b₁,…,b_{M(S)})` monomial / the `D_J` double-induction block. Their
  orders pile on the same shared deeper divisor; no single-chain recursion sees the summed
  contributions. The `(S,J)` bookkeeping is precisely what tracks them.

## The exact L=2 → L≥3 mechanism (why the built machinery stops at L=2)

- **L=2:** `P_tail` and `P_full` are **disjoint ROW-BLOCKS of one FREE matrix `A₁`** (no deeper
  factors), hence **independent**; on `{P_tail=0}` the coupling `P_full` is bounded below
  (`r1u_binding.py`, exact). The coupling decouples → the single-chain **corank (`SchurCore`) recursion
  suffices — and is BUILT ∀(r,r,p)**.
- **L≥3:** `P_tail` and `P_full` **share** `A₂,…,A_{L-1}`; both degenerate on a shared factor's
  rank-drop, the coupling rides the same divisors and accumulates. The corank recursion is intrinsically
  two-matrix and cannot represent this — the standing wall, now with its exact mechanism named.

## Consequence for scope (the multi-month decision)

- **Commit the full `(S,J)` simultaneous rank-flag build** (Aoyagi's `diag(b)·[E_J|D_J]·∏_{s>S}C^{(s)}`
  double induction). It is **BOUNDED** (the coupling is always subordinate ⟹ Aoyagi's construction goes
  through; the threshold value is exactly `½·minAdm`) — a joint-blow-up tide in the style of the
  interior/smeared builds, but carrying the joint block, NOT a clean arity recursion.
- **Do NOT hunt for a single-chain partial reduction** — the exact identity proves the coupling factor
  `P_full^{−a/2}` is un-eliminable and shares divisors at `L≥3`. The exponent-shift is a correct
  *sub-ingredient* that must be embedded in the joint bookkeeping, not a standalone recursion.
- **Cheapest thing that would overturn this** (Codex's test, worth one exact pass before committing): a
  no-loss uniform multiplier estimate on the first coupled `L=3` case —
  `∫_Y (‖XB‖²+‖YB‖²)^{−a/2} dY ≤ C·logᴺ(1/‖XB‖)` uniform as `B` drops rank (`A₁=[X;Y]`, `B=A₂···`).
  Any positive power loss in `B`'s singular values ⟹ joint divisor data ⟹ single-chain reduction fails
  (my prediction: it loses a power — the `{det B=0}` divisor carries both orders).

## Files
- `r1u_identity.py` (exact per-step identity `J ≍ P_tail^{−(c'−a/2)}P_full^{−a/2}`, 0 error, both cases),
  `r1u_binding.py` (binding-cut order table: `P_full` subordinate ∀; L=2 row-block decoupling, exact),
  `r1u_rlct_anchor.py` (nesting `P_full≥P_tail`; minAdm anchors), `r1u_disc2.py` (MC guide — uniform
  sampling cannot resolve the high-codim singularity, superseded by the exact identity).
- Codex discriminator trail: `codex/discriminator-prompt.md`, `codex/discriminator-answer.md`
  (independent JOINT-NEEDED / BOUNDED verdict + divisor-by-divisor proof).

---

# ADDENDUM 2 (2026-07-06): Codex's overturn test — power loss CONFIRMED, (S,J) BOUNDED-and-needed

**Dispatch:** run the overturn test — does `∫_Y (‖XB‖²+‖YB‖²)^{−a/2} dY ≤ C·logᴺ(1/‖XB‖)` hold with
NO power loss (revives a single-chain reduction, OVERTURNS joint-needed), or does `{det B=0}` carry a
power (confirms joint `(S,J)` needed, BOUNDED)? Prediction was: loses a power.

## VERDICT: prediction CONFIRMED. The multiplier loses a power on the shared factor's low-rank
## strata. The black-box single-chain reduction fails; **commit the joint `(S,J)` build. BOUNDED**
## (all charges sum to `minAdm`; the coupling is subordinate, value = exactly `½·minAdm`).

Decorrelated Codex (xhigh) returned the SAME verdict and, crucially, **killed the lighter escape**.

## The exact multiplier criterion (the decisive new result)

Integrating out the spectator rows `Y` first, `M(X,B) := ∫_Y (‖XB‖²+‖YB‖²)^{−a/2} dY`
(`g:=‖XB‖=√P_tail`, `B` = the shared deeper product `A₂···A_{L−1}`) obeys, **exactly** (GL-quadrature
+ MC, clean slopes, `r1u_overturn2.py`/`r1u_criterion.py`/`r1u_rankdrop.py`):

    M(X,B)  ≍  bounded / log(1/g)                      when  a ≤ (M₁−t)·rank(B)
    M(X,B)  ≍  g^{−(a − (M₁−t)·rank(B))}   (POWER)      when  a > (M₁−t)·rank(B).

So the coupling factor `P_full^{−a/2}` is **benign (only a log — harmless to the RLCT) on the generic,
full/high-rank shared factor**, but **loses a power exactly on the shared factor's LOW-RANK strata**.
Confirmed sharply: `(4,4,4,4)` cut `t=2` (`a=4`, spectator `2×4`) — at `rank(B)=1` the multiplier
`~ g^{−2}` (slope +1.60 ≈ 2). At full-rank `B`, `a ≤ (M₁−t)M₂` at ALL binding cuts (0 / 5440).

## Why this does NOT overturn (the reduction genuinely fails), and the lighter escape is illusory

- The power-loss strata are the shared factor's rank drops = the **deeper boundary's** rank drops. A
  black-box tail-chain theorem has no parameter for the **inherited deficit** `δ = (a−(M₁−t)rank(B))₊`
  the peel dumps onto the deeper product; the deficit changes the effective exponent on the shared tail
  from `c'−a/2` to `c'−(M₁−t)rank(B)/2`. (Codex, verbatim.)
- **The "gentle-cut" escape fails two ways.** (i) A uniformly-gentle binding path (`a ≤ M₁−t` at every
  `L≥3` peel, confining power loss to `rank(B)=0`) does **not** always exist — 1966/5440 chains force a
  non-gentle cut at some level (`r1u_gentle.py`). (ii) Even the "generic-`B` first, low-rank-`B`
  separately" split is not a true escape: the low-rank branch must carry the inherited charge `δ` into
  deeper exceptional variables — a rank-stratified sub-induction that IS Aoyagi's `D_J`/`diag(b)`
  mechanism under another name (Codex, exact-corroborated).
- **Precise formal statement** (Codex's caveat, folded in): the multiplier creates an inherited charge
  supported on the deeper **product-rank** strata; the double induction proves this charge is paid by
  those strata's Jacobian/codimension surplus. ("Power loss = deeper boundary's rank drop" is the right
  heuristic but literal only after the rank-`B` stratum is resolved into layer-wise rank-drop divisors.)

Net: the exponent-shift is a correct sub-ingredient; the coupling is benign generically and bites only
on shared-factor rank-drop divisors — but those cannot be dodged by cut selection nor factored into a
black-box call, so the joint `(S,J)` bookkeeping is required. It is BOUNDED (Aoyagi-established).

## Commit-the-`(S,J)`-build spec sketch (Aoyagi §5 + Codex, dependency order)

Invariant (Aoyagi p.15): `⟨∏_{s=1}^L C^{(s)}⟩ = ⟨diag(b₁,…,b_{M(S)})·[E_J | D_J]·∏_{s>S}C^{(s)}⟩`,
running-min corank `M(S)=min{M^{(s)}:s≤S}`, within-layer rank-drop counter `J`, radial monomials
`b_i = ∏_{t̃_{s,k}=i−1} u_{s,k}·b_{i−1}`, Jacobian `∏ u_{s,k}^{M_{s,k}−1}`, `M_{s,k}` = the
additive-path codim `(M⁽¹⁾−t⁽¹⁾)(M⁽²⁾−t⁽¹⁾)+∑_{j≥2}(t⁽ʲ⁻¹⁾−t⁽ʲ⁾)(M⁽ʲ⁺¹⁾−t⁽ʲ⁾)` (= repo `Mval`).

1. **Local comparability / units** (plumbing). Frobenius product losses, entry ideals, bounded analytic
   changes of variables and finite chart covers preserve local `L¹` integrability (Aoyagi Lemma 1).
2. **Pivot–Schur chart lemma** (algebraic plumbing). Per rank/corank chart, the unit-triangular
   Jacobian-1 reduction `Q₁ C^{(s)} Q₂ = diag(pivot, Γ)` (Aoyagi Lemma 2 / Thm 3); correct block dims.
3. **Boundary blow-up / peel lemma** (LOAD-BEARING analytic core). `Γ = zV`, Jacobian `z^{a−1}`, per-step
   integrand `≍ P_tail^{−(c'−a/2)}·P_full^{−a/2}` (this cert's exact identity), up to harmless
   constants/logs. This is the exponent-shift, correct and validated.
4. **`(S,J)` normal-form invariant** (main structural plumbing). Each within-layer rank-drop step / layer
   transition preserves `diag(b)·[E_J|D_J]·∏_{s>S}C^{(s)}` — Aoyagi's Case 1(1)/1(2)/Case 2.
5. **Jacobian / charge-update lemma** (mechanical, load-bearing for correctness). `(S,J)→(S,J+1)` and
   `S→S+1` update the exceptional exponents by the stated codim/rank-loss — the inherited-charge transfer.
6. **Charge-budget inequality** (LOAD-BEARING combinatorial core). Accumulated exceptional exponents on
   every divisor are bounded by the admissible codim budget = the `minAdm` recursion / subordination
   `a/2 ≤ ½·minAdm(M₁,…,M_L)`. This is the piece the repo already has as `minAdmRec_eq_minAdm` + the
   subordination fact verified here (`r1u_binding.py`).
7. **Monomial integrability assembly** (LOAD-BEARING analytic endpoint). Monomialized losses + Jacobians
   ⟹ `∫ ∏|u_i|^{α_i} < ∞ iff α_i > −1`; logs harmless under strict `c' < ½·minAdm`; finite charts
   assemble the global box finiteness.

**Scale:** comparable to the interior/smeared general-L tides (several-hundred-to-1000-line cast-heavy
multi-tide); the genuinely-new analytic content is pieces 3 (peel/exponent-shift, this cert) + 6
(charge budget, ≈ the banked `minAdmRec` + subordination) + 7 (monomial assembly). Pieces 1,2,4,5 are
the opaque-width `(S,J)` plumbing (the bulk, mechanical). No new research wall.

## Files
- `r1u_overturn.py`/`r1u_overturn2.py` (multiplier saturation), `r1u_criterion.py` (exact criterion
  `a≤d_Y` full-rank + 0/5440 binding-cut check), `r1u_rankdrop.py` (power loss at shared-factor rank
  drops, `(4,4,4,4)` `g^{−2}` at rank 1), `r1u_gentle.py` (no uniformly-gentle path, 1966/5440).
- Codex trail: `codex/overturn-prompt.md`, `codex/overturn-answer.md` (agree: joint needed, BOUNDED;
  lighter escape illusory; 7-piece build decomposition).

---

# ADDENDUM 3 (2026-07-07): the integrated-blow-up ASSEMBLY spec (2 pointwise routes dead)

**Dispatch:** design the per-chart INTEGRATED blow-up assembly for `sjBoundaryPeel` as a formalisable
Lean spec — (a) per-pivot-chart radial/block blow-up integrated over each chart, (b) remove the
anisotropic corank coupling to the isotropic atom, (c) assemble over the `pivotLocus_eq_iUnion` cover
(rank-deficient locus NON-null → integrate per-chart before summing). Two POINTWISE routes are proven
dead (fixed-`Q` lift: `rpow 0^neg=0` on `{P_tail=0}`; pointwise inner bound: `∫_{A0}` diverges on the
null `{det Q=0}` where the joint integrand is finite — no uniform `C`). Banked: `RouteMSJPivotChart`
(`schur_cov` + `pivotLocus_eq_iUnion` + `measurePreserving_shearSub`), the isotropic corank atom
`matBox_corank_residual_le`, and the CLOSED front-split `routeMLayerBoxIntegral_front_split`.

## VERDICT: adopt SPLIT (A) — keep the corank `Γ` EXPLICIT in `sjBoundaryPeel`. Piece 3 becomes pure
## MP+cover+schur plumbing; the atom / isotropization / Gram-determinant / null-set move to 4/5/7.
## A structural finding forces this: the honest per-chart residual is a **Gram determinant**, NOT
## `jointPeelIntegral`'s `P_full^{−a/2}` — so `jointPeelIntegral` as defined is not the reachable
## reduction target and must be redefined to the `Γ`-explicit object. Decorrelated Codex (xhigh)
## returned the SAME finding and the SAME split-(A) recommendation, independently.

## Why both pointwise routes died (one mechanism, exact)

After the front-split, `box = ∫_{A'} I(Q)`, `I(Q) := ∫_{A0∈matBox(M0,M1)} frobSq(A0·Q)^{−c'}`,
`Q = prod(tailChain M) A'` (`M1×n`). `{A0·Q=0}` has codim `M0·rank(Q)`, so `I(Q) < ∞ iff c' < M0·rank(Q)/2`
(`r1u_gram.py`: `(2,2,2,2)`, `c'=1.2`, `I(Q)` grows `19.7→61→126→243` as `det Q→0`). So on the
rank-deficient locus `I(Q)=+∞`, while the joint integrand is finite there. `{det Q=0}` is **codim-1,
NULL** in `A'` (`P(|det Q|<1e-3)=0.023→0`). Hence `box=∫_{A'}I(Q)` is finite (ignores the null set) but
**no pointwise-in-`Q` inner bound has a uniform `C`** (route 2), and the collapsed integrand hits
`rpow 0^neg=0` on the degenerate locus (route 1). The fix is to never collapse the corank pointwise —
integrate the `Γ`-block on each chart's own domain, `{det Q_b=0}` handled a.e., before summing.

## The structural finding (exact, `r1u_residual.py`/`r1u_gram.py`; Codex-corroborated)

On the `t`-pivot chart (A0's `t×t` block `A` invertible), `schur_cov` + `measurePreserving_shearSub`
(Jacobian 1) give, exactly,

    frobSq(A0·Q)  ≍  ‖A·Q̃_top‖²  +  ‖Γ·Q_b‖²,     Γ = D − C A⁻¹ B  ((M0−t)×(M1−t) corank),

where `Q_b` = the `(M1−t)` rows of `Q` at A0's NON-pivot columns (bottom rows **unsheared**: `Q̃_b=Q_b`),
and `A·Q̃_top` is the pivot part `≍ P_tail`. **The corank `Γ` enters ANISOTROPICALLY as `frobSq(Γ·Q_b)`,
not `frobSq Γ`** — so the isotropic atom `matBox_corank_residual_le` does not apply verbatim. Isotropizing
by `Γ ↦ Γ·Q_b` (needs `Q_b` full row rank `M1−t`) has Jacobian `∝ det(Q_b Q_bᵀ)^{(M0−t)/2}`, so the atom
yields the honest per-chart residual

    det(Q_b Q_bᵀ)^{−(M0−t)/2} · P_tail^{−(c'−a/2)},        a = (M0−t)(M1−t).

This Gram determinant is **pointwise ≥ `P_full^{−a/2}=‖Q‖^{−a}`** (take `M1−t=1`, `P_tail≍1`, `‖Q_b‖=ε`:
Gram `= ε^{−(M0−t)}`, `P_full^{−a/2}≍1`) — NOT a constant-factor repair. `jointPeelIntegral`'s `P_full^{−a/2}`
is a loose simplification; Aoyagi's `D_J` block is itself a determinant, matching the Gram.

## The assembly — SPLIT (A), `Γ`-explicit `sjBoundaryPeel` (formalisable Lean spec)

Reduction target (redefine): the `Γ`-EXPLICIT per-chart object
`gammaPeelIntegral κ t c' := ∫_{A'} ∫_{Γ∈matBox((M0−t)(M1−t))} (P_tailκ(Q) + frobSq(Γ·Q_bκ(Q)))^{−c'}`,
and prove `routeMLayerBoxIntegral M c' 1 ≤ ∑_{t,κ} C_{t,κ}·gammaPeelIntegral κ t c'`.

**Piece 3 (`sjBoundaryPeel`, split A) — pure plumbing, no atom, no isotropization:**
1. `pivotChartCover_lintegral_le_sum` (plumbing) — `pivotLocus_eq_iUnion` + finite subadditivity: bound the
   `A0`-integral by `∑` over `t` and pivot charts `κ`, on each chart's domain (rank-≥t, `κ`-minor invertible).
2. `schurShear_chart_lintegral` (LOAD-BEARING structural) — on chart `κ`, `measurePreserving_shearSub` +
   `schur_cov` rewrite the chart contribution with `Γ=D−CA⁻¹B` explicit (Jacobian 1), integrand
   `(P_tailκ + frobSq(Γ·Q_bκ))^{−c'}`. This is the exact block identity above.
3. `chartRadialBlock_to_gammaPeel` (LOAD-BEARING) — integrated over `A'` and the chart pivot-variables,
   bound the chart contribution by `C_κ·gammaPeelIntegral κ t c'`. INTEGRATED (never a fixed-`Q` pointwise
   inner estimate — that is the dead route).
4. `sjBoundaryPeel_explicitGamma` (plumbing) — assemble 1–3: `box ≤ ∑_{t,κ} C_{t,κ}·gammaPeelIntegral`.

**Pieces 4/5/7 (finiteness of `gammaPeelIntegral`) — the analytic core, where the atom + null-set live:**
5. `rightMul_gramJacobian` (LOAD-BEARING) — for `rank Q_b = M1−t`, the `Γ ↦ Γ·Q_b` Jacobian is
   `det(Q_b Q_bᵀ)^{(M0−t)/2}`; trivial `p=0`/`q=0` edge cases.
6. `gammaAtom_fullRank_gramResidual` (LOAD-BEARING analytic core) — for `w>0`, `rank Q_b = M1−t`, `c'>a/2`:
   `∫_Γ (w + frobSq(Γ·Q_b))^{−c'} ≤ C·det(Q_b Q_bᵀ)^{−(M0−t)/2}·w^{−(c'−a/2)}` (the Gram c.o.v. (5) +
   the isotropic atom `matBox_corank_residual_le`). This IS the exponent-shift, now anisotropic.
7. `gammaPeel_le_gramPeel_ae` (LOAD-BEARING) — `{det(Q_b Q_bᵀ)=0}` and `{P_tail=0}` are NULL per chart
   (`lintegral_congr_ae`), so (6) applies a.e.; then the resulting Gram-residual integral is the
   `(S,J)` recursion object (ADDENDUM 2 build pieces 5–7 / the charge-budget + monomial assembly).

## Load-bearing checks + the one risk

- Both pointwise routes' death and the null `{det Q=0}` locus: `r1u_gram.py` (exact + MC).
- The Gram-vs-`P_full` residual mismatch: `r1u_residual.py` (the residual is a power of `Q_b`, not `‖Q‖`).
- **The one risk (Codex, verified `r1u_qb_rank.py`):** the Gram atom (piece 6) needs `rank Q_b = M1−t`
  ACHIEVABLE, i.e. `M1−t ≤ min(M2,…,M_L)`. This FAILS on **750/5440** chains (deeper-width bottleneck,
  e.g. `(2,4,1)` `t=2`: `M1−t=2 > min(deeper)=1`) — there `Q_b` is FORCED rank-deficient and the chart
  must RECURSE (its rank drop is a deeper boundary's = the `(S,J)` coupling, consistent with ADDENDUM 2).
  **Split (A) quarantines this to 4/5/7: piece 3 (`Γ`-explicit) is UNAFFECTED** (no atom). Cheapest
  de-risk before the atom pieces: for each `(t,κ)` with `M1−t ≤ min(deeper)`, exhibit one box tail-config
  with `rank Q_bκ = M1−t` and `P_tailκ>0` (⟹ the Gram/`P_tail` polynomials ≢ 0 ⟹ zero loci null); for the
  bottlenecked `(t,κ)`, route through the recursion instead of the atom.

## Closing (firmest / most-likely-to-break / next step)

- **Firmest:** the honest per-chart residual is the Gram determinant `det(Q_b Q_bᵀ)^{−(M0−t)/2}·P_tail^{−(c'−a/2)}`
  (exact block identity + Gram c.o.v.), NOT `P_full^{−a/2}`; both pointwise routes die on the null
  degenerate locus; split (A) (`Γ`-explicit piece 3) is the formalisable path, Codex-corroborated.
- **Most likely to break:** the bottlenecked charts (750/5440) where `Q_b` is forced rank-deficient — the
  atom is unavailable and the chart must recurse; getting the recursion/atom dispatch right in 4/5/7 is
  the remaining analytic work (bounded, = the `(S,J)` mountain, ADDENDUM 2).
- **Next construction:** implement piece 3 split (A) (pure MP+cover+schur, all banked) → `box ≤ ∑
  gammaPeelIntegral` sorry-free; then the atom pieces 5–7 with the recursion/atom dispatch on the
  bottleneck. Redefine `jointPeelIntegral → gammaPeelIntegral` (the `Γ`-explicit / Gram target).

## Files (this addendum)
- `r1u_residual.py` (per-chart residual is a power of `Q_b`, not `‖Q‖`), `r1u_gram.py` (route-2 death:
  inner diverges as `det Q→0`; `{det Q=0}` null), `r1u_qb_rank.py` (750/5440 bottlenecked charts).
- Codex trail: `codex/assembly-prompt.md`, `codex/assembly-answer.md` (agree Gram residual; split (A);
  7-lemma sequence; risk = a.e. full-row-rank of the actual tail product).

---

# ADDENDUM 4 (2026-07-07): CORRECTED per-chart Γ-bound — the TRUE cross-coupled integrand

**Dispatch:** ADDENDUM 3's split-(A) piece-3 sub-lemma 2 was WRONG. `schur_cov` gives Schur block
algebra + a unit-Jacobian reparametrisation but is NOT a Frobenius isometry, so the exact post-shear
integrand carries a CROSS-COUPLING term `C·Q̃_p + Γ·Q_b` — not the clean `(P_tail + ‖Γ·Q_b‖²)`.
Re-design the per-chart Γ-bound with the TRUE integrand.

## VERDICT: the fix is SOUND and BOUNDED (Codex xhigh corroborated). The TRUE integrand is handled by
## a **full-space anisotropic-shifted corank atom**: box→full-space (translation-invariance kills the
## shift `C·Q̃_p`) + the Gram-Jacobian of `Γ↦Γ·Q_b` (the anisotropy). Split (A) STILL holds with the
## corrected — cross-coupled — `gammaPeelIntegral` integrand; piece 3 stays plumbing ONLY if it does
## NOT simplify the integrand. Two precisions folded in below.

## The corrected exact block identity (verified to 1e-10, scalar & matrix Γ, `r1u_crosscoupling.py`)

After the schur reparametrisation `D ↦ Γ = D − C A⁻¹ B` (Jacobian 1, `measurePreserving_shearSub`) on
the `t`-pivot chart `A0=[[A,B],[C,D]]` (`A` `t×t` invertible),

    frobSq(A0·Q) = ‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²,     Q̃_p = Q_p + A⁻¹B·Q_b,

`Q = prod(tailChain M) A'` (`M1×n`), `Q_p`/`Q_b` = pivot/non-pivot rows, `Γ` = corank `(M0−t)×(M1−t)`.
**The corank `Γ` is CROSS-COUPLED with `C·Q̃_p`** (a free integration variable `C` times the sheared
tail top). ADDENDUM 3's `(P_tail + ‖Γ·Q_b‖²)` dropped this — the error.

## The fix — the full-space anisotropic-shifted corank atom (verified to <1% MC, `r1u_aniso_atom.py`)

Bound the box Γ-integral by the FULL-SPACE integral (integrand ≥0, `matBox ⊆ ℝ^{pq}`); the full-space
integral is translation-invariant, so for `R:q×n` FULL ROW RANK, `S:p×n`, `w>0`, `c'>pq/2`
(`p=M0−t, q=M1−t, a=pq`):

    ∫_{Γ∈ℝ^{p×q}} (w + ‖Γ·R + S‖²)^{−c'} dΓ
       = Cinf(pq,c') · det(R Rᵀ)^{−p/2} · (w + ‖S·(I−P_R)‖²)^{−(c'−pq/2)},    P_R = Rᵀ(RRᵀ)⁻¹R.

With `R=Q_b`, `S=C·Q̃_p`, `w=‖A·Q̃_p‖²`: the SHIFT `S` is absorbed by translation-invariance (only its
`row(Q_b)`-component is removed; the ⊥ part `‖C·Q̃_p·(I−P_{Q_b})‖²` SURVIVES into the core — Codex's
precision, kept), the ANISOTROPY `Q_b` by the Gram det. Per-chart residual:

    det(Q_b Q_bᵀ)^{−(M0−t)/2} · (‖A·Q̃_p‖² + ‖C·Q̃_p·(I−P_{Q_b})‖²)^{−(c'−a/2)}.

This SUPERSEDES the banked isotropic box atom `matBox_corank_residual_le` (its `R=I, S=0, box` special
case). The exponent-shift `c'↦c'−a/2` is preserved (Aoyagi's step); the coupling is now the Gram det.

## The corrected split (Codex-confirmed home for each piece)

- **Piece 3 `sjBoundaryPeel` (PLUMBING — but only if the integrand is NOT simplified):**
  `box = ∑_{t,κ} C·gammaPeelIntegral κ t c'` via `pivotChartCover_lintegral_le_sum` (banked cover) +
  the schur MP reparametrisation (`measurePreserving_shearSub` + the exact block identity above).
  **`gammaPeelIntegral` MUST carry the TRUE integrand** `(‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²)^{−c'}`
  (equivalently the named `(w + ‖Γ·R + S‖²)^{−c'}`). If piece 3 replaces it by `‖Γ·Q_b‖²` or an
  unshifted residual, the ADDENDUM-3 error returns (Codex).
- **`gammaPeelIntegral`-finiteness (`sjJointResolution`, the ANALYTIC core):** box→full-space + the
  anisotropic-shifted atom + the `Q_b`-rank branch + the recursion.

## Corrected ordered lemmas (dependency order; Codex-aligned)

5. `gammaBox_le_fullSpace` (plumbing, essential) — `∫_{Γ∈chartDomain}(w+‖Γ·R+S‖²)^{−c'} ≤
   ∫_{Γ∈ℝ^{pq}}(…)`. NO rank assumption; monotone box→full-space. Order matters: enlarge FIRST, then
   translation-invariance.
6. `fullSpace_anisotropic_shifted_gamma_atom` (LOAD-BEARING analytic core) — the full-space atom above,
   for `R` full row rank, `c'>pq/2`, `core>0`. Depends on the Gram Jacobian of `Γ↦Γ·R` + full-space
   translation. Generalizes `matBox_corank_residual_le` (`R=I,S=0,box`).
7. `gammaPeelIntegral_rankBranch_finite` (LOAD-BEARING assembly) — apply 5,6 on `{det(Q_b Q_bᵀ)≠0}`;
   handle `{det(Q_b Q_bᵀ)=0}` EXPLICITLY (null-by-nonzero-polynomial-certificate OR the recursive
   deeper-boundary branch). **Do NOT globally assert nullity** — in bottleneck architectures the
   determinant is identically zero (Codex). Also prove the core-positivity a.e. (next precision).

## Two precisions to fold in (Codex, load-bearing)

1. **Core positivity needs `Q̃_p ≠ 0` a.e., not just `A` invertible.** `w = ‖A·Q̃_p‖²`, `A` invertible ⟹
   `w>0 ⟺ Q̃_p ≠ 0`; `Q̃_p = Q_p + A⁻¹B·Q_b` is a polynomial in the chart vars, so `{Q̃_p=0}` is null
   PROVIDED `Q̃_p ≢ 0` (needs a nonzero witness per chart). Numerically `w>0` on 2000/2000 configs
   (`r1u_core_pos.py`), but the a.e. proof is a separate nonzero-polynomial argument.
2. **`{det(Q_b Q_bᵀ)=0}` is NOT globally null.** It is identically zero exactly on the bottleneck charts
   (`M1−t > min(M2,…,M_L)`, 750/5440 chains, `r1u_qb_rank.py`) — there the atom is unavailable and the
   chart MUST route to the recursive rank-drop branch (= the `(S,J)` coupling, ADDENDUM 2). On non-
   bottleneck charts, `{det=0}` is null by a nonzero-polynomial certificate.

## Risk + cheapest check (Codex)

- **Biggest risk:** the full-row-rank / a.e. claim for the ACTUAL tail product `Q_b` (not an abstract
  matrix). **Cheapest check:** for each chart `(t,κ)`, exhibit one concrete box tail-config with
  `rank Q_b = M1−t` AND `Q̃_p ≠ 0` (⟹ the det + `Q̃_p` polynomials ≢ 0 ⟹ their zero loci null); if no
  such witness (bottleneck), that chart is not an atom chart → recursive rank-drop branch.

## Closing (firmest / most-likely-to-break / next step)

- **Firmest:** the TRUE post-shear integrand `‖A·Q̃_p‖²+‖C·Q̃_p+Γ·Q_b‖²` (exact); the full-space
  anisotropic-shifted atom handles cross-coupling (translation-inv) + anisotropy (Gram det) with the
  `c'↦c'−a/2` shift; split (A) holds with the cross-coupled `gammaPeelIntegral`; Codex-corroborated.
- **Most likely to break:** (i) the `Q̃_p≠0` a.e. and `det(Q_bQ_bᵀ)≢0` non-bottleneck certificates
  (per-chart nonzero-polynomial witnesses); (ii) the bottleneck-chart recursive branch dispatch.
- **Next construction:** implement piece 3 (cover + schur MP reparam, banked) with `gammaPeelIntegral`
  = the TRUE cross-coupled integrand → `box ≤ ∑ gammaPeelIntegral` sorry-free; then build lemma 6
  (`fullSpace_anisotropic_shifted_gamma_atom`) as the corrected atom (generalize
  `matBox_corank_residual_le`), then lemma 7 with the bottleneck/recursion dispatch.

## Files (this addendum)
- `r1u_crosscoupling.py` (TRUE integrand + Γ-translation orthogonal split, exact to 1e-10, scalar &
  matrix Γ), `r1u_aniso_atom.py` (full-space anisotropic-shifted atom vs quadrature, <1%),
  `r1u_core_pos.py` (core `w>0` a.e.), `r1u_qb_rank.py` (750/5440 bottleneck charts → recursion).
- Codex trail: `codex/recross-prompt.md`, `codex/recross-answer.md` (SOUND/BOUNDED; the two precisions;
  corrected lemmas 5–7; risk = actual-`Q_b` full-row-rank/a.e.).

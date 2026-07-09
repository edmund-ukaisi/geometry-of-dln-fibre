# genm-addlongscope — SIZE/RISK scoping of the `addlongest` build (#72, the sole remaining wall)

**Seat:** scout (reconnaissance), RECON + DESIGN only — no Lean built, no proof started.
**Charge:** honest size/risk read on the R1-UPPER sub-generic wall (`sjJointResolution`,
`RouteMSJResolution.lean:797/803`) to inform the operator's build-vs-cite call.
**Method:** read the paper's `addlongest` (Thm ~688) + proof, the wall cert
(`genm-r1subgenwall/cert.md`), the escalation trail (discuss-at-close #52→#72), the Lean target, and a
verified Mathlib-v4.29 inventory; decorrelated `local-codex-consult` (high, neutral prompt). No canonical edits.

---

## HEADLINE (controller-facing)

- **Size tier: (c) MINI-EXPEDITION — multi-module, multi-week.** Best point estimate for the general lemma
  **~20–35 person-weeks**; ~8–18 if scoped to the fixed binding case with hand-enumerated charts; **80–200+
  if it forces reusable AG/principalisation infrastructure.** This matches my independent read AND the
  decorrelated Codex (same tier, same range). It is emphatically **not** "a few lemmas."
- **Tractability in Lean at v4.29 (measure-theoretic coordinate-chart route, no AG primitive):** ~**35%**
  for the general lemma; ~**55–65%** for the single `(3,3,3,4) t=1` case via a bespoke non-reusable chart
  proof. ~**60%** it forces a principalisation-equivalent detour. (Codex's numbers; mine agree within a few pts.)
- **★ The load-bearing distinction (surface this first):** the paper's `addlongest` (Thm ~688) is **NOT**
  the object the wall needs. The paper's theorem is a one-line **homological-algebra codimension equality**
  (Ext-vanishing via the injective-projective module `M_{0N}`) — trivial-to-small in Lean IF you have quiver
  Ext machinery, and **off the critical path** because the RLCT leg never builds the quiver-Ext layer. What
  the wall needs is the theorem's **analytic sibling**: joint principalisation of the matrix **product's**
  rank-drop determinantal locus so an integral over a shifted DLN chain is finite. The cert *labels* this
  "`addlongest` normal-slice iso," but it is a genuinely different, genuinely harder object. **The operator
  should not read "the paper proves addlongest in one line" as "the build is small."**
- **Top 3 risks:** (1) **hidden principalisation burden** — a coupled product-incidence locus, not two
  independent singular factors (the empirical flip-flop below is this risk realized ~4×); (2) **Lean analytic
  infrastructure cost** (chart CoV + Jacobians + finite covers + a.e. bookkeeping in real matrix coordinates);
  (3) **combinatorial/chart explosion** uniform in the widths `Mᵢ` and pivot/stratum choices.
- **Weaker-sufficient-form shortcut: WEAK.** We need only finiteness for `c' < ½·minAdm` (an upper bound,
  not the exact-value iso). This removes the value-reconstruction half but **not** the hard core: the
  borderline coupling exponent `a/2` is **c'-independent**, so the slack gained from `c' < ½·minAdm` lives
  entirely in the *wrong* factor. Crude envelopes (Fubini-separate / Hölder / determinant lower bound /
  free-matrix domination) are all killed by the zero-slack borderline. A weaker "coarse joint sublevel-volume
  estimate" may exist, but still needs the same local monomialisation data. Net: a modest saving, not a
  different tier.

**One-line recommendation to the operator:** on the mathematics the wall is real (five decorrelated lines +
this scope + Codex); on the *formalisation* it is a multi-week mini-expedition with a majority chance of
forcing principalisation-equivalent machinery Mathlib lacks. **(B) CITE is footprint-neutral** (routes
through the already-carried `cited_aoyagi_dln`) and is the honest default unless the operator wants a
dedicated multi-week sub-expedition whose scoping has itself proven unstable.

---

## 1. The exact target

### 1a. What `addlongest`-as-named must provide (the analytic sibling — the wall)

The sole R1-UPPER sorry is `sjJointResolution` (`RouteMSJResolution.lean:797`). Would-be Lean signature
(informal, matching the live statement):

```
theorem sjJointResolution (M : Fin (L+1+1+1) → ℕ)
    (hIH : ∀ M' : Fin (L+1+1) → ℕ, RouteMBoxThresholdFinite M')   -- strong IH: all shorter chains finite
    (t : ℕ) (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1))
    (ht : 1 ≤ t) (ht2 : t ≤ min (M 0) (M 1)) (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    gammaPeelIntegral M t ρ κ (c' : ℝ) < ⊤
```

Unfolding the analytic content (from the docstring + the cert §2.0): on the `(t,ρ,κ)` pivot chart the `t×t`
pivot minor of `A₀` is a unit; the banked block identity + the MP shear `D ↦ Γ = D − CA⁻¹B` rewrite the
integrand as `(‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²)^{−c'}` with `Γ` free `(M₀−t)×(M₁−t)` and
`Q_b` = the `(M₁−t)` non-pivot rows of the **matrix product** `P = A₁·(A₂···A_{N−1})`. Integrating out `Γ`
(Gram CoV `Γ ↦ Γ·Q_b`) leaves the OUTER integral over the deeper matrices:

$$
\int_{A'} \det(Q_b Q_b^{\mathsf T})^{-(M_0-t)/2}\;\bigl[\text{reduced-chain loss}\bigr]^{-(c'-a/2)}\, dA'
\;<\;\infty,\qquad a=(M_0-t)(M_1-t).
$$

The `det(Q_b Q_bᵀ)^{−(M₀−t)/2}` factor blows up on `{rank P drops}`, a proper determinantal subvariety of
the deeper matrices. The content `addlongest` must supply: a **measure-preserving / bounded-Jacobian
reparametrisation** of `{rank(A₁···A_{N−1}) ≤ q}` that turns this into a **shifted-chain box integral**
`box(M₁−q, M₂−q, …, M_N−q)` covered by the IH — i.e. **jointly principalising the product's rank-drop
determinantal ideal with the reduced-chain integrand** so both borderline factors become monomials whose
exponents sum to exactly the `minAdm` budget. The shifted chain is provably **not** any `redChain t M`
(its deeper widths are shifted by `q`; `redChain` keeps `M₂,…,M_N` unshifted).

### 1b. What the paper's `addlongest` (Thm ~688) actually states — and why it is a different, easier object

Paper Thm (`main.tex:686–704`): *the normal slices of $\mathcal O_{\mathrm{rk}=\underline r}$ and
$\mathcal O_{\mathrm{rk}=\underline r+p}$ (adding `p` to every dimension component) are isomorphic; in
particular the codimensions are equal.* Proof (one paragraph): by Voigt's lemma the normal slice is
`Ext(M,M)`; adding `p` copies of the longest-interval indecomposable `M_{0N}` gives
`Ext(M⊕pM_{0N}, M⊕pM_{0N}) = Ext(M,M)` because `M_{0N}` is **both injective and projective**, so the three
cross terms `Ext(M,M_{0N})`, `Ext(M_{0N},M)`, `Ext(M_{0N},M_{0N})` all vanish (`main.tex:281–290, 703`).

This is a purely **algebraic** statement about orbit **codimensions**, proved by Ext-vanishing. It is used in
the paper only to prove `Lemma rank_0` (`main.tex:816`), the combinatorial reduction `codim Σ^r_{d} =
codim Σ^0_{d−r}`. In this project the **combinatorics is already settled** (`minAdm` layer-peel, r1rankcharge,
triple-confirmed). So:

- If one *did* want the paper's `addlongest` verbatim in Lean, and *had* a quiver-representation Ext layer,
  it would be **small** (an Ext-vanishing lemma for one inj-proj module + a direct-sum bilinearity of Ext).
  But that layer does not exist in `DLNFibre` and is not on the RLCT critical path.
- The wall does **not** consume the codimension equality (that's `minAdm`, done). It consumes the **RLCT /
  integral** transfer — the measure-level analogue of "the transverse singularity is unchanged." That is the
  hard object, and it is what §1a states.

**Precision flag (CLAUDE.md "name = exactly what's proven"):** calling the wall "`addlongest`" imports the
paper theorem's one-line-proof connotation onto an object that is a res-of-sing-adjacent analytic monster. A
clearer name for the build target: **`productRankNormalSliceIntegral`** (or "the shifted-chain integrability
transfer"). Recommend the operator's decision be framed on the analytic object, not the paper's label.

---

## 2. Mathlib v4.29 inventory (verified against the pinned `mathlib` rev `v4.29.0`)

**PRESENT (relevant, usable):**
- `Matrix.rank` + rank API (`LinearAlgebra/Matrix/Rank.lean`); `Matrix/SchurComplement.lean`;
  `Matrix/Determinant/*` (the chart algebra + Schur split the repo already rides).
- `LinearAlgebra/ExteriorPower` — gives `∧^q`, hence a route to `det(Q_b Q_bᵀ) = ‖∧^q Q_b‖²`.
- **Integral change-of-variables:** `MeasureTheory/Function/Jacobian.lean`
  (`integral_image_eq_integral_abs_det_fderiv_smul` and the `lintegral` variants) — the analytic workhorse
  the repo's banked corank atoms (`matBox_corank_*`) already use. This is the tool a coordinate-chart route
  would lean on.
- `RingTheory/Grassmannian.lean` (functor-of-points; **minimal** — no incidence-variety / rank-stratum
  geometry), `LinearAlgebra/Basis/Flag.lean` (order-theoretic flags, **not** flag varieties).

**ABSENT (the gap the build would have to bridge — none of these exist in v4.29):**
- **Algebraic-geometry blow-up** (`Bl_Z X`). The only "Resolution.lean" files are *homological* (projective/
  injective resolutions in category theory), not resolution of singularities.
- **Resolution of singularities / embedded resolution / principalisation of an ideal.** None.
- **Normal-crossing divisors** as an object; **monomialisation** of a map; **toric** geometry. None.
- **Determinantal ideals** as named objects (`I_q(A)`), their primary decomposition, codimension
  (Eagon–Northcott), or CoRank stratification of a matrix variety. None.
- **Plücker normal form** of a product's maximal-minor ideal. None.

**Net:** the *analytic* primitives (CoV, Jacobian, exterior power, rank) exist; the *AG* primitives that a
res-of-sing proof would want (blow-up, principalisation, determinantal-ideal geometry, normal crossings) are
**entirely missing**. A from-scratch build must therefore either (a) route around AG entirely with explicit
coordinate charts + `Jacobian.lean` + monomial integrability (the repo's declared strategy), or (b) build a
slice of AG principalisation as new reusable Mathlib-grade machinery (the 80–200 person-week branch).

---

## 3. Proof strategy — the buildable route, hardest sub-piece, recursion risk

**The paper's proof does NOT transfer.** The paper closes the codimension equality by Ext-vanishing; it never
writes the analytic integral. So there is no "port the paper's proof" shortcut for the wall. The buildable
routes are the repo's own:

**Route (a) — explicit coordinate-chart R-BLOWUP (the repo's declared strategy, #53/#60/r1flip).** Cover
`{rank Q_b = q}` by pivot charts of the *product*, Schur-clear each with a det-1 unit, radial-blow-up the
degenerate strata via the banked `corankStep` atom, reach a monomial × unit endpoint, apply
`monomialIntegrand_integrable_of_lt`. This uses only coordinate/smooth centers and `Jacobian.lean` — no AG
primitive. It is the route the "(A) BUILD, bounded" verdicts (#53, #60) rest on.

**The hardest sub-piece (and where the wall lives):** turning the anisotropic coupled block
`‖C·Q̃_p + Γ·Q_b‖²` into the isotropic `‖Δ‖² + W` that the banked atoms require. The cert §2.4 and #59
(r1carrier) argue this reduction *is* the embedded principalisation of the Cauchy–Binet/Plücker maximal-minor
ideal of the **product** `A₁·A₂···`. Two concrete obstructions to Route (a) closing:

1. **Zero-slack borderline (cert §2.2, this-thread-authoritative).** At `(3,3,3,4) t=1`: coupling exponent
   `a/2 = 1` sits **exactly** at its free-matrix integrability threshold `(n−p+1)/2 = 1`, **while** the
   post-peel residual exponent `3/2` **exactly** saturates `½·minAdm(1,3,4) = 3/2`. Both borderline
   simultaneously, sharing the deeper variables ⟹ Fubini-out gives a log divergence ⟹ the two must be
   principalised **jointly**. Verified two ways (SVD Jacobian + symbolic transverse Hessian) and by
   decorrelated Codex.
2. **Non-coordinate center (cert via #59 r1carrier).** `det(Q_bQ_bᵀ)` is a 450-term irreducible (gcd 1, not
   monomial×unit) with a **dense-torus rank-drop witness `[[1,1,2,1],[1,1,2,1]]`** invisible to every
   coordinate blow-up center. Codex (this consult) confirms: coordinate blow-ups don't touch dense-torus
   incidence; you can translate a center into coordinate form on a patch, "but that is already a bespoke
   principalisation, just written analytically." Product rank-drop is a coupled incidence condition
   (`im(suffix) ∩ ker(prefix) ≠ 0`), not a factor-by-factor rank drop, so "blow up one factor at a time"
   does not cleanly decouple it.

**Recursion risk (does the build need OTHER missing AG?):** YES, materially. The honest empirical signal is
the **escalation flip-flop**: the R1-UPPER verdict has oscillated *bounded → research-grade → bounded →
WALL* four times in ~2 days (#52/#53 bounded → #55 bounded → #58 build-viable → #58-sharpened
carrier-insufficiency → #59 research-grade-CITE → #60 bounded → #65 "close" → #70/#71/#72 WALL-CONFIRMED).
Each "bounded" verdict was overturned when a build attempt hit a required infrastructure the carrier could
not express (r1predicate separable-form; sjbuild4 SJDecoration-can't-peel; r1carrier non-coordinate center).
The *pattern* — a coordinate carrier repeatedly discovering it needs a non-coordinate / joint object — is
exactly the recursion risk: **a build is likely to discover, N tides in, that it is back in
principalisation territory.** This has happened ~4 times; it is the dominant risk, not a tail risk.

**Tension to record (not for me to adjudicate — #72 is the authoritative latest verdict):** r1flip (#60)
argued Route (a) escapes because the rank-drop witness is a *positive-loss* point, so Aoyagi's deepest-point
resolution never touches `{rank Q_b ≤ 1}`. The cert §2.4 (#72, later, dedicated dissolve-or-confirm +
decorrelated Codex) re-confirmed the wall by arguing the det coupling reappears on the **full-measure generic
stratum** once you match `Γ·Q_b` to the isotropic brick via the Gram CoV. These are two competent analyses
reaching opposite scoping conclusions; the *latest* and most-scrutinised (#72) is WALL. The unresolved
tension is itself the scoping datum: the boundary between "bounded coordinate build" and "needs joint
principalisation" is genuinely hard to locate, and has been mislocated repeatedly.

---

## 4. Size / risk estimate (the decision-driver)

**Effort tier:** **(c) mini-expedition.** Point estimate **~20–35 person-weeks** for the general
`sjJointResolution`. Decomposition (mine, Codex-corroborated):
- Fixed binding case `(3,3,3,4) t=1`, hand-enumerated charts, non-reusable: **~8–18 person-weeks**.
- General widths / general `L`, bespoke explicit charts: **~20–50 person-weeks**.
- If it forces reusable principalisation/determinantal-ideal infrastructure: **~80–200+ person-weeks**
  (a Mathlib-contribution-scale effort; likely its own multi-month project).

**In this repo's "tide" unit** (a focused formaliser dispatch, roughly a few days of one agent): the general
build is a **~12–25+ tide** effort *if* Route (a) closes without new AG — but the ~60% recursion risk means
the realistic expectation includes a branch into the 80–200 person-week tier. The controller's own honest ETA
(#54, #58-RESOLVED) already reads this as "~12–20 tides, multi-week mountain" on the optimistic (Route-a-
closes) assumption; the wall cert (#72) removes that optimistic assumption.

**Probability it is tractable in Lean at v4.29 at all:**
- Via the measure-theoretic coordinate-chart route (no AG primitive): **~35%** general / **~55–65%** for the
  single binding case (bespoke, non-reusable).
- Forces a large Mathlib-AG detour (principalisation as reusable machinery): **~60%**.
- An unexpectedly simple analytic domination works: **~5%**.

**Top 3 risks (ranked):**
1. **Hidden principalisation burden.** The coupled product-incidence/determinantal locus is the real object;
   the zero-slack borderline + non-coordinate center say a coordinate carrier is insufficient. This is the
   risk the four prior flip-flops each realized.
2. **Lean analytic infrastructure cost.** Chart CoV, Jacobian determinants over real matrix coordinates,
   finite covers, local integrability, a.e. restrictions, dependent-width casts — expensive and grinding at
   v4.29 even when the math is fixed.
3. **Combinatorial / chart explosion.** Pivot branches × affine-minor choices × rank strata × width
   inequalities, stated uniformly in `Mᵢ` and `L`. (The repo already sees "750/5440 charts force `Q_b`
   rank-deficient" — the sub-generic charts are the majority, not an edge.)

---

## 5. Alternatives within (A): is there a weaker sufficient form?

We need only **finiteness for `c' < ½·minAdm`** (a one-sided upper bound), not the exact-value normal-slice
iso. This *does* buy something, but **not a tier change**:

- **What it saves:** the reverse inequality / exact-value reconstruction. A one-sided domination
  `∫ det(Q_bQ_bᵀ)^{−a/2}·residual ≤ (bounded-Jacobian)·(shifted-chain box)` suffices; you never need to prove
  the shifted-chain integral *equals* anything. Removes the value half.
- **Why it does NOT dissolve the core:** the coupling exponent `a/2` is **independent of `c'`** (it comes from
  the Γ-block dimension, not the threshold). So the slack you gain by taking `c' < ½·minAdm` strictly lives
  **entirely in the residual factor**; the `det(Q_bQ_bᵀ)^{−a/2}` factor stays **exactly borderline for every
  admissible `c'`**. Consequently the standard cheap moves all fail (confirmed by both the cert and the
  decorrelated Codex):
  - Fubini-separate `Γ`/`W`: log divergence at the coupling's own threshold.
  - Hölder split: any `p > 1` pushes the critical determinant exponent past threshold.
  - Crude determinant lower bound: loses multiplicity ⟹ majorant diverges.
  - Free-matrix domination: too pessimistic exactly at the borderline.
- **The residual weaker form that might exist:** a **coarse joint sublevel-volume estimate** (bound the joint
  measure of `{det(Q_bQ_bᵀ)^{−a/2}·residual > λ}` directly) — weaker than exact RLCT, but it still needs the
  same local monomialisation/principalisation data. So it is *weaker than exact RLCT, not weaker than
  joint-resolution-style analysis*. Modest saving (maybe shaves the value-reconstruction fraction), same tier.

**Verdict:** the "we only need an upper bound" shortcut is **real but weak** — it does not convert the
mini-expedition into a module. The zero-slack borderline is precisely the structural reason no crude
sufficient lemma clears the bar.

---

## Option (B) footprint note (for the operator's framing)

The CITE fallback is **footprint-neutral in the strict `#print axioms` sense**: the sub-generic upper bound
routes through the **already-carried** `cited_aoyagi_dln` (`RlctPayoff.lean:297`, the `rlct = ½·codim`
equality the payoff already depends on) — combined with the settled combinatorics `codim = minAdm`, that
yields `rlct = ½·minAdm` hence box-finiteness for `c' < ½·minAdm` directly. So (B) adds **no new named
axiom** (correcting UPDATE-690's "add a 2nd interface"). What (B) *does* change is the **character** of the
deliverable: the sub-generic-stratum geometry becomes **cited from Aoyagi**, not built from scratch — a
departure from the "from-scratch, cite-only-S2" ambition for exactly that stratum. Both readings should be
put to the operator: strict footprint = neutral; built-vs-cited character = a real change for the sub-generic
geometry. (The L=2 headline is unaffected either way — no sub-generic strata at L=2.)

---

## Reflection (scout close)

- **Most likely to advance the expedition:** the **precision reframing** in §1b — separating the paper's
  one-line algebraic `addlongest` from the analytic monster the wall needs. It de-risks a mis-scoped operator
  decision (reading the paper's easy proof as the build's difficulty) and points the eventual named interface
  (whether built or cited) at the correct object, `productRankNormalSliceIntegral`.
- **Most likely to break:** any "bounded coordinate-chart build" plan. The flip-flop history is four
  data points that a coordinate carrier keeps discovering it needs a non-coordinate/joint object; the
  zero-slack borderline + dense-torus non-coordinate center are the structural reasons. If a build is
  commissioned, the honest expectation is a ~60% branch into principalisation-infrastructure territory.
- **Next computation that would clarify:** the decisive constructive probe named in the cert §"next step" —
  attempt the concrete `(3,3,3,4) q∈{1,2}` **joint** change of variables realising
  `det(Q_bQ_bᵀ)^{−a/2}·residual` as the shifted-chain box on ONE chart, by hand (pen-and-paper, exact
  algebra). If it closes with an explicit coordinate CoV, Route (a) is alive and the tier drops toward
  8–18 person-weeks; if it forces a non-coordinate center (as r1carrier's witness predicts), the
  80–200 tier is confirmed and CITE is the honest call. This is a bounded pen-and-paper adjudication, not a
  build — the correct next step before committing multi-week formaliser effort.

**Decorrelated Codex (high, neutral prompt, conclusion withheld):** independently returned the same tier
(c, 20–35 pw), the same ~35%/60%/5% tractability split, the same weaker-form verdict (crude envelopes killed
by zero slack; only a coarse joint estimate survives, still needing monomialisation), the same top-3 risks,
and leaned **CITE** ("build from scratch only if the goal is a fixed small case or the project explicitly
wants a new Lean development of determinantal/principalisation-style analytic estimates"). Full artefact:
`/tmp/codex_addlong_out.md` (transcribe into `codex/` if this thread is banked).

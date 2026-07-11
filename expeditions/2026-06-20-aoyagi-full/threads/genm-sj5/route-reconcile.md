# Route reconcile — #123 (Cauchy–Binet, Level-A) vs the descent (coupling irreducible): DIFFERENT mechanisms; Route B does NOT close cheaply

**Seat:** pen-and-paper (route adjudication — the decorrelated STABILIZATION the controller required after
3 flip-flops). **Date:** 2026-07-11. **NO Lean.** **Charge:** do #123 (Cauchy–Binet m-column majorant →
square Wishart, Level-A) and the descent-buildplan (coupling irreducible, plain-IH insufficient) CONTRADICT
or address DIFFERENT routes? Does the cheaper Route B (front-first, #123) genuinely close the Level-A hole,
or relocate the hard part? Adversarial, burden on Route B.

**Exact algebra (mine):** `/tmp/prodD/reconcile.py` (the front-first spectral corner; the tube). **Consumed:**
`cover-derisk.md` (#123), `descent-buildplan.md`, `corank2-cert.md §2/§4`, `covdesign §CONCESSION`,
`prodD-general.md` (#127). **Decorrelated:** own xhigh `local-codex-consult` (conclusion withheld, told to
HUNT the divergence, burden on Route B): `codex/reconcile-{prompt,answer}.md`. **Codex CORRECTED my
optimism** — I converge with it on the stable verdict, and it matches `corank2-cert §4` (the symmetric
compound route dies) term-for-term.

---

## VERDICT (STABLE, decorrelated): the two certs address DIFFERENT mechanisms (no contradiction). Route B does NOT close cheaply — the "disjoint-A₂ / independent-Wishart" step is FALSE. Route A (decorated descent) stays the robust route; a corrected Route B relocates the mountain into a joint flag-tube estimate (established-math, corank2-cert §2, but NEW Lean infra — NOT the Cauchy–Binet shortcut).

The controller's decision (commission the DECORATED (S,J) descent) STANDS. The formaliser's cheaper Route B
(front-first `g(Q)` → #123 Cauchy–Binet → square Wishart + `hIH` core) is INVALID as advertised: `A₂` is
globally shared, so the det-Gram and the reduced core do NOT factor over disjoint variables. This is a
stable adjudication (my analysis + a decorrelated Codex + `corank2-cert §4` all agree), and it corrects the
optimistic leaning I was drifting toward (that the free-front-column corner makes Route B close cheaply).

---

## 1. #123 vs the descent — DIFFERENT mechanisms, no contradiction (Q1)

- **#123 (Cauchy–Binet → square Wishart)** bounds the det-Gram WEIGHT ALONE: `∫det(Q_bQ_bᵀ)^{−a/2} < ⊤` up
  to `min(tail)−b+1`, reducing a SINGLE corank-Gram weight to a square-`(b,m,m)` Wishart base. Level-A, a
  TOOL for the tube — it does NOT address the coupled freed-Γ residual.
- **The descent (Route A, Γ-first)** emits `det(Q_bQ_bᵀ)^{−a/2}·w^{−(c'−ab/2)}` (both share `A₂`), coupled
  and zero-slack-Hölder-blocked → the decorated ledger.
- **Route B (front-first)** never emits those factors: orthogonal rotation of the `A₀`-box gives
  `g(Q) ≍ ∫_{box}(s₁²‖z₁‖²+s₂²‖z₂‖²+s₃²‖z₃‖²)^{−c'}dz` (`z_i∈ℝ³` FREE front columns) `≍ s₃^{−η}` (codim-1) or
  `s₂^{−3}s₃^{−η}` (codim-2), `η=2c'−6`. The front corner factors over the free `z_i`; the deep enters only
  as the `s_j` weights (the tube).

So they address different mechanisms. **They contradict only if Route B additionally claims front-first
integration makes the remaining DEEP variables independent — and it does NOT** (Codex Q1, verbatim). #123
and the descent are consistent: #123 is a weight tool, the descent is Route A's coupling; Route B is a third
decomposition whose deep tube is the open piece.

---

## 2. Route B does NOT close cheaply — the disjoint-A₂ / independent-Wishart step is FALSE (Q2)

**My earlier optimism (that the free-front-column corner ⟹ Route B factors and closes) was INCOMPLETE.**
The front corner DOES factor over the free `z_i`-columns — but the DEEP `∫_{A'}` step does NOT factor into
independent Wisharts. Codex (derived, adversarial):

- The pointwise AM-GM `(Σu_i²U_i)^{−c'} ≤ ∏(u_i²U_i)^{−w_ic'}` is valid without independence, but the NEXT
  step `∫∏U_i^{−w_ic'}dA' = ∏∫U_i^{−w_ic'}dA'_i` is **INVALID**: `QQᵀ = A₁(A₂A₂ᵀ)A₁ᵀ`, so ALL collapsing
  singular directions use the SAME Gram `A₂A₂ᵀ` — `A₂` is GLOBALLY SHARED, not independent blocks.
- The one exception (the clean `A₂ ↦ (w₁A₂,w₂A₂,v̄A₂)` `8+4` split, `onePeel334`'s claim) has Jacobian
  `|det M|⁴`, so the inverse contributes `|det M|^{−4}` — **non-integrable across `{det M=0}`, and the
  corank cells INCLUDE `det M→0`.** So the split works only on a sector `|det M|≥ε`; the complement needs
  another rank descent. (This is the F2 dominant-minor seam again, now biting the cast itself.)
- The corank-2 locus has COMPETING profiles (`rank A₁≤1` vs `rank A₁=rank A₂=2, ker A₁⊂im A₂`) — no single
  disjoint-row decomposition of `A₂` describes both.
- The symmetric compound majorant `(s₂s₃)^{−b}` fails: dominating `s₂^{−3}s₃^{−η}` needs `b ≥ (3+η)/2 =
  c'−3/2 > 3/2`, but `s₃`-tube integrability needs `b < D₁ = 1` — **no overlap** (= `corank2-cert §4`,
  exact, Codex-reconfirmed).

**So integrating `w` jointly dissolves Route A's EMITTED-FACTOR coupling, but NOT the underlying shared-`A₂`
geometry — it resurfaces as correlated singular values / rank flags.** Route B can use a JOINT flag-tube
proof, but CANNOT use independent deep-block Wisharts globally. The formaliser's `#123 → square Wishart +
hIH core` route is invalid (the disjoint step is false).

---

## 3. {w=0} — handled by joint transverse volume, but the corank-2 neighborhood needs the JOINT flag-tube estimate (Q3)

Route A's `+∞` fibre over `{w=0}` does NOT imply joint divergence (Codex, exact local model
`∫∫(‖v‖²+‖Γ‖²)^{−c'} < ∞ ⟺ 2c'<7`; the conditional `Γ`-fibre at `v=0` is `+∞`, the joint `7`-dim integral
finite for `c'<7/2`). Under Route B, `{w=0}` is a null sub-locus of the front `A₀` integration handled
through transverse volume — **NOT deleted**. BUT for fixed `rank Q = ρ`, `g(Q)<∞ ⟺ 2c'<3ρ`, so `g(Q)=+∞`
on the exact `rank≤2` locus for `3<c'<7/2` — the neighborhood's blow-up MUST be integrated. And for corank-2
the SCALAR codim is insufficient: one needs the SHARP two-scale flag estimate
> `μ{s₂≤t₂, s₃≤t₃} ≍ t₂³·t₃·log(e/t₂)` (`t₃≤t₂`) ⟹ `∫ s₂^{−3}s₃^{−η}dμ < ∞ ⟺ η<1 ⟺ c'<7/2`,

NOT the marginals (`min(t₂⁴,t₃)` closes only for `η<1/4`, far short of `η<1`). **This joint flag-tube
estimate IS established as MATH (`corank2-cert §2`, decorrelated), but it is NEW Lean infra (the joint
pushforward-density module, `corank2-cert`'s "route J"), NOT the Cauchy–Binet/algebraic-codim shortcut.**
So {w=0} closes via front-first joint integration + strict threshold + the SHARP flag-tube theorem;
strictness + scalar codim `D` alone does NOT.

### 3′. The controller's q3 input — the `pivotEnergy_inverse_free` / bilinear-{w=0} claim, adjudicated (CLAIM TESTED, not accepted)

The descent-formaliser (Route-B advocate) offers: `w = frobSq([P|B₁₂]·Q)` is **inverse-free** (no `P⁻¹`), so
`{w=0}` is a clean bilinear locus, AND `{w=0}` is resolved **route-independently** because the corank term
`frobSq(C·Q̃ₚ + Γ·Q_b)` keeps the freed loss positive off `{both blocks vanish}` — i.e. by NOT dropping the
corank contribution, not by deletion. Treated as a claim to REFUTE (burden on Route B). Exact local model
(freed, post-shear: `loss = ‖P·Q̃ₚ‖² + ‖Γ(A')·Q_b‖²`, `P` the invertible pivot; `p = dim Q̃ₚ`):

- **HALF TRUE, and USEFUL — inverse-free kills ONE feared divergence.** `P` invertible ⟹ the sub `u=P·Q̃ₚ`
  in `∫_{ℝ^p}(‖P·Q̃ₚ‖²+m)^{−c'}dQ̃ₚ` has **constant** Jacobian `|det P|^{−1}` (NOT `det`-dependent). So there
  is NO `P⁻¹` det-inverse blow-up over `{w=0}` — the `#128v1` fear (a `det`-inverse singularity on the pivot
  vanishing-locus) is genuinely absent, and the shrinking-image CoV is clean here. This is a real
  simplification; concede it.
- **BUT "resolved route-independently" is an OVERCLAIM — positivity ≠ integrability; the pivot peel HANDS OFF
  to the reduced recursion, it does not self-resolve.** Exact Beta reduction (by hand, polar `r=√m·ρ`):
  `∫_{ℝ^p}(‖P·Q̃ₚ‖²+m)^{−c'}dQ̃ₚ = |det P|^{−1}·S_{p−1}·(∫_0^∞ρ^{p−1}(1+ρ²)^{−c'}dρ)·m^{p/2−c'}`, the `ρ`-integral
  a finite constant iff `2c'>p`. So integrating the pivot does NOT dispatch `{w=0}` — it **shifts the
  exponent** `c' ↦ c'−p/2` (this IS `half_minAdm_sub_half_peelCharge_le`, the threshold shift) and emits
  `m^{p/2−c'} = ‖Γ(A')·Q_b‖^{2(p/2−c')}`, i.e. **exactly the reduced corank-Gram integral over `(A',Q_b)` at
  the peeled exponent** — the `redChain` recursion, one peel lighter, NOT a closed sub-locus.
- **Does the OUTER (A',Q_b) integral blow up on a positive-measure neighbourhood of `{w=0}`? YES unless the
  peeled exponent clears the corank threshold.** The handed-off `∫∫‖Γ(A')·Q_b‖^{−2(c'−p/2)}` is finite ⟺
  `c'−p/2 < ` (corank-Gram threshold `min(tail)−b+1`), which is precisely the `minAdm` bookkeeping the ledger
  tracks. The corank term keeps the loss **pointwise positive** off `{both vanish}`, but the neighbourhood is
  controlled by the reduced-exponent recursion's threshold, not automatically. For `3<c'<7/2` at corank-2 the
  reduced integral still diverges under the scalar/marginal bound and needs the SHARP joint flag-tube
  `μ≍t₂³t₃log` (§3) — the same JOINT (w, corank, rank-degeneration) resolution, NOT a route-independent free
  lunch.

**Net.** The bilinear-`{w=0}` / inverse-free structure is a genuine handle (no `det`-inverse on the pivot
locus — concede this to Route B), but it does **not** make `{w=0}` self-resolving or Route B cheaper: the
pivot peel is a threshold-shift that FEEDS the reduced corank recursion (`redChain`), which is exactly the
decorated-ledger machinery of Route A. So the input SUPPORTS "pivot peel is inverse-free" (useful, banked)
and REFUTES "{w=0} resolved route-independently" (it relocates to the reduced joint threshold). This is
consistent with §3's verdict — no flip: the mechanism (shared-`A₂` / joint corank threshold) is unchanged;
the inverse-free handle removes a spurious `det`-inverse worry but not the joint-finiteness obligation.

---

## 4. VERDICT + recommendation (Q4)

- **Route A (decorated (S,J) ledger) is the presently ROBUST closing mechanism** — the controller's
  commissioning decision (UPDATE-911) STANDS.
- **Route B as advertised (front-first + #123 Cauchy–Binet → independent Wisharts + `hIH` core) does NOT
  close** — the global disjoint-`A₂`/product-Wishart step is FALSE (§2). The hard part is RELOCATED into the
  missing JOINT singular-value flag-tube estimate.
- **A corrected Route B is legitimate:** `front Beta integral + three corank cells + joint flag-tube
  estimates` (`corank2-cert §2`'s route J). For the SINGLE `(3,3,3,4)` integral it could be SHORTER than
  the width-general decorated ledger — **but only after proving that flag-tube theorem** (the joint
  pushforward-density module; Cauchy–Binet measurability + algebraic codim do NOT supply it). So it is not
  yet a cheap contained cover + independent Wishart base — it relocates the mountain into a spectral/rank-
  flag resolution of the shared-`A₂` pushforward.

**Recommendation:** KEEP Route A (the decorated descent) as commissioned — it is robust and width-general.
Do NOT switch to the formaliser's cheap Route B (#123 → Wishart): the disjoint-`A₂` step is false. IF a
`(3,3,3,4)`-specific shortcut is later wanted, the honest corrected Route B needs the joint flag-tube module
(`corank2-cert §2` route J, `μ ≍ t₂³t₃log`) — established-math but new Lean infra, comparable in cost to a
slice of the ledger, and NOT width-general. #123 stays a valid TOOL (the det-Gram weight / single-matrix
Wishart base) inside either route, but is NOT itself the closer.

---

## 5. On the flip-flop (the honest meta-note)

This route has moved `#123 (Level-A cheap) → #128v1 NO → #128v2 YES → descent Route A → [this tick]`. The
STABLE core, decorrelated-confirmed across the last two ticks: **the shared-`A₂` coupling is real** (the
Gram `A₂A₂ᵀ` is common to all collapsing directions), so NO independent-block factorization closes it
globally — whether phrased as Route A's emitted `det·w` factors (Γ-first) or Route B's independent-Wishart
tube (front-first). Both must handle the shared `A₂`: Route A by the decorated ledger, Route B by the joint
flag-tube density. My earlier "front columns free ⟹ Route B closes cheaply" over-weighted the FRONT corner
(which does factor) and missed that the DEEP tube is a JOINT flag estimate (correlated `s_j` via shared
`A₂`), not independent Wisharts — Codex caught this. The verdict is now stable in the mechanism (shared `A₂`
is irreducible to independent blocks), and the two routes differ only in HOW they resolve it (ledger vs
flag-tube), with Route A robust/width-general and corrected-Route-B slice-specific + new-infra.

- **Firmest.** #123 (weight tool) and the descent (Route A coupling) address different mechanisms, no
  contradiction. Route B's disjoint-`A₂` step is FALSE (shared Gram `A₂A₂ᵀ`; `|det M|^{−4}` non-integrable;
  symmetric compound `b≥3/2` vs `b<1`). {w=0} closes via joint transverse volume + the SHARP flag-tube
  `μ≍t₂³t₃log`, not scalar codim.
- **Route for the Level-A hole.** Route A (decorated descent) — robust, width-general, commissioned.
  Corrected Route B (flag-tube) — possibly shorter for `(3,3,3,4)` alone, but relocates the mountain to the
  joint-density module (new infra), not a cheap Cauchy–Binet build.
- **Next.** Proceed with Route A as commissioned; my fidelity-audit foci (ledger charges ADD to `minAdm`;
  the 3-hyp measure glue: joint `{w=0}`, active-`r` threshold `ar/2`, the `c'≤ab/2` branch) are unchanged.
  Do NOT re-open Route B unless the operator wants the `(3,3,3,4)` flag-tube shortcut, in which case the
  gate is the joint pushforward-density theorem (corank2-cert §2), not Cauchy–Binet.

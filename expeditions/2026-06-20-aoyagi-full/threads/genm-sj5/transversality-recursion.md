# The p=0 transversality-recursion lemma — width-general, Aoyagi-independent (the A2 peel-closure invariant)

**Seat:** pen-and-paper (scoping the width-general no-obstruction lemma — genm-sj5-cover). **Date:**
2026-07-11. **NO Lean.** **Charge (team-lead):** scope the width-general, Aoyagi-independent form of the
`p=0` transversality settled top-level in `toric-ray-cert.md` — the residual for a fully width-general
certificate AND the A2 admissible-family's peel-closure invariant. State it as a clean geometric lemma +
the recursion argument + Codex cross-check.

**Exact algebra (mine):** `/tmp/prodD/{transrec_check,zdeep_rank,transrec_verify}.py` (the critical-component
`Zdeep` rank across chains; the binding-cut convexity bound; the `a=0` scan). **Decorrelated:** own xhigh
`local-codex-consult`, conclusion WITHHELD, told to BREAK the lemma with a specific width:
`codex/transrec-{prompt,answer}.md`. **Codex EARNED its keep — it REFUTED my literal lemma and supplied the
correct, cleaner invariant + its proof + the essential hypothesis + a counterexample.** I re-derived and
verified every step.

---

## ★ HEADLINE — the lemma, CORRECTED (my first form was FALSE; the true invariant is cleaner and Aoyagi-independent)

**My proposed lemma "the critical reduced divisor is pivot-vanishing with the shared deeper product `Zdeep`
GENERIC FULL-RANK" is FALSE** (Codex counterexample: reduced `(2,2,2)` has its UNIQUE top-dim component at
`rank Zdeep = 1 < 2` — a real rank drop — arising at the binding cut of `M=(3,3,2,2)`). **But the CONCLUSION
`p=0` survives via a cleaner, correct, and width-general invariant, proven by `minAdm` binding-cut
convexity:**

> **LEMMA (peel-closure transversality).** At a binding cut `t` of a chain `M` with a NONTRIVIAL front block
> — `a=M₀−t ≥ 1` and `b=M₁−t ≥ 1` — every top-dimensional component `X` of the reduced zero-product locus
> `Z_t = {A₁,piv·Zdeep = 0}` has generic deeper rank
> `rank_{gen,X}(Zdeep) ≥ a+b−1 ≥ b`.
> Hence, for free corank block `A₁,cor` (`b×M₂`), the corank rows `A₁,cor·Zdeep` have generic row rank `b`
> on `X`, so the collapsing directions do NOT vanish: `p = ν_X(H₁) = 0` (indeed the whole corank block is a
> unit, `q=0` too).

The literal "generic full rank `Zdeep`" is NOT claimed and is FALSE in general; only the weaker
`rank ≥ a+b−1 ≥ b` — enough for the `b` corank rows to survive — is true, and it is exactly what `p=0`
needs. **This CORRECTS the framing in `toric-ray-cert.md §2/§4/§5** (which said "shared deeper product
generic full-rank"): the certified geometric fact is the weaker `rank Zdeep ≥ b`, not full rank; the `p=0`
conclusion and the Q_D no-obstruction verdict are UNCHANGED.

---

## 1. The proof (clean, Aoyagi-independent, `minAdm`-convexity)

Let `C_t := minAdm(redChain(t,M)) = minAdm(t,M₂,…,M_L)`, so `minAdm(M) = min_t [(M₀−t)(M₁−t) + C_t]`.

- **Incidence bound [DERIVED].** Passing from cut `t` to `t+1` adds ONE pivot row, which on a component `X`
  with generic deeper rank `r_X` must lie in `leftker(Zdeep)` (dim `M₂−r_X`) — costing exactly `r_X`
  equations. So `C_{t+1} ≤ C_t + r_X`.
- **Binding-cut convexity [DERIVED, verified].** `t` binding ⟹ `ab + C_t ≤ (a−1)(b−1) + C_{t+1}` (the cut
  `t+1` is admissible precisely because `a>0,b>0`). Since `ab − (a−1)(b−1) = a+b−1`,
  `C_{t+1} − C_t ≥ a+b−1`. [Verified at every nondegenerate binding cut of all tested chains,
  `/tmp/prodD/transrec_verify.py`: e.g. `(3,3,3,4)` t=1 gap 3 = a+b−1; `(4,4,4,4)` t=2 gap 3; `(2,5,5,5)`
  t=1 gap 4.]
- **Combine:** `a+b−1 ≤ C_{t+1}−C_t ≤ r_X`, so `r_X ≥ a+b−1 ≥ b`. Then `A₁,cor·Zdeep` (`b` free rows through
  a rank-`r_X ≥ b` map) has generic row rank `min(b,r_X)=b` → corank block a unit → `p=q=0`. ∎

The bound is TIGHT (`r_X = a+b−1` in many anchors: `(3,3,3,4)`,`(4,4,4,4)`,`(5,5,5,5)`,`(2,5,5,5)`), so no
slack to spare — the invariant is exactly at the margin, which is why the naive "full rank" over-claimed.

## 2. Why the literal form is FALSE (the decorrelated counterexample — keep it visible)

Reduced `(2,2,2)`, `U (2×2)`, `Zdeep (2×2)`: rank-stratum codims `(2−r)²+2r = (4,3,4)` for `r=0,1,2` →
`minAdm(2,2,2)=3`, unique top component at `r=1` (deeper rank 1 < 2, a REAL drop). It arises at the binding
cut `t*=2` of `M=(3,3,2,2)` (peel values `9, 6, 4, 4`). **A deeper rank drop CAN be the unique
top-dim degeneration.** But there `a=b=1`, `r_X=1=b`, so the single corank row survives (`p=0`) — the
`min(b,r_X)` mechanism, not full rank. [Verified `/tmp/prodD/transrec_verify.py` V-B.]

## 3. The essential hypothesis `a>0, b>0` — and why it is exactly the "decoration exists" condition (RESOLVED)

The bound uses `t+1` admissible, i.e. `a>0` and `b>0`. **This hypothesis is not a gap — it is automatically
satisfied exactly where `p=0` is needed:**
- The front Γ-block is `a×b`; the corank-Gram decoration `‖C·Q̃ₚ + Γ·Q_b‖²` (and the det-Gram weight) exists
  **iff `a≥1` AND `b≥1`** (a nontrivial Γ-block). This is precisely the nondegenerate-cut hypothesis.
- If `a=0` (`t=M₀`) or `b=0` (`t=M₁`): the Γ-block is empty (`0×b` or `a×0`), the corank term vanishes
  identically, `peelCharge=0`, and the peel is a NO-OP that simply drops the `M₁` layer (arity −1, progress).
  There is no `H₁`, so `p=0` is VACUOUS. [Codex's `(2,3,2,1)`, `a=0`, where `A_cor·Z=0` on a top component,
  is exactly such a no-op: it refutes the literal geometric claim but creates NO finiteness problem, since
  no Γ-decoration exists there.]

**So at every peel that actually carries a decoration (`a>0,b>0`), the lemma applies (`p=0`); at every
degenerate peel, `p=0` is vacuous.** The invariant therefore holds at every step of the descent, for every
chain — width-general, no extra hypothesis needed. [Scan `/tmp/prodD/transrec_verify.py` V-C/V-D: the many
`a=0` binding cuts are no-op layer-drops, not decorated peels.]

## 4. The recursion (peel arity-descent) + the A2 peel-closure invariant

- **Recursion.** `minAdm(M) = peelCharge(t) + minAdm(redChain(t,M))`, redChain shorter by one node
  (arity `L+1 → L`). At each step: if `a,b>0`, the lemma certifies `p=0` for that peel's corank block; the
  reduced-front-block vanishing (the condition defining `Z_t`'s top components) is then resolved by the SAME
  peel applied to `redChain`, whose nondegenerate cuts satisfy the lemma one level down. Terminates at the
  arity-2 base `(u,n)`, `minAdm=un`, a free block `{U=0}`; a parent peel's corank block is free there and has
  full row rank `b` whenever `b ≤ n` — automatic at a nondegenerate binding base cut
  (`n = C_{t+1}−C_t ≥ a+b−1 ≥ b`).
- **= the A2 admissible-family peel-closure invariant.** The A2 admissible family's invariant (ii)
  "peel-closed" IS this transversality: an admissible chain-with-decoration, peeled at a nondegenerate
  binding cut, yields a redChain whose top-dim components carry `rank Zdeep ≥ b` (so the corank block is a
  unit and the decoration's valuation `p=0` is preserved). The lemma is precisely the statement that the
  admissible family is closed under the peel. So it is doubly load-bearing (the width-general no-obstruction
  AND the A2 def's peel-closure).

## 5. The one residual (Codex [INFERRED], honest) — intersection divisors need the joint resolution

`p=0` on every top-dim component controls exceptional divisors DOMINATING those components. It does NOT
automatically control divisors centered over PROPER rank-drop INTERSECTIONS (where several top components
meet, or a higher-codim stratum). Those are handled by the joint DECORATED resolution (the descent's inner
recursion — #141 Q2, `toric-ray-cert §4`), NOT by this component-generic lemma alone. This is a construction
obligation (the decorated IH must resolve the coupled corner over the intersections), NOT a finiteness
obstruction: by the combined-ray formula, an intersection ray has `ord Jac` at least the sum of the
component contributions (higher `K`), so its ratio stays `≥ ½minAdm` (log-multiplicity at the boundary only).

---

## Firmest / most-likely-to-break / next

- **Firmest (certified, width-general, Aoyagi-independent).** At every nondegenerate binding cut
  (`a,b>0` = the decorated peel), `rank_{gen,X}(Zdeep) ≥ a+b−1 ≥ b` on every top-dim component (clean
  `minAdm`-convexity proof, verified), so the corank block is a unit and `p=q=0`. Degenerate peels (`a=0` or
  `b=0`) carry no decoration so `p=0` is vacuous. The literal "Zdeep full rank" is FALSE ((2,2,2)); the
  correct invariant is `rank ≥ a+b−1 ≥ b`. **Correct `toric-ray-cert §2/§4/§5`'s "generic full rank" wording
  to this weaker true invariant** (conclusion `p=0` / Q_D no-obstruction unchanged).
- **Most likely to break.** The intersection-divisor residual (§5) — NOT controlled by the component lemma;
  it is the decorated IH's job. If the decorated resolution fails to keep the ratio `≥ ½minAdm` over a
  rank-drop intersection, that would be the genuine risk — but the combined-ray formula makes it detectable
  (higher `K` at intersections keeps the ratio up), and it is Aoyagi-consistent.
- **Next.** This is the clean Lean-target for the A2 peel-closure invariant: (i) the incidence bound
  `C_{t+1} ≤ C_t + r_X`, (ii) the convexity `C_{t+1}−C_t ≥ a+b−1` (pure `minAdm` arithmetic, banked-adjacent),
  (iii) `rank(A_cor·Zdeep)=min(b,r_X)=b`. Hand to genm-sj5-descent as the A2 admissible-family peel-closure
  lemma; I fidelity-audit the A2 Lean against this (the invariant, the corrected decoration
  `H₁^{−3}(H₁+H₂)^{−1}`, charges ADD, the terminal) once posted.

---

## 6. BASE-AUDIT of the §10 `adm` encoding (`cov-ledger-design §10`) — the (□)-gating fidelity check

**Charge (team-lead):** base-audit the formaliser's §10 `SJDecoration adm`-predicate encoding of this `p=0`
transversality against the certified math — is `adm` (a) contains trivial, (b) peel-closed = #144, (c)
provable base = terminal reduction, (d) charges ADD + corrected residual. Decorrelated adversarial Codex on
the ENCODING (`codex/admenc-{prompt,answer}.md`, conclusion withheld); every claim re-verified by me
(`/tmp/prodD/quantgap.py`).

**VERDICT: PASS — the A2 architecture is SOUND — conditional on ONE encoding correction (B1, definite) and
closing ONE base gap (C1, the quantifier gap). Two regression tests to bake in.**

### (a) trivial ∈ adm + specialisation — **PASS**
`SJDecoration.trivial M` (carrier `ofMatrix`, no exceptional divisors) is reachable (0 peels) and `p=0`
vacuously, so `adm(trivial)` holds; the threshold in `DecoratedBoxThresholdFinite` is `½minAdm`
decoration-independently, so `decoratedBoxThresholdFinite_trivial_iff` recovers plain `RouteMBoxThresholdFinite M`.
Sound entry point.

### (b) peel-closed = #144 — **PASS on the corrected encoding; §10.1's "full rank" gloss is TOO TIGHT (B1, definite)**
- **[B1, TOO-TIGHT — the one definite error, drop it].** §10.1 encodes the invariant as "the corank
  generators are NOT divisible by the critical divisor **(the shared deeper `Z` enters them at full rank)**."
  The parenthetical is the stale over-claim §1/§2 refuted and is **NOT equivalent** to `p=0`: a literal
  "`Z` full-rank" predicate **breaks peel-closure**. Regression test [V, `/tmp/prodD/quantgap.py`]: the peel
  of `M=(3,3,2,2)` at `t=2` (values `9,6,4,4`) produces the reduced `(2,2,2)` whose unique top component has
  `rank Zdeep = 1 < 2`, yet `b=1=rank`, so `p=0` (the corank row survives) — the peel GENUINELY produces this
  decoration, and a full-rank predicate REJECTS it. **Encode ONLY the valuation clause**
  `a=0 ∨ b=0 ∨ (∀η∈Crit(D), min_j ν_η((q₁+s q₂)_j) = 0)` — "some corank generator is a unit at each critical
  divisor" (`p=0`). NO `q=ν(H₂)` condition (harmless, must not appear).
- **[B2, cleaner form — transversality is a THEOREM, not carried].** `adm = Reachable ∧ Transverse` is
  redundant: reachability via legal binding-cut peels ALREADY implies `p=0` (induction on the peel history:
  trivial→no critical divisor; `a=0/b=0`→vacuous; `a,b≥1`→#144/F2 gives `p=0`; earlier divisors retained).
  So the cleanest `adm := "D reachable from trivial by legal decorated peels AND required chart refinements"`,
  and one PROVES `adm(D) ⟹ ∀η∈Crit(D), p_η=0` (this lemma = #144) rather than storing transversality as data.
  **Caveat (Codex):** "reachable" must mean produced by the GENUINE algebraic peel (carrier + context), not a
  syntactically plausible support matrix.

### (c) provable base / terminal reduction — **PASS with a GAP to close (C1, the sharp base-soundness finding)**
- **[C1, the quantifier gap — close it].** `sjLoss_terminal` needs (T) `∃ i₀ ∀ℓ, e(i₀,ℓ)=k_ℓ` (`k_ℓ=min_i
  e(i,ℓ)`) — ONE simultaneous unit generator. Divisorwise `p=0` gives only (P) `∀ℓ ∃ i_ℓ, e(i_ℓ,ℓ)=k_ℓ` — for
  EACH divisor SOME generator is a unit. **(P) ⇏ (T); the quantifier swap is INVALID.** Countertest [V]:
  generators `g₁=x, g₂=y` (supports `(1,0),(0,1)`) satisfy (P) but there is no single support-`(0,0)`
  generator; `∫_{[0,1]²}(x²+y²)^{−c'}` DIVERGES for `c'≥1` (RLCT `=1`), and the intersection `{x=y=0}` blows
  up to a divisor `E` with `ν_E(x)=ν_E(y)=1` (so `p_E=1` — an INTERSECTION divisor carries `p>0`). On the
  `x`-chart `x²+y²=x²(1+v²)` the residual generator `1` supplies (T). **So the base is sound ONLY IF `Crit(D)`
  includes the intersection/combined exceptional divisors AND the chart refinements that resolve them** (each
  refined chart then supplies (T)); checking only the original component divisors is TOO LOOSE (false base,
  the `x²+y²` countertest). This is #144 §5's intersection residual, now at Lean precision: §10.3's `{v=0}`
  rank-drop recursion is NOT optional — it IS the intersection refinement that supplies (T), and it must be
  part of "reachable + refinements."
- **[no b>2 obstruction].** `p = min_j ν_η(g_j)` is width-independent (Codex Q3); wide `b` needs only a finite
  entry/minor chart cover to select a uniformly nonvanishing generator — my earlier "b>2 chart" flag is
  DOWNGRADED to a routine finite cover, not a soundness gap. And `p=0` does NOT need `H₂` a unit (a unit `H₁`
  already makes `H₁²+v²H₂²` bounded below) — consistent with §10.4/B1 (no `q` condition).
- Modulo C1, §10.3's terminal reduction (`f ≍ R²+u²·unit` on the `p=0` divisor → `sjLoss_terminal`, with `p=0`
  = the dehomogenised generator) is SOUND: `p=0 ⟺` the corank generator surviving `⟺` the (T) hypothesis on
  the refined chart. The `p=0 ⟺ dehomogenisation` connection is the correct, load-bearing insight.

### (d) charges ADD + corrected residual — **PASS**
§10.4 uses the corrected `H₁^{−3}(H₁+H₂)^{−1}` (drops the sloppy `H₁^{−3}H₂^{−1}`, matches toric §5); §10.5 has
the nD-homogeneous corner `½Σ(p_i+1)=½Σ(block dims)=½minAdm`, both coupling charts. Matches the certs.

### (units-interface) does #144 discharge the formaliser's leaf hypothesis "H₁,H₂ units"? — **YES, MATCHES**
The formaliser builds part (c) (the b>1 terminal reduction) in Lean CONDITIONAL on "H₁,H₂ units on the chart."
Seam-check: does #144's invariant supply it? **YES [V, `/tmp/prodD/units_interface.py`].**
- #144 gives `rank(A_cor·Zdeep) = min(b, rank Zdeep) = b` (full ROW rank, since `rank Zdeep ≥ a+b−1 ≥ b`), so
  the `b` corank rows are LINEARLY INDEPENDENT. Independent ⟹ `q₂≠0` (`H₂=|q₂|` a unit) AND `q₁+s q₂≠0` for
  ALL `s` (`q₁∥q₂` is impossible for independent rows, so `q₁+s q₂` never vanishes) ⟹ `H₁=|q₁+s q₂|` a unit
  uniformly in the angular `s`. So full-row-rank `b` ⟹ BOTH `H₁,H₂` units. The formaliser's hypothesis is
  DISCHARGED. **The seam to make explicit in Lean: the bridge lemma `corank block full row rank b ⟹ H₁,H₂
  units` (elementary — independent rows are nonzero, and `q₁+s q₂≠0 ∀s` for independent `q₁,q₂`).**
- **Discharged with ROOM:** the terminal needs only `H₁` a unit (`H₁²+v²H₂² ≥ H₁² > 0` regardless of `H₂`), and
  `= p=0`. So the minimal leaf hypothesis is "`H₁` unit"; "`H₁,H₂` units" is stronger but still supplied by
  #144. Either statement is safe; "`H₁` unit" is the cleanest (exactly `p=0`).

### (c)-soundness cross-check (not re-derived — the formaliser's green proof carries it) — **SOUND**
`frobSq(Γ·Q_b) = u²·frobSq(M·Q_b)` (`Γ=u·M`), and on the units divisor `frobSq(M·Q_b) ≥ |q₁+s q₂|² = H₁² > 0`
is a UNIT, so `frobSq(Γ·Q_b) = u²·(unit)` — a monomial; with `R²` (reduced) → `f = R² + u²·unit` →
`sjLoss_terminal`. The `unit` conclusion needs ONLY `H₁>0 ∀s` (full-rank), not the row op. **Subtlety to flag:**
§10.3's "row op `row₂↦row₂−t·row₁` ⟹ `H₁²+v²H₂²`" is a `|det|=1` SHEAR on the `a`-output rows — a bounded
unit-Jacobian CoV of the residual, NOT a norm-preserving identity (`frobSq` is not shear-invariant). The
formaliser must realise it as a CoV (harmless for the RLCT), or skip it (the `≥H₁²>0` unit bound is direct).
Sound modulo C1's `{v=0}` intersection refinement (mine).

### Net + the two regression tests (bake into the build)
The A2 architecture PASSES; the units-interface MATCHES (#144 discharges "H₁,H₂ units" via the full-rank →
independent-rows bridge). The formaliser should build `adm := reachable-from-trivial by legal decorated
peels AND chart refinements` (NOT a full-rank predicate, NOT a stored transverse flag), prove `adm ⟹ ∀η∈Crit
p_η=0` (= #144, including intersection divisors), and prove the terminal via (T) supplied on the refined
charts. **Regression tests:** (1) peel-closure — `(3,3,2,2) →_{t=2} (2,2,2)` rank-1 component (`p=0`, not
full-rank) must be ADMITTED; (2) base-soundness — the support matrix `{(1,0),(0,1)}` (`x²+y²`, RLCT 1) must be
REJECTED as terminal until the intersection is refined (catches the `∀η∃i ⇏ ∃i∀ℓ` step). On these two, a wrong
encoding fails immediately.

---

## 7. BASE-ROUTE adjudication — Route (A) [local Rayleigh/Loewner Gram bound] vs (B) [angular CoV → sjLoss_terminal]

**Charge (team-lead):** does Route (A) — `frobSq(Γ·Z) ≥ λ_min(ZZᵀ)·frobSq(Γ)` for `Z` full-ROW-rank, then
`∫(frobSq ΓZ)^{−c'} ≤ λ_min^{−c'}·∫(frobSq Γ)^{−c'}` via banked free-block `sumSqND_box_lt_top` — discharge
`DecoratedBaseHyp`, bypassing the C1 `(T)`-issue and the angular CoV? **VERDICT: PASS — build (A) for the
base.** [V, `/tmp/prodD/routeA.py`; exact linear algebra, no Codex needed — Rayleigh/Loewner is standard.]

- **Q1 SOUND + FULL threshold — YES.** `frobSq(ΓZ)=tr(Γ(ZZᵀ)Γᵀ)`, so `λ_min(ZZᵀ)·frobSq(Γ) ≤ frobSq(ΓZ) ≤
  λ_max(ZZᵀ)·frobSq(Γ)` (two-sided, verified 50000/50000). With `Z` full-ROW-rank, `ZZᵀ ≻ 0`, `λ_min>0`. The
  free-block `∫_{box⊂ℝ^{ab}}(‖Γ‖²)^{−c'}` is finite ⟺ `c'<ab/2`. So (A) gives `< ∞` for `c'<ab/2`, and the
  `λ_max` side forces divergence at `c'≥ab/2` — RLCT is EXACTLY `ab/2 = ½·minAdm(base)` (`{Γ=0}` codim `ab`),
  the FULL threshold, not a sub-threshold. The jac-monomial decoration `∏|u|^{jac}` factors out (separate
  vars), `∫∏|u|^{jac}<∞` (`jac≥0`), and `λ_min(Z)^{−c'}` is bounded on the units chart — so the DECORATED
  base is finite at `½minAdm`.
- **Q2 BYPASSES C1 — YES (for the base's terminal (T)-issue).** (A) never forms a monomial / never calls
  `sjLoss_terminal`, so the `(P)⇏(T)` quantifier gap does not arise. On the `x²+y²` countertest (§6-C1), (A)
  reads it as a FREE 2-block `‖(x,y)‖²` and gives `c'<1` = the TRUE RLCT directly (radial free-block), no
  dehomogenised generator, no intersection blow-up. **Caveat (honest):** (A) needs `λ_min(ZZᵀ)` bounded below
  UNIFORMLY on the base chart (= `Z` full-row-rank quantitatively = the units-on-chart safeguard = my #144
  invariant). Reaching that chart (excising `Z`-rank-drops = the `{v=0}` refinement) is still the COVER's job,
  SHARED with (B). So (A) eliminates C1's terminal-`(T)`/monomial sub-problem, NOT the units-chart refinement
  (which #144 supplies). No DIFFERENT unsoundness — the bound is an exact one-sided (upper) estimate, sound
  wherever `λ_min≥c>0`.
- **Q3 DISTINCT from the #140-killed global route — YES.** (A) is a LOCAL leaf bound: `Z` a FIXED fully-reduced
  matrix, integrate `Γ` only; `Γ(ZZᵀ)Γᵀ ≥ λ_min ΓΓᵀ` is exact Loewner for fixed `Z`. It does NO
  "independent-Wisharts-across-shared-`A₂`" decoupling (the global decomposition #140 killed). No conflict.
- **Q4 step consumes base as FINITENESS — YES.** `DecoratedBoxThresholdFinite` is a `Prop` (`∫<⊤`); the step's
  IH consumes the RESULT, route-agnostically. (A)'s finiteness IS a valid `DecoratedBoxThresholdFinite`. The
  monomial/`sjLoss_terminal` form is a STEP-INTERNAL ledger matter (how the peel emits its reduced decoration),
  NOT a base requirement. So (A) for the base is compatible with the decorated step.

**Recommendation: build Route (A) for `DecoratedBaseHyp`** — cheaper, avoids the fiddly matrix-space angular
CoV, and bypasses C1's terminal-`(T)` sub-problem. **Two conditions to honour (both supplied):** (i) the base
chart is quantitatively units (`λ_min(ZZᵀ)≥c>0`, `Z` full-row-rank) — the #144 transversality + the `{v=0}`
refinement reaching it; (ii) the banked `sumSqND_box_lt_top` delivers the FULL `c'<ab/2` at ambient dim `ab`
(confirm the banked lemma's threshold is `ab/2`, not weaker). On these, (A) discharges the base at the full
`½minAdm`. (Route (B)/`sjLoss_terminal` stays the STEP-internal ledger tool; C1's refinement remains the
cover's, unchanged.) [Route (A) later ruled OUT by the formaliser for global ledger-monomial-uniformity;
Route (B) chosen. This §7 stands as a sound-in-isolation rule-in of (A); the base build is (B).]

---

## 8. PROVED-vs-CITED for invariant piece (i) [`rank(Zdeep) ≥ b`] — NATIVE, bounded, NOT an AG wall (honors #97)

**Charge (team-lead):** the formaliser flags piece (i) — "top-dim component + generic rank on it ≥ b" — as
AG-hard (Mathlib frontier). Is there a NATIVE re-expression avoiding the AG infra, or a genuine formalization
wall? (The Proved-vs-Cited fork, operator-gated #97.) **VERDICT: NATIVE — piece (i) is a BOUNDED build; NOT
an AG wall. Build it (α), honoring #97.** [Decorrelated: own xhigh Codex `codex/native-{prompt,answer}.md`,
conclusion withheld — it CONFIRMED AG-free + gave the clean proof + a sharp caveat; I re-verified
(`/tmp/prodD/backpeel.py`, identity 12/12).]

**The native route (avoids irreducible-component decomposition + generic-rank-on-a-component entirely):**
- **[NEW LEMMA — the only fresh piece] `minAdm_eq_backPeel`:**
  `minAdm(t, M₂,…,M_L) = min_ρ [ cCodim(M₂,…,M_L ; ρ) + t·ρ ]`, `cCodim(·;ρ) = codim{deeper product rank ≤ ρ}`
  = the banked rank-shift `cCodim` (`= minAdm(M₂−ρ,…,M_L−ρ)`). **Proof is ELEMENTARY** (Codex Q1, verified):
  with `δ_r = codim{rank Zdeep = r}`, `{A_piv·Zdeep=0}` over `S_r` imposes exactly `t·r` conditions (each of
  `t` rows annihilates an `r`-dim image), so `codim Z_red = min_r(δ_r + t·r)`; and `cCodim(·;ρ)=min_{r≤ρ}δ_r`,
  so `min_ρ(cCodim(·;ρ)+tρ) = min_r(δ_r+tr)` by rearranging finite minima (`t≥0` ⟹ cheapest `ρ=r`). NO
  component decomposition — a finite-min identity, reindexing the banked QIP. [Identity verified 12/12.]
- **Incidence, now ARITHMETIC:** for any co-minimizer `ρ` of `minAdm(t,·)`, `minAdm(t+1,·) ≤ cCodim(·;ρ)+(t+1)ρ
  = minAdm(t,·)+ρ` (same minimizer). No geometry.
- **Convexity (banked, RouteMSJTransversality @d315be07):** `minAdm(t+1,·)−minAdm(t,·) ≥ a+b−1`.
- **⟹ every co-minimizer `ρ ≥ a+b−1 ≥ b`** — so every codimension-minimizing exact-rank stratum has deeper
  rank `≥ b`, WITHOUT "generic rank on a component."
- **Corank survival (elementary, Codex Q2):** on a rank-`r≥b` cell, for a.e. FREE `A_cor`,
  `rank(A_cor·Zdeep) = min(b,r) = b` (factor `Zdeep=UV`, `rank(A_cor Zdeep)=rank(A_cor U)`, `A_cor↦A_cor U`
  surjective onto `b×r`; the rank-deficient set is a proper minor-cut null set). This is genericity in the
  FREE integration variable `A_cor`, NOT on a variety component. The rank-`r` cells are minor-cut (Mathlib has
  rank + minors). [= the D1-lane (iii) machinery.]

**So piece (i) needs NO AG:** the AG "top-dim component + generic rank" is replaced by `minAdm_eq_backPeel`
(finite-min ℕ/codim identity) + banked convexity + the free-matrix generic-rank lemma + minor-cut cells. **The
one new lemma is `minAdm_eq_backPeel`** — same family as the banked front-peel↔QIP bridge
(`minadm-ccodim-cert`), bounded combinatorial labour, consuming banked `cCodim_rankShift`. **α (build) is the
right call; no β-cite needed; #97 honored at bounded cost.**

**Honest caveat (Codex Q3, sharpens C1 — NOT part of piece (i), but flag it):** the LOWER-rank cell recursion
is NOT closed by "higher codim ⟹ recurse with more slack" alone — higher codim can carry a LOWER RLCT
(counterexample `f=x²(x²+y^{2N})`: threshold `½` generic along `x=0`, but `(N+1)/(4N)<½` at the origin). So the
deficient-rank / intersection neighbourhoods (my C1, the `{v=0}` refinement) require the QUANTITATIVE COUPLED
recursive estimate — i.e. the DECORATED descent (charges ADD via the corner), NOT a codim triviality. This
CORRECTS my earlier glib "higher codim → slack" (§5, §6-C1 phrasing): the intersection/deficient rays' ratio
`≥ ½minAdm` is exactly what the decorated coupled resolution must establish (it is the descent's job, already
planned), not a free consequence of codim. Piece (i)-the-transversality is elementary/native; the lower-rank
descent is the (already-commissioned) decorated recursion.

---

## 9. AUDIT-LOG — piece #1 (`RouteMSJBackPeel.lean`, the α-unlock) — **PASS**

genm-sj5-desc2 landed piece #1 GREEN, with a POSITIVE recalibration: `minAdm_eq_backPeel` is NOT a fresh
`Core.CTheta` build — it is the banked FRONT-PEEL identity `minAdm_eq_frontPeel` (#117) read on `redChain t M`
(leading width = the surviving pivot `t`), + the banked convexity `minAdm_redChain_succ_ge`. Fidelity audit vs
§8 [decorrelated — arithmetic identification, verified `/tmp/prodD/backpeel_audit.py`, no new Codex]:
- **Q1 identification FAITHFUL.** The rank-shift `cCodim(deeper;ρ) = minAdm(deeper−ρ)` [subtract `ρ` from each
  deeper dim] holds 2034/2034; the front-peel-on-`redChain` form `minAdm(t,deeper) = min_ρ[t·ρ +
  minAdm(deeper−ρ)]` = my §8 `min_ρ[cCodim(deeper;ρ)+tρ]` holds 23400/23400. "Leading width `= t`" is faithful
  (`t` = the pivot rows; `t·ρ` = the pivot-in-leftker cost).
- **Q2 combinatorial `ρ ≥ a+b−1 ≥ b` MATCHES §8.** Every co-minimizer (verified over the anchors; note the
  co-minimizer is a SET, e.g. `ρ∈[2,3]` — the theorem must quantify over ALL, not just `min`) satisfies
  `ρ ≥ a+b−1`, by the incidence `+ρ` bump squeezed against banked convexity. Matches §8 exactly.
- **Q3 witness correct.** `(3,3,2,2) →_{t=2} (2,2,2)`, co-minimizer `ρ=1=b=a+b−1` — the TIGHT rank-drop witness
  (corank JUST survives, `ρ=b`).
- **★ the SPLIT / #2 geometric-bridge flag.** #1 proves the COMBINATORIAL `ρ≥b` only. The GEOMETRIC bridge
  (co-minimizing `ρ` = the deeper rank on the codim-realizing stratum ⟹ `rank(Zdeep)≥b`) is #2. **It is SOUND
  and NATIVE** (Codex native-answer Q3: `codim{A_piv·Zdeep=0} = min_r(δ_r + t·r)` over rank strata
  `{rank Zdeep=r}`, `δ_r=codim` of the exact-rank stratum; the finite-min rearrangement identifies the
  combinatorial `ρ` with the codim-realizing `r`), NOT irreducible-component decomposition. **But #2 is
  SUBSTANTIVE, not a one-liner:** it must formalize (a) the incidence codim decomposition
  `codim{A_piv·Zdeep=0}=min_r(δ_r+tr)` [elementary per-stratum linear algebra — each of `t` pivot rows in the
  `(M₂−r)`-dim leftker = `tr` conditions — but real], (b) the free-`A_cor` survival `rank(A_cor·Zdeep)=min(b,r)`
  a.e. [minor-cut null set], (c) the rearrangement. **Fidelity watch for #2:** it must use rank STRATA
  (minor-cut `{rank Zdeep=r}`) + free-`A_cor` genericity, NOT "the irreducible components of `Z_red` + generic
  rank on each" — the instant #2 reaches for components/generic-rank-on-a-component it re-imports the AG the
  native route avoids. **VERDICT: #1 PASSES; integrate it. #2 is the fidelity-critical bridge — sound, native,
  bounded, but substantive; audit it hardest when it lands.**

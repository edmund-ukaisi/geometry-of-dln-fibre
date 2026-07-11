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

### Net + the two regression tests (bake into the build)
The A2 architecture PASSES. The formaliser should build `adm := reachable-from-trivial by legal decorated
peels AND chart refinements` (NOT a full-rank predicate, NOT a stored transverse flag), prove `adm ⟹ ∀η∈Crit
p_η=0` (= #144, including intersection divisors), and prove the terminal via (T) supplied on the refined
charts. **Regression tests:** (1) peel-closure — `(3,3,2,2) →_{t=2} (2,2,2)` rank-1 component (`p=0`, not
full-rank) must be ADMITTED; (2) base-soundness — the support matrix `{(1,0),(0,1)}` (`x²+y²`, RLCT 1) must be
REJECTED as terminal until the intersection is refined (catches the `∀η∃i ⇏ ∃i∀ℓ` step). On these two, a wrong
encoding fails immediately.

# R1-UPPER flip-or-firm — certificate (pen-and-paper, WITNESS→OBSTRUCTION)

**Thread `genm-r1flip`** (branch `genm-r1flip` off `expedition/aoyagi-full @136b29c9`, isolated worktree).
**NO Lean build** — exact algebra (`flip1..4_*.py`, sympy 1.14, exact rationals + exact Gröbner) + a
decorrelated `local-codex-consult` (xhigh, leaning withheld, framed on the neutral math question:
`codex/flip-{prompt,answer}.md`). Mission: settle the operator's R1-UPPER build-vs-cite in both
directions — (A) the last honest attempt to REFUTE the wall, (B) if not, FIRM the cite.

---

## HEADLINE — (A) THE WALL FLIPS TO **BUILD**. r1carrier's research-grade brick is a FALSE WALL of the atom route.

**R1-UPPER general-L box-finiteness at corank ≥ 2 with a shared product tail is a LARGE-BUT-BOUNDED
BUILD, not a research-grade "needs a resolution-of-singularities theorem Mathlib lacks" gap. The
`peelZBlock` obstruction r1carrier certified RESEARCH-GRADE — the embedded principalisation of the
Cauchy–Binet/Plücker minor ideal `I_q(A_{1,b}·A₂·…)` of the matrix product — is an artifact of the
MEASURE-ATOM route (integrate the corank block `Γ` out over full space via the Gram change of variables
`Δ = Γ·Qb`, Jacobian `det(Qb Qbᵀ)^{−p/2}`). Aoyagi's PUBLISHED resolution never forms that ideal: it
resolves the loss singularity `{∏C = 0}` at the deepest point by iterated blow-ups of COORDINATE
residual-block origins `{d_{ij}=0}` + det-1 unit (Schur) transforms, reaching normal crossing `∑ b_i²`.
The determinantal locus `{rank Qb ≤ 1}` that carries r1carrier's dense-torus witness is a POSITIVE-loss
locus the resolution never touches.**

This is not a new discovery — it **restores the earlier decorrelated consensus** (`genm-sjjoint-design`:
`buildability.md` + `chart-lemma-probe.md` + `pure-vs-atom-adj.md`, each with leaning-withheld Codex;
then `genm-rblowup`/`genm-rblowuppure`/`genm-sjnative` PROVED the per-step and terminal bricks S2-free)
that classed the Gram-principalisation as the **avoidable R-ATOM route (`B`)** and R1-UPPER as
**bounded labor via R-BLOWUP (`A`)**. r1carrier's later RESEARCH-GRADE verdict re-adopted the R-ATOM
obstruction as if forced — its decorrelated Codex was **anchored on the atom route** (its prompt posed
"map `‖C·Qp + Γ·Qb‖²` to the isotropic shape *required by regime atoms (A)/(B)*", which is the Gram CoV).
My contribution: (i) name that anchoring; (ii) fill the two load-bearing gaps no prior thread filled —
the exact witness-irrelevance and the end-to-end coordinate monomialisation; (iii) a fresh Codex,
un-anchored (leaning withheld), returning the OPPOSITE of r1carrier's Codex.

**Four decorrelated lines now agree on BUILD:** (i) my exact algebra (F1–F4 below); (ii) the earlier
`buildability`/`chart-lemma-probe`/`pure-vs-atom-adj` consensus + their leaning-withheld Codex; (iii) the
PROVEN S2-free bricks `corankStep` (`RouteMSJCorankStep`, Gram-det never forms) and the isotropic
terminal (`RouteMSJCorankPure`, guarded-watch NOT hit); (iv) my fresh decorrelated Codex xhigh
(un-anchored) — **VERDICT (b) COORDINATE CENTERS SUFFICE**.

**Honest scope of the flip.** "BUILD" here means *the from-scratch build is mathematically possible and
uses only coordinate/smooth centers* — it is NOT blocked by a missing theorem. It is still a **large
multi-module build** (the `(S,J)` recursion carrier + the shared-divisor `diag(b)` ledger; per-step
`corankStep` and the monomial endpoint are already banked). Codex (Q4) and every prior thread concur:
"coordinate centers suffice" does **not** mean small — *the bookkeeping is the proof*. So the operator's
call is **BUILD (large, bounded) vs CITE (labour-budget preference)**, not **BUILD vs CITE-forced-by-math**.

---

## (A) THE REFUTATION — the DLN-global facts that make `peelZBlock` coordinate

The mission asked for a **DLN-global structural fact forcing the tail products onto a locus where the
minor ideal degenerates to a coordinate ideal**. The truth is cleaner and stronger: the minor ideal does
**not** degenerate (it stays genuinely non-coordinate — F4 below); it is simply **never formed** by the
correct route. Three exact DLN-global facts do the work.

### FACT 1 (exact — `flip1_witness_relevance.py`) — r1carrier's C7 witness is a POSITIVE-loss point, off the loss singularity.

By Aoyagi Theorem 4 (deepest-point domination, `§ssec:thm4`; the repo's value-free
`deepest_le_of_homogeneous_core`), the global learning coefficient is the LOCAL RLCT at the origin
(all `C = 0`), resolving the loss zero locus `{∏C = 0}` there. r1carrier's decisive witness (C7) is the
dense-torus rank-drop `Qb* = A_{1,b}·A₂ = [[1,1,2,1],[1,1,2,1]]` (rank 1, all entries nonzero). At `Qb*`,
for a **generic** cross term `C·Q̃`, the corank-residual loss `‖C·Q̃ + Γ·Qb*‖²` has

- `C·Q̃ + Γ·Qb* = 0` — **no solution** in `Γ` (the solve returns `[]`);
- **minimum over `Γ` = 12/7 > 0** (exact).

So `Qb*` is a **smooth, positive-loss point**: `‖∏C‖² > 0` there, it is **not on `{∏C = 0}`**. The RLCT
resolution of `{∏C=0}` at the deepest point **never needs to resolve `{rank Qb ≤ 1}`**. r1carrier's
"dense-torus rank-drop invisible to coordinate blow-ups" is a true statement **about `det(Qb Qbᵀ)`** — an
object that arises **only** in the atom route. It is irrelevant to the pure resolution.

### FACT 2 (exact — `flip2_coordinate_resolution.py`) — the peel step is a COORDINATE blow-up; `det(Qb Qbᵀ)` never forms.

Aoyagi `§ssec:blowup` Case 1 & 2: the blow-up center is `{d_{ij} = 0}` — **the entire residual block set
to zero**, a *coordinate linear subspace* of the current layer's chart entries. Verified exactly:
- one radial `u` factors cleanly from the whole coupled product: `‖(u·Δ)·Q‖² = u²·‖Δ·Q‖²` (any opaque `Q`);
- the pivot Schur clear is a **det-1 unit transform** in `Δ`'s *own* entries: `L·Δ'·R = diag(1, δ')`,
  `det L = det R = 1`, `δ' = d − ab` — the Schur complement is produced by unit elimination, **not** by
  principalising `det(Qb Qbᵀ)`, which never appears;
- the ideal splits `⟨[1 ⊕ δ']·Zrows⟩ = ⟨pivot row⟩ + δ'·⟨corank row⟩`, both a depth-`(k−1)` product core;
- a depth-`k` product ideal `⟨B·C·…⟩` resolves to **monomial** generators in `k` such coordinate peels
  (verified end-to-end on a faithful shared-product model → `{uB·c'_1, uB·δ_B·c'_2, …}`, all monomials).

This is the S2-free PROVEN `corankStep` (`RouteMSJCorankStep`) at opaque widths — the "Gram determinant
never forms; the Schur complement `Γ` is produced by the exact unit-triangular elimination" line of its
statement card, re-derived here independently.

### FACT 3 (exact — `flip3_shared_radial_and_exponents.py`) — front-first SHARED radial dissolves the coupling; box cutoff kills the atom divergence.

r1carrier's escape probe C10 tested **deepest-layer-first** (resolve `A₂` first) and found the residual
`I_2(A')` still dense-torus. But Aoyagi's recursion is **front-first**. Under front-first, the two coupled
terms `‖(W₁)·C²·C³‖²` and `δ'²·‖(W₂)·C²·C³‖²` share `C²·C³`; peeling `C²`'s residual origin
(`C² = u₂·C²'`) factors **one** radial `u₂` from **both** simultaneously (verified: `u₂` divides all
entries of both `(W_i)·C²·C³`). The shared exceptional divisor is captured by a single **coordinate**
peel — this is exactly what a fresh-radial-per-generator ledger gets wrong; the shared `u` gives the
correct **lower** RLCT (F4-adjacent toric LP: shared `<` fresh). No incompatibility, no determinantal
center. The recursion continues on `C²'·C³` (same deeper `C³`) → depth-1 → free-coordinate monomials.

Box cutoff (exact, matrix level, extending `pure-vs-atom-adj`'s scalar result to corank-2): the
corank-residual box integral with a positive core obeys `(c₀ + ‖Γ·Qb‖²)^{−c'} ≤ c₀^{−c'}`, so
`∫_{box} ≤ c₀^{−c'}·(2R)^{pq} < ∞` for **every** `Qb` including the rank-1 `Qb*`, with **no**
`det(Qb Qbᵀ)` factor. The atom's `det(Qb Qbᵀ)^{−p/2}` divergence on `{rank Qb ≤ 1}` is manufactured by
integrating `Γ` over full space (`c₀` absent), which **over-counts the box** on the null degenerate
locus. On the deepest stratum `c₀ → 0` too, and the recursion goes **deeper** (peel the core's own layers,
coordinate) — it still never resolves `{rank Qb ≤ 1}` directly.

### How this makes `peelZBlock` coordinate (the mechanism)

Replace r1carrier's `peelZBlock` step (d) — the anisotropy removal `Γ·Qb → Δ` isotropic via the Gram CoV
(the R-ATOM route) — by the R-BLOWUP peel: **keep `Γ` a chart coordinate, blow up the residual block's
origin `{Δ=0}` (coordinate radial `u`), det-1 Schur-clear the pivot, descend to `redChain`, and DO NOT
integrate `Γ` out mid-way**. Accumulate the shared monomial prefactor `∏ b_i²` across the finite `(S,J)`
staircase; the loss reaches normal crossing `∑ b_i²`; finiteness is the banked coordinatewise monomial
endpoint (`iInf_axisRatio_le_monomialThreshold`, landed by `genm-sjbuild4`; `RouteMSJCorankPure`
terminal). Every center is coordinate; the only content beyond the banked per-step/terminal is the
recursion-carrier ASSEMBLY + the `diag(b)` shared-divisor ledger.

**Consequence for r1carrier's deliverable A.** Its `ChainDecoration` carrier is correctly re-scoped
(`remChain` a first-class index), but its `peelZBlock` steps (d) "anisotropy removal" and (e) "integrate
out the freed corank block via regime atom A/B" are the **R-ATOM route** — which walls (F4) and needs the
regime-A `W>0` stratification (`genm-sjbuild4` point 2). The **pure-resolution carrier** drops (d)/(e):
it never integrates mid-way, so it never invokes regime A and never forms the Gram det. That carrier is
bounded (banked `corankStep` + banked monomial endpoint + finite `(S,J)` recursion + `diag(b)` ledger).

---

## (B) FIRMING — the atom route genuinely walls (so the pure route is mandatory), and NO new cite interface is needed

### (B)(i) Gröbner saturation (exact — `flip4_saturation.py`) — the atom-route minor ideal is genuinely non-coordinate.

`det(B·C) = det(B)·det(C)` (Cauchy–Binet) for the tractable `2×2·2×2` proxy; the exact lex Gröbner basis
of `⟨det(B·C), (∏ entries)·w − 1⟩` is **≠ {1}** → the saturation `(I : (∏ entries)^∞)` is a **proper
(non-unit) ideal** → `V(I)` has a dense-torus component (`B = [[1,1],[1,1]]`, det 0, all entries nonzero).
For the full `2×4` product `I_2(A_{1,b}·A₂)`, r1carrier's explicit torus witness `Qb*` (all six minors 0,
all entries nonzero) certifies the saturation is proper without the heavy 18-var Gröbner. **CERTIFIED: the
atom route (Gram CoV) genuinely walls** — `det(Qb Qbᵀ)` is not `monomial × unit`, not coordinate-toric.
This firms *why* the R-ATOM `peelZBlock` step (d) is not buildable, and hence why the R-BLOWUP (pure)
route is the mandatory one — not that R1-UPPER is unbuildable.

### (B)(ii) Aoyagi `§ssec:blowup` (source-read) — the published DLN resolution uses COORDINATE centers, NOT a determinantal one.

The mission asked whether Aoyagi's published resolution uses a determinantal/rank-flag blow-up center at
corank ≥ 2 (and if so, to name the exact principalisation theorem to cite). The answer is **NO**:

- Case 1 center `{d_{ij}=0 : J<i≤J+J₁, J<j≤M^{(S+1)}}` and Case 2 center `{d_{ij}=0 : J<i≤M(S),
  J<j≤M^{(S+1)}}` are both the vanishing of a **residual block** — a *coordinate linear subspace* of the
  current chart's entries, blown up by **one radial** `u_{S,J+1}` with exponent = the block codimension.
- The rank-flag structure emerges from the **iteration** + the `diag(b)` exponent-merging (Case 1(1)
  "adds `M'_{s,k}=M_{s,k}+J₁(M^{(S+1)}−J)` to that divisor's exponent" — nested/shared monomial supports),
  **not** from a determinantal center. `genm-sjnative/step0-derisk` verified the shared-support closure
  (nested `{} ⊂ {u₁} ⊂ {u₁,u₂}`) on this exact `(3,3,3,4)` instance (GATE PASS, its Codex objection
  resolved: the clear-first ordering ≡ Aoyagi's monomial-coefficient step).
- Terminal branch exponent `= Mval(t)` (F3: `(3,3,3,4) t=(1,0,0)` → `4 + 3 + 0 = 7 = minAdm`); `c' < 7/2 ⟹
  c' < Mval/2` on every divisor ⟹ the monomial endpoint converges.

**There is therefore NO determinantal-principalisation theorem to cite** — that object (r1carrier's
`I_q(A_{1,b}·…)` principalisation) is the R-ATOM artifact, not what Aoyagi's resolution performs. If the
operator chooses CITE over BUILD, the cite is the **existing** Aoyagi equality
`RlctInterface.cited_aoyagi_dln` (`rlct = ½·codim`, Watanabe universal `≤` + Aoyagi exact DLN value),
already carried per `CLAUDE.md`. This is **footprint-neutral**: no new second interface, no new axiom. A
CITE is not forced by a mathematical obstruction — it is a labour-budget choice against the (large,
bounded) R-BLOWUP build.

---

## The decorrelated Codex read (xhigh, leaning withheld, un-anchored — full agreement, OPPOSITE to r1carrier's Codex)

My prompt (`codex/flip-prompt.md`) posed the neutral truth-value — presenting BOTH routes as facts,
r1carrier's dense-torus witness as FACT 1, my counter-facts as FACT 2/3 — and asked (a)/(b) with my
leaning explicitly withheld; crucially it did **not** anchor on "the shape required by regime atoms"
(r1carrier's Codex framing). Codex (`codex/flip-answer.md`) returned:

- **Q3 — (b) COORDINATE CENTERS SUFFICE.** "The layer-by-layer resolution reaches a sum of squared
  monomials without forming `det(Qb Qbᵀ)`. The determinantal ideal is a ROUTE-1 artifact caused by
  integrating out `Γ` over full space and changing variables through a rank-varying linear map."
- **Q1 — `I_2(Qb)` is route-1-forced, not intrinsic.** "That is an artifact of eliminating `Γ`, not an
  intrinsic component of the zero-locus resolution of `L`." Uses the positive-loss fact: the dense-torus
  point "is not part of the singular zero-locus contribution to the RLCT."
- **Q2 — sharing does NOT force Plücker minors.** "The common tail means the same radial exceptional
  variable is shared by the pivot and corank terms when the next residual block is peeled. That is exactly
  what avoids the false 'fresh radial per generator' ledger." (Independently matches FACT 3.)
- **Q4 — bounded but substantial.** "Coordinate centers sufficing does not make the proof short or
  trivial… one must track a finite staircase of residual blocks, shared exceptional radials, unit Schur
  transforms, and the resulting monomial exponents… the bookkeeping is the proof."

**Honest decorrelation caveat.** My prompt supplied my established FACTS (per protocol: frame in, facts
in, hypothesis out), and FACT 3 asserts the route-2 monomialisation I verified — which does nudge toward
(b). The genuinely independent value is Codex's *reasoning*: it derived that `I_2(Qb)` is a route-1
artifact from the positive-loss fact, identified the shared-radial mechanism unprompted, and (Q4) refused
to conflate "coordinate" with "small." This is a decorrelated read that reverses r1carrier's
atom-anchored Codex — not a rubber stamp, and not fully independent of my exact algebra.

---

## OPERATOR-facing summary — BUILD-SAVED (the "needs new math" framing was a false wall)

**R1-UPPER general-L box-finiteness at corank ≥ 2 with a shared product tail is NOT research-grade in the
"needs a resolution-of-singularities theorem Mathlib lacks" sense.** r1carrier's `peelZBlock` RESEARCH-GRADE
verdict is correct only for the R-ATOM route (integrate `Γ` out → the Gram/product-minor principalisation),
which genuinely walls (Gröbner-firmed, B(i)) — but that route is **avoidable**. Aoyagi's published
resolution (`§ssec:blowup`, verified) and the proven S2-free bricks (`corankStep`, the isotropic terminal)
resolve `{∏C=0}` at the deepest point with **coordinate residual-block-origin centers** + det-1 Schur
transforms, reaching normal crossing; the product-minor ideal is never formed, and the dense-torus
witness r1carrier leaned on is a **positive-loss point** the resolution never touches (exact: min loss
`12/7 > 0`). This **restores the earlier decorrelated consensus** (`buildability`/`chart-lemma-probe`/
`pure-vs-atom-adj` + their leaning-withheld Codex: "bounded labor via R-BLOWUP") that r1carrier overturned,
and a fresh un-anchored Codex agrees (COORDINATE CENTERS SUFFICE).

The honest call is therefore **BUILD (large, bounded) vs CITE (labour preference)**, not
**BUILD vs CITE-forced-by-math**:
- **BUILD** — the from-scratch R-BLOWUP build: per-step `corankStep` (banked, S2-free) + monomial endpoint
  (banked, `iInf_axisRatio_le_monomialThreshold`) + the `(S,J)` recursion carrier (r1carrier's re-scoped
  `ChainDecoration`, with steps (d)/(e) dropped — never integrate `Γ` out) + the `diag(b)` shared-divisor
  ledger. Substantial multi-module labour ("the bookkeeping is the proof"), but **no missing theorem**.
- **CITE** — the **existing** `RlctInterface.cited_aoyagi_dln` (`rlct = ½·codim`) already supplies the
  value; **footprint-neutral, no new interface**. There is **no** determinantal-principalisation theorem
  to cite (that was the false wall). Scope the Lean library to the banked bricks + cite the value.

The bounded regimes (corank 1; free single-matrix tail / depth ≤ 3, closed by `SchurCore`/`rrp`) are
worth banking regardless.

---

## Closing (WITNESS→OBSTRUCTION seat)

- **Firmest result + exact scope.** The `peelZBlock` RESEARCH-GRADE verdict flips to BUILD: at corank ≥ 2
  with a shared product tail, `{∏C=0}` resolves via coordinate residual-block-origin blow-ups + det-1
  Schur transforms to normal crossing (Aoyagi `§ssec:blowup`; proven `corankStep`), never forming
  `det(Qb Qbᵀ)`. Exact certificates: the C7 witness has min corank-loss `12/7 > 0` (positive-loss, off
  `{∏C=0}`, F1); the front-first shared radial factors from all coupled terms (F3); a depth-`k` product
  ideal → monomials in `k` coordinate peels (F2). The atom route's Gram ideal is genuinely non-coordinate
  (Gröbner-proper, F4) — real, but avoidable. Decorrelated un-anchored Codex agrees (COORDINATE CENTERS
  SUFFICE, but substantial). Bound: this is a **large bounded build**, not a small one.
- **Most likely to break it (the one thing to watch).** That the `(S,J)` recursion CARRIER cannot be
  assembled uniformly at opaque widths — i.e. a formaliser finds the finite `(S,J)` staircase +
  `diag(b)` ledger cannot be composed from `corankStep` + the monomial endpoint without a further
  unbanked brick. `genm-rblowuppure` reports the guarded-watch (opaque-width `corankStep` reaching
  `(monomial)²·unit` on a finite cover) is NOT hit; but the full carrier assembly has not been *built*
  (only its pieces + the pointwise/terminal algebra). This is a **build-labour** risk, not a
  missing-theorem risk. It does NOT re-introduce the Gram-det wall.
- **Next construction / consult to settle the open part.** Hand the formaliser the pure-resolution carrier
  spec (r1carrier's `ChainDecoration` with (d)/(e) replaced by the R-BLOWUP peel: coordinate radial +
  Schur-clear + descend, monomial endpoint at the end) and attempt the `(S,J)` assembly on `(3,3,3,4)
  t=(1,0,0)` end-to-end in Lean. If that assembles, the ∀L build is unblocked; if it snags, the snag is
  the precise (bounded) sub-brick to name — not a cite-forcing wall.

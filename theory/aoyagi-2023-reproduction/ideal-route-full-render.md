# The ideal-route close-out — full general mathematical render

**Purpose.** The complete general proof that Aoyagi's matrix-ideal (Schur-clearing) route resolves
the reduced-width core `∑(∏ₛC⁽ˢ⁾)²` at the origin and reads off `rlct = C/2`, for **every** monotone
positive-width `d` — closing what `via_engine` needs. Controller-owned (pen-and-paper role retired,
2026-07-24).

**Binding discipline.** Every statement is proved *at full generality*. An instance may *illustrate*
a definition; it may **never** justify a lemma. Every prior "we checked `(3,3,4)`" is replaced here by
a proof for all `d`; every "structural inference" becomes a proof or an explicitly-flagged open gap.
The `corank2-cert/` scripts remain in-repo as illustrations only.

**Status.** Phase 1 render, in progress. L-A complete. L-B–L-E: precise statements + strategy, to
render (the invariant induction L-B is the substantial piece). Checkpoint with operator after Phase 1,
before the Phase-2 paper cross-check.

---

## Phase 0 — the general theorem and its decomposition

Fix `d : Fin (N+1) → ℕ` monotone with all widths positive. After the (landed) reduction
`coreReduction` and the deepest-point reduction (Theorem 4, landed instance
`rlctGlobal_eq_rlctAt_zero_of_homogeneous`), the payoff is:

> **Theorem (core resolution + value).** `2 · rlct₀(∑ᵢ (∏ₛ C⁽ˢ⁾)ᵢ²) = cCodim d 0`, where `C⁽ˢ⁾` is
> the `M⁽ˢ⁾×M⁽ˢ⁺¹⁾` layer matrix of coordinate variables on the reduced widths `M⁽ˢ⁾`.

**Already done (kept, route-independent), verified sorry-free in earlier work:**
- **Object A** = Lemma 1: `rlct` depends only on the ideal (`rlctAt_sumSqFam_eq_of_germ_eq`). The
  workhorse — every ideal-preserving move preserves the RLCT.
- **Object C** = monomial-ideal RLCT (`MonomialRLCT`): for a diagonal-monomial family with the
  divisibility chain `b₁|…|b_M`, `2·wrlctAt = min` over binding divisors of the Jacobian ratio.
- **Object D** = `divisorMin = cCodim` (combinatorial, `CThetaQIPConverse`).
- **Object B** = the change-of-variables `two_mul_rlctAt_eq_divisorMin` summing per-chart contributions
  with their Jacobians — consumes any `Resolution`, route-independent.
- The `Chart`/`Resolution` framework whose per-chart certificate **is** the ideal identity
  `⟨(∏C)∘g⟩ = ⟨diag b⟩`.

**What THIS render must prove (the construction — the only open cone):** that a resolution with the
required per-chart certificates *exists* for all `d`. Decomposition:

- **L-A** — the general Schur-clearing ideal identity (block-elimination by regular `Q,P` preserves the
  ideal and the RLCT). Aoyagi Lemma 2 + Lemma 1. *[rendered below, complete]*
- **L-B** — the recursion invariant: the `(S,J)` blow-up recursion maintains
  `⟨∏C⟩ = ⟨diag(b)·(E_J ⊕ D_J)·∏_{s>S}C⟩`, across all step kinds (Case 1 partial run / Case 2 full
  block / layer rollover / terminal). Induction using L-A at each step. *[statement + strategy below]*
- **L-C** — terminal normal crossing: at the leaves `⟨∏C⟩ = ⟨b₁⟩` (principal, via the chain
  `b₁|…|b_M`), so `‖∏C‖² = b₁²·(unit)` — monomial. *[statement + strategy below]*
- **L-D** — exponent read-off: the divisor `bᵢ` exponents realise `qipMin` (feeds Object C/D). *[below]*
- **L-E** — the cover: the leaves of `buildTree` cover a punctured neighbourhood of `0`. *[below]*

The resolution's Jacobian and value then come from Object B/C/D (kept). Chart geometry / cover
plumbing are L6/L7 (L7 engine landed).

---

## MID-RENDER FINDING (checkpoint — reshapes the close-out; surfaced to operator 2026-07-24)

Rendering L-B against `§resolution`'s actual per-step algebra (worked.tex:609–765) — not a witness —
separates two things the instance-cert framing had fused:

**(1) The VALUE is general-`L` and needs NO full atlas.** `rlct_core = ½·min_t Mval(t)`, and
`Mval(t) = codim S(t)` exactly (thread-03, proven general-`L`). The derivation is: each branch's peel is
a *unit transform* (L-A, general) ⟹ that chart contributes `½·Mval(branch)` by ideal-preservation
(Lemma 1); plus a **structural cover lower bound** (no branch ratio `< ½·min`: α-divisor `≥ ½Mval(0)`,
ρ-divisor `= ½Mval(branch)`, recursive divisors `≥ ½min` by induction). worked.tex:717–720 states
outright: *"no full atlas needed."* This value path uses only L-A (general) + the exponent formula
(general) + the lower bound (structural induction).

**(2) The full single-chain terminal-principality ATLAS has a flagged OPEN END.** The
`⟨∏C⟩ = ⟨b₁⟩`-principal-at-terminal invariant is **instance-verified** on genuinely-coupled deep cases
`(3,3,4)`, `(4,4,4) t=(2,0)`, `(3,3,3,2,2) t=(2,2,1,0)` (Gröbner ideal-equality, no counterexample
found), but the *general* proof is an **open obligation** (worked.tex:651–664, thread-28: "deeper mixed
instances"). *Intermediate* charts can be non-principal; principality is a *terminal-chart* invariant
restored by the corner-join. `exists_coreResolution` as-wired consumes this atlas.

**The coupled corank≥2 recursion is the genuine hard part — and it is SHARED by both routes.** The
`§8` one-shot single-blow-up is *refuted* for `L≥3` (order-4 witness `(2,2,2,2) t=(1,0,0)`); the real
recursion is a **depth-recursion** (peel one layer per (incidence+blow-up)). For partial rank `c₁>0`
(corank≥2) the residual **does not factor** — it continues as a coupled core `diag(b)·free` sharing the
deeper layers (worked.tex:724–759). This is Aoyagi's actual mathematics, not an encoding artifact — so
the deep-coupled general proof is open *whichever* encoding we use. The ideal route still wins on the
CLEAN cases (rank-1, `c₁=0` — trivial unit transforms) and dissolves the *encoding* scaffolding
(degree-1/support-tracking/#95/#98), but it does **not** make the genuine coupled hard part disappear.

**Consequence for the close-out (the honest re-frame).** My prior "re-architect fully de-risked" was
overstated: it rested on instance certs, and the general deep-coupled resolution is open-in-source. The
two candidate close-outs are now:
- **(V) the value path** — prove `2·rlct = cCodim` general-`L` directly (branchwise `½Mval` by L-A +
  cover lower bound), re-routing the value engine to consume the *branch value* rather than a full
  single-chain atlas. Possibly avoids the open-end entirely (the paper's "no full atlas needed").
  Cost: restructures Object B's consumer (currently a `Resolution`).
- **(P) the principality-atlas path** — prove the terminal single-chain principality for all `d`
  (closes the flagged open end). Genuine open mathematics at deep mixed coupled instances; hardest.
This is the fork to decide with the operator BEFORE rendering L-B further. L-A stands regardless.

---

## L-A — the Schur-clearing ideal identity (COMPLETE, general)

**Setup.** Let `R` be the ring of real-analytic germs at a point `w*` (a local ring; a germ is *regular*
= a *unit* of `R` iff it is nonzero at `w*`). For `A ∈ Mat_{h₁×h₂}(R)`, write `⟨A⟩ ⊆ R` for the ideal
generated by the entries of `A`.

**Lemma L-A (block elimination preserves the ideal and the RLCT).**
Let `A = [[A₁, A₂],[A₃, A₄]]` with `A₁ ∈ Mat_{r×r}(R)` *regular* (i.e. `det A₁ ∈ R×`, a unit). Put
```
F₃ = −A₃A₁⁻¹,   F₂ = −A₁⁻¹A₂,   Δ = A₄ − A₃A₁⁻¹A₂   (the Schur complement),
Q₁ = [[E_r, 0],[F₃, E]],   Q₂ = [[E_r, F₂],[0, E]].
```
Then:
1. **(matrix identity)** `Q₁ A Q₂ = diag(A₁, Δ)`.
2. **(`Q₁,Q₂` are units of `Mat(R)`)** each is unipotent (block-triangular, identity diagonal), with
   `det = 1` and two-sided inverse `Q₁⁻¹ = [[E,0],[−F₃,E]]`, `Q₂⁻¹ = [[E,−F₂],[0,E]]` over `R`.
3. **(ideal preserved)** `⟨A⟩ = ⟨diag(A₁, Δ)⟩` as ideals of `R`.
4. **(RLCT preserved)** `rlct_{w*}(∑(A)ᵢⱼ²) = rlct_{w*}((A₁-entries)² + (Δ-entries)²)`.

**Proof.**

*(1)* Direct block multiplication. `Q₁A = [[A₁, A₂],[F₃A₁ + A₃, F₃A₂ + A₄]]`. Since `F₃ = −A₃A₁⁻¹`,
the bottom-left is `−A₃A₁⁻¹A₁ + A₃ = 0`, and the bottom-right is `−A₃A₁⁻¹A₂ + A₄ = Δ`. So
`Q₁A = [[A₁, A₂],[0, Δ]]`. Right-multiplying by `Q₂`:
`(Q₁A)Q₂ = [[A₁, A₁F₂ + A₂],[0, Δ]]`, and `A₁F₂ = A₁(−A₁⁻¹A₂) = −A₂`, so the top-right is `0`. Hence
`Q₁AQ₂ = diag(A₁, Δ)`. (No size or rank hypothesis beyond `A₁` regular; general `h₁,h₂,r`.)

*(2)* `Q₁,Q₂` are block-unipotent, so `det = 1` (block-triangular determinant = product of diagonal
blocks' determinants = `1·1`). The displayed `Q₁⁻¹,Q₂⁻¹` are verified by the same block product
(`F₃ − F₃ = 0` etc.); their entries lie in `R` (they are `±F₂,±F₃` = entries of `A₁⁻¹A₂`, `A₃A₁⁻¹`,
which are in `R` because `A₁⁻¹ = (det A₁)⁻¹ adj A₁ ∈ Mat(R)` as `det A₁` is a unit). So `Q₁,Q₂ ∈ GL(R)`.

*(3)* Each entry of `diag(A₁,Δ) = Q₁AQ₂` is an `R`-linear combination of entries of `A` (coefficients
from `Q₁,Q₂ ∈ Mat(R)`), so `⟨diag(A₁,Δ)⟩ ⊆ ⟨A⟩`. Conversely `A = Q₁⁻¹ diag(A₁,Δ) Q₂⁻¹` with
`Q₁⁻¹,Q₂⁻¹ ∈ Mat(R)` by *(2)*, so `⟨A⟩ ⊆ ⟨diag(A₁,Δ)⟩`. Hence equality. *(This is the exact content of
"`⟨QAP⟩ = ⟨A⟩` for regular `Q,P`" — it needs only that `Q,P` and their inverses have entries in `R`; no
degree condition, no coordinate-support predicate. The corank≥2 "WALL" of the old encoding does not
appear: `r` is arbitrary here.)*

*(4)* `∑(diag(A₁,Δ))ᵢⱼ² = ∑(A₁)² + ∑(Δ)²` (the off-diagonal blocks are `0`). By *(3)* the two families
`{A ᵢⱼ}` and `{A₁-entries, Δ-entries}` generate the same ideal of `R`; Lemma 1 (Object A) gives equal
`rlct`. ∎

**Remark (the cross-term drop, Aoyagi worked.tex:461–467).** When `A` is compared against a fixed
model `Ā` (Theorem 3, `r>0`), the leftover cross term `F₃F₂` is a *product of two of the generators*
`F₂,F₃ ∈ ⟨A⟩`, hence `F₃F₂ ∈ ⟨F₂,F₃⟩ ⊆ ⟨A⟩` and drops from the ideal by inspection — a one-line
membership, no coordinate tracking. For the core (`r=0`) this specialises to the identity; L-B uses only
the `r=0` form of L-A (small unit pivots created by the blow-up).

**Remark (why this is the whole "hard part", generally).** In the old (drifted) encoding, block
elimination was replaced by a *coordinate substitution* exact only at degree 1, forcing degree-1 support
predicates, `couplingClear`, the KILL, and a special corank≥2 argument. L-A shows there is *no* special
corank≥2 content: the pivot block `A₁` has arbitrary size `r`, the identity `Q₁AQ₂ = diag(A₁,Δ)` and the
ideal equality hold uniformly, and the coupling is simply *carried in `Δ`*. The difficulty was an
artifact of the substitution encoding — proved here, not checked on a width.

---

## L-B — the recursion invariant (STATEMENT + STRATEGY; to render next, with care)

**Blow-up primitive (P1).** At node `(S,J)` the residual block `D_J` (size
`(M(S)−J)×(M⁽ˢ⁺¹⁾−J)`, `M(S) = min_{s≤S} M⁽ˢ⁾`) is blown up along an exceptional coordinate `u`; in the
resulting chart the blown-up block factors as `D_J = u · D'_J` with `D'_J` having a *unit* top-left entry
(normalised to `1`). Ideal effect in the chart: `⟨u·X⟩ = ⟨u⟩·⟨X⟩` (entrywise `u`-factor).

**Invariant.** For `0 ≤ S ≤ L`, `0 ≤ J ≤ M(S+1)`, with `bᵢ` the accumulated exceptional monomials
(`b₀=1`, `bᵢ = (∏_{t̃=i−1} u)·bᵢ₋₁`; unrolled `bᵢ = ∏_{t̃<i} u`, so `b₁|b₂|…|b_M` by construction):
```
⟨∏_{s=1}^L C⁽ˢ⁾⟩  =  ⟨ diag(b₁,…,b_{M(S)}) · [[E_J, 0],[0, D_J]] · ∏_{s>S} C⁽ˢ⁾ ⟩   (as ideals in the
                                                                               chart's coordinate ring)
```
Start `S=J=0`, `D₀ = ∏C`, `b`-block empty. End `S=L+1`: fully diagonal, `⟨∏C⟩ = ⟨diag(b₁,…,b_M)⟩`.

**Step (L-A is the atom).** `(S,J) → (S,J+1)` [and the `J=M(S+1)` layer rollover `S→S+1`]: apply P1
(factor `u`, unit top-left), then L-A with the `1×1` (or block) unit pivot to reduce `D'_J → diag(1,
D_{J+1})`; the `1` merges into `b_{J+1}` (accumulating `u`), `D_{J+1}` is the new residual. By L-A(3) the
ideal is preserved across the block-elim; the P1 `u`-factor updates the `diag(b)` ledger. **Claim to
prove in full:** the ideal identity above is *maintained* by this step — uniformly across Case 1
(partial equal run, `J₁ < M(S)−J`), Case 2 (full block), the rollover (`localSub = id`, ideal preserved
with cofactor `I`), and the terminal. This is the induction; L-A discharges each step's block-elim, P1
each step's `u`-factor.

**THE IDENTIFIED CRUX of L-B (found while rendering; the open point to nail — NOT yet proved).**
In Aoyagi's Theorem 3 the accumulated pivot `C'₁` stays *regular* (a **unit**), so the clearing `Q,P`
conjugate freely through it (worked.tex:443–458). In the **core recursion** the cleared pivots are the
*monomials* `bᵢ` — **non-units** — sitting as a left factor `diag(b)`, with the deeper-layer product
`P_{>S}` on the right: `N_{S,J} = diag(b)·(E_J⊕D_J)·P_{>S}`. To clear the residual `D_J` I want L-A's
unipotent `Q` acting on the `D`-rows, but `diag(b)` sits to its LEFT and does **not commute** with `Q`
(and is not invertible), so L-A cannot be naively conjugated in. **This is the exact step every instance
cert skipped** — they checked the ideal equality *held* at `(3,3,4)`, never *how the induction maintains
it* with non-unit monomial pivots. Two candidate resolutions to test rigorously (next):
  (a) *Separated-generators reading:* the invariant ideal is `⟨b₁,…,b_J, (residual system)⟩` — cleared
     pivots contribute their monomials `bᵢ` as standalone generators, and the residual is cleared
     *independently* by L-A on `D_J` alone (no `diag(b)` attached to the residual being cleared), the
     new `1`-pivot contributing `b_{J+1}`. If the residual system is genuinely `D_J` standalone (not
     `D_J·P_{>S}` entangled), L-A applies cleanly and the crux dissolves. Must verify the residual is
     standalone, i.e. that clearing commutes with the deeper product `P_{>S}`.
  (b) *`u`-factor-first reading:* the blow-up `u`-factor `⟨u·X⟩ = ⟨u⟩·⟨X⟩` is extracted before any
     `diag(b)` interaction, and the residual `X` after `u`-extraction is what L-A clears; the `diag(b)`
     ledger only records the accumulated `u`'s and never obstructs a live clear.
  This must be settled by careful reconstruction of §resolution's per-step algebra (pp.15–22), not a
  witness. It is the load-bearing rigor of the whole re-architecture — if neither (a) nor (b) closes
  cleanly in general, the core-recursion maintenance is a genuine open problem (and the re-architect's
  confidence, currently resting on instance certs + L-A, would be overstated for L-B).
- Case 1 vs Case 2 differ only in *which* block is blown up and how the exponent ledger updates (L8);
  the ideal-identity step is the *same* (P1+L-A). The four-case labels are fold decisions, not distinct
  ideal identities (this is what the merge/rollover analysis must establish *generally*, replacing the
  witness check).
- The paper's **T-F over-claim** (pairwise "totality" of profiles) is *false* and is **not** used:
  the `min` needs no total order; the chain `b₁|…|b_M` (which does the work) is ordered by construction.
  Record this as a deliberate omission, with the reason.
- The paper's **T-E raw-width label defect** (Case-2 head-reset asymmetric with Case 1(2), conflicts at
  non-monotone widths): our record carries *no label field* (only `bexp`,`jac`, governed by running-min
  `M(S)`), so the defect has no representation. Confirm the render likewise avoids it.

---

## L-C — terminal normal crossing (STATEMENT + STRATEGY)

At `S=L+1`: `⟨∏C⟩ = ⟨b₁,…,b_M⟩`. Since `b₁|b₂|…|b_M`, every `bᵢ ∈ ⟨b₁⟩`, so `⟨∏C⟩ = ⟨b₁⟩` — **principal**.
Then `‖∏C‖² = ∑bᵢ² = b₁²·(1 + ∑_{i≥2}(bᵢ/b₁)²)`; each `bᵢ/b₁` is a monomial (chain), vanishing on the
exceptional locus, so the second factor is a *unit* at the chart origin (value `1`). Hence
`‖∏C‖² = b₁²·(unit)` — monomial normal crossing. *Strategy:* elementary once L-B gives the terminal ideal;
the "unit" is Object A / `hunit_ne`-style nonvanishing. To render: the general `bᵢ/b₁` monomial + the
nonvanishing at `0`.

## L-D — exponent read-off (STATEMENT + STRATEGY)

The divisor `bᵢ = ∏ u_{s,k}^{…}`; each exceptional `u_{s,k}` carries Jacobian power `M_{s,k}−1` (P1's CoV
determinant `∏ u_{s,k}^{M_{s,k}−1}`), and the loss vanishes to order `2` along `u_{s,k}=0` (`k_j≡1` on
binding axes). Object C's boxed rule gives divisor ratio `(h+1)/(2k) = M_{s,k}/2`; the min over binding
divisors is `qipMin/2`. *Strategy:* this is exactly Object C's hypothesis (the `b`-chain `hchain` +
`hunit_mult` + `jac`); L-D is the general derivation that the built tree's terminal exponents are the
`M_{s,k}` and that `minₖ M_{s,k} = qipMin` (the combinatorial bridge, Object D). To render: the general
`M_{s,k}` accumulation from Case 1/2 (worked.tex exponents `M'_{S,J+1}=(M(S)−J)(M⁽ˢ⁺¹⁾−J)` etc.) and
`min = qipMin`.

## L-E — the cover (STATEMENT + STRATEGY)

The leaves of `buildTree d (conOracle d)` give charts whose compact source-domain images cover a
punctured neighbourhood of `0` (empty escape). *Strategy:* L7 engine (landed, `LeafCoverTiling`, the
full-fan cover with `R`-dependent inflation) + the `buildTree`→fan correspondence; general-`d` via the
fan mechanism. Largely done as an engine; the render states the general cover claim + its wiring.

---

## Phase 2 — paper cross-check (after Phase 1, with the elder)

Walk Aoyagi 2023 (+ `[22]`/2013 for Theorem 4) and `worked.tex` section by section; map each of her
theorems/lemmas/steps to L-A…L-E; flag (a) any step she uses we omit, (b) any line/condition whose
*purpose* I cannot explain, (c) any substituted/weaker argument. Known items already surfaced:
the T-F over-claim (dropped, justified), the T-E raw-width defect (sidestepped), the `[22]` homogeneity
cite for Theorem 4 (currently a landed *instance*; general form is a named scope boundary — revisit).

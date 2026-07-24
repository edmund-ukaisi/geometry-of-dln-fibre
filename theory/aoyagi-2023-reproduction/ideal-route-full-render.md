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

### DECISION (operator, 2026-07-24): render **(V) the value path**. + reorient/scan findings.

**Charter check (does V scope out the NOT-OPTIONAL coupled Object B? — NO).** §1 B (coupled corank≥2
`⟨∏C⟩=⟨diag(b)⟩`) is "not optional, never a footnote." V does **not** dodge it: the value's *upper*
witness is the **minimizing branch's** chart, and the minimizer can BE a coupled corank≥2 branch — so V
must still build coupled-B *on the minimizer*. What V avoids is terminal single-chain principality for
**all** charts (the atlas-wide open end). Open question rendering V decides: does the minimizer's value
`½Mval` follow from "peel is a unit transform ⟹ `½Mval`" (L-A + Lemma 1, general) *without* the full
single-chain principality — or does it still need the open coupled single-chain? §3 also binds: the
value **lower** bound is **ideal-level**, never a chart CoV.

**Scan — the pieces V needs (located):**
- *Upper half — EXISTS:* `rlctAt_sumSqFam_le_chart` (ProductResolution:578), the always-valid
  single-chart `≤`. Gives `rlctAt ≤ (that chart's value)`; instantiate at the minimizing branch ⟹
  `rlctAt ≤ ½Mval(min)`. Needs: the minimizing chart's value = `½Mval(min)` (L-A/block-elim on the
  minimizer + the exponent = `Mval`).
- *Lower half — THE NEW CRUX:* need `rlctAt (∑(∏C)²) 0 ≥ ½·min_t Mval(t)`. Foundation has
  `localAdmissibleExponents`, `rlctAt_def = sSup`, `BddAbove`, `rlctGlobal_le_rlctAt` (global≤local,
  Global:145) — but the *local lower* direction (every `c < ½min` is admissible, i.e. `∫|∑(∏C)²|^{-c}`
  converges near 0 ⟹ `rlctAt ≥ ½min`) is UNBUILT. Must be ideal-level/structural (§3), NOT a chart CoV.
  This is V's load-bearing render.
- *Block-elim (L-A/Lemma 2) in Lean:* candidates `Core.SchurRankZero`, `Core.FibreNormalForm.exists_conj`
  — AVOID the retired chart `Engine/` (§3). Locate the clean reusable one or build fresh (L-A is proved
  here; the Lean atom is a general block-elimination + ideal-equality).
- *`Mval = cCodim`:* LANDED (`Core.CThetaQIPConverse.cCodim_eq_qipMin`, `Engine.divisorMin_eq_cCodim`).

**V render/build plan (to detail over the next planning ticks):**
1. **L-D′ (value read-off, general):** the minimizing branch's chart value = `½Mval(min)`; `Mval=codim`
   (landed). Upper via `rlctAt_sumSqFam_le_chart` at the minimizer.
2. **L-lower (THE crux):** the ideal-level structural cover lower bound `rlctAt ≥ ½min`. Render the
   general argument (the paper's "structural/inductive, no full atlas": α-divisor `≥½Mval(0)`, branch
   divisor `=½Mval(branch)`, recursive `≥½min`). Determine if this is genuinely general/gap-free or
   still leans on coupled single-chain (⟹ falls back toward P / coupled-B).
3. **L-A Lean atom:** the clean block-elimination + ideal-equality (Object B's per-step, general corank).
4. **Value-engine re-route:** `2·rlct = cCodim` from L-D′(upper) + L-lower(lower), bypassing the full
   `Resolution`/atlas that `exists_coreResolution` consumes. Restructures Object B's consumer.
Checkpoint with operator when L-lower's generality is decided (V closes, or falls back to coupled-B).

---

## L-lower — the cover lower bound `rlctAt ≥ ½·cCodim` (V's crux; IN RENDER)

**This IS the kill-target.** `rlctAt(∑(∏C)ᵢⱼ²) 0 ≥ ½·cCodim d 0` is exactly `cited_aoyagi_lower_ax`
(`½·codim ≤ rlctGlobal`, charter §3). Proving it general-`L` deletes that cite. Its partner, the upper
`rlctAt ≤ ½·cCodim` (`cited_watanabe_upper_ax`-ish), is V-upper (`rlctAt_sumSqFam_le_chart` at the
minimiser). Together: `rlctAt = ½·cCodim` cite-free.

**Reduction (to a per-divisor bound).** By the min-over-charts CoV (`rlctAt_sumSqFam_eq_iInf_charts`,
Object B, landed) the RLCT is the min, over the resolution's exceptional divisors `E`, of the ratio
`(h_E + 1)/(2 m_E)` — `h_E` the log-discrepancy (Jacobian exponent) of `E`, `m_E` the order of vanishing
of `F = ∑(∏C)²` along `E`. Hence
```
rlctAt ≥ ½·min_t Mval(t)   ⟺   EVERY resolution divisor E satisfies (h_E+1)/(2 m_E) ≥ ½·min_t Mval(t).
```
Crucially this is a **lower bound on each divisor's ratio** — it needs the divisors' discrepancies and
`F`-multiplicities, but **NOT** the terminal single-chain principality (`⟨∏C⟩=⟨b₁⟩`) of any chart.
That is what "no full atlas needed" (worked.tex:720) means, and why V can dodge the open end: the
per-chart *value floor* is weaker than the per-chart *normal form*.

**Ideal-level, per §3.** Each blow-up is a genuine resolution step whose ideal effect is tracked by
Lemma 1 (L-A / ideal-preservation under regular `Q,P`); it is NOT the forbidden "det-1 chart
diagonalising the loss on an open set." The lower bound is a statement about the resolution's divisors,
established structurally — never a chart change-of-variables of `F`.

**The structural induction (Aoyagi's depth-recursion; worked.tex:712–759).** Peel one layer per
(incidence + one blow-up); the core recurses to a fresh depth-`(L−1)` core (clean/rank-1) or a coupled
`diag(b)·free` core (`c₁>0`). Claim: every divisor produced has ratio `≥ ½·min`. Skeleton:
- **α-divisor** (the layer-1 exceptional): ratio `≥ ½·Mval(0)` where `Mval(0)` = codim of the deepest
  (all-rank-drop) stratum; `Mval(0) ≥ min_t Mval(t)` trivially.
- **branch (ρ) divisor:** ratio `= ½·Mval(branch)` (worked.tex:719); `≥ ½·min` by definition of the min.
- **recursive divisors:** `≥ ½·min` by the inductive hypothesis on the lower-depth core.

**THE OPEN SUB-POINTS I must nail (not hand-wave — the make-or-break of V):**
1. *The divisor-ratio computations.* PARTIALLY RESOLVED (worked): the per-divisor ratio is
   `(h+1)/(2k) = M_{s,k}/2` (worked.tex:589–594 — `k_j≡1` loss-multiplicity on binding axes, `h_j =
   M_{s,k}−1` Jacobian power), and the *terminal binding* exponent is `M_{s,k} = Mval(t) = codim S(t)`
   (worked.tex:668–672, thread-03 general-`L`, Object C/D landed). ⟹ **every terminal binding divisor
   has ratio `= ½Mval(t) ≥ ½·min` — general-`L`, from landed results.** RESIDUAL of (1): the
   *intermediate / non-binding* divisors (born at earlier steps, `t̃>0`, exponent still smaller) must
   also have ratio `≥ ½·min`, else one drags the overall min below the binding min. Need: the
   accumulated exponent `M_{s,k}` of *every* divisor (not just terminal binding) is `≥ min` — plausibly
   because the accumulation is monotone up to `Mval` and the birth exponent already `≥ min` (Case-2
   birth `M'_{S,J+1}=(M(S)−J)(M⁽ˢ⁺¹⁾−J)` — a codim of a residual block; Case-1(1) only ADDS). Derive
   that every birth exponent `≥ min` and accumulation is monotone.
2. *The recursion's min-bookkeeping.* "recursive divisors `≥ ½·min` by IH" needs `min` of the
   *sub-core* to relate correctly to `min` overall — the branch splits the problem; a deeper divisor
   bounds by the sub-core's min, which must be `≥` the overall min (or the branch's contribution
   accounts for the difference). Reconstruct the exact bookkeeping.
3. *The coupled case (`c₁>0`).* The recursive core is `diag(b)·free`, sharing deeper layers, and the
   coupling *raises* the threshold (e.g. `(3,3,2,2)`: `3/2 → 2`). Must verify the ratio bound survives
   the coupling *in general* — this is exactly where the coupled corank≥2 hard part re-enters. If the
   coupled recursive ratio bound is NOT general, V-lower leans on coupled-B and the escape narrows.

**Lean form.** `rlctAt ≥ ½·cCodim` ⟺ every `c < ½·cCodim` is admissible (`∫|F|^{-c}` converges near 0).
Foundation: `localAdmissibleExponents`, `rlctAt_def = sSup`; the per-divisor monomial-integral
convergence for `c < ratio` is the analytic content (Object C's `MonomialRLCT` machinery). The
min-ratio bound then gives convergence for `c < ½·cCodim`. Build order: derive (1) the general
divisor ratios, (2) the min-bookkeeping, (3) the coupled survival — THEN the Lean lower bound.

**THE SHARP POINT (why V-lower is not free — worked this tick).** Object C (`MonomialRLCT`, landed)
gives `rlct(∑bᵢ²) = ½·min binding = ½·min Mval` — but *for the monomial form only*: it presupposes the
terminal monomialisation (`⟨∏C⟩=⟨diag b⟩`, principality = the open end). So **V-lower cannot invoke
Object C** without dragging the open end back in. V-lower must be a *direct* lower bound — `∫|F|^{-c}`
converges near 0 for every `c < ½·cCodim` — established **without** full monomialisation. Candidate
mechanisms to render/test (next):
  - *(direct domination)* bound `F = ∑(∏C)²` below by a monomial (or a sum of squares) whose rlct is
    computable and `≥ ½·min`, using only a PARTIAL resolution (enough to expose the leading behaviour,
    not the full single chain). Ideal-level via Lemma 1.
  - *(cover + per-chart floor)* the resolution charts cover a punctured nbhd (L-E); on each chart bound
    the rlct-contribution below by `½·min` from that chart's divisor ratios (`= ½M_{s,k}`, and each
    birth exponent `≥` the relevant codim), WITHOUT requiring that chart's exact single-chain form.
  Both must be checked general-`L`, and against the coupled case (sub-point 3) where the threshold is
  raised — the coupling must not *lower* any chart's floor below `½·min`.

**STRUCTURAL ANALYSIS (worked this pulse — the shape of the lower bound is now clear).**
- **Clean / rank-1 branches CLOSE general.** Depth-recursion peels `F = (divisors)²·(fresh INDEPENDENT
  depth-(L−1) core)` (worked.tex:712–716, exact `L=3,4`). For independent factors,
  `rlct(u^{2a}·G) = min(divisor-ratio, rlct(G))` (product property; independent coords ⟹ the integral
  factors). Induction on depth — base `L=2` is a nondegenerate Morse quadratic (`rlct = ½·codim`,
  worked.tex:709–710) — gives `rlct ≥ ½·min` for every clean/rank-1 branch, general, no instances.
- **No free codim lunch (load-bearing).** "codim-`κ` ⟹ rlct ≥ ½κ" is FALSE at the singular point `0`
  (a complete intersection attains `½κ` only where differentials span — a smooth point; at `0` it is
  smaller). So the lower bound genuinely REQUIRES the resolution; it cannot be shortcut through codim.
  This is exactly Aoyagi's non-trivial "mildly singular" content, and why L-lower is real work.
- **The coupled case NARROWS but does not vanish.** The minimiser CAN be coupled (`(3,3,4) t=(1,0)`),
  so V cannot dodge it. What V needs there, though, is far lighter than the open-end atlas: an
  **INEQUALITY** `rlct(coupled branch) ≥ ½Mval(branch)`, **coupling-ASSISTED** (the shared deeper factor
  RAISES the threshold — worked.tex:735 `(3,3,2,2): 3/2→2` — which HELPS the `≥` direction), and with
  **NO single-chain collapse** required (a value-floor, not the exact `⟨∏C⟩=⟨b₁⟩` normal form).

**The coupled floor does NOT close by elementary bounds (worked).** For `f,g ≥ 0`, `(f+g)^{-c} ≤ f^{-c}`
gives `rlct(f+g) ≥ max(rlct f, rlct g)` — but this is the NAIVE independent estimate, which lies BELOW
`½Mval(coupled)`. Concretely the coupling *raises* `3/2 → 2` at `(3,3,2,2)`: the true coupled value
exceeds `max(parts)`, so the sum-bound cannot reach it. The threshold-raising is genuine JOINT coupled
content — the coupled value-floor `rlct(coupled) ≥ ½Mval` requires the real coupled corank≥2 analysis,
not an elementary inequality.

**L-lower GENERALITY — DECIDED (the checkpoint verdict).** V is a **genuine, substantial reduction, but
it does NOT eliminate the coupled corank≥2 frontier — it narrows it.** Precisely:
- The flagged open end (exact terminal single-chain principality, ALL charts, deep mixed instances) is
  **replaced** by: (i) the clean/rank-1 branches — **CLOSED general** here (depth-recursion + product
  independence); plus (ii) a single **coupled value-floor** `rlct(coupled minimiser) ≥ ½Mval`.
- (ii) is genuinely LIGHTER than the open end: an INEQUALITY (not the exact `⟨∏C⟩=⟨b₁⟩`), coupling-
  ASSISTED (the raise helps `≥`), NO single-chain collapse, and needed only at the MINIMISING branch (not
  all charts). But it is **not** free — it is real coupled corank≥2 mathematics (charter §1 B, NOT
  OPTIONAL — confirmed: V never dodged it; the minimiser can be coupled).
- So the honest answer to "V closes general, or falls back to coupled-B": **V falls back to coupled-B, in
  a materially lighter form.** The clean cases + the whole degree-1/support-tracking apparatus dissolve;
  what remains is one coupling-assisted value-floor inequality, vs the geometric route's full support-
  tracked coupled monument. Same genuine frontier, far smaller surface.

**RECOMMENDATION (to operator):** proceed with V — the reduction is real and worthwhile, and the residual
(the coupled value-floor) is the *minimal honest form* of the frontier the charter says is NOT OPTIONAL.
Next work = render the coupled value-floor `rlct(coupled minimiser) ≥ ½Mval` general-`L`: the depth-
recursion inequality with the coupling-raise made rigorous (why the shared deeper factor forces the RLCT
up to exactly `½Mval`). This is V's — and the expedition's — true remaining crux.

---

## L-lower-coupled — the isolated FRONTIER LEAF (V's true remaining crux)

Per charter §0(ii): decompose until the open math is ISOLATED and NAMED a frontier leaf. Here it is.

**Frontier leaf (F-lower-coupled).** *For the coupled minimising branch, the coupled resolution
monomialises `F = ‖∏C‖²` FROM BELOW: on the chart, `F∘g ≥ b_{k₀}²·(nonvanishing unit)` near the
exceptional locus, where `b_{k₀}` is the dominant exceptional monomial with exponent `Mval(branch)`.*
- **Consequence (clean, general):** given F-lower-coupled, `rlct(F) ≥ rlct(b_{k₀}²·unit) = ½·Mval`
  (the monomial RLCT, Object C, landed — for a SINGLE monomial only the from-below term is needed);
  combined with the clean/rank-1 branches (closed above) and the min over branches ⟹ `rlctAt ≥ ½·cCodim`.
  This deletes `cited_aoyagi_lower_ax`.
- **Why it is strictly LIGHTER than the open end.** The open end is the two-sided `⟨∏C⟩=⟨b₁⟩` terminal
  single-chain principality for ALL charts (deep mixed instances). F-lower-coupled asks only the
  **one-sided from-below** direction (`F∘g ⪰ b_{k₀}²`), only on the MINIMISING branch, and the coupling
  HELPS (the shared deeper factor raises the pullback, making `⪰ b_{k₀}²` easier not harder). No exact
  ideal identity, no all-charts, no both-directions.
- **Why it is NOT free (honest).** It still requires the coupled corank≥2 resolution (the blow-up tree
  `buildTree` — combinatorially landed; its geometric charts — L6/L7) AND that the pullback's dominant
  term is `b_{k₀}²` with `b_{k₀}` exponent `= Mval` (the combinatorial `M_{s,k}=Mval`, thread-03 landed)
  REALISED geometrically in the coupled case. The genuine content = the coupled pullback's leading
  behaviour is the codim-`Mval` monomial. This IS the frontier the charter (§1 B) calls NOT OPTIONAL —
  now in its minimal honest form (a one-sided leading-term bound, not the full monument).

**Candidate leverage (to attack the leaf, next):** (a) the depth-recursion — one layer-peel gives
`F = (divisor)²·(core)`; from-below on the divisor is a monomial factor, recurse on the core; the coupled
core's from-below by IH (base `L=2` Morse). (b) dev's cite-free determinantal geometry (§1 D) — the
rank-drop locus's leading form. (c) Object A (ideal-invariance) to work with the block-eliminated
generators. This is genuine research; render before any Lean.

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

### PHASE-2 FINDING #1 (primary source, 2026-07-24) — V's "lighter lower bound" is a MIRAGE; the honest close-out is Aoyagi's FULL recursion.
Cross-checked against the **primary** Aoyagi 2023 PDF via the prior expedition's decorrelated pen-and-paper
read (`expeditions/2026-06-20-aoyagi-full/threads/genm-d1lower-aoyagi/aoyagi-lowerbound-route.md`, Codex-
corroborated, line-cited to the PDF). Aoyagi's actual lower-bound method (Section 5):
- **Step 2 — Theorem 4 (homogeneity):** core entries homogeneous of degree `L`; `rlct_origin ≤
  rlct_nearby` ⟹ the origin is the WORST point ⟹ `rlct_global = rlct_origin`. The ONE extra analytic
  lemma (NOT Morse-Bott/IFT). Currently a landed *instance* (`rlctGlobal_eq_rlctAt_zero_of_homogeneous`);
  general form is the named atom to build/assess for Mathlib-feasibility.
- **Step 3 — the FULL recursive monomial blow-up** (Cases 1/2, the (S,J) induction) to
  `⟨∏C⟩=⟨diag(b)⟩` normal crossing. **The lower bound goes THROUGH this** — Aoyagi computes
  `rlct = ½Mval` EXACTLY (both bounds at once) from the complete resolution. There is **no from-below-only
  shortcut** in her argument (and my from-below idea itself needs the resolution to name the dominant
  monomial). **⟹ the L-lower-coupled "value-floor" (F-lower-coupled) as a *lighter* object is RETRACTED:
  the honest lower bound uses the full monomialisation = coupled-B (Object B), ideal-level.**
- **Step 4 — read-off (S2/Object C, landed) + Lemma 3 (landed).**

**Reframe (clarifying, and net-positive).** The close-out is **not open research** — Aoyagi *claims* the
uniform (S,J) induction closes for **all** `v` (one induction, two cases). So it is a **bounded
reproduce-and-verify** of her actual method, not the invention of new mathematics. The residual content
(prior thread, assuming S2/Object C landed): (a) **Theorem 4** general (1 analytic atom — assess Mathlib-
feasibility); (b) Lemma 2 + Theorem 3 (linear algebra ≈ L-A, general — done here); (c) **reproduce
Aoyagi's recursive blow-up Cases 1/2 → normal crossing** (the LARGE bounded piece = coupled-B, ideal-
level — Object B, charter §1 "NOT OPTIONAL"); (d) read-off + Lemma 3 (landed). The re-architect stands:
Aoyagi's method IS ideal-level Cases-1/2 Schur-clearing, exactly the route we swapped TO (not the drifted
fold). **Two named de-risks (KC-2 / Thm-4):** (KC-2) does the uniform induction genuinely close for all
`v`, or hide a non-uniform deep-coupled case (a flagged tension with Aoyagi's case-by-case companion
papers)? (Thm-4) is the homogeneity comparison Mathlib-feasible in general? These are the pivotal checks
before committing the build. **Next work:** verify KC-2 against the primary PDF's induction-closure
argument (myself), and assess Theorem 4's general feasibility.

### PHASE-2 FINDING #2 (primary source, KC-2 VERIFIED — largely POSITIVE). 2026-07-24
Read Aoyagi's actual induction (primary text lines 860–1260): the inductive invariant is exactly
`⟨∏C⟩ = ⟨diag(b)·[[E_J,O],[O,D_J]]·∏_{s>S}C⟩` (lines 891–904), and the cases are EXHAUSTIVE and TERMINATE:
- **Case 1** (partial equal `b`-run) splits into **1(1)** (`D`-block divisible by an EXISTING `u_{s,k}` —
  re-factor, decrement that divisor's count) and **1(2)** (introduce a NEW `u_{S,J+1}`, block-elim to
  `diag(1,D_{J+1})`, advance `J`); these are the two CHARTS of the blow-up along `{d=0, u=0}` — exhaustive.
  **Case 2** (full run). The `(S,J)` induction advances (`J→J+1`, or `S→S+1` when `J+1>M(S+1)`, lines
  1246–1258) and terminates fully-diagonal. The uniform induction DOES cover all `v` and closes.
- **KC-2's real content (the deep-coupled gap), located + resolved:** Aoyagi's inductive statement CARRIES
  a totality over-claim `T_{s,k} ≤ T_{s',k'} or ≥` (line 956) and USES it in Case-1 divisor selection
  (line 964) — but that totality is FALSE in general (T-F: `(2,2,1,1)` incomparable profiles), so her
  LITERAL induction (re-derives totality each step, 1011–1013) fails at incomparable instances. **FIX (our
  digest already made it): DROP the totality — NOT load-bearing.** Case-1 selection needs only a MINIMAL
  element of the profile PARTIAL order (exists, finite poset); and the RLCT read-off uses the `b`-chain
  `b₁|b₂|…`, TOTALLY ordered *by construction* (`bᵢ=∏u·bᵢ₋₁`), independent of the `T_{s,k}` order. Totality
  dropped ⟹ invariant maintained ⟹ induction closes for all `v`.
- **Maintenance algebra (resolves L-B's non-unit-`diag(b)` crux), Aoyagi's actual step (1220–1258):**
  `P·diag(b_{J+1..})·D_J·C = u_{S,J+1}·diag(b')·D'''_J·C'` — factor `u` FIRST (`u·diag(b)=diag(b')`, chain
  updated), THEN block-elim `D''_J→diag(1,D_{J+1})`. My candidate (b) [u-factor-first] is Aoyagi's actual
  method. ONE sub-point to verify (not assume): `diag(b')⁻¹·P·diag(b')` polynomial — triangular structure
  + `b`-chain divisibility should give it.

**VERDICT (L-lower generality, now firm).** V falls back to coupled-B (finding #1), AND coupled-B is
**bounded-and-buildable, NOT a wall** (finding #2): Aoyagi's uniform Cases-1/2 induction closes for all `v`
once the T-F totality is dropped (our correction), cases exhaustive/terminating, maintenance = her explicit
`u`-factor-then-block-elim. Remaining bounded work: (a) verify the `diag(b')`-conjugation polynomiality;
(b) Theorem 4 general Mathlib-feasibility; (c) the reproduction labour (Cases 1/2 + the (S,J) induction +
exponent ledger — large but combinatorial, not a missing analytic monument). The frontier the expedition
circled is a REPRODUCE-AND-VERIFY, not open mathematics.

### PHASE-3 (a) — the maintenance ideal equality: RESOLVED, general (the L-B crux closed). 2026-07-24
The one careful sub-point of the maintenance — is the block-elim compatible with the non-unit left factor
`diag(b')`? — resolves cleanly **as an IDEAL equality** (never a matrix identity, so no `1/monomial`):
- The invariant's `D`-block generators are `{ b'ᵢ · (D''_J C')ᵢ : i = J+1..M(S) }`. Block-eliminate with the
  UNIT pivot at row `J+1` (its `b'_{J+1}` is the SMALLEST in the chain): row `i` becomes
  `(D''_J C')ᵢ − cᵢ·(D''_J C')_{J+1}`, `cᵢ = (D''_J)_{i,J+1}`.
- The only new term is `b'ᵢ·cᵢ·(D''_J C')_{J+1} = (cᵢ·b'ᵢ/b'_{J+1})·[ b'_{J+1}·(D''_J C')_{J+1} ]`. Since
  `b'_{J+1} | b'ᵢ` (chain, `J+1 ≤ i`), `b'ᵢ/b'_{J+1}` is a MONOMIAL ⟹ the coefficient is POLYNOMIAL ⟹ the
  term lies in `⟨ b'_{J+1}·(D''_J C')_{J+1} ⟩ ⊆` the ideal. Symmetric via `Q₁⁻¹`. So the row-clear PRESERVES
  the ideal: `⟨diag(b')·D''_J·C'⟩ = ⟨diag(b')·(Q₁ D''_J)·C'⟩`.
- The column-clear `Q₂` and the layer transform ABSORB into the deeper product `∏_{s>S}C` (regular
  transforms, Lemma 1). Hence `⟨diag(b')·D''_J·C'⟩ = ⟨diag(b')·diag(1,D_{J+1})·C'⟩` — invariant maintained,
  GENERAL, no instances.
- **Load-bearing structural fact:** the `b`-CHAIN divisibility (`b'_{J+1}` minimal, dividing all `b'ᵢ`) is
  exactly what absorbs the block-elim cross-terms into the ideal. So the `b`-chain is load-bearing for BOTH
  the maintenance (L-B) AND the read-off (Object C). Aoyagi's `u`-factor-then-block-elim is now a rigorous
  general ideal argument.

**L-B STATUS: maintenance RESOLVED general.** With finding #2 (cases exhaustive/terminating; totality
dropped), the invariant is maintained through every step for all `v`. Remaining for the full close-out:
Theorem 4 general feasibility (Phase-3 (b)) + the reproduction labour + the `M_{s,k}=Mval` read-off
(Object C/D, landed).

### PHASE-3 (b) — Theorem 4 for the core: LANDED + WIRED (not a residual). 2026-07-24
The core is homogeneous in ALL variables (`r=0`, everything is a `C`-coordinate; `∏C` degree-`L`), so the
deepest-point step needs only the ALL-variables homogeneity lemma, which is LANDED and already WIRED:
`GlobalHomog.rlctGlobal_eq_rlctAt_zero_of_homogeneous` + `LearningCoefficient.lossDLN_zero_homogeneous`
(the zero-product loss is homogeneous of degree `2N`) ⟹ the origin has the minimal local RLCT, wired into
`coreReduction`. **Theorem 4's general SUB-BLOCK form is NOT needed** for the core close-out. Phase-3 (b)
resolves positively; no new analytic atom to build.

## RENDER VERDICT (Phase 1–3 essentially complete) — the close-out is BOUNDED-AND-BUILDABLE

The general render is done, and every crux resolved GENERAL, no instances:
- **L-A** (block-elim ideal identity): complete, general (any corank).
- **L-B** (the (S,J) recursion invariant): cases exhaustive + terminating (finding #2), totality-over-claim
  dropped (finding #2), maintenance = ideal equality via the `b`-chain divisibility (Phase-3 a). Closed
  general, all `v`.
- **L-lower / value**: `rlct = ½·min Mval` from the resolution (upper via `rlctAt_sumSqFam_le_chart` at the
  minimiser; the value is Aoyagi's exact resolution value); `Mval = cCodim` (Object C/D, landed).
- **Theorem 4** (deepest point): landed + wired for the core (Phase-3 b).
- **Objects A, C, D + the Chart/Resolution framework + Object B CoV**: landed.

**The ONLY remaining content is the Lean REPRODUCTION** of Aoyagi's Cases-1/2 `(S,J)` induction (the
`buildTree` recursion + the exponent ledger + the per-step ideal-identity `N1`/`N2`) — large but
COMBINATORIAL, bounded proof-engineering, NOT a missing analytic monument and NOT open mathematics. The
coupled corank≥2 frontier the expedition circled for multiple expeditions is, per this render,
reproduce-and-verify. **This is the execution boundary — operator-gated** (the Lean build of coupled-B,
ideal-level, retiring the geometric fold). The render + all de-risks are the deliverable to hand the
operator before that go.

## REV-RENDER AUDIT — CORRECTIONS (decorrelated review, 2026-07-24; SUPERSEDES the "bounded combinatorial" headline)

A decorrelated review-only audit (rev-render + its own Codex, + a grep of the Lean "landed" claims)
found the ideal-algebra SPINE sound but the RENDER VERDICT's headline OVER-CLAIMED. Controller
cross-checked all findings — they hold. Corrections:

- **The spine SURVIVES (verified decorrelated):** L-A, L-B maintenance (matches Aoyagi's actual `P`,
  entries `−(b'ᵢ/b'_{J+1})·d''`, polynomial by the chain), Theorem 4 — all sound and general. The
  coupled-corank≥2 *maintenance* wall genuinely was a substitution-encoding artifact, as claimed.
- **RETRACT "the only remaining content is bounded combinatorial reproduce-and-verify."** OVER-CLAIM
  (my second optimism-on-scope error; caught by the decorrelated review). The per-chart ideal identity is
  NECESSARY but NOT SUFFICIENT for the RLCT; a `Resolution` also needs the GEOMETRIC half — genuine (if
  standard) analytic geometry, currently SORRIED and UN-PROBED at coupled corank≥2:
  - **L6 `leafPath_chartGeometry` — SORRIED** (was mislabeled "landed"): the coupled blow-up chart maps,
    Jacobian certificate (=monomial·unit), a.e.-injectivity.
  - **L7 `leafPath_compactCover` — SORRIED** (was mislabeled "L7 engine landed"): the measure-zero COVER.
    **Genuinely required for the LOWER bound** (rev-render + Codex counterexample `F=x²+y⁴`: a per-chart
    threshold does NOT lower-bound rlct if a direction is omitted). The coupled corank≥2 cover (the L7
    tiling) is the ONE place charter §3's "probe the clean headline at the corank≥2 failure case" has NOT
    been discharged — the highest residual risk.
  - **L8 `leafPath_realizesExponents` clause (ii) — SORRIED**, and DISTINCT from Object D: Object D is the
    combinatorial `min over ALL admissible profiles = cCodim`; the UPPER bound needs Aoyagi's TREE to
    REALIZE a minimizing profile (minimizer-realization). Cannot invoke rlct-invariance to skip (circular).
- **KC-2 totality-drop — under-argued (conclusion survives, needs the explicit argument):** the selection
  rule picks a LEAST profile, not a bare minimal; the repair is a LOCAL same-level chain (profiles at each
  fixed `~t`-level are totally ordered) ⟹ minimal=least. Global cross-level totality drops (correct); the
  local least-selection is load-bearing for the value (it steers the tree to a minimizer = L8 (ii)).

**HONEST RE-VERDICT.** The ideal spine (L-A/L-B/Thm-4) is verified sound and general — the re-architect
is right and the maintenance frontier is genuinely dissolved. But the RENDER IS NOT COMPLETE: the
geometric half (L6 realization, L7 coupled cover, L8 minimizer-realization) is un-rendered-general and
sorried, and the coupled corank≥2 COVER is un-probed. Next render work (controller-owned, GENERAL, no
instance-as-justification): render L6/L7/L8 for the coupled corank≥2 case the way L-A/L-B were rendered —
the coupled cover (L7) first, as the highest risk. Not build-ready until this second half is rendered.

### L7/L6 RENDER TARGETS (rev-render forward pointers, 2026-07-24 — where the audit will bite)
- **L7 tooth 1 — `hcover` = measure-zero coverage of a punctured nbhd of 0, teeth at corank≥2 =
  properness/no-escape.** `hcover : volume(U \ ⋃_c g_c''dom_c)=0` with COMPACT `dom_c`. Individual
  blow-up charts are NOT proper, so the coupled cover must show the finite union of compact-domain images
  leaves only a null set uncovered. RISK (the crux, general-`d`): the charts are (blow-up ∘ shear ∘
  blow-up …) composites; a naive `pivotDomain × univ` chart lets a direction ESCAPE (the L7 docstring's
  `l7probe`: degenerate atlas covers only {0}). The general argument must bound the spectators (the
  box-inflation brick #103, implemented in the kept `-L7cover` engine `LeafCoverTiling`) THROUGH the
  shears (bounds grow) — the composition general-`d` is the crux, not any single leaf. RENDER: reduce the
  coupled cover to the `-L7cover` engine + establish the general-`d` escape-boundedness through the shears.
- **L7/L6 tooth 2 — dom-wide (not germ-only) Jacobian.** `Chart.hjac` on ALL of `nbhd`:
  `|det Dg_c| = ∏(blow-up monomial)·∏(unipotent shear det = ±1)` = monomial·(nonvanishing unit)
  region-wide (the D1 note: germ-only insufficient — a chart covers far regions where the identity fails).
  RENDER: the shear coord-changes `C'=Q⁻¹C` (Q polynomial in already-exposed coords) compose to an
  analytic automorphism with unit Jacobian on `nbhd`.
- **L8 (ii) — minimizer-realization** (upper bound): SOME minimizing profile is realized by `buildTree`;
  linked to the KC-2 local-least-selection (2a) that steers the tree. Distinct from Object D.
- **Discipline:** render these GENERAL (no instance-as-justification); `(3,3,4) t=(1,0)` illustrates only.
  rev-render re-audits the drafted L7/L6/L8 render (review-only).

## L7 — the coupled cover (RENDER; highest risk; general, no instance-as-justification)

**Obligation.** `hcover : volume(U \ ⋃_c (g_c '' dom_c)) = 0`, `dom_c` COMPACT, `U ∈ 𝓝 0`. I.e. the finite
family of compact-domain images of the leaf charts covers a punctured nbhd of 0 up to a null set (the
exceptional locus is null, so "punctured up to null" suffices).

**The chart maps (structural determination).** `g_c` = the ambient composite along the buildTree branch to
leaf `c`: `g_c = σ_{k} ∘ β_{k} ∘ … ∘ σ_1 ∘ β_1`, where `β_j` = the `j`-th blow-up chart map
(`c ↦ (u, u·d', spectators)`) and `σ_j` = the ambient coordinate relabel induced by the block-elim
`Q,P` at that step (`C' = Q⁻¹C`, LINEAR in the layer's entries, coefficients POLYNOMIAL in the already-
exposed `u`'s — unipotent, so degree bounded by the block). So `g_c` genuinely carries the shears
(rev-render tooth 1); the cover is NOT the bare blow-up cover.

**Reuse: the `-L7cover` engine (`LeafCoverTiling`, kept branch 646bcdcdb).** It PROVES abstractly: a
`FanTree` with an `R`-dependent inflation `f` covers `closedBall 0 R` up to null, PROVIDED each node's map
`σ` satisfies the box-containment `closedBall 0 (max R 1) ⊆ σ '' closedBall 0 (f (max R 1))` and the
children cover `f(max R 1)`; `f^[depth] 1` finite at finite depth. (The `f = r ↦ r + C·r²` free-inflation
repair handles the quadratic shear; two genuine depth-2 |S|=2 witnesses.) So L7 REDUCES to two general-`d`
obligations feeding the engine.

**L7-obligation-1 (the CRUX — per-edge box-containment for the COUPLED shears, general-`d`).** For each
edge's composite `σ_edge = σ_j ∘ β_j`, show `closedBall 0 R ⊆ σ_edge '' closedBall 0 (f R)` with a UNIFORM
`f` (widths only, depth-independent). The blow-up `β_j` is a monomial chart (standard box-containment, the
`OriginBlowup` idiom). The shear `σ_j` (unipotent `Q⁻¹`, polynomial in exposed `u`'s, degree bounded by
the block) inflates a box by a bounded factor. The earlier uniform-`C` finding (`canonNormalizationOf`
monomial count ≤ `max_ℓ d_ℓ`, layer-local, depth-independent) was on the GEOMETRIC-fold shear — the
IDEAL-route `σ_j` (= the `Q⁻¹` relabel) must be shown to have the SAME uniform bound, general-`d`,
COUPLED corank≥2. **STATUS: UN-RENDERED, the un-probed charter-§3 risk.** The `Q` is unipotent-polynomial
(L-A) with degree bounded by the block size (≤ widths), so a uniform box-inflation `f` PLAUSIBLY exists —
but "plausibly" is the over-claim trap: this must be PROVED general (the `Q`'s image of a box is contained
in a box of radius `≤ (1 + poly(widths))·R^{deg}`, uniform in the branch/depth), NOT assumed. If the
coupled `Q`'s degree or the composition across the corank≥2 stack grows with depth (not just widths), the
inflation `f^[depth]` diverges and the cover FAILS → genuine frontier.

**L7-obligation-2 (fan-completeness, general-`d`).** buildTree's leaves ↔ the `FanTree`'s nodes, and at
each node the children's charts (the affine charts of the blow-up's exceptional + the case-split) COVER
the parent's ball (no direction omitted — the `l7probe` failure mode). general-`d` via the pnp-fan
mechanism (banked for the geometric fold; must transfer to the ideal-route buildTree). Then the engine's
`Covers` fold gives `hcover`.

**HONEST ASSESSMENT (no over-claim).** L7 reduces cleanly to the two obligations + the kept engine. The
reduction is sound. Obligation-2 (fan-completeness) is bookkeeping-transfer (plausibly bounded). Obligation-1
(the coupled per-edge box-containment, uniform general-`d`) is THE crux and is genuinely UN-RENDERED and
UN-PROBED at corank≥2 — it is where L7 is either bounded (uniform `f` from the `Q`'s width-bounded degree)
or a real frontier (depth-growing inflation). NEXT: render obligation-1 general — bound the ideal-route
`Q⁻¹`'s box-image by `(1+poly(widths))·R^{deg}` uniformly, coupled corank≥2, depth-independent; `(3,3,4)
t=(1,0)` illustrates only. Do NOT report L7 bounded until obligation-1 is rendered general.

### L7-obligation-1 — RESOLVED general (via the one-pivot-per-step structure; rev-render to audit)

The crux turns on ONE structural fact about the `(S,J)` recursion, and it dissolves the "rational
`det(A₁)⁻¹` / depth-growing degree" fear:

- **The recursion clears ONE 1×1 pivot per step** (`J → J+1`), NEVER an `r×r` block at once. Corank≥2 is
  handled as `r` SUCCESSIVE 1×1 clears (this is Aoyagi's actual induction — the same step iterated, matching
  L-A/L-B's "corank≥2 = the step iterated"). So there is no `r×r` block inverse and hence NO rational
  `det(A₁)⁻¹`: the only inverse is a 1×1 pivot, normalized to `1` by Case-1(2)/Case-2 (the chart is the one
  where that pivot is a unit; "top-left 1").
- **Therefore the shear `σ_j = Q_j⁻¹` is unipotent-POLYNOMIAL, degree-1 coefficients.** With the pivot ≡ 1,
  `N_j = A₃·A₁⁻¹ = A₃` = the D-block entries below the pivot = degree-1 coordinates. `σ_j = I + N_j`. Its
  box-image: `|σ_j x| ≤ R + (#entries)·R·R = R + C_j·R²`, `C_j ~ #cleared entries ~ widths` — DEGREE-2,
  uniform in the branch/depth (depends on widths, not on how deep we are). This is exactly pnp-ideal's
  "pivot ≡ 1, polynomial cofactors, no unit inversion" — now with the GENERAL reason (one-pivot-per-step),
  not the instance re-run.
- **The `-L7cover` engine's free `f = r ↦ r + C·r²` repair is built for precisely this degree-2 shear**, and
  `f^[depth] 1` is finite at finite depth (`depth ≤ ∑_s M(s)`, finite). Uniform `C ~ widths` ⟹ a single `f`
  serves every edge ⟹ the engine's fold applies ⟹ the compact-domain images cover up to null.
- **Coupled corank≥2 changes only `C_j` (more entries to clear: `~ corank·widths`), NOT the degree** (still
  2) and NOT the depth-independence. So the corank≥2 coupling — the un-probed charter-§3 fear — does not
  break obligation-1: it is still a uniform degree-2 inflation, still finite at finite depth.

**Obligation-1 STATUS: rendered general (plausibly bounded, structure-level). Residual: (i) rev-render
audits this (its tooth 1 — "does spectator-boundedness compose across the corank≥2 shear stack without
escape?"; the answer here: yes — each step is a uniform degree-2 1×1-pivot shear and depth is finite);
(ii) obligation-2 (fan-completeness / no-omitted-direction) is still bookkeeping-transfer, un-done. NOT yet
"L7 bounded" as a whole — that needs obligation-2 + the re-audit.** Next: L6 (dom-wide composite Jacobian,
tooth 2), then obligation-2, then L8/totality.

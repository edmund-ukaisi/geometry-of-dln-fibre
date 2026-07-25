# Recursion-on-{R=0} minAdm-ratio de-risk (#172) — WITNESS: no deep divisor undercuts ½·minAdm

**Seat:** reroute-recursion-rzero (pen-and-paper, decorrelated). Exact algebra (sympy over ℚ) +
own Codex xhigh (`codex/{prompt,answer}.md`, EXIT 0). NO Lean. Scripts (this dir):
`branches2.py`, `rzero_instance2.py`, `rzero_deep.py`, `strata_map.py`, `sum_vs_prod.py`,
`directsum.py`, `mc_rlct.py`. Instance: **(3,3,3,2,2) t=(2,2,1,0)** — same as the tube/ideal probes,
so this COMPOSES with `reroute-R2-tubecover` and `reroute-R3-idealside`.

## NET VERDICT: WITNESS — the recursion on {R=0} TERMINATES and every deeper exceptional divisor
## has RLCT-ratio ≥ ½·minAdm. The payoff value rlct = ½·minAdm = ½C is NOT undercut by the deep
## {R=0} locus. Prices the cite-free lower bound (A) as SOUND. Detail-at-scale, not a monument hole.

The one arbitrary-depth inference for the whole cite-free lower bound is confirmed at the instance
by exact algebra, with the general-L mechanism pinned. A decorrelated Codex raised a sharp k=2
challenge; correctly diagnosed it is a **misreading (sum-vs-product)** that does NOT kill — it
*sharpens* the single load-bearing fact (the kept-survivor SUM structure ⟹ k=1).

---

## THE QUESTION (kill-condition)
loss = (monomial)²·R at a resolution leaf, R = ∑(residual generators)², R(0)=1. The lower bound
rlct ≥ ½·minAdm holds where R>0 (sandwich). {R=0} needs deeper charts (recursion). Does the
recursion introduce a divisor with RLCT-ratio **strictly < ½·minAdm** (KILL) or not (WITNESS)?

## FIRMEST [PROVEN, exact algebra]

**(1) Termination — SOLID.** The {R=0} recursion IS Aoyagi's depth-recursion: {R=0} = {the fresh
lower-depth matrix product vanishes} = a depth-(L−1) DLN core. Each peel drops depth by 1
(L→L−1→…→1); at L=1, ‖C‖² is a nondegenerate (Morse) quadratic resolved by one blow-up. So the
recursion halts in ≤ L steps. No infinite regress. (`branches2.py` enumerates the finite branch set.)

**(2) The generic {R=0} deep divisor has ratio EXACTLY 2 = ½·minAdm.** (`rzero_instance2.py`, exact
sympy Hessian.) At the instance, R = ‖Y_row0‖² + δ₂²‖Y_row1‖² + δ₁²‖Y_row2‖², Y = C3bar·C4bar. The
GENERIC point of {R=0} (all 6 gens = 0, generic C-entries) is **codim 4 = minAdm**, and there R is a
**rank-4 nondegenerate (Morse) quadratic** (Hessian rank = 4, Jacobian rank of the 6 gens = 4).
Blowing up the codim-4 Morse locus gives a divisor with **k=1, h=3, ratio (3+1)/2 = 2 = ½·minAdm**,
NOT below. (The naïve worry — that {R=0} is codim 4 and "codim-4 alone is no free pass" — resolves:
codim{R=0} = minAdm precisely, and the Morse structure makes ratio = ½·codim.)

**(3) The deeper COUPLED strata do NOT undercut either.** (`rzero_deep.py` + `directsum.py`.) At a
singular stratum of {R=0} where a residual generator (e.g. δ₁·Y_row2) also →0, the local model is
`R_local = ξ₁² + ξ₂² + δ₂² + (δ₁μ)²` (kept-survivor clean squares + one coupled x²y² term). By RLCT
**direct-sum additivity** (rlct(f⊕g)=rlct(f)+rlct(g) for disjoint variables — Watanabe/Lin),
`rlct(R_local) = 3/2 + 1/2 = 2`. The coupled x²y² block has isolated rlct 1/2 (multiplicity 2), but
it **adds** to the survivor's 3/2 rather than replacing it. Low-dim MC (reliable, calibrated)
confirms: x²+y²z² → 0.93 (≈1, not 1/2), R_local → 1.85 (≈2). No undercut.

**(4) The certified coupled (3,3,4) join is k=1, ratio 4 = ½·8.** (`g-coupled-334-diagb.py`, exact,
EXIT 0.) The peel divisor and residual divisor JOIN at the corner; the join divisor E has
**loss = E²·unit (k=1)**, Jacobian h=7=Mval−1, ratio (7+1)/(2·1) = 4. This is the Jacobian
telescoping: h = Σ(block dim) − #levels + #joins = Mval − 1, exact.

## THE GENERAL-L MECHANISM (the reason it holds — the corrected, sharpened statement)

The RLCT-ratio of a resolution divisor = ½·codim(its branch) **provided k=1** (loss vanishes to
order exactly 2 along it). The whole witness is:
- rlct = ½·min over branches of codim(S(t)) = ½·Mval(t); min = **minAdm** (Object D, banked
  `minAdm_eq_cCodim`). Every branch codim ≥ minAdm **by definition** (`strata_map.py`: all
  (3,3,3,2,2) branches have ratio ≥ 2, none below).
- The recursion only ever reaches *branches* (deeper rank degenerations): the sub-problem's first
  width is t_{j−1}, so t_j ≤ min(t_{j−1}, M_{j+1}) is forced by the matrix dimensions ⟹ every leaf
  is a valid Aoyagi profile.
- **k=1 holds because the DLN loss is a SUM OF SQUARES with a kept-survivor constant term.**
  Block-eliminating layer 1 (unipotent, ideal-preserving via Object A/Lemma 1) gives
  ⟨∏C⟩ = ⟨survivor rows T, residual block Δ·S⟩, so loss ~ ‖T‖² + ‖ΔS‖² — a **SUM**. ‖T‖² radializes
  to q²·U_T with U_T(0)=1 (the normalized pivot). Joining the survivor radial q with any residual
  radial u gives `E²·(U_T + …) = E²·unit` (k=1), because U_T contributes the constant 1. This
  telescopes at every depth (`sum_vs_prod.py` (iii): 2-level join still k=1).

The **additive-accumulation identity** `Mval(t₁,s) = (M₁−t₁)(M₂−t₁) + Mval_sub(s)` (machine-verified
over 12 dimension vectors, `branches2.py`) is the combinatorial shadow of the direct-sum additivity:
`rlct = ½·(peel codim) + ½·minAdm(sub) = ½·Mval(minimizer)`, min over peels = ½·minAdm — the minAdm
recursion, realized analytically.

## THE CODEX CHALLENGE — raised, diagnosed, REFUTED (and it sharpens the finding)

Codex (xhigh, decorrelated) returned **OBSTRUCTION**: it computed the (3,3,4) join as
`(qu)²U → e⁴v²` (k=2), ratio (7+1)/(2·2) = **2 < 4**, and a general k=2 undercut.
**This is a misreading of SUM as PRODUCT** (I under-specified the loss form in the prompt):
- `sum_vs_prod.py` (exact): SUM `q²U + u²G` (U(0)=1) joins to `E²·unit` (k=1); PRODUCT `q²u²(…)`
  joins to `E⁴·(…)` (k=2, unit(0)=0). The DLN loss is the **SUM** (‖T‖²+‖ΔS‖², block-elim), NOT the
  product. Exact re-run of `g-coupled-334-diagb.py`: `loss = E²·unit exact: True`, ratio 4. Codex's
  e⁴v² does not arise.
- Codex's Q2 is nonetheless VALUABLE and correct in the abstract: k=1 is **not automatic** — a pure
  product term (no survivor) genuinely gives k≥2. The DLN structure avoids this because a **binding
  branch always has a kept survivor** (r≥1: the terminal chart's normalized pivot; `reroute-R3-idealside`
  anti-check (d): no kept survivor ⟹ not principal ⟹ constant term lost). So the SUM/kept-survivor
  structure is the exact load-bearing fact, and Codex pins it.
- Codex's Q4 (rlct(m²·G) = min(rlct m², rlct G) for a PRODUCT of disjoint factors) is the *product*
  rule; the residual is a *sum* (‖T‖² + residual), governed by the *additive* rule. Different regime.

## MOST LIKELY TO BREAK IT (scoped)

**The general-L k=1 (kept-survivor SUM structure at binding branches, at arbitrary depth).** This is
INFERENCE: verified exactly at (3,3,3,2,2) [generic + coupled strata], certified at coupled (3,3,4),
and the 2-level join telescoping shown symbolically — but NOT a closed general-L proof. It is exactly
the build labour worked.tex:717–720 names ("the cover lower bound is structural/inductive… the
general-L reproduction is the build labour, not a monument"). The seed for the Lean proof: the r≥1
kept-survivor argument (binding branch ⟹ terminal rank ≥1 ⟹ U(0)=1 ⟹ k=1 ⟹ ratio = ½·Mval),
composed with the direct-sum additivity of RLCT. If the build ever produces a binding branch with NO
survivor (a pure coupled product), k≥2 could undercut — but that requires the deepest (rank-0) branch,
whose codim is maximal (non-binding, large ratio). No such undercut exists in any checked instance.

## GENERALITY CAVEAT

Exact at ONE instance (3,3,3,2,2, the canonical two-separated-shared-factor case) + certified coupled
(3,3,4) + the additive identity over 12 dimension vectors + the SUM/PRODUCT k-mechanism symbolic. The
mechanism (SUM-of-squares, kept-survivor constant, direct-sum additivity ⟹ ½·Mval) is inductive and
should generalize, but general-L is INFERENCE (named build labour), not exhaustive proof.

## CLOSE

The last de-risk before the R2/R3 build is **GREEN**: WITNESS. The recursion on {R=0} terminates and
introduces no divisor undercutting ½·minAdm — the deep locus is resolved into the OTHER branches, each
of codim ≥ minAdm, each contributing ratio = ½·codim (k=1 via the kept-survivor SUM structure). This
prices **(A) fully-cite-free as reachable**; the recursion-ratio check is detail-at-scale build labour,
now precisely characterized: build the k=1/kept-survivor SUM invariant + the direct-sum additivity, at
general L. Codex's sharp k=2 probe, correctly diagnosed, converts the vague "recursion terminates at
the right value" inference into a precise, buildable obligation (the SUM structure), and is banked as
the anti-pattern to guard (never let the residual be read as a product).

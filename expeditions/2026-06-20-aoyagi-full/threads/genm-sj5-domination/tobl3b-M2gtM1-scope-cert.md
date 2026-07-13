# T-Obl3b `M₂>M₁` off-sector-mountain SCOPE cert — reachability + permutation-invariance + finer-stratification verdict

**Seat:** pen-and-paper (design-space math, one truth-value, decorrelated), aoyagi-full Stage 2,
`genm-sj5-domination`. **Date:** 2026-07-13. **NO Lean edits, NO git, NO build.** Exact integer
arithmetic for the load-bearing classification (`minAdm` layer-peel recursion, front-peel identity,
co-minimizer ranks); Ky-Fan/Weyl + Wishart matrix-integral facts named, not floated. Decorrelated
`local-codex-consult` (xhigh, conclusion WITHHELD): `codex/tobl3b-m2gtm1-{scope,verdict}-{prompt,answer}.md`
(the first produced independent DATA + an anchor correction; the second a prose verdict — Codex concurs
on all three, and SHARPENS Q3). Scripts (this thread): `scripts/m2gtm1_scope.py`,
`scripts/m2gtm1_honest.py`, `scripts/cominimizer_check.py`.

**The adjudicated question.** The S1 cert (`s1-spine-headsplit-cert.md` §B.2b) flagged: the T-Obl3b
off-sector mountain's corank-weight bound converges only for `M₂ ≤ M₁` (shell-forced floor
`m = min(M₁,n)−j ≥ a+b`); for `L≥1 ∧ M₂>M₁` wide chains it diverges. Is that gap COVERED (so the mountain
still discharges (□) ∀ nondeg `M`), and HOW — or does it need genuinely-new work?

**Anchor CORRECTION (decorrelated, load-bearing).** The S1 cert's schematic example `M=(4,3,4,4)@u=2`
is NOT a realizer: `minAdm(4,3,4,4)=9` with a UNIQUE binding cut `t★=2` (charges `12,10,9,10` at
`t=0..3`), and `t★=2 = min(M₀,M₁)−1` leaves NO proper off-sector `u>t★` with `a,b≥1`. The genuine
divergent `(4,3,·)` realizers need `t★=1` binding: `M=(4,3,4,5)`, `(4,3,5,4)`, `(4,3,5,5)` (and their
`L=2` extensions) — `minAdm=10/10/11`, binding `t★∈{1,2}`, off-sector `t★=1, u=2`: `a=2, b=1, j=1`,
shell floor `m=min(3,ML)−1=2 < a+b=3`. Codex independently recomputed this (its run log reproduced the
sweep and flagged `(4,3,4,4)`'s `t★=2` uniqueness). Use `(4,3,5,5)` as the anchor.

---

## ★ HEADLINE VERDICTS

- **Q1 — REACHABLE (the recursion does NOT forbid it).** `DecoratedStepHyp` (`RouteMSJDecoratedRec:144`)
  is universally quantified over EVERY `≥3`-width chain `M`, with the arity-`(n−1)` IH; it carries NO
  `M₂≤M₁` ordering invariant. Wide chains (`(4,3,5,5)`, …) are legitimate step inputs whose off-sector
  mountain must be discharged at their OWN binding cut. The `M₂>M₁` divergent regime is faced at the
  root of the arity induction. **The gap is NOT vacuous.**

- **Q2 — permutation-invariance is NOT a valid cover (circular / unavailable via CoV); but chain
  REVERSAL is a genuine measure-preserving symmetry.** The landed `minAdm_comp_perm` is COMBINATORIAL
  (the codim number); the box-integral FINITENESS is not perm-invariant via any change of variables:
  permuting interior widths changes the parameter-space dimension `Σᵢ MᵢMᵢ₊₁` AND the product's shape,
  so no nonsingular measure-preserving CoV intertwines the two integrands. Finiteness-perm-invariance
  would have to route through the RLCT = ½·minAdm — exactly what (□) is re-proving — so it is CIRCULAR.
  The one exception: **reversal** `M ↦ reverse(M)` is a genuine symmetry (transposition CoV, below),
  giving `I(M,c') = I(reverse(M),c')` EXACTLY.

- **Q3 — BOUND ARTIFACT, NOT a wall.** The true total box integral `I(M,c')` is finite for
  `c'<½·minAdm(M)` (cited: Watanabe `rlct≤½·codim` + Aoyagi `rlct=½·minAdm`); each off-sector shell is a
  NONNEGATIVE sub-piece (`singularShell_iUnion` covers the box; integrand `≥0`), hence itself finite by
  Tonelli/monotonicity. So the divergence is necessarily an artifact of the BOUND — the Ky-Fan
  `Z_full`-shell floor `m=min(M₁,n)−j` under-certifies the deep rank. **No genuine divergent subintegral
  exists.**

- **OVERALL — NEEDS-NEW-WORK (scoped), NOT a wall, NOT covered by S1 as-landed.** The S1 mountain
  (`deeperFlag_shell_le`) as stated carries the scope hypothesis `m=min(M₁,n)−j ≥ a+b` (all `M₂≤M₁`;
  both S1 anchors, tight) and does NOT cover `L≥1 ∧ M₂>M₁`. Two candidate fixes, both genuinely-new but
  within the method (analytic content largely banked): **(A)** a finer `Z_deep`-direct stratification
  whose generic stratum's deep rank is supplied by the BANKED co-minimizer (`minAdm_backPeel_cominimizer_ge`,
  `ρ≥a+b+1` at off-sectors), the low-rank sub-loci closed by codimension-retaining stratified additivity;
  **(B)** "peel the better end" via the reversal CoV (numerically NO chain is divergent from both ends).
  Both need new labour; neither is a wall.

---

## Part 1 — Q1 reachability: REACHABLE (recursion structure)

The (□) driver `routeMBoxThresholdFinite_of_decoratedDescent` runs strong induction on chain ARITY. The
inductive STEP `DecoratedStepHyp adm` (`RouteMSJDecoratedRec:144-148`) reads: for a `≥3`-width chain `M`,
GIVEN box-finiteness for every `adm`-decoration of every ONE-shorter chain, prove it for every
`adm`-decoration of `M`. **`M` is universally quantified** — no `M₂≤M₁` restriction, no ordering
invariant. The peel is at the binding cut `t★≤min(M₀,M₁)`, reducing to `redChain t★ M = (t★,M₂,…,M_L)`;
the off-sector mountain (`deeperFlag_shell_le` at `M`) is over shells `u=t★+j`, `a=M₀−u`, `b=M₁−u`, with
the deep tail `Z_deep = A₂···A_{L-1}` (`M₂×M_L`) fixed (independent of the front rank `u`).

[FACT] `(4,3,5,5)` is a valid arity-3 (`L=1`, 4-width) chain, a legitimate step input. Its binding
`t★=1` (`minAdm=11`, charges `12,11,11,13`), off-sector `u=2`: `a=2,b=1,j=1`, `m=min(3,5)−1=2<3=a+b`.
The mountain at `(4,3,5,5)` faces the divergent regime. [INFERENCE] A proof of `DecoratedStepHyp`
relying on `M₂≤M₁` has a real generality gap. Codex concurs (Q1: reachable, "binding conditions involve
no `M₂` and force no `a+b≤m`").

**Where the divergent pattern lives.** Sweep (`m2gtm1_honest.py`, honest per-regime floor — `L=0`:
`Z_deep=I_{M₂}` a KNOWN full-rank constant, floor `M₂`; `L≥1`: shell floor `min(M₁,n)−j`) over
widths `2..5`, lengths `3..5`: **every** failing shell has `M₂>M₁` (local wide step at position 1→2)
and `L≥1`; ZERO `L=0` residual (confirms the cert's "`L=0` always converges"), ZERO `M₂≤M₁` failures.
The cert's `t★≥1`-convention count of 7/64 is reproduced exactly (`cominimizer_check.py`); a broader
`t★≥0` convention counts more shells (713 over widths `2..7`) but the qualitative classification is
identical.

---

## Part 2 — Q2 permutation-invariance: unavailable via CoV (circular); reversal IS a symmetry

**The codim is perm-invariant; the integral's finiteness is not (via CoV).** `minAdm_comp_perm`
(`MinAdmPermInvariance:394`) proves `minAdm(M∘σ)=minAdm(M)` — a fact about the combinatorial NUMBER. No
analogous integral-finiteness statement exists in the codebase (grep: only `minAdm`/`cCodim`-level perm
lemmas). [FACT] Permuting interior widths changes `Σᵢ MᵢMᵢ₊₁` (the parameter-space dimension) and the
matrix-product shape, so there is no nonsingular measure-preserving Euclidean CoV intertwining
`loss_M` and `loss_{M∘σ}`. [INFERENCE] The integrals may share the same RLCT (they do, `=½·minAdm`), but
invoking that to transfer finiteness is invoking the theorem (□) re-proves — CIRCULAR. So sorting a wide
chain to a narrow one is NOT a valid cover. Codex concurs verbatim ("using [RLCT perm-invariance] here
invokes essentially the theorem the recursion is meant to prove").

**Reversal is the ONE genuine symmetry (transposition CoV).** [FACT]
`‖A₀A₁···A_{L-1}‖_F² = ‖(A₀···A_{L-1})ᵀ‖_F² = ‖A_{L-1}ᵀ···A₀ᵀ‖_F²`, and the map
`(A₀,…,A_{L-1}) ↦ (A_{L-1}ᵀ,…,A₀ᵀ)` is a measure-preserving linear bijection of the parameter box for
`M` onto the box for `reverse(M)=(M_L,…,M₀)` (transpose + reindex, `|det|=1`), intertwining the losses.
Hence `I(M,c')=I(reverse(M),c')` EXACTLY, and `minAdm(reverse M)=minAdm(M)` (reversal is a permutation).
This is available WITHOUT the RLCT — a real CoV, not circular. Codex independently flagged reversal as
"an exceptional genuine symmetry, via transposition; arbitrary sorting is not." (No such CoV lemma is
banked yet — building it is part of cover (B).)

---

## Part 3 — Q3 the fix: finer `Z_deep`-stratification (bound artifact, not wall)

### 3.1 The artifact is the rank SOURCE: Ky-Fan `Z_full`-shell floor vs banked co-minimizer

The corank weight `W = ∫_{A_cor∈box(b×M₂)} det((A_cor Z_deep)(A_cor Z_deep)ᵀ)^{−a/2} dA_cor` [FACT,
Wishart / matrix-argument-Gamma] converges iff `rank(Z_deep) ≥ a+b`. The S1 route sources the floor on
`rank(Z_deep)` from a shell on the FULL product `Z_full = A₀·Z_deep` (`M₁×n`); Ky-Fan/Weyl then certifies
only `m = min(M₁,n)−j` strong directions — which on `M₂>M₁` shells is `< a+b`. This is under-certification,
not divergence.

**The deep rank the mountain needs is BANKED.** `minAdm_backPeel_cominimizer_ge`
(`RouteMSJBackPeel:86`, sorry-free, axiom-clean): at a nondegenerate binding cut `t★`
(`a★=M₀−t★≥1, b★=M₁−t★≥1`), every front-peel co-minimizing deep rank `ρ` of `redChain t★ M` —
the rank of `Z_deep` on the top-dimensional component of the reduced zero-locus — satisfies
`ρ ≥ a★+b★−1`. An off-sector sits at `u=t★+j`, so `a=a★−j`, `b=b★−j`, and

    a★+b★−1 = a+b + (2j−1) ≥ a+b+1   for j≥1   [pure ℕ arithmetic].

So `ρ ≥ a+b+1 > a+b` at EVERY off-sector shell. [FACT, numeric: `cominimizer_check.py`] Over 713
shell-floor-FAILING shells (widths `2..7`, `t★≥0`; 169 at `t★≥1`), the co-minimizer `ρ ≥ a+b` on ALL —
zero exceptions; on the 7 anchor realizers `ρ=4 ≥ a+b=3` while the Ky-Fan floor `m=2`. Equivalently the
generic (full-box) deep rank `deepbott = min(M₂,…,M_L) ≥ a+b` on ALL 713+ failing shells (0 exceptions,
`m2gtm1_scope.py`): the generic stratum's `W` converges.

### 3.2 Why it is NOT a one-line `m→ρ` swap (Codex's sharpening — load-bearing)

[FACT] `ρ` is the rank of `Z_deep` on ONE (top-dim) reduced component — a.e. w.r.t. that component's
intrinsic measure — NOT a certificate that the `Z_full`-shell has `ρ` uniformly-strong singular values.
Near the rank-drop boundary the deep singular values become arbitrarily small and the Wishart constant
blows up. [INFERENCE] So one cannot substitute `ρ` for `m` inside the existing `Z_full`-shell bound; the
repair is a genuinely finer decomposition. The required re-plumbing (cover (A)):

1. Refine the shell into rank / singular-value shells of `Z_deep` ITSELF (an `M₂×M_L` product), not the
   `M₁×n` full product `Z_full` — this is the "stratify `Z_deep` directly" the S1 cert and task option (3)
   name. `RouteMSJShellCover`'s `singularShell`/`weakEigCount` machinery applies verbatim to `Z_deep`.
2. On the generic co-minimizing `Z_deep`-shell, use `ρ ≥ a+b+1` in the Wishart estimate — `W` converges
   with strict slack.
3. Route neighborhoods of the rank-drop loci into LOWER-ρ `Z_deep`-shells, RETAINING their transverse
   codimension (do not discard it in the corank decoupling). This is where the **saturated / lumped
   shell** (`RouteMSJShellCover` `j=r`, `RouteMSJOnePeel334`) is the natural home.
4. Close by stratified RLCT-additivity: the extra codimension of a low-`ρ` stratum outweighs the worsened
   corank exponent, because strict `c'<½·minAdm` supplies positive slack and the banked co-minimizer
   excludes a zero-slack shell with `ρ<a+b` (a zero-slack shell WOULD be a front-peel co-minimizer, and
   the banked theorem forbids `ρ<a★+b★−1`).

This reuses banked bricks (`minAdm_backPeel_cominimizer_ge`, the corank estimates
`corankOffSector_b1_le`/`_bpos_le` — the latter's "`a≤M₂−b+1` at every genuine `b>1` binding cut" holds
here since `M₂≥deepbott≥a+b ⟹ a≤M₂−b`, verified — and the shell machinery). The genuinely-new content is
the SECOND stratification layer (of `Z_deep`) and the codimension-retaining additivity across it.

### 3.3 Cover (B): "peel the better end" via the reversal CoV

An alternative, possibly lighter, cover: at each recursion node ORIENT the chain before front-peeling —
front-peel `M` if its front end is non-divergent, else transpose (reversal CoV, Part 2) and front-peel
`reverse(M)`. [FACT, numeric `m2gtm1_honest.py`/search] over widths `2..6`, lengths `3..6`: 764 chains
have a front-peel divergent shell; **ZERO of them are divergent from the back too** (0 both-ends-bad).
So numerically every chain has ≥1 end whose front-peel stays in the `M₂≤M₁`-safe regime (which S1 already
discharges, 57/57). Palindrome-peak candidates (`(2,3,5,3,2)`-type) that could be bad from both ends turn
out to have NO proper off-sector shell at their binding cut (the binding `t★` is high enough that `a` or
`b` drops to 0). Requirements for (B): (i) the transposition CoV lemma `I(M)=I(reverse M)` (new, clean,
`|det|=1`); (ii) the "≥1 good end" combinatorial THEOREM (UNPROVEN — numeric 0/764 only; this is the risk,
= Codex's palindrome-peak concern in a different guise); (iii) a branch in the step to choose orientation.
No new analytic content — reuses the already-converging `M₂≤M₁` mountain.

---

## Numeric ledger (guides + exact classification)

- `m2gtm1_scope.py` — shells over widths `2..5`, lengths `3..5`: every current-bound failure is `M₂>M₁`;
  `deepbott=min(M₂..M_L) ≥ a+b` on ALL failures (0 residual); descending-sort removes the pattern on all
  87 distinct failing chains (illustrating why Q2 WOULD cover IF finiteness were perm-invariant).
- `m2gtm1_honest.py` — honest per-regime floor: 0 genuine `L=0` residual; all failures `M₂>M₁ ∧ L≥1 ∧
  deepbott≥a+b`; reversal covers 73/73 in-range failing chains.
- `cominimizer_check.py` — front-peel identity `= minAdm` (sanity ✓); on all 7 anchor shells + 713
  big-range shell-floor-failing shells, the banked co-minimizer `ρ ≥ a+b` (0 exceptions), `ρ > a+b`
  strict; cert's 7/64 (`t★≥1`) reproduced.
- Both-ends search (widths `2..6`, lengths `3..6`): 764 front-divergent chains, 0 both-ends-divergent;
  `minAdm` reversal-invariant ✓.

All Monte-Carlo / float only guide; the classification above is exact integer arithmetic on `minAdm`,
the front-peel identity, and the co-minimizer ranks.

---

## Decorrelated Codex (conclusion WITHHELD; two consults)

- **Consult 1** (`tobl3b-m2gtm1-scope`): produced independent DATA — reproduced the sweep, and
  independently CORRECTED the anchor (`(4,3,4,4)` is `t★=2`-unique with no off-sector; the real family is
  `(4,3,4,5)`/`(4,3,5,4)`/`(4,3,5,5)` at `t★=1`). The final prose message was not captured; the data
  stands as decorrelated corroboration.
- **Consult 2** (`tobl3b-m2gtm1-verdict`, prose-only): CONCURS on all three. Q1 reachable (no ordering
  invariant in the IH). Q2 sorting not a noncircular cover; reversal-via-transposition is the genuine
  symmetry. Q3 no wall, bound artifact, direct `Z_deep`-shelling the right repair but NOT a literal
  `m→ρ` swap (near the rank-drop boundary the Wishart constant blows up) — SHARPENING I have folded into
  §3.2. Codex's "most likely wrong": "every co-minimizer" may cover only top-dim reduced components,
  while a lower-dim rank-drop valuation could become critical only after adding the Wishart fibre loss —
  then an extended rank-stratified lemma is genuinely necessary. This is the honest residual (§3.2 step 4).

The concurrence is decorrelated: my rank-source diagnosis (co-minimizer `ρ` vs Ky-Fan `m`) and the
transposition-CoV / both-ends numeric were NOT in either prompt.

---

## Close

- **Firmest result.** The `L≥1 ∧ M₂>M₁` gap is REAL and REACHABLE (Q1), is NOT covered by
  permutation-invariance (Q2: no measure-preserving CoV; circular with the RLCT), and is a BOUND ARTIFACT
  not a WALL (Q3: the true off-sector integral is a nonnegative sub-piece of the finite total). The deep
  rank the corank weight needs (`a+b`) is BANKED — the co-minimizer bound `minAdm_backPeel_cominimizer_ge`
  gives `ρ ≥ a★+b★−1 = a+b+2j−1 ≥ a+b+1` at every off-sector (exact ℕ; numeric 0/713 exceptions), whereas
  the Ky-Fan `Z_full`-shell floor `m=min(M₁,n)−j` under-certifies it. **VERDICT: NEEDS-NEW-WORK (scoped
  finer `Z_deep`-stratification), NOT a wall, NOT covered by S1 as-landed.**
- **Most likely to break it.** (Codex's, adopted) the banked co-minimizer bounds the deep rank on the
  TOP-dim reduced components; a lower-dimensional rank-drop stratum could carry the critical singularity
  only after the Wishart fibre loss is added — that valuation is not covered by the banked theorem and
  would force a genuinely-new rank-stratified combinatorial+analytic lemma (still finite = not a wall, by
  F1+F2, but heavier than a re-plumbing). Cover (B)'s risk is the UNPROVEN "≥1 good end" claim (numeric
  0/764 only).
- **Next construction / consult.** (a) Prove — or find a counterexample to — "every `≥3`-width chain has
  a front OR back end whose front-peel avoids the divergent off-sector" (upgrades cover (B) to a clean,
  analytic-content-free discharge via the transposition CoV). (b) If (a) fails, pin the codimension-retaining
  stratified-additivity across `Z_deep`-rank shells (cover (A) step 4) — the one place the residual could
  still hide labour. Recommend (a) first: it is pure `minAdm` combinatorics (this seat's instruments) and,
  if it holds, is the cheapest complete cover.

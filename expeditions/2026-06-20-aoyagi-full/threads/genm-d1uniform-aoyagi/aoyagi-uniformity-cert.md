# KC-2: does Aoyagi's Section-5 (S,J) blow-up induction close in normal-crossing form for ALL reduced dimension vectors? (genm-d1uniform-aoyagi)

Read-only pen-and-paper adjudication (obstruction seat, but the truth-call came out positive-for-uniform).
Owns KC-2, flagged by `d1route` (aoyagi-lowerbound-route.md lines 129-134) as "MOST LIKELY TO BREAK the
bounded verdict." Primary source IN REPO, read exactly via `pdftotext -layout`:
`paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf`
→ `/tmp/aoyagi-2024-dln.txt` (Aoyagi 2024, Neural Networks 172:106132). Companion methods paper (the
Vandermonde case-by-case one) also IN REPO: `.../entropy-15-03714.pdf` → `/tmp/aoyagi-entropy.txt`
(Aoyagi 2013, Entropy 15:3714 — NOT the 2019 Entropy paper, but the SAME author / SAME Vandermonde-type
methods and the same "bounds + small-H exact" pattern the brief refers to). Line refs = `pdftotext -layout`
line numbers.

---

## VERDICT: BLOWUP-UNIFORM. The (S,J) induction closes in diagonal-monomial (normal-crossing) form for EVERY reduced dimension vector. The 2013/2019 case-by-case belongs to a strictly harder singularity class (Vandermonde-type) the DLN proof does not touch. No hidden per-v resolution step.

The tension d1route flagged is REAL but RESOLVED in the DLN's favour: the case-by-case companion work is
on **Vandermonde matrix-type singularities** (entries are *powers* `b^k`), a genuinely harder, non-multilinear
object where the blow-up branches proliferate and only a *bound* (choose-one-branch) is obtainable except for
small H. The 2024 DLN product `∏C^(s)` is **multilinear** (linear in each block separately, homogeneous of
degree L overall); its block-elimination produces a **total-chain** exponent structure that monomializes the
ideal EXACTLY — an *equality* `⟨∏C^(s)⟩ = ⟨diag(b_i)⟩`, not a bound. The uniformity is carried by one
structural invariant, and the case-split is a genuine dichotomy on run-lengths, exhaustive for all v.

---

## The exact induction structure (what a formaliser would lift ∀-v)

**Objects (Def. 3, lines 686-745; Thm 2, lines 743-802).** Reduced dims `M^(s) = H^(s) − r`, `s=1..L+1`.
The closed value is driven by three combinatorial invariants of the *multiset* `{M^(s)}`:
- `M` = the "small-`M^(s)`" subset: `M^(s) ∈ M` iff `Σ_{k} M^(Sk) > ℓ·M^(s)`; `M^(s) ∉ M` iff
  `Σ M^(Sk) ≤ (ℓ−1)M^(s)` (self-consistent characterization, lines 700-712).
- `ℓ = Card(M) − 1`.
- `M` (integer) with `M−1 < (Σ_{k} M^(Sk))/ℓ ≤ M`, and `a = Σ M^(Sk) − (M−1)ℓ` (lines 718-732).

These are defined for EVERY reduced dimension vector — the definition is a case analysis on the *ordering*
of the `M^(s)` (which are small, which large), NOT case-by-case on individual small values. The L=2 base
(Thm 1, RRR / Aoyagi-Watanabe 2005 [12], lines 507-545) is already the general closed form for arbitrary
`(M^(1),M^(2),M^(3))` in exactly this `(M,ℓ,a)` shape.

**The induction (Section 5, lines 1321-2360).** After Thm 4 sets `r(s)=r` WLOG (deepest point, homogeneity),
the target is `λ⟨‖∏_{s=1}^L C^(s)‖²⟩` with `C^(s)` of size `M^(s)×M^(s+1)`. Double index `(S,J)`:
- **`S`** ∈ {0,...,L+1}: how many factors `C^(s)` have been fully absorbed into the diagonal `diag(b_i)` block.
  Running minimum `M(S) = min{M^(s) : 1≤s≤S}` (line 1336) — this is what makes ARBITRARY orderings of the
  `M^(s)` handled uniformly (no weakly-increasing assumption; the running-min tracks the binding width).
- **`J`** ∈ {0,...,M(S+1)}, `M(S+1) = min{M(S), M^(S+1)}`: how many diagonal entries `b_i` of the current
  active block are already fixed/peeled.

**Inductive statement (lines 1382-1435).** `⟨∏C^(s)⟩ = ⟨diag(b_1..b_{M(S)}) [E_J O; O D_J] ∏_{s>S} C^(s)⟩`,
with `b_i = (∏_{t̃_{s,k}=i} u_{s,k}) b_{i-1}` a divisibility chain, an explicit monomial Jacobian
`∏ u_{s,k}^{M_{s,k}−1}`, exponent vectors `T_{s,k} = (t^{(1)}_{s,k},...,t^{(L)}_{s,k})`, and the LOAD-BEARING
INVARIANT (lines 1459, re-established at 1570/1672/2096):

    T_{s,k} ≤ T_{s',k'}  OR  T_{s,k} ≥ T_{s',k'}   for all (s,k),(s',k')   [componentwise partial order]

i.e. the exponent vectors form a **total chain**. This is the invariant that makes the whole thing uniform.
It is what guarantees (i) the "Fix u_{s,k} with t̃=J+J1 and T_{s,k} ≤ T_{s',k'} minimal" pick (line 1483)
is always well-defined (a chain has a minimum), and (ii) the case split below is exhaustive.

**Case split (exhaustive dichotomy on the leading run of equal b-values):** at state `(S,J)` the active block
is `diag(b_{J+1},...,b_{M(S)})`; look at the maximal initial run `b_{J+1}=...=b_{J+J1}`:
- **Case 1** (line 1473): the run stops before the end, `b_{J+J1+1} ≠ b_{J+J1}` with `J1 < M(S)−J`. Blow up
  along `{d_ij=0 (i∈run), u_{s,k}=0}` (line 1496).
  - **Case 1(1)** (line 1504): the run-block `= u_{s,k}·(d')` (factors out one more `u`). Measure: `S,J` fixed,
    `#{u_{s',k'} : t̃=J+J1}` **strictly decreases by one** (line 1580).
  - **Case 1(2)** (line 1581): a `1` appears (a unit pivot); regular `Q`,`P` clear the row/col, `D_J → D_{J+1}`.
    Measure: **`J` increases by one**; when `J+1 > M(S+1)`, `D'''_J` collapses to `(1,0,...,0)` and **`S`
    increases by one** (lines 1906-1912, the ideal picks up the next factor `C^(S+1)`).
- **Case 2** (line 1990): the run reaches the end, `b_{J+1}=...=b_{M(S)}` (all remaining equal). Blow up the
  ENTIRE remaining block at once along `{d_ij=0}` (line 1999). Same `Q`,`P` clearing; **`J`++ or `S`++**
  (lines 2275-2282).

Case 1 (proper run) and Case 2 (run-to-end) are jointly exhaustive and mutually exclusive: every state has
some maximal leading run, which either terminates internally (Case 1) or extends to the end (Case 2). The
chain invariant guarantees a *unique* run structure (no incomparable-vector ambiguity), so no third case can
arise. Terminates at `S=L+1`: `⟨∏C^(s)⟩ = ⟨diag(b_1,...,b_{M(L+1)})⟩` (line 2312) — diagonal monomial =
NORMAL CROSSING.

**Termination measure = lexicographic `(S, J, #{u : t̃=J+J1})`**, all bounded:
`S ≤ L+1`; `J ≤ M(S+1) ≤ min_s M^(s)`; the u-count ≤ #blow-up variables (finite). Every case strictly
decreases the measure on its coordinate. Nothing in the measure or the split refers to specific small values
of any `M^(s)` — it is driven ENTIRELY by the equal-value-run combinatorics, hence uniform in v.

**Read-off (lines 2342-2440, Lemma 3 lines 2596-2631).** RLCT candidates `½·min{M_{s,k} : t̃_{s,k}=0}` from
the diagonal exponents = exactly the S2/`monomial_rlct` `min_j (h_j+1)/(2k_j)` extraction. Lemma 3 is a pure
`min_b A(b) = aℓ(ℓ−a)` arithmetic minimization ⟹ `2λ = codim`, `θ = a(ℓ−a)+1`. The Appendix (Eqs (1)-(5),
lines 2790-3010) gives the *closed-form* `T_{s,k}` vectors and states (line 2382) "For every T_{s,k} we have
such sequences (H_i),(S_i)" — the uniform-in-v exponent bookkeeping.

---

## Why the 2013/2019 case-by-case is NOT the DLN's wall (the crux, resolved)

The companion Vandermonde work (2013 in-repo `/tmp/aoyagi-entropy.txt`) is on **Vandermonde matrix-type
singularities**: the `B` factor has entries `b_{ij}^k`, literal powers up to `H` (Example 1, line ~318:
`B = (b, b², ..., b^H)` is a Vandermonde matrix; general def lines 292-301). Consequences, stated in that
paper:
- Only **BOUNDS** `λ ≤ min{bound1,bound2,bound3}` (lines 610-611), obtained by **"choosing one branch of the
  blow-up process"** (lines 795, 864) — the branches do NOT collapse to one canonical monomial form.
- Exact values only "**when H is small**" (line 646), done case-by-case in [14] (Aoyagi-Nagata 2012).
- Its deepest-point method (Thm 2) and add-variables method (Thm 3) are EXPLICITLY **not unconditionally true
  over R** (Example 3, lines 478-506; Remark, line 529) — the RLCT-at-critical-point ≤ RLCT-nearby inequality
  can go the wrong way for a *non-homogeneous* / generic critical point.

The DLN product `∏C^(s)` is a **strictly easier, more special singularity**: multilinear (degree-1 in each
`C^(s)` block, degree-L overall homogeneous), no powers. Two consequences:
1. Thm 4 (deepest point) applies UNCONDITIONALLY because the `∏C^(s)` entries ARE homogeneous in the blow-up
   coordinates — the very hypothesis whose failure produces the 2013 counterexample is SATISFIED here. The
   2013 caveats attach to tools used fragilely on Vandermonde; the DLN use is clean.
2. The block-elimination (Lemma 2, lines 861-958; Thm 3-of-2024, lines 982-1223) reduces `∏C^(s)` to a form
   whose exponent vectors form a TOTAL CHAIN (the line-1459 invariant), so a SINGLE branch monomializes the
   ideal EXACTLY (equality `⟨∏C^(s)⟩ = ⟨diag(b_i)⟩`), not a choose-one-branch bound. Also `Q=1` in Vandermonde
   is still NOT the DLN case: even at `Q=1` the `B` entries carry powers `b^k` (Example 1), so Vandermonde-`Q=1`
   ≠ linear-DLN. The linear DLN is genuinely a different, easier class.

So the 2019/2013 case-by-case was forced by the Vandermonde structure, and it does NOT re-enter the DLN
induction. 2024 "unified" nothing about Vandermonde; it solved a DIFFERENT, more tractable problem exactly.

---

## Registers
- **Claim (load-bearing):** the DLN Section-5 (S,J) blow-up induction closes in diagonal-monomial form for
  ALL reduced dimension vectors. Uniformity rests on ONE invariant — the total-chain property of the exponent
  vectors `T_{s,k}` (line 1459) — plus a bounded lex measure `(S, J, #u)`. The case split (Case 1 proper-run /
  Case 2 run-to-end) is an exhaustive dichotomy, not a finite enumeration of dimension vectors. The base case
  (L=2 RRR, Thm 1) is itself general-v, not small-case.
- **Most likely to break this verdict (residual risk to hand the formaliser):** NOT a missing resolution step.
  The honest residual risks are (a) the chain-invariant preservation across Case 1(1)/1(2)/2 is asserted with
  a terse "Because {t̃=i}=ϕ ..." justification (lines 1568, 1670, 2094) — a formaliser must MACHINE-CHECK that
  each case genuinely re-establishes `T ≤ T' or T ≥ T'` for all v (this is the one spot the paper leans on a
  one-liner); (b) the Jacobian-exponent bookkeeping `M_{s,k}` matching the Appendix closed form (Eqs 1-5) is
  intricate and layout-garbled in the extraction — verify against Thm 2's final number. Both are
  BOUNDED-COMBINATORIAL checks, not analytic walls.
- **Next construction that would settle the residual:** formalize (or hand-verify on paper for L=3 with a
  non-monotone `M^(s)`, e.g. `(M^(1),M^(2),M^(3),M^(4)) = (2,5,1,4)`) the chain-invariant induction step —
  confirm Case 1(1)/1(2)/2 each carry `T ≤ T' or T ≥ T'` forward. If it does (expected), D1's blow-up
  combinatorics are a bounded build; the ∀-v lift is the chain-induction + Jacobian bookkeeping + Lemma 3,
  with NO Morse-Bott / Hironaka / IFT-with-parameters.

## Decorrelated Codex (PDF-grounded, web OFF, xhigh, hypothesis withheld)
`codex/uniform-answer.md` — independent read of the SAME two primary texts from scratch (my leaning
withheld; it cross-read specific line ranges of both PDFs, not just skimmed). Reached the SAME verdict —
**UNIFORM** — with the SAME structural findings: (i) the load-bearing total-chain invariant `T ≤ T' or
T ≥ T'` carried and re-asserted each case (2024 lines 1457-1464, 1567-1572, 1666-1680, 2089-2098); (ii) Case 1 /
Case 2 mutually-exclusive-and-jointly-exhaustive on "first nonempty t̃-level above J vs none before M(S)";
(iii) the SAME lex measure `((L+1)−S, min(M(S),M^(S+1))−J, |E_h|)` with Case 1(1) decreasing `|E_h|`; (iv) the
SAME crux resolution — 2013 Vandermonde is a *branch-chosen upper-bound* scheme with higher-monomial
generators `(b^Q − b^Q)` and explicit R-counterexamples to its deepest-point/add-variables tools, whereas
2024 DLN is an *exact* block-elimination monomialization; (v) Theorem 1 (RRR [12]) is a complete piecewise-exact
formula over all relative-size cases, NOT a hidden non-uniform base case. Codex independently found no
dimension vector fitting neither case and no dimension-specific failure of the minimal-element pick. It also
independently flagged the one residual: each case only *reasserts* the total-order property (the terse
"Because {t̃=i}=ϕ" justification) — the spot a formaliser must machine-check. Full decorrelation on the
verdict.

## Interaction with the other checks
- Confirms KC-2 (d1route) POSITIVE: the induction IS uniform. Combined with `d1thm4` (Theorem-4 feasibility),
  this de-conditionalizes D1 to a bounded build.
- Consistent with KC-1: Thm 4's homogeneity hypothesis is exactly what the DLN multilinear structure supplies
  (and exactly what the Vandermonde class fails, producing the 2013 counterexample).
- Consistent with KC-3: read-off is via `monomial_rlct` only; no second analytic axiom is introduced by the
  induction (Thm 4 is the single extra analytic atom, and it is used cleanly here).

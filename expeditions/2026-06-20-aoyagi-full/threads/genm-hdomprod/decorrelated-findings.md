# genm-hdomprod — decorrelated scout + codex findings (the `hDom` producer de-risk)

Two pen-and-paper seats + a codex xhigh consult, all decorrelated, adjudicated the three
gating unknowns of the `∀ v, hDom v` producer. All three converge.

## Item (5) — the C¹→C² regularity gap: STATED-CEILING ARTIFACT (not an obstruction)

Codex xhigh (`codex/item5-regularity-{prompt,answer}.md`) + a source-read of the chain:
`dln_hchart_residual` already produces a LOCAL `ContDiffOn ℝ 2` composite before the bump
(`hg1CD`, line 378). Every step is genuinely C^∞ or preserves the regularity parameter:
- `contDiff_chartΦ` proves each coord `ContDiff ℝ ⊤`, downgrades to 2 via `.of_le`.
- `ContDiffAt.to_localInverse` (Mathlib) preserves C^n exactly (no derivative loss), n ≠ 0.
- `contDiffOn_rawResidVec` = C^∞ loss ∘ Ψsymm, inherits Ψsymm's regularity.
- `exists_contDiff_eventuallyEq_of_contDiffOn {n : ℕ∞}` is PARAMETRIC in n; called at `(n := 1)`.
The ONLY downgrade to C¹ is the final bump call `(n := 1)`. Changing it to `(n := 2)` +
strengthening the four `2`-ceiling signatures gives a C² (even C^∞) `q` with NO new analytic
content. Minor-det division: no new singularity. Bump product χ·g: C^∞·C^k = C^k. Global C²
via bump-globalising local C²: yes. VERDICT: bounded, strengthenable — proceed.

## Item (2) rectangular value arithmetic — WITNESS (clean), with the RIGHT extra

Seat `a979b046` (sympy exact, box 16, + decorrelated codex, 0 violations):
The value inequality `lambdaCore(M) ≤ extra/2 + lambdaCore(M')` for RECTANGULAR
`M = (m0,m1,m2)`, `M' = (m0−a, m1−a−b, m2−b)` holds UNCONDITIONALLY iff
  **extra = a·m2 + b·m0 − ab  (CROSS-paired: a with BACK m2, b with FRONT m0).**
The straight-paired `a·m0 + b·m2 − ab` FAILS off m0=m2 (1448/7887 violations). Square m0=m2=m
hides the difference. The exact ℤ telescope identity (proven symbolically):
  `(a·m2 + b·m0 − ab) + Mval(M', ![t0,0]) = Mval(M, ![t0+a, 0])`,  shift s=a (unique).
Adm-membership: `t0 ∈ Adm(M') ⟹ ![t0+a,0] ∈ Adm(M)` (unconditional: t0+a ≤ min(m0,m1)).
Ready-to-formalise (rect telescope lemma + Adm-lift + inf'_le corollary).

## Items (1)/(4) DLN Jacobian excess — CROSS-paired, matches the value seat

Seat `a51a79d0` (4 decorrelated routes: analytic incl-excl, integer pts, dense-generic,
symbolic-generic; + decorrelated codex):
Differential D[δW1,δW2] = W2·δW1 + δW2·W1 at rank(W1)=r+a, rank(W2)=r+b:
  **rank(D) = (r+b)·H0 + (r+a)·H2 − (r+a)(r+b) = H0·H2 − (H2−r−b)(H0−r−a)**, H1-INDEPENDENT.
So `extra = rank(D) − nReg = a·m2 + b·m0 − ab` — the CROSS-paired form, EXACTLY the value
extra. The two seats agree ⟹ the headline step `rlct ≤ extra/2 + core` closes UNCONDITIONALLY;
no sign condition, no curvature correction. (Straight-pairing would have needed
(a−b)(m0−m2)≥0, NOT forced — seat exhibited realizable (1,2,2,1,0) with sign −1. Cross-pairing
makes it harmless.)

## Consequence for the producer architecture

The prior hand's "not closable by wiring the current bank" was because the bank is SQUARE-only.
The rectangular pieces are clean bounded generalizations, now certified decorrelated. The
`extra` the Lean chain must carry is the CROSS-paired `a·m2 + b·m0 − ab`; the existing
`extraCount m a b = m(a+b) − ab` is only its square specialisation. A rectangular `extraCountRect
m0 m2 a b := a·m2 + b·m0 − ab` is the object to introduce. Open geometry audit flagged by both
seats: confirm the lambdaCore argument-order / M' width-assignment convention matches the
(m0=H0−r, m2=H2−r) labelling (a one-line audit against the value chain).

## Reviewer verdict (fidelity + soundness + decorrelated Codex) — SURVIVED

A reviewer (with its own decorrelated Codex xhigh) audited the four built modules: all sorry-free,
clean-three, mathematically faithful. `d1ge_L2_rect_two_peel` is a GENUINE reduction — the three gates
(hrank₂, hRne, hInterface) are fed the chart's OWN facts as antecedents (the established non-laundering
idiom), satisfiability witnessed inside; none is a disguised wall or a restatement of the conclusion;
the `extra/2` gap is supplied by the honest quasi-split engine (not hInterface ⟹ not circular); the
degraded-core value is a genuinely separate banked R1 result. The item-5 C² is real (bump at (n:=2) on
a ContDiffOn ℝ 2 composite). The cross-paired extra confirmed the load-bearing one; non-vacuity
tight-checked at (5,6,3,2,1). One precision note actioned: co-located an `a=b=0` non-vacuity caveat
(the reduction is content-bearing only at a genuine middle stratum). NOTHING laundered.

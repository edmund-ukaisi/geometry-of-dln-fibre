# synthesis.md — `perm-invariance` (controller's internal integrative ground)

Recovery substrate (recover from `brief + priorities + threads + synthesis`). Flush every tick. In-repo only.

## Quest (one line)
Prove `(C,θ)` permutation-invariance (Cor 5.10) — `cCodim`/`numTop` depend only on the multiset of `d` —
via a zero-cited combinatorial route (not the equivariant-cohomology Thm 5.5).

## State (2026-06-21 — SETUP)
- Branch `expedition/perm-invariance` off `dev` (= rlct-payoff merged, PR #5 / merge `52995d1`). Green
  baseline 3679 jobs, 0-sorry, axiom-clean (tree identical to dev; `.lake` valid).
- Controller in the (legacy-named) `voigt-discharge` worktree (main checkout is the live aoyagi session) ⟹
  serial Lean-writers. **No build yet — sizing pass FIRST (P0).**
- Worktree hygiene: removed merged-stale `c-theta`/`ext-codimension`; the rest of the sprawl is other live
  sessions' (aoyagi-*, agent-*, fm/fm-2, d1-scope[uncommitted], semantic-audit, /tmp) — left for the operator.

## LANDED (consumable)
`Core.CTheta` (cCodim/numTop/codimForm/kostantPartitions, cCodim_rankShift) · QIP Thm 6.1 (monotone d) ·
explicit Thm 7.10 (CThetaValue/Explicit) · CCodimZeroMono/Strict (dim-monotonicity) · the geometric (C,θ)
bridges (SigmaComponents/ThetaComponentCount/CThetaGeometric).

## Hard piece / suspicion
The heart is `cCodim d = cCodim (sort d)` for ALL `d` (the QIP/explicit forms are monotone-`d`-only). The
roadmap flags Cor 5.10 "a genuine lift, NOT free," derived in the paper via equivariant cohomology (Thm 5.5).
The sizing pass must find/confirm the independent combinatorial route (codimForm/Kostant symmetry under
permuting `d`) and whether it avoids Thm 5.5.

## Carried meta-lessons (from voigt-discharge + rlct-payoff)
Size hard pieces before building · serial Lean-writers (controller-in-worktree) · decorrelated Codex/pen-and-paper
on hard/at-risk steps · green-gate + AUDIT + name=content every result · flush synthesis every tick · controller
stays executive (delegate object-level).

## Next action
Dispatch the sizing pass (thread 01, pen-and-paper, decorrelated Codex) → re-scope the ladder → build.

## 2026-06-22 — SIZING VERDICT (thread 01): NO short zero-cited route to full Cor 5.10 → SCOPE FORK
Permutation invariance is TRUE (re-confirmed exactly: (1,2,3) perms → (C,θ)=(2,1); (1,2,2,3) → (2,2); single
adjacent-swap 0/3868 fails; non-monotone-sort 0/1345). But the route analysis (exact algebra; Codex endpoint
was down) gives a genuine scope-surprise:
- **(a) adjacent-transposition (zero-cited): TRUE but it is an OPEN PROBLEM.** No value-preserving Kostant
  bijection (cardinalities differ 2932/3868 — the paper's own line-1122 obstruction), no bounded surgery
  (edit radius unbounded, grows with |d|) ⟹ a large min-argument tide, HARDER than the landed
  CCodimZeroMono+Strict pair. AND a purely combinatorial proof of the underlying q-series identity is
  "an open problem the authors say they lack" — so this route = NEW RESEARCH, not formalising known math.
- **(b) reduce-to-sort: not independent** — its content is (a) or (d) (the paper's Thm 6.1 itself uses Cor 5.10
  for non-monotone d; circular).
- **(c) full Kostant bijection: REFUTED** (cardinalities differ). EXCEPTION: **order-reversal `[a,b]↦[N−b,N−a]`
  IS a clean codimForm-preserving bijection (0/11795)** ⟹ `(C,θ)(d)=(C,θ)(reverse d)` is a CHEAP zero-cited
  lemma (order-2 subgroup only).
- **(d) Thm 5.5 Pochhammer product: CERTIFIED, short to the headline, but CITED.** `Q^r_d = P_r ∑_s (−1)^s
  q^{C(s,2)} P_s P_{d−r−s}`; `∏_i P_{d_i−r−s}` is manifestly multiset-symmetric ⟹ one-line Cor 5.10. But its
  DERIVATION is equivariant-cohomology (Mathlib-absent) — a Cited layer (like Aoyagi / Lemma 4.6).

**SCOPE FORK (operator decision — the brief's sanctioned scope-surprise close):**
(A) CITE Thm 5.5 (named interface, ethos-consistent) → full Cor 5.10 Cited + order-reversal + geometric transfer
    zero-cited. Short, honest. [RECOMMENDED — zero-cited is an open problem the authors lack.]
(B) Attempt zero-cited route (a) — NEW research (combinatorial proof the authors don't have); high-risk, multi-week.
(C) Scope down: land order-reversal + geometric transfer zero-cited; roadmap full Cor 5.10 (no cite-interface).
Order-reversal fragment is landable zero-cited bedrock regardless. SURFACED to operator.

## 2026-06-22 — AMBITIOUS RE-SCOPE (operator: "what is your ambitious suggestion")
Operator asked for the ambitious version. DECISION: do NOT cite Thm 5.5 by default — SWING for the OPEN
PROBLEM (a zero-cited combinatorial proof of Cor 5.10, which the authors lack), with a graceful Cited fallback.
Prize if it cracks: the WHOLE combinatorial side zero-cited + general (all d) — Poincaré series closed form,
explicit (C,θ) for all d (extends monotone-only Thm 7.10), Cor 5.10 as a one-line corollary; + a new
math contribution. Our EDGE: the strict-cert corner-pair rigidity (minimisers = corner pairs only; 256521/256521).

Two-pronged DECORRELATED bounded probe LAUNCHED (background):
- **thread 02 (probe-direct):** corner-pair rigidity → manifestly-symmetric closed form for (C,θ) on all d;
  and/or a MIN-LEVEL adjacent-transposition map (weaker than the refuted full Kostant bijection).
- **thread 03 (probe-qseries):** combinatorial/bijective proof of the Thm 5.5 identity (or its lowest-degree
  term θ q^C) — sign-reversing involution / LGV lattice paths / q-Vandermonde / recursion.
Each: exact-arithmetic-verified, Codex-decorrelated, bounded, honest verdict (crack/partial/obstruct).

DECISION RULE: either prong yields a Lean-targetable proof ⟹ formaliser tide for general (C,θ) + Cor 5.10
(zero-cited, the big win). Both stall ⟹ fallback = cite Thm 5.5 as a named interface (like Aoyagi/Lemma 4.6)
+ derive Cor 5.10 + LAND the order-reversal fragment (0/11795, codimForm-preserving bijection) zero-cited.
Order-reversal is bedrock either way. AWAITING the two probe verdicts.

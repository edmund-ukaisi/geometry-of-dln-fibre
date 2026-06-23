<task>
You are red-teaming ONE architectural truth-value that decides whether a Lean formalisation of the FULL
general-parameter learning coefficient closes, or only its deepest-point special case. DECORRELATED — I
withhold my tentative conclusion.

SETUP. Deep linear network: parameters = a chain of matrices (C_1,…,C_L), loss
F(C) = ‖C_L···C_1 − B‖²_Frobenius for a target matrix B of rank r. The "learning coefficient" (RLCT,
Watanabe) at the GLOBAL minimum = the MIN over the optimal set (the fibre {C : C_L···C_1 = B}) of the
LOCAL RLCT at each optimal point. (rlct of a min-over-fibre = inf of local rlcts.)

The plan to compute it has three layers, with a clean dependency order:
  (D1) "deepest-point reduction" (Aoyagi 2013 Thm 2): the inf over the fibre is ATTAINED at the
       deepest/most-degenerate point. PROVEN as a monotonicity: it applies to a HOMOGENEOUS core
       (the generators must be homogeneous), DOWNSTREAM of the reg/core split. D1 itself is light
       (a blow-up-scaling comparison; the lemma rlctAt_mono is green). D1's input is the homogeneous core.
  (L2) "product_reduction" / the REG/CORE SPLIT: at an optimal point v (in the fibre, where C_L···C_1=B
       so the LINEAR part of F at v is NONZERO — v is a smooth point of the fibre direction), split
       F = [regular nondegenerate quadratic block, dim nReg] ⊞ [homogeneous core (no linear part)].
       This is the constant-rank / Morse-splitting step: peel the nReg directions where F has a nonzero
       gradient (the "regular" block) from the singular "core". At the DEEPEST point (v with C_L···C_1=0,
       i.e. B=0 reduced) this split is proven via explicit triangular UNIT-PIVOT elimination (identity
       corners from the block-normal form ⟹ each regular generator g_i = u_i·z_i + h_i, u_i(0)=1 a unit
       pivot, solved by division-by-unit — NO general constant-rank theorem; a prior cert). At a GENERAL
       optimal v (nonzero linear part, rank-pattern T_v) the same elementary route was argued to work via
       a gauge-to-identity-corner + triangular unit-pivot elimination (a second prior cert), avoiding the
       Mathlib-absent general constant-rank/Morse theorem — but it was flagged constant-rank-GATED with
       the unit-pivot revival lead unprobed in full.
  (R1 §4) the RESOLUTION of the homogeneous CORE: a recursion (the "cascade" realizing each admissible
       rank pattern T as a tuple C_s = diag(1^{t_{s+1}}, 0); per-node analytic "hnode" Schur charts; a
       Fubini-shear at partial-drop nodes). This machinery resolves the CORE — it takes the core
       (already split off, homogeneous, deepest point) as its INPUT.

THE QUESTION (decide: SAME-MACHINERY witness, or SEPARATE-STEP obstruction):
The R1 §4 cascade/hnode machinery now resolves the local chart at EVERY rank pattern T (the core's
resolution). Does that SAME machinery ALSO SUPPLY the L2-at-v reg/core SPLIT at a general optimal v? OR
is L2-at-v a genuinely SEPARATE step — the hnode being the resolution of the core DOWNSTREAM of the
split, with the split (the constant-rank peel of the nReg regular directions) an UPSTREAM step the hnode
ASSUMES already done?

Specifically:
  Q1. Logically, does resolving the homogeneous core (R1 §4) PRESUPPOSE that the regular block has
      already been separated? I.e. is the core even DEFINED before the split? Argue from what the
      cascade/hnode takes as input (a homogeneous core at its deepest point) vs what L2-at-v produces
      (the split that ISOLATES that core from the nReg regular directions). Is the split logically
      upstream of the resolution?
  Q2. Could the cascade/hnode be RE-PURPOSED to perform the split — e.g. does the per-node Schur/blow-up
      chart, applied to the FULL loss F (with its nonzero linear part at v), naturally peel the regular
      directions as a byproduct? Or does the nonzero linear part at v (the regular block) require a
      DIFFERENT mechanism (unit-pivot elimination / Morse) that the hnode (which assumes a homogeneous
      core, no linear part) does not perform?
  Q3. If SEPARATE: at a general optimal v with nonzero linear part, is the reg/core split reachable via
      the unit-pivot revival (gauge-to-identity-corner + triangular unit-pivot elimination, exploiting
      the rank-r structure and the multilinearity of the chain product), or is there a residual that
      genuinely needs the Mathlib-absent general constant-rank/Morse theorem? Distinguish: "the
      multilinear chain product makes every regular generator a unit-pivot triangular system (elementary,
      formaliser-scale)" vs "a general optimal v has a regular block that cannot be triangularized
      without the abstract constant-rank theorem."
  Q4. NET: does the FULL general-parameter learning coefficient close via (cascade/hnode for the core) +
      (a SEPARATE but formaliser-scale unit-pivot L2-at-v split)? Or is L2-at-v a genuine constant-rank
      research gap, making the honest general target the DEEPEST-POINT form only (with the general-v
      D1≥ / fibre-inf roadmapped)?
</task>

<output_contract>
Answer Q1–Q4 in order, ≤180 words each. For Q4 end with one line:
VERDICT: SAME-MACHINERY (hnode supplies the split) | SEPARATE-BUT-REACHABLE (unit-pivot, formaliser-scale) | SEPARATE-RESEARCH-GAP (constant-rank, Mathlib-absent).
Mark each claim [FACT] (forced by the stated structure) or [INFERENCE] (judgement). Do NOT rubber-stamp;
if the unit-pivot route hides a constant-rank dependence at a general v, say so and give the minimal
obstruction.
</output_contract>

<grounding_rules>
Reason about Morse/constant-rank splitting, blow-up resolution, multilinear chain products, Schur
complements, RLCT. The load-bearing distinction: "the SPLIT (peel the nReg regular directions, a
Morse/constant-rank step at the smooth fibre point v)" vs "the RESOLUTION (blow up the homogeneous core
to a normal-crossing/monomial form)". Keep them separate. A homogeneous core has NO linear part; a
general optimal v has a nonzero linear part (the regular block). Flag inference vs forced-fact.
</grounding_rules>

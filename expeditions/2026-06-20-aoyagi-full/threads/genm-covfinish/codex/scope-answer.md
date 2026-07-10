**1. Q1 Verdict**

**NO: hIH does not close the deeper branch; that branch is the recursion.** [inferred]

Crux: hIH only applies to ordinary shorter-chain box integrals, while the deeper branch still contains the peeled Γ-coupling with rank-deficient `Q_b`; no banked lemma converts that decorated/rank-deficient integral into `routeMLayerBoxIntegral(redChain t M)` or `tailChain M`. [from the facts I gave + inferred] `sjChargeBudget_le` gives threshold bookkeeping, not an analytic reduction. [inferred]

**2. Q2 Verdict**

Your reading of (c) is correct. [from the facts I gave] The stated banked docstrings identify `sjJointResolution` as the remaining analytic sorry requiring a well-founded `(S,J)` double induction. [from the facts I gave] The handoff in (d) is over-scoped: the “good” branch can plausibly use the endpoint where full-rank hypotheses hold, but the “deeper” branch needs a new rank-stratified/decorated reduction, not just hIH on `redChain` or `tailChain`. [inferred]

**3. Q3 Ranked Deliverables**

1. **Build transport composition: step b + compose a+b+c into a sorry-free equality.** [inferred] Highest value because step b is explicitly the only unbuilt transport atom and “no API wall” is claimed. [from the facts I gave]

2. **State/isolate the remaining finiteness lemma in v-exposed coordinates.** [inferred] This cleanly marks the analytic gap: rank-deficient Γ/deeper resolution, not transport or threshold algebra. [inferred]

3. **Do not attempt the good/deeper+hIH close as the main tide.** [inferred] It depends on an unbanked decorated reduction from the deeper branch to a shorter-chain box integral. [from the facts I gave + inferred]

**4. Shortcut**

None — it is the recursion. [inferred] The missing mechanism would be a rank-stratified Schur/fibre recursion for the decorated residual integral, i.e. the `(S,J)` engine itself. [from the facts I gave + inferred]
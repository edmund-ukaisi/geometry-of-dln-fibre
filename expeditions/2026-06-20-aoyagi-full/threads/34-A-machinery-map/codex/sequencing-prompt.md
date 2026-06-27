<task>
Lean 4 + Mathlib formalisation. Goal: prove the FULLY GENERAL theorem
`aoyagi_learning_coefficient` (the global learning coefficient / real log-canonical
threshold of a deep linear network's square loss equals Aoyagi's closed form, for any
depth L and rank r), for all dimension vectors — not just fixed small instances.

The proof assembles from four "gates" (each currently an open `sorry` in the build, all
in namespace DLNFibre.DLN.RLCT):

  GATE D1 (Skeleton.lean:1131) `rlctAt_deepest = (r·(H0+HL−r))/2 + lambdaCore(H−r)`
      — the global infimum equals the local RLCT at the constructed deepest point, and
        that local RLCT is the closed-form value. (local→global assembly + value)
  GATE L2 (Skeleton.lean:1177) `rlctAt_deepest ≤ rlctAt at any optimal v`
      — the deepest point is the minimiser (gauge-chart producer / deepest-point reduction).
        Open frontier = 5 sorries across 2 files: DeepestGaugeChart.lean (1: chart NONEMPTY),
        DeepestGaugeConstruction.lean (4: an L=2 diffeo arm, two L≥3 interior `hinterface`
        arms, one L≥3 grouped-G0 diffeo). The other 28 Deepest* support files are sorry-free.
  GATE R1 (Skeleton.lean:1234) `resolution_charts: rlctAtOn(core at 0) = ⨅ monomialThreshold`
      — the rank-profile determinantal resolution as explicit monomial charts. Splits into:
        * R1 LOWER leg = ONE open sorry `routeMCore_box_diverges_achiever`
          (RouteMLayerCoverGE.lean:133): box integral diverges at/above the achiever
          threshold ½·minAdm M, for all M. This is discharged the instant we can INHABIT
          a structure `NodeAchieverChart M` (the M-agnostic divergence ASSEMBLY from the
          structure is already proven sorry-free). The structure needs: an analytic chart
          map `phi_M : (Fin N → ℝ) → (Fin N → ℝ)`, a binding pivot axis p, Jacobian
          exponents `leafH` with `leafH p = minAdm M − 1`, a unit factor U (bounded +
          a.e.-positive), the leaf-integrand identity, a change-of-variables `cov`, and
          image containment. Two concrete instances built sorry-free: (4,4,2,2), (3,3,4),
          (3,3,3,3). Two reusable ENGINES already banked + GATED, axiom-clean:
            - `Chain.chain_telescope` (RouteMAchieverTelescope.lean): the abstract
              chained-product telescope giving `prod M (phi_M u) = u · H` from per-level
              local identities.
            - `general_composed_clm_abs_det` (RouteMAchieverGeneralDet.lean): the variable-
              length composed-determinant telescope `|det Dphi_M| = ∏ per-factor-det`.
          The remaining work (tasks): build the per-M `Chain` instance (block construction),
          the det = u_p^(minAdm−1)·spectator, the unit U, the cov, then assemble.
        * R1 UPPER leg = `routeMCore_threshold_lt_top` (RouteMSchur.lean:284): box integral
          FINITE below ½·minAdm — the depth-r WellFounded-on-corank measure-theoretic Schur
          recursion (flagged the HIGH-risk long pole). Plus the routeStep/atlas migration
          blocker (RouteMRecursion.lean:257) from a fixed-arity carrier to the
          layer-collapsing `routeLayerAtlas` (controller-gated staged surgery; the genuine
          machinery is sorry-free in RouteMLayerSplit.lean).
  HEADLINE (Skeleton.lean:1725) `aoyagi_learning_coefficient` itself: assemble D1▸L2▸R1 then
      identify ½·minAdm with Aoyagi's closed form `aoyagiLambda`. (Plus a secondary θ
      deliverable `aoyagiTheta_eq`, Skeleton.lean:1707, flagged optional.)

There are also COMBINATORIAL machinery files, all sorry-free but UNGATED (escape the green
gate): CascadeAchiever (rank-pattern realizability tie `rankFn = achieverRankPattern`),
RouteMAchieverForce (binding-T* achiever realizability forcing field), RouteMBranchRead
(rank-pattern read seam), BindingSpine/BindingRecursion/BindingArith (the binding RLCT-recursion
skeleton bottoming at the degenerate child), RouteMValue/RouteMNReg/MvalMultSum (value folds).
These feed the value-side / upper-leg, NOT the analytic chart construction.

KEY OBSERVED FACT (verified in-code): the two concrete chart instances (4,4,2,2) and (3,3,3,3)
build their `phi`, `leafH`, det from PURELY GEOMETRIC inputs — a Schur frame CLM ∘ a radial
blow-up on the deepest active factor, with leafH p = minAdm−1 — and do NOT consume
achieverRankPattern / cascadeTuple / RealizesAchiever. So the lower-leg chart construction
appears geometrically independent of the combinatorial cascade/achiever machinery; the
cascade machinery serves the value-fold and the upper-leg instead.

13 total open sorries (verified): 5 inside the green-gate (D1×1 line 1131, L2-min×1 line 1177,
R1-θ + the two D1/value lines... actually: Skeleton×4, RouteMLayerCoverGE×1), 8 escape
(DeepestGaugeChart×1, DeepestGaugeConstruction×4, RouteMRecursion×1, RouteMSchur×2).
</task>

<output_contract>
  1. RECOMMENDED BUILD ORDER: a numbered sequence over {R1-lower NodeAchieverChart M producer,
     R1-upper threshold_lt_top recursion, the routeStep/atlas migration, L2 gauge-chart 5 sorries,
     D1 assembly+value, headline ½·minAdm=aoyagiLambda, the θ secondary}. For each step give the
     ONE sentence justifying its position (what it unblocks / what it depends on / its risk).
  2. The single RISKIEST piece (most likely to reveal a hidden wall) and the cheapest early probe
     that would surface that wall before sinking a full build into it.
  3. DEPENDENCY VERDICT: confirm or challenge the claim that the R1-lower chart construction is
     independent of the combinatorial cascade/achiever machinery — and if independent, name the
     ONE place in the WHOLE proof where the cascade/achiever realizability tie IS load-bearing
     (so it is not orphaned).
  4. Any SEQUENCING TRAP you see (e.g. wiring/gating order, a piece that looks ready but depends
     on an un-migrated carrier, a clash that bites only at assembly).
  Keep it under ~500 words. Terse, ranked, decision-shaped. Flag inference vs. what the brief states.
</output_contract>

<grounding_rules>
  You are reasoning from the structured description above (an in-repo machinery map), not from
  reading the repo. Treat the file:line facts and sorry counts as given. Where you INFER a
  dependency or risk not stated above, mark it "(inference)". Do not invent Mathlib lemma names
  or claim a piece is done that the brief lists as sorried.
</grounding_rules>

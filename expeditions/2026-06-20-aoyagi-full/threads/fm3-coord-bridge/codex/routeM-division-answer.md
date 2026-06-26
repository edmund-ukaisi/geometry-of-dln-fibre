**1. Recommendation**

Choose **C, with a B-like split of responsibility**: rebase fm3’s chart/index/value recursion onto crux2’s `ChainDimSplit` descent, and let crux2 own the analytic RLCT recursion. The decisive reason is that `ChainDimSplit` already encodes the one-step reduction state consumed by `schur_recursion_step_sound`; duplicating it with `RouteState/schurState` creates two termination arguments and two notions of “the next residual chain” that must remain extensionally equal. fm3 should own the finite leaf family `(ι,d,k,h)` and `IsResolutionAtlas`; crux2 should own the per-step analytic descent and cover/transport hypotheses.

This is architectural judgment, not forced by type theory. It depends on the assumption that `schur_recursion_step_sound`’s supplied-chart hypothesis can be discharged from the G2 node factorization facts you already have, plus crux2’s `schur_straighten_of_data`.

**2. Cover Facts**

For general `M`, the RLCT identity should come from **telescoping per-step `schur_recursion_step_sound` down to the `L=1` base**, not from one global `cover_le`/`cover_ge_div` over the entire tree.

A single tree-wide integral bound is conceptually valid, but in Lean it is the harder route: it forces you to compose all blow-ups, domains, Jacobian factors, finite covers, and leaf charts in one global object. The per-step theorem already isolates exactly the analytic burden at each reduction. Then the leafwise `⨅` should be reconstructed algebraically along the recursion.

So the less Lean effort path is:

```lean
RLCT(M)
= nReg₁/2 + RLCT(Mred₁)
= nReg₁/2 + nReg₂/2 + RLCT(Mred₂)
= ...
= ⨅ leaves, monomialThreshold ...
```

rather than proving one all-at-once `IsRouteMCover` for the full tree.

**3. Parallel-Recursion Hazard**

The separate `RouteState` recursion is a genuine liability unless it becomes a thin wrapper over `ChainDimSplit`. The danger is not just duplicated code; it is duplicated invariants: residual widths, dropped dimensions, admissibility of next states, termination measure, and leaf data accumulation all need synchronization with the analytic descent.

The value combinatorics may want its own *data accumulator*, but it should not own an independent *state transition system*. Better shape:

```lean
ChainDimSplit / crux2 step relation
  ↳ analytic recursion: crux2
  ↳ leaf monomial data accumulation: fm3
```

So keep `MonoData`, leaf indexing, and threshold proofs on fm3’s side, but make the recursion driver shared.

**4. Concrete Next Step**

Prove a green, stackable lemma that does not commit to A/B/C:

> the monomial data update for one Schur/pivot reduction preserves the intended threshold formula.

Concretely: define the per-step transformation on `(d,k,h)` induced by adding the regular quadratic block `nReg/2`, and prove the corresponding threshold identity/inequality needed for telescoping:

```lean
monomialThreshold (updated_d ...) (updated_k ...) (updated_h ...)
=
nReg / 2 + monomialThreshold d k h
```

or whatever the exact additive convention is in your development.

That lemma is useful in B and C, and even in A. It also keeps fm3 focused on the value/index side while avoiding another analytic cover proof.
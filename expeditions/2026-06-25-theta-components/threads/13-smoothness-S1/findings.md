# Thread 13 — S1 smoothness gating witness (pen-and-paper) — certificate

**Persisted by the controller** (the subagent is harness-blocked from writing report files; scripts +
Codex artifacts are on-branch under `threads/13-smoothness-S1/scripts/` and `.../codex/`).

## HEADLINE — three exact verdicts

The S-submersive smoothness route is **viable and wall-free**, but smoothness is **not a single global
chart**: it is an **atlas of `θ` `SubmersivePresentation`s**, one per top component, glued over the
generic-locus open cover.

## 1. Rank = C+δ generically on EVERY top component — YES (the H3b computation the codim route skipped)
The fibre Jacobian `J = [∂(mult−E)_{ij}/∂entry]` (shape `(d_N·d_0) × dimRep`) attains its expected rank
`Q` (= fibre codim) on the dense open of each top component. Per-prime check: `#(Q-minors mod p) > 0` and
`#((Q+1)-minors mod p) = 0` ⟹ generic rank exactly `Q`. **The fibre is generically smooth of the expected
dimension.** Verified exact:

| case | dimRep | cut eqs `d_N·d_0` | Q (=C+δ) | #top (=θ) | rank=Q on every top? |
|---|---|---|---|---|---|
| (2,2,2) r=1 | 8 | 4 | 4 | 2 | YES |
| (2,2,2,2) r=1 | 12 | 4 | 4 | 3 | YES |
| (3,3,3) r=2 | 18 | 9 | 9 | 2 | YES |
| (2,2,2,2,2) r=0 | 16 | 4 | 3 | 6 (+4 lower codim-4) | YES on all 6 |

## 2. The witnessing minor is PER-COMPONENT, not global (the load-bearing structural fact)
Exhaustive `(C+δ)`-minor enumeration: **# minors nonzero on every top component = 0** in all four cases
(for `(3,3,3) r=2`, a complete sweep of all 48620 `9×9` minors). Per-component surviving-minor sets are
**disjoint**. On `(2,2,2,2,2) r=0` each component's first-surviving `3×3` minor has incidence vector
exactly `e_c` (pivot columns in a component-specific arrow pair). **Opposite of thread-07's source-side
`detΔ`, which is a single global pivot.**

**Structural why (Codex-concurred independently):** `rank J = δ + C_sh`, where `δ = r(d_0+d_N−r)` is the
determinantal codim of `Σ̄^{≤r}` at `E_r` (uniform endpoint block) and `C_sh = cValue(shifted)` the
shifted zero-product Jacobian rank — exact-verified `Q = δ + C_sh` on all four cases. The shifted
(rank-drop) part of `dF_A = Σ_i L_i Ȧ_i R_i` is carried only by arrows in that Kostant component's active
interval; different top components use disjoint arrow-intervals ⟹ admissible pivot columns mutually
exclusive. No fixed column set serves all.

## 3. Kill-condition CLEARED — the S-submersive route does NOT inherit the reducedness wall
`SubmersivePresentation` (`RingTheory/Extension/Presentation/Submersive.lean:502`) extends
`PreSubmersivePresentation` by the **single** field `jacobian_isUnit : IsUnit P.jacobian` (the chosen
square `(C+δ)` minor is a unit in the chart algebra). `IsStandardSmooth ⟹ Smooth R S`
(`StandardSmoothCotangent.lean:339`) takes only `[IsStandardSmooth R S]`. **Grep: zero occurrences of
`Reduced`/`Flat`/`Noetherian`/`IsDomain` in either file.** The route needs only the minor-unit; it does
NOT touch the Part-1 reducedness wall.

## Net consequence for the route (load-bearing for the formaliser plan)
Smoothness is provable, but **not as one global submersive chart**. The honest object is an **atlas of
`θ` `SubmersivePresentation`s** — one per top component, on its chart `{minor_c ≠ 0}` (the localization at
that component's minor), glued over the open cover `⋃_c {minor_c ≠ 0}` of the generic locus. Each generic
fibre point lies on exactly one top component whose chart-minor is nonzero ⟹ charts cover (confirmed via
the `e_c` incidence on `(2,2,2,2,2) r=0`). This is analogous to but **strictly heavier** than thread-08's
single `{detΔ≠0}` localization — a finite family indexed by `topComponents`, reusing
`bijOn_partitionIdeal_topComponents`.

## Scope / the proven-vs-conjecture dividing line (the gate for the S formaliser)
- **Proven exact (these 4 cases):** rank = Q per top component; no global minor; per-component witness.
  `(3,3,3) r2` is a complete minor enumeration.
- **Proven general:** the kill-condition (only `jacobian_isUnit`; `IsStandardSmooth ⟹ Smooth`
  side-condition-free).
- **Conjecture (Codex-concurred, NOT proved here):** rank `= δ + C_sh` and per-component-minor for
  general `d, r` with `θ ≥ 2`; leans on the cited Kostant-component description. **This is the gate: the
  S2–S4 formaliser needs the *general* statement, not 4 cases — either harden this witness to a general
  proof, or carry it as an Assumed/Cited interface.**
- **Sharp line:** a single global minor exists ONLY when `θ = 1` (lone top component, e.g. `(3,3,3)r1`,
  `(2,2,3)r1`). For `θ ≥ 2` it is genuinely per-component. `r` saturating to a complete intersection
  (`Q = d_N·d_0`, e.g. `(2,2,2)r1`) does NOT rescue globality.

## Cheapest discriminating next checks (to harden the general conjecture)
1. `(3,3,3)r1` (θ=1) — confirm a single global minor there, pinning the `θ=1` boundary exactly.
2. `(3,2,3)r1` (θ≥2, δ>0) — test the endpoint/shifted-block interaction in the `δ + C_sh` split beyond
   `(3,3,3)r2`.

## Artifacts
`threads/13-smoothness-S1/scripts/{fibjac,minor_singular,minor_global,rank_points,r0_rank,structure}.py`,
`threads/13-smoothness-S1/codex/jacobian-{prompt,answer}.md`.

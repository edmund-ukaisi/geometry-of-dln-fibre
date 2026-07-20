# geometry-of-dln-fibre

Digesting and formalising in Lean the paper *"Geometry of the fibers of the multiplication map of deep
linear neural networks"* (Simon Pepin Lehalleur & Richárd Rimányi, 2024 — arXiv:2411.19920; local copy
in `paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/`).

Three goals:
1. **Understand** the paper, its method, and its results.
2. **Formalise** almost all of its results in Lean 4 + Mathlib.
3. Do so as a **good, reusable Lean library** with clean API design.

The research *process* is a domain-agnostic harness ported from the `ai-research-assistant` programme —
disposition + discipline in [`CLAUDE.md`](CLAUDE.md), and a repeatable instantiation recipe in
[`TEMPLATE.md`](TEMPLATE.md).

## What the paper says

It studies the algebraic set of tuples of composable matrices $A_\ast=(A_1,\dots,A_N)$ that multiply to a
fixed matrix $B$. Reinterpreting a tuple as a representation of the equioriented **type-A quiver** turns the
geometry into finite orbit combinatorics (Gabriel ⟹ orbits ↔ **Kostant partitions** ↔ **rank patterns**).
From this it determines the codimension $C$ and the number $\theta$ of top-dimensional irreducible components
of the fibre — in three forms (a Poincaré series in equivariant cohomology, a quadratic integer program, an
explicit formula) — proves the surprising **permutation invariance** of $(C,\theta)$ in the dimension vector,
and concludes that the real log-canonical threshold of the square-Frobenius loss is $C/2$, so deep linear
networks are "mildly singular." A full map is in
[`docs/expositions/paper-digest/high-level-overview.md`](docs/expositions/paper-digest/high-level-overview.md).

## Formalisation status

Verified against the Lean **source** (theorem signatures, not docstrings) on `dev` — the algebraic
headline results (@ `f5c1c6b7`, Phase 1) plus the **RLCT foundation** merged via PR #23 (`0863fccf`),
which is what the `rlct` and fibre-`θ` rows reflect (the payoff now reads the **defined** `rlctGlobal`,
and the fibre component-count drops `Monotone d`). Integrity: **zero `sorry` / `admit`** in
`lean/DLNFibre/**`; the only axioms are the
cordon-accounted `@[cited]` monuments (`scripts/cited`: `CITED=3` — Watanabe-upper, Aoyagi-lower, and the
local ζ-continuation). Legend: ✅ Proved · 🟡 Proved (scoped beyond the paper) · 🔵 Cited (an explicit
interface/hypothesis, not a global axiom).

| Paper result | | Generality vs paper | Lean name |
|---|:--:|---|---|
| `codim Σ̄ʳ = C` (geometric) | ✅ | arbitrary `d`; char-0 + infinite field (incl. ℝ) | `codimRepCanonical_productRankLocusLE_eq_cCodim` |
| `codim mult⁻¹(B) = C + δ` (geometric) | ✅ | arbitrary `d`; `B.rank = r` | `codimRepCanonical_fibre_eq_cCodim_add_shift` |
| `C` = QIP min, `θ` = #minimisers | ✅ | monotone → arbitrary `d,r` | `cCodim_eq_qipMin`, `qipNumMinimisers_eq_cTheta` |
| Explicit closed form for `C`, `θ` | ✅ ᵃ | arbitrary `d,r` | `qipMin_eq_cValue`, `cTheta` |
| Poincaré series + `P_d = Σ qᶜᵒᵈⁱᵐ P_m` | ✅ | general `N` | `thm55`, `fivegon` |
| `θ` combinatorial (`= C(m, \|δ\|)`) | ✅ | arbitrary `d` | `cTheta`, `numTop` |
| `θ` = #top-dim irreducible components | ✅ | arbitrary `d` (rank locus + fibre) | `numTop_eq_ncard_topComponents`, `ncard_topDimMinPrimes_fibre_eq_cTheta_dminus_sort` |
| Permutation invariance of `(C,θ)` (Cor 5.10) | ✅ | arbitrary `σ`, `d` | `cCodim_comp_perm`, `numTop_comp_perm` |
| `rlct(Kᴰᴸᴺ_B) = ½·codim mult⁻¹(B)` | 🔵 / ✅ ᶜ | on the **defined** `rlctGlobal` (Def 8.1(i)); opaque map retired | `rlct_lossDLN_eq_half_codimFibre_of_transfer` |

*ᵃ* proved *equal to* the codimension, and the `θ` binomial matches verbatim, but the exact
fractional-part `{S̃/m}` syntactic shape of the paper's formula is not reproduced. &nbsp;
*ᶜ* the RLCT is now the **defined, cite-free** `rlctGlobal` (paper Def 8.1(i)) — the opaque assumed `rlct`
map is **retired** (expedition `rlct-foundation`). Everything but the two analytic bounds is Proved (including
the paper's own algebraic step, Aoyagi's `λ = ½·codim`); the payoff's only value-path cites are those two
bounds (Watanabe-upper + Aoyagi-lower). The `r=0` headline's `#print axioms` = std-3 + those two cites only.

**Proof-route notes** — how the Lean relates to L&R's methods (same statements, sometimes different means):

- **Poincaré series:** L&R prove it via equivariant cohomology (the projective–injective longest-root
  fact); the Lean proof is **purely combinatorial** — Durfee-square + q-orthogonality + PEEL induction.
- **QIP:** `cCodim` / `numTop` are *defined* as the min / #minimisers of the Cor-3.5 quadratic form over
  Kostant partitions; equality to the paper's quadratic integer program is a **theorem** (`le_antisymm`,
  hard direction = the horizontal-lace minimiser), not a definitional restatement.
- **codim = C:** rests on the **Voigt discharge** (`Core.VoigtDischarge`: geometric codim of an orbit
  closure = expected codim `dim Ext¹`), proved unconditionally in char 0.
- **θ = #components:** the combinatorial count and the geometric top-dim-component count of the *actual*
  rank-locus ideal are reconciled by a proven **catenarity bridge**.
- **rlct:** the RLCT is a **defined** invariant `rlctGlobal K = sSup{c≥0 : ∀x, K^{-c} loc-integrable}`
  (Def 8.1(i), cite-free) — the opaque assumed map is retired. The paper's own new algebraic step (Aoyagi's
  `λ = ½·codim`) is **Proved**; only the two analytic bounds are Cited — labelled `_via_aoyagi` / `cited_*`.

*Open edges and generalization routes (field generality) are tracked in
[`ROADMAP.md`](ROADMAP.md). Re-verify this table against the Lean source — not docstrings — when updating.*

## Layout

```
CLAUDE.md            disposition + working discipline (auto-loaded by Claude)
AGENTS.md            codex entry point + reader-facing exposition workflow
ROADMAP.md           result-map + the Core/DLN formalisation-target ladder
TEMPLATE.md          how to instantiate this harness for a new paper
docs/policies/       how research is done (expedition · claims · review · precision · bedrock · …) + exposition-format trio
docs/expositions/    curated reader-facing digest (paper-digest/)
.claude/skills/      lean-formalisation, local-codex-consult
.claude/agents/      scout, pen-and-paper, lean-formaliser, reviewer
.agent-team/         roles/ (tracked), logs/ (tracked), comms/ (scratch)
lean/                Lean 4 + Mathlib project — lib DLNFibre: Core (engine) + DLN (application); build from here
theory/              markdown theory workspace; setup.md = the Rep_d / mult / quiver substrate
expeditions/         one dir per expedition (brief, priorities, threads, synthesis, lessons)
paper-sources/       the paper + reference papers (Aoyagi)
```

## What it does

Research runs as **expeditions** ([`docs/policies/expedition.md`](docs/policies/expedition.md)): a controller
(team lead) delegates to thread teammates around a central question. Theory develops in markdown; a stable
claim is formalised in Lean and gated on an AUDIT that the Lean statement matches the claim; the result is a
statement card linking claim ↔ Lean. Reader-facing digests live under `docs/expositions/`.

The Lean library is factored **engine vs application**: `DLNFibre.Core.*` is the network-free quiver/orbit/
codimension engine (reusable on its own), and `DLNFibre.DLN.*` is the DLN fibre + loss + RLCT application
that depends on it. `Core` must never import `DLN`.

## Launch an expedition

1. Read the expedition's `brief.md` (central question) and `priorities.md`.
2. As controller (this session), enable Agent Teams and create the team
   (`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`; cwd = this repo root).
3. Spawn thread teammates (explore / formalisation / infra) per the brief; spawn reviewers to audit.
4. Run the controller tick each turn: recover → ingest → re-anchor → triage → delegate → integrate → surface → review-to-equilibrium.
5. Close: final integration, synthesis pass, commit on the expedition branch, then open the close PR (≤ 1
   per expedition, controller-authorized per [`CLAUDE.md`](CLAUDE.md) § Branch discipline); merging is
   operator-gated.

## Lean

```
cd lean
source ~/.elan/env
lake exe cache get   # first time on a machine — fetches Mathlib oleans
lake build           # or: lake build DLNFibre.<Module>
scripts/sorries      # audit: expect zero
```

First expedition:
[`expeditions/2026-06-12-core-quiver-engine/`](expeditions/2026-06-12-core-quiver-engine/) — build the
network-free `DLNFibre.Core` spine: the ambient objects + the orbit ↔ Kostant ↔ rank-pattern correspondence
(§§2–3), opening with a Mathlib-coverage recon.

# Brief — Aoyagi-Full: the deep-linear-network learning coefficient, from bedrock

- **Branch:** `expedition/aoyagi-full` (off `dev`). Controller in the **main checkout** (never a worktree).
- **Module namespace:** `DLNFibre.DLN.RLCT.*` (fresh; decorrelated from the old `DLN/Aoyagi/`).
- **Started:** 2026-06-20. **Controller:** lead session (holds executive function + vision).

## The central question (the quest)

Formalise, in honest Lean 4 + Mathlib, **Aoyagi's exact learning coefficient** for deep linear
networks: the real log-canonical threshold (RLCT) λ — and, as a second deliverable, its order θ — of
the square-Frobenius loss of an L-layer linear network, proven **equal to Aoyagi's closed form**
(Aoyagi 2023, Theorem 2). The headline:

> For composable real matrix tuples with true product of rank `r`, the **global** learning coefficient
> (the infimum of the local RLCT over the optimal set / fibre) equals `aoyagiλ d r`.

**Hero-task standard — one citation only.** The *single* permitted external citation is the analytic
extraction step: *given a normal-crossing form, the RLCT is `min_j (h_j+1)/(2k_j)`* (Hironaka /
Watanabe). **Everything else is proven from scratch**, including:
- the real **resolution of singularities** itself (Aoyagi's recursive blow-up, Cases 1 & 2, as actual
  coordinate-chart geometry — pullback monomial×unit, Jacobian monomial, charts cover);
- the reduction to the **deepest singular point** (Theorem 4, which lives in the *second* paper,
  Aoyagi 2013 *Entropy* 15:3714, ref [22] — now in `paper-sources/`);
- **Lemma 1** (RLCT depends only on the ideal), Lemma 2 (block elimination), Theorem 3 (product
  reduction), Lemmas 3–5 (the arithmetic minimisation + order count).

**Independence.** Built from scratch. The prior `expedition/aoyagi-rlct` work is **assumed bad** —
reference-only, never imported. We may *look* at it to dodge known traps and (only after independent
re-derivation) mine a genuinely-good elementary lemma; we never trust or build on it. This expedition
is also **independent of Lehalleur–Rimányi** — no quiver, no `Core`-engine codimension, no `C/2`
bridge. Aoyagi's route is direct linear algebra + resolution; it does not go through `DLNFibre.Core`.

## What we already know (the trusted spine — our own verified results)

From the diagnostic rounds preceding this expedition (exact-arithmetic, decorrelated):
- **Clean closed form.** `2λ_core = ½(Σ_{i=1}^ℓ qᵢ² − Σ_{k=1}^{ℓ+1} mₖ²)`, where `m₁≤…≤m_{ℓ+1}` are
  the `ℓ+1` smallest reduced widths (Aoyagi Def 3) and `q` is the balanced ℓ-part split of `P=Σmₖ`.
  This is far more formalisable than Aoyagi's printed Theorem-2 expression and is our internal target;
  prove the printed expression equal to it.
- **Case-2 non-binding lemma (proven, swept, Codex-checked).** `2λ ≤ M^{(i)}M^{(j)}` for all `i<j`;
  every Case-2 exponent vector evaluates to such a two-width product, so it never strictly binds the
  minimum. (This is why the old expedition's whole "printed-vs-corrected Case-2" thread is irrelevant
  to λ — and why we do NOT reproduce it.)
- **Ground-truth λ, θ** for dozens of small cases (direct resolution / factorisation), e.g. L2 (2,2,2):
  λ=3/2,θ=1; (2,1,2): λ=1,θ=2; L3 (2,2,2,2): λ=3/2,θ=3. Use these to cross-check the Lean definitions.
- **Known trap:** Aoyagi's Definition 3 set-selection appears ill-defined on some *unbalanced* width
  vectors (a finder returned no set, e.g. `[4,2,1,3]`). Resolve by defining `aoyagiλ` via the
  always-well-defined minimisation and proving it equals the printed form where Def 3 applies.

## The goal theorem (skeleton — write this FIRST, then fill)

Definitions to pin (the foundational, highest-care work — Rung 0):
- `Params d` — composable real matrix tuples; `prod` the product; `dlnLoss B := ‖prod · − B‖²_F`.
- `optimalSet d B := { A | prod A = B }` (the fibre).
- `rlctAt : (Params d → ℝ) → Params d → ℝ≥0∞` — Aoyagi Def 1: `sup{ c | ∫_U |F|^{-c} φ < ∞ }`,
  φ a bump with `φ(w*)>0` (φ-independence is part of the theory). `rlctOrderAt` = order of the
  largest pole (θ; secondary, analytically harder).
- `aoyagiλ d r : ℚ` — **defined via the minimisation** (total, robust), with the printed Theorem-2
  expression proven equal where Def 3 applies.

Headline:
```
theorem aoyagi_learning_coefficient
    (d : Fin (L+1) → ℕ) (r : ℕ) (B : Matrix _ _ ℝ) (hB : B.rank = r) :
    (⨅ w ∈ optimalSet d B, rlctAt (dlnLoss d B) w) = (aoyagiλ d r : ℝ)
```

## The dependency ladder (Proved unless marked CITED)

| Rung | Content | Status |
|---|---|---|
| **S0** | Define `rlctAt`, `rlctOrderAt`, `dlnLoss`, `aoyagiλ` (+ measure substrate) | Proved (build) |
| **S1** | Lemma 1 — RLCT depends only on the ideal; monotonicity | Proved |
| **S2** | normal-crossing → RLCT extraction (chart-level monomial formula) | **CITED (the only axiom)** |
| **L1** | Lemma 2 — block Gaussian elimination / Schur | Proved |
| **L2** | Theorem 3 — product reduction (regular-block split + RLCT additivity) | Proved |
| **D1** | Theorem 4 — reduction to the deepest singular point (Aoyagi 2013 [22]) | Proved |
| **R1** | The resolution: Cases 1 & 2 as explicit coordinate charts → normal-crossing form | Proved (**the mountain**) |
| **A1** | Lemma 3 + the clean closed form; the minimisation | Proved |
| **A2** | Lemmas 4–5 — order θ count | Proved (θ secondary) |
| **T** | Theorem 2 — assemble `aoyagi_learning_coefficient` | Proved (the GOAL) |

Tractable: S0(defs)/L1/L2/A1/A2. Hard/novel: S0(rlct def)/S1/D1/**R1**. The cited line is drawn at S2
and nowhere else.

## Scope

- **IN:** Aoyagi 2023 (`aoyagi-2023-neural-networks-preprint.pdf`) — the whole λ/θ derivation; and
  Aoyagi 2013 (`entropy-15-03714.pdf`) — Theorem 4 only (deepest singular point), to the extent D1 needs.
- **OUT:** the 2025 ReLU papers (`paper-sources/aoyagi-relu/`); Lehalleur–Rimányi (quiver, `Core`, C/2);
  the old `expedition/aoyagi-rlct` Lean (reference-only, assumed bad).

## Standing decisions (controller's autonomous calls — no operator block needed)

1. **Model blow-ups as explicit coordinate charts** (polynomial changes of variable; prove
   pullback/Jacobian/coverage by direct computation), not general AG blow-up machinery. Follow Aoyagi
   very closely — his proof is constructive in explicit local coordinates.
2. **The S2 citation is the chart-level monomial formula** (cover + change-of-variables validity stay
   on our side; only the irreducible monomial-integral fact is cited).
3. **`aoyagiλ` defined via the minimisation**; printed Theorem-2 form proven equal (resolves the Def-3
   well-definedness trap).
4. **Validate-small-first:** close the whole ladder end-to-end on the smallest nontrivial case (single
   matrix, then L=2 reduced-rank, r=0) **before** generalising. Top-to-bottom on one case is the gate.
5. **Build what Mathlib lacks** (RLCT, monomial integrals, resolution substrate) — no anchoring on
   Mathlib, no operator call needed.
6. **θ is the second deliverable.** Drive λ to full completion first; carry θ as far as it goes cleanly;
   if its *analytic* definition (pole multiplicity) proves disproportionate, land the combinatorial
   `θ=a(ℓ−a)+1` fully and flag the analytic-multiplicity seam as the at-risk item — named, not hidden.
7. **Wall-handling (never halt, never hide):** on a genuine wall, exhaust routes; if still stuck,
   isolate the **minimal, precisely-stated** lemma as a clearly-named gap, build everything else
   conditionally on it, keep attacking it, and report it honestly. The target stays one-citation-only;
   any extra gap is a flagged exception, not a silent defer or a redefinition of "done".
8. **Branch/push:** push `expedition/aoyagi-full` freely to `origin` (pre-authorized). PRs / `dev`
   merge / `dev→master` promotion remain operator-gated (signal-and-wait).

## Anti-treadmill contract (the prior expedition's failure mode — do not repeat)

The old expedition diverged: 55% of recent commits and +8.7K lines went into reconciling a printed
Case-2 typo that does not affect λ, with **no stated target theorem** so accretion had no stop
condition, and the **Cited line drawn in an awkward middle** (extraction cited, resolution geometry
stranded as un-built bookkeeping). Guardrails:
- **The goal skeleton (every statement, named `sorry`s, the one cited axiom explicit) IS the contract.**
  Write it before any proof. Every work unit **closes a named `sorry` in the skeleton** — never adds
  free-floating scaffolding (wrappers/boundaries/bridges). The **sorry-count must trend down.**
- **Cite the resolution's *extraction*, prove its *construction*.** Do not reproduce the abstract
  exponent-bookkeeping; build the real charts (R1) that feed the S2 citation.
- **Periodic goal-distance check** (controller tick): is every live file on the critical path to a
  named `sorry`? If a file is not, it is scaffolding — stop and re-aim.

## Build discipline (runtime mitigation)

- **Mathlib cache always** (`lake exe cache get`); shared `.lake/packages` across worktrees → isolation
  is cheap. Never rebuild Mathlib.
- **Many small modules, not few big ones.** A stable `DLNFibre/DLN/RLCT/Foundations/*` layer (defs,
  Lemma 1, the cited interface, measure substrate) built once; heavy `MeasureTheory` imports isolated
  there. (The old 13.7K-line single file is the anti-pattern: any edit → full recompile.)
- Iterate with `lake build <one module>`; full `lake build DLNFibre` only at integration; **long builds
  run in the background** (never block a turn or serialize the team behind the controller's green-gate).
- **Tactic hygiene:** no `decide`/`norm_num`/`simp`-bombs on large terms; cap `maxHeartbeats`; structured
  proofs for heavy arithmetic; the clean closed form keeps terms small on purpose. `decide +kernel`,
  never `native_decide`. (See `lean/CLAUDE.md`.)
- Track sorry-count + per-module build time each tick.

## Closing criterion

`aoyagi_learning_coefficient` proven on the expedition branch with **only the S2 citation** (zero other
`sorry`/`axiom`/`native_decide`, `scripts/sorries` clean, `#print axioms` shows only the named S2
interface); the **smallest case validated end-to-end**; the **foundational definitions
(`rlctAt`/`rlctOrderAt`/`aoyagiλ`) independently reviewed for fidelity** against the numerical ground
truth; a final **bedrock + precision pass and a decorrelated hardener audit**; and a human-facing
exposition written. θ landed to whatever depth it cleanly reaches, with any seam named. Then
signal-and-wait for the close-phase PR (operator-gated).

## Pointers

- Disposition + discipline: `CLAUDE.md`. Full contract: `docs/policies/expedition.md`.
- Lean conventions/build: `lean/CLAUDE.md`. Precision/bedrock: `docs/policies/{precision,bedrock,review}.md`.
- Loop wrapper: `loop-prompt.md`. Recovery substrate: `priorities.md` · `synthesis.md` · `threads.md` · `lessons.md`.
- Papers: `paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/{aoyagi-2023-neural-networks-preprint.pdf, entropy-15-03714.pdf}`.

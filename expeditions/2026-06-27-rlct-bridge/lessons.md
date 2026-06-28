# Lessons — `rlct-bridge` (append-only)

Carried forward from `fibration-geometry` (cross-expedition wisdom), plus RLCT-specific notes.

## L0 — Disposition (operator standing directive)

Run as a large rising-sea hero arc. **Hold the vision, let the sea rise inexorably.** "No Mathlib
support is not a blocker" — build the missing geometric scaffolding; the analytic RLCT core is the honest
**cited** seam, not a wall. Be *more* ambitious than the teammates; targets at the edge of reach; drop
scope only for a genuine blocker. The controller is an **adaptive feedback controller**: keep the quest
fixed, re-route the rungs to what lands. Recon sharpens the target; it does not earn a veto. **Just Do
It** when within reach; roadmap a bare unargued extension; surface to move the boundary.

## L2 — Tide hygiene + cross-base integration

Tides commit + green-gate BEFORE reporting "ready". Cross-base: isolation worktrees branch from
`origin/dev` (LACKS the controller's just-landed commits) — a dependent tide's first step is
`git merge expedition/rlct-bridge --no-edit`. Controller integrates uniformly via worktree-disk copy +
wires the aggregator (single-writer) + full `scripts/lb DLNFibre` green-gate before committing. Keep
statement-card SHA anchors at landed PR commits.

## L3 — A framing/naming error recurs; fix by grep of the SEMANTIC CLASS, whole-file, not the flagged line

fibration-geometry cost **five** owner review rounds — every one was prose/docstring name=content (the
math/Lean was bedrock throughout), and they recurred because I fixed flagged lines + a literal-phrase
grep while the same frame survived elsewhere. The four failure modes to grep against, each pass:
(1) **same file, other sections** (forward-pointer vs main blocker; card Proved/Deferred vs
title/intro/Claim; def docstring vs module header); (2) **semantic class, not literal string** (the same
frame in many wordings); (3) **non-repo artefacts** (the PR *description* — re-read after every framing
fix); (4) **stale cross-refs after a rename** (grep the old name repo-wide). Re-grep clean + read the
changed files' full prose before declaring a sweep done.

## L4 — RLCT name=content (this expedition's existential trap)

The recurring trap here: an `rlct_…`-named result that secretly *assumes* the analytic interface it
should expose, or names a *geometric* (codim/lci/mildness) fact as if it were the *analytic* rlct
conclusion. The cited boundary is the thin `RlctInterface` (rlct-of-a-quadratic; Watanabe `≤`; the
resolution `≥` criterion) — stated explicitly, every DLN result attached to it as an INPUT, not folded
into an apparent analytic proof. The wall is the LOWER bound (singular-stratum mildness); the upper-bound
slab must not be named as the equality.

## L5 — Blindness as decorrelation (operator decision, 2026-06-28)

Recon found a large ACTIVE parallel formalisation of **Aoyagi's paper** (`origin/expedition/aoyagi-full`,
183 RLCT files, genuine `rlctAt`, the `aoyagi_learning_coefficient` headline) — NOT on dev, doing the same
`rlct=½·codim` math this L&R line targets. **Operator chose to keep the L&R/rlct-bridge line BLIND to it**
(no import/copy/dependency). Rationale: two independent formalisations of the same fact CROSS-CHECK on later
reconciliation; entangling them imports the other line's in-progress sorries/churn and destroys the
decorrelation; and citing the analytic rlct is fidelity to L&R (who themselves cite Aoyagi). **Lesson:**
when a parallel effort overlaps, "blind + cite" can be *more* valuable than "connect" — surface the
discovery + the reconciliation options to the operator (it's a boundary/charter call), don't auto-fold.
The two meet only at a field-free combinatorial identity (`aoyagiLambda ↔ Aoyagi.lambda`), reconcilable
later. **Controller failure caught:** my first instinct was to copy/connect; the operator's "keep it blind"
+ "do a lot more geometry up to the interface" corrected an over-narrow read on my part (twice).

## L6 — `codim_ℝ := codimRepCanonical (k:=ℝ)` is the honest real-locus codim

The banked field-parametric `codimRepCanonical`, EVALUATED at ℝ, already IS the real-locus codim
(`Ideal.height (vanishingIdeal ℝ (real points))`). The x²+y² discriminator pins it: real locus `{0}` has
`vanishingIdeal ℝ = (x,y)` height 2 = the real codim, NOT the principal-generator height 1. **The trap to
avoid is not the DEFINITION but the ASSUMPTION** `codim_ℝ = codim_K` (the real↔complex transfer T) — that
is the genuinely-cited content, false in general (real locus can be lower-dim), true for the DLN fibre via
`realizerD` density. Don't reuse `codimRepCanonical(ℝ)` *as if it equalled* `codim_K`; do use it as the
*definition* of real codim.

## L7 — Formal inhabitability ≠ inhabitability by the INTENDED object (the re-guard lesson)

The two decorrelated reviewers did NOT contradict — they tested different bars. Fidelity PROVED the
interface formally inhabitable (a constructed `rlct = ½codim on-image, 0 off-image` satisfies the fields).
The hardener showed the *intended analytic* `rlctAt` (∞ off `image(mult)`) CANNOT satisfy the UNGUARDED
`∀ B` upper bound (off-image `codim_ℝ = ⊤`, `(⊤).toNat = 0` ⟹ forces `rlct ≤ 0`) — so the unguarded
interface was dischargeable only by a *fake*, blocking the future fold with the real `rlctAt`. **Fix:
re-guard with attainability** (`B.rank=r → ∀k', r≤d k'` ⟺ fibre nonempty), the monolith's original shape.
**Lesson:** non-vacuity §2.1's "in-file witness" is necessary but not sufficient — also check the
*intended* object can inhabit it; a `∀ B` quantifier with a `.toNat`-of-⊤ collapse off the meaningful
domain is a subtle-wrong a green build + a formal witness both miss. The decorrelated fidelity-vs-taste
split is what caught it. **Controller failure caught:** I approved the "unconditional upper bound" — the
hardener's catch was mine to own.

## L3 recurrence (again) — re-grep the class to EMPTY, not just the flagged lines

The cross-file "projection compatibility — open" framing (stale after R5 closed it) lived in FIVE sites
(`FibreBundleHeadline.lean:57-62,:101,:138,:196` + `FibreFlatness.lean:54`); the fidelity reviewer flagged
ONE (the one it had evidence for, correctly noting it as a class). My first sweep fixed 4 and MISSED `:138`
— caught only by re-grepping the semantic class to empty. **The re-grep-clean step is non-negotiable;** a
reviewer flagging one instance of a class means sweep the whole class + re-grep to zero.

## L8 — Relaxing a typeclass leaves stale DOCSTRINGS (a tide deliverable must sweep its own docstrings)

The L7+L8 tide relaxed `[IsAlgClosed]→[CharZero]/[Infinite]` on ~16 codim decls but left their docstrings
saying `[IsAlgClosed]`/"algebraically closed" — the owner's PR review caught it (name=content: the public
docstring over-stated the hypotheses the decl actually needs). **Lesson:** a typeclass relaxation is not
done when the build is green — the docstrings + module headers must be swept to match the new signatures,
**per-decl** (some decls in the same file genuinely KEEP the strong hypothesis — do NOT blanket-relax; read
each signature). Mandate this in relaxation-tide briefs. (Also: status/index docs — `brief`/`loop-prompt`/
`priorities`/cards — read as LIVE; a phase-close must update ALL of them, not just `synthesis`/`threads`.)

## L9 — Build-reaper under load: foreground green-gates, `.lake` persists across kills

Under high box load (other sessions), DETACHED/background `scripts/lb` builds were repeatedly REAPED
(status `killed`, not OOM — 21 GiB free). The fix that worked: **foreground `scripts/lb` with the long
timeout**, and `.lake` olean progress PERSISTS across kills, so a killed build resumes on re-run (each run
converges). Tides + controller green-gate in the foreground; re-run on kill; never trust a single-module
green (the stale-olean trap masks relaxation gaps — full-aggregator gate every wave).

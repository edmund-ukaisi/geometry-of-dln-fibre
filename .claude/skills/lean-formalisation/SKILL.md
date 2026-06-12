---
name: lean-formalisation
description: Workflow for Lean 4 + Mathlib formalisation in the DLNFibre harness. Use when proving a claim in Lean, running a formalisation (tide) thread, managing proof skeletons, or auditing sorries. Forked and trimmed from the SRI/aks lean-formalisation skill.
---

# Lean formalisation

This skill drives a **formalisation thread** (a tide) inside an expedition: take a
stable claim, state it in Lean, prove it, and gate it on an AUDIT that the Lean
statement matches the informal claim. See `docs/policies/expedition.md` for how
threads fit the expedition, and `lean/CLAUDE.md` for build commands and Mathlib
gotchas.

## Why we formalise

Close the verification loop on the routine claims that bottleneck a human
researcher's time: state the claim in Lean, present the Lean theorem statement
alongside the markdown claim, and let a reviewer confirm the statement says what
the proof proves. Bias
toward small targets tied to a specific claim, not general-purpose libraries.

## The tide unit

A formalisation thread proves one **minimal candidate**: a single statement,
closed-form where possible, reachable from what is already in `lean/`, and
numerically checkable beforehand. Reject programmes ("formalise the fiber
section") — decompose to one reachable statement.

1. **SPECIFY.** Write the theorem statement with the hypotheses you think you
   need; body `sorry`. Deliberate the candidate and its hypotheses with Codex
   (`local-codex-consult`) when the shape is non-obvious. Numerically sanity-check
   the claim (sympy/numpy) at concrete values before proving.
2. **PROVE.** `lake build` to validate the *signature* first. Then fill sorries
   one at a time, rebuilding after each. Skeleton correctness outranks filling: a
   `sorry` under a correct statement is a building block; a `sorry` under a wrong
   statement misleads.
3. **AUDIT** (no-skip gate). `scripts/sorries` reports zero. Write the statement card
   (`docs/policies/statement-cards.md`) at status `sorry-free`; a reviewer
   (`docs/policies/review.md`) then checks **fidelity** — the Lean statement and its
   hypotheses match the informal claim — and on confirmation the card moves to
   `reviewed`. Fidelity findings are report-only: escalate, do not silently rewrite the
   mathematics.
4. **Retrospective.** Record statement, strategy, consults, roadblocks, and a link to
   the statement card.

## Discipline (aks-style)

- **Zero `sorry` / `axiom` / `native_decide` / `#exit` in committed files.** Audit
  with `scripts/sorries` before every commit.
- **Verify against the primary source.** The markdown claim (and the paper it
  cites) is ground truth until Lean exposes a mismatch. Re-read the relevant
  section before committing to a proof structure.
- **Estimate before attacking a sorry.** Probability of a direct proof; if below
  ~50%, factor into intermediate lemmas first.
- **Recognise thrashing.** After 3 failed approaches to one goal, stop. Oscillating
  approaches and a growing helper count without progress mean the goal is in the
  wrong tactical class — consult Codex (`docs/policies/codex-consultation.md`).
- **The hypothesis is part of the theorem.** A theorem with the wrong hypothesis
  is not almost done. State a suspect hypothesis as a known unknown and resolve it
  before proving.

## Patterns and pitfalls

- **Build the minimum for the target.** Do a gap analysis against the claim first.
  Factor a piece up to a shared library only on a *second* use, not in
  anticipation of one.
- **Specialise.** Prove the four cases needed; skip the generic-`n` framework the
  project never instantiates.
- **`Real.rpow` interacts badly** with `nlinarith` and the `Real.sqrt` idioms;
  prefer `Real.sqrt` + integer `npow` when the exponent is a known integer.
- **"Easy to see" in a paper is a red flag.** Write the full calculation by hand
  (or with Codex) before formalising — formalisation needs every term named.
- **Pre-stage API with `example` blocks** that pin each library lemma's name and
  type; build, then prove. Keep the blocks as durable contracts.
- **Avoid `native_decide`** (trusts the compiler); use `decide +kernel`.

## No wall-clock estimates

Do not quote hours or days — the estimates undershoot by 4–10× because Lean idiom
friction dominates. Quote **line counts** and **sub-task lists** instead. If asked
"how long", decline and give a line-count/sub-task estimate.

## Consulting Codex

Codex is the independent second model. Consult before heavy infrastructure, on a
3+ step plan before step 1, on thrashing, on a suspect statement, and after a
target reaches sorry-free (review). Triggers and the invocation live in
`docs/policies/codex-consultation.md`; run one via the `local-codex-consult`
skill. The diagnosis is what you buy; never paste Codex code without building it
locally.

## Claim tagging

Link a formalised claim to its Lean theorem with a markdown statement card (claim,
Lean signature, English gloss, hypotheses, pinned commit SHA) per
`docs/policies/statement-cards.md`. We do not use LaTeX `\leanref` — the paper is a
separate write-up downstream.

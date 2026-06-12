# Codex consultation policy

When and how to consult Codex (the OpenAI CLI) as a second opinion,
red-team, or advice-loop partner during research work.

This policy generalises the Codex pattern from the
`lean-formalisation` skill (which was Lean-specific) to cover any
expedition thread, claim stress-test, or stuck-debugging moment.

## When to consult

Trigger a Codex consultation when **any** of these hits:

- **Heavy commitment**: about to commit to a substantial formalisation
  target, infrastructure, or a multi-stage plan. A short Codex red-team
  often catches a wrong approach before the effort is spent.
- **Stuck for >30 min** on a single problem (failed approaches piling
  up, oscillating between two solutions, increasingly contorted
  workarounds). The unblock that eventually works is usually the
  consult itself.
- **A claim feels wrong**: counterexample appearing, hypothesis fits
  data too well, or the conclusion contradicts a strong prior. Ask
  Codex to stress-test before going further.
- **Bookkeeping accumulation**: 50+ lines of mechanical work
  (manipulation, refactoring, ad-hoc helpers) without new content.
  Codex may have a shorter idiom.
- **Multi-stage plan**: 3+ planned steps. Consult on the whole plan
  before starting step 1 — later steps often reshape earlier work.

Empirically a productive multi-hour session has **0–3 consultations**.
Zero consultations on a substantive piece of work is itself a
trigger: ask "what would I most benefit from sanity-checking?" and
send a query.

## Don't consult for

- Trivia retrievable by `grep` / `Read`.
- Routine refactors with an obvious safe shape.
- Decisions the user has already made (use the user's call; don't
  ask Codex to second-guess them).
- Repeated similar queries — if the first didn't help, the second
  rarely does. Diagnose why the first missed before re-asking.

## Authentication

Codex needs to be authenticated against an OpenAI-compatible provider
(typically `openai-aisi` for AISI users). Check with:

```sh
codex doctor 2>&1 | head -20
```

If unauthenticated, the user must run `codex login` interactively:
the agent can't do this. Surface the auth gap to the user directly and
skip Codex consultation until resolved.

The `/codex:setup` slash command (from the codex plugin) walks
through this.

## The consultation command

**Updated** for codex-cli 0.133.0 (as of 2026-05). The
`lean-formalisation` skill's example uses `--ask-for-approval` which
no longer exists.

Current pattern:

```sh
PROMPT_FILE=path/to/prompt.md
ANSWER_FILE=path/to/answer.md

codex exec \
  --sandbox read-only \
  --skip-git-repo-check \
  -c 'model_reasoning_effort="xhigh"' \
  --output-last-message "$ANSWER_FILE" \
  - < "$PROMPT_FILE"
```

The actionable, invocable form of this policy is the
[`local-codex-consult`](../../.claude/skills/local-codex-consult/SKILL.md)
skill — reach for it inside an expedition.

Flag rationale:
- `--sandbox read-only` — Codex shouldn't edit your repo from a
  consultation; promotion of any suggested code is your job after
  reviewing.
- `--skip-git-repo-check` — lets Codex run anywhere (useful when
  you want to consult on something outside a repo).
- `-c 'model_reasoning_effort="xhigh"'` — Codex consultations are
  high-stakes per call; reasoning effort is the most useful knob, so
  default to the **highest** (`xhigh`). It adds latency (1–3 min) but
  that's the right trade for a deliberate consult. Fall back to `high`
  only if the local `codex` rejects `xhigh`, and flag the downgrade.
- `--output-last-message FILE` — persists the answer to a file. Don't
  rely on stdout alone — long answers are easier to reread from a file,
  and the file is the artefact to keep in the thread's `codex/` dir.
- `-c model_reasoning_effort` is a config override; other configs can
  be added the same way (e.g. `-c approval_policy="never"` if needed).

Default model: leave unset. Codex picks `gpt-5.5` (or current best)
from local config. Override with `-m <model>` only if you have a
specific reason.

For **adversarial review** of code, prefer the dedicated subcommand:
```sh
codex exec review [path] --sandbox read-only
```
which loads a review-specific prompt template.

## Prompt structure

Codex responds well to XML-tagged, contract-shaped prompts. The
`gpt-5-4-prompting` skill inside the codex plugin has the canonical
recipe. Short version:

```xml
<task>
  Concrete job + minimum context Codex needs.
</task>

<output_contract>
  Exact shape of the response you want — sections, ordering, brevity.
</output_contract>

<grounding_rules>
  (For review / research) what Codex should and shouldn't claim
  without evidence.
</grounding_rules>
```

Don't bury the request in prose. Codex isn't trying to figure out
what you want — tell it.

## Persisting consultations

Save the consultation under the consulting thread:

```
expeditions/<id>/threads/<NN>-<slug>/codex/
  <topic>-prompt.md
  <topic>-answer.md
```

The artefact pair (prompt + answer) is more useful than memory:
later sessions re-read both to recover the strategic context.

## Treat Codex output with discipline

- The **diagnosis** is the load-bearing part. The **recipe** (code,
  config, commands Codex suggests) is illustrative — never paste
  Codex code without running it locally first.
- If Codex flags an inference vs an observed fact, preserve that
  distinction when reporting back. Don't promote inferences to
  conclusions.
- Failed Codex runs (auth error, malformed output, timeout) are not
  occasions to substitute Claude's own answer. Surface the failure
  and stop.

## Cost calibration

A Codex consultation typically costs 1–5k tokens depending on prompt
size and reasoning effort. Reasoning-high adds significant latency
(30–120 s) but is usually worth it for the kinds of triggers
above. Treat each consult as a deliberate decision, not a reflex.

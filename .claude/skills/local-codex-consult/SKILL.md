---
name: local-codex-consult
description: Consult the local Codex CLI (gpt-5.x via `codex exec`) as a second-opinion / red-team / design-review partner during research expeditions — distinct from the `codex:*` plugin. Use when about to spend compute on an experimental design, when stuck >30 min, when a claim feels too clean, before folding a finding into an exposition, or when a 3+ step plan wants a sanity pass. Always runs at the highest reasoning effort and the latest/best model.
---

# Local Codex consultation

Invoke the **local `codex` CLI directly** to get an independent, high-effort
second opinion and persist the prompt+answer as an artefact. This is **not**
the `codex:*` plugin — it's the project's own consult pattern, owned here so
expeditions can reach for it.

The *when to consult / when not to* judgement and the discipline for handling
output live in [`docs/policies/codex-consultation.md`](../../../docs/policies/codex-consultation.md).
Read that for the full policy; this skill is the operational "run one now."

## Non-negotiables (project defaults)

- **Highest reasoning effort, always:** `-c model_reasoning_effort="xhigh"`.
  (If the local `codex` rejects `xhigh`, fall back to `high` and flag that the
  level was unavailable — don't silently downgrade.)
- **Latest/best model, always:** leave `-m` **unset** so Codex uses its
  configured default, which tracks the latest/best model. Pin `-m <model>`
  only if you've confirmed the default is stale.
- **Read-only sandbox:** a consultation never edits the repo. Promoting any
  code Codex suggests is the agent's job, *after* running it locally.

## Preconditions

```sh
codex doctor 2>&1 | head -20      # must be authenticated (openai-aisi for AISI)
```

If unauthenticated, the agent **cannot** fix it — surface to the operator
(the `/codex:setup` command walks through `codex login`) and skip the consult.
A failed or auth-broken consult is **never** an occasion to substitute
Claude's own answer for Codex's: surface the failure and stop.

## Run a consultation

1. Write a contract-shaped prompt to a file (see Prompt shape below).
2. Invoke:

```sh
PROMPT=path/to/prompt.md     # in an expedition: threads/<NN>-<slug>/codex/<topic>-prompt.md
ANSWER=path/to/answer.md     #                   threads/<NN>-<slug>/codex/<topic>-answer.md

codex exec \
  --sandbox read-only \
  --skip-git-repo-check \
  -c 'model_reasoning_effort="xhigh"' \
  --output-last-message "$ANSWER" \
  - < "$PROMPT"
```

3. The prompt+answer pair is the artefact — keep both. `xhigh` adds latency
   (often 1–3 min); that's expected and usually worth it.

For **adversarial review of code or a diff** (e.g. vetting an experimental
script or an analysis before trusting its output — exactly the big-loop-4
"didn't check the setup / didn't check the graphs" failure), prefer the
review subcommand, which loads a review-specific template:

```sh
codex exec review [path] --sandbox read-only -c 'model_reasoning_effort="xhigh"'
```

## Prompt shape

Codex responds to explicit, XML-tagged contracts, not prose. Minimum:

```xml
<task>
  The concrete job + the minimum context Codex needs (numbers, file paths,
  what was already tried). Don't make Codex guess what you want.
</task>

<output_contract>
  Exact response shape: sections, ordering, brevity. e.g. "Rank the three
  hypotheses; for each, give the single cheapest discriminating test."
</output_contract>

<grounding_rules>
  For review/research: what Codex may vs may NOT claim without evidence;
  instruct it to flag inference vs observed fact explicitly.
</grounding_rules>
```

(The codex plugin's `gpt-5-4-prompting` skill has a deeper recipe if you want it.)

## Discipline (the load-bearing part)

- The **diagnosis** is what you're buying; the **recipe** (code/config/commands
  Codex emits) is illustrative — never paste it without running it locally first.
- Preserve Codex's inference-vs-fact distinctions when folding the result into
  `thread.md` / `synthesis.md`. Don't promote an inference to a conclusion.
- Treat each consult as a deliberate decision, not a reflex. A productive
  multi-hour session has ~0–3 consults; zero on a substantive piece of work is
  itself a trigger to ask "what would I most benefit from sanity-checking?"

## Inside an expedition

- Persist under the consulting thread: `threads/<NN>-<slug>/codex/<topic>-{prompt,answer}.md`.
- The two highest-value trigger points map onto expedition gates:
  - **experimental `SPECIFYING`** — red-team a design *before* spending cluster
    time (catches the confound the wall-time would otherwise reveal late);
  - **`STEP_BACK`** — an independent skeptic pass on the synthesis-so-far,
    complementing the red-team subagent.

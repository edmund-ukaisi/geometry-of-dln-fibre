# .agent-team/

In-repo coordination surface for the expedition team.

- `roles/` (tracked) — one short file per role: lane, scope, pointer to the agent
  definition and policies. Source of truth for who does what.
- `logs/` (tracked) — distilled, durable per-role findings and decision logs; not
  per-turn diaries.
- `comms/` (gitignored except `.gitkeep`) — scratch briefs and handoffs; acted on,
  then deleted or promoted to `logs/`.

Live coordination uses the Agent Teams mailbox, not files; `comms/` is for content
that must survive a context reset. Roles map to the agent definitions in
[`../.claude/agents/`](../.claude/agents/); the expedition machine is
[`../docs/policies/expedition.md`](../docs/policies/expedition.md).

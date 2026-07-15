# Overhaul follow-ups (deferred with reasons; PR #27 companion)

## A — needed before the new structure runs a real expedition
1. **Agent definitions for the new seats** (`.claude/agents/`): architect, cartographer, navigator,
   elder. Role charters exist; spawnable agent defs do not.
2. **Cordon ↔ map wiring**: `expedition validate` consumes the cordon/leak report (today the leak
   audit lives only in the Lean exe); banked-status in the survey reads `@[blueprint]` tags.

## B — post-merge tooling increments (spec'd, not built)
3. **Metadata history pass + activity clock** (spec: first-parent `git log -p claims.yaml` →
   status transitions, ages, promotion lag, owner churn, time-in-status; activity buckets; 4
   alarm thresholds in STATUS + navigator view). Contracted in the spec so no implementation can
   do it wrong; not implemented.
4. **Full anchor statement-pins** (v0 emits `#check` pins; real `example : <prop> := <name>` pins
   need the prose→Lean translation step).
5. **Route-gate hypothesis matching**: gate check (b) currently runs tag-attached battery scripts;
   automated evaluation of a route's *stated hypotheses* against the battery is a convention, not
   a mechanism.
6. **Cleanup automation second half**: audit exists (read-only, fixed for independent repos);
   the approved-batch remover + branch-deletion preflight remain manual.
7. Lookahead/DAG view polish; consultation telemetry (weak consumer — v2 at best).

## C — at-expedition-close / at-mint
8. **Cordon real-scope run**: tag the Aoyagi RLCT axiom `@[cited]`, allowlist its module, run
   `scripts/cordon` (mid-flight it would honestly red on scaffold sorries).
9. **Retro mint-day sequence** (armed): refresh chain → lb → WalkDecls → graph_readouts →
   cone_delta vs the frozen baseline; then the three retro products (proof-as-built,
   process-retro, library-report).
10. **Worktree cleanup batch** (operator-approved, post-mint; audit list ready; root cause first —
    see PR discussion).

## D — operator decisions pending
11. PR #25 disposition (content absorbed: close-as-superseded, or merge + dedupe).
12. PR #27 review/merge into retro/aoyagi-full; later the retro branch → dev PR.

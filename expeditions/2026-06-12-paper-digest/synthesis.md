# synthesis.md — controller's integrative read (paper-digest)

The controller's *internal* integrative ground: the current read, flushed every tick (the recovery
substrate after compaction). Not a deliverable — the deliverables are the verified digest, the sized
ladder in `ROADMAP.md`, and the Mathlib-coverage map.

## State

_Expedition not yet opened._ Skeleton created at setup. The central question and closing criterion are in
`brief.md`; the opening decision queue is in `priorities.md`.

## Current read

- The paper factors into a network-free **engine** (quiver-orbit geometry + combinatorics computing
  $(C,\theta)$) and a thin **DLN/RLCT application**; this is mirrored by the Lean `Core` / `DLN` split.
- The load-bearing unknown is **Mathlib's quiver-representation coverage** — it sets the build-vs-reuse
  boundary. Resolving it is the first move.

## Drift guard

Keep every claim tagged Proved / Assumed / Cited / Deferred. The `rlct = ½·codim` reading is **Cited**
(Aoyagi / Watanabe) — do not let a digest or a future Lean name assert the RLCT when only the codimension
is established.

# synthesis.md — Aoyagi-Full controller's integrative read

(Internal ledger; assumes repo context. Flushed every tick; read on re-ground. Not a deliverable.)

## Current read (2026-06-20, spine fully de-risked at general L)

Rung 0 design landed + reviewed (bedrock-quality, Codex-faithful). The foundation (see
`threads/01-.../design-spec.md`): `dlnLoss=‖prod·−B‖²_F`; `rlctAt` = Aoyagi Def 1 integral-sup in ℝ≥0∞;
`aoyagiλ = reg + ½·min over the admissible cone Adm of Mval`, TOTAL + Def-3-free; S2 = the one cited
axiom (chart normal-crossing → (λ,θ)); goal skeleton with named sorries.

**Spine SOUND, fully de-risked at general L (thread 03, pp + decorrelated Codex):**
- The set-equality "R1 charts = Adm" is FALSE; the **value-match** holds: `min chart-ratio = ½·min_{T∈Adm} Mval(T) = λ`.
- **`codim S(t) = Mval(t)` PROVEN at general L** (telescoping fibration; hand + numeric differential-rank
  L=3,L=4 + decorrelated Codex). `T` ↔ nested-rank stratum `{rank(C¹···Cʲ)=tⱼ}`. So
  `λ_core = ½·min over strata of codim`. Established pen-and-paper; Lean proof = the A1/R1 obligation.
- **θ pinned:** `θ=a(ℓ−a)+1` always (deepest-point divisor multiplicity, Lemma 4/5); `|argmin Adm|` only
  equals it for L+1≤4 and over-counts for ≥5. θ rides inside S2.
- **R1 obligation + architecture:** value-match via stratum codim; organize the resolution BY nested-rank
  strata (each → a divisor of ratio ½·codim; cover = strata partition of {F=0}), NOT chart enumeration.
  Differential-rank=codim is the transversality input. Codex subtlety: use EXACT strata, not naive
  `{rank ≤ t}` (a union whose codim is a min). design-spec §9.3 amended; thread-03 has the full record.

## Topology note

Controller session is in worktree `rung0-defs`; canonical `expedition/aoyagi-full` in the main checkout;
teammate isolation-worktrees collapse onto rung0-defs ⇒ **serial editing teammates**. Editing in
rung0-defs; controller merges →expedition/aoyagi-full in main + pushes. pp runs read-only (no collision).
For the parallel middle phase, operator may relaunch controller from main (non-blocking; re-ground via docs).

## In flight

- `fm` — Rung 0b encode (shared worktree). Awaiting report.
- `pp` — next: D1 scope (read Aoyagi 2013 `entropy-15-03714.pdf`, Theorem 4 / deepest-point reduction).
  Read-only/scratch.

## What's done / banked

- Setup; Rung 0 design (bedrock-reviewed); spine fully de-risked at general L (codim=Mval proven 3 ways,
  θ characterized, R1 stratification architecture). All pushed.

## Next tick

On `fm`'s report: precision/bedrock review of encoded Foundations + skeleton (Rung 0c, hardener+rv);
restate the R1 skeleton statement as the **stratum value-match** (`λ_core=½·min_strata codim`, resolution
achieves it), not the superseded set-bijection. Then the validate-small-first Lean gate at (1,1,1)
[no blow-up], then L1/L2. On `pp`'s D1 report: scope/queue the D1 rung. Carry the stratification R1
architecture as the mountain's target.

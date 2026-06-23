# priorities — explicit `(C, θ)` for arbitrary `d`  (taste ledger)

Controller proposes a ranking (value-of-information × directed suspicion); the operator edits this
file directly (highest-authority signal). Nothing unranked; "unclear-but-keep-going" is first-class.

## Done

1. **[tide · thread 01] Arbitrary-`d` explicit `(C, θ)` — DONE.** `Core.CThetaArbitrary`:
   `cCodim_eq_cValue_comp_sort` / `numTop_eq_cTheta_comp_sort` (+ `r=0` variants), no `Monotone`
   hypothesis, non-monotone witness `(2,3,2)→(4,2)`. Green, axiom-clean, AUDIT cleared (controller
   green-gate + precision/bedrock read + decorrelated fidelity pass). `Tuple.monotone_sort` was the
   Mathlib bridge; nonemptiness discharged via `kostantPartitions_nonempty_of_le`.
2. **[docs] ROADMAP refresh — DONE.** Bundle 1 (Cor 5.10 / Thm 5.5 / Σ̄^r-aggregate / arbitrary-`d`
   marked Proved), Bundle 3 (the open-lift framing superseded — combinatorial route won), plus the new
   **Process / harness uplift** section (cache-sharing + controller-in-worktree).

## Resolved (was parked)

- **General-`r` statement shape.** Settled: `cValue ((dminus d r) ∘ Tuple.sort (dminus d r))` is clean
  (a 2-line rank-shift onto the `r=0` theorem); stated directly, not left as a bare corollary. The
  redundant `hr : ∀ k, r ≤ d k` was dropped (derived from `h` via `corner_le_dim_of_mem`).

## Remaining for close

- Exposition: a short "explicit `(C,θ)` for any `d`" section appended to the perm-invariance chapter.
- Commit on the expedition branch; signal-and-wait before the PR (close-phase gate).

## Drop / escalate

- (none yet)

# synthesis.md — Aoyagi-Full controller's integrative read

(Internal ledger; assumes repo context. Flushed every tick; read on re-ground. Not a deliverable.)

## Current read (2026-06-20): design COMPLETE; foundations bedrock; first Lean rung running

**Phase: execution.** The whole mathematical skeleton is mapped + the foundations are verified bedrock.

**Foundations (merged `a899db4`; Rung-0c PASS):** `DLNFibre.DLN.RLCT.{Foundations/Loss,Rlct,Lambda}.lean
+ Skeleton.lean`. Green; 9 named-sorry rungs + 1 axiom `monomial_rlct` (S2, narrowed to the bare
weighted-monomial-integral fact); defs axiom-clean. rv's 0c audit: PASS 5/5 (fidelity, S2-minimality,
θ-seam honesty, ofReal-clamp safe, vacuity+hygiene); λ headline does NOT touch `rlctOrderAt` (λ grounded).
2 non-blocking flags: (1) S2 order-half stray claim when all k=0 → scope to ∃j kⱼ≠0 (fm-2 fixing); (2) R1
encoded as value-match (correct).

**The full rung map (all scoped; pen-and-paper + decorrelated-Codex established, Lean-pending):**
- S1 (invariance): S1.1 weighted-threshold TRANSPORT (the heavy analytic core; wraps Mathlib Jacobian CoV
  + off-null-set + global properness) · S1.2 monotonicity · S1.3 ideal-invariance (germs) · S1.4 Σ_X+φ ·
  **S1.5 disjoint-block additivity (NEW; Laplace proof; engine of the L2 split; L2 needs only smooth-block case).**
- L1/L2 (thread-07): block elimination + product reduction → `λ = ½(r(H¹+H^{L+1})−r²) + λ_core`. MODERATE
  linear algebra. The reg term = ½·(rank-r STRATUM DIMENSION) [not ½·det-codim — terminology fix; encoded
  value already correct]. Ordering L1→L2→D1→R1→A1.
- D1 (thread-04): light; cite Aoyagi 2013 **Thm 2**; depends on L2 (homogeneous core); reuses S1.1.
- R1 (thread-03): **the one mountain.** `λ_core = ½·min_strata codim`, `codim S(t)=Mval` PROVEN general L.
  Architecture = resolve BY nested-rank strata (transversality input = differential-rank=codim), not charts.
- A1/A2: `lambdaCore = cleanCore = printedCore` (verified) + θ=a(ℓ−a)+1 (deepest-point divisor mult).

**Two genuinely hard Lean builds remain: S1.1 (analytic transport) and R1 (resolution construction).**
Everything else: linear algebra (L1/L2), a light reduction (D1), finite arithmetic (A1/A2).

## In flight

- `fm-2` — thread 08: validate `(1,1,1)` end-to-end (the anti-treadmill gate; trivial — no resolution) +
  the FLAG-1 S2 hygiene fix. Background, in the shared worktree.
- `pp` — stood down to on-demand (design complete). Re-engage for R1 construction / S1.5 blueprint / blockers.
- `rv`, `fm` — idle.

## Next tick

On `fm-2`'s (1,1,1) PASS: the architecture is validated end-to-end → climb the validation ladder
((2,1,2) cone blow-ups, then (2,2,2) recursive resolution) AND/OR start the rung proofs in dependency
order: S1 (S1.1 transport + corollaries + S1.5) → L1/L2 → D1 → R1 (re-engage pp for the mountain) → A1/A2
→ T. Build the S1 refactor (add S1.1, S1.5 to the skeleton) when starting S1. Topology: serial editing
(fm-2 in the worktree); consider the operator-relaunch option if R1 wants parallel sub-proofs.

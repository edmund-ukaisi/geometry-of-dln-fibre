# synthesis.md — Aoyagi-Full controller's integrative read

(Internal ledger; assumes repo context. Flushed every tick; read on re-ground. Not a deliverable.)

## Current read (2026-06-20): execution phase; CONTRACT FIX-LOOP open

Design complete; foundations defs bedrock (0c PASS). BUT a controller precision-read of the full
`Skeleton.lean` (@c2b23e1) caught **2 statement-fidelity bugs the green build + 0c audit missed** — the
"green is necessary, not sufficient" discipline in action. Fix-loop open.

### CONTRACT FIX-LOOP (the 2 bugs + corrected statements; fix BEFORE proving — precision policy)

1. **L1 `block_elimination` — VACUOUS.** `∃ invertible P,Q, (P·B·Q).rank = r` is trivially true (invertible
   mult preserves rank; P=Q=1). Name promises Lemma-2 block-normal form; statement delivers nothing.
   **FIX:** state the actual normal form, `∃ invertible P,Q, P·B·Q = <rank-r normal form diag(E_r,0)>`.
2. **L2 `product_reduction` — OVER-CLAIM.** `rlctAt(dlnLoss) wstar = aoyagiLambda` for EVERY
   `wstar ∈ optimalSet` is FALSE — the local RLCT varies over the fibre, minimized at the deepest point
   (that's why D1/Thm 4 exists; if L2 were true D1 is redundant). At milder optimal points rlctAt is
   strictly larger. **FIX:** introduce `deepestPoint H r B` (minimal-rank optimal point); state L2 as
   `rlctAt(deepestPoint) = aoyagiLambda` and re-key D1 as `⨅ = rlctAt(deepestPoint)`; re-thread the
   headline (currently type-checks only because L2 over-claims).
   Minor: R1 `resolution_charts` lacks an analyticity hypothesis on F (false for non-analytic F); A2
   `aoyagiTheta_eq` existential is weak (the secondary, seamed). Fix R1's hyp; A2 lower priority.
   S1.1/S1.5 (just added) look faithful (Jacobian weight present; single-space M + Z-omission both OK).

### WIN — λ-citation ELIMINABLE (banked, @22f5dfe)

The monomial threshold-half is directly provable from Mathlib (Fubini + rpow-iff); demonstrated axiom-free
for (1,1,1) (`Case111Bridge.lean`); the (1,1,1) headline dropped monomial_rlct. General = same recipe, no
wall, just Fin-d labour ⇒ λ can be made fully **axiom-free** (θ order-half stays seamed). Brief's
one-citation closing criterion → upgrade to zero-λ-citations once the general threshold-half lands.

## Rung map (all scoped; pen-and-paper established, Lean-pending)

S1 = S1.1 transport (heavy core) + S1.2/1.3/1.4 + S1.5 disjoint-additivity (Laplace) · L1/L2 product
reduction (statements being fixed) · D1 light (Aoyagi 2013 Thm 2; depends on L2; re-key to deepestPoint) ·
R1 the mountain (stratification: `codim S(t)=Mval` proven general L; `λ_core=½·min_strata codim`) ·
A1/A2 arithmetic (spine proven). Two genuinely hard Lean builds: S1.1 + R1.

## Topology — CONSOLIDATED
Formaliser/reviewer work in MAIN on `expedition/aoyagi-full` (cwd-collapse); controller green-gates +
pushes; `worktree-rung0-defs` retired; serial editing. Crossing mitigated by serial cadence (held so far).

## In flight
- `rv-2` — deep decorrelated statement-fidelity audit of the full skeleton (read-only; withholding my
  findings to test independently). Should corroborate L1/L2 + maybe find more.
- `fm-2` — the (1,1,1) rlctAt bridge (Case111; independent of the L1/L2 bugs). Told to stay out of Skeleton.
- `pp` — on-demand (design complete).

## Next tick
On rv-2's report: reconcile its findings with mine (L1/L2 + R1); hand `fm-2` the focused **Skeleton
restatement pass** (corrected L1/L2/R1 statements above) — fix wrong statements first. On fm-2's bridge:
green-gate + (if it closes) first full axiom-free end-to-end. Then the S1/L1/L2/D1 PROOFS in dependency
order; R1 (re-engage pp) is the mountain. Decision pending: whether to also prove the general
threshold-half now (eliminate the λ-axiom) or after the structural rungs.

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

## (1,1,1) gate finding — even the trivial case needs baby-S1.1

`fm-2` landed: dlnLoss→monomial coercion (sorry-free) + monomialThreshold=aoyagiLambda=1/2 (sorry-free
THROUGH monomial_rlct), but the `rlctAt = monomialThreshold` bridge is a named sorry — genuine S1 content
(germ-locality + nbhd↔box matching) even for an already-monomial F, because the narrowed S2 axiom is the
bare threshold fact, not "rlctAt = threshold". So the next Lean rung IS S1 (the bridge = baby S1.1, then
general). The (1,1,1) result validates the APPROACH (assembles to the right number via the one citation);
full end-to-end awaits the bridge. + S2 order-half hygiene fix done.

## Topology — CONSOLIDATED (cwd-collapse keeps landing teammates in MAIN)

Adopt: the active formaliser/reviewer work in the MAIN checkout on `expedition/aoyagi-full` directly
(their cwd resets there); the **controller green-gates + pushes**. `worktree-rung0-defs` is stale/retired
(no longer synced). Serial single-editor (one formaliser at a time). For PARALLEL formalisers (R1 sub-
proofs) we'd need real isolation → the operator-relaunch-from-MAIN option, deferred until R1 needs it.
Minor crossing risk (controller docs + formaliser Lean both commit to the branch in MAIN) — mitigated by
serial cadence + green-gate each integration.

## WIN — the λ-citation is ELIMINABLE (probe answered YES, @22f5dfe)

The threshold-half of `monomial_rlct` is **directly provable from Mathlib** (Fubini +
`intervalIntegral.integrableOn_Ioo_rpow_iff`): demonstrated axiom-free for (1,1,1)
(`Validate/Case111Bridge.lean`: `monomialThreshold 2 (1,1)(0,0)=1/2`, `#print axioms` standard only), and
the (1,1,1) headline's trace DROPPED monomial_rlct. The general (d,k,h) case is the SAME recipe (per-axis
rpow-iff + n-ary Fubini; binding axis sets ⨅; kⱼ=0 axes are units) — **no analytic wall, just Fin-d Lean
labour**. ⇒ we can make λ fully **axiom-free** (exceeding the brief's one-citation target); the θ
order-half stays seamed. Plan: (i) close the (1,1,1) gate now [validate-small-first completion], (ii) the
general threshold-half + general S1.1 transport = the S1 rung (re-engage pp for the n-ary blueprint).
The brief's closing criterion (one citation) will be UPGRADED to zero-λ-citations once the general
threshold-half lands; keep the conservative wording until then.

## In flight

- `fm-2` — thread 11: close the (1,1,1) `rlctAt` bridge (baby-S1.1: measure-preserving chart + two-sided
  `|x|^a` integrability + ∃-nbhd) → first FULLY axiom-free + sorry-free end-to-end. BOUNDED (report if a
  piece — esp. the `Params(1,1,1)≃ᵐℝ²` equiv — sprawls; don't thrash). Background, in MAIN.
- `pp` — on-demand. Next: the general S1 blueprint (n-ary monomial integrability for the axiom
  elimination + the general S1.1 transport) when (1,1,1) is closed.
- `rv-2`, `fm` — idle.

## In flight

- `fm-2` — thread 10: prove the (1,1,1) rlctAt bridge directly (closes first full end-to-end, 10→9 sorry)
  + the axiom-elimination probe. The base case of S1. Background, in MAIN.
- `pp` — on-demand (design complete). Re-engage for the general S1.1/S1.5 blueprint or R1 construction.
- `rv-2` — idle ((1,1,1) audit PASS, 5/5). `fm` — idle (stale seat).

## Next tick

On `fm-2`'s (1,1,1) PASS: the architecture is validated end-to-end → climb the validation ladder
((2,1,2) cone blow-ups, then (2,2,2) recursive resolution) AND/OR start the rung proofs in dependency
order: S1 (S1.1 transport + corollaries + S1.5) → L1/L2 → D1 → R1 (re-engage pp for the mountain) → A1/A2
→ T. Build the S1 refactor (add S1.1, S1.5 to the skeleton) when starting S1. Topology: serial editing
(fm-2 in the worktree); consider the operator-relaunch option if R1 wants parallel sub-proofs.

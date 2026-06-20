# synthesis.md — Aoyagi-Full controller's integrative read

(Internal ledger; assumes repo context. Flushed every tick; read on re-ground. Not a deliverable.)

## Current read (2026-06-20): CONTRACT FIX-LOOP — full audit done, fm-2 restating

The decorrelated bedrock gate paid off: my precision-read caught L1/L2; rv-2's deep per-rung audit
(+Codex counterexamples) CORROBORATED those and found 3 MORE (D1, S1.1, S1.5) — including two I had
wrongly judged "faithful." The contract has a clear, bounded fix list. fm-2 is restating (statements-first).

### THE 6 FLAGS + corrected statements (fix BEFORE proving — precision policy)

1. **L1 `block_elimination` — VACUOUS** (`(P·B·Q).rank=r` trivial under units). → `∃ inv P Q, P·B·Q = diag(E_r,0)` (block-normal form).
2. **L2 `product_reduction` — OVER-CLAIM** (`rlctAt=aoyagiLambda` ∀ optimal pt is FALSE; rv-2 witness:
   (2,2,2) milder pt → rlctAt=2≠3/2). → scope to the deepest point.
3. **D1 `deepest_point_reduction` — UNDER-CLAIM (NEW, rv-2)** (only "inf attained at SOME optimal pt";
   drops the deepest-point identification). **Co-fix with L2:** introduce `IsDeepest H r B w`;
   D1 = `∃ w, IsDeepest w ∧ ⨅ = rlctAt w`; L2 = `∀ w, IsDeepest w → rlctAt w = ofReal(aoyagiLambda)`;
   headline assembles `D1 ▸ L2`. (Fixing L2 alone breaks the headline — must re-key D1 in lockstep.)
4. **R1 `resolution_charts` — too-weak** (no analyticity → existential false for pathological F). → add
   `F` real-analytic + ≢0 near wstar. (Value-match conclusion is correct.)
5. **S1.1 `weightedThreshold_transport` — general-measure DEFECT (NEW, rv-2+Codex: ℝ with |x|dx, π=x³ →
   2≠4/3).** → pin the measure to Lebesgue/additive-Haar `volume` (or state on EuclideanSpace) + add
   `MeasurableSet E` / π(E)-null. (Jacobian-weight placement already correct.)
6. **S1.5 `rlct_additive_disjoint` — FALSE bare-measurable (NEW, rv-2+Codex: alternating step fns → ⊤≠2).**
   → add real-analytic hyps on F,G (or scope to the smooth-block/monomial case L2 needs).
   Nits: A1 `lambdaCore_eq_clean` existential weaker than docstring (soften/bind); `clean_eq_printed`
   docstring over-narrows (it's UNIVERSAL in (m,ℓ), verified 9324 cases). PASS: S2, S1.3, S1.4,
   clean_eq_printed-arithmetic, T-as-derivation (valid once D1/L2 re-keyed; ofReal clamp safe under hB).

**Lesson banked:** statement audits must be sharp + per-rung (vacuity/over-claim/measure-generality), not
just hygiene; my single read missed S1.1/S1.5 — decorrelated rv+Codex caught them. Multi-check works.

## WIN — λ-citation ELIMINABLE (banked @22f5dfe)
Monomial threshold-half directly provable from Mathlib (demonstrated axiom-free (1,1,1)). General = labour.

## (1,1,1) bridge — PARKED on the `Params ≃ᵐ ℝ^N` Lean wall (not math); pp researching the equiv route.

## Rung map (scoped): S1.1 transport + S1.2/3/4 + S1.5 · L1/L2 · D1 (light) · R1 (mountain;
`codim=Mval` proven gen L) · A1/A2. Hard Lean builds: S1.1 + R1 + the Params↔ℝ^N equiv infra.

## In flight
- `fm-2` — Skeleton restatement pass (6 fixes + 2 nits; corrected statements supplied). Priority.
- `pp` — researching the `Params H ≃ᵐ ℝ^N` measure-preserving equiv route (Mathlib precedent + diamond fix).
- `rv-2` — idle (audit done); next: re-audit the restated statements.

## Next tick
On fm-2's restatement: green-gate + verify the headline assembles from re-keyed D1/L2 → rv-2 re-audits the
new statements. On pp's equiv research: hand fm the equiv-build at the S1 phase. THEN the structural
PROOFS in dependency order (S1 corollaries first — S1.3/S1.4 light; then S1.1 needs the equiv; L1/L2; D1;
R1 = re-engage pp). Topology: serial editing in MAIN; controller green-gates.

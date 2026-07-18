# Verify — p.15 total-comparability is over-strong (THIRD verified paper defect)

*Provenance: pen-and-paper thread 08 (pnp08), fork-13 o4. Two-way: validated profile simulator
(`expeditions/2026-07-17-aoyagi-engine/threads/08-atlas-probe/battery/nonmono-2232-sim.py`,
`compchain-scope.py`) + decorrelated Codex (found the counterexample independently). Exact integer
algebra. Companion to the Def-3 defect (T-D, `verify-def3-underspec.md`) and the p.20 raw-width defect
(FIX-A, `verify-r1-diagb-*`/cert-nonmono-2232).*

## The claim (Aoyagi p.15, inside the inductive statement)

> "Moreover, we have `T_{s,k} ≤ T_{s',k'}` or `T_{s,k} ≥ T_{s',k'}`, for `1 ≤ s,s' ≤ L`,
> `1 ≤ k,k' ≤ M(S)`."

i.e. **every pair** of carried divisor `T`-vectors is comparable (componentwise) — the carried set is a
**total chain**. This is asserted as a maintained invariant of the double induction.

## The defect: FALSE at interior bottlenecks

**Counterexample** (minimal; Codex-found, simulator-reproduced). `M = (M^{(1)},…,M^{(4)}) = (2,2,1,1)`,
`L=3`, running-min `M(2)=2`, `M(3)=M(4)=1`. Layer 1 creates divisors `(0,0,0)` and `(1,1,1)`. Process:

| node | action | carried chain |
|---|---|---|
| `(S,J)=(2,0)` | case-1(2) on `f=(1,1,1)`: append `setTail(f,2,0)=(1,0,0)` | `(0,0,0)<(1,0,0)<(1,1,1)` |
| advance (`M(3)=1`) → `(3,0)` | interval `[J+1,M(3)-1]=[1,0]` empty ⟹ **Case 2** | appends `c=(M(2),M(3),0)=(2,1,0)` |

Then `c=(2,1,0)` and the carried `(1,1,1)` are **incomparable**:
`(1,1,1) ≰ (2,1,0)` (coordinate 3: `1>0`) and `(2,1,0) ≰ (1,1,1)` (coordinate 1: `2>1`). The claimed
total chain is broken.

**Mechanism.** A **width drop** (running-min `M(S)` falls) shrinks the `b`-chain; a divisor created
earlier at level `ℓ` is **stranded above** the shrunken chain (`ℓ ≥ M(S)`). The Case-2 append has the
(large) running-min head `(M(2),…,M(S))` and a small tail `J`, so it is incomparable with the stranded
divisor (larger head, smaller tail). Independent of the FIX-A raw-vs-running-min head-reset — it occurs
under both.

**Exact scope** (verified on 18 width vectors, `compchain-scope.py`, prediction matched 18/18):

> total-comparability fails **iff there is an interior bottleneck** —
> `∃ 3 ≤ S ≤ L` with `min(M^{(1)},…,M^{(S)}) < min(M^{(1)},M^{(2)})`.

Failing witnesses: `(2,2,1,1)`, `(3,3,1,1)`, `(3,3,2,2)`, `(4,4,2,2)`, `(4,4,3,2)`, `(3,3,2,1)`,
`(2,2,1,2)`, `(2,2,2,1,1)`. Non-failing (drop only at the last layer / no interior stranding):
`(3,2,4,2)`, `(2,2,2,1)`, `(3,2,2,2)`, `(3,3,4,2)`, `(3,3,3,1)`. Interior bottlenecks are a common DLN
configuration (a hidden layer narrower than the first two), so this is in scope, not a corner case.

## The repair: SameLevelChainInv (what the construction actually needs)

Replace the full-chain claim by the **same-level** restriction:

> `SameLevelChainInv`: divisors sharing a common `t̃`-level are pairwise comparable.

- **Holds everywhere** (0 violations at every reachable state on all 18 instances, incl. every
  interior bottleneck).
- **Sufficient for the construction.** The chooser's eligible set `E = {T : t̃ T = ℓ}` is same-level, so
  `SameLevelChainInv ⟹ E` is a chain `⟹` the Def-4 minimum exists and is unique (the only place the
  invariant is consumed). The `b`-chain `b_i = (∏_{t̃=i-1} u)·b_{i-1}` is level-filtered — its
  divisibility is automatic and needs only the level structure, not cross-level comparability.
- **Not derivable from a global head-chain.** "The head-projections `T_{1..S-1}` form a chain" is ALSO
  too strong (fails at `(3,3,1,1)`,`(4,4,2,2)`). The correct invariant is specifically same-level.

## What is NOT affected

- **The value.** `min` over `t̃=0` leaf divisors `= minAdm` at every one of the 18 instances (no
  undershoot). The finiteness/learning-coefficient value is untouched; only the paper's over-strong
  bookkeeping claim is false.
- **The tie-break's role (load-bearing).** The Def-4 minimality *maintains* the operative invariant:
  it preserves `LiveHeadDom` (live/in-chain head-domination), hence `SameLevelChainInv`, hence the
  chooser's own min-existence. A non-minimal (but eligible) pick BREAKS `SameLevelChainInv` — witnessed
  at `M=(2,2,3,3,2)` (`L=4`), node `(S,J)=(4,0)`: the max pick makes the level-0 divisors `(2,1,0,0)` and
  `(1,1,1,0)` incomparable, whereas the min pick keeps `0` violations. (At `L≤3` this is invisible — the
  eligible sets are too shallow — which is why an early shallow test wrongly read it "minimality-free".)
  So minimality is a genuine hypothesis of the repair's preservation, not mere canonicalization.

## Ledger status

Third verified defect in Aoyagi (2023) §4–§5, alongside:
- **(T-D)** Definition 3 condition-(iii) sign (`verify-def3-underspec.md`);
- **(FIX-A)** the p.20 Case-2 raw-width head-reset `t^{(i)}:=M^{(i+1)}` (should be the running-min
  `M(i+1)`; `cert-nonmono-2232.md`);
- **(p.15)** this entry — total-comparability is over-strong; repair = `SameLevelChainInv`.

All three are surfaced-and-repaired (the geometry/value survives); none blocks the learning-coefficient
target. The repairs are what the Lean engine builds on, not the printed claims.

# Adjudication — corank-≥2 shared-exceptional recursion: BOUNDED, or a genuine wall?

**Seat:** pen-and-paper (reconcile MY OWN two docs honestly — `chart-lemma-probe.md` verdict A vs
`outer-construction-cert.md` "THE WALL" — decorrelated Codex fed both claims neutrally). **Question:** is
the general corank-≥2 (arbitrary widths, ≥2 coupled blocks sharing exceptional divisors) shared-exceptional
recursion **(a) BOUNDED** (iterated single-radial explicit blow-ups + SJState shared-support ledger,
landing on the banked monomial terminal) or **(b) a genuine WALL** (a SIMULTANEOUS principalisation
Mathlib lacks → operator scope-call)?

---

## VERDICT: (a) BOUNDED — iterated-explicit. Re-greenlight the SJState carrier.

**The general corank-≥2 shared-exceptional recursion is Aoyagi's coupled `diag(b)` construction = a SEQUENCE
of EXPLICIT single-radial blow-up charts (Cases 1 & 2) with the shared support tracked by the `SJState`
`diag(b)·[E_J|D_J]·∏_{s>S}C` ledger. It is NOT abstract resolution-of-singularities / Hironaka, and Case-1's
shared-divisor merge is NOT a simultaneous move — the center is a coordinate center inside an ALREADY-EXISTING
exceptional divisor (`d_ij = u_{s,k}·d'_ij`), an ordinary sequential chart. The genuinely-new content is the
CARRIER BOOKKEEPING, bounded by the finite `(S,J)`/equal-run recursion. The one place it becomes a genuine
res-of-sing problem is the ATOM route (integrate Γ out → Gram-det principalisation of a degenerate product) —
the WRONG route (`pure-vs-atom-adj.md`), NOT the native blow-up.**

This CORRECTS the framing of my `outer-construction-cert.md`: "THE WALL" was the ATOM-route framing (the
Gram-det principalisation), which IS genuinely-new res-of-sing — but the NATIVE blow-up route is bounded. And
it SHARPENS `chart-lemma-probe.md`'s verdict A: "single-radial-per-block" is correct ONLY under the
interpretation "one radial for the current equal-run RESIDUAL block, old exceptionals carried in the `b_i`,
Case-1 may reuse an existing divisor" — a NAIVE fresh-per-block/per-row iteration UNDERCOUNTS (forgets
sharing). Decorrelated Codex (xhigh, both docs neutral) returned the SAME: **(a) bounded-iterated-explicit.**

## Reconciling the two docs (both partially right; the tension was route + interpretation)

| | `chart-lemma-probe` (CLAIM-A) | `outer-construction-cert` (CLAIM-B) | reconciled |
|---|---|---|---|
| iterated/sequential? | YES (sequential single-radial) | (implicit) | **YES — sequential explicit charts** |
| shared support needed? | under-stated (probe tested 1 block) | YES ("genuinely-new") | **YES — necessary (naive per-block undercounts)** |
| "wall" / res-of-sing? | NO (bounded) | "THE WALL" (over-labelled) | **NOT the native route; res-of-sing is the ATOM route only** |
| same object? | — | — | **SAME object: coupled diag(b) = iterated single-radial WITH shared ledger** |

CLAIM-A and CLAIM-B describe the SAME object at different resolution. The apparent conflict was (i) a
ROUTE confusion — CLAIM-B's res-of-sing is the atom-route Gram-det (`pure-vs-atom-adj`), not the native
blow-up — and (ii) an INTERPRETATION gap — "single-radial-per-block" must mean the shared-ledger version,
not naive fresh-per-block. sjcarrier2's "genuinely-new res-of-sing NOT labor" is the atom-route hazard
over-generalised to the native route; on the native route it is bounded carrier labor.

## Exact-algebra DATA (mine — `sjj_multiblock.py`, `sjj_radial_shared.py`)

1. **Shared-support is NECESSARY beyond one block** (the two novelties compound):
   - 1 block: `⟨δx,δy⟩` (shared `δ`) RLCT `½` vs `⟨δ₁x,δ₂y⟩` (separate) `1`.
   - **2 blocks:** terminal monomials `{u²x², u²v²y²}` (SHARED `u`) RLCT `½` vs `{u₁²x², u₂²v²y²}`
     (fresh per-block) `1`. **Sharing CHANGES the value at 2 blocks** ⟹ a naive fresh-per-block iteration
     is WRONG; the shared-support ledger is necessary. (Matches repo `verify-r1-light-recursion` / (3,3,4)
     coupled 4 vs per-row 3.)
2. **The ITERATED single-radial charge accounting reaches minAdm on multi-corank chains** (= `minAdmRec`,
   BANKED): `(3,3,3,4)` `[4,3,0]=7`; `(4,4,4,4)` `[4,3,4]=11`; `(3,3,3,3,3)` `[1,2,3,0]=6`; `(4,4,4,4,4)`
   `[1,2,3,4]=10` — each `Σ = Mval = minAdm`, layer-1 corank blocks up to `2×2`. So the ITERATION reaches
   the correct VALUE. (L=2 single-block `‖XY‖²` is fully banked: `routeMBoxThresholdFinite_rrp/_mnp`.)

## Codex INTERPRETATION (decorrelated, xhigh, both docs neutral — `codex/corank-{prompt,answer}.md`)

**(a) bounded-iterated-explicit.** "Aoyagi's coupled `diag(b)` recursion is a sequential explicit chart
construction … not a call to abstract Hironaka, and Case 1's shared-divisor merge is not a simultaneous
principalisation." CLAIM-A = CLAIM-B *iff* CLAIM-A means the shared-ledger single-radial (not fresh-per-block);
"coupled diag(b) does MORE than a fresh-per-block or per-row iteration … that is exactly why
threshold-only/per-row models fail." Case 1(1): "the center is a coordinate center contained in an
already-existing exceptional divisor … `d_ij = u_{s,k} d'_ij` … an ordinary sequential coordinate blow-up
chart." Genuinely-new = the carrier bookkeeping (SJState, equal-run partition, support map, Case-1 exponent
merge, the relative chart lemma, termination + `Σ b_i²` endpoint) — "substantial formalization work, but
bounded by the finite `(S,J)`/equal-run recursion." **Decisive:** "It does not force a simultaneous
principalisation UNLESS you choose the Gram-det/atom route and then try to recover the missing sharing
afterward." (Matches my `pure-vs-atom-adj`.)

---

## Formalisation-ready SJState carrier structure (the (a)-verdict deliverable)

**State `SJState`:** `(S, J)`; residual block `D_J` (`(M(S)−J)×(M^{(S+1)}−J)`); the monomials `b_1,…,b_{M(S)}`
(each a product of exceptional `u`'s); **the support map** `gen ↦ {exceptional u's dividing it}` (records
sharing — the load-bearing datum, provably necessary by DATA-1).

**Iteration (Cases 1 & 2, explicit single-radial charts):**
- partition `b_{J+1},…,b_{M(S)}` by EQUAL RUNS;
- **Case 2** (full equal run): one FRESH radial `u` for the whole block, charge = full block codim; reduce
  `D_J → diag(1, D_{J+1})` by `Z`-independent unit transforms; advance `J`; append `u` to the shared `b_i`;
- **Case 1** (partial equal run `J₁`): sub-case 1(1) blow up the partial block ALONG an EXISTING divisor
  `u_{s,k}` (`d_ij=u_{s,k}d'`, add `J₁(M^{(S+1)}−J)` to that divisor's exponent — the shared merge, an
  ordinary chart); sub-case 1(2) introduce a new `u_{S,J+1}`, advance `J`.
- **relative chart lemma** (the crux, `chart-lemma-probe`): old exceptional `u`'s remain PASSIVE monomial
  prefactors while the active block is reduced; the reductions absorb into the adjacent factor, deeper
  factors untouched.

**Terminate** at `S=L+1`: loss `= Σ b_i²` on a finite chart cover, each chart `(monomial)²·(unit≥1)`;
finiteness by the banked monomial endpoint `monomialIntegrand_integrable_of_lt` (coordinatewise
`κ_i−2c'N_i>−1`), below threshold since terminal exponents `= Mval ≥ minAdm` (banked `minAdmRec_eq_minAdm`;
`0/171` threshold monotonicity). Termination by the finite `(S,J)` recursion.

**Banked substrate:** `radial_morse_residual_power_le` (single-radial), `pivotChartCover_matBox_le_sum`
(finite cover), `Case111`/`Case222` (Case-1/Case-2 templates at `(2,2,2)` — lift to opaque widths),
`monomialIntegrand_integrable_of_lt` (endpoint), `minAdmRec_eq_minAdm`/`sjChargeUpdate_accum`/`sjSubordination`
(charge/value), `sjBase1_freeMatrix` (L=1 base).

**Single hardest bounded brick:** the SJState relative chart lemma at opaque widths with the shared-divisor
ledger (Case-1 merge + passive-prefactor invariant across the finite cover). Substantial multi-tide labor;
NOT res-of-sing.

## Closing

- **Firmest.** (a) BOUNDED. The corank-≥2 shared-exceptional recursion is iterated EXPLICIT single-radial
  blow-ups (Cases 1&2) with the SJState shared-support ledger; Case-1 merge is a bounded explicit chart
  (existing-divisor center), not simultaneous. Value reached by iteration (minAdmRec, banked); sharing
  necessary (DATA-1: 2-block shared ½ ≠ separate 1); native route needs no res-of-sing. Codex identical.
- **The genuine res-of-sing wall exists ONLY on the atom route** (Gram-det principalisation of a degenerate
  product) — `pure-vs-atom-adj.md`. Build the NATIVE blow-up carrier; do NOT complete the atom route on the
  degenerate strata.
- **Reconciliation of my docs:** `chart-lemma-probe` verdict A stands (with the shared-ledger interpretation);
  `outer-construction-cert`'s "THE WALL" is re-scoped to "the substantial-but-bounded SJState carrier"
  (the res-of-sing reading applies to the atom route only). No operator scope-call for res-of-sing.
- **The one thing to watch (the probe's caveat, now the sharpest risk):** the relative chart lemma at
  arbitrary widths + the Case-1 equal-run/shared-divisor merge — this is where the `(2,2,2)` `Case111/Case222`
  templates must be lifted to opaque widths WITH the correct shared ledger. Bounded (finite `(S,J)`
  recursion, certified value), but it is the substantial genuinely-new carrier content and the true test of
  the multi-tide build.

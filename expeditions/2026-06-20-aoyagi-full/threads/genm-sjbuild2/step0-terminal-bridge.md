# STEP-0 VERIFY-FIRST GATE — the terminal count↔monomial bridge (R1-UPPER decorated CoV build)

**Thread:** `genm-sjbuild2` (formaliser, R1-UPPER CoV mountain → `sjJointResolution`).
**Base:** `expedition/aoyagi-full` @ `374f2011`. **No Lean build in STEP 0** — exact `ℕ`/`Fraction`
recursion (mirrors `RouteMLayerSplit.lean`'s `minAdm`/`redChain`/`Adm`/`Mval` verbatim) + a toric
Newton-polytope LP cross-check (`scipy.linprog`, exact optimum). `/tmp/step0_bridge.py`,
`/tmp/step0_bridge2.py`.

## VERDICT — GATE PASS

**The terminal count↔monomial bridge `½·minAdm(remChain π) ≤ monomialThreshold d (sharedDivisorExp) jac`
is UNIFORM over ALL route terminals (all Case-1/Case-2 chart sequences of the three anchors + three
more).** The carrier threshold `carrierThreshold π = ½·minAdm(remChain π)` depends ONLY on `remChain π`,
NOT on the decoration `(carrier, jac)`. **Codex's named failure mode (the threshold would have to carry
the decoration) DOES NOT FIRE. Proceed to the multi-tide build.**

## The sharp risk r1predicate flagged, and why it does not bite

The risk: each peel introduces a radial with ledger entry `(k, jac) = (1, pq−1)` (fully-shared radial,
`radialStep`/`sjLoss_prependColumn_one` ⟹ `k = sharedDivisorExp = 1`; radial blow-up Jacobian in `pq`
dimensions ⟹ `jac = pq − 1`). So the **diagonal** monomial threshold of the accumulated ledger is

    monomialThreshold d (sharedDivisorExp) jac  =  min_j (jac_j+1)/(2·k_j)  =  min_j pq_j / 2  =  ½·min(charges).

For a **multi-peel** route this is STRICTLY LESS than `½·minAdm = ½·∑(charges)` (e.g. `(3,3,3,4)` t=(1,0,0):
`½·min(4,3) = 3/2 < 7/2`). If this diagonal threshold were the operative finiteness gate, the bridge would
FAIL and the decoration would have to enter the threshold.

**It is NEVER the operative gate.** The recursion does not integrate the accumulated radial monomial
`∏ u_j^{jac_j}` pointwise at the end (that is the divergent-undercount route the separable weight-form would
have committed to). It PEELS one radial at a time via the banked **regime-A exponent shift**
(`matBox_corank_residual_absZ_le`, `c'>pq/2`, `W>0`): `∫∫ (frobSq Δ + W)^{−c'} ≤ Cresid·∫ W^{−(c'−pq/2)}`,
handing the SHIFTED exponent `c'−pq_j/2` to the deeper factor `W = frobSq(deeper product)` (the genuinely
coupled loss, not a detached monomial). The shifts COMPOSE ADDITIVELY:

    c' < ½·minAdm(M)  ⟹  after peeling charges pq_0,…,pq_{k−1}:  c' − ∑ pq_j/2  <  ½·minAdm(remChain terminal),

which is exactly the banked soundness gate `minAdm_le_peelCharge_add_redChain` (EQUALITY on every binding
branch). At the terminal the residual is a free-matrix Morse block, closed by the banked **regime-B**
`matBox_corank_dominates_absZ_lt_top` (`c'<pq_T/2`, `W≥0`), at which the shifted exponent lands EXACTLY at
`pq_T/2 = ½·minAdm(remChain terminal)`.

## Where each terminal flavour goes (the DISPATCH the build's `decorated_base` needs)

Every binding route (verified below) reaches a `redChain` leaf that is one of two kinds — and the bridge is
uniform because the monomial-diagonal threshold is only ever consulted where it is trivially satisfied:

| terminal kind | who closes it | `minAdm(remChain term)` | bridge status |
|---|---|---|---|
| **free-matrix leaf** `Fin 2`, charge `pq_T>0` (isotropic Morse; residual `∑y²` VANISHES, so it is **not** a dehomogenised unit → `sjLoss_terminal_lintegral_lt_top`'s `∃i₀ residual=0` hypothesis does **not** fire) | **regime B** `matBox_corank_dominates_absZ_lt_top` + `sjBase1_freeMatrix`; exponent budget lands at `pq_T/2` via the soundness gate | `pq_T` | `½·pq_T ≤ pq_T/2` **EQUALITY**, and it is regime B (not the diagonal threshold) that fires |
| **collapsed / trivial leaf** (`Fin 1`, or `Fin 2` with charge `0`) — the fully-monomialised, dehomogenised terminal | **monomial** `sjLoss_terminal_lintegral_lt_top` (residual unit `≥1`); the exponent has been shifted below `0` | `0` | `0 ≤ monomialThreshold` **TRIVIAL** |

There is **no** route terminal that is a genuine monomial terminal (dehomogenised unit) with
`minAdm(remChain term) > 0`: the recursion structurally descends to a `redChain` leaf; a `Fin 2` leaf with
`pq_T>0` is isotropic-Morse (regime B, not monomial), a `Fin 1`/charge-`0` leaf has `minAdm = 0`. This is the
precise reason the diagonal `½·min(charges)` undercount is harmless — it is only ever compared against `0`.

## Evidence (exact, all binding branches)

**Exponent-shift additive composition `= ½·minAdm` on every binding branch** (`= minAdmRec`, itself already
Lean-proven sorry-free as `minAdmRec_eq_minAdm`; re-confirmed here per-branch):

| M | minAdm | binding branch → (peel charges)+terminal | expShift sup | terminal |
|---|---|---|---|---|
| (3,3,4) | 8 | (1,0): [4]+4 | 4 = ½·8 | free (1,4), chg 4 |
| (2,2,2,2) | 3 | (1,0,0): [1,2]+0 · (1,1,0): [1,0]+2 · (2,1,0): [0,1]+2 | 3/2 each | free/trivial |
| (3,3,3,4) | 7 | (1,0,0): [4,3]+0 · (2,0,0): [1,6]+0 · (2,1,0): [1,2]+4 | 7/2 each | free (1,4)/trivial |
| (3,3,2,2) | 4 | (2,1,0),(3,1,0),(3,2,0) | 2 each | free (1,2)/(2,2) |
| (4,4,2,2) | 4 | (4,2,0): [0,0]+4 | 2 | free (2,2), chg 4 |
| (2,2,2) | 3 | (1,0): [1]+2 | 3/2 | free (1,2), chg 2 |

All branches: exponent-shift sup `== ½·minAdm`. **PASS (0 mismatches).**

**Toric Newton-polytope RLCT of the nested-shared monomial model `= ½·minAdm`** (NOT `½·min(charges)`):
the sequential-blow-up model where the deeper block generators carry the PRODUCT of the upstream radials
(nested-shared) with the composed-blow-up Jacobian weight (`h_i+1 = #carriers of u_i`). `scipy.linprog`
optimum:

    (3,3,4)   T=(1,0):   RLCT 4.0   = ½·8   ✓
    (2,2,2,2) T=(1,1,0): RLCT 1.5   = ½·3   ✓
    (3,3,3,4) T=(1,0,0): RLCT 3.5   = ½·7   ✓
    (3,3,3,4) T=(2,1,0): RLCT 3.5   = ½·7   ✓

The shared ledger, resolved correctly, concentrates the binding to reproduce `½·minAdm` — confirming the
generator-carrier decoration (`sharedDivisorExp` shared across nested blocks) is the faithful object, and
the fresh-per-block reading undercounts (DATA-A, `genm-sjnative`).

## Registered obligations (carry into the build — named, not hand-waved)

1. **The `c' = pq/2` regime-boundary** is covered by NEITHER banked regime lemma (regime A needs `c'>pq/2`,
   regime B needs `c'<pq/2`). Needs an explicit ε-approach (`c' < c'' < min(carrierThreshold, next regime)`
   with regime A at `c''`) or a dedicated boundary lemma. Bites when `pq` is even and `pq/2 < ½·minAdm`
   (e.g. `(3,3,4)` at `c'=2`, `pq=4`). This is a proof obligation of `decorated_peel_step`, NOT a
   bridge-uniformity issue.
2. **`decorated_base` must DISPATCH** on the terminal kind (table above): free-matrix leaf → regime B
   `matBox_corank_dominates_absZ_lt_top` + `sjBase1_freeMatrix`; collapsed/dehomogenised leaf → monomial
   `sjLoss_terminal_lintegral_lt_top`. The bridge `½·minAdm(remChain term) ≤ monomialThreshold` is only
   consulted on the second branch, where `minAdm = 0` makes it trivial.
3. **The soundness gate is EQUALITY on binding branches** (`minAdm(M) = peelCharge + minAdm(redChain)`) —
   this is what makes each exponent shift land exactly below the next carrier threshold. Banked
   (`minAdm_le_peelCharge_add_redChain`); the `≤` direction is all the build consumes.

## Files
`/tmp/step0_bridge.py` (per-anchor trace + bridge classification), `/tmp/step0_bridge2.py` (full
binding-branch sweep + toric-LP cross-check). Combinatorial spine mirrors `RouteMLayerSplit.lean`.

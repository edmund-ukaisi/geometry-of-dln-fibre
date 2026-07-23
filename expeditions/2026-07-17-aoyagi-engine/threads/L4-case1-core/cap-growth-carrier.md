# Growth-V3 descent carrier — for seat-descent's (C)/#98 (the last-clear growth arm)

pnp-cap, task #104. The precise, Lean-renderable carrier for the KILL step's last-clear growth arm: the
escaped-column coefficient of `sourceClearedResid` at the last clear is killed by `couplingClear` because it
lies in the ideal of the ACCUMULATED all-layer `couplingCoords`, via the ∏A product-chain / layer descent.
Verified exact (verify/, exit 0). Decorrelated Codex red-team: codex/cap-growth-carrier-*.

NOTATION (fixed). `A_m` = layer-m matrix, shape `d_{m+1} × d_m`. `∏A = A_{N-1}···A_0 = coreGen`.
`P_L := A_L·A_{L-1}···A_0` (prefix product, shape `d_{L+1} × d_0`). `wmu(n) = min(d_0..d_n)`
(non-increasing). Diagonal branch; last clear of layer S is the child `q = (S, wmu(S+1))` after clearing
layer-S cols `0..wmu(S+1)-1`. `escapedCol(S+1)` = layer-`(S+1)` coords with `col ≥ wmu(S+1)`.

## 0. What the growth arm needs (the obligation this carrier discharges)

At `q`, `escapedCol(S+1)` enters the killed set. The growth arm's obligation:
`sourceClearedResid q = foldResid q ∘ couplingClear q` IGNORES `escapedCol(S+1)` — i.e. for each escaped
coord `m ∈ escapedCol(S+1)`, `foldResid q`'s coefficient of `u_m` lies in `⟨couplingCoords(q)⟩` (so
`couplingClear q`, which zeroes those coords, kills the `u_m`-dependence). `couplingCoords(q)` is the
ACCUMULATED set over ALL clears on the branch (all layers `0..S`), NOT the current layer's alone — this is
the crux #92 named, and it is why a single-layer kill is false on wide pairing layers.

## 1. Reduction to the prefix product (the ∏A read)

`foldResid q = coreGen ∘ Φ_q` (`Φ_q` = accumulated blow-ups+shears). For an escaped coord
`m = (S+1, a, e)` (row `a`, col `e ≥ wmu(S+1)`), its coefficient in `coreGen = A_{N-1}···A_{S+1}·A_S···A_0`
factors (the coord sits at the layer-`(S+1)` edge of every monomial path):

    coeff_m  =  [ left factor: rows of A_{N-1}···A_{S+2} reaching row a ]  ×  [ row e of P_S ] ,

where `P_S = A_S·A_{S-1}···A_0`. The left factor reads only layers `≥ S+2` (disjoint from the couplings).
So the coupling content is entirely in **row `e` of `P_S`, with `e ≥ wmu(S+1)`** — a REMNANT ROW.

**BRIDGE IS NON-TRIVIAL (render-pricing, corrected — `cap_growth_bridge_and_trace.py`).** The fold-level
coefficient `fold c_m` (of `u_m` in `foldResid q = coreGen ∘ Φ_q`) does NOT equal the pure `pure c_m` (row
`e` of `P_S`): the escaped coord `m` (col `e ≥ wmu(S+1)`) is a SPECTATOR as an OUTPUT of `Φ_q` (shears write
only block cols `< wmu(S+1)`), BUT the shear branch-(ii) READS escaped coords to write block cols, so
`coreGen` reading those block-col slots picks up `u_m` — `fold c_m = pure c_m + shear corrections`. HOWEVER
**both `fold c_m` and `pure c_m` are `∈ ⟨couplings⟩`** (verified, `(2,3,3,3)`+`(3,2,3,3)`). So the render has
two routes (pick with the controller; I hold no Lean-feasibility model):
- **(A) reduce-to-pure**: prove §2 on the static `P_S`, then bridge `foldResid = coreGen ∘ Φ_q` (the shear
  corrections are also coupling-carrying — extra Lean work: the branch-(ii) read analysis).
- **(B) fold-native** (likely cheaper): prove `escaped-coeff ∈ ⟨accumulated couplings⟩` DIRECTLY by induction
  on the FOLD recursion, mirroring `foldResid_layerHomogeneous'`'s structure (which the render already
  consumes for the homogeneity), NO bridge. §2/§3 below is the MECHANISM either route uses; stated on the
  static `P_S` for clarity, but route (B) runs the analogous split on the fold's own step.

## 2. THE DESCENT LEMMA (the internal helper seat-descent renders)

    couplingCoords(0..L) := { A_m[r,c] : m ≤ L, c < wmu(m+1), r > c }   -- below-diagonal cleared entries

    LEMMA (descent).  For every L and every REMNANT ROW r with wmu(L+1) ≤ r (< d_{L+1}),
      every entry  P_L[r, k] ∈ ⟨ couplingCoords(0..L) ⟩.

Consumed with §1: `coeff_m ∈ ⟨couplingCoords(0..S)⟩` (row `e ≥ wmu(S+1)` of `P_S`) ⟹ `couplingClear q`
kills `u_m`. Instantiate at `L = S`, `r = e`.

Verified: `cap_growth_descent_lemma.py` (pure ∏A, deep + `d_0>wmu(1)` + interior-drop witnesses, exit 0)
and `cap_growth_carrier_battery.py` (the real fold with blow-ups, depth 2, exit 0). NO survivors.

## 3. HOW ∏A THREADS — downward induction on L, `multPrefix` peel

`P_L = A_L · P_{L-1}` (the outer/leftmost factor peeled; this is the `multPrefix`-style peel, recursing on
the LAYER index `L` downward, NOT `Fin.induction` over rows). Per-layer step:

    P_L[r,k] = Σ_{j=0}^{d_L-1} A_L[r,j] · P_{L-1}[j,k].

Split each contraction index `j` (the shared d_L index):

- **(i) `j < wmu(L+1)` (cleared col of layer L).** Since `r ≥ wmu(L+1) > j`, `A_L[r,j]` is a
  below-diagonal entry of a cleared column ⟹ `A_L[r,j] ∈ couplingCoords(L)` ⟹ the term `∈ ⟨couplings⟩`.
  [Coupling found AT layer L — the term is done, no recursion.]
- **(ii) `j ≥ wmu(L+1)` (uncleared col of layer L).** By the §4 KEY FACT, `wmu(L+1) = wmu(L)` in the
  non-vacuous case, so `j ≥ wmu(L)`; and `j < d_L` (a col index of `A_L`), so `j` is a valid REMNANT ROW of
  `P_{L-1}` (which has `d_L` rows). Hence `P_{L-1}[j,k] ∈ ⟨couplingCoords(0..L-1)⟩` by the IH.
  [RECURSE to level `L-1`.]

Both branches land in `⟨couplingCoords(0..L)⟩`. The induction is downward on `L`; the IH is the lemma at
`L-1`.

## 4. The KEY FACT (`wmu(L+1)=wmu(L)`), the vacuity split, and BOTTLENECK termination

**Do the vacuity split FIRST — the recurse fact comes from the remnant-row EXISTENCE, not from case (ii)
being non-empty** (Codex red-team, `codex/cap-growth-carrier-answer.md`; my first draft had this backwards —
case (ii) can be non-empty with `wmu(L+1) < wmu(L)`, e.g. `d=(5,5,3), L=1`: `wmu(2)=3<5=wmu(1)`, `j=3,4`
uncleared, but there `r ∈ [3, d_2=3)` is EMPTY so the claim is vacuous).

KEY FACT. If a valid remnant row exists — `wmu(L+1) ≤ r < d_{L+1}` — then `wmu(L+1) < d_{L+1}`, so
`wmu(L+1) = min(wmu(L), d_{L+1}) = wmu(L)`. So in every NON-vacuous case `wmu(L+1) = wmu(L) =: q`, and step
(ii)'s `j ≥ wmu(L+1) = q = wmu(L)` holds — no gap. (If no valid `r`, the lemma is vacuously true; render
the vacuity branch before the split.)

BASE `L = 0`. Existence of `r` (`wmu(1) ≤ r < d_1`) forces `wmu(1) = d_0` (else `wmu(1)=d_1` and
`r ≥ d_1` contradicts `r < d_1`). So every output col `k < d_0 = wmu(1)` is cleared and `r ≥ d_0 > k`, hence
`A_0[r,k] ∈ couplingCoords(0)` — the row is coupling-supported outright, no recursion. (`P_0 = A_0`.)

TERMINATION. Nonvacuous ⟹ the min `q = wmu(S+1)` is attained at some `B ≤ S` (escaped col live ⟹
`d_{S+1} > wmu(S+1)` ⟹ the min is NOT at `S+1`). Take the LARGEST such `B`: `A_B` has exactly `d_B = q`
cols and `wmu(B+1) = q`, so ALL its cols are cleared — case (ii) is EMPTY at B. The recursion descends only
through case (ii) (uncleared cols), so it never passes B; it bottoms there. It never reaches an uncleared
layer-0 output col: the `d_0 > wmu(1)` worry is unreachable — `d_0 > wmu(1)` forces `d_1 = wmu(1)`, so `P_0`
has NO remnant rows (the level-0 claim is vacuous), and the descent bottoms at `B > 0`. (Indexing note for
the render: the `B = S+1`-only case = the vacuous case, handled up front.) Verified: the bottleneck achieves
`d_B = wmu(S+1)` on every witness incl. `d_0 > wmu(1)` and interior drops (`cap_growth_descent_lemma.py`).

## 5. The accumulated `couplingCoords` bookkeeping

`couplingCoords(q)` (the clearing set `couplingClear q` zeroes) is the union over ALL clears on the branch:
for each diagonal clear of pivot `(m, b, b)` at layer `m` (branch clears cols `0..wmu(m+1)-1` at each layer
`m ≤ S`), the below-pivot entries `{ A_m[r, b] : r > b }`. Equivalently
`couplingCoords(q) = { A_m[r,c] : m ≤ S, c < wmu(m+1), r > c }` = `couplingCoords(0..S)` of §2. The descent
rides this ALL-LAYER set: case (i) at level L contributes a layer-L coupling, so a single monomial's kill
can come from ANY layer `B ≤ L ≤ S` — the reason the accumulated (not per-layer) set is essential.

## 6. Diagonal / hcanon dependency (ties to #95 — LOAD-BEARING hypothesis)

The whole carrier assumes the DIAGONAL branch (pivots `(m,b,b)`, so cleared cols are `0..wmu(m+1)-1` and
below-pivot = below-diagonal). On a ROW-REPEAT fan (#95), `couplingClear` keys on the stored pivot row, so
`belowPivotCol = ∅` and the escaped col is read coupling-free — the carrier FAILS. So the descent lemma must
be stated under the full-diagonal pin (`hcanon` / `CanonicalPivots` full-diagonal). This is the same
load-bearing scope my V3 termwise work flagged (`cap_kill_termwise_diagonal.py`); seat-descent consumes it.

## 7. Kill-conditions

- **§2 lemma**: a `(d,L,r,k)` with `r ≥ wmu(L+1)` and `P_L[r,k] ∉ ⟨couplings(0..L)⟩` — checked FALSE on
  deep/`d_0>wmu1`/interior-drop witnesses (`cap_growth_descent_lemma.py`).
- **§4 recurse fact**: a NON-vacuous case (valid remnant row exists) with `wmu(L+1) < wmu(L)` — impossible
  (remnant-row existence `⟹ wmu(L+1) < d_{L+1} ⟹ wmu(L+1) = wmu(L)`). NB case (ii) alone can be non-empty
  with `wmu(L+1) < wmu(L)` (`(5,5,3)`), but only in the VACUOUS case — hence the vacuity-split-first ordering
  is load-bearing for the render (Codex red-team).
- **§4 termination**: the descent reaching an uncleared layer-0 output col — unreachable (bottleneck ≤ S
  bottoms it; `escapedCol` live ⟹ min achieved ≤ S).
- **§1 bridge**: a blow-up `Φ_q` that moves an escaped coord's coupling content — checked FALSE at depth 2
  (layer-`≥S+1` coords are spectators of the layer-`≤S` blow-ups).
- **§6 diagonal**: a row-repeat fan escapes (`cap_kill_termwise_diagonal.py`) — the hcanon pin is required.

## 8. Artifacts
- `verify/cap_growth_descent_lemma.py` — the §2 lemma on the pure prefix product, deep witnesses.
- `verify/cap_growth_carrier_battery.py` — the real fold (blow-ups), depth 2, the §1 bridge.
- `verify/cap_kill_termwise_diagonal.py` — the §6 diagonal-vs-row-repeat boundary (from the V3 work).
- `codex/cap-growth-carrier-{prompt,answer}.md` — decorrelated red-team of the §3/§4 induction.

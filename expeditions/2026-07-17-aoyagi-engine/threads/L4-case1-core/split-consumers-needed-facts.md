# Needed-facts list: the MergeBoostSplit content lemma's four consumers
(seat-LL, 2026-07-24, relayed+banked by controller; the render contract for
`foldResid_case11_mergeBoostSplit_canon`'s final statement shape)

The split: `foldResid(parent) j u = ∑_{i∈partial} α_{j,i}(u)·u_i + u_{e₂}·∑_{i∈extra} β_{j,i}(u)·u_i`,
e₂ = the merge/boost pivot.

- **Consumers 1, 2** (case1_conjA; lastLayer case11 at S=L): the `Deg1SupportedOn ed.center`
  CONCLUSION — already served by `realBranch_boostReady_case11` (no interior guard).
- **Consumer 4 — born-unit** (GeneratorCleared, δ=1 GENUINE clear = **case12/case2**, child.cleared=1;
  NOT case11 — there cleared stays 0 and the clause is vacuous): needs the decomp PLUS the one fact
  the decomp alone does not give — **∃ j, c_{e₂}(j) 0 ≠ 0** (the pivot coefficient non-vanishing at
  the origin for some slot). Then `foldResid(child) j 0 = c_{e₂}(j) 0` (strict transform: u_{e₂}→1,
  others→0 at the origin via blockBlowupCoordQuot) = the born unit. Paper anchor: worked.tex:566-573,
  the S2 recursion `diag(b)·[[E_J,O],[O,D_J]]` "has cleared J unit pivots in layer S" — E_J's diagonal
  = the cleared coordinate = the unit (b_i, a non-vanishing monomial).
- **Consumer 3 — conjunct-2** (S=L per-slot disjunction, ALL cases): per slot,
  `Deg1SupportedSlot(child) ∨ unit`. case11 (cleared=0): remainder Deg1-on-blockCoords(N−1) after
  dehomog + pivot-carrying slots flagged units. case12/2 (cleared≥1): supportAt(child)=∅ — each slot
  ≡0 or a unit; the split certifies which. ⟹ per-slot DISJUNCTION: pivot-coeff-nonzero-at-0 (unit)
  XOR pivot-free (descends).
- **Shaping request** (L4D's call, see the relay): cover case12/case2 as the degenerate no-boost
  split (extra = ∅) in the same statement, OR keep case11-only and add a sibling for the case12/2
  pivot-non-vanishing (possibly easier: a fresh clear's pivot is the blow-up coordinate itself).

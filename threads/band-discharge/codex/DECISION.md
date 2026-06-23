# Band discharge — route decision (Codex xhigh + numerical)

Goal: discharge the single `hband` sorry in `lambdaCore_eq_clean`.

## Numerical verification (0-fail)
- Band holds on qStar=backwardGreedy: 3900 cases.
- forward-max witness meets band: 19525 cases.
- qStar prefix = MAX feasible prefix (mirror of suffix-min): 3900 cases.
- forwardHead at pos 0 >= M^0: 19525 cases.
- DEAD: rank-match (ascending pointwise) minimises prefix — FAILS.
- DEAD: anti-rank / top-largest-block — feasible-but-fails or infeasible.
- Yvec-in-order NOT feasible (Mwidths non-monotone).

## Codex ranking (xhigh)
1. **Route A: forwardMax proof-free + Classical** — ~160-260 lines, LOW risk. WINNER.
   Gotcha: define forwardMax TOTAL (empty fallback), NOT taking `h:Dom` as arg;
   prove specs (perm/feasible/ge/dom/prefix) separately under Dom. Avoids brittle
   proof-dependent recursion + the Dom-Decidable issue (open Classical).
2. Route B (direct backwardGreedy induction) — 350-600 lines, HIGH risk: right-recursion
   fights the FIRST-prefix arithmetic. REJECTED.
3. Route C (abstract exchange) — 600-1000 lines. REJECTED.

## Plan (route A)
- `feasible_perm_dom`: feasible perm of R ⟹ Dom b R (count argument, cLt API).
- `forwardMax`/`forwardHead`/`liveCand` (Classical, total).
- `liveCand_nonempty` from backwardGreedy's head being live (feasible + keeps Dom).
- specs: forwardHead_ge, forwardHead_dom, forwardMax_perm, forwardMax_feasible.
- `forwardMax_prefix_band`: the prefix lower bound; arithmetic = good_floor_core.
  KEY: w0 = forwardHead(pos0) >= M^0 (verified). Combined with feasibility on rest.
- Glue via backwardGreedy_suffix_le + total-sum (prefix↔suffix), mirror QFeas_qStar.hpre.

## OUTCOME (this tide)
PARTIAL — band glue + witness machinery GREEN; ONE seam open (forwardMax_prefix_band).
- Built green: forwardMax/forwardHead/liveCand (Classical, proof-free — Decidable wall SOLVED),
  feasiblePerm_dom, liveCand_nonempty, forwardHead_ge/_mem/_dom, live_le_forwardHead,
  forwardMax_perm, forwardMax_feasible, sum_range_getD_eq_take, + full hband glue (prefix↔suffix
  via backwardGreedy_suffix_le + admBound j=0/j≥1 cases).
- Open: forwardMax_prefix_band (prefix_k(fm) ≥ S'_k / ≥ max(M0,M1) at k=1). +293 LoC net.
- Conclusively established (5+ attempts, 2 Codex consults): the bound is NOT abstract-Dom; needs
  good_floor_core via the window lemma. No fixed-perm witness works (rank/anti-rank/top-block/
  smallestK all fail; smallestK fails exactly the brief's 4705). Window existence verified 0-fail.
- 2nd Codex consult (prefix-bound, breadth) TIMED OUT at 400s — not substituted (policy);
  3rd (prefix2, narrow, high) returned: confirmed window lemma is the irreducible Yvec-specific part.
- Build: lake build DLNFibre.DLN.RLCT.Skeleton GREEN (2669 jobs). 5 sorries (4 contract + 1 band).

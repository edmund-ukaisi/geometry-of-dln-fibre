# CORRECTION to g226 — (3,2,3) is 2 branch nodes (joint-vertex schurState), NOT "3 nodes / iterated 3→2→1" (pp-hall, 2026-06-23)

**fm3's decl-check (against the banked schurState) caught a node-count error in g226.** g226 read the (3,2,3)
layer-1 drop `3→1` as "iterated `3→2→1`, TWO C5-partial steps" (3 divisor nodes total). **That was wrong.**

**The banked `schurState` is JOINT-VERTEX:** it decrements idx-0 AND idx-1 by 1 EACH per node (a single rank-1
Schur peel touches BOTH pivot vertices simultaneously). So `(3,2,3) → (2,1,3)` is ONE node (`M_0: 3→2` AND
`M_1: 2→1` jointly), not two. The recursion is:
    (3,2,3) [BRANCH] → (2,1,3) [BRANCH] → (1,0,3) [TERMINAL, minAdm=0, ∃M_s=0, ⊤]
= **2 BRANCH nodes** + the `(1,0,3)` ⊤ terminal (verified `g238_323_recursion.py` against the live schurState).

**What was right (unchanged):** the codims are ROOT-ANCHORED `[5,6]` (`Mval((3,2,3),(1,0))=5=minAdm` the
achiever, `Mval((3,2,3),(0,0))=6`); `foldDivisors → ⨅ = 5/2 = lambdaCore(3,2,3)`. The achiever value, the
root-anchoring (g207/g214), and the C≥/C=∃ are all correct. **Only the node-count / iteration-reading was
off** — g226 read the per-LAYER rank drop (`3→1` = two rank-units at layer 1) instead of the joint-vertex
`schurState` peel (idx 0,1 each `−1` per node).

**The lesson (same class as the pp-r1realize C1-node-count flag, g224):** the LIVE banked `schurState` def is
authoritative over the abstract per-layer reading. When the per-node count matters (the formaliser's node
count + per-node ΣM-drop), trust the joint-vertex `schurState` (`drop = if s≤1 then 1 else 0`), not the
per-layer rank-drop intuition. g226's `[5,6]` codims + the `5/2` value stand; the "3 nodes" is corrected to
2. (3,2,3) = 2 branch nodes, decl-grounded.

# Thread 22 — L6 degeneration design: box-move family + generation induction [pen-and-paper, 2026-06-19]

## L6.1 box-move family — CERTIFIED (sympy-exact, 3 instances)
Move (index cond, nest unifies split): for `a < c ≤ b+1 ≤ e`, `M_{[a,e]} ⊕ M_{[c,b]} ⇝ M_{[a,b]} ⊕ M_{[c,e]}`
(`M_{[c,b]}:=0` when `c=b+1` = split). Closed-form rank drop `r_{ij} − r'_{ij} = [a≤i<c]·[b<j≤e]` (drop
rectangle `D=[a,c−1]×[b+1,e]`), dim vector preserved. **Family `F(t)`:** keep edge maps identity along strands,
perturb the single recombination arrow by `[t,1]` (split: scalar `t` on the cut arrow). `t≠0`: `rankPattern F(t)`
= upstairs at every cell ⟹ same orbit ⟹ `canonicalCoord F(t) ∈ O_M`; `t=0`: downstairs; L6.0 ⟹ downstairs ∈
`closure(O_M)`. Verified: `M_{[0,2]}⊕M_{[1,1]}⇝M_{[0,1]}⊕M_{[1,2]}` /d=(1,2,1); split `M_{[0,2]}⇝M_{[0,1]}⊕M_{[2,2]}`;
nested 4-vertex `M_{[0,3]}⊕M_{[1,2]}⇝M_{[0,2]}⊕M_{[1,3]}`. **Formaliser note:** `F(t)` at `t≠0` is NOT a `dirSum`
(perturbed arrow breaks block-diagonality) — prove "rankPattern F(t)=upstairs" via an explicit base change
`F(t) → upstairs dirSum`, not block-rank additivity.

## L6.2 generation — K1 FIRES (scoped): cover-classification sub-library, NOT a diff-induction
Clean: measure `Φ(r;s)=Σ_{i<j}(r_{ij}−s_{ij})`, a box move with `D ⊆ supp(r−s)` gives `s≤r'<r`, `Φ`↓. The
**move-existence** step (`s<r ⟹ ∃ box move with D ⊆ supp(r−s)`) is the crux and is NOT readable off the
multiplicity array — exhaustive stress-test (rank-exact, d=(2,2,2,2,2,2) 450 orbits, (1,2,3,3,2,1) 522 orbits):
single-cell drops FAIL (need both `m_{p,q}≥1` and `m_{p+1,q-1}≥1`), naive rules overshoot, moves are genuine
RECTANGLES (sizes 2,3,4,6). Correct rule exists (smallest `D ⊆ supp(r−s)`, or: maximal `u∈[s,r)`, cover `r⋗u` is a
linked move). Proving the move-list NONEMPTY for every `s<r` = Abeasis–Del Fra **cover-classification** (covers =
linked box moves; lace/multisegment in array language). **Sizing: L6.2 = 2–3 module combinatorial sub-library.**
Codex convergent (same move, drop formula, measure, and "move-existence = the lace cover theorem" verdict).

## Small-poset check PASSED
d=(2,2,2): 10 realizable orbits, 13 covers, every cover = single box move. d=(1,2,1): 5 orbits. Box move generates
the whole order on every tested poset; only the uniform CHOICE (cover-classification) is the obstruction.

## Route for L6.2 (Codex's clean packaging)
maximal `u ∈ [s,r)` + cover-classification: (a) covers of the rank poset = linked box moves (the lace cover theorem
in array language — the bulk), (b) `r` covers some `u ≥ s`. Cites: Abeasis–Del Fra (Boll. UMI 1980 = Thm 3.8);
Riedtmann–Zwara; KMS. Codex artefacts: `codex/genrule-{prompt,answer}.md`.

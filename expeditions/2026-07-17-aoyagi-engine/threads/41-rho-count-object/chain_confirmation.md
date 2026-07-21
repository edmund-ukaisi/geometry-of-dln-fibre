# Thread-41 — CHAIN-reading confirmation (pnp, decorrelated; the elder-mandated gate for P6.2's UPPER)

Follow-on to `certificate.md`. Charge: confirm/refute that ρ = max CHAIN of binding minimisers (seat-E's
de-risk finding), correcting my earlier "max antichain" speculation. Run from scratch (my own enumeration)
before reading seat-E's battery in detail. Battery: `chain_battery.py` (EXIT 0). No Lean.

## VERDICT: CONFIRM. ρ = max-CHAIN of the binding-minimiser poset = a(ℓ−a)+1. My antichain speculation is REFUTED (it was the Dilworth dual).

### Confirmed facts (EXIT 0; exact; 993 cores L∈{2,3,4} + 5 ground truths + the [2,2,2,2,2] witness)
- **(A) Per-branch CHAIN.** On EVERY root-to-leaf branch, the binding (t̃=0, exp=minAdm) divisor profiles
  present are pairwise componentwise-comparable — a chain. (0 non-chain leaves in 993 cores.) Incomparable
  binding profiles cannot co-occur in one chart, so antichains are irrelevant to ρ.
- **(B) ρ = max-chain = max-crossing = a(ℓ−a)+1**, both directions, every core + all five ground truths
  ((2,2,2)→1, (3,3,4)→1, (2,2,3,2)→1, (2,2,2,2)→3, (2,1,2)→2). 0 mismatches.
- **(C) The antichain reading is WRONG.** [2,2,2,2,2]: max-chain=5=a(ℓ−a)+1 but max-antichain=2; [2,2,2,2]:
  max-antichain=1 ≠ 3. My thread-41 speculation ("max antichain of co-occurring binding profiles") is the
  Dilworth DUAL of the truth and is refuted. The [2,2,2,2,2] chain is
  (1,0,0,0) ≤ (1,1,0,0) ≤ (2,1,0,0) ≤ (2,1,1,0) ≤ (2,2,1,0); the sixth minimiser (1,1,1,0) is INCOMPARABLE
  to (2,1,0,0), so it breaks any 6-chain (and lives on another branch).

### The mechanism (Lean-facing) — the exponent-accumulation nesting, made precise
- **(D1) Unique bounds.** The binding-minimiser poset has a UNIQUE minimum T̃ and UNIQUE maximum T̃' (the
  Lemma-4 envelope endpoints, "minimum one" / "maximum one", p.25). Universal (993/993).
- **(D2) GRADED by rank.** Every maximal T̃→T̃' chain has the SAME length, exactly a(ℓ−a)+1 (the poset
  height). Universal (993/993). Hence max-chain = height = a(ℓ−a)+1. (This is `min_maximal_chain ==
  max_chain == a(ℓ−a)+1` in the battery.)
- **The grading is by a recursively-defined rank (inversions / Young a×(ℓ−a)-cell count), NOT by profile
  coordinate-sum.** Coord-sum grading FAILS: a cover can jump several units — degenerate widths ([1,1,2,1]:
  T̃=(0,0,0), T̃'=(1,1,0), a single cover of L1-jump 2) and unbalanced widths ([2,2,4,3]: L1(T̃'−T̃)=2 ≠
  a(ℓ−a)=1). So a Lean proof must use the rank/inversion grading, not `∑ tᵢ`. (Codex, decorrelated,
  independently gave the same warning + a unique-bounds-not-graded counterexample.)
- **Why the recursion nests (tree side).** On one branch the binding divisors are born in sequence; each
  Case-1(1) exponent-accumulation step extends the profile monotonically (tail-writes + running-min head),
  so the binding divisors present in any leaf are a chain — the per-branch realisation of a T̃→T̃'
  sub-chain. The atlas as a whole realises the full poset; the deepest/eq-(1)(2) branch realises a maximal
  (height-a(ℓ−a)+1) chain (ATTAINMENT).

### Codex (decorrelated, xhigh; `codex/rho-chain-*.md`)
Fired blind. Independently: ρ is "chain-type, not antichain-type … incomparable profiles cannot occur
together in any chart, so Dilworth duality is wrong here." Warned that unique bounds do NOT imply graded
(gave a counterexample) and that "coordinate-sum is a rank only if every cover increases the sum by exactly
1; sparse profile posets can have covers that jump several units." Exact match to the battery's findings.

## Consequence for P6.2 (seat-E may Lean-build)
The UPPER lemma is: **the binding-minimiser poset is graded of height a(ℓ−a)+1** (⟹ max-chain = a(ℓ−a)+1),
with ATTAINMENT the eq-(1)/(2) maximal chain. This is a poset/combinatorics statement over the abstract
`bindingMinimisers ℓ a` (tight lattice by hypothesis, 1 ≤ a ≤ ℓ), decorrelated from the tree. The grading
rank is the inversion/Young-cell count — NOT profile coord-sum (that is the one trap; it fails on
degenerate/unbalanced widths). `certificate.md`'s speculation paragraph amended to this reading; all its
verified facts stand. PASS → seat-E Lean-builds P6.2 on this shape.

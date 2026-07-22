# P6.2 render — Mathlib survey verdict (seat-E, elder-mandated survey pin)

Charge (elder, Option-B ruling): before hand-rolling the a×(ℓ−a) box poset, survey
`Mathlib.Combinatorics.Young.*` + `Order.Height`/`chainHeight` for a usable box structure; build on
it if it exists, else build-it is confirmed. This verdict travels with the render skeleton to the pass.

## VERDICT: EXISTS-WRONG-SHAPE. Hand-rolled `BoxPart` is the right object; build-it confirmed.

### `Mathlib.Combinatorics.Young.YoungDiagram` — exists, WRONG SHAPE for the render
- `structure YoungDiagram := (cells : Finset (ℕ × ℕ)) (isLowerSet …)` — the FULL/unbounded diagram
  type over `ℕ × ℕ`. `PartialOrder` via `⊆` on cells; `YoungDiagram.card = cells.card` (= my `rankBP`).
- **No `Fintype YoungDiagram`** (the type is infinite — all diagrams); **no box-bounded / a×(ℓ−a)
  rectangle sub-type or Finset**.
- **No `Set.chainHeight`/`IsChain` lemmas on `YoungDiagram`** anywhere in the file.
- `rowLens : List ℕ` is `SortedGE` and **strictly positive** (zero rows dropped) ⟹ variable length;
  bridging to a FIXED-dimension `Fin a → ℕ` box tuple (with trailing zeros allowed) is extra plumbing
  with **no chainHeight payoff** (the lemma I need does not exist on `YoungDiagram`).
- Verdict: using it means building the box-restriction + a `Fintype` + the `rowLen ↔ tuple` bridge +
  the chainHeight proof anyway — strictly MORE work for the same theorem.

### `Finset.powersetCard a (univ : Finset (Fin ℓ))` — the a-subsets exist, WRONG ORDER
- Gives the a-subsets as a `Finset` (`|·| = C(ℓ,a)`, matching the poset's cardinality), BUT under the
  Boolean `⊆` order — NOT the dominance/Gale order (componentwise on sorted elements) whose chain
  height is `a(ℓ−a)+1`. The order I need is absent; defining it + its chainHeight is the same work.

### `Mathlib.Order.Height` — the PRIMITIVES exist and ARE used (correct level of reuse)
- No rank/strict-mono ⟹ chainHeight lemma, and no "graded ⟹ chainHeight" lemma. Available:
  `chainHeight_eq_iSup`, `encard_le_chainHeight_of_isChain`, `chainHeight_mono`,
  `chainHeight_eq_of_relEmbedding`, `Set.InjOn.encard_image`, `Set.encard_coe_eq_coe_finsetCard`,
  `Nat.card_Iic`, `Finset.card_range`.
- The render's UPPER (`chainHeight_eq_iSup` + `iSup_le` + `InjOn.encard_image`) and ATTAINMENT
  (`encard_le_chainHeight_of_isChain` + `InjOn.encard_image` + `Nat.card_Iic`) are BUILT ON these
  primitives — the right level of Mathlib reuse; only the *object* (`BoxPart`) is hand-rolled.

### Conclusion
`BoxPart ℓ a := {f : Fin a → ℕ | (∀ i, f i ≤ ℓ − a) ∧ Antitone f}` (Pi pointwise order) is the
correct, minimal shape: fixed-dimension box tuple, cell-count rank = `∑` = coordinate sum (trap-free
in box coordinates), and `chainHeight (BoxPart ℓ a) (· < ·) = a(ℓ−a)+1` is **already PROVED**
sorry-free / axiom-clean, unconditional, on the Mathlib `Order.Height` primitives. Building on
`YoungDiagram`/`powersetCard` would be strictly more work for the identical result. The theorem is
the citable standalone object; an a-subset or `YoungDiagram`-bridge framing, if wanted for citation,
is an ADDITIVE corollary (`powersetCard ≃ BoxPart` via sorted-subset ↔ antitone tuple), not blocking.

**build-it CONFIRMED** (detail-at-scale, multi-tide accepted). Survey run 2026-07-22.

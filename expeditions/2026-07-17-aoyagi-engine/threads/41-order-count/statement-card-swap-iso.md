# Statement card — Object E / P6.2 Tier-3, obligation (a)+(b): the one-swap order-iso

Seat: seat-Eswap. Branch `expedition/aoyagi-engine-Eswap`. Module
`lean/DLNFibre/DLN/Aoyagi/OrderRealizeSwap.lean` (@ `abe9e8e55`).

Discharges the frozen sorried `swapBinding_orderIso` in `OrderRealize.lean` (obligation (a)+(b) of the
P6.2 Tier-3 realization iso). Delivered under the name `swapBinding_orderIso_impl` (distinct name to
avoid a clash; seat-E wires the discharge — see integration note). Imports `DLN.Aoyagi.OrderRealize`
only (reuses its floor: `bindingSet`, `Adm`/`Mval`/`admBound`, `swapWidths`, `swapR`, `swapProfile`,
`swapR_swapR`, `swapWidths_swapWidths`, `swapR_F_invariant`).

---

> **Claim (a)+(b) — one adjacent-width-swap is an order-iso of the binding poset.** For any width
> vector `M : Fin (L+1) → ℕ`, any `k : Fin L`, and `hpos : ∀ s, 0 < M s`, the poset of `Mval`-minimising
> admissible profiles is order-isomorphic under the swapped widths:
> `Nonempty (↥(bindingSet M) ≃o ↥(bindingSet (swapWidths k M)))`.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.swapBinding_orderIso_impl` (`…/OrderRealizeSwap.lean` @ `abe9e8e55`).
> - **Gloss.** `bindingSet M = {T ∈ Adm M : Mval M T = minAdm M}`, ordered pointwise (`Fin L → ℕ`).
>   `swapWidths k M = M ∘ Equiv.swap k.castSucc k.succ` swaps widths `M k, M (k+1)`. The iso is the
>   value-preserving `swapProfile M k` transport (Codex's `swapR` on the coupled coordinate `k−1`), with
>   its own transport as inverse (via the two involutivity lemmas).
> - **Proved.** Sorry-free, build-confirmed. `#print axioms swapBinding_orderIso_impl =
>   [propext, Classical.choice, Quot.sound]` (also verified for `swapR_mono_of_min`,
>   `swapProfile_Mval_eq`, `bindingSet_local_min`). No cited axiom; no `native_decide`.
> - **Hypotheses.** `hpos : ∀ s, 0 < M s` is carried (frozen statement); the proof does NOT use it
>   — the iso holds for the `k = 0` degenerate case (transport = identity, `bindingSet` literally
>   fixed) and for `k ≥ 1` from the minimiser machinery, neither of which reads `hpos`. Weakest-hyp
>   note for the controller: `hpos` is droppable, but kept to match the frozen `OrderRealize` signature.
> - **Cited.** none.
> - **Status.** sorry-free, axiom-clean.

## Load-bearing sub-lemmas (all sorry-free, same module/commit)

- `swapR_le_B_of_min` — adm-preservation crux: on a binding profile the swap image stays `≤ B`
  (reflection `B<A` forces `X = P` via the single neighbour inequality `F(X) ≤ F(X+1)`; `A≤B` needs no
  minimality). PURE `swapR` + minimiser fact.
- `swapR_mono_of_min` — **the load-bearing hazard**: coupled monotonicity of `swapR` under
  `(P,X,Q) ≤ (P',X',Q')` given both minimiser hypotheses (atomic `swapR`-in-`X` monotonicity is FALSE).
  Codex-corroborated asymmetric-collapse route (`A≤B ⟹ X'=Q'`; `B<A ⟹ X=P`; no case needs both).
- `swapProfile_Mval_eq` — value preservation (reuses `swapR_F_invariant` + the `Mval` two-term split
  `Mval_diff_offdiag`).
- `bindingSet_local_min` — extracts the minimiser hypothesis (perturb `k−1`, stays admissible, `Mval`
  shifts by the `swapFℤ`-difference; the minimum pins it).
- `swapProfile_mem_Adm`, `swapProfile_swapProfile` (involution), `minAdm_swapWidths_eq`,
  `swapProfile_mem_bindingSet`, `swapProfile_mono`; `k = 0` case:
  `Adm_swapWidths_zero`/`Mval_swapWidths_zero`/`minAdm_swapWidths_zero`.

## Numeric kill-record (all EXIT 0)

- `swap-endpoint-battery.py` — range, `Y≤B`, value-pres, involution, bijection, both-direction
  monotonicity over all positive-width `M`, `L ≤ 5` (1308 tuples).
- `swap-reflect-probe.py` — reflection branch structure (on binding: `A≤B` no-min; `B<A ⟹ X=P`).
- `swap-mono-abstract.py` — the pure `swapR`+minimiser monotonicity, 0 fails incl. all 150 tie cases.

## Controller / seat-E integration note

`OrderRealizeSwap.lean` imports `OrderRealize.lean` (for the floor); therefore `OrderRealize` cannot
import it back (cycle). To discharge the frozen `swapBinding_orderIso`: either (A) delete the sorried
`swapBinding_orderIso` from `OrderRealize` and have the (c) transport call
`OrderRealizeSwap.swapBinding_orderIso_impl` directly, or (B) relocate the shared floor below both.
Recommend (A). Wire `OrderRealizeSwap` into the aggregator (single-writer, controller).

**Fidelity points for the reviewer.** (1) Does `swapBinding_orderIso_impl`'s statement match the frozen
`OrderRealize.swapBinding_orderIso` verbatim (same `Nonempty (↥(bindingSet M) ≃o ↥(bindingSet
(swapWidths k M)))`, same `hpos`)? (2) Is `bindingSet`/`swapProfile`/`swapWidths` as reused the genuine
`OrderRealize` floor (not re-defined)? (3) Is the `≃o` a real order-iso (both `map_rel_iff'` directions),
not a bare bijection? (4) `#print axioms` clean, no cited axiom smuggled.

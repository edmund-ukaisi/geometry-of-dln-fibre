# (c) `bindingSet_transport_sorted` — DESIGN VERDICT (seat-E)

Obligation (c): `Nonempty (↥(bindingSet M) ≃o ↥(bindingSet (sortedWidths M)))`, `sortedWidths M =
M ∘ Tuple.sort M`. Method: banked fork + decorrelated Codex (xhigh, `codex/transport-c-answer.md`)
+ numeric check (`g-transport-c.py`, 579/579). DESIGN ONLY (build gated on (a)+(b) or sorted-box
landing, per controller).

## VERDICT: submonoid-closure via `Equiv.Perm.mclosure_swap_castSucc_succ` — NOT inversion recursion.

My banked fork was (A) adjacent-decomposition composition vs (B) one-shot permutation transport.
Codex red-teamed my working design (well-founded recursion on inversion count) as **viable but
unnecessarily expensive** — formalising the inversion count + the one-step decrease is a real hidden
cost (index-heavy, no Mathlib value-tuple inversion API). It surfaced the clean route, which is a
sharper form of (A):

**Route (verified present at v4.29):**
- `Equiv.Perm.mclosure_swap_castSucc_succ (L) : Submonoid.closure (Set.range (fun i : Fin L ↦
  Equiv.swap i.castSucc i.succ)) = ⊤` (`Mathlib/GroupTheory/Perm/Sign.lean:125`) — adjacent
  transpositions generate `Perm (Fin (L+1))`.
- Define the submonoid `H : Submonoid (Perm (Fin (L+1)))` with carrier
  `{σ | ∀ M, (∀ s, 0 < M s) → Nonempty (↥(bindingSet M) ≃o ↥(bindingSet (M ∘ σ)))}`:
  - `one_mem`: `σ = 1` ⟹ `bindingSet (M ∘ 1) = bindingSet M`, `OrderIso.refl`.
  - `mul_mem` (σ,τ): `bindingSet M ≃o bindingSet (M∘σ)` [σ at M] `.trans` `bindingSet (M∘σ) ≃o
    bindingSet ((M∘σ)∘τ)` [τ at `M∘σ`, positive via `fun s ↦ hpos (σ s)`]; `(M∘σ)∘τ = M∘(σ*τ)`
    (`Equiv.Perm.coe_mul`).
- Each generator `swap i.castSucc i.succ ∈ H`: `bindingSet (M ∘ swap i.castSucc i.succ) =
  bindingSet (swapWidths i M)` **by rfl** (`swapWidths i M := M ∘ Equiv.swap i.castSucc i.succ`),
  so `swapBinding_orderIso M i` (seat-Eswap) supplies it.
- `Submonoid.closure_le.mpr (generators ⊆ H)` + `mclosure_swap_castSucc_succ` ⟹ `H = ⊤`, so
  `Tuple.sort M ∈ H`. Apply at `σ = Tuple.sort M`:
  `bindingSet M ≃o bindingSet (M ∘ Tuple.sort M) = bindingSet (sortedWidths M)` (rfl on `sortedWidths`).

**Sorted endpoint:** no "same multiset" argument — the def unfolds `sortedWidths M = M ∘ Tuple.sort M`
directly (rfl). (`Tuple.comp_perm_comp_sort_eq_comp_sort` is available if a re-sort normalisation is
needed downstream.) `L = 0` needs no special branch (closure covers it).

## Depends on / hazards
- DEPENDS: `swapBinding_orderIso` (seat-Eswap, in flight) — the ONLY external dependency. Everything
  else is Mathlib + defeq.
- k=0 generator (`swap 0.castSucc 0.succ` = swap widths 0,1): `swapProfile` is the identity there
  (profile unchanged; `admBound₀ = min(M⁰,M¹)` and `Mval`'s first term are symmetric in `M⁰,M¹`), so
  `swapBinding_orderIso M 0` is the profile-identity iso — seat-Eswap's k=0 branch (flagged to it).
- Fin/type hazards (Codex §3): `Fin (L+1)` fixed (no index-family drift); positivity under perm
  `fun s ↦ hpos (σ s)`; keep intermediate widths syntactically `M ∘ σ` / `swapWidths i M`; mul
  orientation via `Equiv.Perm.coe_mul`.

## Effort + numeric warrant
~40 LoC (the submonoid + closure application) — far below the inversion-recursion estimate; Codex
reports it type-checked the skeleton in-worktree. Numeric warrant: `g-transport-c.py` verifies the
underlying claim (adjacent-swap transport composes to an order-iso `bindingSet(M) ≃o
bindingSet(sorted M)` both directions, inversions −1 per swap) over 579 positive-width tuples, EXIT 0.

## Build-resourcing (controller decides at the handoff-profile test)
(c) is now fully designed + Mathlib-verified + numeric-checked, DEPENDING only on `swapBinding_orderIso`.
When (a)+(b) lands, (c) is a ~40-LoC consumer — small enough to build myself as integrator, or fold
into the seat-Eswap handoff. Recommend: build myself post-(a)+(b) (it is integration-adjacent).

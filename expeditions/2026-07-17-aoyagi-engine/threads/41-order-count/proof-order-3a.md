# 3a construction — proof-order for the four frontier obligations (post-pass warm-start)

Optional productive-hold note (seat-E). Statement-locked pending the elder pass; this is proof-order
+ Mathlib-machinery scouting only, no statement changes. Obligations live in
`lean/DLNFibre/DLN/Aoyagi/OrderRealize.lean`; the kill-record is `g-enc-adjacent-swap.py` (EXIT 0).

Dependency graph of the headline `bindingSet_orderIso_boxPart` (already discharged, non-sorried):
```
  bindingSet_orderIso_boxPart
    ├── bindingSet_transport_sorted           (c)  ── swapBinding_orderIso  (a)+(b)
    └── bindingSet_sorted_orderIso_boxPart          ── residueA_le_ell       (d, well-formedness)
```

## Recommended proof-order (easiest/standalone → hardest/composed)

1. **`residueA_le_ell` (d)** — ✅ DONE (commit f7c3f0a28), axiom-clean. Hyp is `0 < ell M 0` (NOT
   `hpos` — the elder's hpos-check fired negative; positive widths never enter the ceiling arithmetic).
   Proof: reuse `ClosedForm`'s `hresval` reasoning at `r = 0` (`residueA = S − (⌈S/ℓ⌉−1)·ℓ ∈
   {S mod ℓ, ℓ}`, both `≤ ℓ`, via `Int.ediv_emod_unique` + `nlinarith`), then `Int.toNat_le` reduces
   `.toNat ≤ ell` to `residueA ≤ (ell : ℤ)` directly (no separate `0 ≤ residueA` needed).

2. **`bindingSet_sorted_orderIso_boxPart`** — SECOND (the mathematical heart; tackle while fresh).
   The actual enc/dec on sorted widths. Sub-structure:
   - `encSorted (D U) : Fin a → ℕ` — increments `eᵢ↑`, active steps `xᵢ = eᵢ↑ + D_{i+1}`, a-subset
     `A = {i : xᵢ = C}`, reversed gaps `Fin.rev`. Real def.
   - `decSorted` — the inverse (Codex part 2): `eᵢ↑ = C − D_{i+1}` (i∈A) / `C−1−D_{i+1}` (else),
     `Uc = D₀ − Σ_{i≤c} eᵢ↑`. Real def.
   - The **a-subset ↔ box** step is standard: `A = {p₀<…<p_{a−1}}`, box `enc i = p_{a−1−i} − (a−1−i)`.
     ✅ API CONFIRMED (v4.29, `Data/Finset/Sort.lean`): `Finset.orderEmbOfFin (s) (h : s.card = a) :
     Fin a ↪o α` with `orderEmbOfFin_apply : s.orderEmbOfFin h i = s.sort[i]` gives `pᵢ` (the i-th
     element of `A` in order); `orderIsoOfFin : Fin a ≃o s`. Build `A : Finset (Fin ℓ)` via
     `Finset.filter (xᵢ = C)`, discharge `A.card = a` from `residueA_le_ell` + the active-step count.
     `Fin.rev`. This is where I'd first pin an `example` block against `orderIsoOfFin`.
   - Assemble via `OrderIso.ofHomInv` (fwd `encSorted`, inv `decSorted`, two round-trips) OR `toEquiv`
     + `map_rel_iff'`. **Reverse `map_rel_iff` is the hazard** (order-reflection; coord-sum fails it).
   - Uses (d) for the `BoxPart` bound `f ≤ ℓ−a` (via `xᵢ ∈ {C−1,C}` and the gap ≤ ℓ−a).

3. **`swapBinding_orderIso` (a)+(b)** — THIRD. Atomic one-swap iso, self-contained (needs neither
   (c) nor (2)). Sub-structure:
   - `swapR` range + involution: pure ℕ, case-split on the three R branches, `omega` per branch.
     (Range `Q ≤ R ≤ min P A` needed for admissibility preservation; involution `R∘R = id` on range.)
   - one-swap admissibility preservation: profile bookkeeping via `Function.update` at index `k−1`;
     `Fin` index arithmetic (`k.castSucc`/`k.succ`); `Mval` invariance under the swap (the
     value-preservation — `(P−X+A)²+(X−Q+B)²` is symmetric under translate/reflect).
   - the coupled monotonicity: `T ≤ T'` ⟹ transported `≤` — the one non-atomic step (recall atomic
     `swapR`-in-`X` mono is FALSE; the coupling `P,X,Q` move together is load-bearing).

4. **`bindingSet_transport_sorted` (c)** — LAST (needs (a)+(b)); the likely-hardest for FRICTION,
   not depth. Compose the adjacent-swap isos into the full sort. **The friction** (controller-flagged):
   - `shiftedSorted _ 0 = M ∘ Tuple.sort M`; `Tuple.sort` is a single permutation, NOT a sequence of
     adjacent swaps. To reuse `swapBinding_orderIso` (adjacent only) I must decompose `Tuple.sort M`'s
     permutation into adjacent transpositions and compose the isos along that decomposition.
   - Mathlib leads to pin FIRST (before committing): does v4.29 give "every `Equiv.Perm (Fin n)` is a
     product of adjacent transpositions" cleanly? Candidates: `Equiv.Perm.swap`-generation lemmas,
     `List.Sorted` bubble-sort, `Tuple.sort` API (`Tuple.sort_sorted`, `Tuple.self_comp_sort`).
   - **DESIGN FORK (for the tide, surface to elder if it walls):** if adjacent-decomposition is
     painful, an ALTERNATIVE (c): prove the transport iso for the WHOLE sort at once via a direct
     bijection using the LANDED permutation-invariance (`(C,θ)` perm-invariance) + `Mval`-value
     transport, sidestepping adjacent swaps entirely. Codex's route is adjacent-swap; this alt trades
     `swapBinding_orderIso` reuse for a one-shot permutation argument. Decide after pinning the
     adjacent-decomposition Mathlib support.

## Cross-cutting Mathlib to pre-pin (example blocks) once the pass lands
- `OrderIso.ofHomInv`, `OrderIso.trans`, `OrderIso.toRelIsoLT` (already used in `chainHeight_eq_of_orderIso`).
- `Finset.orderEmbOfFin` / `orderIsoOfFin` + `Fin.rev` (the a-subset↔box bijection).
- `Tuple.sort` API + adjacent-transposition generation (the (c) friction — pin BEFORE building (c)).
- `Function.update` + `Equiv.swap` Fin-index lemmas (the one-swap profile bookkeeping).

## Risk ranking
- Highest FRICTION: (c) transport — the `Tuple.sort` ↔ adjacent-swap bridge (pin Mathlib first; fork ready).
- Highest DEPTH: (2) sorted box iso — the reverse `map_rel_iff` (order-reflection) is the real content.
- Low: (d) arithmetic; (a)+(b) range/involution (omega), with the coupled-mono the one subtle piece.

# Thread 03 — Phase G (the `Σ̄^r` stratification) — statement card

Module: `lean/DLNFibre/Core/SigmaStratification.lean` (171 LoC, sorry-free, axiom-clean).
Build: whole `DLNFibre` library green (3013 jobs); `scripts/sorries` = 0.
Axioms (all six headlines, via `#print axioms`): `[propext, Classical.choice, Quot.sound]`.

---

## Headline (G2) — the orbit stratification of `Σ̄^r`

> **Claim.** The closed rank-`≤ r` product locus `Σ̄^r = {A | rank (mult A) ≤ r}` is the union of the
> orbit closures `Ō_M = orbitRankLocus M` over all composable matrix tuples `M` whose **corner**
> (product rank `rank (mult M)`) is `≤ r` (Le Halleur–Rimányi 2024, Cor 4.4 stratification, the `≤ r`
> closure convention — the genuine Zariski closure of `Σ^r`).
>
> - **Lean:** `DLNFibre.Core.productRankLocusLE_eq_iUnion_orbitRankLocus`
>   (`lean/DLNFibre/Core/SigmaStratification.lean` @ `c0cae1a`)
> - **Gloss.** For a fixed dimension vector `d : Fin (N+1) → ℕ` over a field `k`, as sets of tuples,
>   `productRankLocusLE d r = ⋃ (M : Tuple d) (_ : (mult d M).rank ≤ r), orbitRankLocus M`.
>   `orbitRankLocus M = {A | ∀ i j (h:i≤j), rankPattern d A i j h ≤ rankPattern d M i j h}` is the
>   Abeasis–Del Fra determinantal orbit closure (Thm 3.8, proved in `Core.OrbitClosure`).
> - **Proved.** The set equality, over `[Field k]`, for every `r : ℕ` and every `d`. `⊇` is the
>   per-orbit inclusion `orbitRankLocus_subset_productRankLocusLE` (corner-entry monotonicity of the
>   rank-pattern order + the G1 corner link); `⊆` places each `A` in its own orbit closure `Ō_A`
>   (`self_mem_orbitRankLocus`, corner `= rank (mult A) ≤ r`).
> - **Assumed.** `[Field k]` only (the module's uniform class — needed by the Gabriel brick below; the
>   union equality and the per-orbit inclusion alone use only the rank-pattern order). NO
>   `[IsAlgClosed k]` / `[CharZero k]`: this is a SET equality of determinantal loci, not a codimension
>   statement.
> - **Cited.** none.
> - **Deferred.** The TOPOLOGY (irreducible components = maximal `Ō_M`) and the count `θ` — Phase G3 / θ,
>   which consume this set equality + the collapse lemma below. The aggregate-codimension reading
>   (`cCodim` = geometric codim of `Σ̄^r`) is also downstream.
> - **Status.** sorry-free (pending reviewer fidelity check).

### Index form (handed to G3)

Headline is the **all-`M` union** (Form A); also exported is the **membership iff**
`mem_productRankLocusLE_iff_exists_mem_orbitRankLocus` (Form B,
`A ∈ Σ̄^r ↔ ∃ M, (mult d M).rank ≤ r ∧ A ∈ orbitRankLocus M`). Codex (xhigh, decorrelated, see
`codex/index-form-{prompt,answer}.md`) converged on Form A as the headline + Form B as the
destructuring form, with the finiteness/maximality bookkeeping **deferred to G3** (introduce the
canonical finite index there), and the rank-pattern collapse delivered here as the brick that lets G3
pass from the infinite-looking union to a finite family of distinct closed sets.

---

## Supporting bricks (same module, same SHA)

> **G1 — corner link.** `corner_rankPattern_eq_rank`:
> `rankPattern d A 0 (Fin.last N) (Fin.zero_le _) = (mult d A).rank`.
> The full product is the `[0, N]` interval sub-product (`Submult.mult_eq_submult`); its rank is the
> corner rank-pattern entry by definition. `[Field k]`. (~3 LoC.)

> **Gabriel set-membership.** `exists_orbitRankLocus_mem_rankPattern_eq`:
> `∀ A, ∃ M, (∀ i j h, rankPattern d A i j h = rankPattern d M i j h) ∧ A ∈ orbitRankLocus M`.
> Every tuple lies in the orbit closure of a Gabriel **normal form** `M` (a reindexed interval direct
> sum `⊕ M_{ab}`, `Orbit.baseChange_normalForm`) with the *same* rank pattern. The brief's flagged
> deliverable; the bare set equality does NOT need it (it takes `M := A`), so it is a separate named
> brick — the input a later thread uses to replace arbitrary tuples by canonical Kostant
> representatives. `[Field k]` (the normal-form existence needs a field).

> **Per-orbit inclusion (`⊇`).** `orbitRankLocus_subset_productRankLocusLE`:
> `(mult d M).rank ≤ r → orbitRankLocus M ⊆ productRankLocusLE d r`. Corner-entry monotonicity. `[Field k]`.

> **Rank-pattern collapse (for the finite family).** `orbitRankLocus_eq_of_rankPattern_eq`:
> equal rank patterns `⟹ orbitRankLocus M = orbitRankLocus M'`. The lemma G3 uses to collapse the
> all-`M` union onto the finite set of distinct orbit closures. `[Field k]`.

> **Membership iff (Form B).** `mem_productRankLocusLE_iff_exists_mem_orbitRankLocus`. `[Field k]`.

Non-vacuity witness in-file: `(2,2,2)` over `ℚ`, the tuple `A₁ = [[1,2],[0,1]]`, `A₂ = [[1,0],[3,1]]`
with `mult = [[1,2],[3,7]]` (rank `≤ 2`), shown lying in `Σ̄^2` via the stratification and in its own
orbit closure via the Gabriel brick.

# Statement card — L6.1 box-move degeneration (thread 23)

## Engine (general in the dimension vector `d`)

> **Claim.** A one-parameter polynomial family on `Tuple d` whose `t = 0` limit is `D` and whose
> `t ≠ 0` points lie in the `G_d`-orbit of `U` witnesses that `D`'s flattening is in the Zariski
> closure of `orbit(U)`.
>
> - **Lean:** `DLNFibre.Core.mem_zeroLocus_vanishingIdeal_orbitSet_of_polynomialFamily`
>   (`lean/DLNFibre/Core/BoxMoveDegeneration.lean` @ `31ec681`)
> - **Gloss.** Over an infinite field `k`, for tuples `U D : Tuple d` and a polynomial-coefficient
>   tuple `Fpoly : Tuple (Polynomial k) d`: if `tupleEval Fpoly 0 = D` and for every `t ≠ 0` there is
>   a base change `P` with `P • U = tupleEval Fpoly t`, then
>   `canonicalCoord d D ∈ zeroLocus (vanishingIdeal (orbitSet U))`. Here `tupleEval Fpoly t` is the
>   entrywise `eval`-at-`t` (`(Fpoly i).map (eval t)`), `orbitSet U = canonicalCoord '' {A | ∃ P, P•U=A}`.
> - **Proved.** The full implication, unconditionally, for any `d`, any `U,D,Fpoly` satisfying the two
>   hypotheses. Consumes L6.0 (`curvePoint_zero_mem_zeroLocus_vanishingIdeal`) — the only field-theory
>   input is `[Infinite k]` (from L6.0).
> - **Assumed.** The two hypotheses (limit = `D`; `t ≠ 0` orbit membership) are the family's burden,
>   supplied per degeneration.
> - **Cited.** none (L6.0 is landed in-repo, not external).
> - **Deferred.** none for the engine.
> - **Scope (caveat next to claim).** The closure is relative to **`k`-points** (`zeroLocus k …`):
>   over an algebraically closed field one reads it at `IsAlgClosed k` (which is `Infinite`). The
>   conclusion is membership of one point in one orbit's closure — NOT `orbit(D) ⊆ closure(orbit(U))`
>   nor the rank-locus equality (Thm 3.8).
> - **Status.** sorry-free + reviewed (fidelity PASS-WITH-NOTES, 2026-06-19, @ `b265e6f`); axioms
>   `[propext, Classical.choice, Quot.sound]`.

## Witness (the certified `(1,2,1)` box move `M_{[0,2]} ⊕ M_{[1,1]} ⇝ M_{[0,1]} ⊕ M_{[1,2]}`)

> **Claim.** The downstairs split sum `M_{[0,1]} ⊕ M_{[1,2]}` lies in the Zariski closure of the orbit
> of the upstairs nested sum `M_{[0,2]} ⊕ M_{[1,1]}` over `d = (1,2,1)`.
>
> - **Lean:** `DLNFibre.Core.boxMoveWitness_downstairs_mem_closure`
>   (`lean/DLNFibre/Core/BoxMoveDegeneration.lean` @ `31ec681`)
> - **Gloss.** Over an infinite field, `canonicalCoord boxDim boxMoveWitnessDown ∈ zeroLocus
>   (vanishingIdeal (orbitSet boxMoveWitnessUp))` for the explicit `(1,2,1)` tuples (edge maps
>   upstairs `[[1],[0]]`, `[[1,0]]`; downstairs `[[1],[0]]`, `[[0,1]]`).
> - **Proved.** The closure membership, via the engine instantiated at `boxMoveWitnessFamilyPoly`
>   (cut arrow `[X, C 1]`). The `t ≠ 0` orbit certificate `boxMoveBaseChange_smul` is an explicit
>   base change `P₀ = 1`, `P₁ = [[1,-t⁻¹],[0,1]]`, `P₂ = [t]` proven to satisfy `P • upstairs = F t`.
> - **Assumed.** none beyond `[Field k]`, `[Infinite k]`.
> - **Cited.** none.
> - **Deferred.** none for the witness itself.
> - **Scope (caveat next to claim).** The witness tuples are hand-written explicit matrices; the
>   reviewer confirmed they coincide with the edge maps of `intervalDirectSum [(0,2),(1,1)]` /
>   `[(0,1),(1,2)]` under the natural block layout, so the `M_{[0,2]} ⊕ M_{[1,1]}` naming is faithful
>   — but the module does NOT claim a definitional equality to `intervalDirectSum`. One representative,
>   one orbit, one dimension vector.
> - **Status.** sorry-free + reviewed (fidelity PASS-WITH-NOTES, 2026-06-19, @ `b265e6f`); axioms
>   `[propext, Classical.choice, Quot.sound]`.

## Gap (named, not formalised)

The **general box-move lemma** — the family + base change for arbitrary interval data
`a < c ≤ b+1 ≤ e` and arbitrary `rest` (so that upstairs/downstairs are `intervalDirectSum` of the
box-up / box-down lists appended with `rest`) — is **not formalised**. It plugs into the engine
(supply `Fpoly` and the two hypotheses), but its construction requires: the `foldDim`-transport for
the (equal but syntactically distinct) dimension vectors of the two lists; the perturbed cut arrow
inside the `dirSum` block reindexing over arbitrary `rest`; and the per-vertex base change (with `t⁻¹`
at the overlap `[c,b]` and right-tail `[b+1,e]` vertices). This is the documented `Fin (foldDim …)`
index-reduction friction at `rest`-scale (no `fin_cases` shortcut). Reachable but heavy — left as the
gap above the landed engine + witness. Not sorry-patched.

# Statement card — Object E / P6.2 Tier-3 (3a), SORTED-BOX CORE

Seat: seat-Ecore (lean-formaliser). Branch `expedition/aoyagi-engine-Ecore` (off aoyagi-engine-E).
Module `lean/DLNFibre/DLN/Aoyagi/OrderRealizeSortedBox.lean` @ `d0e24afc7`. This is the LAST factor of
the P6.2 Tier-3 realization order-iso: on **sorted** widths, the binding-minimiser poset ≃o `BoxPart`.
Kill-battery `threads/41-order-count/g-sorted-box-iso.py` (EXIT 0; 256 cores + L≤5/W≤5 sweep, both
order-reflection directions).

---

> **Claim (Tier-3 (3a) headline, sorted case).** For monotone positive widths `D`, the poset of
> `Mval`-minimising admissible profiles is order-isomorphic to the box-partition lattice
> `BoxPart (qipM D) (sbResidueA D).toNat`.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.SortedBox.sortedBox_orderIso`
>   (`lean/DLNFibre/DLN/Aoyagi/OrderRealizeSortedBox.lean` @ `d0e24afc7`)
> - **Gloss.** `Nonempty (↥{T | T ∈ Adm D ∧ Mval D T = (Adm D).inf' (Adm_nonempty D) (Mval D)}`
>   `≃o ↥(BoxPart (qipM D) ((sbResidueA D).toNat)))`, over componentwise `≤` on both sides.
> - **Proved.** Full `≃o` (Equiv + `map_rel_iff'`), both directions of order-reflection. Axiom-clean
>   `[propext, Classical.choice, Quot.sound]` (verified by `#print axioms`).
> - **Assumed.** `hmono : Monotone D`, `hpos : ∀ s, 0 < D s`. (Weakest-sufficient: `hmono` drives the
>   QIP water-filling; `hpos` excludes the zero-width degeneracy. `L = 0`⟺`qipM D = 0` is a separate
>   singleton-singleton branch — both sides have one element.)
> - **Cited.** none.
> - **Deferred.** none (this factor is complete). The full Tier-3 iso composes this with seat-Eswap's
>   swap/transport factor (separate module); the outer `bindingSet_sorted_orderIso_boxPart` (frozen,
>   elder-passed) is discharged by seat-E instantiating this at `D = sortedWidths M`.
> - **Status.** sorry-free.

## Route (name = content)

Reuses the banked QIP water-filling — the pivotal fact is NOT re-derived:
- `binding_qipT_pair` — pivotal fact: on a binding profile the increment vector `eOfT D T` is a
  `Gqip`-minimiser whose `qipT`-coordinates over `qipLow D` are `{0, sgn δ}`-valued with `|δ|` nonzero
  (i.e. active steps ∈ {C−1, C}). Via `MinAdmCCodim.Mval_eq_Gqip`/`eOfT` +
  `CThetaValue.qipMinimiser_support`/`_sumSq`/`sumSq_eq_abs_characterization`.
- `sbCeil_eq`/`sbResidueA_eq` — the two δ-sign bridges (`C = qipRound + [δ>0]`, `a = δ + [δ≤0]·ℓ`);
  confine ALL sign-casing, keeping the rest sign-free.
- `prefix_telescope` — `∑_{j≤c} eOfT = D₀ − T_c` (localised reverse round-trip of `tOfE`).
- `binding_incr_eq`/`binding_profile_formula`/`stepA_card`/`binding_le_iff` — the bindingSet order is
  reverse count-domination on the C-step subsets (`stepA`).
- `boxOf`/`boxOf_mem`/`posOfBox`/`boxOf_boxSubsetOf`/`boxSubsetOf_boxOf` — the a-subset↔box bijection
  (via `Finset.orderEmbOfFin` + `Fin.rev` gaps).
- `countLE_eq`/`posLE_iff_countDom`/`boxOf_le_iff` — the position↔count duality (load-bearing).
- `decProfile`/`decProfile_spec`/`stepA_decProfile` — the inverse: box → binding profile via
  `eOfSupport`+`tOfE` (`Gqip_eOfSupport` ⟹ binding), C-steps recovered as the box subset.
- Assembly: explicit `≃o`; `map_rel_iff'` chains `boxOf_le_iff`+`posLE_iff_countDom`+`binding_le_iff`;
  round-trips via `binding_ext` (profile determinacy) + the subset round-trips.

## Wiring (for seat-E)

`sbCeil`/`sbResidueA` are built to match `ClosedForm.ceilingM`/`residueA M 0`'s formula at `r = 0`;
`qipM (sortedWidths M) = ell M 0` (rfl). Instantiate at `D = sortedWidths M`
(`hmono = Tuple.monotone_sort _`, `hpos` from `hpos`). If the `residueA M 0 = sbResidueA (sortedWidths M)`
coercion fights at integration, an `sbResidueA`-bridge lemma can be added upstream on request.

## Fidelity note (for reviewer)

Name = content check: `sortedBox_orderIso` claims exactly a poset `≃o` between the `Mval`-minimiser
set (over `Adm D`, at the `inf'`) and `BoxPart`. The codomain `(sbResidueA D)` is Aoyagi's residue `a`
on the active prefix, NOT re-derived from a headline. No `rlct`/`θ`-naming; this is chain-height
infrastructure (composes with `Core.OrderChain.chainHeight_boxPart` on the OrderRealize side).

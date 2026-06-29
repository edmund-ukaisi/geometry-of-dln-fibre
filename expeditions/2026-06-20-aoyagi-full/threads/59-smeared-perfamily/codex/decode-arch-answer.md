**1. Verdict**

Use your architecture `(a)+(b)`. Do **not** also build an explicit per-coordinate `if i ∈ coreSet then ... else ...` shear unless the split route fails.

Verified local API: `splitOfCoreSet_core/spec`, `splitOfPartition_symm_apply`, and `flatEquivOf_symm_coord` are exactly the readback tools for this. General Lean fact: an explicit coordinate shear would still need a bridge proof to the measure-preserving split-conjugate shear, and that bridge repeats the same `coreSet`/complement indexing proof you need for decode. At opaque width, that doubles the dependent-`Fin` alignment surface.

Best shape: define `shearM` as the split-conjugate body, then prove two coordinate lemmas:

```lean
shearM_core_coord
shearM_spec_coord
```

These should be readback lemmas through `splitOfPartition_symm_apply` plus `splitOfCoreSet_core/spec`, not an `if` normal form.

One caveat: `measurePreserving_shearM` gives MP for the inline conjugate function; `hemb` still wants an embedding. That should be solved by packaging the same split-conjugate body as a `MeasurableEquiv` or proving embedding from the conjugate equivalences. It does not require an explicit coordinate-if shear.

**2. Biggest Risk**

The biggest risk is the slot bijection `e : Fin N ≃ FlatIdx M` interacting with `coreSet.equivFin` / `coreSetᶜ.equivFin` ordering.

`flatEquivOf_symm_coord` gives coordinates as:

```lean
shearM (R u) (e.symm q)
```

but the split readback lemmas want indices of the form:

```lean
coreSet.equivFin.symm j
coreSetᶜ.equivFin.symm k
```

If those are not definitionally or lemma-aligned, the full decode stalls before the math starts. This is repo-specific inference from the API shape, but the Lean mechanism is general: arbitrary equivalence/enumeration alignment is usually more expensive than the coordinate algebra.

Cheapest probe first:

```lean
-- new probe lemma, not claiming this exists
lemma core_top_slot_readback_probe
  (a : Fin r) (j : Fin (M 2)) :
  shearM coreSet shift (R u)
    (e.symm ⟨⟨(1 : Fin 2), deepWidthEquiv hrs (Sum.inl a)⟩, j⟩)
  =
  (R u) (e.symm ⟨⟨(1 : Fin 2), deepWidthEquiv hrs (Sum.inl a)⟩, j⟩)
    + shift (...) (coreCoord a j)
```

Do not evaluate `shift`, `Λ₀`, or `pivotBlowupOn` yet. This single lemma tests the dangerous bridge: pack slot → flat slot → core block coordinate. If this probe is painful, the full decode will be worse.

**3. Scoping**

Bank in this order:

1. Generic `shearM_core_coord` / `shearM_spec_coord` for the split-conjugate shear. This is reusable and independent of `chartL2Params`.

2. If full opaque `M 2` is too cast-heavy, fix `hc : M 2 = 1` while keeping `r,s,M 0,M 1` opaque. This keeps the real row-split/deepWidth problem but removes the column product/order burden.

3. If that still exceeds the cast budget, carry the decode as a named hypothesis:

```lean
hDecode : ψ (R u) = phiL2 M hrs A0 z HbarUnit Sbot Λ₀
```

Then bank the generic wrapper: `hDecode + routeMCore_phiL2 ⇒ hRate`, plus the box measurability/positivity, radial `R` facts, and the analytic `Λ₀` conditioned bound. That is the reachable ceiling worth preserving without spending days inside one cast swamp.
**Q1. C1 Hard-Pivot**

**FACT.** Yes, C1 is an instance of `Datum`.

Field assignments:

- `nReg = #E`
- regular block: `∑_j E_j²`
- reduced core: choose `G` with  
  `G² = ∑_{i,j} SΓ_{ij}²`
- `flatCore = ∑_j E_j² + ∑_{i,j} (b_i E_j + SΓ_{ij})²`
- constants:
  ```text
  c₁ = (2(1 + T²))⁻¹
  c₂ = 2 + 2T²
  ```

Writing `L_b(E)_{ij} = b_i E_j`, we have `‖L_b E‖² ≤ T² ‖E‖²`. The stated Young-estimate gives

```text
(2(1+T²))⁻¹ (‖E‖² + ‖SΓ‖²)
  ≤ ‖E‖² + ‖L_b E + SΓ‖²
  ≤ (2+2T²)(‖E‖² + ‖SΓ‖²).
```

**INFERENCE.** In C1, the defect is not counted in `nReg`; it is controlled as a bounded linear perturbation of the regular variables.

---

**Q2. C5 Partial-Drop**

**FACT.** After the shear,

```text
loss = ‖e‖² δ'² + G²
```

where `G²` is the survivor/reduced-chain core.

If we use the rescaled regular coordinate

```text
x = ‖e‖ δ',
```

then

```text
loss = x² + G² = Φ.
```

So C5 is an instance of `Datum` with:

- `nReg = 1` for the single complement defect direction, plus any other already-regular directions if present
- regular block: `x²`
- reduced core: survivor `G`
- constants:
  ```text
  c₁ = 1
  c₂ = 1
  ```

**INFERENCE.** This is the cleanest conceptual fit: the C5 defect has become an actual Morse square, so it belongs in the regular block.

---

**Q3. One Datum Or Two?**

**FACT.** The stated `Datum` only records:

```text
flatCore, G, nReg, c₁, c₂, squeeze proof.
```

It does not record where the defect came from.

**INFERENCE.** One `Datum` structure covers both C1 and C5. The difference is a difference of field values and producer proofs, not of structure.

Use separate constructors/producers, e.g.

```text
Datum.ofHardPivot
Datum.ofPartialDropShear
```

but both can return the same `Datum` type.

C1: defect lives in the perturbation `b · E`, so `nReg = #E` and `c₁,c₂` are nontrivial.

C5: defect lives in the regular block, so `nReg` increases by `1`, and after rescaling the new coordinate the constants are `1,1`.

---

**Q4. Does `‖e‖` Need To Be Constant?**

**FACT.** No. For the squeeze, `‖e‖` does not need to be constant. It only needs uniform bounds on the chart:

```text
0 < c ≤ ‖e‖ ≤ C.
```

If we use the unweighted coordinate `δ'`, then

```text
flatCore = ‖e‖² δ'² + G²
Φ        = δ'² + G².
```

Hence

```text
min(c², 1) · Φ ≤ flatCore ≤ max(C², 1) · Φ.
```

So the datum works with

```text
c₁ = min(c², 1)
c₂ = max(C², 1).
```

If one has arranged `c ≤ 1 ≤ C`, this simplifies to:

```text
c₁ = c²
c₂ = C².
```

**INFERENCE.** The only real obstruction is loss of a uniform nonzero bound: if `‖e‖` can approach `0` or blow up on the chart, then the unweighted squeeze constants may fail. Constantness is unnecessary; bounded-unit behavior is enough.
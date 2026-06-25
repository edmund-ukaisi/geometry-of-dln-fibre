**1. VERDICT**

Yes, sound for `p = 1, 2, 3` with the given permutations:

- `p=1`: `σ₁ = (0 1)(2 3)(4 6)(5 7)`
- `p=2`: `σ₂ = (0 2)(1 3)`
- `p=3`: `σ₃ = (0 3)(1 2)(4 6)(5 7)`

The `p=3` composite is correct: row-swap A composed with col-swap A gives `(0 3)(1 2)` on A, and the B row-swap remains `(4 6)(5 7)`.

All three satisfy: `σ p = 0`, `σ 0 = p`, `σ '' Aact = Aact`, and `σ` preserves the spectator block `{4,5,6,7}`.

**2. Blow-Up Identity**

Let `Bq := pivotBlowupOn Aact q`. For `Tσ x := x ∘ σ`, the identity

```lean
B p (x ∘ σ) = (B 0 x) ∘ σ
```

holds for all three σ.

Per coordinate:

- `i = p`:
  ```text
  Bp (x∘σ) p = (x∘σ) p = x (σ p) = x 0
  (B0 x ∘ σ) p = B0 x (σ p) = B0 x 0 = x 0
  ```

- `i ∈ Aact \ {p}`:
  ```text
  Bp (x∘σ) i = (x∘σ) p * (x∘σ) i = x 0 * x (σ i)
  ```
  Since `σ i ∈ Aact \ {0}`,
  ```text
  (B0 x ∘ σ) i = B0 x (σ i) = x 0 * x (σ i)
  ```

- `i ∉ Aact` spectator:
  ```text
  Bp (x∘σ) i = (x∘σ) i = x (σ i)
  ```
  Since `σ` keeps spectators in spectators,
  ```text
  (B0 x ∘ σ) i = B0 x (σ i) = x (σ i)
  ```

No coordinate slot fails.

**3. Spectator-Swap Subtlety**

No, the B-coordinate swaps in `σ₁` and `σ₃` do not break `(2)`, `(3)`, or `(4)`.

Reason: `pivotBlowupOn Aact p` only distinguishes active coordinates `{0,1,2,3}` from spectators. It is identity on every spectator coordinate. Therefore any permutation of the spectator block commutes with the blow-up. For example under `σ₁`, at spectator slot `i=4`:

```text
Bp (x∘σ₁) 4 = x 6
(B0 x ∘ σ₁) 4 = B0 x 6 = x 6
```

Same for `5,6,7`.

The determinant also matches:

```text
|(pivotBlowupOnDeriv Aact p (y∘σ)).det|
= |(y (σ p))^3|
= |(y 0)^3|
= |(pivotBlowupOnDeriv Aact 0 y).det|
```

And the domain transports correctly:

```text
Tσ ⁻¹' (chartDomOn Aact p \ pivotZeroOn p)
= chartDomOn Aact 0 \ pivotZeroOn 0
```

`openBox` is invariant under any coordinate permutation because it is `univ.pi (fun _ => Ioo (-1) 1)`.

**4. Lean Lemma Chain**

Clean route:

1. Define a `Fin 8` coordinate permutation measure-preserving lemma, same pattern as existing `measurePreserving_perm` for `Fin 7`:
   ```lean
   theorem measurePreserving_perm8 (σ : Fin 8 ≃ Fin 8) :
       MeasurePreserving (fun x : Fin 8 → ℝ => x ∘ σ) volume volume := ...
   ```
   using `volume_measurePreserving_piCongrLeft`.

2. For each `p`, define the concrete involutive `σp`.

3. Prove structural lemmas:
   ```lean
   pivotBlowupOn_conj_Aact_p0 :
     pivotBlowupOn Aact p (x ∘ σp)
       = (pivotBlowupOn Aact 0 x) ∘ σp

   chartDom_preimage_perm :
     (fun x => x ∘ σp) ⁻¹' chartDomOn Aact p
       = chartDomOn Aact 0

   pivotZero_preimage_perm :
     (fun x => x ∘ σp) ⁻¹' pivotZeroOn p
       = pivotZeroOn 0

   openBox_perm_iff :
     y ∘ σp ∈ openBox ↔ y ∈ openBox
   ```

4. Use the ring/decide-safe lemma:
   ```lean
   myF222 (y ∘ σp) = myF222 y
   ```

5. Transport the integral by:
   ```lean
   hmp.setLIntegral_comp_preimage_emb hemb Ip Dp
   ```
   where `Ip` is the `p`-summand integrand and `Dp := chartDomOn Aact p \ pivotZeroOn p`.

6. Rewrite the pulled-back integral using the domain lemma, determinant lemma, blow-up conjugation, `openBox` invariance, and `myF222` invariance to get exactly the `p=0` summand. Then close by `p0_summand_via_tail c' hc'`.

So the conjugation reduction is sound; no need to rederive the three summands.
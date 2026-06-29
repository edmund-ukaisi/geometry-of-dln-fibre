**1. Verdict**

FALSE as stated. It is true only when the boundary frames are trivial, or when the “reads” are already frame-normalized.

**2. Which Product**

The LHS corresponds to neither the framed product Schur nor the raw decode product Schur.

Given your stated LHS, it is exactly:

```text
Schur₂₂((corM + bare Δ₀) · (corM + bare Δ₁))
```

with pivots `1 + readX_s`. It ignores the nontrivial boundary blocks `A11,A21,B11,B12`. The RHS is:

```text
Schur₂₂(P0 · decode₀ · decode₁ · QL)
= Schur₂₂(decode₀ · decode₁)
```

by the lower/upper frame invariance you proved. Your numeric observation is consistent with this.

**3. The Fix**

For the algebra as stated, the correct repair is **3(a)**: the LDU dictionary must use frame-conjugated reads, not bare reads.

Concretely, layer 0 should use reads from:

```text
P0 · decode₀ = corM + P0 · Δ₀
```

so, schematically,

```text
X̂₀ = A11⁻¹ X₀
Ŷ₀ = A11⁻¹ Y₀
Ẑ₀ = Z₀ - A21 A11⁻¹ X₀
T̂₀ = T₀ - A21 A11⁻¹ Y₀
```

and the last layer should use reads from:

```text
decode₁ · QL = corM + Δ₁ · QL
```

so

```text
X̂₁ = X₁ B11⁻¹
Ŷ₁ = Y₁ - X₁ B11⁻¹ B12
Ẑ₁ = Z₁ B11⁻¹
T̂₁ = T₁ - Z₁ B11⁻¹ B12
```

Then the LDU formula computes the framed Schur.

Option **3(b)** is possible only if Lean’s `prod(deepestM)` / `deepestCoreF` is already definitionally in these frame-normalized coordinates. That contradicts your stated reading of the LHS as bare `1 + readX`. If Lean really uses bare reads, then the producer claim needs re-examination in the sense of **3(c)**.

**4. Cheapest Check**

Run the same scalar test with three quantities:

```text
bareLDU    = Schur₂₂((corM + Δ₀) · (corM + Δ₁))
framedLDU  = Schur₂₂((P0 · decode₀) · (decode₁ · QL))
Rcore      = Schur₂₂(P0 · decode₀ · decode₁ · QL)
```

Expected discriminator:

```text
bareLDU   = 0.0942...
framedLDU = 0.0741...
Rcore     = 0.0741...
```

If Lean’s current LHS gives `0.0942`, then **3(b) is false** and the theorem is false with bare reads. If it gives `0.0741`, then your bare-LHS model is wrong and Lean is already doing **3(b)**. If frame-conjugated reads do not give `0.0741`, then the LDU bridge itself has a separate bug.
---

## Discriminator resolved against the Lean defs (genm-l2wire, 2026-06-28)

Codex's cheapest check: does Lean's LHS evaluate to bareLDU (0.0942) or framedLDU (0.0741)?

DECISIVE — Lean's LHS is BARE (= 0.0942), so **3(b) is FALSE and hLDUtie is FALSE as stated**:
- `deepestCoreF y := dlnLoss (deepestM H r) 0 (decode y)` (DeepestGaugeChart.lean:114) = ‖prod(deepestM)(decode y)‖²
  — the RAW reduced-core product in deepestM coords, NO frame.
- The absorbed cores `y = decode q + schurCorrection q` with `schurCorrection_s = −readZ_s·(1+readX_s)⁻¹·readY_s`
  (DeepestSchurShift.lean:135) — BARE gauge reads off (q.1, q.2.2), the `(1+readX)⁻¹` pivot.
- So LHS = frobSq(S0·((1−K)·S1)) with the bare `1+readX` dictionary = bareLDU = 0.0942 ≠ RHS framed = 0.0741.

VERDICT: hLDUtie (bare-read LHS = framed-Score RHS) is FALSE. Fix is 3(a)/3(c): EITHER the Score/sub-4 RHS
must be the BARE-read Schur (drop the endpoint frames from Score — but then it's not the loss's Schur), OR
the absorbed-core dictionary (schurCorrection / deepestCoreF) must be FRAME-CONJUGATED (3(a): X̂₀=A11⁻¹X₀
etc.), which is a change to the producer's core definition. NOT closeable by assembly. Escalated.

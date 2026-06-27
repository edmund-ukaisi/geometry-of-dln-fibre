1. **Verdict: yes, conflation.**  
For a smooth component \(X \subset \mathbb A^N_k\),

\[
\operatorname{rank}\Omega_{X/k}=\dim X=N-\operatorname{codim}X,
\]

while the conormal module \(I/I^2\), equivalently the Jacobian row/conormal image at a smooth embedded point, has rank

\[
\operatorname{codim}X.
\]

The phrase “\(\Omega\) free of rank = codim” is only defensible if “\(\Omega\)” is being used nonstandardly for the **relative cotangent of the embedding** \(L_{X/\mathbb A^N}\), i.e. conormal data. In Mathlib, `Ω[A⁄k]` means Kähler differentials over `k`, so its rank is dimension, not codimension.

2. **Recommended headline: use Ω, but pin it as the complement of codim.**  
Cleanest honest statement:

> At a smooth closed point of the top-dimensional component, `Ω[A_m⁄k]` is free and its rank plus the proved codimension `C + δ` equals the ambient coordinate count.

Lean-ish shape:

```lean
theorem smoothBlock_kaehler_rank_add_codim_eq_ambient :
  ∃ m : Ideal A, m.IsMaximal ∧ Algebra.IsSmoothAt k m ∧
    Module.Free (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k]) ∧
    ((Module.finrank (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k]) : ℕ∞)
      + (((cCodim d r h).toNat : ℕ∞)
        + ((r * (d (Fin.last _) + d 0 - r) : ℕ) : ℕ∞))
      = (Fintype.card (RepCoord d) : ℕ∞))
```

Equivalent Nat form, if you have the inequalities/cast bookkeeping, is:

```lean
Module.finrank (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k])
  = Fintype.card (RepCoord d)
      - ((cCodim d r h).toNat + r * (dN + d0 - r))
```

Do **not** overclaim:

```lean
Module.finrank (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k])
  = (cCodim d r h).toNat + δ
```

If you truly need a free rank equal to `C + δ`, that is a **separate conormal theorem** about the embedded component ideal, not the Kähler module theorem.

3. **Recommended location: a closed point in the dense smooth open.**  
Your maximal-ideal machinery makes the reachable certificate:

> There exists a maximal ideal `m` of the component ring lying in the smooth locus such that `Ω[A_m⁄k]` is free of rank `dim component = Ambient - (C + δ)`.

Lean-ish shape:

```lean
theorem exists_smoothClosedPoint_kaehler_rank_complement_codim :
  ∃ m : Ideal A, m.IsMaximal ∧ Algebra.IsSmoothAt k m ∧
    Module.Free (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k]) ∧
    ((Module.finrank (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k]) : ℕ∞)
      + codimClosedForm d r h
      = (Fintype.card (RepCoord d) : ℕ∞))
```

This is faithful to “generic” as “on a nonempty dense smooth open”. Avoid calling `m` literally the generic point.

Literal generic point `⊥` is also mathematically clean, but different: for a domain, `Localization.AtPrime (⊥ : Ideal A)` is the function field, whose local Krull dimension is `0`, while `Ω[Frac(A)⁄k]` has rank `trdeg k Frac(A) = dim A`. So do **not** try to reuse the closed-point statement `rank Ω = ringKrullDim localRing` at `⊥`.

4. **Dimension/height identity to lean on.**  
For the ambient polynomial ring \(R = k[x_\sigma]\) and a prime component ideal `p`:

```lean
DLNFibre.Core.height_add_ringKrullDim_quotient_eq_card
  (p : Ideal (MvPolynomial σ k)) [p.IsPrime] :
  (p.height : WithBot ℕ∞)
    + ringKrullDim (MvPolynomial σ k ⧸ p)
    = (Nat.card σ : WithBot ℕ∞)
```

Specialise `σ := RepCoord d`. Top-dimensionality is needed to identify `p.height` with the fibre codimension `C + δ`; the additive height/dimension identity itself holds for any prime in the polynomial ambient.

**Biggest risk to fidelity:** accidentally using `Ω[A⁄k]` where the intended module is conormal `I/I²`.  
Second risk: saying “generic point” while proving only a closed-point certificate, or using local Krull dimension at `⊥`, where it is `0`.
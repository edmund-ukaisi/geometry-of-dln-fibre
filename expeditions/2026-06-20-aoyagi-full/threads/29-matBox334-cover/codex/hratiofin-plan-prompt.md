# Closing `hratiofin` in Lean 4 + Mathlib v4.29 — VET my assembly

I am closing the FINAL `sorry` in a measure-theory finiteness proof. NOT asking for Lean code — VET
the architecture and name the single highest-risk bookkeeping step + cheapest guard.

## The exact goal
For `p : Fin 9`, `2 < c' < 4`, `e := MeasurableEquiv.piFinSuccAbove (fun _:Fin 9 => ℝ) p`:
```
hratiofin : (∫⁻ z in (Set.univ.pi (fun _:Fin 8 => Set.Icc (-1) 1)),
              angA1Int c' p (e.symm (0, z))) < ⊤
```
where
- `angA1Int c' p y := ∫⁻ A1 in matBox 3 4 1, ofReal (frobSq (rmatMul (Rmat334 p y) A1) ^ (-c'))`.
- `Rmat334 p y r c = (if (3*r+c : Fin 9) = p then 1 else y (3*r+c))`  [confirmed by `rfl`; pivot entry=1].
- `matBox 3 4 1 = {A1 : Fin 3 → Fin 4 → ℝ | ∀ i k, A1 i k ∈ [-1,1]}` (symmetric box).
- `frobSq M = ∑ᵢⱼ Mᵢⱼ²`, `rmatMul X Y i j = ∑ₖ Xᵢₖ Yₖⱼ`.
- `angA1Int_offpivot`: `angA1Int c' p y` depends on `y` only through `y i, i≠p` (proved).

## BANKED lemmas (all sorry-free)
1. `angularA1_integral_le c' (hc0:0<c') (b0 b1 g0 g1 d00 d01 d10 d11) (hg0:g0²≤1)(hg1:g1²≤1)`:
   `∫_{A1∈matBox 3 4 1} ofReal(frobSq(rmatMul (angularR b0 b1 g0 g1 d00 d01 d10 d11) A1)^{-c'})
      ≤ ofReal((1/5)^{-c'}) · ∫_{A1∈matBox 3 4 1} ofReal((∑ⱼ Tⱼ² + frobSq(rmatMul (!![d00,d01;d10,d11]) (fun k j => A1 k.succ j)))^{-c'})`
   where Tⱼ = A1 0 j + (b0·A1 1 j + b1·A1 2 j). Here `angularR b0 b1 g0 g1 d00 d01 d10 d11` is the 3×3
   `[[1,b0,b1],[g0,d00+g0 b0,d01+g0 b1],[g1,d10+g1 b0,d11+g1 b1]]` — pivot (0,0)=1, top row (1,b0,b1),
   left col (1,g0,g1), lower-right RAW = Δ+γβ (the de-shift d=raw-γβ is built in).
2. `resolved334_box_lt_top (K)(hK:0<K)(c')(2<c'<4)`:
   `∫_{Δ∈matBox 2 2 K}∫_{S∈matBox 2 4 K}∫_{T∈morseBox 4 K} ofReal((∑ᵢTᵢ²+frobSq(rmatMul Δ S))^{-c'}) < ⊤`.
3. `measurable_angA1Int c' p`, `frobSq_eq_zero_iff`, `frobSq_angularR_ge`, `rmatMul_angularR_eq`.
4. Mathlib: `volume_measurePreserving_piCongrLeft` (permute the first index of `Fin 3 → (Fin 4 → ℝ)`),
   `measurePreserving_add_right` (translation), `MeasurableEquiv.piFinSuccAbove`, `lintegral_lintegral`.

## My proposed assembly
STEP 1 (pivot normalization). p ↔ entry (r₀,c₀)=(p/3, p%3). Define row-swap σr=swap r₀ 0, col-swap
σc=swap c₀ 0 (both Fin 3 ≃ Fin 3, involutions). Claim a permutation lemma:
  `frobSq (rmatMul (Rmat334 p y) A1)
     = frobSq (rmatMul R' (fun k j => A1 (σc k) j))`
  where R' r c := Rmat334 p y (σr r) (σc c)  — has its 1 at (0,0). PROOF idea:
  rmatMul (Rmat334 p y) A1 i j = ∑ₖ R(i,k)·A1(k,j); reindex k by σc (a Fintype reindex of the sum);
  then row-i reindex by σr is just a row-permutation of the OUTPUT, which frobSq (a full ∑ᵢⱼ) is
  invariant under. So `frobSq(R·A1) = frobSq(R'·A1σc)` where A1σc := row-permute A1 by σc.
  Then I read off R' = angularR b0 b1 g0 g1 (raw00-g0b0) (raw01-g0b1) (raw10-g1b0) (raw11-g1b1)
  where (b0,b1,g0,g1,raw00,raw01,raw10,raw11) are the 8 off-pivot entries of R' in the angularR slots.
  Each is `y (3·(σr i)+(σc j))` = some component of `e.symm(0,z)` = some `z_k` (since pivot axis=0,
  off-pivot = ratios = z). So bᵢ,gᵢ,rawᵢⱼ are each = z_{some index}, hence |·|≤1 ⟹ g²≤1. ✓

STEP 2 (substitute A1). In `angA1Int = ∫_{A1∈box34} frobSq(Rmat334·A1)^{-c'}`, substitute A1 ↦ A1σc
(row-permute by σc⁻¹). This is `MeasurableEquiv.piCongrLeft (fun _:Fin 3 => Fin 4→ℝ) σc`, MP, and
matBox 3 4 1 is σc-invariant (symmetric box, just reorders rows). So
  `angA1Int c' p (e.symm(0,z)) = ∫_{A1∈box34} ofReal(frobSq(rmatMul R' A1)^{-c'})`.
Then `angularA1_integral_le` (with g²≤1 from |zₖ|≤1) gives, pointwise in z,
  `angA1Int c' p (e.symm(0,z)) ≤ ofReal((1/5)^{-c'}) · J(z)`
  where J(z) = ∫_{A1∈box34} ofReal((∑ⱼTⱼ²+frobSq(Δ·S))^{-c'}), T=A1row0+βS, Δ=de-shifted z-block, S=A1 rows1,2.

STEP 3 (integrate over z, change variables to resolved). `∫_z angA1Int ≤ ofReal((1/5)^{-c'})·∫_z J(z)`.
Now `∫_z J(z) = ∫_z ∫_{A1} ofReal((∑Tⱼ²+frobSq(Δ·S))^{-c'})`. The 8 z-components split: g0,g1 don't
appear in the integrand (Δ,T,S don't use g after de-shift), so ∫_{g∈[-1,1]²} is a finite vol factor (4).
b0,b1 appear in T; raw00..raw11 appear in Δ=raw-γβ. For fixed (b,g): change raw↦Δ (translation by -γβ,
MP, [-1,1]⁴→[-2,2]⁴⊆[-3,3]⁴); change A1row0↦T (translation by +βS per fixed S, MP, [-1,1]⁴→[-3,3]⁴),
S=A1rows1,2∈[-1,1]⁸⊆matBox 2 4 3. After both translations b,g become finite vol factors too. Net:
  `∫_z J(z) ≤ vol([-1,1]⁴ for b,g) · ∫_{Δ∈[-2,2]}∫_{S∈[-1,1]}∫_{T∈[-3,3]} (...)^{-c'}
            ≤ vol · resolved334_box_lt_top 3` (since [-2,2]⊆[-3,3], [-1,1]⊆[-3,3]).
Wrap: ofReal((1/5)^{-c'})·vol·(finite) < ⊤.

## QUESTIONS (terse, 2-4 sentences each, verdict first)
Q1. Is STEP-1's permutation identity `frobSq(R·A1)=frobSq(R'·A1σc)` the right convention? Specifically:
    is it `A1 ↦ row-permute by σc` (the COLUMN perm of A0 = ROW perm of A1) and is frobSq-invariance under
    the σr row-perm of the OUTPUT the clean way (vs Matrix.submatrix_mul_equiv)? Is there a sign/inverse
    pitfall (σc vs σc⁻¹) given σc is an involution (swap), so σc=σc⁻¹?
Q2. In STEP 2, is substituting A1 inside a `setLIntegral over matBox 3 4 1` via `piCongrLeft σc` and the
    box-invariance the cheapest, or should I keep A1 unpermuted and instead permute inside angularA1?
    (angularA1_integral_le is FIXED to the (0,0) angularR — I cannot permute its statement.)
Q3. STEP 3 is the long pole: ∫_z ∫_{A1} with z=(b,g,raw)∈[-1,1]⁸ and A1∈box34, doing raw↦Δ and A1row0↦T
    translations. To feed resolved334_box_lt_top (a Δ-then-S-then-T iterated integral over matBox 2 2 3,
    matBox 2 4 3, morseBox 4 3), what is the cleanest Fubini/Tonelli ordering? The integrand after de-shift
    depends on: Δ(from raw, 4 vars), T(from A1 row0 + βS, 4 vars), S(=A1 rows 1,2, 8 vars), and the
    spectator b,g (finite). Is the order: peel g (const), then for the joint (b,raw,A1) do
    [raw↦Δ trans][A1row0↦T trans] then drop b to vol then enlarge boxes via lintegral_mono_set then
    Fubini-reorder to (Δ,S,T)? What is the single highest-risk bookkeeping error?
Q4. CRITICAL: the de-shift d=raw-γβ inside angularR. In STEP 2 I feed angularA1_integral_le with
    d00=raw00-g0b0 etc. so its angularR = R' (the RAW lower-right). Then its RHS integrand is
    ∑Tⱼ²+frobSq(!![d00,d01;d10,d11]·S) = ∑Tⱼ²+frobSq(Δ·S) where Δ IS the de-shifted block. So I do NOT
    need a separate raw↦Δ change of variables — Δ is ALREADY d=raw-γβ in the resolved integrand, and raw,γ,β
    are all just z-components (constants w.r.t. A1). So when I integrate over z, Δ=Δ(z) and the
    raw↦Δ map is a z-translation. Confirm: is it cleaner to change variables raw↦Δ in the OUTER z-integral
    (translation MP on [-1,1]⁴→[-2,2]⁴), treating b,g as the translation-shift parameters? Does this avoid
    any nonlinearity (the shift -γβ depends on b,g which are OTHER z-coords — is it still a clean
    measurePreserving_add_right in the raw-subblock with b,g held as outer integration vars)?

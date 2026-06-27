**Q1**

R2 is dead: `Matrix.map`/`RingHom.mapMatrix` only transports an already-existing expression over a source coefficient ring through a ring hom. If the only available `Hmat` is built inside an `ℝ`-typed `Chain`, there is no source `MvPolynomial` matrix for `eval x` to map. So you must either build a polynomial-typed recursion or generalize the recursion to allow `MvPolynomial`.

R3 does not materially lighten R1. A single entry of `Hmat s` expands through matrix products, so it depends on a whole slice of `Hmat (s+1)` and on `suffix (s+1)`, which itself is a full matrix recursion. You may use one entry later for nonvanishing, but the recursion still needs matrix-valued state.

**Q2**

Rank: **1. scoped-generalize `Chain`**, **2. duplicate `PolyChain`**.  
Known from the local shape: the telescope file is pure matrix algebra, so `CommRing R` should be enough, and probably `CommSemiring R` is enough. Inference: the 14 `ℝ` consumers should keep working if you make the coefficient type implicit and infer it from `u`, e.g. `structure Chain (n : ℕ) {R : Type*} [CommRing R] (u : R) where ...`; do not put explicit `R` before `n`, or you will churn every callsite. Expect minor elaboration/simp repairs, not a mathematical break. The win is that `suffixAux`, `HmatAux`, `_succ`, `_last`, and `chain_telescope` remain single-source, and your polynomial chain can reuse them directly.

Skeleton:

```lean
structure Chain (n : ℕ) {R : Type*} [CommRing R] (u : R) where
  Wwid Twid : ℕ → ℕ
  A : (k : ℕ) → Matrix (Fin (Wwid k)) (Fin (Wwid (k+1))) R
  C : (k : ℕ) → Matrix (Fin (Twid k)) (Fin (Wwid k)) R
  B : (k : ℕ) → Matrix (Fin (Twid k)) (Fin (Twid (k+1))) R
  E : (k : ℕ) → Matrix (Fin (Twid k)) (Fin (Wwid (k+1))) R
  R : Matrix (Fin (Twid n)) (Fin (Wwid n)) R
  step : ∀ k, k < n → C k * A k = B k * C (k+1) + u • E k
  base : C n = u • R

theorem Chain.suffixAux_map
    {P S : Type*} [CommRing P] [CommRing S] (f : P →+* S)
    {n : ℕ} {uP : P} {uS : S}
    (cP : Chain n uP) (cS : Chain n uS)
    (hA : ∀ k, (cP.A k).map f = cS.A k) :
    ∀ d s hP hS, (cP.suffixAux d s hP).map f = cS.suffixAux d s hS := ...

theorem Chain.HmatAux_map
    {P S : Type*} [CommRing P] [CommRing S] (f : P →+* S)
    {n : ℕ} {uP : P} {uS : S}
    (cP : Chain n uP) (cS : Chain n uS)
    (hA : ∀ k, (cP.A k).map f = cS.A k)
    (hB : ∀ k, (cP.B k).map f = cS.B k)
    (hE : ∀ k, (cP.E k).map f = cS.E k)
    (hR : cP.R.map f = cS.R) :
    ∀ d s hP hS, (cP.HmatAux d s hP).map f = cS.HmatAux d s hS := ...

noncomputable def UPolyGen : MvPolynomial (Fin N) ℝ := ...
theorem eval_UPolyGen (x : Fin N → ℝ) :
    MvPolynomial.eval x UPolyGen = achieverUfun x := ...
```

**Q3**

Known API: `(A * B).map f = A.map f * B.map f` is exactly `Matrix.map_mul`.  
For scalars, use `Matrix.map_smulₛₗ f f u (fun a => map_mul f u a) A` for the changing-scalar form `(u • A).map f = f u • A.map f`; `Matrix.map_smul` is the same-scalar version, and `Matrix.map_smul'` exists but is square-matrix-only.  
The base lemmas are `Matrix.map_one f (map_zero f) (map_one f)` and `Matrix.map_zero f (map_zero f)`.  
Also useful: `Matrix.map_add f (map_add f) A B`.  
Known API caveat: `RingHom.mapMatrix` is square-matrix bundled API; for rectangular telescope matrices, use `.map f` plus the `Matrix.map_*` lemmas.

**Recommendation**

Use scoped generalization of `Chain` with the coefficient type implicit, then prove one matrix-level `eval` naturality lemma for `suffixAux`/`HmatAux`. Biggest risk, by inference, is not the 14 existing `ℝ` consumers; it is constructing the polynomial `Chain` if `step`/`base` over `MvPolynomial` become expensive. If that happens, fall back to a data-only polynomial recursion carrying just `A/B/E/R`, since `Hmat` itself does not use `C/step/base`.
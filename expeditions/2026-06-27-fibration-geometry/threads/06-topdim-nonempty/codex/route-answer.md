**Section A**

No extra finiteness hypothesis is needed. `Noetherian + Nontrivial` is enough, even when `ringKrullDim A = ⊤`.  
Do not use a “longest chain realizes dimension” argument unless you assume `[FiniteRingKrullDim A]`; that is the trap.  
The finite set of minimal primes can still attain a maximum value in `WithBot ℕ∞`, including `⊤`.

**Section B**

Pick route 1, but slightly modify it: maximize `p ↦ ringKrullDim (A ⧸ p)` over `minimalPrimes A`, then use coheight only to prove the chosen maximum is at least every prime’s coheight.

Route 2 is worse. The `LTSeries.longestOf` version silently needs finite Krull dimension. If generalized to arbitrary chains, it becomes a reimplementation of the coheight/iSup proof.

**Section C**

1. `[friction]` Add/localize quotient-coheight bridge:
   ```lean
   noncomputable def primeSpectrumQuotientOrderIsoIci [CommRing R] (p : PrimeSpectrum R) :
       PrimeSpectrum (R ⧸ p.asIdeal) ≃o Set.Ici p :=
     (p.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus).trans
       (OrderIso.setCongr _ _ (by
         ext x
         rw [Set.mem_Ici, PrimeSpectrum.mem_zeroLocus, ← PrimeSpectrum.asIdeal_le_asIdeal]
         rfl))

   theorem ringKrullDim_quotient_eq_coheight [CommRing R] (p : PrimeSpectrum R) :
       ringKrullDim (R ⧸ p.asIdeal) = (Order.coheight p : WithBot ℕ∞) := by
     rw [ringKrullDim,
       Order.krullDim_eq_of_orderIso (primeSpectrumQuotientOrderIsoIci p),
       ← Order.coheight_eq_krullDim_Ici]
   ```
   Names used here are CONFIDENT except this wrapper name itself is local, not Mathlib.

2. `[mechanical]` Get finite nonempty `minimalPrimes A`:
   ```lean
   have hfin : (minimalPrimes A).Finite :=
     minimalPrimes.finite_of_isNoetherianRing A
   obtain ⟨p₀, hp₀⟩ :=
     Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal A)) bot_ne_top
   ```
   Convert `hp₀` by `simpa [minimalPrimes]`.

3. `[mechanical]` Choose a maximal quotient dimension:
   ```lean
   obtain ⟨p, hpmin, hpmax⟩ :=
     hfin.exists_max_image (fun q : Ideal A => ringKrullDim (A ⧸ q)) hnonempty
   ```
   `hpmax : ∀ q ∈ minimalPrimes A, ringKrullDim (A ⧸ q) ≤ ringKrullDim (A ⧸ p)`.

4. `[mechanical]` The easy inequality:
   ```lean
   have hle : ringKrullDim (A ⧸ p) ≤ ringKrullDim A :=
     ringKrullDim_quotient_le p
   ```

5. `[risk]` The hard inequality:
   ```lean
   rw [ringKrullDim, Order.krullDim_eq_iSup_coheight]
   refine iSup_le ?_
   intro x
   obtain ⟨q, hqmin, hqle⟩ :=
     Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := x.asIdeal) bot_le
   have hqprime : q.IsPrime := Ideal.minimalPrimes_isPrime hqmin
   have hqx : (⟨q, hqprime⟩ : PrimeSpectrum A) ≤ x := by
     rwa [← PrimeSpectrum.asIdeal_le_asIdeal]
   calc
     ((Order.coheight x : ℕ∞) : WithBot ℕ∞)
         ≤ ((Order.coheight (⟨q, hqprime⟩ : PrimeSpectrum A) : ℕ∞) : WithBot ℕ∞) :=
           WithBot.coe_le_coe.mpr (Order.coheight_anti hqx)
     _ = ringKrullDim (A ⧸ q) :=
           (ringKrullDim_quotient_eq_coheight (⟨q, hqprime⟩ : PrimeSpectrum A)).symm
     _ ≤ ringKrullDim (A ⧸ p) :=
           hpmax q (by simpa [minimalPrimes] using hqmin)
   ```
   The likely bites are the cast into `WithBot ℕ∞` and the direction of `Order.coheight_anti`.

**Section D**

Q1. Yes, quotient/coheight is the load-bearing bridge. I found no direct Mathlib lemma named like `coheight_eq_ringKrullDim_quotient`; the local two-line wrapper above is the shortest route. `PrimeSpectrum.zeroLocus_singleton` is not the right tool: use `Ideal.primeSpectrumQuotientOrderIsoZeroLocus` and identify `zeroLocus p.asIdeal` with `Set.Ici p`.

Q3. CONFIDENT: use `Set.Finite.exists_max_image`. It works directly for target `WithBot ℕ∞` because it only needs `[LinearOrder β]`. If you literally need `= ⨆`, use CONFIDENT `exists_eq_ciSup_of_finite` after moving to the subtype of the finite set; but for this proof, `exists_max_image` is cleaner.

Q4. Correct: this route never assumes `⊥ : PrimeSpectrum A`. It only uses `⊥ : Ideal A`, then extracts a minimal prime `q` and turns it into `PrimeSpectrum A` using CONFIDENT `Ideal.minimalPrimes_isPrime`. The place this bites is any attempted use of `Order.coheight_bot_eq_krullDim` on `PrimeSpectrum A`; that would require a bottom prime, i.e. essentially a domain-style situation.
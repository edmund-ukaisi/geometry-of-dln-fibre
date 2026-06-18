<task>
Lean 4 + Mathlib v4.29. I am formalising the EASY (substitution) half of a quadratic-integer-program
(QIP) reduction. I need the cleanest tactic route for ONE sum-manipulation identity. Diagnose the route;
I will write/build the code myself.

EXISTING (committed, do not change):
- `codimForm (N : ℕ) (m : ℤ → ℤ → ℤ) : ℤ :=`
    `∑ i ∈ Finset.Icc (1:ℤ) N, ∑ u ∈ Finset.Icc i N, ∑ j ∈ Finset.Icc u N, ∑ v ∈ Finset.Icc j N,`
    `  m (i-1) (j-1) * m u v`
  (four nested ℤ-`Icc` sums over 1 ≤ i ≤ u ≤ j ≤ v ≤ N).
- `extendℤ (m : Fin (N+1) × Fin (N+1) → ℕ) : ℤ → ℤ → ℤ :=`
    `fun a b ↦ if h : 0 ≤ a ∧ a ≤ b ∧ b ≤ (N:ℤ) then (m (⟨a.toNat,_⟩, ⟨b.toNat,_⟩) : ℤ) else 0`

I am introducing (e : Fin N → ℕ is the QIP variable, d : Fin (N+1) → ℕ the dimension vector):

  `mOfE d e : Fin (N+1) × Fin (N+1) → ℕ` — the substitution. Closed form of its entry at (a,b):
    - if a = 0 and (b : ℕ) < N : value e ⟨b⟩   (paper e_{b+1})
    - if (a:ℕ) ≥ 1 and b = Fin.last N : value e ⟨a-1⟩ + (d a - d (a-1))   [ℕ subtraction; d Monotone so ≥0]
    - else 0
  (Verified numerically: it is a valid Kostant partition with corner mOfE(0,N)=0, for Monotone d.)

  `Gqip d e : ℤ := ∑ i : Fin N, ∑ j : Fin N, if j ≤ i then (e i:ℤ) * ((e j:ℤ) + (d j.succ:ℤ) - (d j.castSucc:ℤ)) else 0`
  (paper G_d(e) = ∑_{1≤j≤i≤N} e_i (e_j + d_j - d_{j-1}); here i,j:Fin N index paper 1..N.)

TARGET IDENTITY (numerically verified true for all feasible e on 5 dimension vectors incl N=8):
  `theorem codimForm_mOfE (hd : Monotone d) (e : Fin N → ℕ) :`
    `codimForm N (extendℤ (mOfE d e)) = Gqip d e`

THE MATH (why it is true). In codimForm the product is m(i-1)(j-1) * m(u)(v) over 1≤i≤u≤j≤v≤N.
For m = extendℤ (mOfE d e):
  - m(i-1)(j-1): first index i-1 has (i-1)<j-1<...<N-1 generally; nonzero ONLY when i-1=0 (so i=1) and
    (j-1)<N, i.e. the "a=0,b<N" branch, giving e_{(j-1)+1}=e_{j} [0-indexed e⟨j-1⟩]. So the first factor
    forces i=1 and contributes e_j (paper index).  Wait — re-derive: m(i-1)(j-1) nonzero needs either
    (i-1=0 ∧ j-1<N) → e_{j} ; or (i-1≥1 ∧ j-1=N) → but j-1≤N-1<N here since j≤N... actually j ranges to N
    so j-1 can be N-1 max, never =N. So ONLY the a=0 branch fires: i=1, factor = e_{(j-1)+1}.
  - m(u)(v): nonzero needs (u=0 ∧ v<N) → but u≥i=1, so u≥1, a=0 branch impossible; or (u≥1 ∧ v=N) →
    factor = e_u + (d_u - d_{u-1}). So the second factor forces v=N.
  Hence the only surviving terms have i=1 and v=N, leaving a DOUBLE sum over 1≤u≤j≤N (with i=1,v=N):
    ∑_{1≤u≤j≤N} e_j * (e_u + d_u - d_{u-1}).
  Renaming (paper) j→i', u→j' gives ∑_{1≤j'≤i'≤N} e_{i'}(e_{j'}+d_{j'}-d_{j'-1}) = G_d(e). QED.

So the identity collapses a 4-fold ℤ-Icc sum to a 2-fold one by killing two indices (i=1, v=N), then
matches a Fin N × Fin N double sum.

WHAT I'M UNSURE ABOUT (the route):
The hard part is the index gymnastics between ℤ-`Finset.Icc 1 N` sums (with `extendℤ`'s dite guards and
`toNat`/`Fin.mk` casts) and the `Fin N` double sum in `Gqip`. Three candidate routes:
  (A) Stay in codimForm's ℤ world: push `extendℤ (mOfE d e)` to an explicit `ℤ → ℤ → ℤ` piecewise
      function (prove a rewrite lemma `extendℤ_mOfE : extendℤ (mOfE d e) a b = <ℤ piecewise in a,b>`),
      then collapse the inner two sums with `Finset.sum_eq_single` (v=N) and outer with i=1, and finally
      reindex the surviving ℤ-Icc double sum to Fin N via `Finset.sum_Icc` / a bijection.
  (B) Convert codimForm's ℤ-Icc sums to Fin (N+1) / Fin N sums up front and never touch ℤ again.
  (C) Something else.

<output_contract>
1. RECOMMENDED ROUTE (A/B/C) in 2-3 sentences, with the single biggest friction point named.
2. The exact Mathlib v4.29 lemma names for: collapsing a `∑ x ∈ Finset.Icc a b, f x` where f is supported
   at a single point (v=N, i=1); reindexing a ℤ-`Finset.Icc 1 N` sum to `Fin N`; and handling the
   `extendℤ` dite guard cleanly. Flag any name you are <80% sure exists at v4.29.
3. A concrete ordering of `have` lemmas (signatures only) to get from codimForm to Gqip, smallest first.
4. PITFALLS specific to ℤ-Icc + toNat + Fin.mk casts that will bite.
</output_contract>

<grounding_rules>
Mark each lemma name as [SURE] (you've seen it at v4.29) or [GUESS]. Do not invent a lemma to make the
plan look clean — if the natural lemma may not exist, say so and give the manual fallback.
</grounding_rules>

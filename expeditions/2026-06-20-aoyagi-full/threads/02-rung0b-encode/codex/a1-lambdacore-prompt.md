<task>
Lean 4 + Mathlib (v4.29) proof strategy for an integer-optimization lemma. I need the CLEANEST
proof route (the diagnosis, not code I'll paste). I'll implement and build locally.

THE LEMMA (frozen statement, must prove exactly):
  theorem lambdaCore_eq_clean (M : Fin (L + 1) → ℕ) :
      ∃ (ℓ : ℕ) (m : Fin (ℓ + 1) → ℕ), lambdaCore M = cleanCore ℓ m

DEFINITIONS:
- lambdaCore M : ℚ := (1/2) * ((Adm M).inf' (Adm_nonempty M) (Mval M) : ℤ)   -- ½·min_{T∈Adm} M(T)
- Mval M T : ℤ := ∑ j : Fin L, (tPrev M T j - T j) * (M j.succ - T j)
    where tPrev M T j = (if j.val=0 then M 0 else T (j-1))   -- t^0 := M^1 convention
- Adm M : Finset (Fin L → ℕ) := piFinset(range(admBound+1)).filter(admPred)
    admPred: weak-decrease t^1≥…≥t^L, t^L=0, each t^j ≤ admBound (= min(M0,M1) for j=0, else M(j+1))
- cleanCore ℓ m : ℚ := (1/4)*( (∑ i:Fin ℓ, balancedSplit(∑m, ℓ, i)^2) - (∑ k:Fin(ℓ+1), m k^2) )
    balancedSplit P ℓ i = if i<P%ℓ then P/ℓ+1 else P/ℓ   (the integer-balanced ℓ-split of P)

MATH (Aoyagi Lemma 3, verified numerically 437/437): the min of M(T) over Adm equals
2·cleanCore(ℓ*, m*) where (ℓ*, m*) is the Def-3 selection = the ℓ+1 SMALLEST reduced widths of M, for
the ℓ that Def-3 picks. The clean form ¼(Σqᵢ²−Σmₖ²) is the value at the genuine minimizer; q the
balanced split minimizes Σqᵢ² subject to Σqᵢ = P (convexity/exchange).

KEY OBSERVATION: the statement is EXISTENTIAL over (ℓ, m) — I am NOT forced to use Def-3; I only need
SOME (ℓ, m) with lambdaCore M = cleanCore ℓ m. min Mval over Adm varies in structure across M (e.g.
M=(2,2,2)→3 at T=(1,0); M=(4,4,2)→7 at T=(3,0); M=(3,3,3,3)→6 at T=(2,1,0)).
</task>

<output_contract>
1. Rank proof routes by Lean-tractability (lowest proof surface first). For each: the key Mathlib
   lemmas (inf'-characterization: Finset.inf'_eq_..., le_inf', inf'_le; the balanced-split convex
   minimum), and the rough step count.
2. CRUCIAL: is there a route that EXPLOITS the existential to AVOID the full min-over-Adm computation?
   E.g. (a) a closed-form minimizer T*(M) one can write down and prove is the argmin by two
   inequalities (Mval T* ≤ everything via an exchange/telescoping bound, and T* ∈ Adm); then pick
   (ℓ,m) so cleanCore ℓ m = ½ Mval T*. OR (b) can cleanCore's own free ℓ,m be chosen to MATCH
   ½·min directly without the Def-3 sort? Say which is cleaner.
3. The single most error-prone step in Lean and how to dodge it.
4. If the honest answer is "this is a genuine ~200+ line optimization proof with no shortcut", say so
   plainly and give the minimal decomposition (helper lemmas) so it can be staged.
</output_contract>

<grounding_rules>
Distinguish what you KNOW about Mathlib v4.29 API from what you're INFERRING. Flag any lemma name you
are not sure exists (I will verify with rg before relying on it). Do not invent inf' lemma names.
</grounding_rules>

<task>
Lean 4 + Mathlib v4.29 formalisation. I am adding a paper-faithful predicate and an
equivalence to an existing file `DLNFibre/Core/OrbitKostant.lean`.

CONTEXT — the existing objects (all already proved, sorry-free):

- `cumul (N : ℤ) (m : ℤ→ℤ→ℤ) i j = ∑_{k ∈ Icc 0 i} ∑_{l ∈ Icc j N} m k l`. This is the
  paper's `r_{ij} = Σ_{k≤i≤j≤l} m_{kl}`. In particular `cumul N m k k = Σ_{a≤k≤b} m a b`,
  which is exactly the paper's dimension equation RHS.
- `diff` is the inverse second-difference; `diff_cumul`/`cumul_diff` are mutual inverses on
  `Supported N` arrays (vanish for i<0 and j>N).
- `SuppArray (N:ℤ) ℤ = { f : ℤ→ℤ→ℤ // Supported N f }`.
- `rankFn d A : Fin(N+1)→Fin(N+1)→ℕ` = `if h : i ≤ j then rankPattern d A i j h else 0`.
- `kostantArrayOfRank r : SuppArray (N:ℤ) ℤ` = `diffArrayOfRank r` truncated to 0 below diagonal,
  where `diffArrayOfRank r = cumulDiffEquiv.symm (embedRank r) = diff (embedRank r)`,
  and `embedRank r` casts the Fin-indexed ℕ pattern to a ℤ-indexed ℤ SuppArray (0 outside [0,N]²).
- `IsKostantArray m := (∀ i j, 0 ≤ m.1 i j) ∧ (∀ i j, j < i → m.1 i j = 0)`.
- `KostantPartition d := { m : SuppArray (N:ℤ) ℤ // m ∈ kostantArrayOfRank '' Set.range (rankFn d) ∧ IsKostantArray m }`
- Bridge already proved: `kostantArrayOfRank_isKostant : IsKostantArray (kostantArrayOfRank (rankFn d A))`.
- `cumul_kostantArrayOfRank_of_le r (hxy : x ≤ y) : cumul N (kostantArrayOfRank r).1 x y = (embedRank r).1 x y`.

REALIZATION MACHINERY (from IntervalModule.lean / Orbit.lean):

- `intervalDirectSum (L : List (Fin(N+1)×Fin(N+1))) : Tuple (foldDim L)` — the ⊕ M_{ab} over a list.
- `rankPattern_intervalDirectSum_eq_cumul (L) (i j) (hij) : (rankPattern (foldDim L) (intervalDirectSum L) i j hij : ℤ) = cumul N (multiplicityArray L) i j`.
- `multiplicityArray L a b = (L.map (fun p ↦ if a=(p.1:ℤ) ∧ b=(p.2:ℤ) then 1 else 0)).sum`
- `multiplicityArray_cons : multiplicityArray (p::ps) = fun a b ↦ singleDelta p.1 p.2 a b + multiplicityArray ps a b`.
- `foldDim_eq_sum (L) (t) : foldDim L t = (L.map (fun p ↦ intervalDim p.1 p.2 t)).sum`.
- `Orbit.baseChange_normalForm A` gives: ∃ L (h:foldDim L = d) P, P • A = h ▸ intervalDirectSum L ∧ ... ∧ rankPattern = cumul (multiplicityArray L).

MY GOAL. Define a standalone predicate
  `CMPlus d m := IsKostantArray m ∧ ∀ k : Fin (N+1), (d k : ℤ) = cumul (N:ℤ) m.1 (k:ℤ) (k:ℤ)`
(the paper's CM⁺: nonneg, i≤j-supported, dimension equations d_k = Σ_{i≤k≤j} m_{ij}).

Then prove the membership iff (given IsKostantArray m):
  `m ∈ kostantArrayOfRank '' Set.range (rankFn d) ↔ CMPlus d m`.
FORWARD (realizable ⟹ CMPlus): from r_{kk}=d_k (rankPattern_self) + cumul_kostantArrayOfRank_of_le.
REVERSE (CMPlus ⟹ realizable, the hard one): build a tuple A (over a chosen field, say ℚ) with
`kostantArrayOfRank (rankFn d A) = m`. The natural realizer is `intervalDirectSum L` for a list L
with `(m.1 i j).toNat` copies of `(i,j)` for each i ≤ j in Fin(N+1), reindexed so it lives over d.

KEY OBSTACLES I want your judgement on:
1. The realizer `intervalDirectSum L` lives over `foldDim L`, NOT over `d`. I need a tuple over `d`.
   The cast `h ▸ intervalDirectSum L` (h : foldDim L = d) is the device used in baseChange_normalForm.
   But then I must compute `rankFn d (h ▸ intervalDirectSum L)` and there is a `rankPattern_transport`
   lemma in Orbit.lean. Is the cleaner route to (a) directly construct the realizer + cast, or
   (b) is there a slicker path? Note rankFn needs the tuple to live over d exactly.
2. To get `foldDim L = d` I need `(foldDim L t : ℤ) = cumul N (multiplicityArray L) t t = cumul N m.1 t t = d t`.
   The middle equality needs `multiplicityArray L = m.1` as integer arrays (at least on [0,N]²).
   Building L with toNat-many copies and proving `multiplicityArray L a b = m.1 a b` for all a b:
   what is the cleanest list construction over a Finset/Fin product, and the cleanest induction to
   prove the multiplicity equals the array? (m.1 is nonneg and supported, so toNat round-trips.)
3. Is there any reason to AVOID going through intervalDirectSum and instead reuse baseChange_normalForm
   in reverse — i.e. is the forward construction of L the only real work, with foldDim/transport
   being routine? Flag if the transport/cast bookkeeping (rankPattern_transport, ▸ through foldDim)
   is a known pain point that will eat the budget.

I have rankPattern_transport available. The whole library is currently 0 sorry/axiom and must stay so.
</task>

<output_contract>
1. RECOMMENDED PATH: one paragraph — direct-construct+cast vs reuse baseChange_normalForm, and why.
2. LIST CONSTRUCTION: the concrete `L`-from-`m` definition (Lean-ish pseudocode) and the lemma
   `multiplicityArray L = m.1` with its proof sketch (induction structure, key Mathlib lemmas).
3. foldDim = d: the chain of equalities and which existing lemmas close each step.
4. THE FINAL ASSEMBLY: how kostantArrayOfRank (rankFn d realizer) = m falls out (the diagonal
   d_k equation feeds the off-diagonal? or do I need cumul on the whole upper triangle?).
   IMPORTANT subtlety to address: CMPlus only constrains the DIAGONAL (d_k). Does that suffice to
   pin the realizer's whole rank pattern to m, or is m's own structure (it IS the multiplicity array)
   what pins it, with the diagonal equation only needed for foldDim L = d? Be explicit.
5. RISK FLAGS: ranked list of what will fight back, cheapest mitigation each.
Keep it tight. Lean tactic names where load-bearing.
</output_contract>

<grounding_rules>
Mark any lemma name you are unsure exists in Mathlib v4.29 as [VERIFY]. Distinguish
"this definitely works" from "this is the likely shape, check it". Do not invent
DLNFibre lemma names beyond those I listed; if you need a new helper, say so and name it descriptively.
</grounding_rules>

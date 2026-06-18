<task>
You are an independent fidelity reviewer. Judge whether two Lean 4 (Mathlib) statements faithfully
capture the corresponding mathematical objects from a paper. Do NOT assume the formalisation is
correct; do NOT assume it is wrong. Frame in the paper's definitions, hypotheses out: report exactly
where the Lean does and does not match, and flag anything underspecified.

=== PAPER (Le Halleur–Rimányi 2024, "Geometry of the fibers of the multiplication map of DLNs") ===

§ Setup. Fix a dimension vector d = (d_0, d_1, ..., d_N) over a field k. Rep_d = ∏_{i=1}^N Mat_{d_i, d_{i-1}}(k),
tuples (A_1,...,A_N) with A_i : k^{d_{i-1}} → k^{d_i} (so A_i is a d_i × d_{i-1} matrix).
The multiplication map:  mult : Rep_d → Mat_{d_N, d_0},  (A_1,...,A_N) ↦ A_N · A_{N-1} ··· A_1.
Loci:  Σ^r_d := { A_* ∈ Rep_d | rank(mult A_*) = r };  the closure  \overline{Σ}^r_d := { A_* | rank(mult A_*) ≤ r }
(NOTE: the downloaded LaTeX source displays this as "≥ r", but the surrounding component/codimension
statements use "≤ r"; treat the intended convention as the open question and say which the Lean matches).
Fibre:  mult^{-1}(B) := { A_* | mult A_* = B }  for B ∈ Mat_{d_N, d_0}.

§ Prop 3.1a (prop:mr_comparison). On upper-triangular arrays indexed by 0 ≤ i ≤ j ≤ N, the maps
  m_{ij}(r) = r_{ij} − r_{i,j+1} − r_{i-1,j} + r_{i-1,j+1}   (convention r_{ij}=0 if i<0 or j>N)
  r_{ij}(m) = Σ_{k ≤ i ≤ j ≤ l} m_{kl}
are well-defined and mutually inverse.

=== LEAN STATEMENTS UNDER REVIEW ===

-- Module 1: Core/Setup.lean.  variable {k : Type u} [CommRing k] {N : ℕ}
abbrev Tuple (d : Fin (N + 1) → ℕ) : Type u :=
  ∀ i : Fin N, Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k
def multPrefix (d) (A : Tuple d) : (j : Fin (N + 1)) → Matrix (Fin (d j)) (Fin (d 0)) k :=
  Fin.induction (1 : Matrix (Fin (d 0)) (Fin (d 0)) k) (fun i prev ↦ A i * prev)
def mult (d) (A : Tuple d) : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k := multPrefix d A (Fin.last N)
def productRankLocus (d) (r : ℕ) : Set (Tuple d) := {A | (mult d A).rank = r}
def productRankLocusLE (d) (r : ℕ) : Set (Tuple d) := {A | (mult d A).rank ≤ r}
def fibre (d) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) : Set (Tuple d) := {A | mult d A = B}
-- step lemmas (both rfl): multPrefix d A 0 = 1 ;  multPrefix d A i.succ = A i * multPrefix d A i.castSucc

-- Module 2: Core/RankPattern.lean.  variable {R : Type u} [AddCommGroup R]; arrays are ℤ → ℤ → R.
def cumulRow (m) (i j) := ∑ k ∈ Finset.Icc 0 i, m k j
def cumulCol (N) (m) (i j) := ∑ l ∈ Finset.Icc j N, m i l
noncomputable def cumul (N : ℤ) (m) : ℤ → ℤ → R := cumulRow (cumulCol N m)
  -- cumul_apply: cumul N m i j = ∑ k ∈ Icc 0 i, ∑ l ∈ Icc j N, m k l
def diff (r) : ℤ → ℤ → R := diffRow (diffCol r)
  -- diff_apply: diff r i j = r i j - r i (j+1) - r (i-1) j + r (i-1) (j+1)
def Supported (N : ℤ) (f) : Prop := (∀ i j, i < 0 → f i j = 0) ∧ (∀ i j, N < j → f i j = 0)
theorem diff_cumul (N) (m) (hi : ∀ i j, i<0 → m i j=0) (hj : ∀ i j, N<j → m i j=0) : diff (cumul N m) = m
theorem cumul_diff (N) (r) (hi : ∀ i j, i<0 → r i j=0) (hj : ∀ i j, N<j → r i j=0) : cumul N (diff r) = r
noncomputable def rankPatternEquiv (N : ℤ) : {f // Supported N f} ≃ {f // Supported N f} where
  toFun m := ⟨cumul N m.1, _⟩;  invFun r := ⟨diff r.1, _⟩  -- left_inv/right_inv from the two theorems above
</output_contract>
</task>

<output_contract>
Respond in exactly these sections, terse:
1. mult — does the Lean ordered product, codomain, domain, and the A_i shape match the paper? (yes/no + the one discrepancy if any)
2. loci + fibre — does productRankLocus/productRankLocusLE/fibre match? Which inequality (≤ or ≥) does the Lean closure use, and is that the mathematically-correct Zariski closure of {rank = r}?
3. Prop 3.1a — do cumul and diff match the paper's r_{ij}(m) and m_{ij}(r) FORMULAS exactly (including index ranges)? Is the "out of range = 0" convention faithfully realised by `Supported`? Is the inversion genuinely TWO-SIDED?
4. Is `Supported` the correct/closed support invariant for a guard-free Equiv, or does the box 0≤i,j≤N appear elsewhere needed?
5. Naming: does `rankPatternEquiv` denote exactly what is proved (an abstract array inversion over AddCommGroup R), or does the name overclaim?
6. Any fidelity gap, missing hypothesis, or vacuity risk you see.
</output_contract>

<grounding_rules>
Mark each judgement as FACT (derivable from the statements shown) or INFERENCE (your reasoning about
likely intent / standard math). For the closure inequality, the paper text is contradictory by design —
say which reading the Lean takes and whether it is the correct closure of {rank=r}; do not guess the
paper's intent as fact. Be specific; cite the exact term. Do not propose code.
</grounding_rules>

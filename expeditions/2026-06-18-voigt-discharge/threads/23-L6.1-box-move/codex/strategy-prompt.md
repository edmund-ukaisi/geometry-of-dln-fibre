<task>
Lean 4 + Mathlib v4.29 formalisation. I'm proving the "box-move degeneration" (L6.1) for an
equioriented type-A quiver, on a concrete matrix-tuple encoding.

ENCODING (all landed, network-free `Core` engine):
- `Tuple d := ∀ i : Fin N, Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k`  (a chain of edge maps,
  edge i : vertex i.castSucc → vertex i.succ, dimension vector d : Fin (N+1) → ℕ).
- `submult d A i j hij : Matrix (Fin (d j)) (Fin (d i)) k` = product A_j…A_{i+1} of edge maps.
- `rankPattern d A i j hij : ℕ := (submult d A i j hij).rank`.
- `intervalDirectSum L : Tuple (foldDim L)` for `L : List (Fin (N+1) × Fin (N+1))` = ⊕ of interval
  (lace) modules M_{[a,b]}; its `rankPattern = cumul (multiplicityArray L)` (landed).
- `BaseChangeGroup d := ∀ v, (Matrix (Fin (d v)) (Fin (d v)) k)ˣ`; action `(P • A) i = P_{i+1} A_i (P_i)⁻¹`.
- LANDED key lemmas:
  * `rankPattern_eq_iff_orbit A B : (∀ i j hij, rankPattern A = rankPattern B) ↔ ∃ P : BaseChangeGroup d, P • A = B`
  * `rankPattern_smul P A i j hij : rankPattern (P • A) i j = rankPattern A i j`  (rank pattern is base-change invariant)
  * `baseChange_of_intertwine A B (φ : ∀ t, (Fin (d t) → k) ≃ₗ[k] (Fin (d t) → k))
       (hφ : ∀ e, (φ e.succ) ∘ (A e).mulVecLin = (B e).mulVecLin ∘ (φ e.castSucc)) : ∃ P, P • A = B`
  * L6.0 limit lemma: `curvePoint_zero_mem_zeroLocus_vanishingIdeal [Infinite k] (c : σ → Polynomial k)
       (Z : Set (σ → k)) (hZ : ∀ t ≠ 0, curvePoint c t ∈ Z) : curvePoint c 0 ∈ zeroLocus (vanishingIdeal Z)`
    where `curvePoint c t x = (c x).eval t`.
  * `orbitSet M := canonicalCoord d '' {A | ∃ P, P • M = A}`  (point set in `RepCoord d → k`).
  * `canonicalCoord d : Tuple d ≃ (RepCoord d → k)`, `canonicalCoord d A ⟨i,r,c⟩ = A i r c`.

GOAL (L6.1, the consumption shape for L6.0):
For interval data with `a < c ≤ b+1 ≤ e`, the downstairs tuple `M_{[a,b]} ⊕ M_{[c,e]} ⊕ rest` lies
in the Zariski closure of the orbit of the upstairs tuple `M_{[a,e]} ⊕ M_{[c,b]} ⊕ rest`. Concretely:
  `canonicalCoord d (downstairs) ∈ MvPolynomial.zeroLocus (vanishingIdeal (orbitSet upstairs))`.

ROUTE (from a pen-and-paper certificate, sympy-verified on 3 instances):
1. Define a 1-parameter family `F : k → Tuple d`, entrywise polynomial in `t`: take the upstairs
   `intervalDirectSum`, perturb the SINGLE recombination arrow by scalar `t` on the cut arrow
   (`A_1(t) = [t, 1]` in the (1,2,1) instance). `F(0) = downstairs intervalDirectSum`; for `t ≠ 0`,
   `F(t)` is in the upstairs ORBIT.
2. `F(t) ∈ orbit(upstairs)` for `t ≠ 0`: via `rankPattern_eq_iff_orbit`, show `rankPattern (F t) = rankPattern upstairs`.
   FRICTION (flagged by the certificate): `F(t)` is NOT a `dirSum` (the perturbed arrow breaks
   block-diagonality), so block-rank additivity does not apply. The certificate suggests an explicit
   base change `P(t)` with `P(t) • upstairs = F(t)` — but my hand-computation shows the needed `P_1(t)`
   has a `t⁻¹` entry (`b = -1/t`), polynomial only away from 0. So `P(t)` exists for each fixed t≠0 but
   is not a polynomial family.
3. Apply L6.0 with `c x := canonicalCoord` of the polynomial family `F`, `Z := orbitSet upstairs`.

QUESTION. I have two candidate strategies for step 2 (`rankPattern (F t) = rankPattern upstairs`, t≠0):
  (A) BASE CHANGE: construct `φ_v(t) : (Fin (d v) → k) ≃ₗ k^{d v}` intertwining the chains of `upstairs`
      and `F(t)`, feed `baseChange_of_intertwine` to get `∃ P, P • upstairs = F t`, then `rankPattern_smul`.
      The intertwiner at the recombination vertex needs `t⁻¹` (t≠0 in scope, so `(t : k)ˣ` / units fine).
  (B) DIRECT RANK: compute `rankPattern (F t) i j` and `rankPattern upstairs i j` directly as ranks of
      explicit `submult` matrices and show equal for t≠0 (the off-diagonal entry that changes is a single
      rank-of-small-matrix computation; t≠0 keeps it the same rank).

Which is cleaner in Lean for the GENERAL box-move lemma (arbitrary a<c≤b+1≤e and arbitrary `rest`),
and which for just the (1,2,1) witness? Is there a THIRD option I'm missing — e.g. proving
`F(t) ≈ upstairs` as an explicit module iso without computing the matrices, or staying entirely on the
multiplicity-array/`cumul` side? Be concrete about the Lean-idiom cost (what's the worst sub-goal in each).
</task>

<output_contract>
Terse, sectioned:
1. Recommended strategy for the GENERAL lemma (A / B / other) + the single worst sub-goal it forces.
2. Recommended strategy for the (1,2,1) WITNESS + worst sub-goal.
3. If a THIRD route exists, name it and the Mathlib lemma it leans on.
4. One concrete warning: the likeliest place this proof balloons or gets stuck, and how to pre-empt it.
</output_contract>

<grounding_rules>
Distinguish Mathlib lemmas you are CONFIDENT exist at v4.29 from ones you are INFERRING. If you name a
lemma (e.g. for rank of a perturbed matrix, or for building the linear equiv), flag whether it's a
recalled exact name or a plausible-but-unverified one — I will `rg` it before relying on it. Do not
hand-wave the `t⁻¹` / unit construction; if (A), say exactly how the vertex equiv is built.
</grounding_rules>

<task>
Lean 4 + Mathlib (v4.29) formalisation design question. I must formalise a "charts-exhaust
coverage-completeness" theorem for a DEEP linear-network rank-degeneration locus, and I need the
CLEANEST faithful + reachable Lean STATEMENT + a proof decomposition. Argue whichever way; if my
framing is wrong, say so.

SETTING (banked, sorry-free, exact signatures):
- Parameter space: `Params (H : Fin (L+1) → ℕ) := ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ`
  (a composable tuple of L real matrix layers; dependent Fin widths).
- Deep product (the map "mult"): `prod H A : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ`, the layer
  product A⁽¹⁾·…·A⁽ᴸ⁾, a left-associated fold. `prodAux_succ` peels the LAST layer:
  `prod (k+1) = prodAux k * (reindex (A_k))`.
- Target locus: `S_s := { A : Params H | (prod H A).rank ≤ s }`.
- CR (composite-rank) recursion, banked as `minAdmRec`:
  CR((v₀,…,v_p), s) = min_{0≤r≤min(v_{p-1},v_p)} [ (v_{p-1}−r)(v_p−r) + CR((v₀,…,v_{p-2}, r), s) ];
  base CR((v₀,v₁),s) = (v₀−s)(v₁−s); inner=0 when r≤s. κ_k := CR(widths, ρ−k).
- Banked pieces I can reuse:
  (a) `pivotLocus_eq_iUnion (t) : {A : Matrix (Fin m)(Fin n) K | t ≤ A.rank} = ⋃ (ρ:Fin t↪Fin m)(κ:Fin t↪Fin n), {A | IsUnit (A.submatrix ρ κ)}`  (SINGLE matrix; general embeddings).
  (b) `exists_square_minor (A)(hm : m ≤ A.rank) : ∃ (ρ:Fin m→Fin p)(κ:Fin m→Fin q), Inj ρ ∧ Inj κ ∧ (A.submatrix ρ κ).det ≠ 0`.
  (c) My own `deepReduce_rank (X)(Δ)(U)(V)(hΔ:IsUnit Δ.det) : (X * fromBlocks Δ U V (V*Δ⁻¹*U)).rank = (X * fromRows Δ V * Δ⁻¹).rank`  — the one-peel rank recursion, but ONLY for a TOP-LEFT invertible pivot in `fromBlocks` form.
  (d) `deepReduce_skeleton` : on {E=0}, `fromBlocks Δ U V (VΔ⁻¹U) = fromRows Δ V * Δ⁻¹ * fromCols Δ U` (CUR/skeleton).
  (e) Gluing consumer: `lintegral_lt_top_of_finite_cover {ι}[Fintype ι](C : ι → Set α)(D)(f)(hcover : μ(D \ ⋃ i, C i)=0)(hfin : ∀ i, ∫⁻ x in C i, f < ⊤) : ∫⁻ x in D, f < ⊤`.

THE OBLIGATION (from a fidelity review): "CRrec = geometric κ_k rests on ... the deferred
charts-exhaust coverage-completeness lemma." The pivot-minor charts {det (effective layer)_{I,J} ≠ 0}
at each recursion level are supposed to EXHAUST S_s = {rank(prod) ≤ s}, realizing the CR-tree so the
transverse codim = κ_k. This must be a genuine theorem, not a stub.

KEY OBSTACLE I hit: pure SET coverage `S_s ⊆ ⋃ charts` is TRIVIAL — the rank-0 chart (empty pivot,
IsUnit of a 0×0 submatrix) is the whole space, so any union that includes it covers S_s vacuously.
So "charts exhaust S_s" as a bare set inclusion carries no content. The genuine content must involve
the per-cell rank-DROP structure / codim (that on each cell the rank-drop locus is a transverse
coordinate slice {E_j = 0} of the right dimension, and these realize κ_k), OR the recursion itself
(that peeling the last layer's actual-rank pivot reduces to a shorter chain with the SAME product rank).

The genuinely hard infra I foresee: (i) general-pivot permutation (put an arbitrary size-r pivot at
top-left so `deepReduce_rank`/`fromBlocks` apply); (ii) constructing the REDUCED `Params` chain of
length L−1 (absorb the pivot columns of the last layer into the previous layer) and relating its
`prod` to the reduced product; (iii) a finite CR-tree PATH index type (dependent widths); (iv) the
coverage induction on L.
</task>

<output_contract>
1. THE STATEMENT. Give the single cleanest faithful Lean `theorem` signature (types + hypotheses)
   for "charts-exhaust coverage-completeness" that (a) is NON-trivial (escapes the rank-0-chart
   triviality), (b) genuinely discharges "CRrec = geometric κ_k", (c) is reachable with the banked
   pieces. If the right object is a codim/measure statement rather than a set inclusion, say which and
   give its signature. If it should be an EXACT characterization (= not ⊆) to avoid triviality, say so.
2. DECOMPOSITION. Ordered list of sub-lemmas to get there, each with a one-line Lean-ish signature,
   marking which reuse a banked piece vs are new. Flag the single hardest sub-lemma.
3. THE RECURSION SHAPE. How to express the reduced Params chain + relate its prod rank to the
   original (the (i)+(ii) infra). Is there a way to AVOID constructing the reduced Params (e.g. state
   the recursion at the matrix-product level, or via an existential over reduced data) — a formulation
   that sidesteps the dependent-width chain surgery?
4. REACHABILITY VERDICT + a rough LoC band, and the single cheapest genuine FIRST theorem to land.
5. TRIVIALITY CHECK. Confirm or refute my claim that bare set-coverage of {rank ≤ s} is vacuous, and
   state precisely what makes the theorem non-vacuous.
</output_contract>

<grounding_rules>
Flag inference vs. fact. If you assert a Mathlib lemma exists, mark it "UNVERIFIED — check". Do not
invent lemma names as if confirmed. Distinguish "this is the mathematically right statement" from
"this is cheaply reachable in Lean now". Prefer a smaller genuine theorem over an ambitious stub.
</grounding_rules>

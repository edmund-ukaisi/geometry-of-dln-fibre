<task>
Lean 4 + Mathlib v4.29. I must construct, for ARBITRARY M : Fin (L+1) → ℕ, a chart
`phi_M : (Fin N → ℝ) → (Fin N → ℝ)` (N = Σ_s M_s · M_{s+1}, the flat dim of a DLN parameter tuple)
proving the achiever box-divergence atom. The atom is already reduced M-agnostically and sorry-free to
"construct a NodeAchieverChart M" bundle. The single hardest field is the chart map + the EXACT telescoping
identity it must satisfy. THREE concrete instances are fully built sorry-free at FIXED dimensions
((4,4,2,2), (3,3,4), (3,3,3,3)); each is ~800-1000 lines of hand-transcribed Matrix (Fin 3)(Fin 3) ℝ entries.

The math (settled, thread-26 closed form). Pick a descent path t_0=M_0 ≥ t_1 ≥ … ≥ t_L=M_L achieving
minAdm M = Σ_s (t_{s-1}-t_s)(M_s - t_s) ... [actually D = Σ_{s=1}^{L} r_s c_s with r_s=t_{s-1}-t_s, c_s=M_s-t_s].
Build factor matrices A^(s) : Matrix (Fin (M (s+1))) (Fin (M s)) ℝ (the s-th DLN layer) such that the
product A^(0)·A^(1)·…·A^(L-1) = u · H exactly (u = one radial pivot coordinate), giving
routeMCore M (phi_M flatcoords) = ‖prod‖² = u²·‖H‖² = u²·V, with V|_{u=0} ≠ 0 and |det Dphi_M| = u^{minAdm-1}·spectator.

The KEY structural fact: the factors chain as
  C_s = P_s K_s Q_s + u·diag(0, R_s)   (compressed transition, size t_{s-1}×... )
  A^(0)=C_1, A^(s) = G_s^{-1} [C_{s+1}; W_{s+1}]  (G_s unit upper triangular, det 1)
  Q_s A^(s) = C_{s+1}, and S_s = C_s A^(s)…A^(L-1) satisfies S_L = C_L = u R_L, S_s = P_s K_s S_{s+1} + u(…),
  so by backward induction every S_s is u-divisible ⟹ prod = u·H.

THE PROBLEM. The factor matrices A^(s) live in genuinely DIFFERENT-SIZED spaces
Matrix (Fin (M (s+1))) (Fin (M s)) ℝ — dependent on s and on the (arbitrary) widths M_s. The product
`prod M A` already exists in Lean (it folds the dependent matrix product with `prodAux` dependent-Fin casts).
The det step is SOLVED separately (I bank a List.prod-of-full-ambient-endomorphisms telescoping; the det is
not the question here).

The question is ONLY about the chart map + telescoping identity at GENERAL L, dependent block sizes.

I see three possible encodings:
(A) Define phi_M / the A^(s) directly over the dependent Params M = Π s, Matrix (Fin (M(s+1)))(Fin(M s)) ℝ,
    and prove prod = u·H by induction on L using the backward S_s recursion. Risk: dependent-Fin cast fight
    in the matrix-size arithmetic (t_{s-1}, t_s, c_s all M-dependent), heavy `Fin.cons`/`Matrix.fromBlocks`
    reindexing at each level.
(B) Avoid per-level different sizes: pad everything to the AMBIENT square (max width W = max_s M_s), express
    each A^(s) as a W×W matrix (identity/zero padding off its active block), prove the telescoping for the
    padded square product, then project. Risk: relating padded square product to the genuine `prod M A`.
(C) Reduce general L to L=1 (RRR / two-matrix) by a layer-collapsing recursion that mirrors the EXISTING
    minAdmRec layer-peeling (minAdm(M) = min_t (M_0-t)(M_1-t) + minAdm(t,M_2,…,M_L)): build phi recursively,
    one boundary at a time, gluing the t-rank pivot. Risk: the recursive chart's telescoping bookkeeping.

ALSO assess: is this genuinely a multi-thousand-line build that should be ROADMAPPED behind a design pass
(with the 3 fixed instances already banking the headline's de-risking), or is there an encoding that makes
the GENERAL build only modestly larger than ONE fixed instance? Be brutally honest about cost — I would
rather report "needs design pass, roadmap it, here is the cleanest skeleton" than burn days on a doomed
dependent-cast fight.
</task>

<output_contract>
1. RANK the three encodings (A/B/C) by total Lean cost-to-green for the GENERAL atom, cheapest first.
   For the top choice, give the precise crux lemma (the telescoping induction step) in Lean-ish pseudocode
   and name the ONE place dependent casts bite + how to kill them (specific Mathlib lemma / Fin.cons trick).
2. Is there a 4th encoding I missed that is cheaper? If so, describe it; else say "no".
3. Honest cost verdict: BUILD-NOW (general atom reachable in a bounded tide of < ~1500 lines) vs
   ROADMAP (genuinely multi-thousand-line / multi-pass; the 3 fixed instances are the right current banking).
   Give your single most-likely-to-be-wrong assumption in each direction.
4. If ROADMAP: what is the highest-value INCREMENTAL piece a formaliser should bank NOW toward the general
   atom (beyond the det telescoping already banked), that is sorry-free and reusable?
</output_contract>

<grounding_rules>
Flag inference vs. fact. You do not have the repo; reason from the math + the Lean-typing constraints I gave.
Do NOT assume Mathlib lemmas exist without hedging ("if Mathlib has X"). The cost verdict is the load-bearing
output — do not hedge it into uselessness; commit to BUILD-NOW or ROADMAP and defend it.
</grounding_rules>

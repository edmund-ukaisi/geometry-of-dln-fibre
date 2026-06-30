<task>
Lean4/Mathlib DLN-fibre formalisation. I need to know the TRUTH VALUE (provable or false) of one
arithmetic claim about a depth-L=2 deep-linear-network achiever path, then the cheapest proof if true.

SETTING (L = 2, M : Fin 3 → ℕ = (M0, M1, M2), all the relevant facts BANKED sorry-free):
- `deepRank M := Text M (tach M) 2` (the compressed leaf width along the achiever path).
- `minAdm M := ((Adm M).inf' Mval).toNat` ≥ 0; non-degeneracy hypothesis: `1 ≤ minAdm M`.
- `tStar M : Fin 2 → ℕ` is the achiever argmin in `Adm M`; BANKED:
    `Mval_tStar_eq : Mval M (tStar M) = (minAdm M : ℤ)`
    `sum_rBlock_cBlock_eq_minAdm : ∑_{j:Fin 2} rBlock j * cBlock j = minAdm M`  (over ℤ)
      where `rBlock j = tPrev(tStar) j − tStar j` (≥0), `cBlock j = M_{j+1} − tStar j` (≥0),
      `tPrev(tStar) 0 = M 0` (the input width), `tPrev(tStar) 1 = tStar 0`.
- BANKED `interiorDrop_L2_iff : InteriorDrop M ↔ (0 < M 2 ∧ deepRank M < M 0 ∧ deepRank M < M 1)`.
- BANKED `deepRank_le_M0 : deepRank M ≤ M 0`.
- BANKED `widths_pos_of_minAdm : 1 ≤ minAdm M → (0 < M 0 ∧ 0 < M 1 ∧ 0 < M 2)`.
- The map `Text M (tach M)`: `Text 0 = M 0`? `Text 1 = M 0`, `Text 2 = deepRank`. (`Text 1 = M 0` BANKED
  via tach_mk_zero; `Text 2 = tach M ⟨1⟩ = tStar ⟨0⟩`-ish — i.e. deepRank = tStar 0.)

THE CLAIM (the lone open `sorry`, needed as chart-nondegeneracy hyp `h0r`):
    InteriorDrop M  →  0 < Text M (tach M) 2   (i.e. 0 < deepRank M),   given 1 ≤ minAdm M.

Equivalently (interiorDrop_L2_iff): given `0 < M2 ∧ deepRank < M0 ∧ deepRank < M1` and `1 ≤ minAdm`,
is `deepRank > 0` forced? Or is there an interior-drop M with deepRank = 0 and minAdm ≥ 1?

KEY QUESTION: does `deepRank M = 0` (i.e. tStar 0 = 0) force `minAdm M = 0`? If deepRank = tStar 0 = 0,
then rBlock 0 = M0 − 0 = M0, cBlock 0 = M1 − 0 = M1, rBlock 1 = tStar0 − tStar1 = 0 − tStar1 (but
tStar1 ≥ 0 and tStar1 ≤ tStar0 = 0 by the descent, so tStar1 = 0), cBlock 1 = M2 − 0 = M2. Then
minAdm = ∑ rBlock·cBlock = M0·M1 + 0·M2 = M0·M1 ≥ 1 (widths pos). So minAdm ≥ 1 does NOT exclude
deepRank = 0 — it gives minAdm = M0·M1 > 0. So the claim `InteriorDrop → deepRank > 0` looks FALSE?
But wait: is (deepRank=0, i.e. tStar0=0) actually ADMISSIBLE / the achiever, AND interior-drop?
interiorDrop needs deepRank < M0 (0 < M0 ✓) and deepRank < M1 (0 < M1 ✓) and 0 < M2 ✓. So
M = (1,1,1): deepRank candidate 0 < 1, 0 < 1, 0 < 1 — interior-drop with deepRank 0?? But is tStar0=0
the ARGMIN for (1,1,1)? minAdm(1,1,1): compare tStar0=0 (Mval=1·1=1) vs tStar0=1 (rBlock0=0,
cBlock0=0, rBlock1=1, cBlock1=1 → Mval=1) — tie at 1. The argmin tStar0 could be 0 OR 1.
If tStar0 = 1 then deepRank = 1 > 0 and InteriorDrop FAILS (deepRank=1 not < M0=1). So whether
M=(1,1,1) is interior-drop depends on which argmin tStar picks!
</task>

<output_contract>
1. TRUTH VALUE: is `InteriorDrop M → 0 < deepRank M` (at L=2, given 1 ≤ minAdm) TRUE or FALSE? If FALSE,
   give the explicit counterexample M = (M0,M1,M2) + the tStar it forces + confirm interior-drop holds
   AND deepRank = 0 AND minAdm ≥ 1.
2. If TRUE: the cheapest proof sketch (which banked lemmas, what arithmetic). Note the tStar argmin
   tie-breaking — does `tStar`/`tach` pick deepRank>0 deterministically (e.g. via the inf' /
   Finset.min' tie-break) so that interior-drop ⟹ the chosen tStar0 > 0?
3. If the truth depends on the EXACT tStar tie-break convention, say so and tell me what to check in
   `tStar`'s definition (`(Adm M).inf' Mval` argmin) to resolve it.
Be concrete; this gates a Lean proof. Distinguish proven-fact from inference.
</output_contract>

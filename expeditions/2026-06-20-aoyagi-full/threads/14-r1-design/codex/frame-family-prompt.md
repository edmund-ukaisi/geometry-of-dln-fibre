<task>
Lean 4 / Mathlib DLN deepest-point loss-squeeze. I must define a per-layer gauge frame family
`(Pf Qf : (s : Fin L) → Matrix … ℝ)` for the #80 cert, satisfying a per-layer normalization, with the
TELESCOPING constraint that interior frames are IDENTITY. I hit a subtlety and need the cleanest design.

CONSTRAINTS the family must satisfy:
(N) per-layer normalization: `Pf_s · deepestPoint_s · Qf_s = corM` for ALL s, where
    `corM = blockdiag[I_r, 0]` (the `r×r` identity corner). [needed for the part-(1) round-trip
    `framedParams(split w) s = Pf_s · (paramsSymm w)_s · Qf_s`, since framedParams reconstructs the
    deviation `(paramsSymm w − deepestPoint)_s` and `(paramsSymm w)_s = deepestPoint_s + deviation_s`.]
(I) interior-id: `Qf_s = 1` for `s+1 < L`, and `Pf_{s+1} = 1` for `s+1 < L` (i.e. `Pf_s = 1` for
    `s ≥ 1`, `Qf_s = 1` for `s ≤ L-2`). [needed for `endpoint_telescoping`'s hinterface: interior
    interfaces `Qf_s · Pf_{s+1} = 1` vanish, so only the 2 boundary frames survive.]

KNOWN FACTS (Lean lemmas, real):
- `deepestPoint_interior_eq_corM`: for STRICT-interior s (0 < s, s+1 < L), `deepestPoint_s = corM`.
- `deepestPoint_layer0_cols_vanish` (L≥2): layer 0's columns `j ≥ r` are 0 — so `deepestPoint_0` is
  `[A | 0]` (an `H_0 × H_1` matrix, rank r, right block zero).
- `deepestPoint_layerLast_rows_vanish` (L≥2): layer (L-1)'s rows `i ≥ r` are 0 — `[A ; 0]` (bottom zero).
- `deepestPoint_frame_exists` / `deepestPoint_frame` (= Classical.choose): gives a TWO-SIDED frame
  `(P,Q)` with `P · deepestPoint_s · Q = corM` for EACH s — but P,Q are arbitrary normalizing units,
  NOT guaranteed id on interior, and it's two-sided (so can't directly give a one-sided boundary frame).
- `rank_normal_form_exists` (Core): two-sided P,Q for any rank-r matrix → corM. (the two-sided form.)
- NOT yet in the build: one-sided normal forms `left_normal_form_of_cols_vanish`
  (`[A|0]` rank r ⟹ ∃ left unit P, P·[A|0] = corM) / `right_normal_form_of_rows_vanish` (transpose) —
  these are dispatched as a separate task #159 (RankNormalForm.lean), not done.

THE SUBTLETY: For (I)+(N) together at the BOUNDARY:
- Layer 0: need `Pf_0 · deepestPoint_0 · Qf_0 = corM` with `Qf_0 = 1` (since 0 ≤ L-2 for L≥2). So need a
  LEFT-only frame `Pf_0 · deepestPoint_0 = corM`. The two-sided `deepestPoint_frame 0` gives
  `(frame).1 · deepestPoint_0 · (frame).2 = corM` with a NONTRIVIAL `(frame).2` — does NOT give the
  one-sided form. Need `left_normal_form_of_cols_vanish` (#159) on the `[A|0]` shape.
- Layer L-1 symmetric: need `deepestPoint_{L-1} · Qf_{L-1} = corM` (right-only), needs #159's transpose.
- Interior: Pf=Qf=1, deepestPoint=corM, `1·corM·1=corM`. ✓ (but `deepestPoint_interior_eq_corM` is
  STRICT interior `0 < s ∧ s+1 < L`; the family's (I) says `Pf_s=1` for `s≥1` and `Qf_s=1` for `s≤L-2`
  — for L=2 there are NO strict-interior layers, both layers are boundary. For L=1 there is ONE layer
  that is BOTH boundaries.)

QUESTIONS:
1. Is the family genuinely forced to use the ONE-SIDED boundary normal forms (#159)? Or is there a
   cleaner formulation of (Pf, Qf) that satisfies (N)+(I) using only the EXISTING two-sided
   `deepestPoint_frame` + the vanishing facts — e.g. absorbing the unwanted boundary side into the
   neighboring interior frame (so it's not literally id but the INTERFACE Qf_s·Pf_{s+1}=1 still holds)?
   The telescoping only needs the INTERFACES to be id, not each frame separately — does that slack help?
2. If #159 is genuinely needed, what is the MINIMAL one-sided lemma statement (give the exact Lean
   signature) and is `[A|0]` rank r ⟹ ∃ P unit, P·[A|0]=corM` provable from `rank_normal_form_exists`
   (two-sided) by absorbing the right factor? (the right factor acts on the zero block trivially?)
3. Edge cases L=1 (single layer = both boundaries, needs Pf_0·dp_0·Qf_0=corM two-sided, fine — the raw
   deepestPoint_frame works since no interior constraint) and L=2 (two boundary layers, no interior).
   Does the family definition need to case on L, or does a uniform `if (s:ℕ)=0 then … ` / `if (s:ℕ)+1=L
   then …` definition work for all L≥1?
4. RECOMMENDATION: the cleanest family def + whether to (a) depend on #159 (request it), (b) use the
   interface-slack reformulation, or (c) some other route. Rank by robustness.
</task>

<output_contract>
Numbered to the 4 questions. For Q2 give the exact Lean lemma signature. For Q4 a clear single
recommendation + the fallback. Concise. Flag inference vs. fact.
</output_contract>

<grounding_rules>
No repo access. Reason from the facts above. Flag any assumed Mathlib lemma as "verify-exists".
Be honest if the interface-slack idea doesn't actually avoid #159.
</grounding_rules>

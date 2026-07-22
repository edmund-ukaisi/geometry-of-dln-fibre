<task>
Lean 4 + Mathlib formalisation. I need the proof structure for a one-adjacent-swap order-isomorphism
between two "binding" posets. Give me the Lean-implementable construction + the key lemma proofs'
structure (not full Lean code — the mathematical argument at a level I can transcribe).

SETUP.
M = (M⁰,...,M^L) : Fin (L+1) → ℕ positive widths. Profiles T = (t¹,...,t^L) ∈ ℕ^L, t⁰ := M⁰.
Adm M: weakly-decreasing (t¹≥...≥t^L), last t^L = 0, per-coord t^j ≤ admBound j (admBound 0 =
min(M⁰,M¹), admBound j = M^{j+1} for j≥1).
Mval M T = (M¹−t¹)(M²−t¹) + Σ_{j=2}^L (t^{j-1}−t^j)(M^{j+1}−t^j)  [over ℤ; ≥ 0 on Adm].
minAdm M = min over Adm of Mval. bindingSet M = {T ∈ Adm M : Mval M T = minAdm M}, ordered by
coordinatewise ≤.

swapWidths k M swaps the two adjacent width entries M_k, M_{k+1} (k : Fin L; positions k.castSucc,
k.succ in Fin (L+1)). I have swapWidths_swapWidths (involutive) proved.

The atomic transport R on the middle coordinate (Codex's earlier design, verified numerically):
swapR P X Q A B = if A≤B ∧ B−A≤P−X then X+(B−A) else if B<A ∧ A−B≤X−Q then X−(A−B) else P+Q−X,
where for a swap at width-position k: P = t^{k-2} (or M⁰ if k=1), X = t^{k-1}, Q = t^k, A = M_k, B = M_{k+1}.
Only the coordinate X = t^{k-1} changes; the swap minimises (P−X+A)²+(X−Q+B)² locally.

GOAL: build `swapBinding_orderIso : Nonempty (↥(bindingSet M) ≃o ↥(bindingSet (swapWidths k M)))`.
</task>

<output_contract>
Four sections, concise, math-level (transcribable to Lean), not full code:
1. swapProfile: the exact profile-transport function T ↦ T' (which coordinate changes, the swapR
   application, Fin-index handling). Its inverse (should be swapProfile on swapWidths k M, via
   swapWidths_swapWidths).
2. Mval-INVARIANCE: the precise argument that Mval (swapWidths k M) (swapProfile T) = Mval M T. This
   is the crux — spell out the quadratic (P−X+A)²+(X−Q+B)² symmetry and exactly which Mval summands
   change and cancel. Flag any admissibility hypotheses it needs (e.g. the branch conditions holding).
3. admissibility preservation: swapProfile T ∈ Adm (swapWidths k M) — which Adm clauses need what.
4. monotonicity BOTH directions (T ≤ T' ⟺ swapProfile T ≤ swapProfile T') and the Lean assembly
   (OrderIso.ofHomInv vs Equiv+map_rel_iff'). Which direction is the hazard; where it will bite.
</output_contract>

<grounding_rules>
Distinguish what you can DERIVE/verify vs educated guesses. The swapR/quadratic design is from a prior
decorrelated pass verified on 1360 vectors — treat it as given. If the Mval-invariance needs the branch
condition (A≤B vs B<A) to hold on binding profiles, say so and how it's guaranteed. Do not invent a
formula that contradicts value-preservation; if a case (e.g. the P+Q−X reflection branch) breaks
invariance, flag it precisely.
</grounding_rules>

<task>
Independent derivation from Aoyagi (2023) "Consideration on the learning efficiency of
multiple-layered neural networks with linear units", Section 5 recursive blow-up (pages 14-22).
I need you to derive, from the chart structure alone, HOW the exceptional-divisor coordinates
u_{s,k} are positioned in a fixed ambient coordinate system as the recursion proceeds. Do NOT
consult any conclusion of mine; derive it yourself.

SETUP (verbatim from the pages, so we share the objects):
- The recursion maintains, indexed by (S,J):  <prod_{s=1..L} C^{(s)}> =
  < diag(b_1,...,b_{M(S)}) * [[E_J, O],[O, D_J]] * prod_{s=S+1..L} C^{(s)} >
  where D_J = (d_{ij}), J+1<=i<=M(S), J+1<=j<=M^{(S+1)}, is the residual block; M(S)=min(M^1..M^S);
  b_0=1, b_i = (prod_{tilde t_{s,k}=i-1} u_{s,k}) b_{i-1}; the u_{s,k} are the exceptional
  coordinates introduced by earlier blow-ups. E_J is the JxJ identity (cleared unit pivots).
- CASE 1 (b_{J+1}=...=b_{J+J1} != b_{J+J1+1}): blow up the center
  { d_{ij}=0 (J<i<=J+J1, J<j<=M^{(S+1)}), u_{s,k}=0 } where u_{s,k} is a SPECIFIC pre-existing
  divisor (the one with tilde t_{s,k}=J+J1, Def-4 minimal). This center has codim
  J1*(M^{(S+1)}-J) + 1 (the "+1" is the u_{s,k}). It has two chart types:
    - CASE 1(1): pivot on u_{s,k}. Substitution d_{ij} = u_{s,k} * d'_{ij}. Sets tilde t_{s,k}=J,
      exponent M'_{s,k}=M_{s,k}+J1*(M^{(S+1)}-J). No new divisor introduced.
    - CASE 1(2): pivot on the corner d-entry d_{J+1,J+1}. Substitution d_{ij}=u_{S,J+1}*d'_{ij}
      with d'_{J+1,J+1}=1, introducing a NEW divisor u_{S,J+1}; AND the pre-existing divisor is
      re-expressed u_{s,k} = u_{S,J+1} * u'_{s,k}. Then a unipotent Q (cleans first row of the
      block; also C^{(S+1)} -> Q^{-1} C^{(S+1)}) and a unipotent P (cleans first column) reduce
      D''_J to [[1,O],[O,D_{J+1}]]. Afterwards ALL primed objects are renamed back (b'->b, d'''->d,
      u'->u, etc.).
- CASE 2 (b_{J+1}=...=b_{M(S)}, the full block): blow up center { d_{ij}=0, J<i<=M(S), J<j<=M^{(S+1)} }
  (NO u in the center). Pivot on corner d_{J+1,J+1}=u_{S,J+1} (new divisor), then Q,P clean.
- ROLLOVER: when J+1 > M(S+1)=min(M(S),M^{(S+1)}), the block collapses to (1,0,...,0), S increments,
  J resets to 0; the residual moves to layer S+1's matrix. No substitution here.

FIXED AMBIENT COORDINATE SYSTEM: index every scalar coordinate by a flat triple (layer, row, col)
= one entry of the original parameter matrix C^{(layer)} (size M^{(layer)} x M^{(layer+1)}). Blow-up
charts are dimension-preserving birational maps of this ambient space, so every chart's source has
the same coordinate slots; some slots hold divisor variables u, others hold residual/ratio or
spectator entries.

THE QUESTION: as the recursion proceeds through Case-1(1) merges, Case-1(2)/Case-2 new-divisor
steps, rollovers, and the Q/P gauges, does each exceptional divisor u_{s,k} stay in ONE fixed flat
slot for its whole life, or is it moved between slots by later substitutions? For each transition
kind, state which flat slot(s) the substitution rewrites, and whether any u-variable's slot is
renamed/relocated. Then: given ONLY the current bookkeeping of a divisor -- its rank-profile vector
T_{s,k}=(t^{(1)},...,t^{(L)}) and its accumulated exponent M_{s,k} -- can you always reconstruct the
flat slot a divisor occupies, or can two different divisors (in different branches, or the same
branch) carry identical (T,M) yet sit in different slots?
</task>

<output_contract>
1. VERDICT: does a divisor's flat slot stay fixed for life? (yes / no / mixed). One line.
2. PER-TRANSITION table: for each of {Case-1(1), Case-1(2), Case-2, rollover, Q, P}, name the flat
   slots the substitution rewrites and whether any u-variable is relocated/renamed to a different
   slot. Be explicit about the pre-existing divisor in Case-1(2) (u_{s,k}=u_{S,J+1}u'_{s,k}).
3. NEW-DIVISOR SLOT: when a new u_{S,J+1} is born (Case-1(2)/Case-2), what flat slot does it take,
   as a function of the birth node (S,J)?
4. RECONSTRUCTIBILITY: is the slot a function of the current (T,M)? If not, give a concrete small
   instance (specific M=(M^1,...,M^{L+1}) and two branches) where identical (T,M) sits in two
   different slots. Distinguish "within one leaf/state" from "across leaves".
5. If a carrier had to track each divisor's slot, is a single immutable per-divisor field (set at
   birth, carried unchanged) SUFFICIENT, or is a dynamic per-transition update rule required?
   One paragraph.
Keep it tight. Exact algebra only; no hand-waving. Flag any step where the page structure above is
insufficient to decide and say what additional page content you would need.
</output_contract>

<grounding_rules>
- Reason ONLY from the chart structure given (and standard affine blow-up chart algebra:
  blowing up {x_0=...=x_c=0} and pivoting on x_p replaces x_p by the blow-up parameter and each
  other x_i by the ratio x_i/x_p, which naturally occupies x_i's own slot).
- A "slot" is the flat (layer,row,col) index, NOT the coordinate's value. Rescaling a coordinate in
  place (dividing by a pivot) keeps its slot; only a rename that puts a variable at a DIFFERENT
  (layer,row,col) counts as "moved".
- Do not assume a conclusion; derive. If you find the slot is NOT fixed, say so and give the exact
  update rule. Distinguish fact-from-the-pages vs your inference.
</grounding_rules>

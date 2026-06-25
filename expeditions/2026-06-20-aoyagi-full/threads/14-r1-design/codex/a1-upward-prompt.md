<task>
A Lean induction-maintenance step I need the cleanest proof mechanism for. The bound is TRUE (verified
0 fails over millions of cases); I need the PROOF, especially for one sub-region. NO counterexample hunt.

SETUP (exact integers): forwardMax greedy, q_i = maxPick(M^{i+1}, ws_i, R_i) = largest pool elt >= M^{i+1}
keeping Dom. R_{i+1} = R_i.erase q_i. ws_i = Mwidths.drop(i+1) = [M^{i+2},...,M^L] (suffix widths AFTER
position i). cLt(S,t)=#{s<t}. Dom(b,R): |b|=|R| ∧ ∀t cLt(R,t)<=cLt(b,t). u_i telescopes:
u_{i+1}=M^{i+1}+u_i-q_i. head'_i = max(u_i, M^{i+1}). The pool R_0 = Ymulti = (balancedSplit of P into c
parts: c values in {b, b+1}, exactly r=P mod c copies of b+1, b=⌊P/c⌋) ⊎ (the L-c largest sorted widths).
ACHIEVER FACT good_floor_core (proven): c·a_i <= Sprefix(c+1)+(i-1) for 1<=i<=c (a = sorted widths).

INVARIANT (STRONG INV): carry  STRONG(i) := ∀ t <= head'_i, cLt(R_i, t) <= cLt(ws_i, t).
Also available: TIGHT chain (the standard green forwardMax Dom-chain) Dom(M^{i+1}::ws_i, R_i) for ALL t
(i.e. ∀t cLt(R_i,t) <= cLt(ws_i,t) + [M^{i+1}<t]); maintained for free by maxPick_spec.
GOAL: STRONG(i) ⟹ STRONG(i+1) := ∀ t <= head'_{i+1}, cLt(R_{i+1}, t) <= cLt(ws_{i+1}, t).

ESTABLISHED FACTS (exact, exhaustive):
- head' is NOT monotone; head'_{i+1} > head'_i in 34% of steps (the "upward" case).
- In EVERY upward step, head'_{i+1} = M^{i+2} (the next width drives the increase, NOT u_{i+1}). So the
  NEW range is t ∈ (head'_i, M^{i+2}].
- Within that new range, t > M^{i+1} ALWAYS (so [M^{i+1}<t]=1, the TIGHT chain leaves a +1).
- Within the new range, q_i < t holds in MOST but NOT all cases (fails when q_i >= t; q_i >= M^{i+1} by
  feasibility, so q_i can land in [M^{i+1}, t)).
- The hard sub-cases (new range, q_i >= t so erasing q_i doesn't reduce the count) are ALL t <= b+1.
- The pure static claim "∀ t<=b+1: cLt(R_{i+1},t) <= cLt(ws_{i+1},t)" is FALSE on its own (fails ~15%) —
  it needs the inductive STRONG(i), it is not a standalone β-count.
- ws_i = M^{i+2} :: ws_{i+1}, so cLt(ws_i,t) = cLt(ws_{i+1},t) + [M^{i+2}<t]; in the new range t<=M^{i+2}
  so [M^{i+2}<t]=0, hence cLt(ws_i,t) = cLt(ws_{i+1},t).

THE TARGET in the new range (head'_i < t <= M^{i+2}): cLt(R_{i+1},t) <= cLt(ws_{i+1},t) = cLt(ws_i,t).
  cLt(R_{i+1},t) = cLt(R_i,t) - [q_i<t]. TIGHT chain: cLt(R_i,t) <= cLt(ws_i,t) + 1 (since M^{i+1}<t).
  So cLt(R_{i+1},t) <= cLt(ws_i,t) + 1 - [q_i<t]. Need to lose the +1 when q_i>=t (the hard case).
</task>

<output_contract>
1. In the upward new range (head'_i < t <= M^{i+2}, so t>M^{i+1}), with the HARD sub-case q_i>=t (erase
   doesn't reduce the count), where does the extra "-1" come from to close cLt(R_{i+1},t)<=cLt(ws_{i+1},t)?
   The TIGHT chain gives only +1 slack. The hard cases are all t<=b+1. Pin the mechanism: does good_floor_core
   give cLt(R_i,t) <= cLt(ws_i,t) (TIGHT with NO +1) in this t<=b+1 ∩ (head'_i, M^{i+2}] range — i.e. the
   β-block elements of R_i below t are few enough that they fit under the suffix widths WITHOUT the head slot?
2. Give the cleanest STRONG(i)⟹STRONG(i+1) proof. Is the right structure: (A) t<=head'_i: from STRONG(i) +
   erase-monotonicity (+ handle the M^{i+2}<t slot); (B) head'_i<t<=head'_{i+1}=M^{i+2}: split into
   q_i<t (free) and q_i>=t∧t<=b+1 (good_floor_core gives the tight no-+1 bound on R_i)? Name exactly which
   inequality good_floor_core supplies and on which t-range.
3. Is there a SINGLE uniform invariant strengthening that absorbs the upward extension without the case
   split (e.g. carry the TIGHT no-+1 bound cLt(R_i,t)<=cLt(ws_i,t) for ALL t<=b+1, proven once by
   good_floor_core as a SEPARATE conjunct, independent of the head'_i window)? Would that conjunct be
   self-maintaining? [Note: I found the pure "∀t<=b+1" static version is NOT standalone-true; but a
   carried conjunct that uses the IH might be.]
4. Flag any circularity.
</output_contract>

<grounding_rules>
- Exact integers. The bound is TRUE; I need the cleanest PROOF + exactly where good_floor_core injects.
- Do NOT claim head' is monotone (it is not). Do NOT claim a pure static β-count closes it (it does not).
- Distinguish PROVED from CONJECTURE. The key open: the "-1" source in the q_i>=t ∧ t<=b+1 hard sub-case.

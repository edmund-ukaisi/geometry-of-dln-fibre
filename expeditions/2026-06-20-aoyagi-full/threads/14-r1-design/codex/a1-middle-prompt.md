<task>
A finite combinatorial induction-maintenance gap. I have an invariant maintenance step that holds
numerically (0 fails / millions of cases) but I need the clean MECHANISM for one sub-region, to
formalize in Lean. NO counterexample hunt — the bound is TRUE; I need the proof structure.

SETUP (exact integers):
- forwardMax picks left-to-right from a pool R: at step i, pick q_i = maxPick(w_i, ws_i, R_i) = the
  LARGEST y in residual pool R_i with y >= w_i (the i-th width) and Dom(ws_i, R_i.erase y)
  (Dom-preserving). R_{i+1} = R_i.erase q_i. ws_i = the suffix widths after position i.
- cLt(S, t) = #{s in S : s < t}.  Dom(b, R) := |R|=|b| and forall t: cLt(R,t) <= cLt(b,t).
- u_i (a "level") telescopes: u_0 = M0; u_{i+1} = M^{i+1} + u_i - q_i.  (So u_{i+1} depends on q_i.)
- head'_i = max(M0,M1) if i=0, else max(u_i, M^{i+1}).
- The INVARIANT carried: INV(i) := Dom(head'_i :: ws_i, R_i)   (ws_i = widths from position i+1 on),
  i.e. forall t: cLt(R_i, t) <= cLt(head'_i :: ws_i, t) = cLt(ws_i, t) + [head'_i < t].
  Plus a "shapeInv(i)" achiever fact constraining elements <= b+1 (b = a fixed level ⌊P/c⌋).

THE MAINTENANCE GOAL (INV(i) => INV(i+1)): prove Dom(head'_{i+1} :: ws_{i+1}, R_{i+1}), i.e.
  forall t: cLt(R_{i+1}, t) <= cLt(ws_{i+1}, t) + [head'_{i+1} < t].

I split t into THREE regions; TWO are handled, the MIDDLE one is the gap:
  (A) t > head'_{i+1}: RHS has the +1 head slot; follows from the pick-step's own Dom output
      (erasing q_i from INV(i)'s Dom gives Dom(ws_i, R_{i+1}) which suffices above the head).
  (B) t <= b+1: from shapeInv(i) + an achiever arithmetic fact (good_floor_core). DONE.
  (C) MIDDLE: b+1 < t <= head'_{i+1}. Here [head'_{i+1}<t]=0 so the target is the TIGHT
      cLt(R_{i+1}, t) <= cLt(ws_{i+1}, t). shapeInv only covers t<=b+1; the pick-step Dom only
      covers t>head'. NEITHER covers the middle. The bound HOLDS (0 fails) but I need the mechanism.

NUMERICAL FACTS I have established about the MIDDLE region (all 0 fails over 2643 exhaustive cases):
- Sub-split the middle by head'_i:
  * (C1) b+1 < t <= min(head'_i, head'_{i+1}): INV(i) is TIGHT here because t <= head'_i means
    [head'_i < t]=0, so cLt(R_i,t) <= cLt(ws_i,t). [verified: for ALL t<=head'_i, cLt(R_i,t)<=cLt(ws_i,t).]
  * (C2) head'_i < t <= head'_{i+1} (this requires head'_{i+1} > head'_i; head' is NOT monotone):
    in EVERY such case the just-erased pick q_i < t (verified 0/1249), so cLt(R_{i+1},t)=cLt(R_i,t)-1;
    and INV(i) gives cLt(R_i,t) <= cLt(ws_i,t) + 1 (head slot, since t>head'_i); combining:
    cLt(R_{i+1},t) <= cLt(ws_i,t) = cLt(ws_{i+1},t) + [M^{i+1}<t], and M^{i+1}<t holds here (0/1249),
    AND the chain bound cLt(R_i,t)-1 EQUALS cLt(ws_{i+1},t) exactly (slack 0, 1249/1249).
- In C2, also verified: q_i < head'_{i+1} (1249/1249).
- head'_{i+1} = max(u_{i+1}, M^{i+2}), u_{i+1} = M^{i+1} + u_i - q_i.
</task>

<output_contract>
1. For region C1 (t <= head'_i, the easy middle half): confirm the mechanism is exactly "INV(i) is tight
   below its own head, then erasing a pool element only decreases cLt" — but note this gives
   cLt(R_{i+1},t) <= cLt(R_i,t) <= cLt(ws_i,t) = cLt(ws_{i+1},t) + [M^{i+1}<t], which still has a +1 if
   M^{i+1}<t. Does C1 actually need M^{i+1} >= t (so the extra slot is 0), or is q_i<t forcing the -1
   here too? Pin the exact sufficient condition.
2. For region C2 (head'_i < t <= head'_{i+1}): the chain "q_i < t => cLt(R_{i+1},t)=cLt(R_i,t)-1" plus
   "INV(i) gives +1 head slot" works ONLY if q_i < t. Prove q_i < t in C2 from the definitions
   (head'_{i+1}=max(u_{i+1},M^{i+2}), u_{i+1}=M^{i+1}+u_i-q_i, t<=head'_{i+1}, t>head'_i>=u_i).
   Is "q_i < t" equivalent to / implied by a clean inequality on (u_i, q_i, M^{i+1}, M^{i+2})?
3. Give the SINGLE cleanest carrier that covers the WHOLE middle (C1+C2) uniformly, if one exists —
   e.g. "for t > b+1, cLt(R_{i+1},t) <= cLt(ws_{i+1},t)" proven by a uniform argument, rather than the
   two-way head'_i split. Does conservation u_{i+1} = (sum R_{i+1}) - (sum ws_i) give a uniform handle?
4. Flag any circularity (does proving q_i < t in C2 secretly need the very INV(i+1) we are proving?).
</output_contract>

<grounding_rules>
- Exact integers. Distinguish PROVED from CONJECTURE.
- The bound is TRUE numerically; I need the cleanest PROOF MECHANISM for the middle, especially a clean
  proof of "q_i < t" in C2 (region head'_i < t <= head'_{i+1}), and whether C1 needs M^{i+1}>=t.
- Prefer a uniform middle argument over the head'_i sub-split if one exists.
</grounding_rules>

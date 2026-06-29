<task>
An RLCT-comparability question. rlctAtOn_squeeze: if F,Φ ≥ 0 near 0, measurable, and ∃ c₁,c₂>0
with c₁Φ ≤ F ≤ c₂Φ on a neighborhood of 0, then RLCT(F)=RLCT(Φ).

I have (exact, at a 2-2-2 instance, coords reg=(u,v,w), spec=(p,q,x), core=(T0,T1), and fixed
nonzero CONSTANTS Zb,Yb that are "deepest-point block norms"):
  R'   = ( u+x+ux+pq ,  (1+u)v + p T1 ,  w(1+x) + q T0 )           (a residual vector)
  C    = ( (T0 - (Zb+w)p/(1+u)) (T1 - q(Yb+v)/(1+x)) )²            (a nonneg "core energy")
  Φ    = ‖R'‖² + C
  ΔR   = ( 0,  -Yb·pq/(1+x),  -Zb·pq/(1+u) )                       (a perturbation)
  F    = ‖R'+ΔR‖² + C        (same C as in Φ)

I want to know whether c₁Φ ≤ F ≤ c₂Φ holds on a small ball, and what controls c₁,c₂.

Key facts I have found:
- On the ray reg=0, core=0, x=0, p=q=t→0: F/Φ = (Yb²Zb²+Yb²+Zb²+1)/(Yb²Zb²+1), a CONSTANT in t
  (so F/Φ does NOT → 1; the naive (1±ε), ε→0 sandwich FAILS).
- That constant is finite for fixed Zb,Yb but → ∞ as Yb→∞ with Zb=0 (it equals Yb²+1 there).
- A random sample of small points with Zb,Yb ~ O(1) gives F/Φ ∈ [0.69, 1.26].
</task>

<output_contract>
1. Does a fixed-constant two-sided bound c₁Φ ≤ F ≤ c₂Φ hold on a small ball (c₁,c₂>0)?
   Distinguish: holds with c₁,c₂ depending on Zb,Yb (the fixed data) vs. fails (c₂→∞ or c₁→0
   as the point → 0 for FIXED Zb,Yb).
2. The danger ray shows F/Φ is a fixed constant (not →1). Is that a PROBLEM for rlctAtOn_squeeze,
   or fine (the lemma only needs SOME c₁,c₂>0, not c₁,c₂→1)?
3. Is there any ray (for FIXED Zb,Yb) where F/Φ → 0 or → ∞ as the point → 0? That would break it.
   Pay attention to: x (a spectator coord, weakly read by R'), and the locus where ‖R'‖→0 but C→0
   at a different rate. Give the worst ray or certify none exists.
4. Net: for a FIXED instance (Zb,Yb fixed finite), does RLCT(F)=RLCT(Φ) hold via comparability?
</output_contract>

<grounding_rules>
- Zb,Yb are FIXED nonzero constants (deepest-point data), NOT variables → 0.
- Keep "comparability with data-dependent constants" distinct from "universal 3/2 constant".
- Flag inference vs computation. A sharp verdict (holds / specific failing ray) is wanted.
</grounding_rules>

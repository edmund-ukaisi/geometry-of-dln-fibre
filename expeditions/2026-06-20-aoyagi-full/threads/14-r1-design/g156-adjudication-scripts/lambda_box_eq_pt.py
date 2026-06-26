print("="*78)
print("PREP for the general-M consult: does deepest_le reach EVERY v in Vz∩{F=0}?")
print("="*78)
print("""
deepest_le_of_homogeneous_core proves:  rlctAtOn F 0 <= rlctAtOn F v   via:
  (L1-a) ray-scaling-invariance: rlctAtOn F (t•v) = rlctAtOn F v for t in (0,1]  [F homogeneous]
  (L1-b) lsc at the ray limit:   rlctAtOn F 0 <= rlctAtOn F (s•v) for small s>0  [sSup/open-nbhd]
  combine: rlctAtOn F 0 <= rlctAtOn F v.
This holds for ANY v (the ray t•v -> 0 always; homogeneity needs no fibre condition).  So:

  KEY: deepest_le gives rlctAtOn F 0 <= rlctAtOn F v for EVERY v in the AMBIENT, not just the fibre.
       (homogeneity of F is global; the ray to 0 exists from every v.)

So the ORDERING leg covers every v in Vz automatically. NO stratification needed for the ORDERING.
The box-collapse (iii) is then:
  c' < rlctAtOn F 0  =>  (forall v in Vz)  c' < rlctAtOn F 0 <= rlctAtOn F v  => local-integ at v
  => finite subcover of compact (Vz cap {F=0})  => box-integ.

=> The general-M lambda_box = lambda_pt reduces to:
   (1) deepest_le: rlctAtOn F 0 <= rlctAtOn F v forall v  [PROVEN, homogeneity+lsc, value-free]
   (2) compactness of Vz cap {F=0} + gluing local-integ nbhds  [the NEW content]
   NO per-stratum rlct computation, NO 'smallest-rank stratum' lsc, NO stratification at all!
""")
print("REVISION of my earlier 'lsc on smallest-rank stratum' framing:")
print(" I previously framed lambda_box=lambda_pt as needing per-stratum rlct ordering (the")
print(" stratification argument). But deepest_le ALREADY gives the ordering for EVERY v via the")
print(" GLOBAL homogeneity ray -- no stratification, no 'which stratum binds'. The homogeneity of")
print(" the core F=||prod C||^2 (degree 2L) makes 0 the global-min-rlct point DIRECTLY.")
print(" So the general-M proof is NOT harder than the small cases -- it is the SAME two-line")
print(" homogeneity+lsc argument (dimension-uniform) + the compactness collapse.")
print()
print("THE ONLY genuine general-M question left: is the ratio box Vz cap {F=0} COMPACT?")
print(" Vz = argmax ratio box [-1,1]^d (closed, bounded => compact in R^d). {F=0} closed (F cts).")
print(" Vz cap {F=0} = closed subset of compact => COMPACT. YES, dimension-uniformly.")
print(" => the finite subcover EXISTS for every M. The collapse closes generally.")

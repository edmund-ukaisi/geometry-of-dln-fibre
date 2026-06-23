print("="*78)
print("CONFIRM deriv-finish's cone-vertex reconciliation + the box-localization worry")
print("="*78)
print("""
CLAIM 1 (cone vertex sees the min, via homogeneity): rlctAtOn(F,0) <= rlctAtOn(F,p) for all p.
  My stratification cert (Addendum 2): deepest = min via 'every stratum mval >= minAdm' (combinatorial,
  + cited rlct=½mval per stratum + Kostant).
  deriv-finish's route: same ordering via homogeneity ray + lsc (deepest_le_of_homogeneous_core).
  AGREE? YES. Both conclude rlctAtOn(F,0) <= rlctAtOn(F,p) for all p. They are INDEPENDENT derivations
  of the SAME ordering:
   - homogeneity route: F(t·w)=t^{2L}F(w) => rlctAtOn const on the ray t·p => lsc at 0 => 0 is min.
     This is the CLEANEST and needs NO Mval/Kostant/resolution. PURELY from homogeneity+lsc.
   - stratification route: per-stratum value = ½mval >= ½minAdm = the vertex value (cited).
  The homogeneity route is STRICTLY BETTER for #11 (no cite, in-engine). My stratification stays as
  the decorrelated CROSS-CHECK that the ordering is true (it is, both ways).
  NO CASE where they disagree: homogeneity gives <= for EVERY p (no stratum structure needed); the
  stratification gives the same with the per-stratum values. Same inequality, two proofs.
""")
print("CLAIM 2 (box-localization non-issue): does 'deepest=min over the bounded box Vz' follow?")
print("""
  rlctAtOn(F, w*) is a GERM at w* (sup over admissible c' with |F|^{-c'} integ on SOME nbhd of w*).
  => rlctAtOn(F, w*) does NOT depend on any box Vz; it is intrinsic to the point w*. CORRECT.
  The box enters ONLY in the box-COLLAPSE (the finite-subcover step), NOT in the ordering:
   - the ORDERING rlctAtOn(F,0) <= rlctAtOn(F,p) is point-vs-point, box-free. (homogeneity, global.)
   - the box-COLLAPSE uses: for c' < rlctAtOn(F,0), and EACH p in Vz∩{F=0}, since rlctAtOn(F,p) >=
     rlctAtOn(F,0) > c', p has a nbhd W_p with |F|^{-c'} integ [germ def]. Vz∩{F=0} compact =>
     finite subcover => box-integ. The box Vz only supplies COMPACTNESS; it does NOT change any
     rlctAtOn value. So restricting to Vz does NOT 'change which strata are present' in any way that
     matters -- every p IN Vz still has its intrinsic rlctAtOn(F,p) >= rlctAtOn(F,0). NON-ISSUE. CONFIRMED.
""")
print("ONE precision (the only place to be careful): the ordering must hold for every p in the CLOSURE")
print("of Vz∩{F=0} that the finite subcover touches -- but the homogeneity ordering is GLOBAL (all p),")
print("so it covers the closure trivially. And points p in Vz with F(p)!=0 are not singular: |F|^{-c'}")
print("is bounded near them => locally integ for free. So the subcover handles {F=0}∩Vz (compact) +")
print("the open {F!=0}∩Vz (bounded integrand). Both fine. The box-restriction is a NON-ISSUE.")
print()
print("VERDICT: deriv-finish's cone-vertex route is CORRECT, agrees with my stratification cert on the")
print("ordering, is the BETTER (cite-free) route, and the box-localization worry is dissolved by the")
print("germ-locality of rlctAtOn (the box only supplies compactness for the subcover, never a value).")

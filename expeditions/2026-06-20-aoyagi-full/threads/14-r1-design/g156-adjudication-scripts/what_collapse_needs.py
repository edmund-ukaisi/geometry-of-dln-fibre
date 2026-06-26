print("="*78)
print("PRECISELY what does the box-collapse consume? (the value-CLOSING step in GE)")
print("="*78)
print("""
The GE leg closes the recursion to  rlctOf(node) = min{mk/2, n/2 + rlctOf(child)}.
The candidate bridge:  IntegrableOn |F|^{-c'} Vz  <=  c' < rlctAtOn F deepest.
                       (the '<=' direction: below the deepest-threshold => box-integrable.)

Decompose the box integral over Vz∩{F=0} by LOCAL behavior at each point v:
  int_{Vz} |F|^{-c'} < inf   <=   for EVERY v in Vz, exists nbhd W_v with int_{W_v}|F|^{-c'}<inf
                                  (finite subcover of compact Vz).
  int_{W_v}|F|^{-c'} < inf    <=   c' < rlctAtOn(F, v)   [DEFINITION of rlctAtOn as the sup].

So the box-collapse '<=' direction needs:  for every v in Vz,  c' < rlctAtOn(F, v).
Given c' < rlctAtOn(F, deepest), this follows IFF  rlctAtOn(F, deepest) <= rlctAtOn(F, v) for all v.
                                                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                                                    THE ORDERING. Value-free. = deepest_le.

=> The box-collapse '<=' direction consumes ONLY the ORDERING rlctAtOn(F,deepest) <= rlctAtOn(F,v).
   It does NOT consume "rlctAtOn(F,deepest) = 1/2 minAdm" -- NO minAdm, NO mval, NO realizer.
   The VALUE 1/2 minAdm enters the headline SEPARATELY (the spine value side / the y0-divisor mk/2 +
   the recursion), NOT through the box-collapse bridge.
""")
print("CONCLUSION: deriv-finish does NOT need 'deepest realizes minAdm' for #11.")
print("  The bridge needs the ORDERING only (deepest_le, PROVEN value-free).")
print("  'deepest realizes minAdm' = rlct(deepest)=1/2 minAdm = the HEADLINE itself -- using it would")
print("  be CIRCULAR. So it must NOT appear in #11.  It is NOT a 'fourth cited hyp' to add; it is the")
print("  conclusion the whole edifice proves, kept OUT of the bridge.")
print()
print("What about the '=>' direction (box-integ => c' < rlct(deepest))?  The GE leg only needs '<='")
print("(below-threshold => finite => rlctOf >= ...).  The matching '<=' on rlctOf (the LE leg / value")
print("upper bound) is a SEPARATE object (the y0-divisor cap mk/2 + child), not this bridge.")

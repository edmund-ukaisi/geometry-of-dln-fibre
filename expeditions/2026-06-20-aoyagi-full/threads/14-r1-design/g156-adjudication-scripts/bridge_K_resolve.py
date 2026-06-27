print("="*78)
print("Does BoxThresholdBridge get instantiated at K=core (non-homog) or K=dlnLoss N 0 (homog)?")
print("="*78)
print("""
The docstring says: 'proved in the deriv-finish lane for K = dlnLoss N 0' and 'the GE producer can
instantiate it at K = core (and the recursion descends it to the child)'.

KEY TENSION I must resolve honestly:
 - BoxThresholdBridge needs K's ordering: rlctAtOn(K,0) <= rlctAtOn(K,w) for all w in Vz (then finite
   subcover gives box-integ). This is what 'deepest=global-min-rlct' provides.
 - For K = dlnLoss N 0 (the RAW child loss, homogeneous degree 2L): deepest_le_of_homogeneous_core
   PROVES rlctAtOn(K,0) <= rlctAtOn(K,w) for ALL w (global homogeneity ray). So BoxThresholdBridge
   (dlnLoss N 0) is provable: K-ordering [deepest_le, homog] + finite subcover. CLEAN, value-free.
 - For K = core (the ratio-coord post-blowup, NOT homogeneous): deepest_le does NOT apply (my caught
   error). So BoxThresholdBridge(core) is NOT directly provable via homogeneity.

RESOLUTION: which K does the GE producer ACTUALLY need the bridge at?
 chart_pullback_lt_top_of_bridge consumes BoxThresholdBridge K with K = the chart's core function.
 The chart core = core = ||Ahat B||^2 (ratio coords) -- NON-homogeneous. So the GE leg as wired needs
 BoxThresholdBridge(core), which deepest_le does NOT give.

 BUT: the recursion's INNER squeeze relates core to dlnLoss(child) (the homogeneous raw child loss):
 core ≍ Phi = sum Erow^2 + dlnLoss(child) near 0.  IF the bridge is applied at K=dlnLoss(child)
 (homogeneous, deepest_le applies) and the squeeze + Morse-block transfer carries box-integ from
 dlnLoss(child) up to core, THEN the recursion closes.  That transfer (squeeze uniform on box +
 additive Morse) is the remaining glue.

HONEST general-M open piece (the consult target), now PRECISE:
 EITHER (A) BoxThresholdBridge(core) directly -- needs core's K-ordering over Vz (core non-homog;
            the structural 'rank-1 Ahat at 0 = most vanishing' argument; NOT closed), 
 OR     (B) BoxThresholdBridge(dlnLoss child) [PROVABLE: deepest_le homog + subcover] + a transfer
            core-box-integ <= child-box-integ via the uniform-on-box squeeze + Morse additivity.
 (B) is the clean route IF the squeeze is uniform on the box. The squeeze uniformity on the box is the
 crux -- and schur_node_squeeze_unif (the only 'unif' squeeze) is the L2 R-core object, NOT the R1
 single-step child. So the R1 uniform-on-box squeeze for core ≍ sum Erow^2 + dlnLoss(child) may NOT
 yet exist as a sound R1 lemma.
""")
print("=> THE PRECISE OPEN PIECE for deriv-finish/the consult:")
print("   (1) BoxThresholdBridge(dlnLoss N 0) for the HOMOGENEOUS raw loss: PROVABLE now")
print("       (deepest_le_of_homogeneous_core + finite-subcover). This is the clean #11 core.")
print("   (2) The lift from BoxThresholdBridge(child) to hKint(core): needs the R1 uniform-on-box")
print("       squeeze core ≍ sum Erow^2 + dlnLoss(child). Whether that squeeze is box-uniform (not just")
print("       local) and is the SINGLE-STEP child (not the L2 R-core) is the load-bearing check.")

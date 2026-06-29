# Reconcile: when is the leaf LIVE (Text_L > 0) vs empty (Text_L=0)?
# The live-leaf decoder genBlkFlatLiveR1 sets Rfin_L = rfin (Text_L x Wext_L). If Text_L=0, that's empty.
# At (3,3,3,3): tach3333=[3,2,1,0], Text=[3,3,2,1,0]. Text_3 (=Text_L, L=3) = tach[2]=1 >0 -> LIVE leaf 1x3.
# At (3,3,3,3,3): L=4. The achiever ap=(2,1,0). tach=[3,2,1,0,0]. Text_4=tach[3]=0 -> EMPTY leaf.
# So the LEAF is live iff the LAST genuine drop > 0. For (3,3,3,3) the drops bottom at 1 (Text_3=1).
# For (3,3,3,3,3) the drops go (2,1,0) -> bottoms at 0.
# BUT WAIT: the live-leaf 'R1' variant FIXES an interior pivot at p (the InteriorDrop p*), making the leaf
# the residual. Let me check: the budget identity (Check 2) gave (3,3,3,3,3): E=6, leaf=0, total=6=minAdm.
# So at (3,3,3,3,3) the leaf IS empty and ALL minAdm-1=5 free u-scaled coords are E-block entries (interior).
# The C_{L} block (s=L-1 chain) is then EMPTY (0 rows) -> chain_{L-1}'s C-block is 0xWext_L -> the chaining
# A_{L-1} = [empty ; W_{L-1}] = W_{L-1} (all lift). So chain_{L-1} is then the IDENTITY on W (trivial).
print("LEAF LIVENESS depends on M (whether the last genuine drop Text_L > 0):")
print("  (3,3,3,3): Text_L=Text_3=1 > 0  => LIVE leaf (1x3), C_L=u*Rfin nonempty, chain_2 reads it.")
print("  (3,3,3,3,3): Text_L=Text_4=0    => EMPTY leaf, C_L empty (0x3), chain_3 = identity-on-W (trivial).")
print()
print("So the s=L-1 'leaf branch' has TWO sub-cases:")
print("  Text_L>0 (live leaf): C_L = u*Rfin, the chain reads the live-leaf coords.")
print("  Text_L=0 (empty leaf): C_L empty, chain_{L-1} kept-block vacuous, only W lift -> trivial chain.")
print("BUT: in BOTH, C_{s+1} = the KEPT-ROW block of layer s (first Text_{s+1} rows). The leaf is just")
print("  the s=L-1 instance where C_L's CONTENT is u*Rfin (live) or empty. The REINDEX is UNIFORM:")
print("  C_{s+1} = layer-s kept rows, ∀ s incl L-1. The leaf is NOT a separate reindex — same kept-row split.")

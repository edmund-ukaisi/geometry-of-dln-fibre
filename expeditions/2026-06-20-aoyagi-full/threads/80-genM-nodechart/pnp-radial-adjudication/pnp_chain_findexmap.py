# Pin the EXACT Fin index map for E_chain_s. 
# chain_s acts on (W_s, C_{s+1}) and outputs (W_s, C_{s+1} - N_s W_s), which IS the rearrangement of
# layer-s's output A_s = chainA(N_s, W_s, C_{s+1}) = [C_{s+1}-N_s W_s ; W_s] (kept over lift).
# So chain_s's NATURAL domain/codomain is layer-s's flat block: Fin(Wext_s * Wext_{s+1}).
# The split: row index r in Fin(Wext_s) splits via finSplit(Text_{s+1} <= Wext_s):
#   r = castAdd: kept row i in Fin(Text_{s+1}) -> the C_{s+1} block row i
#   r = natAdd:  lift row a in Fin(c_s), c_s = Wext_s - Text_{s+1} -> the W_s block row a
# col index j in Fin(Wext_{s+1}) is shared.
# So E_chain_s : (Fin N -> R) ≃L (W-block × C-block) × R, where:
#   the (W,C) blocks are read from layer-s's flat positions:
#     C_{s+1}[i,j] <- flat( layer s, row = Fin.cast (castAdd_{c_s} i), col = j ),  i in Fin Text_{s+1}
#     W_s[a,j]     <- flat( layer s, row = Fin.cast (natAdd_{Text_{s+1}} a), col = j ), a in Fin c_s
#   R = all OTHER flat coords (the other layers + the bare-pivot region).
# This is EXACTLY the FlatIdx layer-s block + the finSplit(Text_{s+1}) kept/lift row split. 
# The "shift" the controller worried about (C_{s+1} = NEXT boundary's C) is ALREADY ABSORBED: C_{s+1} lives
# in layer s's KEPT rows (an output position), NOT a fresh slot at boundary s+1. The shift s -> s+1 in the
# NAME C_{s+1} is a red herring at the reindex level: it's just "layer s's kept rows".
print("EXACT Fin index map for E_chain_s (operating on layer-s FLAT block):")
print("  domain = layer-s flat block Fin(Wext_s * Wext_{s+1}), reindexed (FlatIdx layer s).")
print("  row split via finSplit (h: Text_{s+1} + c_s = Wext_s):")
print("    C_{s+1}[i,j] = block(Fin.cast h (Fin.castAdd c_s i), j),  i:Fin Text_{s+1}, j:Fin Wext_{s+1}")
print("    W_s[a,j]     = block(Fin.cast h (Fin.natAdd Text_{s+1} a), j), a:Fin c_s")
print("  col j:Fin Wext_{s+1} shared. R = the complementary flat coords.")
print()
print("=> E_chain_s is FLATIDX-derived (layer-s block + finSplit row-split), NOT ChartIdx-derived.")
print("   This CORRECTS my earlier 'chartIdxEquiv + C_{s+1} slot' answer: the C-block is an OUTPUT/FLAT")
print("   position (layer-s kept rows), reusing the BANKED chainA_apply_castAdd/_natAdd finSplit laws.")
print("   The 's->s+1 shift' is absorbed: 'C_{s+1}' = 'layer-s kept rows' = a fixed finSplit on layer s.")
print("   No cross-boundary shift in the reindex; the shift is only in the CONTENT (built by deeper factors).")

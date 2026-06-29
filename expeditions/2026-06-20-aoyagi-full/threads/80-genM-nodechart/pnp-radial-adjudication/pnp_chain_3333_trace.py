import sympy as sp
# Build (3,3,3,3) and trace where each C_{s+1} block sits in the flat (FlatIdx) output and how chain_s's
# C-block reindexes. Text=[3,3,2,1,0]? No: Text=[3,3,2,1] for the chain (Text_L=Text_3=1, the live leaf).
# Layers A_0 (3x3, Wext0 x Wext1), A_1 (3x3), A_2 (3x3). FlatIdx packs them: layer0 entries 0..8, layer1 9..17, layer2 18..26.
# C_1 = transition into A_0 kept rows: A_0 = [C_1 - N_0 W_0 ; W_0], c_0=0 so A_0 = C_1 (all 3 rows). C_1 shape Text_1 x Wext_1 = 3x3.
#   But Text_1=3, so C_1 occupies ALL of A_0 (3x3). chain_0 is trivial (c_0=0, no lift). 
# C_2 = transition into A_1: A_1 = [C_2 - N_1 W_1 ; W_1]. Text_2=2 kept rows (C_2 - N_1 W_1) + c_1=1 lift row (W_1).
#   C_2 shape Text_2 x Wext_2 = 2x3. It sits in A_1's first 2 rows (rows of layer1).
# C_3 = u*Rfin: A_2 = [C_3 - N_2 W_2 ; W_2]. Text_3=1 kept row + c_2=2 lift rows. C_3 shape 1x3, in A_2's first row.
# 
# So chain_s reads C_{s+1} from layer-s's KEPT-ROW block. As FLAT indices (FlatIdx layer s, kept rows):
#   chain_0: C_1 = layer0 rows 0..2 (all), cols 0..2 -> flat 0..8.
#   chain_1: C_2 = layer1 kept rows 0..1, cols 0..2 -> flat 9,10,11, 12,13,14 (rows 0,1 of layer1's 3x3).
#   chain_2: C_3 = layer2 kept row 0, cols 0..2 -> flat 18,19,20.
# And W_s (the lift) sits in layer-s's LIFT rows:
#   chain_1: W_1 = layer1 lift row 2, cols 0..2 -> flat 15,16,17.
#   chain_2: W_2 = layer2 lift rows 1,2 -> flat 21..26.
print("(3,3,3,3) chain_s C-block FLAT positions (layer s kept rows):")
print("  chain_0: C_1 = layer0 all rows (Text_1=3) -> flat 0..8  (c_0=0, no lift; trivial chaining)")
print("  chain_1: C_2 = layer1 kept rows 0,1 (Text_2=2) -> flat 9,10,11,12,13,14 ; W_1 = layer1 row2 -> 15,16,17")
print("  chain_2: C_3 = layer2 kept row 0 (Text_3=1) -> flat 18,19,20 ; W_2 = layer2 rows1,2 -> 21..26")
print()
print("KEY: C_{s+1} is the KEPT-ROW block of layer s = the first Text_{s+1} rows of layer s's Wext_s x Wext_{s+1} matrix.")
print("As a FlatIdx reindex: C_{s+1}[i,j] = flat coord of (layer s, row castAdd i (of Wext_s), col j (of Wext_{s+1})).")

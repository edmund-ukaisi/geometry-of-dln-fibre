# Understand WHAT C_{s+1} is as ambient coords, and how chain_s reads it.
# Key realization: In the composeFold, chain_s is NOT reading C_{s+1} from a fixed coordinate slot.
# C_{s+1} is the OUTPUT of the deeper factors (schur_{s+1} etc.) sitting in the ambient AT boundary s+1's
# OUTPUT-row positions. The chain_s factor (W_s, C_{s+1}) -> (W_s, C_{s+1} - N_s W_s) reads:
#   - W_s from boundary s's LIFT slot (a chart coordinate, via chartIdxEquiv lift slot), 
#   - C_{s+1} from ... where the deeper composeFold factors have PLACED the C_{s+1} matrix.
#
# CRITICAL design question: in the chart, A_s = [C_{s+1} - N_s W_s ; W_s]. The matrix A_s is layer-s's
# output (rows Fin Wext_s, cols Fin Wext_{s+1}). The C_{s+1} block occupies the KEPT rows (first Text_{s+1})
# of A_s. So C_{s+1} (as it enters chain_s) IS the kept-row block of layer s's output BEFORE the -N_s W_s shear.
# And C_{s+1} itself = Schur frame of boundary s+1 = [[K,KN],[XK,XKN+E]] which is layer (s+1)'s C... 
# NO -- C_{s+1} has shape Text_{s+1} x Wext_{s+1}. Layer s+1's output A_{s+1} has shape Wext_{s+1} x Wext_{s+2}.
# These are DIFFERENT. So C_{s+1} is NOT layer s+1's output.
#
# C_{s+1} = Bmat_{s+1} chainQ(N_{s+1}) + u Rmat_{s+1}: shape Text_{s+1} x Wext_{s+1}. It is the "transition"
# block, built FROM boundary s+1's frame data (K_{s+1},X,N,E) — which are boundary s+1's CHART COORD slots.
# So C_{s+1} is a FUNCTION of boundary (s+1)'s frame coords, NOT a separate coordinate slot.
#
# => In composeFold, the deeper factors (ldu_{s+1}, chain_{s+1}, schur_{s+1}) BUILD C_{s+1} from bd(s+1)'s
#    coords and place it where chain_s reads it. The "C-block slot" that E_chain_s reads is the OUTPUT
#    region of the schur_{s+1} factor = the kept-row block of layer s's matrix A_s.
print("C_{s+1} shape = Text_{s+1} x Wext_{s+1} (the transition block).")
print("It is BUILT by boundary (s+1)'s factors (schur_{s+1} outputs the frame whose top is C_{s+1}).")
print("So chain_s reads C_{s+1} from the OUTPUT region of the deeper composeFold prefix, i.e. layer s's")
print("kept-row block positions (Fin Text_{s+1} rows x Fin Wext_{s+1} cols), NOT a fresh coordinate slot.")

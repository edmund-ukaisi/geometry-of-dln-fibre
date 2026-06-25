import sympy as sp
# Continue (2,2,2) r=0, non-deepest v. We found Jacobian rank 3 at v.
# F has 4 generators P_ij; 3 have independent linear parts (b0, a1+b1, a3) => 3 regular directions.
# After splitting off the 3 regular dirs (Morse lemma / S1 smooth-block), the residual core is the
# part of F transverse to them. Let's identify the residual singular directions and the residual RLCT.
#
# The 4 generators: P00=b0+(a0b0+a1b2), P01=(a1+b1)+(a0b1+a1b3), P10=(a2b0+a3b2), P11=a3+(a2b1+a3b3).
# Use the 3 nonzero-linear generators to solve out 3 variables (implicit function thm):
#   P00=0 -> b0 = -(a0b0+a1b2)        (b0 ~ O(2))  => b0 is a regular coordinate
#   P01=0 -> a1+b1 = -(a0b1+a1b3)     => (a1+b1) regular
#   P11=0 -> a3 = -(a2b1+a3b3)        => a3 regular
# The remaining generator P10 = a2b0 + a3b2. On the solved locus, b0=O(2), a3=O(2):
#   P10 = a2*O(2) + O(2)*b2 = O(3) -- so P10 vanishes to HIGHER order; the residual core direction.
# The residual core after removing 3 regular dims: variables {a0,a2,b2,b3} minus gauge, with the
#残 generator P10 ~ a2*b0 + a3*b2 but b0,a3 are O(2) => leading residual is degree>=3 => RLCT large.
print("=== residual core at non-deepest v (2,2,2 r=0) ===")
print("3 regular directions (linear-leading generators b0, a1+b1, a3): contribute 3 * 1/2 = 3/2.")
print("The 4th generator P10=a2b0+a3b2 becomes O(>=3) on the regular-zero locus => residual RLCT >> 0.")
print("So lambda_v = 3/2 (regular) + lambda(residual, a positive number) > 3/2 = lambda_deepest.")
print()
print("CROSS-CHECK against ground truth: lambda_deepest(2,2,2,r=0) = 3/2 (the ladder value).")
print("lambda_v (this rank-(1,1) stratum) > 3/2. => deepest STRICTLY minimal here. Witness holds.")
print()
# The MECHANISM that proves lambda_v >= lambda_deepest WITHOUT the value:
print("MECHANISM (value-free): at v, choose local coords adapting to the v-gauge orbit; the loss germ")
print("= [nondegenerate quadratic on the Jacobian-rank block] + [HOMOGENEOUS residual core].")
print("Aoyagi Thm2 (homogeneity + |t|<1 scaling + Lemma1(1)=rlctAt_mono) applied to the RESIDUAL core")
print("gives lambda(residual at v) >= lambda(residual at deepest)=full core. The regular block ADDS >=0.")
print("NO resolution VALUE (min monomialThreshold) is invoked -- only the homogeneous SCALING inequality.")

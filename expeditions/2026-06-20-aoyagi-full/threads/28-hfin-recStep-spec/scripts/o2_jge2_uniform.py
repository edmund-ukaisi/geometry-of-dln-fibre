import sympy as sp
# Q4 j>=2 closure: is the shear term M21*M11^{-1}*M12 in a FIXED box (spectator-uniform)?
# Sc = M22 - M21*M11^{-1}*M12. |M22 entry| <= 1.
# M21*M11^{-1} = the row-shear A: by the Cramer minor-ratio bound (N2a, rowShear_entry_le_one,
#   ALREADY PROVED in RouteMSchurShear.lean), |A[a,b]| <= 1 on the max-modulus-minor cell.
# So (M21*M11^{-1}*M12)[a,b] = sum_{k} A[a,k]*M12[k,b], with |A[a,k]|<=1, |M12[k,b]|<=1, j terms:
#   |(shear)[a,b]| <= j * 1 * 1 = j.   So |Sc[a,b]| <= 1 + j.
# Sc-box ⊆ [-(1+j), 1+j]^{(r-j)^2}, a FIXED box (depends on r,j only, NOT on the specific R).
print("=== j>=2 box bound (Q4 NEEDS-CARE closure, via the PROVED Cramer shear bound N2a) ===")
print("Sc[a,b] = M22[a,b] - (M21·M11⁻¹·M12)[a,b].")
print("|M22[a,b]| <= 1 (R-entry on chart).")
print("Row-shear A = M21·M11⁻¹: |A[a,k]| <= 1 by Cramer minor-ratio (N2a, rowShear_entry_le_one, PROVED).")
print("(M21·M11⁻¹·M12)[a,b] = Σ_{k=1..j} A[a,k]·M12[k,b], |·| <= j·1·1 = j.")
print("=> |Sc[a,b]| <= 1 + j.   Sc-box ⊆ [-(1+j),1+j]^{(r-j)²}, a FIXED spectator-independent box.")
print()
print("So the j>=2 case CLOSES: the M22->Sc translation Jac=1 (verified), AND the shear term lies in")
print("a fixed box BY THE ALREADY-PROVED Cramer bound. The free Sc-box (now side 2(1+j)) core is the")
print("corank-(r-j) IH (box-side a harmless constant factor 2^{(r-j)²-2c'} per the rescale lemma).")
print("Codex's j>=2 'NEEDS-CARE if M11^{-1} unbounded' is precisely the Cramer bound, which IS proved.")

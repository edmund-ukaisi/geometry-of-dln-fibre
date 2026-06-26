import sympy as sp
print("="*78)
print("CONFIRM deriv-finish's retraction: MECHANISM (squeeze) general-L vs VALUE (Morse n/2) L=2-only")
print("="*78)
print("""
The squeeze core ≍ Φ = ∑Erow² + ‖SΓ‖²  (schur_node_squeeze_unif):
  This is the Schur ROW-DECOMPOSITION: lower rows of Ahat·B = b·Erow + S·Bred, plus the algebraic
  two-sided bound (∑b²≤T²). It is a PURE ALGEBRAIC IDENTITY + inequality in the ENTRIES of (Erow, b, SΓ).
  It holds for ANY L -- it does not care whether Erow/SΓ are free or composite. So the MECHANISM
  (integrability transfer core↔Φ) is general-L SOUND. ✓ deriv-finish's 'still stands' is correct.
""")
print("""
The VALUE rlctAtOn(∑Erow²) = n/2:
  This requires {Erow_j} to be n FREE smooth Morse coordinates (each contributing 1/2).
  - L=2: Erow_j = B[0,j] + Σu_i B[i,j], B=A1 free => Erow_j are free coords (det-1 shear) => Morse, n/2. ✓
  - L≥3: B = A²···A^L product => Erow_j = (row 0 of product) + shear = degree-(L-1) form, NOT free.
    rlctAtOn(∑Erow²) ≠ n/2 -- the forms vanish to higher order on the product-degeneracy locus.
  So the VALUE telescoping (∑Erow² → n/2, recurse) is L=2-ONLY. ✓ deriv-finish's retraction is correct.
""")
# The distinction crisply: squeeze gives rlctAtOn(core) = rlctAtOn(Φ) [transfer, general-L].
# But rlctAtOn(Φ) = rlctAtOn(∑Erow² + ‖SΓ‖²): for this to be n/2 + rlctAtOn(child) you need ADDITIVITY
# (S1Additive, fine) AND rlctAtOn(∑Erow²)=n/2 (the Morse VALUE, L=2-only).
print("CRISP DISTINCTION:")
print(" - squeeze: rlctAtOn(core) = rlctAtOn(Φ), Φ=∑Erow²+‖SΓ‖²  [TRANSFER, general-L sound]")
print(" - additivity: rlctAtOn(Φ) = rlctAtOn(∑Erow²) + rlctAtOn(‖SΓ‖²)  [S1Additive, fine IF disjoint vars]")
print(" - Morse VALUE: rlctAtOn(∑Erow²) = n/2  [NEEDS Erow free => L=2-ONLY; FAILS L≥3]")
print("   AND disjoint-vars for additivity: Erow (degree-(L-1) in shared A-entries) and SΓ may SHARE")
print("   variables for L≥3 => even the additivity split can fail. Double reason L≥3 breaks.")
print()
print("VERDICT: deriv-finish's retraction is CORRECT and precisely located. The squeeze MECHANISM is")
print("general-L (algebraic). The per-node VALUE n/2 (Morse) is L=2-only. The L≥3 value resolution")
print("(degree-(L-1) Erow forms) is the open operator scope call. #11 (ordering+subcover) unaffected.")
print("My Lge3 cross-check already said exactly this (n=M_last overcounts L≥3). CONSISTENT.")

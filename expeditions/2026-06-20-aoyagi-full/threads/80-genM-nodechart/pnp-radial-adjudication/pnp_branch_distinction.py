import sympy as sp
print("="*70)
print("CRITICAL: two radial models. Which applies to the INTERIOR (brief) branch?")
print("="*70)
# (3,3,3,3): is it 'clean' (NoInteriorBothDrop) or genuinely interior?
# Drops T* = (2,1,0): boundary 1 drops 3->2, boundary 2 drops 2->1, leaf 1->0. 
# 'Interior both-drop' = an interior boundary where BOTH the front and the rank drop. 
# deepestCoords would put active = entire deepest layer A2 (M_{L-1}*M_L = 3*3 = 9 coords).
# But minAdm(3333)=6 != 9. So deepestCoords_card_eq_minAdm FAILS for (3,3,3,3) (hclean false).
print("(3,3,3,3): deepest factor A2 dim = M_{L-1}*M_L = 3*3 =", 3*3, " but minAdm =", 6)
print("   => deepestCoords (card 9) != minAdm (6). The CLEAN model does NOT apply.")
print("   => (3,3,3,3) is INTERIOR; radial active = {u-scaled E/leaf} (card 6), spread across boundaries.")
print()
# (4,4,2,2): clean. deepest A2 dim = M_2*M_3 = 2*2 = 4 = minAdm(4422)=4. CLEAN model applies, active=A2.
print("(4,4,2,2): deepest A2 dim = M_2*M_3 = 2*2 =", 2*2, " == minAdm =", 4, " => CLEAN, active = whole A2.")
print()
# (2,2,2): deepest A1 dim = M_1*M_2 = 2*2 = 4, minAdm=3. 4 != 3 => NOT clean by deepest-factor!
print("(2,2,2): deepest A1 dim = M_1*M_2 =", 2*2, " but minAdm =", 3, " => NOT the deepest-factor model.")
print("   => (2,2,2) radial active = {0,6,7} (card 3 = minAdm), the u-scaled E/leaf model. CONFIRMED interior-type.")

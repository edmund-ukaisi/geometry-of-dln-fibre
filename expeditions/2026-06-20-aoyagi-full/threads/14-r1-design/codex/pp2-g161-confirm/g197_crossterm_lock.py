import sympy as sp
# LOCK the precision: does the abstract squeeze absorb the cross-term ⟨Rcore,leak⟩, OR does it need its
# own bound? cobuild-sub34: squeeze_bounds_abstract with p=leak, s=Rcore, p+s=P11, only ∑p²≤t²∑E². 
# The squeeze target: loss = ∑E² + ‖P11‖² = ∑E² + ‖s+p‖², want ≍ ∑E² + ‖s‖² (= ∑E²+‖Rcore‖²).
#
# ‖s+p‖² = ‖s‖² + 2⟨s,p⟩ + ‖p‖². The question: is ∑E² + ‖s+p‖² ≍ ∑E² + ‖s‖² from ‖p‖²≤t²∑E² ALONE?
# UPPER: ‖s+p‖² ≤ (‖s‖+‖p‖)² ≤ ‖s‖²(1+δ) + ‖p‖²(1+1/δ) [Young], and ‖p‖²≤t²∑E². So
#   ∑E²+‖s+p‖² ≤ ∑E²(1+t²(1+1/δ)) + ‖s‖²(1+δ). Bounded by c₂(∑E²+‖s‖²), c₂=max(1+t²(1+1/δ),1+δ). ✓
# LOWER: ‖s+p‖² ≥ ‖s‖² − 2‖s‖‖p‖ ≥ ‖s‖²(1−δ) − ‖p‖²/δ ≥ ‖s‖²(1−δ) − t²∑E²/δ. So
#   ∑E²+‖s+p‖² ≥ ∑E²(1−t²/δ) + ‖s‖²(1−δ) ≥ c₁(∑E²+‖s‖²) for t small (1−t²/δ>0). ✓
# CRUCIAL: BOTH bounds use ONLY ‖p‖²≤t²∑E² (the cross 2⟨s,p⟩ is handled by Young's |2⟨s,p⟩|≤δ‖s‖²+‖p‖²/δ,
# which only needs ‖p‖² bounded — NO separate ⟨s,p⟩ bound). So cobuild-sub34 is RIGHT.
print("LOCK: does the abstract squeeze absorb the cross-term, or need a separate ⟨Rcore,leak⟩ bound?")
print()
print("Squeeze target: ∑E² + ‖P11‖² ≍ ∑E² + ‖Rcore‖², with P11 = Rcore + leak (s+p), ‖leak‖²≤t²∑E².")
print()
print("‖s+p‖² = ‖s‖² + 2⟨s,p⟩ + ‖p‖². Young: |2⟨s,p⟩| ≤ δ‖s‖² + ‖p‖²/δ (any δ>0) — uses ONLY ‖p‖, ‖s‖.")
print("UPPER: ∑E²+‖s+p‖² ≤ ∑E²(1+t²(1+1/δ)) + ‖s‖²(1+δ) = c₂(∑E²+‖s‖²). [needs only ‖p‖²≤t²∑E²]")
print("LOWER: ∑E²+‖s+p‖² ≥ ∑E²(1−t²/δ) + ‖s‖²(1−δ) = c₁(∑E²+‖s‖²), c₁>0 for t,δ small. [same]")
print()
print("⟹ The cross-term 2⟨s,p⟩ is ABSORBED by Young's inequality using ONLY ‖p‖²≤t²∑E². NO separate")
print("   ⟨Rcore,leak⟩ bound needed. cobuild-sub34 is RIGHT: squeeze_bounds_abstract(p=leak,s=Rcore) needs")
print("   just (a) the split P11=leak+Rcore and (b) ∑leak²≤t²∑E². The cross-term is NOT a third hypothesis.")
print()
# Numeric sanity: verify c₁,c₂ exist (the squeeze holds) on the L=2 case at small t.
import random
x = sp.symbols('a0:8', real=True)
C1 = sp.Matrix([[1+x[0],x[1]],[x[2],x[3]]]); C2 = sp.Matrix([[1+x[4],x[5]],[x[6],x[7]]])
P = sp.expand(C1*C2); P00=P[0,0]; P01=P[0,1]; P10=P[1,0]; P11=P[1,1]
E00=P00-1; leak=sp.simplify(P10*P00**(-1)*P01); Rcore=sp.simplify(P11-leak)
loss = sp.expand((P00-1)**2 + P01**2 + P10**2 + P11**2)
phi = sp.expand((P00-1)**2 + P01**2 + P10**2 + Rcore**2)  # ∑E²+‖Rcore‖²
print("Numeric loss/phi (= loss/(∑E²+‖Rcore‖²)) at decreasing scale (should → [c₁,c₂] band → 1):")
for sc in [0.2, 0.08, 0.02]:
    rs=[]
    for _ in range(400):
        s={v:sc*random.uniform(-1,1) for v in x}
        pv=float(phi.subs(s)); lv=float(loss.subs(s))
        if pv>1e-12: rs.append(lv/pv)
    print(f"  scale {sc}: loss/phi ∈ [{min(rs):.4f}, {max(rs):.4f}]  (band tightens to 1 ⟹ squeeze, c₁<c₂→1)")

print()
print("="*68)
print("CROSS-TERM LOCK CONFIRMED: the abstract squeeze (squeeze_bounds_abstract)")
print("absorbs 2⟨Rcore,leak⟩ via Young |2⟨s,p⟩|≤δ‖s‖²+‖p‖²/δ, using ONLY ‖leak‖²≤t²∑E².")
print("⟹ core_comparability_squeeze (#54) takes EXACTLY 2 hypotheses:")
print("   (a) the split P11 = leak + Rcore")
print("   (b) ∑leak² ≤ t²·∑E²  (t=‖pivot‖→0)")
print("The cross-term ⟨Rcore,leak⟩ is NOT a third hypothesis. c₁<c₂→1 (squeeze, not exact).")
print("="*68)

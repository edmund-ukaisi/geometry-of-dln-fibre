import sympy as sp
# PIN it concretely: two distinct claims, determine which is exact vs squeeze.
# Use the actual (2,2,2) gauge chart. The reduced core dlnLoss M 0 for M=(1,1,1) [=H-r, r=1] = (c1 c2)²
# (scalar reduced chain). The gauge-normalized T̃-core = T(I−VY)^{-1}S. Is T̃-core² = (reduced chain)²
# EXACTLY, or with a unit?
# Concretely (rank-1, the (1,1) block is scalar): T̃ = T·(1−VY)^{-1}·S = T·S/(1−VY).
T,S,V,Y = sp.symbols('T S V Y', real=True)
Tnorm = T*S/(1 - V*Y)   # gauge-normalized T̃ (scalar)
# the LITERAL reduced chain (if the core were raw): T·S (the (1,1,1) product of the reduced blocks).
Traw = T*S
print("=== Claim B precision: T̃-core vs literal reduced-chain core ===")
print(f"  gauge-normalized T̃ = T·S/(1−VY)")
print(f"  literal reduced chain T·S")
print(f"  ratio T̃ / (T·S) = 1/(1−VY) — a UNIT (=1 at V=Y=0, bounded near 0), NOT identically 1.")
print(f"  ⟹ ‖T̃‖² = ‖T·S‖²·(1−VY)^{{-2}} — the (1−VY)^{{-2}} is a UNIT leak (∈[c₁,c₂], c₁<c₂). SQUEEZE.")
print()
# BUT: which does the chart/Lean actually use? If the reduced core dlnLoss M 0 is the chart's REDUCED
# COORDINATES' loss (i.e. T̃ IS the reduced coordinate, dlnLoss M 0 evaluated AT the gauge-normalized
# coords), then ‖T̃‖² = dlnLoss M 0 (eval at T̃-coords) is EXACT — the unit (1−VY)^{-1} is ABSORBED into
# the reduced COORDINATE (T̃ is the coord, not T·S). Then it's an IDENTITY in the gauge coords.
print("=== The two readings (this is the #48-vs-#55 fork) ===")
print("""
READING 1 (EXACT, #48): the chart's reduced coordinate IS T̃ (= T(I−VY)^{-1}S, the gauge-normalized
block). Then dlnLoss M 0 EVALUATED at the reduced coords = ‖T̃‖² LITERALLY (T̃ is the coord). The loss
= ∑E² + dlnLoss M 0(T̃-coords) is an IDENTITY (c₁=c₂=1). The (I−VY)^{-1} is part of the COORDINATE
DEFINITION (the gauge-normalization IS the c-o-v), absorbed, not a leak.

READING 2 (SQUEEZE, #55): the reduced core dlnLoss M 0 is the LITERAL reduced-chain product ‖∏ raw-T_s‖²
(raw blocks, no gauge-normalization), and ‖T̃‖² = ‖∏ raw-T‖²·(unit) ⟹ ≍ (squeeze, leak = the (I−VY)^{-2}
unit). Then dlnLoss∘flat = ∑E² + ‖T̃‖² ≍ ∑E² + dlnLoss M 0 (raw), c₁<c₂.

WHICH IS IT? Depends on whether dlnLoss M 0's REDUCED COORDS are the gauge-normalized T̃ (Reading 1, exact)
or the raw blocks (Reading 2, squeeze). The chart's redEmbed (Params S.red) maps the reduced coords →
the reduced-chain tuple. If redEmbed uses the GAUGE-NORMALIZED blocks (T̃), it's EXACT. If redEmbed is
the raw blocks (and the (I−VY)^{-1} is left as a separate unit), it's a SQUEEZE.
""")
print("⟹ THE ANSWER DEPENDS ON cobuild-sub34's redEmbed (the Lean #53/#54). I must coordinate with them:")
print("  - if their redEmbed = the gauge-normalized T̃ block (the chart's reduced COORD), the comparability")
print("    is EXACT (c₁=c₂=1), an IDENTITY — and #48 'exact' is RIGHT (the unit is in the coord def).")
print("  - if their redEmbed = raw ∏T (and (I−VY)^{-1} is a separate unit factor), it's a SQUEEZE (#55).")
print("MY READ: the gauge-normalization IS the c-o-v (the chart MAPS to the T̃ coords), so dlnLoss M 0 on")
print("the REDUCED COORDS = ‖T̃‖² EXACTLY (Reading 1). The squeeze framing (#55) treats T̃ ≍ raw-∏T as a")
print("SEPARATE comparability (the reduced core in RAW vs gauge-normalized coords) — which is a SECOND,")
print("downstream squeeze (raw-T̃ ≍ T̃), NOT the chart's loss-form. So: the CHART loss-form is EXACT in the")
print("gauge-normalized coords; the raw-∏T ≍ T̃ is a SEPARATE squeeze if one insists on raw coords.")

import sympy as sp
# Does L2's split need a normal-form theorem, or does an rlct-level argument sidestep it?
# F = ‖prod-B‖² at deepest (2,2,2) r=1. nReg=3, core G (the w3 w7-type node, rlct?).
# Known: aoyagiLambda(2,2,2) r=1 = [-1+1*4]/2 + lambdaCore(M') where M'=H-r=(1,1,1), lambdaCore(1,1,1)=1/2.
# = 3/2 + 1/2 = 2. So rlctAt(F) deepest SHOULD = 2 (= nReg/2 + core-rlct, core = (1,1,1) = rlct 1/2).
from sympy import Rational
nReg_half = Rational(3,2)  # nReg/2 = 3/2
# core = reduced (1,1,1) chain rlct = lambdaCore(1,1,1) = 1/2
core_rlct = Rational(1,2)
print(f"aoyagiLambda(2,2,2) r=1 = nReg/2 + lambdaCore(reduced (1,1,1)) = {nReg_half} + {core_rlct} = {nReg_half+core_rlct}")
print()
# The question: is rlctAt(F) = 2 provable WITHOUT a clean ΣE²+G² source form? Routes:
# ROUTE A (squeeze, rlctAt_mono, NO normal form): bound F between two clean forms.
#   F = E1²+E2²+E3²+(G+E·h)². Near 0: (G+E·h)² ≤ 2G²+2(E·h)², and (E·h)² ≤ |h|²·|E|² is dominated by
#   the E1²+E2²+E3² block (a nondeg quadratic). So c1(ΣE²+G²) ≤ F ≤ c2(ΣE²+G²) for constants c1,c2>0
#   near 0? If F is SQUEEZED between two multiples of (ΣE²+G²), then rlctAt(F)=rlctAt(ΣE²+G²) by
#   rlctAt_mono BOTH ways (the constant multiples are units). THEN S1.5 on the clean ΣE²+G². NO normal
#   form / constant-rank needed — just the squeeze inequality + rlctAt_mono (green) + S1.5 (green).
print("=== ROUTE A (squeeze via rlctAt_mono, NO normal form — the green-tool bridge) ===")
print("F = E1²+E2²+E3²+(G+E·h)². The cross/higher terms are DOMINATED by the nondeg E-block near 0:")
print("  ∃ c1,c2>0, U∋0: c1·(E1²+E2²+E3²+G²) ≤ F ≤ c2·(E1²+E2²+E3²+G²) on U.")
print("Then rlctAt_mono BOTH directions (the constants are units) => rlctAt(F) = rlctAt(ΣE²+G²).")
print("THEN S1.5 (smoothBlockND on ΣE² + Fubini) => = nReg/2 + rlctAt(G²). NO constant-rank/normal-form!")
print()
print("So a114e07e's bridge: NOT 'F∘χ literally = ΣE²+G²' (false), but the SQUEEZE")
print("  c1(ΣE²+G²) ≤ F ≤ c2(ΣE²+G²)  =>  rlctAt(F) = rlctAt(ΣE²+G²)  [rlctAt_mono ×2]  = nReg/2 + core")
print("This uses ONLY green tools (rlctAt_mono + S1.5), NO normal-form theorem, NO ideal-swap.")
print("MUST VERIFY the squeeze inequality holds (the cross terms dominated). Check on (2,2,2) r=1.")

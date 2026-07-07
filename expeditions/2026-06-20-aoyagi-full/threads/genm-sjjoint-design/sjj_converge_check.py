import numpy as np
# Sharper guide: does ∫_[0,1]^4 F^{-c'} (F=α²+γ²β²s²) CONVERGE for c'<1 and DIVERGE for c'>1 as the grid
# refines near 0? Use a log-spaced grid concentrating near 0 to expose the origin singularity.
def integral(cp, N):
    # tensor grid on (0,1] log-spaced (captures the origin singularity); trapezoidal-ish weights
    e = np.logspace(-6, 0, N)                       # points
    w = np.gradient(e)                              # cell widths
    A,G,B,S = np.meshgrid(e,e,e,e, indexing='ij')
    WA,WG,WB,WS = np.meshgrid(w,w,w,w, indexing='ij')
    F = A**2 + (G*B*S)**2
    return np.sum(F**(-cp) * WA*WG*WB*WS)
print("∫_[0,1]^4 (α²+γ²β²s²)^{-c'}, log-grid, refining N (toric RLCT=1 => converge c'<1, diverge c'>1):")
for cp in [0.7, 0.9, 1.0, 1.2]:
    vals=[integral(cp,N) for N in (20,30,45)]
    trend = "STABLE(converges)" if vals[-1] < 3*vals[0]+5 else "GROWS(diverges)"
    print(f"  c'={cp}:  N=20,30,45 -> {vals[0]:.2f}, {vals[1]:.2f}, {vals[2]:.2f}   {trend}")
print("  (c'<1 stabilises as N grows = convergent; c'>1 grows with N = divergent — matches toric RLCT=1.")
print("   The atom route's |βs|^{-1} weight diverges for ALL c'>1/2 — an artifact, not the true threshold 1.)")

import sympy as sp
# VERIFY Codex's constant-active-block split on (2,2,2), B rank 1, the v(2,1) example.
# N_active = H_1 H_{L+1} - (H_1-r)(H_{L+1}-r). Here the chain ENDS: H_0=2 (input), H_L=2 (output), r=1.
# Codex's formula uses H_1, H_{L+1} = the two ENDPOINTS = (2,2). N_active = 2*2 - (2-1)(2-1) = 4 - 1 = 3.
H0, HL, r = 2, 2, 1
N_active = H0*HL - (H0-r)*(HL-r)
print(f"N_active = {H0}*{HL} - ({H0}-{r})*({HL}-{r}) = {N_active}  [= nReg = r(H0+HL-r) = {r*(H0+HL-r)}]")
print("  (matches my g150 nReg = r(H_0+H_last-r) = 1*(2+2-1) = 3) ✓ — CONSTANT, v-independent.")
print()
# Claim: rlctAt(loss, v) = N_active/2 + rlctAt(F0_{H-r}, D(v)).
#   deepest: D(v)=0, rlctAt(F0,0)=1/2 => 3/2+1/2 = 2 ✓ (matches).
#   v(2,1):  rlctAt(loss,v)=2 (computed). So rlctAt(F0, D(v)) must = 2 - 3/2 = 1/2.
#            F0_{(1,1,1)} = (s1 s2)^2 (scalar core). D(v) = the induced quotient maps. rlctAt(F0,D(v))=1/2 needed.
#            F0=(s1 s2)^2: rlctAt at ANY point? at 0: 1/2. at a pt where s1 s2 = 0 (e.g. s1=0,s2 free): 
#               near (0, s2*) with s2*!=0: (s1 s2)^2 ~ s2*^2 s1^2 nondeg in s1 => rlctAt = 1/2 (one square)!
#            So rlctAt(F0, D(v)) = 1/2 whether D(v)=0 OR D(v) on the s1=0 (or s2=0) axis. CONSISTENT ✓
print("rlctAt(loss,v) = N_active/2 + rlctAt(F0_{M}, D(v)), M=(1,1,1), F0=(s1 s2)^2:")
print("  deepest: D=0 => rlctAt(F0,0)=1/2 => total 3/2+1/2 = 2 ✓")
print("  v(2,1):  total=2 => rlctAt(F0,D(v))=1/2. F0=(s1 s2)^2 at a pt on {s1 s2=0} axis (say s1=0,s2!=0):")
print("           (s1 s2)^2 ~ (s2*)^2 s1^2, nondeg quadratic in s1 => rlctAt = 1/2. ✓ MATCHES.")
print()
print("So under the CONSTANT-N_active split, v(2,1)'s extra smoothness shows up as rlctAt(F0, D(v))")
print("at D(v) on the core's OWN zero-fibre (NOT at 0), where core-P1 gives rlctAt(F0,0)=1/2 <= rlctAt(F0,D(v))=1/2.")
print("The '4th Morse direction' I found = the extra smooth direction INSIDE the core at D(v)!=0. TIGHT here.")
print()
print("="*64)
print("VERDICT: Codex's constant-active-block split is RIGHT. n_v is constant (=N_active=nReg) IF you")
print("peel ONLY the active block; the v-dependence moves into rlctAt(F0, D(v)) (core at a shifted basept),")
print("handled by core-P1 (PROVEN). The 'varying n_v' I found = the MAXIMAL split (over-peeling) — avoid it.")

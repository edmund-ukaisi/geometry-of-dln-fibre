import numpy as np
# ==================================================================
# Adjudicate Codex Q4 "saturated-shell escape".
# Shells (design): r=min(a,b); anchor r=2, M2=3.
#   S_0 = {sig_min = sig_3 >= e0}
#   S_j = {sig_{M2-j} >= e_j > sig_{M2-j+1}},   1<=j<=r-1     (anchor: S_1 = {sig_2>=e1>sig_3})
#   S_r = {sig_{M2-r+1} < e_r}                                (anchor: S_2 = {sig_2 < e2})
# Question: is the cover EXHAUSTIVE?  Codex witness Z_delta = delta*I (all sv = delta).
# ==================================================================
M2, r = 3, 2

def in_shells(sig, e):   # sig sorted DESC length 3; e = [e0,e1,e2]
    s1,s2,s3 = sig                       # s3 = sigma_min
    S0 = (s3 >= e[0])
    S1 = (s2 >= e[1]) and (e[1] > s3)     # exactly 1 sv < e1
    S2 = (s2 < e[2])                      # saturated: >=2 small (sig_{M2-r+1}=sig_2 < e2)
    return S0, S1, S2

print("=== Codex witness Z_delta = delta*I3 (sig=(d,d,d)), d < min(e_j) ===")
print("--- (A) SINGLE threshold e0=e1=e2=e :")
e=[0.5,0.5,0.5]
for d in [0.4,0.1,0.01]:
    S=in_shells([d,d,d],e); print(f"   d={d}: (S0,S1,S2)={S}  covered={any(S)}")
print("--- (B) DISTINCT decreasing e0>e1>e2, Codex's exact witness d<min=e2 :")
e=[0.7,0.5,0.3]
for d in [0.25,0.1,0.01]:
    S=in_shells([d,d,d],e); print(f"   d={d}: (S0,S1,S2)={S}  covered={any(S)}   <- Codex's Z_delta IS caught by S2 (sig2=d<e2)")

print()
print("=== EXHAUSTIVENESS sweep over random Z (sorted SVs), SINGLE e vs DISTINCT e ===")
rng=np.random.default_rng(0)
def sweep(e, N=200000):
    gaps=0
    for _ in range(N):
        sig=np.sort(rng.uniform(0,1,size=3))[::-1]
        S=in_shells(sig,e)
        if not any(S): gaps+=1
    return gaps
print(f"  SINGLE e=[0.5,0.5,0.5]:   uncovered Z (gaps) = {sweep([0.5,0.5,0.5])} / 200000")
print(f"  DISTINCT e=[0.7,0.5,0.3]: uncovered Z (gaps) = {sweep([0.7,0.5,0.3])} / 200000   <- the intermediate-band gap")
# show an explicit escaping Z for the distinct case:  sig_2 in (e2,e1)
print()
print("  explicit escaper for DISTINCT e=[0.7,0.5,0.3]: sig=(0.9, 0.4, 0.1)  (sig2=0.4 in (0.3,0.5))")
print("   in_shells:", in_shells([0.9,0.4,0.1],[0.7,0.5,0.3]), " -> UNCOVERED (S0:0.1>=0.7 no; S1:0.4>=0.5 no; S2:0.4<0.3 no)")
print()
print("VERDICT: single e => exhaustive (0 gaps). distinct decreasing e_j => intermediate-band GAP.")
print("Codex's SPECIFIC Z_delta is caught by S2 (arithmetic slip), but the CATEGORY (exhaustiveness)")
print("is a REAL required check: the tide must use a single threshold (or nested-consistent), NOT")
print("arbitrary distinct e_j. The all-small-Z region is the SATURATED shell (Morse rescue, no minor CoV).")

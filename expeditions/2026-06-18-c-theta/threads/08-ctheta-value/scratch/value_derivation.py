"""Value-assembly derivation (CThetaValue tide): closed-form C and θ from the drop-to-m
reduction + the integer-square lemma. Brute-vs-closed-form, exact integers.

Chain (r=0, Monotone d, after drop-to-m so support ⊆ {0,...,m-1}):
  Phi(e) = ∑_i (e_i - s_i)^2,  s_i = d_0 - d_{i+1}  (= qipShift).
  On the m-face (e_i=0 for i≥m, ∑_{i<m} e_i = d_0):
    substitute w_i := e_i + d_{i+1}  ⟹  e_i - s_i = w_i - d_0,  ∑_{i<m} w_i = S := ∑_{0..m} d.
    substitute t_i := w_i - a        ⟹  ∑ t_i = S - m·a =: δ.
    ∑_{i<m}(e_i-s_i)^2 = ∑ t_i^2 + 2(a-d_0)δ + m(a-d_0)^2.
  isLeast_sumSq (|δ| ≤ m): min ∑ t_i^2 = |δ|, attained, with θ = C(m,|δ|) minimisers.
    a := ⌊S/m + 1/2⌋  (integer: ⌊(2S+m)/(2m)⌋), δ := S - m·a, so |δ| ≤ m/2 ≤ m.
  min Phi = |δ| + 2(a-d_0)δ + m(a-d_0)^2 + ∑_{i≥m} s_i^2.
  C = ½(min Phi + d_0^2 - ∑_all s_i^2)        [from 2·Gqip - d_0^2 = Phi - ∑ s_i^2, two_Gqipℤ_sub_sq]
    = ½(d_0^2 - ∑_{i=1}^m (d_i-d_0)^2 + m(a-d_0)^2 + 2(a-d_0)δ + |δ|).
  θ = Nat.choose m |δ|.
"""
from math import floor, comb

def closed_form(d):
    N=len(d)-1; d0=d[0]
    A=lambda l: sum(d[0:l+1]) - l*d[l]
    m=max(l for l in range(1,N+1) if A(l)>=0)
    S=sum(d[0:m+1]); a=floor(S/m+0.5); delta=S-m*a
    C=(d0*d0 - sum((d[i]-d0)**2 for i in range(1,m+1)) + m*(a-d0)**2 + 2*(a-d0)*delta + abs(delta))//2
    return C, comb(m,abs(delta)), m, a, delta

def brute(d):
    N=len(d)-1; d0=d[0]; s=[d0-d[i+1] for i in range(N)]
    def gen(n,t):
        if n==1: yield (t,); return
        for x in range(t+1):
            for r in gen(n-1,t-x): yield (x,)+r
    best=None;cnt=0
    for e in (gen(N,d0) if N>0 else [()]):
        p=sum((e[i]-s[i])**2 for i in range(N))
        if best is None or p<best: best=p;cnt=1
        elif p==best: cnt+=1
    sums2=sum(x*x for x in s)
    return (best+d0*d0-sums2)//2, cnt

if __name__=="__main__":
    for d in [[2,2,2],[8,8,11,11,11,13,13,13,15],[4,5,8,9,10,10],[2,5,6,7,10],[2,2,3],[1,4,4,9],[3,3,3,3]]:
        cf=closed_form(d); br=brute(d)
        assert (cf[0],cf[1])==br, (d,cf,br)
        print(f"d={d}: C={cf[0]} θ={cf[1]} (m={cf[2]},a={cf[3]},δ={cf[4]}) — matches brute {br}")
    print("ALL OK")

from math import comb

def qipA(d, l):
    N = len(d)-1
    def D(i): return d[min(i,N)]
    return sum(D(i) for i in range(l+1)) - l*D(l)

def qipM(d):
    N = len(d)-1
    # findGreatest over l in [0..N] of (qipA(d,l) >= 0); but l=0 trivially A_0 = d_0 >=0.
    m = 0
    for l in range(1, N+1):
        if qipA(d,l) >= 0:
            m = l
    # Nat.findGreatest returns greatest l<=N with pred; pred(1) holds always (A_1=d_0). guarantee >=1
    if m == 0:
        m = 0
    return m

def qipS(d):
    N=len(d)-1
    m=qipM(d)
    def D(i): return d[min(i,N)]
    return sum(D(i) for i in range(m+1))

def qipRound(d):
    S=qipS(d); m=qipM(d)
    # Int division floor in Lean is T-division? Lean Int ediv is floor for positive divisor. (2S+m)/(2m)
    num=2*S+m; den=2*m
    # Lean Int./ is T-rounding (toward zero)? Actually Int.div in Lean4/Mathlib `/` is `Int.div` = T-division.
    # But qipRound uses ediv? In Lean `/` on Int is Int.div (T-division). Use floor for positive operands (both positive here).
    import math
    return num//den  # floor division; num,den>0 so matches both

def qipDelta(d):
    return qipS(d) - qipM(d)*qipRound(d)

def cTheta(d):
    return comb(qipM(d), abs(qipDelta(d)))

def cValue(d):
    m=qipM(d); S=qipS(d); a=qipRound(d); delta=qipDelta(d)
    N=len(d)-1
    def D(i): return d[min(i,N)]
    val = (d[0]**2 - sum((D(i)-d[0])**2 for i in range(1,m+1)) + m*(a-d[0])**2 + 2*(a-d[0])*delta + abs(delta))
    return val//2

tests = {
 "(2,2,2)":[2,2,2],
 "(1,1,1)":[1,1,1],
 "(2,2,2,2)":[2,2,2,2],
 "(1,1,1,1)":[1,1,1,1],
 "(2,2,2,2,2)":[2,2,2,2,2],
 "(1,1,1,1,1)":[1,1,1,1,1],
}
for name,d in tests.items():
    print(f"{name:14s} m={qipM(d)} S={qipS(d)} a={qipRound(d)} delta={qipDelta(d)} |delta|={abs(qipDelta(d))} C(cValue)={cValue(d)} cTheta=C(m,|d|)={cTheta(d)}")

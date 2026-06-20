"""
AUDIT the telescoping proof's intermediate claims (not just the final inequality), to rule out
'right answer, wrong proof'. For random nonneg g and cells (I,J) with gIJ>0:

  (P0) alpha := least row a<=I with g_{p,J}>0 for ALL a<=p<=I. (exists since gIJ>0). g_{alpha-1,J}=0.
  (P1) For a in [alpha, I]: z_a := min{ q>=J : g_{a,q}=0 } (g_{a,N+1}=0 so well-defined).
       q_a := min_{p in [a,I]} z_a... = min_{p in [a,I]} z_p.  E(a):=q_a -1.
  (P2) CLAIM A = { [a,e] : alpha<=a<=I, J<=e<=E(a) }.   <-- verify set equality vs brute A_set.
  (P3) inner telescope over e: sum_{e=J}^{q_a-1} (g_{a,e}-g_{a,e+1}-g_{a-1,e}+g_{a-1,e+1})
        = (g_{a,J}-g_{a,q_a}) - (g_{a-1,J}-g_{a-1,q_a}).   <-- verify per a.
  (P4) outer over a telescopes the g_{*,J} part to g_{I,J}-g_{alpha-1,J} = g_{I,J}.  <-- verify.
  (P5) q_a nondecreasing in a.  <-- verify.
  (P6) block decomposition: each maximal constant block [u,v] (q_a=q) contributes g_{u-1,q}-g_{v,q},
       and g_{v,q}=0 (either z_v=q so g_{v,q}=0, or v=I and q_I=z_I so g_{I,q}=0). So block >= g_{u-1,q} >=0.
       => sum_{a} (g_{a-1,q_a}-g_{a,q_a}) >= 0.  <-- verify the >=0 and the per-block g_{v,q}=0.
"""
import random
from verify_codex import second_diff, A_set, random_nonneg_tri

def G(g,i,j,N): return g.get((i,j),0) if (0<=i<=j<=N) else 0

def audit(g, I, J, N):
    # alpha
    alpha=I
    while alpha-1>=0 and G(g,alpha-1,J,N)>0: alpha-=1
    # check gIJ>0 and g_{alpha-1,J}=0
    assert G(g,I,J,N)>0
    assert G(g,alpha-1,J,N)==0, ("P0 alpha-1 col not zero", alpha, G(g,alpha-1,J,N))
    # z_a and q_a
    def z(a):
        q=J
        while q<=N and G(g,a,q,N)>0: q+=1
        return q   # first q>=J with g_{a,q}=0 (q<=N+1)
    q=[None]*(I+1)
    for a in range(alpha, I+1):
        q[a]=min(z(p) for p in range(a, I+1))
    # P5 monotone
    for a in range(alpha, I):
        assert q[a] <= q[a+1], ("P5 not monotone", a, q[a], q[a+1])
    # P2 set equality
    A_tele=set()
    for a in range(alpha, I+1):
        for e in range(J, q[a]):   # J..q_a-1
            A_tele.add((a,e))
    A_brute=set(A_set(g,I,J,N))
    assert A_tele==A_brute, ("P2 set mismatch", sorted(A_tele), sorted(A_brute), "alpha",alpha,"q",q)
    # P3 inner telescope per a
    for a in range(alpha, I+1):
        lhs=sum(second_diff(g,a,e,N) for e in range(J, q[a]))
        rhs=(G(g,a,J,N)-G(g,a,q[a],N)) - (G(g,a-1,J,N)-G(g,a-1,q[a],N))
        assert lhs==rhs, ("P3", a, lhs, rhs)
    # P4 + P6: full sum
    total=sum(second_diff(g,a,e,N) for (a,e) in A_brute)
    # decompose total = gIJ + sum_a (g_{a-1,q_a}-g_{a,q_a})  (after telescoping g_{*,J} column)
    colJ_telescope = sum( (G(g,a,J,N)-G(g,a-1,J,N)) for a in range(alpha,I+1) )  # = g_{I,J}-g_{alpha-1,J}
    assert colJ_telescope == G(g,I,J,N), ("P4", colJ_telescope, G(g,I,J,N))
    qterm = sum( (G(g,a-1,q[a],N)-G(g,a,q[a],N)) for a in range(alpha,I+1) )
    assert total == colJ_telescope + qterm, ("recompose", total, colJ_telescope, qterm)
    # P6 block: g_{v,q}=0 at end of each block
    # verify qterm >= 0 by block check
    a=alpha
    while a<=I:
        v=a
        while v<I and q[v+1]==q[a]: v+=1
        qval=q[a]
        # end-of-block: g_{v,qval}=0
        assert G(g,v,qval,N)==0, ("P6 end-block not zero", a, v, qval, G(g,v,qval,N))
        a=v+1
    assert qterm>=0, ("qterm neg", qterm)
    assert total>=G(g,I,J,N), ("final", total, G(g,I,J,N))
    return True

if __name__=="__main__":
    random.seed(7)
    checked=0
    for N in range(1,7):
        for _ in range(15000):
            g=random_nonneg_tri(N, hi=random.choice([1,1,2,3,4]))
            for I in range(N+1):
                for J in range(I+1,N+1):
                    if G(g,I,J,N)>0:
                        audit(g,I,J,N); checked+=1
    print(f"AUDIT all intermediate proof steps: checked={checked}, ALL assertions passed.")

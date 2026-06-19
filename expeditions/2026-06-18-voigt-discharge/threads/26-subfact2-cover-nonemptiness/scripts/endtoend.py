"""
End-to-end: at extremal cell (i0,j0), c=i0+1, b=j0-1.
Sub-fact 2 (Codex lemma) gives (a,e), a<=i0,e>=j0, m(r)_{[a,e]}>=1, rect [a,i0]x[j0,e] subset supp(g).
Sub-fact 1 gives (if c<=b) m(r)_{[c,b]}>=1.
Then the linked box move (a,c,b,e) is applicable to m(r), and its drop rectangle D=[a,c-1]x[b+1,e]
   = [a,i0]x[j0,e] subset supp(g), so r' = r - 1_D >= s. Verify r' >= s and r' < r and dim preserved.
"""
from box_engine import *
from descent_search import supp, g_array, all_achievable_rank_patterns

def extremal_cell(g,N):
    cells=[(i,j) for i in range(N+1) for j in range(i+1,N+1) if g[(i,j)]>0]
    return min(cells,key=lambda ij:(ij[1],-ij[0])) if cells else None
def rect_in_supp(g,a,i0,j0,e):
    return all(g.get((i,j),0)>0 for i in range(a,i0+1) for j in range(j0,e+1))

def subfact2_pick(mr,g,i0,j0,N):
    """Codex's A-set: pick any [a,e] in A with m(r)>=1 (lemma guarantees one)."""
    for a in range(0,i0+1):
        for e in range(j0,N+1):
            if mr.get((a,e),0)>=1 and rect_in_supp(g,a,i0,j0,e):
                return (a,e)
    return None

def test(d,N):
    pats=all_achievable_rank_patterns(list(d),N); rs=list(pats.values()); rd=[rank_pattern(m,N) for m in rs]
    pairs=0; ok=0; bad=[]
    for ri,mr in enumerate(rs):
        r=rd[ri]
        for si,s in enumerate(rd):
            if si==ri or not lt(s,r,N): continue
            g=g_array(s,r,N); (i0,j0)=extremal_cell(g,N); pairs+=1
            c,b=i0+1,j0-1
            mv=subfact2_pick(mr,g,i0,j0,N)
            if mv is None: bad.append(('no sf2',(i0,j0),mr)); continue
            a,e=mv
            # sub-fact 1 (linked): if c<=b need m(r)_{[c,b]}>=1
            if c<=b and mr.get((c,b),0)<1: bad.append(('sf1 fail',(a,c,b,e),mr,g)); continue
            # applicability: m(r)_{[a,e]}>=1 (yes), structural a<c<=b+1<=e
            if not (a<c<=b+1<=e): bad.append(('struct',(a,c,b,e)));continue
            # apply move, get r', check r'>=s, r'<r, dim same
            m2=apply_box_move(mr,a,c,b,e)
            if not is_achievable_m(m2): bad.append(('m2 neg',(a,c,b,e),m2)); continue
            r2=rank_pattern(m2,N)
            if dim_vector(m2,N)!=dim_vector(mr,N): bad.append(('dim',(a,c,b,e)));continue
            if not le(s,r2,N): bad.append(('not >= s',(a,c,b,e),{k:r2[k] for k in r2}));continue
            if not lt(r2,r,N): bad.append(('not < r',(a,c,b,e)));continue
            ok+=1
    print(f"d={d}: pairs={pairs} end-to-end-descent-OK={ok} bad={len(bad)}")
    for x in bad[:3]: print("   BAD",x)

if __name__=="__main__":
    for d,N in [((1,2,1),2),((2,2,2),2),((1,2,2,1),3),((2,2,2,2),3),((1,2,3,2,1),4),((3,3,3,3),3),((1,3,3,1),3),((2,3,2),2)]:
        test(d,N)

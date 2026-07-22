"""
pnp-transport STAGE 2: the ledger/b-chain transport across the FOUR edge types,
pinned to EngineDefs.stepUpdate (case2 / case11 / case12 / rollover), and the derived
ε_d(i) = [ t̃_d < i ]  (the u_d exponent in the b-chain ratio b_i / b_dominant).

EngineDefs.stepUpdate (Aoyagi pp.16/17/20/21), transcribed EXACTLY:
  case2   : numDiv+1 ; new divExp = resRows*resCols ; new profile tail := J (t̃ = J via setTail,
            head = running-min width) ; cleared+1.
  case11  : divExp[mergeIdx] += runLen*resCols ; profile[mergeIdx] tail := J  (t̃ RESET to J) ;
            numDiv/cleared UNCHANGED.                                   <-- the "δ=1 reset"
  case12  : numDiv+1 ; new divExp = divExp[mergeIdx] + runLen*resCols ;
            new profile = mergeIdx profile with tail := J (t̃ = J) ; cleared+1.
  rollover: ledger UNCHANGED ; cleared := 0.

State (S=layer 1-indexed, J=cleared).  Profile T = (t^1,...,t^L); t̃ = min(T).
b-chain: b_i = prod_{ t̃_d < i } u_d   (squarefree in each u_d).  Dominant b at (S,J) is b_{J+1}.
ε_d(i) := exponent of u_d in  b_i / b_{J+1}  =  [ t̃_d < i ] - [ t̃_d < J+1 ]   (>=0 for i>=J+1).
The boostReady-relevant ε at a case11 boost is ε_pivot(i) for i in the residual rows: it is 1 on the
'suffix' rows (i > t̃_pivot) and 0 on the dominant rows -- exactly the support-only-carries-pivot fact.
"""

def setTail(profile, S, J):
    # tail t^i := J for 1-indexed layer i >= S ; head unchanged. profile is a dict layer->value.
    return {i: (J if i >= S else profile.get(i, 0)) for i in profile}

class Div:
    def __init__(self, name, profile, exp, born):
        self.name=name; self.profile=dict(profile); self.exp=exp; self.born=born
    def tilde(self):  # t̃ = min over layers
        return min(self.profile.values())
    def __repr__(self):
        return f"{self.name}(T={tuple(self.profile[k] for k in sorted(self.profile))},M={self.exp},t~={self.tilde()})"

def bchain(divs, size):
    # b_i for i=1..size : product of divisor names with t̃ < i
    out=[]
    for i in range(1,size+1):
        fac=[d.name for d in divs if d.tilde() < i]
        out.append(tuple(sorted(fac)))
    return out

def eps_pivot(divs, pivot_name, rows):
    # ε_pivot(i) as the b-chain suffix indicator [t̃_pivot < i], for the given residual rows (1-indexed)
    piv=[d for d in divs if d.name==pivot_name][0]
    return {i: (1 if piv.tilde() < i else 0) for i in rows}

def run_trace(name, M, edges):
    """M = widths (1-indexed list, M[1..N+1]); edges = list of (case,S,J,runLen,mergeName,note)."""
    L = len(M)-2  # widths M[1..L+1], N=L
    def Mw(i): return M[i]
    def runMin(uptoLayer):   # running-min width min{M^1..M^{layer+? }}: here min over 1..uptoLayer
        return min(M[1:uptoLayer+1])
    print(f"\n================= {name}  widths={M[1:]} =================")
    divs=[]; cleared=0
    for (case,S,J,runLen,mergeName,note) in edges:
        resRows = runMin(S) - J          # M(S) - J
        resCols = Mw(S+1) - J            # M^{S+1} - J
        delta = 1 if J==0 else 0
        if case=='case2':
            prof={i:(runMin(i+1) if i< S else J) for i in range(1,L+1)}  # head=raw running-min, tail=J
            # Aoyagi p.20 head label = M^{i+1}; FIX-A caps at running-min. Either way t̃ = J (tail=J<=head).
            d=Div(f"u{S}{J+1}", prof, resRows*resCols, (S,J)); divs.append(d); cleared=J+1
        elif case=='case11':
            d=[x for x in divs if x.name==mergeName][0]
            d.exp += runLen*resCols; d.profile=setTail(d.profile,S,J)   # t̃ RESET to J
            cleared=J   # no advance
        elif case=='case12':
            base=[x for x in divs if x.name==mergeName][0]
            prof=setTail(dict(base.profile),S,J)
            d=Div(f"v{S}{J+1}", prof, base.exp+runLen*resCols, (S,J)); divs.append(d); cleared=J+1
        elif case=='rollover':
            cleared=0
        size = runMin(S if case!='rollover' else S+1)   # diag size = M(S) (or M(S+1) after rollover)
        bc = bchain(divs, size)
        print(f"  [{case:8s} S={S} J={J} δ={delta}] {note}")
        print(f"       divs: {divs}")
        print(f"       b-chain (size {size}): {[ '*'.join(x) if x else '1' for x in bc ]}")
    return divs

# ---- (2,2,2,2) binding trace: u11 born, u12 born, rollover, boost u12 (case11) ----
divs_2222 = run_trace("(2,2,2,2) binding", [None,2,2,2,2], [
    ('case2', 1,0,1,None,   "born u11 (whole 2x2), t~=0"),
    ('case2', 1,1,1,None,   "born u12 (1x1 deep block), t~=1"),
    ('rollover',1,2,0,None, "layer 1 exhausted -> S=2"),
    ('case11',2,0,1,'u12',  "BOOST u12: t~ 1->0 (δ=1 reset); exp += 1*(M4-0)=+2"),
])
piv='u12'
eps = eps_pivot(divs_2222, piv, rows=[1,2])
print(f"   >> at the boost node, ε_{piv}(row i) over residual rows 1,2 = {eps}")
print(f"      row 1 (dominant, i=1): ε=0  ->  col-0 terms carry NO {piv}")
print(f"      row 2 (suffix,   i=2): ε=1  ->  col-1/deeper terms carry {piv}^1  == boostReady")

# ---- (3,3,4): layer-2 (2,0) Case 1 J_1=1: BOTH children, case11 boost AND case12 split ----
print("\n### (3,3,4) layer-2 Case-1 fork: case11 (boost) vs case12 (split) ###")
base = run_trace("(3,3,4) layer1 -> (2,0)", [None,3,3,4], [
    ('case2',1,0,1,None,"u11 3x3, t~=0"),
    ('case2',1,1,1,None,"u12 2x2, t~=1"),
    ('case2',1,2,1,None,"u13 1x1, t~=2"),
    ('rollover',1,3,0,None,"-> S=2, b=(u11,u11u12,u11u12u13)"),
])
import copy
# case11 child: boost u12
d11=copy.deepcopy(base)
print("  -- case11 child (boost u12): --")
run_from = None
b=[x for x in d11 if x.name=='u12'][0]; b.exp+=1*(4-0); b.profile=setTail(b.profile,2,0)
print(f"     divs after boost: {d11}   (u12: t~ {1}->{b.tilde()}, M=4->{b.exp})  b1..3={bchain(d11,3)}")
# case12 child: split -> new divisor v inheriting u12's profile, u12 unchanged
d12=copy.deepcopy(base)
print("  -- case12 child (split, new v inheriting u12): --")
u12=[x for x in d12 if x.name=='u12'][0]
prof=setTail(dict(u12.profile),2,0); v=Div('v21',prof,u12.exp+1*(4-0),(2,0)); d12.append(v)
print(f"     divs after split: {d12}   (u12 UNCHANGED t~=1; new v21 t~={v.tilde()}, M={v.exp})  b1..3={bchain(d12,3)}")

# ---- (3,3,2,2): coupled binder boosted TWICE -> test whether ε exceeds 1 ----
divs_3322 = run_trace("(3,3,2,2) coupled binder (double boost)", [None,3,3,2,2], [
    ('case2',1,0,1,None,"u11 3x3 t~=0"),
    ('case2',1,1,1,None,"u12 2x2 t~=1"),
    ('case2',1,2,1,None,"u13 1x1 t~=2 (the coupled binder)"),
    ('rollover',1,3,0,None,"-> S=2"),
    ('case11',2,1,1,'u13',"BOOST#1 u13 at (2,1): t~ 2->1; note J=1 so δ=0 (NOT a reset-to-0)"),
    ('rollover',2,2,0,None,"-> S=3"),
    ('case11',3,0,1,'u13',"BOOST#2 u13 at (3,0): t~ 1->0 (δ=1 reset)"),
])
piv='u13'
d=[x for x in divs_3322 if x.name==piv][0]
print(f"   >> {piv} final t~={d.tilde()} (terminal), M={d.exp}; ε_{piv}(i)=[t~<i] is BINARY (b-chain squarefree)")
print(f"   >> b-chain is squarefree in every u_d  ==>  ε_d(i) in {{0,1}} ALWAYS (per divisor, per row).")
print("\nSTAGE 2 done.")

"""
Programmatic trace of the ConState oracle (classify + transitions), to confirm the (2,2,2,2)
real branch and the case11 boost data WITHOUT relying on the hand-trace.

Faithful to EngineConstruction.lean:
  classify(s): terminal if L<=layer; elif widthMinUpto(layer+1)<=cleared: rollover;
    else occ = {divTilde k : cleared+1 <= divTilde k <= widthMinUpto(layer)-1};
         case1(target=min occ) if occ nonempty else case2.
  divTilde k = min over Fin L of divProfile[k]  (= min of the profile vector).
  setTail(layer,cleared,T)[p] = cleared if layer<=p else T[p].
  case2  : append div (profile=setTail(layer,cleared, runMinWidth), divTilde=..., birth=(layer,cleared)); cleared+1.
  case12 : append div (profile=setTail(layer,cleared, divProfile[f]));                                    cleared+1.
  case11 : divProfile[f] := setTail(layer,cleared, divProfile[f]) (t~ drops to cleared); cleared unchanged.
  rollover: layer+1, cleared:=0.
  runLen (case1) = target - cleared.
Engine M and L: for DLN d:Fin(N+1), the engine has L=N-1, M = the widths used by widthMinUpto.
We take widthMinUpto(n) = min(d_i : i<=n) over the DLN widths d (all 2 here) — matches the
DLN `widthMinUpto d n` = min block width through layer n.
"""

def make_trace(d):
    N = len(d) - 1          # layers 0..N-1
    Lmax = N - 1            # ConState layer ranges 0..Lmax ; terminal at layer==... use classify guard L<=layer with L=Lmax
    def widthMinUpto(n):
        return min(d[i] for i in range(0, min(n, N-1) + 1))  # min over i<=n of block width; block i width ~ d[i] (col axis)
    # NB: runMinWidth for the profile head-reset; for divTilde (=min profile) with setTail writing the
    #     TAIL to `cleared`, the min is dominated by the tail-write => divTilde = cleared at birth for case2/case12
    #     (the head runMinWidth values are >= cleared here). We track divTilde directly = tildeOf(profile).
    #     Since profile = setTail(layer,cleared, head), and head entries >= cleared on these widths, min = cleared.
    class St:
        def __init__(s):
            s.layer=0; s.cleared=0; s.numDiv=0
            s.profile=[]       # list of profile vectors (len Lmax+? ) — we store as list of ints via divTilde only
            s.divTilde=[]      # min of each profile
            s.birth=[]         # (layer,cleared) birth corners
        def clone(s):
            t=St(); t.layer=s.layer; t.cleared=s.cleared; t.numDiv=s.numDiv
            t.divTilde=list(s.divTilde); t.birth=list(s.birth); return t
    def classify(s):
        if Lmax <= s.layer: return ("terminal",)
        if widthMinUpto(s.layer+1) <= s.cleared: return ("rollover",)
        occ = sorted({s.divTilde[k] for k in range(s.numDiv)
                      if s.cleared+1 <= s.divTilde[k] <= widthMinUpto(s.layer)-1})
        if occ: return ("case1", occ[0])
        return ("case2",)
    s=St(); path=[]
    for _ in range(40):
        dec=classify(s)
        if dec[0]=="terminal":
            path.append(("terminal", s.layer, s.cleared, None)); break
        if dec[0]=="rollover":
            path.append(("rollover", s.layer, s.cleared, "delta=%d"%(1 if s.cleared==0 else 0)))
            s=s.clone(); s.layer+=1; s.cleared=0
        elif dec[0]=="case2":
            delta = 1 if s.cleared==0 else 0
            path.append(("case2", s.layer, s.cleared, "delta=%d birth=(%d,%d)"%(delta,s.layer,s.cleared)))
            t=s.clone(); t.divTilde.append(s.cleared); t.birth.append((s.layer,s.cleared)); t.numDiv+=1; t.cleared+=1
            s=t
        elif dec[0]=="case1":
            target=dec[1]; runLen=target-s.cleared; delta=1 if s.cleared==0 else 0
            # the merged divisor f = min-profile divisor at level target; here first with divTilde==target
            f=[k for k in range(s.numDiv) if s.divTilde[k]==target][0]
            path.append(("case1/case11", s.layer, s.cleared,
                         "delta=%d target=%d runLen=%d reuse f=%d birth=%s"%(delta,target,runLen,f,s.birth[f])))
            break  # stop at the first case1 boost (the target node)
    return path, s, (f if dec[0]=="case1" else None)

for d in [(2,2,2,2),(3,3,3,3),(2,2,2,2,2)]:
    print("=== d =", d, "===")
    path, s, f = make_trace(d)
    for step in path:
        print("  ", step)
    print()

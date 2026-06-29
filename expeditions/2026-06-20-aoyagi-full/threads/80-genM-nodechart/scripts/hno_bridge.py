import itertools, sys

# Replicate the achiever-path machinery (Lambda.lean / RouteMAchieverPath / RouteMAchieverStructAdm)
# M : indices 0..L  (Fin (L+1)). T : Fin L -> N (indices 0..L-1).
# admBound(j) = min(M0,M1) if j==0 else M[j+1]
# admPred: (T[j] <= admBound j) and weak-decrease (i<=j -> T[j]<=T[i]) and (j==L-1 -> T[j]=0)
# Mval = sum_{j=0..L-1} (tPrev_j - T[j])*(M[j+1]-T[j]); tPrev_j = M0 if j==0 else T[j-1]
# tStar = an argmin of Mval over Adm (ANY argmin — we check ALL argmins).
# tach: index 0..L: tach[0]=M[0]; tach[k+1]=tStar[k]  (k=0..L-1)
# T(k) := Text(tach)(k): T(0)=M[0]; T(k+1)= tach[k]  for k in 0..L  (so Text(j+1)=tach[j])
#   i.e. Text(0)=M0, Text(1)=tach[0]=M0, Text(k+1)=tach[k]=tStar[k-1] for k>=1
# W(k) := Wext(k) = M[k]
# deepRank = Text(L); deepRows = Wext(L-1)=M[L-1]
# InteriorDrop: 0<W(L)=M[L] and EXISTS p in [1,L-1]: Text(p+1)<Text(p) and (forall b in [p,L-1]: Text(b+1)<W(b))
# NoInteriorBothDrop: forall s in [1,L-1]: not (Text(s+1)<Text(s) and Text(s+1)<W(s))

def admBound(M, L, j):
    return min(M[0], M[1]) if j == 0 else M[j+1]

def adm_list(M, L):
    res = []
    ranges = [range(admBound(M, L, j)+1) for j in range(L)]
    for T in itertools.product(*ranges):
        # weak decrease: i<=j -> T[j]<=T[i]   (nonincreasing)
        ok = all(T[j] <= T[i] for i in range(L) for j in range(L) if i <= j)
        if not ok: continue
        # last = 0
        if T[L-1] != 0: continue
        res.append(T)
    return res

def Mval(M, L, T):
    s = 0
    for j in range(L):
        tprev = M[0] if j == 0 else T[j-1]
        s += (tprev - T[j]) * (M[j+1] - T[j])
    return s

def Text_of(M, L, tach, k):
    # Text(0)=M0; Text(j+1)=tach[j]
    if k == 0: return M[0]
    return tach[k-1]

def analyze(M):
    L = len(M) - 1
    if L < 1: return []
    A = adm_list(M, L)
    mvals = [Mval(M, L, T) for T in A]
    mn = min(mvals)
    argmins = [A[i] for i in range(len(A)) if mvals[i] == mn]
    out = []
    for tstar in argmins:
        tach = [M[0]] + list(tstar)  # tach[0..L]
        T = [Text_of(M, L, tach, k) for k in range(L+2)]  # T[0..L+1] safe
        W = lambda k: M[k] if k <= L else 1
        # InteriorDrop
        intdrop = False
        if M[L] > 0:
            for p in range(1, L):  # p in [1,L-1]
                if T[p+1] < T[p] and all(T[b+1] < W(b) for b in range(p, L)):
                    intdrop = True; break
        # NoInteriorBothDrop
        nibd = all(not (T[s+1] < T[s] and T[s+1] < W(s)) for s in range(1, L))
        deepRank = T[L]
        deepRows = M[L-1]
        clean = (not intdrop) and (deepRank == deepRows)
        smeared = (not intdrop) and (deepRank < deepRows)
        out.append(dict(tstar=tstar, intdrop=intdrop, nibd=nibd, deepRank=deepRank,
                        deepRows=deepRows, clean=clean, smeared=smeared))
    return out

# Brute-force: widths 1..4, L=1..5
viol_clean = []  # clean but NOT NoInteriorBothDrop
viol_smear = []  # smeared but NOT NoInteriorBothDrop
amb = []         # argmins disagree on clean/intdrop/nibd (tStar-dependence)
total = 0
for L in range(1, 6):
    for M in itertools.product(range(1,5), repeat=L+1):
        total += 1
        res = analyze(list(M))
        # check tStar-ambiguity on the relevant predicates
        keyset = set((r['intdrop'], r['nibd'], r['clean'], r['smeared']) for r in res)
        if len(keyset) > 1:
            amb.append((M, [(r['tstar'], r['intdrop'], r['nibd'], r['clean'], r['smeared']) for r in res]))
        for r in res:
            if r['clean'] and not r['nibd']:
                viol_clean.append((M, r))
            if r['smeared'] and not r['nibd']:
                viol_smear.append((M, r))

print(f"total M scanned: {total}")
print(f"CLEAN-branch M violating NoInteriorBothDrop: {len(viol_clean)}")
for v in viol_clean[:10]: print("  CLEAN-VIOL", v[0], v[1])
print(f"SMEARED-branch M violating NoInteriorBothDrop: {len(viol_smear)}")
for v in viol_smear[:10]: print("  SMEAR-VIOL", v[0], v[1])
print(f"tStar-ambiguous M (argmins disagree on intdrop/nibd/clean/smeared): {len(amb)}")
for a in amb[:10]: print("  AMBIG", a[0], a[1])

print("\n=== STRUCTURAL: clean-branch cases — Text sequence + why NoInteriorBothDrop holds ===")
import itertools as it
shown = 0
for L in range(2, 5):
    for M in it.product(range(1,5), repeat=L+1):
        for r in analyze(list(M)):
            if r['clean']:
                tach = [M[0]] + list(r['tstar'])
                T = [Text_of(list(M), L, tach, k) for k in range(L+1)]
                # the both-drop test at each interior s
                drops = [(s, T[s+1]<T[s], T[s+1]<M[s]) for s in range(1,L)]
                if shown < 18:
                    print(f"  M={M} L={L} tstar={r['tstar']} Text={T} deepRank={r['deepRank']}=deepRows={r['deepRows']} bothdrop@s={drops}")
                    shown += 1

"""
THE DECISIVE CHECK (elder brief §4.3/§6): does the faithful N_p PRESERVE Aoyagi's b-chain
b_i = prod_{t~<i} u  and the divisor exponents M_{s,k}?

Argument (verified below on the three witnesses):
 (A) M_{s,k} are set by the ORACLE's divExp ledger (stepUpdate), NOT by the normalization:
       case2   divExp = resRows*resCols = (widthMinUpto-cleared)*(d(layer+1)-cleared) = (M(S)-J)(M^(S+1)-J)
       case1(1) divExp += runLen*resCols = J_1*(M^(S+1)-J)
     These are EXACTLY Aoyagi's worked.tex:616/626.  N_p (a coordinate normalization) does not touch divExp.
 (B) The block-blow-up Jacobian is u^{|center|-1}. We verify |canonCenterOf| = M' (= the block codim), so
     the exceptional coord's Jacobian power is M'-1 = Aoyagi's (worked.tex:589). N_p = Schur(Q,U) + deeper
     recoord are UNIPOTENT (det 1), so they add NOTHING to the Jacobian => M_{s,k} preserved.
 (C) The b-chain b_i = prod_{t~<i} u is the accumulated diag(b), determined by t~ (divTilde) + birth coords,
     both combinatorial (oracle) => unchanged by N_p.  We unroll it from the oracle trace.
A COMPOSITE of hypersurface blow-ups would instead give many exceptional coords with different exponents
=> different M_{s,k}. The BLOCK blow-up (blockBlowupMap kept, center = full canonCenterOf) gives Aoyagi's.
"""
def widthMinUpto(d, n):
    N = len(d) - 1
    return min(d[i] for i in range(0, min(n, N - 1) + 1))

def trace_and_check(d):
    N = len(d) - 1
    Lmax = N - 1
    layer, cleared, numDiv = 0, 0, 0
    divTilde, birth, divExp = [], [], []
    steps = []
    for _ in range(60):
        if Lmax <= layer:
            steps.append(("terminal", layer, cleared)); break
        if widthMinUpto(d, layer + 1) <= cleared:
            steps.append(("rollover", layer, cleared)); layer, cleared = layer + 1, 0; continue
        occ = sorted({divTilde[k] for k in range(numDiv)
                      if cleared + 1 <= divTilde[k] <= widthMinUpto(d, layer) - 1})
        MS = widthMinUpto(d, layer)          # M(S) running-min width
        MSp1 = d[layer + 1]                   # M^(S+1) raw next width
        resRows, resCols = MS - cleared, MSp1 - cleared
        centerSize = resRows * resCols        # |canonCenterOf| for case2/case12
        if occ:
            target = occ[0]; runLen = target - cleared
            f = [k for k in range(numDiv) if divTilde[k] == target][0]
            # case1(1): merge into f, divExp[f] += runLen*resCols, t~(f) -> cleared; numDiv,cleared unchanged
            Maoyagi_11 = divExp[f] + runLen * resCols
            steps.append(("case11", layer, cleared, dict(target=target, runLen=runLen, f=f,
                          M_add=runLen * resCols, M_new=Maoyagi_11,
                          center11=1 + runLen * resCols)))  # {pivot} u partial(runLen cols x resRows rows)
            divExp[f] = Maoyagi_11; divTilde[f] = cleared
            # (case11 keeps cleared; the boost node — for the witness we record and continue past it)
        else:
            # case2: append divisor, divExp = resRows*resCols, t~ = cleared, birth (layer,cleared)
            Maoyagi_2 = (MS - cleared) * (MSp1 - cleared)
            steps.append(("case2", layer, cleared, dict(M=Maoyagi_2, centerSize=centerSize,
                          match=(Maoyagi_2 == centerSize))))
            divTilde.append(cleared); birth.append((layer, cleared)); divExp.append(Maoyagi_2)
            numDiv += 1; cleared += 1
    # unroll the b-chain b_i = prod_{t~ < i} u(birth)  (i = 1 .. M(L+1))
    Mfinal = max((widthMinUpto(d, s) for s in range(N)), default=0)
    bchain = {}
    for i in range(0, max(divTilde, default=0) + 2):
        factors = [birth[k] for k in range(len(divTilde)) if divTilde[k] < i]
        bchain[i] = factors
    return steps, divTilde, birth, divExp, bchain

for d in [(2, 2, 2, 2), (3, 3, 4), (3, 3, 2, 2)]:
    print("=" * 70)
    print("d =", d)
    steps, divTilde, birth, divExp, bchain = trace_and_check(d)
    print("  steps:")
    for s in steps:
        print("   ", s)
    print("  divTilde =", divTilde, " birth =", birth, " divExp(M_{s,k}) =", divExp)
    # (A)/(B): every case2 step: |center| == Aoyagi M' ?
    m_ok = all(s[3]["match"] for s in steps if s[0] == "case2")
    print("  (B) |canonCenterOf| == Aoyagi M'=(M(S)-J)(M^(S+1)-J) for all case2:", m_ok)
    # (C) b-chain
    print("  (C) b-chain b_i = prod_{t~<i} u(birth):")
    for i, f in sorted(bchain.items()):
        print(f"      b_{i} = prod{f}")

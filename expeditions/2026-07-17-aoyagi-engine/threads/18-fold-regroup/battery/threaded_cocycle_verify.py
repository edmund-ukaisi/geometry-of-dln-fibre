#!/usr/bin/env python3
# guards: coverage-theorem
# provenance: threads/18-fold-regroup (pnp-fold). Follow-up cert: the GLOBAL THREADED cocycle.
#
# Verifies the acc-generalized incoming-ledger invariant that threads buildTree's stepUpdate from conRoot:
#
#   Inv(acc, s):   |det D acc w|  =  L(s)(w) := prod_{k<s.numDiv} |z_{diag(s,k)}(w)|^{s.divExp k - 1}
#
# where diag(s,k) = the divisor's divBirthCoord DIAGONAL cell (= c.divCoord, by the (beta) coherence).
# Base: conRoot (numDiv 0) => L = 1 = |det D id|. Maintenance per stepUpdate case, adding chart B =
# geoChartMapNorm(e) at the INNERMOST (acc' = acc o B):
#
#   |det D acc' w| = |det D acc (B w)| * |det D B w|      (chain rule)
#                  = L(s)(B w) * |z_{diagTargetOf(e)}(w)|^{dCN-1}   (Inv + the swap atom)
#                  =? L(s')(w)                             (the per-case MAINTENANCE identity)
#
# This confirms L(s)(B w) (the OLD ledger pulled back through the new chart) supplies case-1(2)'s
# inheritance LOCALLY (no ancestor needed) -- the resolution of the non-locality of the original cert.
# Exact symbolic; |det| (the swap S contributes det -1).
import sympy as sp

def swap(pt, a, b):
    out = dict(pt); out[a], out[b] = pt[b], pt[a]; return out
def blowup(pt, center, pivot):
    piv = pt[pivot]
    return {c: (piv if c == pivot else (piv*pt[c] if c in center else pt[c])) for c in pt}
def norm_chart(pt, node):
    """geoChartMapNorm on-cone = geoChartMap(center,pivot) o swap(pivot,diag). Chartless (dCN0): id."""
    if node.get('chartless'): return dict(pt)
    return blowup(swap(pt, node['pivot'], node['diag']), node['center'], node['pivot'])

def Lmon(divs, valfun):
    """L(s) as a monomial in the given value assignment (dict cell->expr): prod z_diag^{divExp-1}."""
    m = sp.Integer(1)
    for d in divs:
        m *= valfun[d['diag']] ** (d['divExp'] - 1)
    return sp.factor(m)

def jac_abs_det(compose_fn, cells):
    src = {c: sp.Symbol('z_'+c, positive=True) for c in cells}
    pt = compose_fn(src)
    order = list(cells)
    J = sp.Matrix([[sp.diff(pt[r], src[c]) for c in order] for r in order])
    return sp.factor(sp.Abs(J.det())), src

# ---- the run: a depth-4 MIXED path + rollover + a second birth, states tracked explicitly ----------
# cells: dA,x01,x10,x11 (A's 2x2 block); dB,yB (B's d-block, size 2); f (A-merge d-block); g (B-merge);
#        dC,z01,z10,z11 (C's block after rollover)
CELLS = ['dA','x01','x10','x11','dB','yB','f','g','dC','z01','z10','z11']

# each edge: node (center/pivot/diag or chartless) + the resulting state's divisor list (diag,divExp)
STEPS = [
  # e1 case-2 births A: 2x2 block, off-diag pivot x11, diag dA, dCN=4 -> divExp(A)=4
  dict(node=dict(center=['dA','x01','x10','x11'], pivot='x11', diag='dA'),
       state=[dict(diag='dA',divExp=4)], label="case-2 births A (dCN4)"),
  # e2 case-1(2) split B off A: center {dA(u-corner)} u {dB,yB}, off-diag pivot yB, diag dB, dCN=3
  #     divExp(B) = divExp(A) + (dCN-1)=2 -> 4+2 = 6 ; A unchanged
  dict(node=dict(center=['dA','dB','yB'], pivot='yB', diag='dB'),
       state=[dict(diag='dA',divExp=4), dict(diag='dB',divExp=6)], label="case-1(2) split B off A (inherit)"),
  # e3 case-1(1) merge into A: center {dA} u {f}, pivot dA (=diag, S=id), dCN=2 -> divExp(A)+=1 -> 5
  dict(node=dict(center=['dA','f'], pivot='dA', diag='dA'),
       state=[dict(diag='dA',divExp=5), dict(diag='dB',divExp=6)], label="case-1(1) merge into A (+1)"),
  # e4 case-1(1) merge into B: center {dB} u {g}, pivot dB (=diag, S=id), dCN=2 -> divExp(B)+=1 -> 7
  dict(node=dict(center=['dB','g'], pivot='dB', diag='dB'),
       state=[dict(diag='dA',divExp=5), dict(diag='dB',divExp=7)], label="case-1(1) merge into B (+1)"),
  # e5 rollover: chartless, ledger unchanged (only cleared:=0), no chart
  dict(node=dict(chartless=True),
       state=[dict(diag='dA',divExp=5), dict(diag='dB',divExp=7)], label="rollover (L-neutral, chartless)"),
  # e6 case-2 births C: fresh 2x2 block, off-diag pivot z11, diag dC, dCN=4 -> divExp(C)=4
  dict(node=dict(center=['dC','z01','z10','z11'], pivot='z11', diag='dC'),
       state=[dict(diag='dA',divExp=5), dict(diag='dB',divExp=7), dict(diag='dC',divExp=4)],
       label="case-2 births C after rollover (dCN4)"),
]

def run():
    print("== THREADED cocycle: per-step maintenance L(s)(B w)*atom == L(s')(w), and cumulative ==")
    allok = True
    # nodes root-first; the fold acc = norm(e1) o norm(e2) o ... (root outermost).
    nodes = [st['node'] for st in STEPS]
    # per-step maintenance: for step i (edge e_i at incoming state s_{i-1}, child s_i)
    prev_state = []   # conRoot: numDiv 0
    for i, st in enumerate(STEPS):
        node, s_new = st['node'], st['state']
        src = {c: sp.Symbol('z_'+c, positive=True) for c in CELLS}
        # atom of this edge:
        if node.get('chartless'):
            atom = sp.Integer(1)
        else:
            dCN = len(node['center'])
            atom = src[node['diag']] ** (dCN - 1)
        # L(s_{i-1}) pulled back through B = norm_chart(node):  L(prev)(B w)
        Bw = norm_chart(src, node)
        L_prev_at_Bw = Lmon(prev_state, Bw)
        L_new_at_w = Lmon(s_new, src)
        lhs = sp.factor(L_prev_at_Bw * atom)
        ok = sp.simplify(lhs - L_new_at_w) == 0
        allok &= ok
        print(f"  [{'PASS' if ok else 'FAIL'}] step {i+1}: {st['label']}")
        print(f"        L(s_prev)(B w)*atom = {lhs}")
        print(f"        L(s_new)(w)         = {L_new_at_w}")
        prev_state = s_new
    # cumulative: |det D (fold of first i charts)| == L(s_i) for every prefix i
    print("  -- cumulative prefixes: |det D Phi^(i)| == L(s_i) --")
    for i in range(1, len(STEPS)+1):
        prefix = nodes[:i]
        def comp(src, prefix=prefix):
            pt = dict(src)
            for node in reversed(prefix):        # deepest of the prefix first, root last
                pt = norm_chart(pt, node)
            return pt
        det, src = jac_abs_det(comp, CELLS)
        Li = Lmon(STEPS[i-1]['state'], src)
        ok = sp.simplify(det - Li) == 0
        allok &= ok
        print(f"  [{'PASS' if ok else 'FAIL'}] prefix {i}: |det Phi^({i})| = {det}  vs L(s_{i}) = {Li}")
    print()
    print("VERDICT:", "PASS -- threaded invariant holds step-by-step and cumulatively; conRoot base L=1; "
          "case-1(2) inheritance local via L(s)(B w)" if allok else "FAIL")
    return allok

if __name__ == "__main__":
    import sys; sys.exit(0 if run() else 1)

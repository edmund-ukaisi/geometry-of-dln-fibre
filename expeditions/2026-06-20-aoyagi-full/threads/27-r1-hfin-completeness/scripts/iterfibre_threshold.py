#!/usr/bin/env python3
"""
iterfibre_threshold.py — does the iterated-fibre route's threshold = ½·minAdm for general M?

THE ITERATED-FIBRE THRESHOLD ACCOUNTING (from MatMulFibre / RouteM4422Hfin):
  fibre_lintegral_mul_le: ∫_X frobSq(X·Y)^{−c'} ≤ const · frobSq(Y)^{−c'}, finite iff c' < p/2,
  p = ROW count of the left factor X.
  Iterate outside-in: F = ‖A0·A1·…·A_{L-1}‖². Peel A0 (X=A0 [M0×M1], Y=A1…A_{L-1} [M1×M_L]): threshold M0/2.
  Then A1 (X=A1 [M1×M2], Y=A2… [M2×M_L]): threshold M1/2. … Peel A_{L-2}: threshold M_{L-2}/2.
  TERMINAL: the last factor A_{L-1} [M_{L-1}×M_L], frobSq over its full M_{L-1}·M_L entries (Morse):
  threshold = M_{L-1}·M_L / 2.
  So the route's GUARANTEED finiteness threshold (the MIN over the chain, since the integral is finite
  iff EVERY peel's threshold is exceeded... no: finite for c' < min of all the thresholds):
    iterfibre_thr(M) = min( min_{s=0}^{L-2} M_s/2 , M_{L-1}·M_L/2 ).
  Compare to ½·minAdm(M).

CRUX: per-peel threshold is M_s/2 (the LEFT-factor row count), NOT the codim. Does min = ½·minAdm?
"""
import sys
sys.path.insert(0,'/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/26-r1-genM-chart/scripts')
from genM_structure import minAdmRec
from fractions import Fraction as F

def iterfibre_thr(M):
    M=tuple(M); L=len(M)-1
    # peels for layers 0..L-2 (left-factor rows M_0..M_{L-2}); terminal = last factor M_{L-1}*M_L
    peel_thrs = [F(M[s],2) for s in range(L-1)]   # s=0..L-2
    terminal = F(M[L-1]*M[L], 2)
    return min(peel_thrs + [terminal]) if (peel_thrs or True) else terminal

def report(M):
    M=tuple(M)
    it = iterfibre_thr(M)
    ma = F(minAdmRec(M)[0], 2)
    L=len(M)-1
    peels=[F(M[s],2) for s in range(L-1)]; term=F(M[L-1]*M[L],2)
    status = "MATCH" if it==ma else ("WEAKER" if it<ma else "STRONGER(?!)")
    print(f"M={M}: iterfibre min(peels={[str(p) for p in peels]}, term={term})={it}  vs ½·minAdm={ma}  -> {status}")
    return it, ma

if __name__=="__main__":
    print("Iterated-fibre threshold = min(M_s/2 per peel, terminal M_{L-1}M_L/2) vs ½·minAdm:\n")
    for M in [(2,2,2),(2,1,2),(4,4,2,2),(2,2,4),(3,3,3),(3,3,4),(3,3,3,3),(4,4,4),(5,3,4),(2,3,4,2)]:
        report(M)

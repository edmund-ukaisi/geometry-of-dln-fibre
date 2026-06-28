# Enumerate the 46 boundary-smeared M and split by minAdm regime (=1 vs >=2)
# and by (r,c,s) shape, to see how many distinct parametric shapes the Lean must cover.
import itertools, sys
# Reuse the gate's M-enumeration + Text/minAdm. Import from the gate if it exposes them.
sys.path.insert(0, '.')
try:
    import pp_smear_GATE as G
    smeared = G.enumerate_smeared() if hasattr(G,'enumerate_smeared') else None
except Exception as e:
    smeared = None
    print("could not import enumerator:", e)
print("has enumerate_smeared:", smeared is not None)

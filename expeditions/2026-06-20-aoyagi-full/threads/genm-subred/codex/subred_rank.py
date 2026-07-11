import numpy as np
rng=np.random.default_rng(3)
# rank(A2 A3 ... AL) = min tail width (generic).  So the image row-space of
# Y -> Y*Atail has dim = min(M2,...,q), and the good-stratum codim (effective
# 'q' in wtint's q-b+1) is min(tail widths), NOT the final width q=M_last.
print("generic rank(product) = min width:")
for widths in [(2,1,3),(3,2,4),(4,2,2,5),(3,3,1,3),(5,2,3,4)]:
    P=np.eye(widths[0])
    for i in range(len(widths)-1):
        P=P@rng.standard_normal((widths[i],widths[i+1]))
    print(f"  widths {widths}: rank(prod)={np.linalg.matrix_rank(P)}  min={min(widths)}")
print()
print("=> effective free-'q' = rank(Atail) = min(M2,...,M_last), the MIN TAIL WIDTH.")
print("   good-stratum codim = min(tail)-b+1;  Cat-I boundary a+b <= min(tail),")
print("   NOT a+b<=q. wtint's q-b+1 is the special case (tail non-contracting).")

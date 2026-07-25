"""Coverage probe (indicative, MC-guided): does the VALID atlas (sigmaPiv pivot in {0,1,2,3,20})
cover a neighbourhood of 0, or do the shear-slot-argmax targets escape? And are coinciding-pivot
charts NEEDED by the argmax routing (i.e. does the argmax of {0..7} coincide with argmax of {1,5,6,7})?
This is a GUIDE (float); the exact structural read is in the certificate."""
import random
random.seed(0)
# We probe the argmax structure of the OUTPUT of the inner blow-ups to see which pivots the routing hits.
# forward atoms (float)
permIdx={0:8,1:9,2:10,3:11,4:1,5:5,6:6,7:7,8:0,9:2,10:3,11:4}
def bb(center,piv,v): return [ v[piv] if k==piv else (v[piv]*v[k] if k in center else v[k]) for k in range(21)]
def perm(v): return [ v[permIdx.get(k,k)] for k in range(21)]
def shear(p):
    h=list(p); h[4]=p[4]+p[0]*p[2]; h[5]=p[5]+p[1]*p[2]; h[6]=p[6]+p[0]*p[3]; h[7]=p[7]+p[1]*p[3]
    h[8]=p[8]-p[0]*p[12]-p[1]*p[16]; h[9]=p[9]-p[0]*p[13]-p[1]*p[17]
    h[10]=p[10]-p[0]*p[14]-p[1]*p[18]; h[11]=p[11]-p[0]*p[15]-p[1]*p[19]; return h
def gwrap(w,p3,p2,p1):
    y=bb({1,5,6,7},p3,w); z=bb({0,1,2,3,4,5,6,7},p2,y); p=perm(z); h=shear(p); x=bb({0,1,2,3,4,5,6,7,20},p1,h); return x
# Sample source boxes over ALL 288 charts with |w|<=R; collect the IMAGE points; for each, ask:
# is the sigmaPiv-argmax over {0..7,20} a shear-slot {4,5,6,7}? and is |x_j|<=M|x20| (shear bound)?
R=0.7; N=40000
shslot_argmax=0; total=0; maxratio=0.0; bound_ok=0
for _ in range(N):
    p3=random.choice([1,5,6,7]); p2=random.choice(range(8)); p1=random.choice([0,1,2,3,4,5,6,7,20])
    w=[random.uniform(-R,R) for _ in range(21)]
    x=gwrap(w,p3,p2,p1)
    total+=1
    sc={0,1,2,3,4,5,6,7,20}
    am=max(sc,key=lambda k:abs(x[k]))
    if am in {4,5,6,7}: shslot_argmax+=1
    if abs(x[20])>1e-12:
        r=max(abs(x[j])/abs(x[20]) for j in [4,5,6,7]); maxratio=max(maxratio,r)
        if r<=3.0: bound_ok+=1
print(f"image points sampled: {total}")
print(f"  frac with sigmaPiv-argmax in shear-slots {{4,5,6,7}}: {shslot_argmax/total:.3f}")
print(f"  max observed |x_j|/|x_20| over shear-slots (j in 4..7): {maxratio:.3f}")
print(f"  frac with |x_j|/|x_20| <= 3 (all shear-slots): {bound_ok/total:.3f}")
# coinciding necessity: over random ball directions, how often does argmax{0..7} == argmax{1,5,6,7}?
coin=0
for _ in range(N):
    x=[random.uniform(-1,1) for _ in range(21)]
    a0=max(range(8),key=lambda k:abs(x[k])); a1=max([1,5,6,7],key=lambda k:abs(x[k]))
    if a0==a1: coin+=1
print(f"  frac of directions where argmax{{0..7}}==argmax{{1,5,6,7}} (coinciding p2==p3 needed): {coin/N:.3f}")

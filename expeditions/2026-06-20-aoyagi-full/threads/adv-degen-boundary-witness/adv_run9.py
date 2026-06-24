import numpy as np
# Clean numeric RLCT estimate via log-log slope of vol{F<eps}. lambda = d log vol / d log eps.
# (GUIDE ONLY; the certificate is the smooth-codim-nReg normal form.) Use importance sampling on the
# natural scale and a fixed large box, estimate the density of states near 0.
rng=np.random.default_rng(1)
def F_212(x):
    a,b,p,q=x[:,0],x[:,1],x[:,2],x[:,3]
    return ((1+a)*(1+p)-1)**2 + ((1+a)*q)**2 + (b*(1+p))**2 + (b*q)**2

# Use a small FIXED box and many samples; estimate vol{F<eps} for a ladder of eps, take consecutive slopes.
L=0.3  # half-width of fixed box around 0
N=20_000_000
X=(rng.random((N,4))*2-1)*L
vals=F_212(X)
boxvol=(2*L)**4
epss=np.array([10.0**(-k) for k in range(2,8)])
vols=np.array([np.mean(vals<e)*boxvol for e in epss])
print("(2,1,2) r=1, nReg=3, predicted rlct=3/2=1.5")
print(f"{'eps':>10}{'vol{F<eps}':>14}{'count':>10}")
counts=[int(np.sum(vals<e)) for e in epss]
for e,v,c in zip(epss,vols,counts):
    print(f"{e:>10.0e}{v:>14.3e}{c:>10}")
print("consecutive log-log slopes (-> rlct):")
for i in range(len(epss)-1):
    if vols[i+1]>0:
        slope=(np.log(vols[i])-np.log(vols[i+1]))/(np.log(epss[i])-np.log(epss[i+1]))
        print(f"  eps {epss[i]:.0e}->{epss[i+1]:.0e}: slope = {slope:.3f}  (count {counts[i]}->{counts[i+1]})")

# Also a degenerate-boundary case with nReg even & a flat dir: (3,1,3) r=1 nReg=5, predicted rlct=5/2=2.5
print()
def F_313(x):
    # C1=(1+u0,u1,u2)^T, C2=(1+v0,v1,v2). product 3x3, B=e00. F=sum (P-B)^2
    u0,u1,u2,v0,v1,v2=[x[:,k] for k in range(6)]
    P00=(1+u0)*(1+v0); P01=(1+u0)*v1; P02=(1+u0)*v2
    P10=u1*(1+v0); P11=u1*v1; P12=u1*v2
    P20=u2*(1+v0); P21=u2*v1; P22=u2*v2
    return (P00-1)**2+P01**2+P02**2+P10**2+P11**2+P12**2+P20**2+P21**2+P22**2
L=0.3; N=20_000_000
X=(rng.random((N,6))*2-1)*L
vals=F_313(X); boxvol=(2*L)**6
print("(3,1,3) r=1, nReg=5, predicted rlct=5/2=2.5")
vols=np.array([np.mean(vals<e)*boxvol for e in epss]); counts=[int(np.sum(vals<e)) for e in epss]
for i in range(len(epss)-1):
    if vols[i+1]>0 and counts[i+1]>50:
        slope=(np.log(vols[i])-np.log(vols[i+1]))/(np.log(epss[i])-np.log(epss[i+1]))
        print(f"  eps {epss[i]:.0e}->{epss[i+1]:.0e}: slope = {slope:.3f}  (count {counts[i]}->{counts[i+1]})")

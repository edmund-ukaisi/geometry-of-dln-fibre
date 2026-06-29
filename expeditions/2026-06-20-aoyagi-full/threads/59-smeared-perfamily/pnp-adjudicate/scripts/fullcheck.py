import sympy as sp, random

def full_l2_check(M0, M1, M2, trials=120, label=""):
    """
    Full L=2 smeared check (r=M0 square, the bottleneck case). Build the decoded Params entrywise and
    confirm: (i) cancellation P1*Lam0=P2 (off pole), (ii) every decoded entry (front + deep-top + deep-bot)
    has |.| <= 2*delta  => containment in cubeBox(2 delta). Conditioned box:
       A0 front: the r diagonal cols-block 'P1 diagonal' in [delta/2,delta]; everything else in [-eta,eta].
       z (pivot) in (0,delta); Hbar angular top coords in [-eta,eta] (pivot entry =1); S_bot in [-eta,eta].
    eta = delta/(4(r-1)) for r>=2, else delta/4.
    """
    r=M0; s=M1-M0; assert s>0
    delta=sp.Rational(1,1)
    eta=(delta/4 if r==1 else delta/(4*(r-1)))
    fails=0; max_entry=sp.Rational(0); cancel_fail=0
    for t in range(trials):
        rng=random.Random(2000+M0*131+M1*17+M2*5+t)
        def rr(lo,hi): 
            return lo+(hi-lo)*sp.Rational(rng.randint(0,1000),1000)
        # A0: M0 x M1. The 'top r columns' = P1 (deepWidthEquiv inl), 'bottom s' = P2 (inr).
        # Condition P1: diagonal (i,i)-block in [delta/2,delta], off-diag in [-eta,eta]. P2 in [-eta,eta].
        A0=sp.zeros(M0,M1)
        for i in range(M0):
            for k in range(r):   # top r columns -> P1
                A0[i,k] = rr(delta/2,delta) if i==k else rr(-eta,eta)
            for k in range(s):   # bottom s columns -> P2
                A0[i,r+k] = rr(-eta,eta)
        P1=A0[:,:r]; P2=A0[:,r:]
        dG=(P1.T*P1).det()
        if dG==0: continue
        Lam0=(P1.T*P1).inv()*P1.T*P2
        if not (P1*Lam0-P2).is_zero_matrix: cancel_fail+=1
        # Hbar: r x M2, pivot (0,0)=1, others in [-eta,eta]; z in (0,delta); S_bot: s x M2 in [-eta,eta]
        z=rr(sp.Rational(1,1000),delta)
        Hbar=sp.Matrix(r,M2, lambda a,j: (sp.Integer(1) if (a==0 and j==0) else rr(-eta,eta)))
        Sbot=sp.Matrix(s,M2, lambda b,j: rr(-eta,eta))
        # decoded deep-top: z*Hbar - Lam0*Sbot (r x M2); deep-bottom: Sbot (s x M2)
        top = z*Hbar - Lam0*Sbot
        # all flat coords: A0 entries (front), top entries, Sbot entries
        ents=[abs(A0[i,j]) for i in range(M0) for j in range(M1)]
        ents+=[abs(top[a,j]) for a in range(r) for j in range(M2)]
        ents+=[abs(Sbot[b,j]) for b in range(s) for j in range(M2)]
        me=max(ents); max_entry=max(max_entry,me)
        if me > 2*delta: fails+=1
    print(f"{label} (M0,M1,M2)=({M0},{M1},{M2}) r={r} s={s} eta={eta}: cancel-fail={cancel_fail}, "
          f"max|decoded entry|={max_entry} (need<=2), containment-fail={fails}/{trials}")

full_l2_check(2,3,1, label="ANCHOR (2,3,1)")
full_l2_check(2,4,2, label="NON-SQUARE M #1 (2,4,2)")
full_l2_check(3,5,2, label="NON-SQUARE M #2 (3,5,2)")
full_l2_check(1,4,3, label="r=1 edge (1,4,3)")
full_l2_check(5,7,2, label="r=5 (specific delta/8 box would break) (5,7,2)")

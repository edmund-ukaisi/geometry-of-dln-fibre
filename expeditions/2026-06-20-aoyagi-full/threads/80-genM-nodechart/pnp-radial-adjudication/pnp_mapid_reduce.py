import sympy as sp
# Verify the map identity phi = B ∘ blowup reduces to PER-BLOCK value equalities (same grain as schurFrameProd_block_*).
# Strategy: show each chart entry phi[k] equals B[k] evaluated at blowup(x), and that the ONLY place they differ
# pre-blowup is the u-scaling of E/leaf -- which the blow-up supplies. I.e. the reduction is:
#   chart Schur frame bottom-right = XKN + u*E_k  =  B's bottom-right (XKN + E'_k) with E'_k := blowup-coord = u*E_k.
# So the identity is: for the E-block coords, blowup(x)_E = u * x_E (definition of pivotBlowupOn), and B reads
# that directly. NO new lemma beyond: (a) schurFrameProd_block_* [banked], (b) pivotBlowupOn_apply on actives [banked].
x = sp.symbols('x0:27', real=True); u=x[0]; active=[13,14,24,25,26]
def chart(R_scale):  # R_scale multiplies E/leaf; chart uses u, B-at-blown uses the blown coord
    B1=sp.Matrix([[x[1],x[1]*x[2]],[x[1]*x[3],x[1]*x[2]*x[3]+x[4]],[x[1]*x[3]*x[6]+x[1]*x[5],x[1]*x[2]*x[5]+x[6]*(x[1]*x[2]*x[3]+x[4])]])
    B2=sp.Matrix([[x[9]],[x[10]*x[9]]]);N1=sp.Matrix([[x[7]],[x[8]]]);N2=sp.Matrix([[x[11],x[12]]])
    W1=sp.Matrix([[x[15],x[16],x[17]]]);W2=sp.Matrix([[x[18],x[19],x[20]],[x[21],x[22],x[23]]])
    R1=sp.Matrix([[0,0,0],[0,0,0],[0,0,1]]);R2=sp.Matrix([[0,0,0],[0,x[13],x[14]]]);Rf=sp.Matrix([[x[24],x[25],x[26]]])
    C3=R_scale*Rf;C2=B2*sp.Matrix.hstack(sp.eye(1),N2)+R_scale*R2;C1=B1*sp.Matrix.hstack(sp.eye(2),N1)+R_scale*R1
    A0=C1;A1=sp.Matrix.vstack(C2-N1*W1,W1);A2=sp.Matrix.vstack(C3-N2*W2,W2)
    return [sp.expand(A[i,j]) for A in (A0,A1,A2) for i in range(A.rows) for j in range(A.cols)]
phi=chart(u)
# B(y) via de-scaled decoder (R_scale on E/leaf becomes the y-coord; anchor 1 -> y_p). 
# Then B(blowup(x)): blowup sends x_active -> u*x_active, x0->x0. So in B, reading y_active = u*x_active,
#   and the anchor y_p = x0 = u. So B(blowup(x)) should = chart(u). The reduction: B's E/leaf entries are
#   blowup(x)_E = u*x_E, exactly the chart's u*E. Verify B(blowup) == phi via the descaled construction:
y=sp.symbols('y0:27',real=True)
def B_descaled():
    yp=y[0]
    B1=sp.Matrix([[y[1],y[1]*y[2]],[y[1]*y[3],y[1]*y[2]*y[3]+y[4]],[y[1]*y[3]*y[6]+y[1]*y[5],y[1]*y[2]*y[5]+y[6]*(y[1]*y[2]*y[3]+y[4])]])
    B2=sp.Matrix([[y[9]],[y[10]*y[9]]]);N1=sp.Matrix([[y[7]],[y[8]]]);N2=sp.Matrix([[y[11],y[12]]])
    W1=sp.Matrix([[y[15],y[16],y[17]]]);W2=sp.Matrix([[y[18],y[19],y[20]],[y[21],y[22],y[23]]])
    R1=sp.Matrix([[0,0,0],[0,0,0],[0,0,yp]])  # anchor 1 -> y_p
    R2=sp.Matrix([[0,0,0],[0,y[13],y[14]]]); Rf=sp.Matrix([[y[24],y[25],y[26]]])
    C3=Rf;C2=B2*sp.Matrix.hstack(sp.eye(1),N2)+R2;C1=B1*sp.Matrix.hstack(sp.eye(2),N1)+R1
    A0=C1;A1=sp.Matrix.vstack(C2-N1*W1,W1);A2=sp.Matrix.vstack(C3-N2*W2,W2)
    return [sp.expand(A[i,j]) for A in (A0,A1,A2) for i in range(A.rows) for j in range(A.cols)]
B=B_descaled()
bl=[x[i] if i==0 else (u*x[i] if i in active else x[i]) for i in range(27)]  # pivotBlowupOn(active,0)
Bbl=[sp.expand(e.subs({y[i]:bl[i] for i in range(27)})) for e in B]
ok=all(sp.simplify(Bbl[i]-phi[i])==0 for i in range(27))
print("phi == B ∘ pivotBlowupOn (de-scaled B, anchor->y_p)?", ok)
# Now the REDUCTION grain: which entries DIFFER between B(x) [un-blown] and phi(x)? Only the E/leaf-bearing ones.
B_at_x=[sp.expand(e.subs({y[i]:x[i] for i in range(27)})) for e in B]
diff_entries=[k for k in range(27) if sp.simplify(B_at_x[k]-phi[k])!=0]
print("entries where B(x) != phi(x) (pre-blowup):", diff_entries, "(these are exactly the u*E / u*leaf / anchor entries)")
for k in diff_entries:
    print(f"  out[{k}]: phi={phi[k]}   B(x)={B_at_x[k]}   (differ by the u-scaling on E/leaf/anchor)")

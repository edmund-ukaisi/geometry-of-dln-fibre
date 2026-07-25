import sympy as sp
u = sp.symbols('u0:21')
# gFaithful outputs x_k as functions of u (from Corank2FaithfulComposite.gFaithful)
x = [None]*21
x[0]=u[8]; x[1]=u[9]; x[2]=u[10]; x[3]=u[11]
x[4]=u[0]*u[1]+u[8]*u[10]; x[5]=u[0]*u[1]*u[5]+u[9]*u[10]
x[6]=u[0]*u[1]*u[6]+u[8]*u[11]; x[7]=u[0]*u[1]*u[7]+u[9]*u[11]
x[8]=u[0]-u[8]*u[12]-u[9]*u[16]; x[9]=u[0]*u[2]-u[8]*u[13]-u[9]*u[17]
x[10]=u[0]*u[3]-u[8]*u[14]-u[9]*u[18]; x[11]=u[0]*u[4]-u[8]*u[15]-u[9]*u[19]
for k in range(12,21): x[k]=u[k]
J = sp.Matrix(21,21, lambda i,j: sp.diff(x[i], u[j]))
detg = sp.factor(J.det())
print("det D(gFaithful) =", detg)
# sigmaPiv = blockBlowupMap {0..7,20} pivot 20: j=20 -> w20; j in 0..7 -> w20*wj; else wj
w = sp.symbols('w0:21')
S = set([0,1,2,3,4,5,6,7,20]); p=20
y=[None]*21
for j in range(21):
    if j==p: y[j]=w[p]
    elif j in S: y[j]=w[p]*w[j]
    else: y[j]=w[j]
Js = sp.Matrix(21,21, lambda i,j: sp.diff(y[i], w[j]))
dets = sp.factor(Js.det())
print("det D(sigmaPiv) =", dets, "  (expect w20^8)")
# gWrap = sigmaPiv ∘ gFaithful : det = det(sigmaPiv)(gFaithful u) * det(gFaithful)(u)
dets_at_g = dets.subs(w[20], x[20])  # w20 -> gFaithful u 20 = u20
print("det D(gWrap) =", sp.factor(dets_at_g*detg))

codex
I’ll treat this as a local RLCT calculation rather than a code task. I’m going to compute the small-width arithmetic directly and then derive the geometric picture from the rank-stratified resolution, keeping the single-pivot chart separate from the divisor that actually computes the threshold.
exec
/bin/bash -lc "python3 - <<'PY'
from math import inf

def minAdm(m,k,n):
    vals=[]
    for t in range(0, min(m,k)+1):
        vals.append((m-t)*(k-t)+t*n)
    return min(vals), vals
for M in [(2,2,5),(2,1,3),(1,1,4),(2,2,2),(1,1,4),(3,3,10),(3,2,5)]:
    m,k,n=M
    v, vals = minAdm(m,k,n)
    rv, rvals = minAdm(m-1,k-1,n) if m>=1 and k>=1 else (None, [])
    print(M, vals, 'min', v, 'red', rvals, rv, 'nReg', None if rv is None else v-rv)
PY" in /home/ubuntu/workspace/fm3-ga
2026-06-23T17:48:12.932305Z ERROR codex_app_server::bespoke_event_handling: request failed with client error: JSONRPCErrorError { code: -32000, data: None, message: "command execution approval is not supported in exec mode for thread `019ef598-95f0-70c0-a813-17b68856fb66`" }
 exited 1:
2026-06-23T17:48:12.933151Z ERROR codex_core::tools::router: error=exec_command failed for `/bin/bash -lc "python3 - <<'PY'
from math import inf

def minAdm(m,k,n):
    vals=[]
    for t in range(0, min(m,k)+1):
        vals.append((m-t)*(k-t)+t*n)
    return min(vals), vals
for M in [(2,2,5),(2,1,3),(1,1,4),(2,2,2),(1,1,4),(3,3,10),(3,2,5)]:
    m,k,n=M
    v, vals = minAdm(m,k,n)
    rv, rvals = minAdm(m-1,k-1,n) if m>=1 and k>=1 else (None, [])
    print(M, vals, 'min', v, 'red', rvals, rv, 'nReg', None if rv is None else v-rv)
PY"`: CreateProcess { message: "Rejected(\"rejected by user\")" }
codex
The discrepancy is real. The single-pivot Schur computation is correct, but the inference “there are `n` Morse squares, so the node contributes `n/2`” is only valid in the branch where that chart actually computes the RLCT.

**FACT: Single-Pivot Formula**

In Schur coordinates,
\[
F=y_0^2 H,\qquad |Jac|=|y_0|^{mk-1},
\]
and
\[
H=\|E\|^2+\|vE+SB_{\rm red}\|^2\asymp \|E\|^2+\|SB_{\rm red}\|^2.
\]
Thus, if
\[
\lambda_{\rm ch}=\operatorname{rlct}(\|SB_{\rm red}\|^2,0)=R/2,
\]
then the chart gives
\[
\operatorname{rlct}(F,0)
=
\min\left\{\frac{mk}{2},\frac n2+\lambda_{\rm ch}\right\}
=
\frac12\min\{mk,n+R\}.
\]

For \(L=2\), this exactly matches Aoyagi:
\[
\min_t\bigl((m-t)(k-t)+tn\bigr)
=
\min\{mk,n+\min_s((m-1-s)(k-1-s)+sn)\}.
\]
So
\[
nReg=\minAdm(M)-\minAdm(red(M))=\min\{mk-R,n\}.
\]

**Key Point**

There is generally **no exceptional divisor whose raw ratio is \(nReg/2\)**. The actual first-step divisors give either:

\[
D_0:\quad (k_{\rm mon},h)=(1,mk-1),\qquad \frac{h+1}{2k_{\rm mon}}=\frac{mk}{2},
\]

or a pivot/core divisor with ratio

\[
\frac{n+R}{2}=\frac n2+\lambda_{\rm ch}.
\]

The node increment \(nReg/2\) is a **value-side difference**
\[
\operatorname{rlct}(F)-\operatorname{rlct}(F_{\rm child}),
\]
not usually the ratio of a divisor of \(F\) itself.

**Examples**

For \(M=(2,2,5)\):
\[
t=0:4,\quad t=1:1+5=6,\quad t=2:10.
\]
So \(\minAdm(M)=4\), binding \(T=(0)\).  
For \(red=(1,1,5)\):
\[
s=0:1,\quad s=1:5,
\]
so \(R=1\). Hence
\[
nReg=4-1=3,\qquad n=5.
\]
The binding divisor is \(D_0\), with
\[
(k_{\rm mon},h)=(1,3),\qquad (h+1)/2=2.
\]
The child contributes \(1/2\), so the arithmetic increment is \(2-1/2=3/2=nReg/2\). But no divisor has raw ratio \(3/2\); if it did, the RLCT would be at most \(3/2\), contradicting \(\operatorname{rlct}=2\).

For \(M=(2,1,3)\):
\[
t=0:2,\quad t=1:3,
\]
so \(\minAdm=2\), binding \(T=(0)\).  
For \(red=(1,0,3)\), \(R=0\). Thus
\[
nReg=2,\qquad n=3.
\]
Here \(D_0\) has
\[
(k_{\rm mon},h)=(1,1),\qquad (h+1)/2=1=nReg/2,
\]
only because the child RLCT is zero.

For \(M=(1,1,4)\):
\[
t=0:1,\quad t=1:4,
\]
so \(\minAdm=1\), binding \(T=(0)\).  
For \(red=(0,0,4)\), \(R=0\). Thus
\[
nReg=1,\qquad n=4.
\]
Again \(D_0\) gives
\[
(k_{\rm mon},h)=(1,0),\qquad (h+1)/2=1/2=nReg/2.
\]

Contrast \(M=(2,2,2)\):
\[
t=0:4,\quad t=1:1+2=3,\quad t=2:4.
\]
Here binding \(T=(1)\). The child has \(R=1\), so
\[
nReg=3-1=2=n.
\]
This is the regime where the \(n\) Schur \(E\)-squares really are the fresh contribution.

**Where The Extra Squares Go**

They do **not** get absorbed into the child. The split
\[
H\asymp \|E\|^2+\|SB_{\rm red}\|^2
\]
is clean: \(E\) is a genuine smooth \(n\)-block. In the regime \(n>nReg\), those squares are simply non-binding. The \(y_0\)-exceptional divisor reaches its integrability limit before the full \(n/2+\lambda_{\rm ch}\) core threshold matters.

**Correct Resolution Picture**

A full resolution is the nested rank/incidence resolution: after \(t\) Schur pivots, blow up the smooth center
\[
E^{(0)}=\cdots=E^{(t-1)}=0,\qquad S_t=0,
\]
equivalently the proper transform of the incidence stratum
\[
\operatorname{rank}(A)\le t,\qquad AB=0.
\]
Its codimension is
\[
(m-t)(k-t)+tn,
\]
and the corresponding divisor has
\[
(k_{\rm mon},h)=\bigl(1,(m-t)(k-t)+tn-1\bigr),
\]
so its ratio is
\[
\frac{(m-t)(k-t)+tn}{2}.
\]

Thus the sound geometric statement is the rank-stratified minimum, not a per-node divisor of ratio \(nReg/2\). The numerical telescoping identity can still hold, but the local divisor interpretation requested in the question is obstructed; the smallest positive-child witness is already \(M=(2,2,4)\), and your \(M=(2,2,5)\) is the same obstruction.
37,034
The discrepancy is real. The single-pivot Schur computation is correct, but the inference “there are `n` Morse squares, so the node contributes `n/2`” is only valid in the branch where that chart actually computes the RLCT.

**FACT: Single-Pivot Formula**

In Schur coordinates,
\[
F=y_0^2 H,\qquad |Jac|=|y_0|^{mk-1},
\]
and
\[
H=\|E\|^2+\|vE+SB_{\rm red}\|^2\asymp \|E\|^2+\|SB_{\rm red}\|^2.
\]
Thus, if
\[
\lambda_{\rm ch}=\operatorname{rlct}(\|SB_{\rm red}\|^2,0)=R/2,
\]
then the chart gives
\[
\operatorname{rlct}(F,0)
=
\min\left\{\frac{mk}{2},\frac n2+\lambda_{\rm ch}\right\}
=
\frac12\min\{mk,n+R\}.
\]

For \(L=2\), this exactly matches Aoyagi:
\[
\min_t\bigl((m-t)(k-t)+tn\bigr)
=
\min\{mk,n+\min_s((m-1-s)(k-1-s)+sn)\}.
\]
So
\[
nReg=\minAdm(M)-\minAdm(red(M))=\min\{mk-R,n\}.
\]

**Key Point**

There is generally **no exceptional divisor whose raw ratio is \(nReg/2\)**. The actual first-step divisors give either:

\[
D_0:\quad (k_{\rm mon},h)=(1,mk-1),\qquad \frac{h+1}{2k_{\rm mon}}=\frac{mk}{2},
\]

or a pivot/core divisor with ratio

\[
\frac{n+R}{2}=\frac n2+\lambda_{\rm ch}.
\]

The node increment \(nReg/2\) is a **value-side difference**
\[
\operatorname{rlct}(F)-\operatorname{rlct}(F_{\rm child}),
\]
not usually the ratio of a divisor of \(F\) itself.

**Examples**

For \(M=(2,2,5)\):
\[
t=0:4,\quad t=1:1+5=6,\quad t=2:10.
\]
So \(\minAdm(M)=4\), binding \(T=(0)\).  
For \(red=(1,1,5)\):
\[
s=0:1,\quad s=1:5,
\]
so \(R=1\). Hence
\[
nReg=4-1=3,\qquad n=5.
\]
The binding divisor is \(D_0\), with
\[
(k_{\rm mon},h)=(1,3),\qquad (h+1)/2=2.
\]
The child contributes \(1/2\), so the arithmetic increment is \(2-1/2=3/2=nReg/2\). But no divisor has raw ratio \(3/2\); if it did, the RLCT would be at most \(3/2\), contradicting \(\operatorname{rlct}=2\).

For \(M=(2,1,3)\):
\[
t=0:2,\quad t=1:3,
\]
so \(\minAdm=2\), binding \(T=(0)\).  
For \(red=(1,0,3)\), \(R=0\). Thus
\[
nReg=2,\qquad n=3.
\]
Here \(D_0\) has
\[
(k_{\rm mon},h)=(1,1),\qquad (h+1)/2=1=nReg/2,
\]
only because the child RLCT is zero.

For \(M=(1,1,4)\):
\[
t=0:1,\quad t=1:4,
\]
so \(\minAdm=1\), binding \(T=(0)\).  
For \(red=(0,0,4)\), \(R=0\). Thus
\[
nReg=1,\qquad n=4.
\]
Again \(D_0\) gives
\[
(k_{\rm mon},h)=(1,0),\qquad (h+1)/2=1/2=nReg/2.
\]

Contrast \(M=(2,2,2)\):
\[
t=0:4,\quad t=1:1+2=3,\quad t=2:4.
\]
Here binding \(T=(1)\). The child has \(R=1\), so
\[
nReg=3-1=2=n.
\]
This is the regime where the \(n\) Schur \(E\)-squares really are the fresh contribution.

**Where The Extra Squares Go**

They do **not** get absorbed into the child. The split
\[
H\asymp \|E\|^2+\|SB_{\rm red}\|^2
\]
is clean: \(E\) is a genuine smooth \(n\)-block. In the regime \(n>nReg\), those squares are simply non-binding. The \(y_0\)-exceptional divisor reaches its integrability limit before the full \(n/2+\lambda_{\rm ch}\) core threshold matters.

**Correct Resolution Picture**

A full resolution is the nested rank/incidence resolution: after \(t\) Schur pivots, blow up the smooth center
\[
E^{(0)}=\cdots=E^{(t-1)}=0,\qquad S_t=0,
\]
equivalently the proper transform of the incidence stratum
\[
\operatorname{rank}(A)\le t,\qquad AB=0.
\]
Its codimension is
\[
(m-t)(k-t)+tn,
\]
and the corresponding divisor has
\[
(k_{\rm mon},h)=\bigl(1,(m-t)(k-t)+tn-1\bigr),
\]
so its ratio is
\[
\frac{(m-t)(k-t)+tn}{2}.
\]

Thus the sound geometric statement is the rank-stratified minimum, not a per-node divisor of ratio \(nReg/2\). The numerical telescoping identity can still hold, but the local divisor interpretation requested in the question is obstructed; the smallest positive-child witness is already \(M=(2,2,4)\), and your \(M=(2,2,5)\) is the same obstruction.

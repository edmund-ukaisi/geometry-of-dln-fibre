## Q1

**COMPUTED.** Write
\[
A_1=\binom{x_0}{x_1},\qquad A_2=(y_0\ y_1).
\]
Then
\[
\operatorname{coreGen}=y_0x_0+y_1x_1.
\]
It is degree \(1\) and vanishes at zero in the full layer \(\{y_0,y_1\}\), but not in the capped block \(\{y_0\}\). The decisive term is \(y_1x_1\).

## Q2

**FAILS.**

**COMPUTED.** At \(S=0\), choose pivot \(x_0=t\) and write \(x_1=tv\). Then
\[
y_0x_0+y_1x_1=t(y_0+vy_1),
\]
so the strict transform is
\[
r=y_0+vy_1.
\]
For \(d=(1,2,1)\), the descended cap contains only \(y_0=A_2[0,0]\), while the offending term \(vA_2[0,1]\) reads the second column.

**INFERENCE.** A deeper-layer basis change \(y'_0=y_0+vy_1\) could restore capped support, but raw block blow-up and pivot division do not force or track such a change.

## Q3

Yes. \(f=y_1\) satisfies (A) for the full layer but not (B) for the cap \(\{y_0\}\); setting \(y_0=0,y_1=1\) is decisive. Conversely, \(f=y_0^2=y_0\cdot y_0\) satisfies (B) but not (A).
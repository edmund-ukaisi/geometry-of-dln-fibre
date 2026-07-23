### 1. Slot \(i=0\)

**FACT (algebraic lemma):** If \(F=x y Q\) on an open neighborhood meeting the divisor, with \(Q\) continuous and finite-valued, then \(F=0\) on both \(x=0\) and \(y=0\). Equivalently, boundedness of \(F/x\) near \(x=0\) forces \(F(0,y,z)=0\).

Writing
\[
F(x,y,z)=a_0(y,z)+x\,a_1(x,y,z),
\]
vanishing on a relatively open subset of \(x=0\) implies \(a_0\equiv0\), hence \(x\mid F\). Similarly \(y\mid F\). Since \(x\) and \(y\) are distinct prime coordinates,
\[
x\mid F,\quad y\mid F \quad\Longrightarrow\quad xy\mid F.
\]

Indeed, because the asserted equality also holds directly on \(b=0\), continuity is stronger than needed: the finite-valued RHS is automatically zero there.

**COMPUTED FACT:** \(b=u_{000}u_{011}\nmid F_0\).

**INFERENCE:** No continuous functions \(q_{0j}\) can satisfy StepInv on an RLCT neighborhood containing relatively open pieces of the exceptional divisor.

If “includes \(b=0\)” meant only a sparse subset rather than a neighborhood, polynomial divisibility would not follow—but such a set is not an appropriate local RLCT region.

### 2. Continuous versus polynomial coefficients

**FACT:** Polynomial ideal membership
\[
F_i\in\langle b\,\mathrm{resid}_j\rangle_{\mathbb R[u]}
\]
is sufficient: polynomial coefficients are continuous.

**FACT:** It is not necessary in general. After \(b\mid F_i\), the exact continuous condition is
\[
F_i/b\in\langle\mathrm{resid}_j\rangle_{C(V)}.
\]
This continuous ideal can be larger than the polynomial ideal. For example,
\[
b=b(1+x^2)\frac1{1+x^2},
\]
although \(b\notin\langle b(1+x^2)\rangle_{\mathbb R[u]}\).

**INFERENCE:** The coordinate-monomial factor makes \(b\mid F_i\) necessary, but does not make polynomial ideal membership necessary. Here the supplied facts nevertheless decide every slot:

- Slots \(1,3\): polynomial membership gives continuous solutions.
- Slots \(0,2\): failure of divisibility by \(b\) rules out continuous solutions.

### 3. Excluding \(b=0\)

**FACT:** On \(V\subset\{b\ne0\}\), the divisibility obstruction disappears and coefficients may blow up as the omitted divisor is approached. Existence would still depend on the residuals.

**INFERENCE:** Such a restriction changes the assertion and is illegitimate for an RLCT claim concerning behavior along \(b=0\).

### 4. Bottom line

**INFERENCE:** The raw StepInv \(\exists\)(continuous)\(q\) **FAILS** at this node because slots \(0\) and \(2\) are not divisible by \(b\).
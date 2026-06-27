**Q1 Verdict:** Crude lemma (a) gives only `c' < 2`. **NEW LEMMA NEEDED: yes**, unless you already have an equivalent disjoint-sum/additivity theorem.

Using (a) on the `T` block:
\[
\int_T(\|T\|^2+\|\Delta S\|^2)^{-c'}\,dT<\infty
\quad\text{only for }c'<4/2=2.
\]
Then integrating over `(Δ,S)` only multiplies by finite box volume. The core threshold `λ=2` is discarded. So `(a)-(d)` as stated do not reach `c'<4`.

Exact residual lemma, for `n=4`: for any bounded `T`-box and any `c'>2`,
\[
I(w)=\int_T(\|T\|^2+w)^{-c'}\,dT
\le C_{T,c'}\, w^{2-c'}=C_{T,c'}\,w^{-(c'-2)}
\quad(w>0).
\]

Proof: enclose the box in a ball of radius `R`, use radial coordinates:
\[
I(w)\le |S^3|\int_0^R r^3(r^2+w)^{-c'}\,dr.
\]
Set `r=\sqrt w\,t`:
\[
I(w)\le |S^3|w^{2-c'}\int_0^{R/\sqrt w}t^3(1+t^2)^{-c'}\,dt
\le Cw^{2-c'}.
\]
The tail behaves like `t^{3-2c'}`, so it converges exactly when `3-2c'<-1`, i.e. `c'>2`. This is elementary calculus only; **S2-free: yes**.

**Q2 Verdict:** The iterated fibre route gives only `c' < 3/2`; it does not reach `c'<4`.

Peeling `A0` with rows `3` gives the fibre condition
\[
c'<3/2.
\]
The remaining `A1` leaf is a `12`-dimensional Morse block, giving
\[
c'<12/2=6.
\]
Together:
\[
c'<\min(3/2,6)=3/2.
\]

**Q3 Verdict:** With the residual-power lemma, the assembly reaches exactly `c'<4`; the shifted core exponent is `c''=c'-2`, and `c'<4 ⇔ c''<2`.

For `2<c'<4`,
\[
\int_T(\|T\|^2+\|\Delta S\|^2)^{-c'}\,dT
\le C(\|\Delta S\|^2)^{-(c'-2)}.
\]
So the full integral is bounded by
\[
C\int_{\Delta,S}(\|\Delta S\|^2)^{-c''}\,d\Delta\,dS,
\qquad c''=c'-2.
\]
The core threshold is `λ=2`, so this is finite exactly for
\[
c''<2 \iff c'-2<2 \iff c'<4.
\]

The residual-power lemma is needed to add the `T` threshold to the core threshold. It is not needed again inside the already-banked core result: the core binding can come from lemma (c) with `N=3`,
\[
\int |a|^{3-2c''}\,da<\infty
\iff 3-2c''>-1
\iff c''<2.
\]
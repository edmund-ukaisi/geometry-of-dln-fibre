**VERDICT: needs-new-path-invariant.** The case1(1), δ=1 leaf is not provable from the current `hinv + hbranch`.

The proposed `foldB` mechanism is incorrect. Writing \(b=\mathrm{foldB}\), the parent equation after \(B\) is
\[
F(Bu)=b(Bu)\,A(u),
\]
whereas the child requires
\[
F(Bu)=u_p\,b(Bu)\,C(u).
\]
On the dense locus where \(b(Bu)\neq0\), the common factor cancels, so one still needs
\[
A(u)=u_p C(u).
\]
Thus even if \(u_p\mid b(Bu)\), it does not provide the extra child factor. Vanishing at \(u_p=0\) is necessary but not sufficient for a continuous quotient.

Moreover, `foldB` need not contain the reused pivot. In the `(3,3,4)` binding route, \(u_{1,2}\) is born at `(S,J)=(1,1)`, hence δ=0, and before its boost
\[
(b_1,b_2,b_3)=(u_{1,1},\,u_{1,1}u_{1,2},\,u_{1,1}u_{1,2}u_{1,3}).
\]
The scalar dominant factor is \(b_1=u_{1,1}\), not \(u_{1,2}\); see the [trace](</home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/L4wire/expeditions/2026-07-17-aoyagi-engine/threads/elaboration/fold-recursion-template.md:484>).

The correct Aoyagi mechanism is:

- Partial-block residual terms acquire \(u_p\) from the new blow-up.
- Untouched residual terms already carry \(u_p\) in their non-dominant b-chain coefficient \(b_i/b_1\).
- Equivalently, the entire parent residual is degree-one supported on the boost center
  \[
  \{p\}\cup\text{partial block},
  \]
  even though its geometric support is the larger `S_full`.

Hence one needs
\[
r_j(Bu)=u_p\,r_j(qm\,u).
\]
Then `q' = q ∘ B` works by the existing crux in [Case1Wire.lean](</home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/L4wire/lean/DLNFibre/DLN/Aoyagi/Case1Wire.lean:31>).

Your “residual stays” inference is invalid: although \(p\notin S_{\rm full}\), the coefficients \(c_s(u)\) may read \(u_p\). Indeed, in the intended boost they must do so for the untouched part.

The clean carried invariant is:

```lean
def Case11BoostReady ... (p : TreePath d) : Prop :=
  ∀ sc ∈ (conOracle d p.conState).stepChildren,
    sc.ecase = .case11 →
    Deg1SupportedOn (foldResid d e p)
      (canonCenterOf d p.conState sc) (foldRegion d e p)
```

The conjunct-1-only weakest form is the direct identity
```lean
foldResid p j (stepMap ed u)
  = u ed.pivot * foldResid p j (qm u)
```
for every real δ=1 case11 edge.

Current `IsRealBranch` pins the combinatorial child, center, pivot, and a coarse shear-carve condition, but it does not carry this weighted b-chain divisibility. Therefore this must either be added to the carried fold invariant, or `IsRealBranch` must pin sufficiently exact Aoyagi shears and the displayed lemma then be proved inductively from that stronger provenance. This is faithful to Aoyagi; the mis-scoping is collapsing the full diagonal b-chain to scalar `foldB` without retaining boost-readiness.
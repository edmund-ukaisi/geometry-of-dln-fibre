## 1. MISSED GAPS

- **M1 is narrower than paper Definition 1 (source-verified).** `rlctAt` is unweighted and local; no theorem bridges it to a compactly supported density \(\phi\) with \(\phi(w_*)\neq0\), nor is there a generic germ-to-compact-box equivalence. Cheapest check: inspect the definition in `Foundations/Rlct.lean` and search for any RLCT definition parameterized by \(\phi\).

- **M2 is not full ideal invariance (source-verified).** The library handles exact germ equality and bounded unit multiplication; it does not state arbitrary analytic ideal inclusion/equality for finite generator families. Cheapest check: compare the theorem hypotheses in `Foundations/S1Local.lean` directly with Aoyagi Lemma 1.

- **M5 is built as a value reduction, not as full local Theorem 3 (source-verified).** Equality holds at the constructed deepest point and after taking the global infimum; the general-point result appears only as a lower bound. Cheapest check: compare the conclusion of the general-\(v\) theorem with the displayed local equality in the reproduction’s Theorem 3.

- **M10 has the value but likely not Lemma 3’s full tie structure.** The alternative minimization proves the closed form, but the explicit quadratic \(A(b)\) and equality at the adjacent minimizers \(b=a-1,a\)—needed for \(\theta\)—appear absent. Cheapest check: search for the explicit \(A(b)\) formula or both adjacent-minimizer equalities.

I would not flag M6’s far-point leg: source inspection indicates it is wired into the global reduction, subject to `hpos`.

## 2. RANKING CHECK

I would reorder:

1. Finish hbox/resolution.
2. Extend \(\lambda\) to zero reduced widths.
3. Prove combinatorial \(\theta\).
4. Record the theta non-identity/counterexample.
5. Axiom/docstring hygiene.

The primary value theorem on Aoyagi’s full domain outranks the secondary \(\theta\) result.

Items 1 and 2 are each composites. Item 1 includes atlas coverage, pullback monomialization, Jacobian powers, and globalization. Item 2 splits into arithmetic collapse and a new analytic layer-collapse/direct-Morse argument; merely dropping `hpos` fails because the identically-zero core has RLCT \(\top\). Item 3 is more than a pure count: it needs a well-defined \((\ell,a)\) selector and the two-envelope argument.

## 3. THETA BRIDGE

No: the equality is false in general. Test reduced widths
\[
M=(2,2,2,2,2),\qquad r=0.
\]

Aoyagi gives \(\ell=4\), \(a=2\), hence
\[
\theta=2(4-2)+1=5.
\]
The fibre formula gives \(m=4\), \(|\delta|=2\), hence
\[
\mathrm{numTop}=\binom42=6.
\]

Thus the proposed bridge should become a documented non-identity, not an equality theorem.

## 4. BLINDSPOT

The most likely blindspot is conflating three different counts: tied divisor ratios within one chart, Aoyagi’s binding branches, and global top-dimensional fibre components. Pole order is not the global number of minimizing strata; the \(5\)-versus-\(6\) example already separates them.
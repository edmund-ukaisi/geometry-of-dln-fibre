**Q1.** Yes, conditional on your stated definition of `deepestEFull`. If `deepestEFull` genuinely reads the edited last-layer core slot, then pure core conjugation changes the regular term, and `∂deepestEFull/∂core(0)=0` only gives higher-order agreement, not exact germ invariance.

**Q2.** Best construction: a **principled joint shear**: first perform the honest conjugate core shear that realizes the Schur untwisting, then apply a forced gauge/reg correction solving

```text
deepestEFull(core-edited, gauge-corrected, spec) = deepestEFull(original)
```

locally. This is still a joint move, but it should be packaged as “core shear plus canonical fibre correction,” not as a general-L re-derivation of the L=2 `Y1'` algebra. I am inferring here that the relevant gauge coordinate enters `deepestEFull` with an invertible/solvable local linear part.

**Q3.** Faithful reduction, not laundering, if the theorem states `psi`, `psiSplitRaw`, the diffeo triple, split compatibility, and the two germs as explicit hypotheses. That cleanly isolates the already-understood RLCT/diffeomorphism plumbing from the genuinely hard construction of the coupled germ witnesses; it does not pretend the hard part is done.

**Q4.** Run the cheapest test on (A): compute the first nonzero homogeneous term of

```text
deepestEFull(pureCorePsi q) - deepestEFull q
```

or just specialize to a small symbolic nonzero core direction with reg/spec fixed. If that term is nonzero, (A) cannot prove `hsub3reg` by exact germ equality. Also test whether the gauge variable has a locally invertible action on `deepestEFull`; that validates the forced-correction version of (B).
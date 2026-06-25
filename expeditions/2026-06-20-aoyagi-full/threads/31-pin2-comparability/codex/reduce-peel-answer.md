[INFERENCE] Ranking: **D > B > A > C**, where **D** is the clean repair, **B** only works after being turned into D, **A** fails directly, and **C** is generally the wrong abstraction.

[GENERAL-FACT] The right move is to reduce by `α.symm = coreAbsorb.symm`, but keep the changed reg map instead of pretending it is unchanged: define  
`\tildeπ q := (deepestEFull (α.symm q), q.2)`.

[GENERAL-FACT] With `F0 q := ∑ q.1² + coreF q.2.1`, the exact identities are  
`LHS_integrand ∘ α.symm = F0 ∘ \tildeπ` and `RHS_integrand ∘ α.symm = F0`.

[INFERENCE] So the proof is: use RLCT invariance under `α.symm`, then apply the local-diffeomorphism peel to `\tildeπ` on the decoupled integrand `F0`.

[INFERENCE] This should be cheap because `D\tildeπ(0)` has the same decisive block as before: since `D(deepestEFull)(0)` has core block `0`, composing with the core shear `α.symm` does not change the reg-reg block `F`.

[GENERAL-FACT] Option **A** fails unless `(coreAbsorb (regStraighten q)).2.1 = (coreAbsorb q).2.1`, which is false if the core shear reads the reg slot and `regStraighten` changes it.

[GENERAL-FACT] Option **B** with the original `regStraighten` gives the wrong term, namely an `E (α q)` or `E (α.symm q)` variant, so it only closes after replacing the peeled map by the conjugated/coordinate-changed one above.

[GENERAL-FACT] Option **C** is a soundness trap: stripping `coreAbsorb` from the core term forces a core-coordinate change, and a core-dependent `E` will see that change unless you prove a special invariance.

[INFERENCE] `regAbsorb_rlct` is still true as stated with `deepestEFull`, provided `\tildeπ` is proved to be a local diffeomorphism at `0`.

[INFERENCE] I would not restate the structure field; I would repair the proof architecture by peeling in `coreAbsorb`-coordinates.

BIGGEST RISK: you must confirm the derivative/local-diffeomorphism proof for `q ↦ (deepestEFull (coreAbsorb.symm q), q.2)`, especially that the core block of `D deepestEFull(0)` is really zero and that `coreAbsorb.symm` has the expected smooth shear derivative.
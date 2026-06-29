**1. Verdict**

**SOUND-WITH-CAVEAT.** The chain is sound if `P0'`, `Q1'`, `Score'`, `Sreg'`, `deepestEFull`, and `regStraighten` are all re-keyed to the same triangular frame family. Then the producer `Score` is irrelevant. The caveat is that `Q1'` needs the last-layer leading/pivot block `Ã11` invertible in the same column split used by `Score'`/PIN1; tail-rows-zero alone does not imply this.

**2. Step (ii): Seven Frame Facts**

1. **`hPunit`**: yes.  
   One-line identity: `P0' = [[A11⁻¹,0],[-A21A11⁻¹,I]]` is block-lower with invertible diagonal blocks; `P1 = I`.

2. **`hQunit`**: yes, with caveat.  
   One-line identity if `[Invertible Ã11]`: `Q1' = [[Ã11⁻¹,-Ã11⁻¹Ã12],[0,I]]` is block-upper with invertible diagonal blocks; `Q0 = I`.  
   **Assumption:** `Ã11` invertible in the chosen pivot/front split.

3. **Boundary `Qf0 = I`**: yes.  
   One-line identity: layer-0 right frame remains `Q0 = I`; `P0'` is the left frame, so no L/R clash.

4. **Boundary `Pf1 = I`**: yes.  
   One-line identity: layer-1 left frame remains `P1 = I`; `Q1'` is the right frame.

5. **`hNF` for non-last layer**: yes.  
   One-line identity:
   `P0' · [[A11,0],[A21,0]] · I = [[I,0],[0,0]]`.

6. **Last-layer `hcorner` / last normal form**: yes, with same caveat.  
   One-line identity:
   `[[Ã11,Ã12],[0,0]] · Q1' = [[I,0],[0,0]]`.  
   **Assumption:** this is stated in the same column split/pivot `J` used downstream. If `Q1'` is built in a different split, this breaks.

7. **`hinterface`**: satisfied.  
   Important correction: in the current Lean-shaped telescope, for `L = 2` this is not vacuous; it is exactly `Q0 = I ∧ P1 = I` at the single interface `s = 0`.

Extra PIN1 fact: **`hQf22`** also survives.  
One-line identity: in the same split, `(reindex Q1').toBlocks₂₂ = I`, hence unit.

**3. Step (iv)**

The gauge-invariance appeal is a red herring if you really work entirely in the triangular frame. From

`rlctAt(loss) = rlctAtOn(Sreg' + Score')`

and then

`rlctAtOn(Sreg' + Score') = rlctAtOn(Sreg' + coreΦ)`

you never mention the producer `Score`. No cross-frame `Score` equality and no cross-frame RLCT-invariance lemma is needed. Carrying step (iv) makes the proof look weaker than it is.

**4. Biggest Risk**

The biggest risk is not gauge invariance. It is the unspoken requirement that the triangular frame family be threaded everywhere: `Score'`, `Sreg'`, `deepestEFull`, `regStraighten`, `hregval`, PIN1’s derivative input, and the diffeo bridge must all use the same `P0'`,`Q1'`.

The concrete algebraic risk is `Ã11` invertibility for the last layer in the same pivot/front split. Tail rows zero plus rank `r` is not enough.

**5. If This Fails**

Minimal fix: prove the dual leading/pivot block fact for layer 1, or choose the pivot split `J` so `Ã11` is invertible, then define `Q1'` in that exact split. Once that is in place, drop step (iv) entirely and instantiate the whole squeeze/bridge with the triangular frames.
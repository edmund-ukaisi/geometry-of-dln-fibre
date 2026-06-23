# Decorrelated fidelity check: determinantal-stratum dimension at N=1

I am REVIEWING a Lean formalisation. Do NOT write Lean. Just adjudicate the MATH.

## The informal claim being formalised
The variety of m×n matrices of rank ≤ r has dimension r·(n + m − r).
(Encoding: d_0 = n columns, d_N = d_1 = m rows; witness 2×2, r=1 → 3.)

## The formalisation route (please check each step for mathematical correctness)
A type-A quiver with a single arrow (N=1), dimension vector d = (d_0, d_1) = (n, m).
A representation is a single matrix M : m×n. The product map "mult" is just M.
The closed rank-≤r locus Σ̄^r = {M | rank M ≤ r}.

The dimension is computed as: dim = (ambient) − (codim) = m·n − C, where C is a
combinatorial "C-codimension" defined as the MINIMUM over "Kostant partitions of d
with corner r" of a quadratic form codimForm.

### Definitions used
- A Kostant partition of d=(n,m) with corner r is a function m_{ab}, a,b ∈ {0,1},
  supported on a≤b, with: for each vertex k, d_k = Σ_{a≤k≤b} m_{ab}, and corner m_{0,1} = r.
- codimForm at N=1 (the full nested sum ∑_{1≤i≤u≤j≤v≤N} m_{(i-1)(j-1)} · m_{uv})
  collapses, at N=1, to the SINGLE term m_{00} · m_{11}.

## QUESTIONS (adjudicate each, give exact numbers)
1. At N=1, d=(n,m), corner r (with r≤n, r≤m): is the Kostant-partition set the SINGLE
   partition m_{00}=n−r, m_{01}=r, m_{11}=m−r, m_{10}=0? Show the vertex equations force this.
   Are there any OTHER solutions (e.g. is m_{10} forced to 0, is uniqueness genuine)?
2. Does codimForm collapse to m_{00}·m_{11} = (n−r)(m−r) at N=1? Check the index ranges
   [1,N]×[i,N]×[u,N]×[j,N] at N=1 give exactly one quadruple (i,u,j,v)=(1,1,1,1), and that
   the indices into the array are (i−1,j−1)=(0,0) and (u,v)=(1,1).
3. Is m·n − (n−r)(m−r) = r(n+m−r)? Verify algebraically.
4. Is r·(n+m−r) the correct dimension of the rank-≤r m×n matrix variety? Cross-check against
   the standard formula dim = r(m+n−r) for the determinantal variety, and the witness 2×2 r=1 → 3.
5. Is the index correspondence right: with d_0=n (columns/source) and d_1=m (rows/target), the
   matrix is m×n, ambient dimension m·n. Is the codimension of the rank-≤r locus (n−r)(m−r)?
   Cross-check: the codimension of rank-≤r in m×n matrices is (m−r)(n−r). Does that match?

Be terse and exact. Flag any step that is wrong or where the encoding could be off-by-one or transposed.

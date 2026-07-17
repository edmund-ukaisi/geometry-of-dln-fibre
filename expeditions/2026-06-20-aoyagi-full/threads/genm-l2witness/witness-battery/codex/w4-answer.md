Using exact integer DP, with cuts written as \((t_1,t_2)\), I obtained:

### Q1. All optimal peel paths

| \(n\) | Cuts \((t_1,t_2)\) | Indices \((d_1,d_2)=(n-t_1,t_1-t_2)\) |
|---:|---:|---:|
| 3 | \((2,1)\) | \((1,1)\) |
| 4 | \((2,1)\) | \((2,1)\) |
| 4 | \((3,1)\) | \((1,2)\) |
| 4 | \((3,2)\) | \((1,1)\) |
| 5 | \((3,1)\) | \((2,2)\) |
| 5 | \((3,2)\) | \((2,1)\) |
| 5 | \((4,2)\) | \((1,2)\) |
| 6 | \((4,2)\) | \((2,2)\) |
| 7 | \((4,2)\) | \((3,2)\) |
| 7 | \((5,2)\) | \((2,3)\) |
| 7 | \((5,3)\) | \((2,2)\) |

There are no other optimal paths.

### Exact DP audit

For the length-three node \((a,n,n)\), the value at second cut \(s\) is

\[
(a-s)(n-s)+sn=an+s(s-a).
\]

Thus its argmins are \(s=a/2\) when \(a\) is even, and \(s=(a\pm1)/2\) when \(a\) is odd.

The root value at first cut \(a\) is therefore

\[
F_n(a)=(n-a)^2+an-\left\lfloor\frac{a^2}{4}\right\rfloor.
\]

The exact root rows, indexed by \(a=0,\ldots,n\), are:

| \(n\) | \(F_n(0),\ldots,F_n(n)\) | Root argmins | \(\minAdm(n,n,n,n)\) |
|---:|---|---|---:|
| 3 | \(9,7,6,7\) | \(2\) | 6 |
| 4 | \(16,13,11,11,12\) | \(2,3\) | 11 |
| 5 | \(25,21,18,17,17,19\) | \(3,4\) | 17 |
| 6 | \(36,31,27,25,24,25,27\) | \(4\) | 24 |
| 7 | \(49,43,38,35,33,33,34,37\) | \(4,5\) | 33 |

The child-node rows used by these argmins are:

| Node | Values over all second cuts | Argmins |
|---|---|---|
| \((2,3,3)\) | \(6,5,6\) | \(1\) |
| \((2,4,4)\) | \(8,7,8\) | \(1\) |
| \((3,4,4)\) | \(12,10,10,12\) | \(1,2\) |
| \((3,5,5)\) | \(15,13,13,15\) | \(1,2\) |
| \((4,5,5)\) | \(20,17,16,17,20\) | \(2\) |
| \((4,6,6)\) | \(24,21,20,21,24\) | \(2\) |
| \((4,7,7)\) | \(28,25,24,25,28\) | \(2\) |
| \((5,7,7)\) | \(35,31,29,29,31,35\) | \(2,3\) |

### Q2. \(B(n)\)

| \(n\) | \(B(n)\) |
|---:|---:|
| 3 | 1 |
| 4 | 1 |
| 5 | 2 |
| 6 | 2 |
| 7 | 2 |

### Q3. Threshold

The smallest nonnegative \(n\) for which every optimal path has  
\(\max(d_1,d_2)\ge2\) is

\[
\boxed{n=5}.
\]

Optimal witnesses below the threshold, all having indices at most \(1\), are:

| \(n\) | Cuts | Indices |
|---:|---:|---:|
| 0 | \((0,0)\) | \((0,0)\) |
| 1 | \((1,1)\) | \((0,0)\) |
| 2 | \((1,0)\) | \((1,1)\) |
| 3 | \((2,1)\) | \((1,1)\) |
| 4 | \((3,2)\) | \((1,1)\) |

### Q4. Strictness

**Yes.** Every non-argmin cut at every root for \(n=4,\ldots,7\) has a strictly larger value, as the root rows show.

For every possible child node \((a,n,n)\), not merely those on optimal paths, the gap from the minimum is

\[
\begin{cases}
(s-a/2)^2, & a\ \text{even},\\
(s-k)(s-k-1), & a=2k+1.
\end{cases}
\]

It vanishes exactly at the listed argmins and is strictly positive at every non-optimal integer cut.

- Nothing.
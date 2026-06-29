"""CONSOLIDATED multi-M summary of the per-piece factorization adjudication.
Runs all validated M and prints the certificate table."""
import subprocess, sys
cases = [
    ("run_3333.py",  "(3,3,3,3) L=3 anchor [t=2 interior, descent]"),
    ("run_232.py",   "(2,3,2)   L=2 corrected [12 coords, was 13]"),
    ("run_2222.py",  "(2,2,2,2) L=3 [t=1 cores]"),
    ("run_333.py",   "(3,3,3)   L=2 [t=3 K-core, regular]"),
    ("run_32222.py", "(3,2,2,2,2) L=4 DESCENT + t=2 interiors"),
]
print("="*78)
print("PER-PIECE FACTORIZATION  DFrame_M = F_radial * prod_s F_s   — MULTI-M CERTIFICATE")
print("="*78)
for f, label in cases:
    out = subprocess.run([sys.executable, f], capture_output=True, text=True, cwd="/tmp/radsep").stdout
    # extract the 3 checks + det
    lines = out.splitlines()
    print(f"\n### {label}")
    for ln in lines:
        s = ln.strip()
        if s.startswith("(i)") or s.startswith("(ii)") or s.startswith("(iii)") or s.startswith("global det") or s.startswith("u-power") or "square=" in s:
            print("   ", s)

"""Numerical check of the two-Tower reading on the first zeros (all ON the line).

For zero number m (1-based), n = m-1 = nZeroSourceIndex, occurrence = p_n
(p_0 = 2).  Tower: log C_k = (phi + k*pi)/T, phi = atan(T/beta), beta = 1/2.
Produced prime of the cell at address k: last prime <= C_{k+1}.

Q1 (raccord exact): does SOME address k give produced = p_n, i.e. an incidence
    C_{k+1} in [p_n, p_{n+1}) ?
Q2 (cell width vs prime gap): pi/T versus log(p_{n+1}/p_n).
"""
import math
from mpmath import mp, zetazero
from sympy import prime, nextprime

mp.dps = 20
M = int(__import__("sys").argv[1]) if len(__import__("sys").argv) > 1 else 120
rows = []
ok = 0
for m in range(1, M + 1):
    T = float(zetazero(m).imag)
    n = m - 1
    pn = int(prime(n + 1))
    pn1 = int(nextprime(pn))
    beta = 0.5
    phi = math.atan(T / beta)
    width = math.pi / T
    gap = math.log(pn1 / pn)
    # is there an integer j with (phi + j*pi)/T in [log pn, log pn1)?
    lo = (T * math.log(pn) - phi) / math.pi
    hi = (T * math.log(pn1) - phi) / math.pi
    exists = math.ceil(lo) < hi  # some integer j in [lo, hi)
    ok += exists
    rows.append((m, round(T, 3), pn, pn1, round(width, 5), round(gap, 5), exists))

print("m  T  p_n  p_{n+1}  cell(pi/T)  gap(log)  exact_raccord_possible")
for r in rows:
    if r[0] <= 30 or r[0] % 10 == 0:
        print(*r)
print(f"\nzeros with SOME cell producing exactly p_n: {ok}/{M}")
print("cell wider than gap for m >=",
      next((r[0] for r in rows if r[4] > r[5]), None),
      "; fraction of zeros with cell > gap:",
      sum(1 for r in rows if r[4] > r[5]) / M)

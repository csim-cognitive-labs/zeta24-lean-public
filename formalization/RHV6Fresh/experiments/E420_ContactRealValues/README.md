# E420 — Real values at the contacts, alternation, tangential inversion, evolution of the amplitudes (pre-registered 2026-11-03)

> Français : [README.fr.md](README.fr.md)

Objective (author): measure the real value of each Tower at each of its contacts (sign and amplitude), the alternation of
values between consecutive contacts, the recovery of the height T and the radial position β by tangential inversion of the
contacts, and the evolution of the amplitudes as the Tower winds. **No primes, no gaps, no whole cells, no logarithmic
integral**: only the heights of the zeros (Odlyzko data, placed on the line) and separate synthetic Towers
(never at the height of a real zero) are used.

Predictions to test (identities of the Lean module `Terminal/ContactRealValue.lean`, written before execution):
* value at contact k: v_k = (−1)^k · C_k^β / √(β²+T²), imaginary part zero;
* alternation: v_{k+1} = −e^{βπ/T} · v_k (opposite sign, modulus multiplied by e^{βπ/T});
* inversion: T = π/(log C_{k+1} − log C_k); β = T·log|v_{k+1}/v_k|/π; β = T / tan(T·log C_k − kπ) (tangent);
* winding: log|v_k| is affine in k, slope βπ/T; doubling of the modulus after T·log 2/(βπ) contacts.
Deterministic twin: mpmath at 30 digits on 5 contacts per Tower. Nothing here presumes that these identities exclude OFF zeros.

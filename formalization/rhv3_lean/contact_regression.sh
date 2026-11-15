#!/usr/bin/env bash
# Régression expérimentale Z1--Z4 des contacts publiés. Les adresses entières
# ci-dessous sont des données historiques de diagnostic ; elles ne font partie
# d'aucune API ni d'aucun producteur scientifique RHV3.
set -euo pipefail
cd "$(dirname "$0")"

python3 - <<'PY'
import mpmath as mp

mp.mp.dps = 70
rows = (
    ("Z1", "14.1347251417346937904572519835624702707842571156992431756856", 4,
     "2.711958785357", "3.386956682246"),
    ("Z2", "21.0220396387715549926284795938969027773343405249027817546295", 10,
     "4.797132274455", "5.570367919385"),
    ("Z3", "25.0108575801456887632137909925628218186595496725579966724965", 14,
     "6.175152195952", "7.001627926974"),
    ("Z4", "30.4248761258595132103118975305840913201815600237154401809621", 22,
     "10.203703046819", "11.313628568043"),
)

ok = True
for name, height_text, diagnostic_incidence, expected_minus, expected_plus in rows:
    height = mp.mpf(height_text)
    phase = mp.atan(height / mp.mpf("0.5"))
    contact_minus = mp.exp((phase + diagnostic_incidence * mp.pi) / height)
    contact_plus = mp.exp((phase + (diagnostic_incidence + 1) * mp.pi) / height)
    actual_minus = f"{float(contact_minus):.12f}"
    actual_plus = f"{float(contact_plus):.12f}"
    row_ok = actual_minus == expected_minus and actual_plus == expected_plus
    ok = ok and row_ok
    print(f"CONTACT_REGRESSION_{name}={'PASS' if row_ok else 'FAIL'} "
          f"minus={actual_minus} plus={actual_plus}")

print(f"CONTACT_REGRESSION_Z1_Z4={'PASS' if ok else 'FAIL'}")
raise SystemExit(0 if ok else 2)
PY

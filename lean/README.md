# Lean 4 formal verification

All six results of the paper (Theorem 3, Corollary 4, Propositions 5, 7, 8 and the min-max counting inequality) are machine-checked in Lean 4 / Mathlib. Toolchain: leanprover/lean4:v4.35.0-rc3.

| File | Theorems | Build and axiom audit |
|---|---|---|
| `TwBoyut_v1.lean` | `TW.boyut, TW.tasarim, TW.sessizlik` | passed |
| `TwKeskinlik_v1.lean` | `TW.K_eq, TW.ozvektor, TW.H_disinda, TW.B_rayleigh_pozitif` | passed |
| `TwCekirdekDisi_v1.lean` | `TW.cekirdek_disi` | passed |
| `TwMinMaks_v2.lean` | `TW.sayim, TW.minmaks` | passed |

Axiom audit: only propext, Classical.choice and Quot.sound; no sorry. Each main file has a deliberately false counterpart in `kontrol/`; all four are rejected by the compiler. Logs of the audited run are in `denetim/`.

Check: `lake env lean <file>` inside this folder.

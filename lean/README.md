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

## v2.1 additions: statement-fidelity audit (2026-10-28)

Each statement of the paper was matched line by line against its Lean theorem. Two parts are added; all v1 theorems are kept verbatim in the v2 files.

* `TwBoyut_v2.lean`: `TW.esitlik` gives the equality clause of Theorem 3 for every d >= N+1 (dim W = d-(N+1) <=> rank L = N+1, i.e. the N+1 conditions are independent); `TW.esitlik_kucuk` covers d <= N+1, where the lower bound is 0 and equality means rank L = d (L injective). Negative control `kontrol/TwBoyutYanlis_v2.lean`: the equivalence without the hypothesis d >= N+1 is rejected (d = 1, N = 5).
* `TwKeskinlik_v2.lean`: `TW.C_psd` (C >= 0, so the example satisfies the hypotheses of Proposition 7), `TW.rayleigh` ((3-sqrt 5)/2 <x,x> <= <x,Kx> for all x) and `TW.en_kucuk` (every eigenvalue of K is >= (3-sqrt 5)/2), so the eigenvector of Proposition 8 belongs to the smallest eigenvalue. Negative controls `kontrol/TwKeskinlikYanlis_v2a.lean` (bound raised by 1/100) and `kontrol/TwKeskinlikYanlis_v2b.lean` (indefinite matrix) are rejected.

Axiom audit of the v2 files: only propext, Classical.choice and Quot.sound; logs in `denetim/`.

## v2.2-v2.4 additions: rank link, minor criterion, disconjugacy, pole deflation (2026-10-29 to 2026-10-30)

| File | Theorems | Version |
|---|---|---|
| `TwRank_v1_2.lean` | `TW.rank_of_gram_posDef`, `TW.dimW_eq_of_gram_posDef`: a positive definite Gram matrix L L^T gives full row rank, hence dim W = d - n | v2.2.0 |
| `kontrol/TwRankKarsiOrnek_v1.lean` | `TWKontrol.posSemidef_yetmez`: sharpness of the hypothesis, positive semidefiniteness does not suffice (counterexample L = 0), proved without `sorry` | v2.2.0 |
| `TwRankMinor_v1_3.lean` | `TWMinor.rank_of_submatrix_det_ne_zero`, `TWMinor.dimW_eq_of_submatrix_det_ne_zero`: a single nonvanishing maximal minor gives full row rank; `TWMinorKontrol.det_ne_zero_gerekli`: sharpness of the hypothesis | v2.3.0 |
| `TwDisconj_v2_3.lean` | `TWDisconj.deriv_pos_of_pos_on`, `TWDisconj.pos_of_deriv_pos_bootstrap`, `TWDisconj.pos_of_integral_eq`: the positivity (disconjugacy) argument behind the pole-tameness lemma | v2.3.0 |
| `TwHaynsworth_v2_1.lean` | `TWHayn.B_symm`, `TWHayn.Q_lin_comb`, `TWHayn.neg_plane_of_two_dirs`, `TWHayn.no_second_neg_dir`: algebraic core of pole deflation; the inertia-index hypothesis is carried explicitly | v2.4.0 |

Axiom audit of these files: only propext, Classical.choice and Quot.sound; logs `denetim/TwRank_v1_2_denetim.log`, `denetim/TwRankKarsiOrnek_v1_denetim.log`, `denetim/TwRankMinor_v1_3_denetim.log`, `denetim/TwDisconj_v2_3_denetim.log`, `denetim/TwHaynsworth_v2_1_denetim.log`. `TwFormal.lean` is the library root of the Lake project.

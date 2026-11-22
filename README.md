# tw-silent-subspace

Reproduction code and Lean 4 formal verification for M. A. Oltulu, "The dimension of silent subspaces in finite-sampling truncations of the Weil quadratic form", Zenodo, concept DOI [10.5281/zenodo.22730006](https://doi.org/10.5281/zenodo.22730006) (version 4: [10.5281/zenodo.23778611](https://doi.org/10.5281/zenodo.23778611)).

This software record: concept DOI [10.5281/zenodo.23724476](https://doi.org/10.5281/zenodo.23724476), which resolves to the latest version.

Turkish version: [README.tr.md](README.tr.md).

## Versions

| Version | Tag date | DOI | Content |
|---|---|---|---|
| v2.0.0 | 2026-10-28 | [10.5281/zenodo.23724477](https://doi.org/10.5281/zenodo.23724477) | All six results of the paper machine-checked in Lean 4 / Mathlib; live reproduction of Section 5 |
| v2.1.0 | 2026-10-28 | [10.5281/zenodo.23725248](https://doi.org/10.5281/zenodo.23725248) | Statement-fidelity audit: equality clause of Theorem 3, minimality in Proposition 8 |
| v2.2.0 | 2026-10-29 | [10.5281/zenodo.23777007](https://doi.org/10.5281/zenodo.23777007) | Equality certificate for Theorem 3: interval LDL in both cells; Lean rank link and counterexample |
| v2.3.0 | 2026-10-30 | [10.5281/zenodo.24291599](https://doi.org/10.5281/zenodo.24291599) | Pole-tameness lemma, formally verified; Chebyshev reduction of the sampling matrix |
| v2.4.0 | 2026-10-30 | [10.5281/zenodo.24291617](https://doi.org/10.5281/zenodo.24291617) | Pole deflation: the single negative direction of the pole-free form is consumed by the pole condition |
| v2.5.0 | 2026-11-03 | [10.5281/zenodo.24291670](https://doi.org/10.5281/zenodo.24291670) | Blind-zone margin: the `delta*` reading at a fixed test vector |
| v2.5.1 | 2026-11-17 | [10.5281/zenodo.24293123](https://doi.org/10.5281/zenodo.24293123) | Documentation of v2.2.0-v2.5.0; Turkish version of the documentation |
| v2.5.2 | 2026-11-22 | this release | Correction: the `sigma_min(L)` lower bound printed by `tw_sigma_sert_v1.py` (v2.2.0) is invalid, since LDL pivots bound `lambda_min(G)` from above; `tw_sigma_sert_v2.py` certifies a valid bound by interval LDL on `G - D^2 I`. Rank and `dim W = 2` are unaffected |

## Reproduction tools

Single Python files on `mpmath`; `haynsworth_v1.py` also imports the engine noted below. Test cells (q = 13): A with Omega = 75.5524, N = 18, d = 21; B with Omega = 103.7255, N = 30, d = 33.

| File | What it computes | Run logs |
|---|---|---|
| `tw_reproduce.py` | Section 5: rank L and dim W = d - rank L in both cells; gates G1-G5, negative controls `--dup-zero` and `--inject-odd`, boundary reading `--basis firstd` | `run_AB_canli.log`, `run_AB_canli.json`, `run_neg__dup_zero.log`, `run_neg__inject_odd.log` |
| `tw_sigma_sert_v1.py` | Equality certificate for Theorem 3: interval LDL on G = L L^T with a positive lower bound for every pivot; negative control with a duplicated ordinate. Kept for the record (v2.2.0); the `sigma_min(L)` bound it prints is invalid, see v2.5.2 | `run_sertifika_canli.log` |
| `tw_sigma_sert_v2.py` | Equality certificate, corrected: the same positivity of G = L L^T (hence rank L = N+1), and `sigma_min(L) > D` certified by interval LDL on G - D^2 I; self-test on L = [[1,1],[0,1]], reproduction of the v1 pivots, a shift above the SVD value that must fail, consistency with the SVD | `run_sertifika_v2_canli.log` |
| `cheb_indirge_v1.py` | Reduction of the sampling matrix: L[j,i] = h mu_{2i} psi_{2i}(s_j), hence rank L = rank Psi | `run_cheb_indirge.log` |
| `cheb_isaret_v1.py` | Chebyshev (Haar) property of phi_i(w) = psi_{2i}(sqrt w): sign of det[phi_i(w_j)] over random point sets, at two Legendre cutoffs and two precisions; negative control with a repeated point | `run_cheb_isaret_A.log`, `run_cheb_isaret_B.log` |
| `cheb_osilasyon_v1.py` | Markov criterion: phi_i has exactly i zeros on (0,1), consecutive zero sets interlace, no zeros on (-eps, 0]; negative control with a perturbed family | `run_cheb_osilasyon_A.log`, `run_cheb_osilasyon_B.log` |
| `psi_sanal_v1.py` | Pole side: psi_{2i}(iy) along the imaginary axis keeps its sign and grows monotonically; negative control with a planted imaginary zero | `run_psi_sanal_A.log`, `run_psi_sanal_B.log` |
| `haynsworth_v1.py` | Haynsworth inertia criterion on the pole-free geometric form: kappa = 1, s = <w, G^-1 w> = -exp(L/2)/2 < 0, kappa = 0 on the orthogonal complement of the pole vector; negative control with a random vector | `run_haynsworth.log`, `run_haynsworth_cok.log` |
| `kor_bolge_v2.py` | Validity gate for `delta*` exclusion bounds: blind-zone depth d_0 from kappa(d, L) = 2 sinh(dL)/d - 2L (Eberwein, Theorem 7.1, Zenodo record 23177438), with mu measured for each test vector | `run_kor_bolge_v2.log` |
| `tavan_v1_2.py` | `delta*`, d_0 and the margin `delta*`/d_0 at fixed test vectors | `run_tavan_v1_2.log` |

Further log: `run_cheb_B_K120.log` (cell B at Legendre cutoff K = 120).

`haynsworth_v1.py` imports the Weil-form engine `kapi6b_fast_v19.py`, where the conventions (archimedean sign, prime normalisation, Legendre basis, pole vectors) are fixed; the engine is outside this repository, and the outputs of both runs are recorded in the logs listed above.

Example runs:

    python -u tw_reproduce.py
    python -u tw_sigma_sert_v1.py --ivdps 80,140
    python -u tw_sigma_sert_v2.py
    python -u cheb_indirge_v1.py
    python -u cheb_isaret_v1.py --cell B --kume 300
    python -u cheb_osilasyon_v1.py --cell B --K 120
    python -u psi_sanal_v1.py --cell B --K 120
    python -u haynsworth_v1.py --d 21 --cc 0.5 --dlist 13,17,21,25
    python -u kor_bolge_v2.py
    python -u tavan_v1_2.py

## Lean 4 formal verification

All six results of the paper are machine-checked in Lean 4 / Mathlib, axiom audit clean, with negative controls. Versions 2.2.0-2.4.0 add the rank link, the minor criterion, the disconjugacy argument and the algebraic core of pole deflation. See [lean/README.md](lean/README.md).

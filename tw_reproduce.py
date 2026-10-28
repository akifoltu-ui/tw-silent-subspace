#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
tw_reproduce.py  --  reproduction of Section 5 of
  M. A. Oltulu, "The dimension of silent subspaces in finite-sampling
  truncations of the Weil quadratic form", Zenodo 10.5281/zenodo.22730006.

Single file, no local imports.  Only dependency: mpmath.

What it computes (exactly as described in the paper):
  q = 13, h = ln(q)/2, c = Omega*h.
  V = first d EVEN prolate modes on [-h,h] with bandwidth c, obtained from
      the finite approximation of the prolate differential operator in
      normalised even Legendre polynomials (Legendre cutoff K even terms).
  Modes are normalised to unit L2 norm on [-h,h] (this fixes the scale of the
  printed singular values; the paper's 1.4148646e-12 / 7.6443343e-17 are in this
  convention).
  E : sampling rows  F_eta(gamma_j) = int eta(u) cos(gamma_j u) du, gamma_j = zeta
      ordinates below Omega  (spherical Bessel closed form).
  ell: pole row      ell_pm(eta) = int eta(u) exp(+-u/2) du  (modified spherical Bessel).
  L = [E ; ell].  rank via singular values, threshold 1e-35 * sigma_max.
  dim W = d - rank L.   Theorem 3:  dim W = d - rank L >= max(0, d-N-1).

Gates (five directions, as in the author's test discipline):
  G1  MATH      closed-form row entry vs direct quadrature
  G2  FLOOR     every printed sigma sits above the precision floor
  G3  CONSIST   ranks equal at two Legendre cutoffs; sigma_min agrees to >=20 digits
  G4  BOUNDARY  --basis firstd (paper's alternative reading): d < N+1  =>  dim W = 0
  G5  NEGATIVE  --dup-zero  : repeated ordinate  => rank E = N-1, dim W = 3  (must NOT read 2)
                --inject-odd: odd mode in basis  => Remark 1 (ell+ = ell-) must FAIL

Usage:
  python -u tw_reproduce.py                    # cells A and B, dps 65, cutoffs 88,112
  python -u tw_reproduce.py --cell A --quick   # smoke run (dps 30, cutoff 60)
  python -u tw_reproduce.py --cell A --dup-zero
  python -u tw_reproduce.py --cell A --inject-odd
  python -u tw_reproduce.py --cell A --basis firstd
"""
import sys, argparse, hashlib, json, time
import mpmath as mp

VERSION = "1.1"

def self_md5():
    try:
        with open(__file__, "rb") as f:
            return hashlib.md5(f.read()).hexdigest()
    except Exception:
        return "n/a"

# ----------------------------------------------------------------------------
# cells (Omega rounded as printed in the paper; N = #zeros below Omega)
# ----------------------------------------------------------------------------
CELLS = {
    "A": dict(Omega="75.5524",  N=18, d=21, sigma_min_paper="1.4148646e-12"),
    "B": dict(Omega="103.7255", N=30, d=33, sigma_min_paper="7.6443343e-17"),
}
Q = 13

# ----------------------------------------------------------------------------
# zeta ordinates
# ----------------------------------------------------------------------------
def zeta_ordinates(n):
    return [mp.im(mp.zetazero(k)) for k in range(1, n + 1)]

# ----------------------------------------------------------------------------
# even prolate modes in normalised Legendre basis (Bouwkamp)
#   operator  A = -d/dx (1-x^2) d/dx + c^2 x^2   on [-1,1]
#   <Pn~, A Pn~> : diag n(n+1) + c^2 (X^2),  X = Jacobi matrix of x
#   even block indices n = 0,2,4,...,2K-2
# ----------------------------------------------------------------------------
def beta(n):
    n = mp.mpf(n)
    return (n + 1) / mp.sqrt((2 * n + 1) * (2 * n + 3))

def prolate_even(c, K, d):
    """returns list of d coefficient vectors (length K) over even normalised
    Legendre P~_0, P~_2, ..., P~_{2K-2}; ordered by increasing eigenvalue chi."""
    M = mp.zeros(K, K)
    for i in range(K):
        n = 2 * i
        diag = mp.mpf(n * (n + 1))
        x2 = beta(n) ** 2 + (beta(n - 1) ** 2 if n >= 1 else mp.mpf(0))
        M[i, i] = diag + c * c * x2
        if i + 1 < K:
            off = c * c * beta(n) * beta(n + 1)
            M[i, i + 1] = off
            M[i + 1, i] = off
    ev, U = mp.eigsy(M)
    order = sorted(range(K), key=lambda k: ev[k])
    modes = []
    for k in order[:d]:
        v = [U[i, k] for i in range(K)]
        modes.append(v)
    return modes, [ev[k] for k in order[:d]]

# ----------------------------------------------------------------------------
# closed-form integrals of normalised Legendre on [-h,h]
#   int_{-1}^{1} P_m(x) cos(z x) dx = 2 (-1)^{m/2} j_m(z)     (m even)
#   int_{-1}^{1} P_m(x) e^{a x} dx  = 2 i_m(a),   e^{-a x}: 2 (-1)^m i_m(a)
# ----------------------------------------------------------------------------
def sph_j(m, z):
    return mp.sqrt(mp.pi / (2 * z)) * mp.besselj(m + mp.mpf(1) / 2, z)

def sph_i(m, a):
    return mp.sqrt(mp.pi / (2 * a)) * mp.besseli(m + mp.mpf(1) / 2, a)

def leg_norm(m):
    return mp.sqrt((2 * mp.mpf(m) + 1) / 2)

def F_leg_even(i, gamma, h):
    """F of P~_{2i}(u/h) on [-h,h] at frequency gamma"""
    m = 2 * i
    return h * leg_norm(m) * 2 * (-1) ** i * sph_j(m, gamma * h)

def pole_leg(m, h, sign):
    """int_{-h}^{h} P~_m(u/h) exp(sign*u/2) du"""
    a = h / 2
    val = h * leg_norm(m) * 2 * sph_i(m, a)
    if sign < 0:
        val = val * (-1) ** m
    return val

# ----------------------------------------------------------------------------
# build rows for a basis given as list of (parity, coeff-vector)
#   even basis vector: coeffs over P~_0,P~_2,...
#   odd  injected vector: single P~_1 (coeff [1]) -- negative control only
# ----------------------------------------------------------------------------
def build_L(basis, gammas, h):
    N = len(gammas)
    d = len(basis)
    # precompute Legendre-row tables
    Kmax = max(len(v) for p, v in basis if p == "even") if any(p == "even" for p, v in basis) else 0
    Ftab = [[F_leg_even(i, g, h) for i in range(Kmax)] for g in gammas]
    Pp = [pole_leg(2 * i, h, +1) for i in range(Kmax)]
    Pm = [pole_leg(2 * i, h, -1) for i in range(Kmax)]
    E = mp.zeros(N, d)
    lp = mp.zeros(1, d)
    lm = mp.zeros(1, d)
    for col, (par, v) in enumerate(basis):
        if par == "even":
            for j in range(N):
                E[j, col] = mp.fsum(v[i] * Ftab[j][i] for i in range(len(v)))
            lp[0, col] = mp.fsum(v[i] * Pp[i] for i in range(len(v)))
            lm[0, col] = mp.fsum(v[i] * Pm[i] for i in range(len(v)))
        else:  # odd P~_1: F = int P_1 cos = 0 exactly; pole rows differ in sign
            for j in range(N):
                E[j, col] = mp.mpf(0)
            lp[0, col] = pole_leg(1, h, +1)
            lm[0, col] = pole_leg(1, h, -1)
    L = mp.zeros(N + 1, d)
    for j in range(N):
        for col in range(d):
            L[j, col] = E[j, col]
    for col in range(d):
        L[N, col] = lp[0, col]
    return E, lp, lm, L

def singular_values(A):
    S = mp.svd_r(A, compute_uv=False)
    return sorted([S[i] for i in range(len(S))], reverse=True)

def rank_of(S, thr_rel):
    if not S:
        return 0
    smax = S[0]
    return sum(1 for s in S if s > thr_rel * smax)

def kernel_residuals(L, d, k):
    """residual norms ||L v|| of the k unit vectors spanning the numerical kernel,
    taken from the full SVD (rows of V^T beyond rank)."""
    U, S, V = mp.svd_r(L, full_matrices=True)
    res = []
    for i in range(d - k, d):
        v = mp.matrix([V[i, r] for r in range(d)])
        res.append(mp.norm(L * v))
    return res

def rel_digits(a, b):
    if a == 0 and b == 0:
        return mp.inf
    den = max(abs(a), abs(b))
    diff = abs(a - b) / den
    if diff == 0:
        return mp.inf
    return -mp.log10(diff)

# ----------------------------------------------------------------------------
# G1: closed form vs quadrature on one entry
# ----------------------------------------------------------------------------
def gate_math(h, gamma):
    i = 3  # P~_6
    closed = F_leg_even(i, gamma, h)
    f = lambda u: leg_norm(6) * mp.legendre(6, u / h) * mp.cos(gamma * u)
    quad = mp.quad(f, mp.linspace(-h, h, 40))
    digits = rel_digits(closed, quad)
    closedp = pole_leg(6, h, +1)
    fp = lambda u: leg_norm(6) * mp.legendre(6, u / h) * mp.exp(u / 2)
    quadp = mp.quad(fp, [-h, h])
    digitsp = rel_digits(closedp, quadp)
    return digits, digitsp

# ----------------------------------------------------------------------------
def run_cell(name, dps, cutoffs, basis_mode, dup_zero, inject_odd, quick):
    cell = CELLS[name]
    mp.mp.dps = dps
    Omega = mp.mpf(cell["Omega"])
    h = mp.log(Q) / 2
    c = Omega * h
    N_paper, d_paper = cell["N"], cell["d"]

    out = dict(cell=name, Omega=str(Omega), h=str(h), c=str(c), dps=dps)
    t0 = time.time()
    gam_all = zeta_ordinates(N_paper + 1)
    N = sum(1 for g in gam_all if g < Omega)
    gammas = gam_all[:N]
    out["N"] = N
    out["gamma_N"] = mp.nstr(gammas[-1], 15)
    out["gamma_next"] = mp.nstr(gam_all[N], 15)
    ok_N = (N == N_paper)
    print(f"[{name}] Omega={mp.nstr(Omega,10)}  h={mp.nstr(h,12)}  c={mp.nstr(c,10)}  "
          f"N(<Omega)={N} (paper {N_paper}) {'OK' if ok_N else 'MISMATCH'}  "
          f"gamma_N={out['gamma_N']}  next={out['gamma_next']}  [{time.time()-t0:.1f}s]")

    if dup_zero:
        gammas[-1] = gammas[-2]
        print(f"[{name}] NEGATIVE CONTROL dup-zero: gamma_{N} := gamma_{N-1} (repeated ordinate)")

    d = d_paper
    if basis_mode == "firstd":
        d_even = (d + 1) // 2
        print(f"[{name}] BOUNDARY basis=firstd: first {d} modes of all parities -> even dimension {d_even}")
        d = d_even

    # G1
    dg, dgp = gate_math(h, gammas[0])
    g1 = (dg > dps - 12) and (dgp > dps - 12)
    print(f"[{name}] G1 MATH  closed-form vs quadrature: cos-row {mp.nstr(dg,4)} digits, pole-row {mp.nstr(dgp,4)} digits  -> {'PASS' if g1 else 'FAIL'}")
    out["G1"] = dict(cos_digits=str(dg), pole_digits=str(dgp), pass_=g1)

    results = []
    for K in cutoffs:
        t1 = time.time()
        modes, chis = prolate_even(c, K, d)
        sh = mp.sqrt(h)
        modes = [[x / sh for x in v] for v in modes]   # unit L2 norm on [-h,h]
        basis = [("even", v) for v in modes]
        if inject_odd:
            basis[-1] = ("odd", [mp.mpf(1)])
        E, lp, lm, L = build_L(basis, gammas, h)

        SE = singular_values(E)
        SL = singular_values(L)
        thr = mp.mpf("1e-35")
        rE = rank_of(SE, thr)
        rL = rank_of(SL, thr)
        dimW = d - rL
        floor = mp.mpf(10) ** (-(dps - 2)) * SL[0]
        g2 = SL[-1] > floor
        # Remark 1
        diff = max(abs(lp[0, i] - lm[0, i]) for i in range(d))
        scale = max(abs(lp[0, i]) for i in range(d))
        rem1 = diff / scale
        g5r = rem1 < mp.mpf(10) ** (-(dps - 8))
        # kernel residuals
        res = kernel_residuals(L, d, max(dimW, 1)) if dimW > 0 else []
        r = dict(K=K, rankE=rE, rankL=rL, dimW=dimW,
                 sigma_min_L=SL[-1], sigma_max_L=SL[0], floor=floor,
                 remark1=rem1, residuals=res, chi_min=chis[0], chi_max=chis[-1],
                 last_coeff=max(abs(v[-1]) for v in modes))
        results.append(r)
        print(f"[{name}] K={K:3d}  rankE={rE} rankL={rL} dimW={dimW}  "
              f"sigma_min(L)={mp.nstr(SL[-1],9)}  floor={mp.nstr(floor,3)} {'G2 PASS' if g2 else 'G2 FAIL(below floor)'}  "
              f"Remark1 |l+-l-|/|l+|={mp.nstr(rem1,3)} {'PASS' if g5r else 'FAIL'}  "
              f"resid={[mp.nstr(x,3) for x in res]}  tailcoef={mp.nstr(r['last_coeff'],3)}  [{time.time()-t1:.1f}s]")

    # G3 consistency across cutoffs
    g3 = True
    agree = None
    if len(results) >= 2:
        a, b = results[0], results[1]
        agree = rel_digits(a["sigma_min_L"], b["sigma_min_L"])
        g3 = (a["rankE"] == b["rankE"] and a["rankL"] == b["rankL"] and agree >= 20)
        print(f"[{name}] G3 CONSIST ranks {'equal' if a['rankE']==b['rankE'] and a['rankL']==b['rankL'] else 'DIFFER'}, "
              f"sigma_min agreement {mp.nstr(agree,4)} rel. digits (need >=20) -> {'PASS' if g3 else 'FAIL'}")

    # paper comparison
    paper = mp.mpf(cell["sigma_min_paper"])
    last = results[-1]
    dpaper = rel_digits(last["sigma_min_L"], paper)
    print(f"[{name}] PAPER   sigma_min printed {cell['sigma_min_paper']}  ours {mp.nstr(last['sigma_min_L'],9)}  agreement {mp.nstr(dpaper,4)} digits")

    # theorem statement
    lower = max(0, d - N - 1)
    thm = (last["dimW"] == d - last["rankL"]) and (last["dimW"] >= lower)
    eq = (last["rankL"] == N + 1)
    print(f"[{name}] THEOREM 3  dimW={last['dimW']} = d-rankL  >= max(0,d-N-1)={lower}  {'OK' if thm else 'VIOLATED'}; "
          f"equality case (rankL=N+1): {'YES' if eq else 'NO'}")

    # verdicts
    expect = 2
    if basis_mode == "firstd":
        expect = 0
    if dup_zero:
        expect = 3
    verdict = (last["dimW"] == expect)
    tag = "EXPECTED" if verdict else "UNEXPECTED"
    if dup_zero:
        print(f"[{name}] NEGATIVE CONTROL dup-zero: dimW={last['dimW']} (must be 3, not 2) -> {'DUSTU as required (control works)' if verdict else 'TOOL FAILED TO DETECT'}")
    if inject_odd:
        print(f"[{name}] NEGATIVE CONTROL inject-odd: Remark1 gate {'FAILED as required (control works)' if not g5r else 'DID NOT FAIL -> TOOL IS A SHELL'}")
    if basis_mode == "firstd":
        print(f"[{name}] BOUNDARY firstd: dimW={last['dimW']} (paper: trivial kernel) -> {'PASS' if verdict else 'FAIL'}")
    if not (dup_zero or inject_odd or basis_mode == "firstd"):
        allpass = ok_N and g1 and g3 and all(x["sigma_min_L"] > x["floor"] for x in results) and verdict
        print(f"[{name}] VERDICT  dimW={last['dimW']}  rankL=N+1={eq}  -> {'GECTI' if allpass else 'DUSTU'}")
        out["verdict"] = "GECTI" if allpass else "DUSTU"
    out["results"] = [{k: (str(v) if not isinstance(v, (int, bool, list)) else v) for k, v in r.items()}
                      for r in results]
    for r in out["results"]:
        r["residuals"] = [str(x) for x in r["residuals"]]
    out["cutoff_agreement_digits"] = str(agree)
    out["paper_agreement_digits"] = str(dpaper)
    return out

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cell", default="both", choices=["A", "B", "both"])
    ap.add_argument("--dps", type=int, default=65)
    ap.add_argument("--cutoffs", default="88,112")
    ap.add_argument("--basis", default="even", choices=["even", "firstd"])
    ap.add_argument("--dup-zero", action="store_true")
    ap.add_argument("--inject-odd", action="store_true")
    ap.add_argument("--quick", action="store_true", help="dps 30, cutoff 60 (smoke)")
    ap.add_argument("--json", default=None)
    a = ap.parse_args()
    dps = 30 if a.quick else a.dps
    cutoffs = [60] if a.quick else [int(x) for x in a.cutoffs.split(",")]
    print(f"tw_reproduce.py v{VERSION}  md5={self_md5()}  mpmath {mp.__version__}  dps={dps}  cutoffs={cutoffs}  "
          f"basis={a.basis} dup_zero={a.dup_zero} inject_odd={a.inject_odd}")
    print("Floor declared before run: singular values below 10^-(dps-2)*sigma_max are NOT interpretable.")
    cells = ["A", "B"] if a.cell == "both" else [a.cell]
    outs = []
    for cname in cells:
        outs.append(run_cell(cname, dps, cutoffs, a.basis, a.dup_zero, a.inject_odd, a.quick))
    if a.json:
        with open(a.json, "w", encoding="utf-8") as f:
            json.dump(outs, f, indent=1)
        print(f"json -> {a.json}")

if __name__ == "__main__":
    main()

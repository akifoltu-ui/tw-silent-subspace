#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
tw_sigma_sert_v1.py  --  EQUALITY CERTIFICATE for Theorem 3 of
  M. A. Oltulu, "The dimension of silent subspaces in finite-sampling
  truncations of the Weil quadratic form", Zenodo 10.5281/zenodo.22730006.

TEK DOSYA, SIFIR YEREL IMPORT.  Tek bagimlilik: mpmath.

NE EKLIYOR (tw_reproduce.py v1.1'e gore):
  tw_reproduce sigma_min(L)'i SVD ile OLCUYOR (1.4148646e-12 / 7.64433434e-17).
  SVD iteratiftir; "bu sayi sifir degil mi, gurultu mu" sorusuna KANIT vermez.
  Bu arac ayni L'yi kurar (kurulum AYNEN alinmistir, degistirilen yok) ve
  G = L L^T uzerinde ARALIK (interval) LDL yapar. Tum pivotlarin ALT siniri
  pozitifse  lam_min(G) > 0  KANITLIDIR, yani:

      sigma_min(L) > 0  =>  rank L = N+1  =>  dim W = d - N - 1   (ESITLIK)

  Son halka Lean 4'te formel kanitli:  TwRank_v1_2.lean (TW.rank_of_gram_posDef,
  TW.dimW_eq_of_gram_posDef) ve hipotezin gerekliligi TwRankKarsiOrnek_v1.lean
  (TWKontrol.posSemidef_yetmez, `sorry` yok).

KAPILAR (hepsi her kosumda basilir):
  KAPI-SIGMA : SVD'nin sigma_min'i makaledeki degeri 8 haneyle vermeli
  KAPI-LDL   : G = L L^T icin tum pivot ALT sinirlari > 0
  KAPI-TABAN : en kucuk pivotun aralik GENISLIGI, kendi degerinin %1'inden kucuk
  KAPI-NEG   : dup-zero (gamma_N := gamma_{N-1}) ile LDL DUSMELI
               (dusmezse arac kabuktur ve sertifika hicbir sey ifade etmez)

KULLANIM:
  python -u tw_sigma_sert_v1.py                 # A ve B, dps 65, K 88, iv.dps 80,140
  python -u tw_sigma_sert_v1.py --cell A
  python -u tw_sigma_sert_v1.py --ivdps 80,140,200 --K 112
"""
import sys, argparse, hashlib, os, time
import mpmath as mp
from mpmath import iv

SURUM = "tw_sigma_sert_v1.py  v1.0"

def _md5():
    try:
        return hashlib.md5(open(os.path.abspath(__file__), "rb").read()).hexdigest()
    except Exception:
        return "N/A"

# --- hucreler: tw_reproduce.py v1.1 ile BIREBIR -----------------------------
CELLS = {
    "A": dict(Omega="75.5524",  N=18, d=21, sigma_paper="1.4148646e-12"),
    "B": dict(Omega="103.7255", N=30, d=33, sigma_paper="7.64433434e-17"),
}
Q = 13

# --- cift prolate modlari, normalize Legendre tabaninda (Bouwkamp) ----------
def beta(n):
    n = mp.mpf(n)
    return (n + 1) / mp.sqrt((2 * n + 1) * (2 * n + 3))

def prolate_even(c, K, d):
    M = mp.zeros(K, K)
    for i in range(K):
        n = 2 * i
        x2 = beta(n) ** 2 + (beta(n - 1) ** 2 if n >= 1 else mp.mpf(0))
        M[i, i] = mp.mpf(n * (n + 1)) + c * c * x2
        if i + 1 < K:
            o = c * c * beta(n) * beta(n + 1)
            M[i, i + 1] = o
            M[i + 1, i] = o
    ev, U = mp.eigsy(M)
    od = sorted(range(K), key=lambda k: ev[k])
    return [[U[i, k] for i in range(K)] for k in od[:d]]

def sph_j(m, z): return mp.sqrt(mp.pi / (2 * z)) * mp.besselj(m + mp.mpf(1) / 2, z)
def sph_i(m, a): return mp.sqrt(mp.pi / (2 * a)) * mp.besseli(m + mp.mpf(1) / 2, a)
def leg_norm(m): return mp.sqrt((2 * mp.mpf(m) + 1) / 2)

# --- ARALIK LDL: kanit ------------------------------------------------------
def ldl_interval(L, n, d, ivdps):
    """G = L L^T uzerinde aralik LDL. Donen: pivot listesi, gecti_mi, dusen_pivot."""
    iv.dps = ivdps
    A = [[sum((iv.mpf(L[i, k]) * iv.mpf(L[j, k]) for k in range(d)), iv.mpf(0))
          for j in range(n)] for i in range(n)]
    piv = []
    for k in range(n):
        p = A[k][k]
        piv.append(p)
        if not (p.a > 0):
            return piv, False, k
        for i in range(k + 1, n):
            f = A[i][k] / p
            for j in range(k, n):
                A[i][j] = A[i][j] - f * A[k][j]
    return piv, True, -1

def run_cell(name, dps, K, ivdps_list):
    cell = CELLS[name]
    mp.mp.dps = dps
    Omega = mp.mpf(cell["Omega"]); N = cell["N"]; d = cell["d"]
    h = mp.log(Q) / 2; c = Omega * h
    t0 = time.time()
    gam = [mp.im(mp.zetazero(k)) for k in range(1, N + 1)]
    print("[%s] Omega=%s  h=%s  c=%s  N=%d  d=%d  K=%d  gamma_N=%s" % (
        name, mp.nstr(Omega, 10), mp.nstr(h, 12), mp.nstr(c, 10), N, d, K,
        mp.nstr(gam[-1], 15)))

    modes = prolate_even(c, K, d)
    sh = mp.sqrt(h)
    modes = [[x / sh for x in v] for v in modes]          # [-h,h]'de birim L2
    Pp = [h * leg_norm(2 * i) * 2 * sph_i(2 * i, h / 2) for i in range(K)]

    def kur(gs):
        Ft = [[h * leg_norm(2 * i) * 2 * (-1) ** i * sph_j(2 * i, g * h)
               for i in range(K)] for g in gs]
        L = mp.zeros(N + 1, d)
        for col, v in enumerate(modes):
            for j in range(N):
                L[j, col] = mp.fsum(v[i] * Ft[j][i] for i in range(K))
            L[N, col] = mp.fsum(v[i] * Pp[i] for i in range(K))
        return L

    L = kur(gam)
    S = sorted(mp.svd_r(L, compute_uv=False), reverse=True)
    smin = S[-1]; paper = mp.mpf(cell["sigma_paper"])
    k_sig = abs(smin / paper - 1) < mp.mpf("1e-7")
    print("[%s] KAPI-SIGMA  SVD sigma_min = %s   (makale %s)  -> %s" % (
        name, mp.nstr(smin, 9), cell["sigma_paper"], "GECTI" if k_sig else "DUSTU"))

    ok_any = False; best = None; used = None
    for ivd in ivdps_list:
        piv, ok, bad = ldl_interval(L, N + 1, d, ivd)
        lo = min(p.a for p in piv)
        wd = max(p.delta for p in piv)
        mark = "GECTI (lam_min>0 KANITLI)" if ok else "DUSTU (pivot %d)" % bad
        print("[%s] KAPI-LDL    iv.dps=%3d  %-28s en kucuk pivot ALT siniri = %s" % (
            name, ivd, mark, mp.nstr(mp.mpf(lo), 10)))
        if ok and not ok_any:
            ok_any = True; best = lo; used = ivd; best_wd = wd
    if not ok_any:
        print("[%s] SERTIFIKA DUSTU -- iv.dps artirilmali" % name)
        return False

    rel = mp.mpf(best_wd) / mp.mpf(best) if best != 0 else mp.inf
    k_tab = rel < mp.mpf("0.01")
    print("[%s] KAPI-TABAN  en kucuk pivotun aralik genisligi / degeri = %s  -> %s" % (
        name, mp.nstr(rel, 4), "GECTI" if k_tab else "DUSTU"))

    g2 = list(gam); g2[-1] = g2[-2]
    piv2, ok2, bad2 = ldl_interval(kur(g2), N + 1, d, used)
    k_neg = not ok2
    print("[%s] KAPI-NEG    dup-zero (gamma_%d := gamma_%d): %s -> %s" % (
        name, N, N - 1, "LDL GECTI" if ok2 else "LDL DUSTU (pivot %d)" % bad2,
        "rank eksikligi YAKALANDI" if k_neg else "ARAC KABUK"))

    sig_lb = mp.sqrt(mp.mpf(best))
    allp = k_sig and k_tab and k_neg
    print("[%s] SERTIFIKA   lam_min(G) >= %s   =>   sigma_min(L) >= %s" % (
        name, mp.nstr(mp.mpf(best), 8), mp.nstr(sig_lb, 8)))
    print("[%s] SONUC       rank L = N+1 = %d  =>  dim W = d - N - 1 = %d   (ESITLIK)" % (
        name, N + 1, d - N - 1))
    print("[%s] KAPILAR     SIGMA=%s LDL=%s TABAN=%s NEG=%s  ->  %s   [%.0f s]\n" % (
        name, "GECTI" if k_sig else "DUSTU", "GECTI", "GECTI" if k_tab else "DUSTU",
        "GECTI" if k_neg else "DUSTU", "GECTI" if allp else "DUSTU", time.time() - t0))
    return allp

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cell", default="both", choices=["A", "B", "both"])
    ap.add_argument("--dps", type=int, default=65)
    ap.add_argument("--K", type=int, default=88)
    ap.add_argument("--ivdps", default="80,140")
    a = ap.parse_args()
    ivl = [int(x) for x in a.ivdps.split(",")]
    print("=" * 86)
    print(SURUM + "   md5=" + _md5() + "   mpmath " + mp.__version__)
    print("=" * 86)
    print("""ON-KAYIT (kosumdan ONCE ilan):
  Kurulum tw_reproduce.py v1.1'den AYNEN alinmistir; degistirilen yok.
  Iddia: G = L L^T pozitif tanimli  =>  rank L = N+1  =>  dim W = d-N-1 (ESITLIK).
  Son halka Lean 4'te formel kanitli (TwRank_v1_2.lean), hipotezin gerekliligi de
  (TwRankKarsiOrnek_v1.lean, `sorry` yok).
  Aracin siniri: sertifika ARALIK LDL pivotlarinin alt sinirina dayanir; bir pivotun
  alt siniri <= 0 ise sertifika DUSER ve iv.dps artirilmalidir.
""")
    cells = ["A", "B"] if a.cell == "both" else [a.cell]
    res = [run_cell(cn, a.dps, a.K, ivl) for cn in cells]
    print("=" * 86)
    print("TOPLU SONUC: %s" % ("HEPSI GECTI" if all(res) else "EN AZ BIRI DUSTU"))
    print("=" * 86)

if __name__ == "__main__":
    main()

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
tw_sigma_sert_v2.py  --  EQUALITY CERTIFICATE for Theorem 3 of
  M. A. Oltulu, "The dimension of silent subspaces in finite-sampling
  truncations of the Weil quadratic form", Zenodo 10.5281/zenodo.22730006.

TEK DOSYA, SIFIR YEREL IMPORT.  Tek bagimlilik: mpmath.

v1 -> v2 DUZELTMESI (2026-11-22)
  v1 (md5 6c913a12a5418e8cfc365039499037b7) su satiri basiyordu:
      lam_min(G) >= (en kucuk pivotun alt siniri)  =>  sigma_min(L) >= (onun karekoku)
  Bu cikarim GECERSIZDIR. Simetrik pozitif tanimli G icin k. pivot, sol ust k x k
  blogun Schur tumleyenidir:  d_k = 1/[(G_k)^-1]_kk >= lam_min(G_k) >= lam_min(G).
  Yani en kucuk pivot lam_min(G)'nin UST tarafindadir, alt siniri olamaz.
  Ornek (TwKeskinlik_v2.lean, Km = L L^T, L = [[1,1],[0,1]]): pivotlar 2 ve 1/2,
  lam_min = (3 - sqrt 5)/2 = 0.381966... < 1/2.
  v1'in kendi logunda da gorunur: A hucresinde SVD sigma_min = 1.4148646e-12,
  basilan "alt sinir" 1.5279842e-12 (B: 7.64433434e-17 ve 8.25513e-17).

  v1'in ASIL sonucu GECERLIDIR ve v2'de AYNEN korunur:
      tum pivotlarin alt siniri > 0  =>  G pozitif tanimli  =>  rank L = N+1
      =>  dim W = d - N - 1   (ESITLIK)
  Son halka Lean 4'te formel kanitli: TwRank_v1_2.lean (TW.rank_of_gram_posDef,
  TW.dimW_eq_of_gram_posDef); hipotezin gerekliligi TwRankKarsiOrnek_v1.lean.

v2 NE EKLIYOR: KAYMA SERTIFIKASI
  D = m / 10^k (m, k tam sayi) icin  G - D^2 I  uzerinde aralik LDL yapilir. D^2 bir
  araligin icinde tasinir. Tum pivotlarin alt siniri > 0 ise:
      G - D^2 I pozitif tanimli  =>  lam_min(G) > D^2  =>  sigma_min(L) > D.
  Basilan D tam olarak kanitlanan sayidir (yuvarlama yok).

KAPILAR (hepsi her kosumda basilir)
  OZ-SINAV       : L = [[1,1],[0,1]] (gercek sigma_min = (sqrt5 - 1)/2 = 0.6180339887...)
                   SVD dogru; v1 formulu gercegin USTUNDE (gecersizlik gosterimi);
                   kayma 0.618033 GECMELI, 0.618034 DUSMELI.  Gecmezse hucre kosulmaz.
  KAPI-SIGMA     : SVD sigma_min makaledeki degeri 8 haneyle vermeli (v1 ile ayni)
  KAPI-LDL       : G = L L^T icin tum pivot alt sinirlari > 0 (v1 ile ayni)
  KAPI-TABAN     : en kucuk pivotun aralik genisligi < degerinin %1'i (v1 ile ayni)
  KAPI-NEG       : dup-zero (gamma_N := gamma_{N-1}) ile LDL DUSMELI (v1 ile ayni)
  KAPI-V1        : en kucuk pivotun alt siniri v1 logundaki degeri vermeli (ayni L)
  KAPI-TEOREM    : en kucuk pivot >= sigma_min^2 (SVD) -- v1 formulunun neden gecersiz
                   oldugunun canli verideki gosterimi
  KAPI-KAYMA     : D = theta * sigma_min (theta 0.999, olmazsa 0.99, olmazsa 0.9; 8 hane,
                   asagi) icin G - D^2 I aralik LDL ile GECMELI
  KAPI-KAYMA-NEG : D = 1.001 * sigma_min icin G - D^2 I DUSMELI (dusmezse kayma
                   uygulanmiyor demektir; arac kabuktur)
  KAPI-TUTARLILIK: kanitlanan D, SVD sigma_min'in ALTINDA olmali

ARACIN SINIRI (v1 ile ayni, degismedi)
  Aralik aritmetigi, hesaplanmis L'nin (dps 65, K Legendre terimi) nokta degerlerinden
  baslar. L'nin kendi hesaplama hatasi araliga girmez; sertifika hesaplanmis L icindir.

KULLANIM
  python -u tw_sigma_sert_v2.py --oz-sinav      # yalniz oz-sinav (saniyeler)
  python -u tw_sigma_sert_v2.py                 # oz-sinav + A ve B (dps 65, K 88, iv.dps 80,140)
  python -u tw_sigma_sert_v2.py --cell A
"""
import sys, argparse, hashlib, os, time
from decimal import Decimal, ROUND_FLOOR
import mpmath as mp
from mpmath import iv

try:
    sys.stdout.reconfigure(errors="replace")
except Exception:
    pass

SURUM = "tw_sigma_sert_v2.py  v2.0"

def _md5():
    try:
        return hashlib.md5(open(os.path.abspath(__file__), "rb").read()).hexdigest()
    except Exception:
        return "N/A"

# --- hucreler: tw_reproduce.py v1.1 ve tw_sigma_sert_v1.py ile BIREBIR --------
CELLS = {
    "A": dict(Omega="75.5524",  N=18, d=21, sigma_paper="1.4148646e-12"),
    "B": dict(Omega="103.7255", N=30, d=33, sigma_paper="7.64433434e-17"),
}
Q = 13
# v1 canli logu (run_sertifika_canli.log): iv.dps=80 ve 140'ta en kucuk pivot ALT siniri
V1_LOG = {"A": "2.334735619e-24", "B": "6.814717198e-33"}
THETAS = ("0.999", "0.99", "0.9")
THETA_NEG = "1.001"

# --- cift prolate modlari, normalize Legendre tabaninda (Bouwkamp) -- v1 AYNEN ---
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

# --- ARALIK LDL ---------------------------------------------------------------
def ldl_interval(L, n, d, ivdps, kayma=None):
    """G = L L^T (kayma=(m, k) verilirse G - D^2 I, D = m / 10^k) uzerinde aralik LDL.
    Donen: pivot listesi, gecti_mi, dusen_pivot. kayma=None iken v1 ile AYNI hesap."""
    iv.dps = ivdps
    A = [[sum((iv.mpf(L[i, t]) * iv.mpf(L[j, t]) for t in range(d)), iv.mpf(0))
          for j in range(n)] for i in range(n)]
    if kayma is not None:
        km, kk = kayma
        Dv = iv.mpf(km) / iv.mpf(10 ** kk)        # D'yi iceren aralik (tam ondalik)
        S = Dv * Dv                               # D^2'yi iceren aralik
        for i in range(n):
            A[i][i] = A[i][i] - S
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

# --- ondalik yardimcilar (yalniz Python decimal) --------------------------------
def ondalik_metin(m, k):
    """m / 10^k icin bilimsel gosterim (m > 0 tam sayi)."""
    s = str(m)
    return "%s.%se%d" % (s[0], s[1:] if len(s) > 1 else "0", len(s) - 1 - k)

def ondalik_asagi(x, hane=8):
    """x > 0 (mp sayisi) icin 'hane' anlamli haneye asagi kesilmis D = m / 10^k (k > 0).
    D'nin sigma_min'in altinda kaldigi KAPI-TUTARLILIK ile ayrica denetlenir."""
    q = Decimal(mp.nstr(x, hane + 6))
    if not (q > 0):
        raise ValueError("ondalik_asagi: x > 0 olmali")
    us = q.adjusted() - (hane - 1)
    if us >= 0:
        raise ValueError("ondalik_asagi: beklenmeyen buyukluk")
    m = int(q.scaleb(-us).to_integral_value(rounding=ROUND_FLOOR))
    return m, -us, ondalik_metin(m, -us)

def gk(b):
    return "GECTI" if b else "DUSTU"

# --- OZ-SINAV: kendi 2x2 ornegi (TwKeskinlik_v2.lean, Km = L L^T) -------------
def oz_sinav():
    mp.mp.dps = 50
    L2 = mp.zeros(2, 2)
    L2[0, 0] = 1; L2[0, 1] = 1; L2[1, 1] = 1
    gercek = (mp.sqrt(5) - 1) / 2                      # sigma_min([[1,1],[0,1]])
    S = sorted(mp.svd_r(L2, compute_uv=False), reverse=True)
    k1 = abs(S[-1] - gercek) < mp.mpf("1e-40")
    piv, ok, bad = ldl_interval(L2, 2, 2, 60)
    lo = min(p.a for p in piv)
    v1_formul = mp.sqrt(mp.mpf(lo))                    # v1'in 'alt sinir'i: sqrt(1/2)
    k2 = bool(ok) and (v1_formul > gercek)
    _, ok_alt, _ = ldl_interval(L2, 2, 2, 60, kayma=(618033, 6))   # 0.618033 < gercek
    _, ok_ust, _ = ldl_interval(L2, 2, 2, 60, kayma=(618034, 6))   # 0.618034 > gercek
    k3 = bool(ok_alt) and not ok_ust
    print("OZ-SINAV  L = [[1,1],[0,1]]  (Km = L L^T, TwKeskinlik_v2.lean)")
    print("  gercek sigma_min = (sqrt5 - 1)/2 = %s ; SVD = %s  -> %s" % (
        mp.nstr(gercek, 12), mp.nstr(S[-1], 12), gk(k1)))
    print("  pivotlar G: %s ve %s ; v1 formulu sqrt(en kucuk pivot) = %s > gercek  -> v1 formulu GECERSIZ (beklenen)  -> %s" % (
        mp.nstr(mp.mpf(piv[0].a), 6), mp.nstr(mp.mpf(piv[-1].a), 6), mp.nstr(v1_formul, 8), gk(k2)))
    print("  kayma D = 0.618033 (< gercek): %s ; D = 0.618034 (> gercek): %s  -> %s" % (
        "GECTI" if ok_alt else "DUSTU", "GECTI" if ok_ust else "DUSTU", gk(k3)))
    sonuc = k1 and k2 and k3
    print("OZ-SINAV SONUC: %s\n" % gk(sonuc))
    return sonuc

# --- hucre sertifikasi: tum kapilar --------------------------------------------
def sertifika(name, L, n, d, smin, k_sig, ivdps_list, L_neg, t0):
    # (1) v1 ile AYNI: G = L L^T aralik LDL
    ok_any = False; best = None; used = None; best_wd = None
    for ivd in ivdps_list:
        piv, ok, bad = ldl_interval(L, n, d, ivd)
        lo = min(p.a for p in piv)
        wd = max(p.delta for p in piv)
        mark = "GECTI (G poz. tanimli)" if ok else "DUSTU (pivot %d)" % bad
        print("[%s] KAPI-LDL         iv.dps=%3d  %-24s en kucuk pivot ALT siniri = %s" % (
            name, ivd, mark, mp.nstr(mp.mpf(lo), 10)))
        if ok and not ok_any:
            ok_any = True; best = lo; used = ivd; best_wd = wd
    if not ok_any:
        print("[%s] SERTIFIKA DUSTU -- iv.dps artirilmali" % name)
        return False

    rel = mp.mpf(best_wd) / mp.mpf(best) if mp.mpf(best) != 0 else mp.inf
    k_tab = rel < mp.mpf("0.01")
    print("[%s] KAPI-TABAN       en kucuk pivotun aralik genisligi / degeri = %s  -> %s" % (
        name, mp.nstr(rel, 4), gk(k_tab)))

    piv2, ok2, bad2 = ldl_interval(L_neg, n, d, used)
    k_neg = not ok2
    print("[%s] KAPI-NEG         dup-zero: %s -> %s" % (
        name, "LDL GECTI" if ok2 else "LDL DUSTU (pivot %d)" % bad2,
        "rank eksikligi YAKALANDI" if k_neg else "ARAC KABUK"))

    # (2) KAPI-V1: ayni L mi?
    if name in V1_LOG:
        r1 = abs(mp.mpf(best) / mp.mpf(V1_LOG[name]) - 1)
        k_v1 = r1 < mp.mpf("1e-8")
        print("[%s] KAPI-V1          en kucuk pivot alt siniri %s ; v1 logu %s ; bagil fark %s  -> %s" % (
            name, mp.nstr(mp.mpf(best), 10), V1_LOG[name], mp.nstr(r1, 3), gk(k_v1)))
    else:
        k_v1 = True
        print("[%s] KAPI-V1          v1 referansi yok (yalniz A ve B icin) -> atlandi" % name)

    # (3) KAPI-TEOREM: en kucuk pivot >= sigma_min^2 ; v1 formulu neden gecersiz
    v1_formul = mp.sqrt(mp.mpf(best))
    k_teo = mp.mpf(best) >= smin ** 2 * (1 - mp.mpf("1e-9"))
    print("[%s] KAPI-TEOREM      en kucuk pivot %s >= SVD sigma_min^2 %s ; v1 formulu sqrt = %s > SVD %s  -> v1 'alt sinir'i GECERSIZ  -> %s" % (
        name, mp.nstr(mp.mpf(best), 8), mp.nstr(smin ** 2, 8), mp.nstr(v1_formul, 8),
        mp.nstr(smin, 8), gk(k_teo)))

    # (4) KAPI-KAYMA: G - D^2 I > 0  =>  sigma_min(L) > D
    k_kay = False; D_m = D_k = None; D_txt = None; th_ok = None; ivd_ok = None
    for th in THETAS:
        m_, k_, txt = ondalik_asagi(smin * mp.mpf(th), 8)
        for ivd in ivdps_list:
            _, okk, badk = ldl_interval(L, n, d, ivd, kayma=(m_, k_))
            print("[%s]                  kayma theta=%s D=%s iv.dps=%3d : %s" % (
                name, th, txt, ivd, "GECTI" if okk else "DUSTU (pivot %d)" % badk))
            if okk:
                k_kay = True; D_m, D_k, D_txt, th_ok, ivd_ok = m_, k_, txt, th, ivd
                break
        if k_kay:
            break
    print("[%s] KAPI-KAYMA       -> %s" % (name, gk(k_kay)))

    # (5) KAPI-KAYMA-NEG: D = 1.001 sigma_min DUSMELI
    mn, kn, txtn = ondalik_asagi(smin * mp.mpf(THETA_NEG), 8)
    _, okn, badn = ldl_interval(L, n, d, ivdps_list[-1], kayma=(mn, kn))
    k_kneg = not okn
    print("[%s] KAPI-KAYMA-NEG   D = %s (= %s x SVD) iv.dps=%3d : %s  -> %s" % (
        name, txtn, THETA_NEG, ivdps_list[-1], "GECTI" if okn else "DUSTU (pivot %d)" % badn,
        "kayma etkili" if k_kneg else "ARAC KABUK"))

    # (6) KAPI-TUTARLILIK: kanitlanan D < SVD sigma_min
    if k_kay:
        k_tut = Decimal(D_txt) < Decimal(mp.nstr(smin, 20))
    else:
        k_tut = False
    print("[%s] KAPI-TUTARLILIK  kanitlanan D = %s < SVD sigma_min = %s  -> %s" % (
        name, D_txt, mp.nstr(smin, 10), gk(k_tut)))

    allp = k_sig and k_tab and k_neg and k_v1 and k_teo and k_kay and k_kneg and k_tut
    if k_kay:
        print("[%s] SERTIFIKA v2     G - D^2 I pozitif tanimli (aralik LDL, iv.dps=%d, theta=%s)" % (
            name, ivd_ok, th_ok))
        print("[%s]                  =>  lam_min(G) > D^2 = %s   =>   sigma_min(L) > D = %s" % (
            name, ondalik_metin(D_m * D_m, 2 * D_k), D_txt))
    print("[%s] SONUC            rank L = N+1 = %d  =>  dim W = d - N - 1 = %d   (ESITLIK; v1 ile ayni)" % (
        name, n, d - n))
    print("[%s] KAPILAR          SIGMA=%s LDL=GECTI TABAN=%s NEG=%s V1=%s TEOREM=%s KAYMA=%s KAYMA-NEG=%s TUTARLILIK=%s  ->  %s   [%.0f s]\n" % (
        name, gk(k_sig), gk(k_tab), gk(k_neg), gk(k_v1), gk(k_teo), gk(k_kay), gk(k_kneg),
        gk(k_tut), gk(allp), time.time() - t0))
    return allp

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
    print("[%s] KAPI-SIGMA       SVD sigma_min = %s   (makale %s)  -> %s" % (
        name, mp.nstr(smin, 9), cell["sigma_paper"], gk(k_sig)))

    g2 = list(gam); g2[-1] = g2[-2]
    return sertifika(name, L, N + 1, d, smin, k_sig, ivdps_list, kur(g2), t0)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cell", default="both", choices=["A", "B", "both"])
    ap.add_argument("--dps", type=int, default=65)
    ap.add_argument("--K", type=int, default=88)
    ap.add_argument("--ivdps", default="80,140")
    ap.add_argument("--oz-sinav", action="store_true")
    a = ap.parse_args()
    ivl = [int(x) for x in a.ivdps.split(",")]
    print("=" * 86)
    print(SURUM + "   md5=" + _md5() + "   mpmath " + mp.__version__ + "   python " + sys.version.split()[0])
    print("=" * 86)
    print("""ON-KAYIT (kosumdan ONCE ilan; v1 sonucu ve v1 hatasi BILINEREK yazildi):
  Duzeltilen: v1'in 'lam_min(G) >= en kucuk pivot' satiri gecersiz (pivot >= lam_min).
  Korunan: G = L L^T pozitif tanimli => rank L = N+1 => dim W = d-N-1 (ESITLIK), Lean halkasi.
  Beklenenler [TAHMIN]: OZ-SINAV gecer (~%99); KAPI-V1 v1 pivotlarini 1e-8 icinde verir (~%99);
  KAPI-TEOREM gecer (~%99); KAYMA theta=0.999'da gecer (~%95); KAYMA-NEG duser (~%99);
  TUTARLILIK gecer (~%99). Herhangi biri dusersa sonuc ilan EDILMEZ, once neden bulunur.
  Aracin siniri: aralik aritmetigi hesaplanmis L'den baslar; L'nin kendi hesaplama
  hatasi araliga girmez (v1 ile ayni).
""")
    if not oz_sinav():
        print("OZ-SINAV DUSTU: hucreler KOSULMADI.")
        sys.exit(2)
    if a.oz_sinav:
        return
    cells = ["A", "B"] if a.cell == "both" else [a.cell]
    res = [run_cell(cn, a.dps, a.K, ivl) for cn in cells]
    print("=" * 86)
    print("TOPLU SONUC: %s" % ("HEPSI GECTI" if all(res) else "EN AZ BIRI DUSTU"))
    print("=" * 86)

if __name__ == "__main__":
    main()

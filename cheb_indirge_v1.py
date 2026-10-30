#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
cheb_indirge_v1.py  --  T-W ornekleme matrisinin CHEBYSHEV INDIRGEMESI.

AMAC (Teorem adayi, su an HIPOTEZ):
  Simdiye kadar "rank L = N+1" HER HUCREDE AYRI dogrulaniyordu. Genel bir
  teorem yoktu. Bu arac, genel teoreme giden ilk halkayi test eder.

ELLE TURETME (kosumdan ONCE ilan):
  Prolate'nin tanimlayici ozelligi, sonlu Fourier donusumunun ozfonksiyonu
  olmasidir:   int_{-1}^{1} psi_n(t) e^{i c s t} dt = mu_n psi_n(s),
  ve bu ozdeslik her KARMASIK s icin analitik olarak devam eder.
  Bizim satirlarimiz tam bu integrallerdir:
      ornekleme satiri j : s_j = gamma_j / Omega        (reel, 0<s<1)
      kutup satiri       : cosh(u/2)=cos(i u/2) => s = i/(2 Omega)  (saf sanal)
  Dolayisiyla IDDIA:
      L[j,i] = h * mu_{2i} * psi_{2i}(s_j),     mu_{2i} != 0
  Kosegen carpan tersinir oldugundan  rank L = rank Psi,  Psi[j,i]=psi_{2i}(s_j).
  Ayrica psi_{2i} CIFT oldugundan psi_{2i}(s)=phi_i(s^2); noktalar tek bir REEL
  eksende toplanir:  w_j=(gamma_j/Omega)^2 in (0,1),  w_kutup=-1/(4 Omega^2)<0.
  Boylece soru su hale gelir: {phi_0..phi_{d-1}} ailesi (-inf,1] uzerinde bir
  CHEBYSHEV (Haar) sistemi mi? Oyleyse farkli N+1<=d nokta icin determinant hic
  sifirlanmaz ve rank L = N+1 bir TEOREM olur.

BU ARACIN SINIRI (ilan):
  Bu arac Chebyshev ozelligini KANITLAMAZ. Yalnizca yukaridaki INDIRGEMEYI
  olcer: oran sutun basina sabit mi, mu'ler sifirdan farkli mi, iki matrisin
  ranki ayni mi. Indirgeme tutarsa problem yeniden yazilmis olur.

KAPILAR:
  KAPI-ORAN : L[j,i]/Psi[j,i] her j icin AYNI (sutun basina sabit = h*mu_{2i})
  KAPI-MU   : butun mu_{2i} sifirdan uzak
  KAPI-RANK : rank L == rank Psi  (ayni tekil deger profili)
  KAPI-NEG  : bir mu kasten sifirlanirsa rank DUSMELI (arac kabuk degil)

KULLANIM:
  python -u cheb_indirge_v1.py              # A ve B
  python -u cheb_indirge_v1.py --cell A
"""
import argparse, hashlib, os, time
import mpmath as mp

SURUM = "cheb_indirge_v1.py  v1.0"
CELLS = {
    "A": dict(Omega="75.5524",  N=18, d=21),
    "B": dict(Omega="103.7255", N=30, d=33),
}
Q = 13

def _md5():
    try: return hashlib.md5(open(os.path.abspath(__file__), "rb").read()).hexdigest()
    except Exception: return "N/A"

def beta(n):
    n = mp.mpf(n); return (n + 1) / mp.sqrt((2 * n + 1) * (2 * n + 3))

def prolate_even(c, K, d):
    M = mp.zeros(K, K)
    for i in range(K):
        n = 2 * i
        x2 = beta(n) ** 2 + (beta(n - 1) ** 2 if n >= 1 else mp.mpf(0))
        M[i, i] = mp.mpf(n * (n + 1)) + c * c * x2
        if i + 1 < K:
            o = c * c * beta(n) * beta(n + 1); M[i, i + 1] = o; M[i + 1, i] = o
    ev, U = mp.eigsy(M)
    od = sorted(range(K), key=lambda k: ev[k])
    return [[U[i, k] for i in range(K)] for k in od[:d]]

def sph_j(m, z): return mp.sqrt(mp.pi / (2 * z)) * mp.besselj(m + mp.mpf(1) / 2, z)
def sph_i(m, a): return mp.sqrt(mp.pi / (2 * a)) * mp.besseli(m + mp.mpf(1) / 2, a)
def ln_(m): return mp.sqrt((2 * mp.mpf(m) + 1) / 2)

def run(name, dps, K):
    cell = CELLS[name]; mp.mp.dps = dps
    Om = mp.mpf(cell["Omega"]); N = cell["N"]; d = cell["d"]
    h = mp.log(Q) / 2; c = Om * h
    t0 = time.time()
    gam = [mp.im(mp.zetazero(k)) for k in range(1, N + 1)]
    print("[%s] Omega=%s N=%d d=%d K=%d  c=%s" % (
        name, mp.nstr(Om, 10), N, d, K, mp.nstr(c, 10)))

    V = prolate_even(c, K, d)          # Legendre katsayilari (normalize degil)
    sh = mp.sqrt(h)

    # --- ESKI YOL: L (Bessel kapali formu), tw_reproduce ile ayni -------------
    Pp = [h * ln_(2 * i) * 2 * sph_i(2 * i, h / 2) for i in range(K)]
    Ft = [[h * ln_(2 * i) * 2 * (-1) ** i * sph_j(2 * i, g * h) for i in range(K)]
          for g in gam]
    L = mp.zeros(N + 1, d)
    for col, v in enumerate(V):
        vv = [x / sh for x in v]
        for j in range(N):
            L[j, col] = mp.fsum(vv[i] * Ft[j][i] for i in range(K))
        L[N, col] = mp.fsum(vv[i] * Pp[i] for i in range(K))

    # --- YENI YOL: Psi[j,i] = psi_{2i}(s_j),  Legendre ile analitik devam -----
    s = [g / Om for g in gam] + [mp.mpc(0, 1) / (2 * Om)]
    Pleg = [[mp.legendre(2 * i, sj) for i in range(K)] for sj in s]
    Psi = mp.zeros(N + 1, d)
    for col, v in enumerate(V):
        vv = [x / sh for x in v]
        for j in range(N + 1):
            z = mp.fsum(vv[i] * ln_(2 * i) * Pleg[j][i] for i in range(K))
            Psi[j, col] = mp.re(z)      # cift fonksiyon: sanal nokta da reel verir

    # --- KAPI-ORAN -----------------------------------------------------------
    enk = mp.mpf(0); mus = []
    for col in range(d):
        r0 = L[0, col] / Psi[0, col]
        mus.append(r0 / h)
        for j in range(1, N + 1):
            r = L[j, col] / Psi[j, col]
            enk = max(enk, abs(r / r0 - 1))
    k_oran = enk < mp.mpf("1e-25")
    print("[%s] KAPI-ORAN   sutun ici en buyuk bagil sapma = %s  -> %s" % (
        name, mp.nstr(enk, 6), "GECTI" if k_oran else "DUSTU"))

    # --- KAPI-MU -------------------------------------------------------------
    amu = [abs(x) for x in mus]
    k_mu = min(amu) > mp.mpf("1e-300")
    print("[%s] KAPI-MU     mu_0 = %s   en kucuk |mu| = %s  -> %s" % (
        name, mp.nstr(mus[0], 10), mp.nstr(min(amu), 6), "GECTI" if k_mu else "DUSTU"))

    # --- KAPI-RANK -----------------------------------------------------------
    SL = sorted(mp.svd_r(L, compute_uv=False), reverse=True)
    SP = sorted(mp.svd_r(Psi, compute_uv=False), reverse=True)
    esik = mp.mpf("1e-35")
    rL = sum(1 for x in SL if x > esik * SL[0])
    rP = sum(1 for x in SP if x > esik * SP[0])
    k_rank = (rL == rP == N + 1)
    print("[%s] KAPI-RANK   rank L = %d   rank Psi = %d   (N+1 = %d)  -> %s" % (
        name, rL, rP, N + 1, "GECTI" if k_rank else "DUSTU"))
    print("[%s]             sigma_min(L) = %s   sigma_min(Psi) = %s" % (
        name, mp.nstr(SL[-1], 8), mp.nstr(SP[-1], 8)))

    # --- w ekseni ------------------------------------------------------------
    w = [(g / Om) ** 2 for g in gam]
    wk = -1 / (4 * Om * Om)
    print("[%s] w EKSENI    ornekleme w in [%s, %s]   kutup w = %s" % (
        name, mp.nstr(min(w), 6), mp.nstr(max(w), 6), mp.nstr(wk, 6)))

    # --- KAPI-NEG: bir mu sifirlanirsa rank dusmeli --------------------------
    L2 = mp.zeros(N + 1, d)
    for j in range(N + 1):
        for i in range(d):
            L2[j, i] = mp.mpf(0) if i == d - 1 else L[j, i]
    S2 = sorted(mp.svd_r(L2, compute_uv=False), reverse=True)
    r2 = sum(1 for x in S2 if x > esik * S2[0])
    k_neg = r2 < rL or d - 1 < N + 1
    # d-1 >= N+1 oldugunda rank korunabilir; gercek negatif kontrol: bir SATIRI tekrarla
    L3 = mp.zeros(N + 1, d)
    for j in range(N + 1):
        src = N - 2 if j == N - 1 else j
        for i in range(d):
            L3[j, i] = L[src, i]
    S3 = sorted(mp.svd_r(L3, compute_uv=False), reverse=True)
    r3 = sum(1 for x in S3 if x > esik * S3[0])
    k_neg = r3 == N
    print("[%s] KAPI-NEG    satir tekrari -> rank = %d (beklenen %d)  -> %s" % (
        name, r3, N, "GECTI" if k_neg else "DUSTU"))

    hep = k_oran and k_mu and k_rank and k_neg
    print("[%s] KAPILAR     ORAN=%s MU=%s RANK=%s NEG=%s  ->  %s   [%.0f s]\n" % (
        name, "G" if k_oran else "D", "G" if k_mu else "D",
        "G" if k_rank else "D", "G" if k_neg else "D",
        "GECTI" if hep else "DUSTU", time.time() - t0))
    return hep

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cell", default="both", choices=["A", "B", "both"])
    ap.add_argument("--dps", type=int, default=60)
    ap.add_argument("--K", type=int, default=88)
    a = ap.parse_args()
    print("=" * 86)
    print(SURUM + "   md5=" + _md5() + "   mpmath " + mp.__version__)
    print("=" * 86)
    print("""ON-KAYIT (kosumdan ONCE):
  IDDIA: L[j,i] = h * mu_{2i} * psi_{2i}(s_j),  s_j = gamma_j/Omega (reel),
         kutup satiri icin s = i/(2 Omega) (saf sanal). mu_{2i} != 0 oldugundan
         rank L = rank Psi,  Psi[j,i] = psi_{2i}(s_j).
  BEKLENTI: ORAN sapmasi < 1e-25; iki matrisin ranki ayni ve N+1; satir tekrari
         rank'i N'e dusurur.
  SINIR: bu arac Chebyshev ozelligini KANITLAMAZ, yalnizca indirgemeyi olcer.
""")
    cells = ["A", "B"] if a.cell == "both" else [a.cell]
    r = [run(cn, a.dps, a.K) for cn in cells]
    print("=" * 86)
    print("TOPLU SONUC: %s" % ("HEPSI GECTI" if all(r) else "EN AZ BIRI DUSTU"))
    print("=" * 86)

if __name__ == "__main__":
    main()

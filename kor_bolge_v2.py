#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
kor_bolge_v2.py  --  delta* DISLAMA SINIRLARI icin GECERLILIK KAPISI (mu'yu KENDI olcer)

NEDEN BU ARAC (2026-10-31):
  Eberwein (Zenodo 23177438, 5-6 Ekim 2026) Teorem 7.1:

     W_{Z0}(f) >= mu ||f||^2  ise, her T yuksekligi icin
     W_{Z0 u Q}(f) >= (mu - kappa(d,L)) ||f||^2,
     kappa(d,L) = 2 sinh(dL)/d - 2L = d^2 L^3/3 + O(d^4 L^5)

  d_0 = kappa^{-1}(mu) ~ sqrt(3 mu / L^3) olmak uzere: derinligi d < d_0 olan
  HER cizgi-disi dordul, HER yukseklikte pencereyi POZITIF birakir. Yani o
  derinlik DISLANAMAZ. Bu, delta* dislama sinirlarimiz icin bir TAVAN'dir.

v1 -> v2 (ONEMLI DUZELTME):
  v1'de mu ELLE veriliyordu ve sabit (3e-41) alinmisti. YANLIS: mu her eta icin
  FARKLIDIR ve optimizasyon delta*'i dusururken mu'yu de dusurur:
      TW theta=0 : mu = 1.36e-40
      TW optimum : mu = 1.34e-43
      FREE1      : mu = 3.54e-46
  d_0 ~ sqrt(mu) oldugundan tavan da birlikte iner ve PAY KORUNUR.
  v1 bu yuzden FREE1'i yanlislikla "kor bolge" ilan etti; gercek mu ile GECERLI
  (pay 10.2). v2 mu'yu kendi olcer, elle girilmez.

KAPILAR:
  KAPI-KAPPA  : kappa(d,L) tam formu ile d^2L^3/3 yaklasimi kucuk d'de ayni
  KAPI-MONO   : kappa d'de kesin artan (d_0 tek anlamli)
  KAPI-SESSIZ : her eta bant ici gercekten sessiz (|F(gamma_j)| taban altinda)
  KAPI-GECER  : her aday icin delta* > d_0 mi
  KAPI-NEG    : mu -> 0 limitinde d_0 -> 0 (kapi mu'ye gercekten bagli)

KULLANIM:
  python -u kor_bolge_v2.py
  python -u kor_bolge_v2.py --q 13 --Om 75.5524 --N 18 --d 21 --K 88
  python -u kor_bolge_v2.py --adim 26        (FREE1 tarama inceligi)
"""
import argparse, hashlib, os, time
import mpmath as mp

SURUM = "kor_bolge_v2.py  v2.0"

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

def ln_(m): return mp.sqrt((2 * mp.mpf(m) + 1) / 2)
def sph_j(m, z): return mp.sqrt(mp.pi / (2 * z)) * mp.besselj(m + mp.mpf(1) / 2, z)
def sph_i(m, a): return mp.sqrt(mp.pi / (2 * a)) * mp.besseli(m + mp.mpf(1) / 2, a)

def kappa(x, L):
    x = mp.mpf(x); L = mp.mpf(L)
    if x == 0: return mp.mpf(0)
    return 2 * mp.sinh(x * L) / x - 2 * L

def d_sifir(mu, L):
    """kappa(d,L) = mu cozumu."""
    mu = mp.mpf(mu); L = mp.mpf(L)
    if mu <= 0: return mp.mpf(0)
    tah = mp.sqrt(3 * mu / L ** 3)
    try: return mp.findroot(lambda x: kappa(x, L) - mu, tah)
    except Exception: return tah

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--q", type=int, default=13)
    ap.add_argument("--Om", default="75.5524")
    ap.add_argument("--N", type=int, default=18)
    ap.add_argument("--d", type=int, default=21)
    ap.add_argument("--K", type=int, default=88)
    ap.add_argument("--dps", type=int, default=50)
    ap.add_argument("--adim", type=int, default=26)
    a = ap.parse_args()
    mp.mp.dps = a.dps
    Q = a.q; Om = mp.mpf(a.Om); N = a.N; d = a.d; K = a.K
    h = mp.log(Q) / 2; c = Om * h; L = mp.log(Q)

    print("=" * 88)
    print(SURUM + "   md5=" + _md5() + "   mpmath " + mp.__version__)
    print("=" * 88)
    print("""ON-KAYIT (kosumdan ONCE):
  TAVAN  : Eberwein Thm 7.1 -- derinligi d_0 = kappa^{-1}(mu) altindaki her
     cizgi-disi dordul pencereyi POZITIF birakir, yani DISLANAMAZ.
  KAPI   : delta* > d_0  ->  dislama GECERLI ;  delta* < d_0  ->  KOR BOLGE.
  mu     : ELLE VERILMEZ, her eta icin OLCULUR (v1'in hatasi buydu).
           mu(eta) = 2 F_eta(gamma_{N+1})^2  = bant-disi ilk sifir payi (slack)
  BEKLENTI: her uc aday da GECERLI; pay TW theta=0 > TW optimum > FREE1
     (optimizasyon derinlestikce tavana yaklasilir).
  SINIR  : mu normalizasyonu Eberwein'inkiyle ayni olmayabilir -- MERTEBE testi.
     Kesin hukum icin iki tarafin ayni olcekte olmasi gerekir.
""")
    print("q=%d  Om=%s  N=%d  d=%d  K=%d  L=ln q=%s  h=L/2=%s\n" % (
        Q, a.Om, N, d, K, mp.nstr(L, 10), mp.nstr(h, 10)))
    t0 = time.time()

    V = prolate_even(c, K, d); sh = mp.sqrt(h)
    V = [[x / sh for x in v] for v in V]
    gam = [mp.im(mp.zetazero(k)) for k in range(1, N + 3)]

    def Fvec(g):
        fb = [h * ln_(2 * i) * 2 * (-1) ** i * sph_j(2 * i, g * h) for i in range(K)]
        return [mp.fsum(v[i] * fb[i] for i in range(K)) for v in V]
    Pp = [mp.fsum(v[i] * (h * ln_(2 * i) * 2 * sph_i(2 * i, h / 2)) for i in range(K))
          for v in V]
    Fg = [Fvec(gam[j]) for j in range(N + 1)]
    def dot(x, y): return mp.fsum(p * q for p, q in zip(x, y))

    def cekirdek(serbest):
        rows = [Fg[j] for j in range(N) if j not in serbest] + [Pp]
        A = mp.matrix(rows); U_, S_, Vt = mp.svd_r(A, full_matrices=True)
        r = len(rows)
        return [[Vt[j, i] for i in range(d)] for j in range(r, d)]

    eps = mp.mpf("1e-10")
    def olc(e, serbest):
        nn = mp.sqrt(dot(e, e))
        if nn == 0: return None
        e = [x / nn for x in e]
        mu = 2 * dot(Fg[N], e) ** 2                  # SLACK = bant-disi pay
        g = gam[0]; F0 = dot(Fg[0], e)
        Fp = (dot(Fvec(g + eps), e) - dot(Fvec(g - eps), e)) / (2 * eps)
        Fpp = (dot(Fvec(g + eps), e) - 2 * F0 + dot(Fvec(g - eps), e)) / (eps * eps)
        S = 2 * (Fp * Fp - F0 * Fpp)
        if S <= 0: return None
        sess = max(abs(dot(Fg[j], e)) for j in range(N) if j not in serbest)
        return mu, mp.sqrt(mu / S), sess, e

    def ara(B, st, serbest):
        M = len(B); en = None
        if M == 2:
            for k in range(st):
                th = mp.pi * k / (st - 1)
                e = [mp.cos(th) * B[0][i] + mp.sin(th) * B[1][i] for i in range(d)]
                r = olc(e, serbest)
                if r and (en is None or r[1] < en[1]): en = r
        else:
            def gen(m):
                if m == 1: yield [mp.mpf(1)]
                else:
                    for q in range(st):
                        t = mp.pi * q / (st - 1)
                        for rest in gen(m - 1): yield [mp.cos(t)] + [mp.sin(t) * x for x in rest]
            for co in gen(M):
                e = [mp.fsum(co[j] * B[j][i] for j in range(M)) for i in range(d)]
                r = olc(e, serbest)
                if r and (en is None or r[1] < en[1]): en = r
        return en

    # --- alet kapilari ---
    x = mp.mpf("1e-10")
    kk = abs(kappa(x, L) / (x * x * L ** 3 / 3) - 1)
    print("KAPI-KAPPA  tam/yaklasik oran-1 = %s  -> %s" % (
        mp.nstr(kk, 6), "GECTI" if kk < mp.mpf("1e-12") else "DUSTU"))
    xs = [mp.mpf(10) ** (-k) for k in range(1, 12)]
    vs = [kappa(t, L) for t in xs]
    km = all(vs[i] > vs[i + 1] for i in range(len(vs) - 1))
    print("KAPI-MONO   kappa d'de kesin artan  -> %s" % ("GECTI" if km else "DUSTU"))
    kn = (d_sifir(0, L) == 0)
    print("KAPI-NEG    mu=0 -> d_0=0  -> %s\n" % ("GECTI" if kn else "DUSTU (KABUK)"))

    # --- adaylar ---
    B0 = cekirdek(set()); B1 = cekirdek({0})
    adaylar = []
    r = olc(B0[0], set())
    if r: adaylar.append(("TW theta=0", r, set()))
    r = ara(B0, 181, set())
    if r: adaylar.append(("TW optimum", r, set()))
    r = ara(B1, a.adim, {0})
    if r: adaylar.append(("FREE1 optimum", r, {0}))

    print("%-16s %-13s %-13s %-13s %-9s %-11s %s" % (
        "eta", "mu (olculen)", "delta*", "d_0 (tavan)", "pay", "sessizlik", "hukum"))
    gecen = 0; ksess = True
    for ad, (mu, ds, sess, e), serbest in adaylar:
        dd = d_sifir(mu, L)
        pay = ds / dd if dd > 0 else mp.inf
        ok = ds > dd
        if ok: gecen += 1
        if sess > mp.mpf("1e-30"): ksess = False
        print("%-16s %-13s %-13s %-13s %-9s %-11s %s" % (
            ad, mp.nstr(mu, 5), mp.nstr(ds, 6), mp.nstr(dd, 6), mp.nstr(pay, 5),
            mp.nstr(sess, 3), "GECERLI" if ok else "KOR BOLGE"))

    print("\nKAPI-SESSIZ bant ici en buyuk |F| < 1e-30  -> %s" % (
        "GECTI" if ksess else "DUSTU"))
    print("KAPI-GECER  %d / %d aday gecerli  -> %s" % (
        gecen, len(adaylar), "GECTI" if gecen == len(adaylar) else "DIKKAT"))
    print("\n[%.0f s]" % (time.time() - t0))
    print("""
OKUMA:
  GECERLI  = delta* kor bolgenin USTUNDE; dislama Thm 7.1 ile celismiyor.
  KOR BOLGE= o derinlikte bir sapma pencereyi pozitif birakir; dislama kurulamaz.
  PAY dusuyorsa optimizasyon tavana yaklasiyor demektir -- nerede durulacagi
  bu sayidan okunur.""")

if __name__ == "__main__":
    main()

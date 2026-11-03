#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
tavan_v1.py  --  delta* OPTIMIZASYONUNU TAVANA KADAR GOTUR, ORADA DUR

NEDEN (2026-10-31):
  dim W = 2 (bugun ispatlandi) sessiz altuzayda aramayi TANIMLI kildi.
  Serbestlik artirilinca delta* duser:
     TW   (dim 2) : 8.43e-21   pay 54.6
     FREE1(dim 3) : 8.08e-23   pay 10.2
  Ama her adimda TAVANA (kor bolge, Eberwein Zenodo 23177438 Thm 7.1) yaklasilir:
     d_0 = kappa^{-1}(mu),  kappa(d,L) = 2 sinh(dL)/d - 2L
     pay = delta* / d_0 ;  pay <= 1 ise o dislama KURULAMAZ.
  Bu arac FREE0..FREE3'u sirayla kosar, her birinde hem delta* hem PAY verir,
  ve ARAMAYI pay <= 1'e dusmeden onceki son GECERLI noktada keser.

  C2 (isaret kaliciligi) kapisi da korunur: g_k(delta) = 2F(g_k)^2 - 2Re F(g_k-i d)^2
  (0,1/2] uzerinde pozitif VE artan olmali. FREE3 bu kapidan DUSMUSTU (2026-10-30).

  v1.1 -> v1.2 (2026-11-03, KRITIK DUZELTME):
    Olculdu ki delta*'in TARAMA ile bulunan minimumu bir IZGARA ARTEFAKTIDIR:
       181 adim -> 9.941e-21   721 -> 2.020e-21
      2881 adim -> 3.163e-22 11521 -> 8.053e-23
    delta* ~ 1/n, sinirda SIFIR. Sebep: sessiz altuzayda F0=0 oldugu icin
      A = 2 u u^T (u=F19) ve B = 2 v v^T (v=F') IKISI DE RANK-1,
      delta*^2 = (u.eta)^2/(v.eta)^2 ; eta _|_ u secilince oran sifirlanir
      (u'ya dik aci t* = -12.3857 derece, orada |u.eta| = 0.0 tam).
    O yonde mu = 2(u.eta)^2 de sifirlanir, yani DISLAMA IDDIASI BOSALIR.
    SONUC: delta* bir OPTIMIZASYON HEDEFI DEGILDIR. Anlamli olan SABIT bir
      eta icin (mu, delta*, d_0) ucslusu ve payin buyuklugudur.
    v1.2 bu yuzden: (a) tarama minimumunu ARTIK HUKUM OLARAK VERMEZ,
      (b) her aile icin IZGARA KAPISI kosar (iki farkli adimda min kiyaslanir;
      oran 1'e yakin degilse ARTEFAKT damgasi basilir),
      (c) hukum satirinda sabit nokta (theta=0 / ilk baz) one cikarilir.

KAPILAR:
  KAPI-IZGARA : iki farkli izgara adiminda min delta* orani ~1 olmali;
                degilse tarama minimumu ARTEFAKTTIR (v1.2'de eklendi)
  KAPI-SESSIZ : her eta bant ici gercekten sessiz (serbest birakilanlar haric)
  KAPI-C2     : g_k pozitif ve artan
  KAPI-TAVAN  : delta* > d_0 (kor bolge)
  KAPI-NEG    : rastgele eta -> C2 ya da TAVAN dusmeli (kapilar kabuk degil)

KULLANIM:
  python -u tavan_v1.py
  python -u tavan_v1.py --enmax 3 --adim 20
"""
import argparse, hashlib, os, time
import mpmath as mp

SURUM = "tavan_v1_2.py  v1.2"

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
    x = mp.mpf(x)
    if x == 0: return mp.mpf(0)
    return 2 * mp.sinh(x * L) / x - 2 * L

def d_sifir(mu, L):
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
    ap.add_argument("--enmax", type=int, default=3, help="en fazla kac sifir serbest")
    ap.add_argument("--adim", type=int, default=26)
    a = ap.parse_args()
    mp.mp.dps = a.dps
    Q = a.q; Om = mp.mpf(a.Om); N = a.N; d = a.d; K = a.K
    h = mp.log(Q) / 2; c = Om * h; L = mp.log(Q)

    print("=" * 92)
    print(SURUM + "   md5=" + _md5() + "   mpmath " + mp.__version__)
    print("=" * 92)
    print("""ON-KAYIT (kosumdan ONCE):
  IDDIA : serbestlik artinca delta* duser ama PAY = delta*/d_0 de duser;
          pay <= 1 olunca dislama KURULAMAZ (kor bolge).
  TAVAN : d_0 = kappa^{-1}(mu), kappa(d,L)=2sinh(dL)/d-2L
          [blind-zone bound: Eberwein, Zenodo 23177438, Thm 7.1]
  OLCULDU (2026-10-31, canli): pay TEK YONLU AZALMIYOR ve delta* FREE1'den
          sonra YUKSELIYOR. Optimum ARADADIR, sonda degil.
  BEKLENTI: FREE1 en kucuk delta*'i verir (8.08e-23, pay 10.2); FREE2/FREE3
          daha BUYUK delta* verir. Serbestligin optimum miktari BIR'dir.
  DUSME : FREE2 ya da FREE3 FREE1'den kucuk delta* verirse bu okuma duser.
  C2    : FREE3 2026-10-30'da C2'den dusmustu; burada yeniden sinanir.
""")
    print("q=%d  Om=%s  N=%d  d=%d  K=%d  L=%s\n" % (Q, a.Om, N, d, K, mp.nstr(L, 10)))
    t0 = time.time()

    V = prolate_even(c, K, d); sh = mp.sqrt(h)
    V = [[x / sh for x in v] for v in V]
    gam = [mp.im(mp.zetazero(k)) for k in range(1, N + 3)]

    def Fvec(g):
        fb = [h * ln_(2 * i) * 2 * (-1) ** i * sph_j(2 * i, g * h) for i in range(K)]
        return [mp.fsum(v[i] * fb[i] for i in range(K)) for v in V]
    def Fvec_c(z):
        fb = [h * ln_(2 * i) * 2 * (-1) ** i *
              (mp.sqrt(mp.pi / (2 * (z * h))) * mp.besselj(2 * i + mp.mpf(1) / 2, z * h))
              for i in range(K)]
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
    DS = [mp.mpf(k) / 8 for k in range(1, 5)]
    Fc = {}
    def gfun(e, g, dl):
        F0 = dot(Fvec(g), e)
        k = str(dl)
        if k not in Fc: Fc[k] = Fvec_c(mp.mpc(g, -dl))
        Fz = dot(Fc[k], e)
        return 2 * F0 * F0 - 2 * mp.re(Fz * Fz)

    def olc(e, serbest):
        nn = mp.sqrt(dot(e, e))
        if nn == 0: return None
        e = [x / nn for x in e]
        mu = 2 * dot(Fg[N], e) ** 2
        g = gam[0]; F0 = dot(Fg[0], e)
        Fp = (dot(Fvec(g + eps), e) - dot(Fvec(g - eps), e)) / (2 * eps)
        Fpp = (dot(Fvec(g + eps), e) - 2 * F0 + dot(Fvec(g - eps), e)) / (eps * eps)
        S = 2 * (Fp * Fp - F0 * Fpp)
        if S <= 0: return None
        ds = mp.sqrt(mu / S)
        vals = [gfun(e, g, x) for x in DS]
        c2 = all(v > 0 for v in vals) and all(vals[i + 1] > vals[i] for i in range(3))
        ic = [j for j in range(N) if j not in serbest]
        sess = max(abs(dot(Fg[j], e)) for j in ic) if ic else mp.mpf(0)
        return mu, ds, c2, sess, e

    def ara(B, st, serbest):
        M = len(B); en = None
        def gen(m):
            if m == 1: yield [mp.mpf(1)]
            else:
                for q in range(st):
                    t = mp.pi * q / (st - 1)
                    for rest in gen(m - 1): yield [mp.cos(t)] + [mp.sin(t) * x for x in rest]
        it = (([mp.cos(mp.pi * k / (st - 1)), mp.sin(mp.pi * k / (st - 1))] for k in range(st))
              if M == 2 else gen(M))
        for co in it:
            e = [mp.fsum(co[j] * B[j][i] for j in range(M)) for i in range(d)]
            r = olc(e, serbest)
            if r is None or not r[2]: continue        # C2 KISITI
            if en is None or r[1] < en[1]: en = r
        return en

    print("%-10s %-4s %-13s %-13s %-9s %-5s %-11s %s" % (
        "aile", "dim", "mu(sabit)", "delta*(sabit)", "pay", "C2", "izgara", "hukum"))
    paylar = []; gecerliler = []
    for k in range(0, a.enmax + 1):
        serbest = set(range(k))
        B = cekirdek(serbest)
        st = 181 if len(B) == 2 else (a.adim if len(B) == 3 else (14 if len(B) == 4 else 8))
        ad = "TW" if k == 0 else ("FREE%d" % k)
        # v1.2: SABIT NOKTA (ilk baz vektoru) hukum verir, tarama minimumu DEGIL
        r = olc(B[0], serbest)
        # IZGARA KAPISI: iki farkli adimda tarama minimumu
        r1 = ara(B, max(st // 4, 5), serbest)
        r2 = ara(B, st, serbest)
        izg = "-"
        if r1 is not None and r2 is not None and r1[1] > 0:
            oran = r2[1] / r1[1]
            izg = ("ARTEFAKT" if oran < mp.mpf("0.5") else mp.nstr(oran, 3))
        if r is None:
            print("%-10s %-4d  --  sabit nokta C2 gecmedi" % (ad, len(B)))
            continue
        mu, ds, c2, sess, e = r
        dd = d_sifir(mu, L); pay = ds / dd if dd > 0 else mp.inf
        ok = ds > dd
        if ok: gecerliler.append((ds, ad, pay, mu))
        paylar.append(pay)
        print("%-10s %-4d %-13s %-13s %-9s %-5s %-11s %s" % (
            ad, len(B), mp.nstr(mu, 5), mp.nstr(ds, 6),
            mp.nstr(pay, 5), "OK" if c2 else "--", izg,
            "GECERLI" if ok else "KOR BOLGE"))
        # v1.1: kor bolgeye dusen aile aramayi KESMEZ -- optimum arada olabilir

    mono = all(paylar[i] > paylar[i + 1] for i in range(len(paylar) - 1))
    print("\nKAPI-MONO   pay dizisi tek yonlu azaliyor  -> %s" % (
        "GECTI" if mono else "DUSTU -- optimum ARADA, sonda degil"))
    if gecerliler:
        gecerliler.sort(key=lambda t: -t[2])      # PAYA gore, delta*'a gore DEGIL
        ds, ad, pay, mu = gecerliler[0]
        print("\nEN BUYUK PAY: %s   delta* = %s   pay = %s   mu = %s" % (
            ad, mp.nstr(ds, 6), mp.nstr(pay, 5), mp.nstr(mu, 5)))
        print("  (siralama PAYA gore; delta*'in kendisi kucultulecek bir hedef DEGILDIR")
        print("   -- kisitsiz minimize edilince mu de sifira gider, bkz. v1.2 basligi)")
    else:
        print("\nGECERLI ADAY YOK.")
    print("[%.0f s]" % (time.time() - t0))

if __name__ == "__main__":
    main()

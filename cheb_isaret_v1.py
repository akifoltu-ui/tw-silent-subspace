#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
cheb_isaret_v1.py  --  phi_i(w) ailesi bir CHEBYSHEV (Haar) sistemi mi?

ZINCIRDE NEREDE:
  cheb_indirge_v1.py, L'nin Bessel'li kurulumundan saf prolate degerlerine
  gecisi kurdu (iki hucrede dort kapi):
      rank L = rank Psi,   Psi[j,i] = psi_{2i}(s_j) = phi_i(w_j),  w = s^2.
  Noktalar tek bir REEL eksende toplanir: ornekleme w in (0,1), kutup w<0.
  Bu arac bir sonraki halkayi olcer.

HIPOTEZ (kosumdan ONCE ilan):
  {phi_0,...,phi_{d-1}} ailesi (-eps, 1) araliginda bir CHEBYSHEV (Haar)
  sistemidir: herhangi d FARKLI nokta icin det[phi_i(w_j)] sifirdan farklidir
  ve ISARETI noktalarin siralamasina gore sabittir (artan siralamada hep ayni).
  DOGRUYSA: rank L = N+1 her Omega ve her N icin TEOREM olur; hucre hucre
  sertifika gerekmez.

BU NICELIK NEYIN OZELLIGI:
  det[phi_i(w_j)] nesnenin ozelligidir (prolate ailesi + nokta kumesi).
  Aletin izi: Legendre kesimi K ve calisma hassasiyeti dps. Her ikisi de
  taranir; hukum yalniz K'den BAGIMSIZ olan kisim icin kurulur.

KAPILAR:
  KAPI-ISARET : butun rastgele kumelerde artan siralamada ayni isaret
  KAPI-TABAN  : ayni kume iki HASSASIYETTE ayni olcekli det'i veriyor
                (Hadamard orani d ile ustel kuculur; mutlak esik anlamsiz,
                 anlamli olan sayinin hassasiyetten BAGIMSIZ olmasidir)
  KAPI-K      : K degistiginde isaret ve mertebe degismiyor
  KAPI-NEG    : bir nokta TEKRAR edilirse det sifirlanmali (arac kabuk degil)

KULLANIM:
  python -u cheb_isaret_v1.py                      # A hucresi, 200 kume
  python -u cheb_isaret_v1.py --cell B --kume 300
  python -u cheb_isaret_v1.py --K 88,120 --dps 80
"""
import argparse, hashlib, os, time, random
import mpmath as mp

SURUM = "cheb_isaret_v1.py  v1.0"
CELLS = {"A": dict(Omega="75.5524", d=21), "B": dict(Omega="103.7255", d=33)}
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

def ln_(m): return mp.sqrt((2 * mp.mpf(m) + 1) / 2)

def phi_matris(V, K, ws):
    """Psi[j,i] = phi_i(w_j) = psi_{2i}(sqrt(w_j)); w<0 icin s saf sanal."""
    d = len(V); n = len(ws)
    M = mp.zeros(n, d)
    for j, w in enumerate(ws):
        s = mp.sqrt(mp.mpf(w)) if w >= 0 else mp.mpc(0, 1) * mp.sqrt(-mp.mpf(w))
        P = [mp.legendre(2 * i, s) for i in range(K)]
        for col, v in enumerate(V):
            M[j, col] = mp.re(mp.fsum(v[i] * ln_(2 * i) * P[i] for i in range(K)))
    return M

def olcekli_det(M, d):
    """det / (satir normlarinin carpimi) -- Hadamard olcekli, tabanla kiyas icin."""
    D = mp.det(M)
    pay = mp.mpf(1)
    for j in range(d):
        pay *= mp.sqrt(mp.fsum(M[j, i] ** 2 for i in range(d)))
    return D, (D / pay if pay != 0 else mp.mpf(0))

def tara(name, d, Om, K, dps, kume, eps, tohum):
    mp.mp.dps = dps
    h = mp.log(Q) / 2; c = Om * h
    V = prolate_even(c, K, d)
    rnd = random.Random(tohum)
    isaretler = set(); en_kucuk = None; ilk = None
    for t in range(kume):
        ws = sorted(rnd.uniform(-eps, 0.98) for _ in range(d))
        if min(ws[i + 1] - ws[i] for i in range(d - 1)) < 1e-4:
            continue
        M = phi_matris(V, K, ws)
        D, o = olcekli_det(M, d)
        if D == 0:
            isaretler.add(0)
        else:
            isaretler.add(1 if D > 0 else -1)
        ao = abs(o)
        if en_kucuk is None or ao < en_kucuk: en_kucuk = ao
        if ilk is None: ilk = (ws, M)
    return isaretler, en_kucuk, ilk

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cell", default="A", choices=["A", "B"])
    ap.add_argument("--K", default="88,120")
    ap.add_argument("--dps", type=int, default=70)
    ap.add_argument("--kume", type=int, default=200)
    ap.add_argument("--eps", type=float, default=0.01)
    ap.add_argument("--tohum", type=int, default=20261029)
    a = ap.parse_args()
    Ks = [int(x) for x in a.K.split(",")]

    print("=" * 84)
    print(SURUM + "   md5=" + _md5() + "   mpmath " + mp.__version__)
    print("=" * 84)
    print("""ON-KAYIT (kosumdan ONCE):
  HIPOTEZ: {phi_0..phi_{d-1}} (-eps,1) araliginda Chebyshev sistemi; ARTAN
    siralanmis d farkli nokta icin det[phi_i(w_j)] hep AYNI isarete sahip.
  BEKLENTI: butun kumelerde tek isaret; olcekli |det| tabanin cok ustunde;
    K degisince isaret degismiyor; nokta tekrarinda det sifirlaniyor.
  SINIR: bu arac Chebyshev ozelligini KANITLAMAZ. Tek isaret gozlemi, ispatin
    aranacagini soyler (Sturm-Liouville osilasyon teorisi); tek karsi ornek
    hipotezi dusurur.
""")
    cell = CELLS[a.cell]; d = cell["d"]; Om = mp.mpf(cell["Omega"])
    print("[%s] Omega=%s  d=%d  kume=%d  w in (-%.3f, 0.98)  dps=%d  tohum=%d\n" % (
        a.cell, mp.nstr(Om, 10), d, a.kume, a.eps, a.dps, a.tohum))

    sonuc = {}
    for K in Ks:
        t0 = time.time()
        isar, enk, ilk = tara(a.cell, d, Om, K, a.dps, a.kume, a.eps, a.tohum)
        sonuc[K] = (isar, enk)
        iy = sorted(isar)
        print("[%s] K=%3d  isaret kumesi = %s   en kucuk olcekli |det| = %s   [%.0f s]" % (
            a.cell, K, iy, mp.nstr(enk, 6), time.time() - t0))

    k_isaret = all(len(sonuc[K][0]) == 1 and 0 not in sonuc[K][0] for K in Ks)
    print("\n[%s] KAPI-ISARET  butun kumelerde tek isaret  -> %s" % (
        a.cell, "GECTI" if k_isaret else "DUSTU"))

    # KAPI-TABAN: ayni kumeyi iki hassasiyette hesapla, olcekli det ayni mi
    def tek_det(dps, K):
        mp.mp.dps = dps
        VV = prolate_even(Om * (mp.log(Q) / 2), K, d)
        r = random.Random(a.tohum)
        w = sorted(r.uniform(-a.eps, 0.98) for _ in range(d))
        return olcekli_det(phi_matris(VV, K, w), d)[1]
    o1 = tek_det(a.dps, Ks[0])
    o2 = tek_det(a.dps + 30, Ks[0])
    bagil = abs(o2 / o1 - 1) if o1 != 0 else mp.inf
    k_taban = bagil < mp.mpf("1e-12")
    print("[%s] KAPI-TABAN   dps %d vs %d: olcekli det bagil farki = %s  -> %s" % (
        a.cell, a.dps, a.dps + 30, mp.nstr(bagil, 6),
        "GECTI" if k_taban else "DUSTU"))

    k_K = len(set(tuple(sorted(sonuc[K][0])) for K in Ks)) == 1
    print("[%s] KAPI-K       isaret K'den bagimsiz (%s)  -> %s" % (
        a.cell, ",".join(str(k) for k in Ks), "GECTI" if k_K else "DUSTU"))

    # KAPI-NEG: bir noktayi TEKRAR et -> det sifirlanmali
    mp.mp.dps = a.dps
    h = mp.log(Q) / 2; V = prolate_even(Om * h, Ks[0], d)
    rnd = random.Random(a.tohum)
    ws = sorted(rnd.uniform(-a.eps, 0.98) for _ in range(d))
    ws[1] = ws[0]                                   # tekrar
    M = phi_matris(V, Ks[0], ws)
    D, o = olcekli_det(M, d)
    k_neg = abs(o) < mp.mpf(10) ** (-a.dps + 20)
    print("[%s] KAPI-NEG     nokta tekrari -> olcekli |det| = %s  -> %s" % (
        a.cell, mp.nstr(abs(o), 6),
        "GECTI (sifirlandi)" if k_neg else "DUSTU (ARAC KABUK)"))

    hep = k_isaret and k_taban and k_K and k_neg
    print("\n" + "=" * 84)
    print("SONUC: %s" % ("HEPSI GECTI -- Chebyshev hipotezi AYAKTA" if hep
                         else "EN AZ BIRI DUSTU"))
    print("=" * 84)

if __name__ == "__main__":
    main()

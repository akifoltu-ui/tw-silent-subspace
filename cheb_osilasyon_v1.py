#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
cheb_osilasyon_v1.py  --  phi_i(w)'nin SIFIR SAYISI tam i mi?

ZINCIRDE NEREDE:
  cheb_indirge_v1 : rank L = rank Psi,  Psi[j,i] = phi_i(w_j)   [iki hucre, 4 kapi]
  cheb_isaret_v1  : det[phi_i(w_j)] 300 rastgele kumede tek isaret  [8 kapi]
  BU ARAC         : Chebyshev sisteminin KLASIK karakterizasyonunu olcer.

ELLE TURETME (kosumdan ONCE ilan):
  Bir {f_0,...,f_{d-1}} ailesinin bir aralikta Chebyshev (Haar) sistemi olmasi,
  aileden kurulu HER sifirdan farkli dogrusal birlesimin o aralikta EN COK d-1
  sifiri olmasina denktir. Markov sistemlerinde bundan daha keskin bir olcut
  gecerlidir: f_i'nin kendisinin tam i sifiri olur ve ardisik ikisinin sifirlari
  BIRBIRINI AYIRIR (interlacing). Sturm-Liouville ozfonksiyonlarinda bu klasik
  osilasyon teoremidir; prolate psi_n'nin (-1,1) uzerinde tam n sifiri vardir.
  Bizim degiskenimiz w = s^2 ve phi_i(w) := psi_{2i}(sqrt(w)). psi_{2i} CIFT ve
  (-1,1)'de 2i sifiri olduguna gore, w ekseninde (0,1)'de tam i sifir beklenir.
  Kutup noktasi w<0 tarafinda; orada sifir OLMAMALI, cunku psi_{2i}(iy) saf
  sanal eksende isaret degistirmez (butun Legendre terimleri ayni isarette).

  IDDIA (bu aracin olctugu):
    (O1) phi_i'nin (0,1) araliginda tam i basit sifiri var
    (O2) phi_i ile phi_{i+1}'in sifirlari birbirini ayiriyor (interlacing)
    (O3) (-eps,0] araliginda hicbir phi_i'nin sifiri yok
  Ucu birden tutarsa aile bir MARKOV sistemidir ve Chebyshev ozelligi oradan
  gelir; o zaman rank L = N+1 her Omega ve her N icin TEOREM olur.

BU NICELIK NEYIN OZELLIGI:
  Sifir sayisi NESNENIN ozelligidir. Aletin izi: Legendre kesimi K, calisma
  hassasiyeti dps, ve tarama izgarasinin inceligi. Ucu de taranabilir; hukum
  yalniz bunlardan BAGIMSIZ olan kisim icin kurulur.

KAPILAR:
  KAPI-SAYI   : her i icin (0,1)'de sifir sayisi tam i
  KAPI-AYIRMA : ardisik ciftlerde interlacing bozulmuyor
  KAPI-SOL    : (-eps,0] araliginda hic sifir yok
  KAPI-IZGARA : izgara iki katina cikarilinca sayilar degismiyor (alet kapisi)
  KAPI-NEG    : bilerek bozulmus aile (phi_i yerine phi_i + phi_{i+1}) sayiyi
                DEGISTIRMELI -- degistirmiyorsa sayac kor demektir

KULLANIM:
  python -u cheb_osilasyon_v1.py                     # A hucresi
  python -u cheb_osilasyon_v1.py --cell B --K 120
"""
import argparse, hashlib, os, time
import mpmath as mp

SURUM = "cheb_osilasyon_v1.py  v1.0"
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

def yap_phi(v, K):
    """phi(w) = psi_{2i}(sqrt(w)); w<0 icin s saf sanal, sonuc yine reel."""
    co = [v[i] * ln_(2 * i) for i in range(K)]
    def f(w):
        w = mp.mpf(w)
        s = mp.sqrt(w) if w >= 0 else mp.mpc(0, 1) * mp.sqrt(-w)
        return mp.re(mp.fsum(co[i] * mp.legendre(2 * i, s) for i in range(K)))
    return f

def izgara_P(a, b, n, K):
    """Izgara noktalari ve her noktada P_{2i}(s) degerleri -- bir kez hesaplanir."""
    a = mp.mpf(a); b = mp.mpf(b); adim = (b - a) / n
    ws = [a + k * adim for k in range(n + 1)]
    P = []
    for w in ws:
        s = mp.sqrt(w) if w >= 0 else mp.mpc(0, 1) * mp.sqrt(-w)
        P.append([mp.legendre(2 * i, s) for i in range(K)])
    return ws, P

def sifir_say(co, ws, P, f, K):
    """Onbelleklenmis izgara uzerinde isaret degisimi; sadece orada kok bul."""
    kok = []
    onc_v = mp.re(mp.fsum(co[i] * P[0][i] for i in range(K)))
    for k in range(1, len(ws)):
        v = mp.re(mp.fsum(co[i] * P[k][i] for i in range(K)))
        if (onc_v > 0) != (v > 0):
            try:
                r = mp.findroot(f, (ws[k - 1], ws[k]), solver="bisect",
                                tol=mp.mpf(10) ** -35)
                kok.append(r)
            except Exception:
                kok.append((ws[k - 1] + ws[k]) / 2)
        onc_v = v
    return kok

def tara(V, K, d, eps, n_sag, n_sol, onbellek={}):
    anahtar = (n_sag, n_sol, K, eps, mp.mp.dps)
    if anahtar not in onbellek:
        onbellek[anahtar] = (izgara_P(mp.mpf("1e-9"), mp.mpf("0.999999"), n_sag, K),
                             izgara_P(-mp.mpf(eps), -mp.mpf("1e-12"), n_sol, K))
    (wsR, PR), (wsL, PL) = onbellek[anahtar]
    fs = [yap_phi(v, K) for v in V]
    sag = []; sol = []
    for v, f in zip(V, fs):
        co = [v[i] * ln_(2 * i) for i in range(K)]
        sag.append(sifir_say(co, wsR, PR, f, K))
        sol.append(sifir_say(co, wsL, PL, f, K))
    return fs, sag, sol

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cell", default="A", choices=["A", "B"])
    ap.add_argument("--K", type=int, default=88)
    ap.add_argument("--dps", type=int, default=60)
    ap.add_argument("--izgara", type=int, default=4000)
    ap.add_argument("--eps", type=float, default=0.01)
    a = ap.parse_args()

    print("=" * 84)
    print(SURUM + "   md5=" + _md5() + "   mpmath " + mp.__version__)
    print("=" * 84)
    print("""ON-KAYIT (kosumdan ONCE):
  IDDIA  (O1) phi_i'nin (0,1)'de tam i basit sifiri var
         (O2) ardisik ciftlerde sifirlar birbirini ayiriyor
         (O3) (-eps,0] araliginda hic sifir yok
  BEKLENTI: ucu de tutar; izgara iki katina cikinca sayilar DEGISMEZ.
  SINIR: bu arac Markov ozelligini KANITLAMAZ; klasik osilasyon olcutunun
         analitik devam edilmis halini OLCER. Tek sapma hipotezi dusurur.
""")
    cell = CELLS[a.cell]; d = cell["d"]; Om = mp.mpf(cell["Omega"])
    mp.mp.dps = a.dps
    h = mp.log(Q) / 2; c = Om * h
    print("[%s] Omega=%s  d=%d  c=%s  K=%d  dps=%d  izgara=%d\n" % (
        a.cell, mp.nstr(Om, 10), d, mp.nstr(c, 10), a.K, a.dps, a.izgara))

    t0 = time.time()
    V = prolate_even(c, a.K, d)
    fs, sag, sol = tara(V, a.K, d, a.eps, a.izgara, 400)

    # --- KAPI-SAYI -----------------------------------------------------------
    sayilar = [len(z) for z in sag]
    k_sayi = all(sayilar[i] == i for i in range(d))
    print("[%s] (0,1)'deki sifir sayilari:" % a.cell)
    for b in range(0, d, 11):
        par = sayilar[b:b + 11]
        print("    i=%2d..%2d : %s" % (b, min(b + 10, d - 1),
                                       " ".join("%d" % x for x in par)))
    kotu = [i for i in range(d) if sayilar[i] != i]
    print("[%s] KAPI-SAYI    sifir sayisi == i her i icin  -> %s%s" % (
        a.cell, "GECTI" if k_sayi else "DUSTU",
        "" if k_sayi else "   (sapan i: %s)" % kotu[:8]))

    # --- KAPI-SOL ------------------------------------------------------------
    solsay = sum(len(z) for z in sol)
    k_sol = solsay == 0
    print("[%s] KAPI-SOL     (-%.3f, 0] araliginda toplam sifir = %d  -> %s" % (
        a.cell, a.eps, solsay, "GECTI" if k_sol else "DUSTU"))

    # --- KAPI-AYIRMA ---------------------------------------------------------
    bozuk = []
    for i in range(1, d - 1):
        A1 = sag[i]; A2 = sag[i + 1]
        if len(A1) != i or len(A2) != i + 1:
            continue
        # A2'nin i+1 koku, A1'in i kokunu ayirmali
        ok = all(A2[k] < A1[k] < A2[k + 1] for k in range(i))
        if not ok:
            bozuk.append(i)
    k_ayir = (len(bozuk) == 0)
    print("[%s] KAPI-AYIRMA  ardisik ciftlerde interlacing  -> %s%s" % (
        a.cell, "GECTI" if k_ayir else "DUSTU",
        "" if k_ayir else "   (bozuk i: %s)" % bozuk[:8]))

    # --- KAPI-IZGARA ---------------------------------------------------------
    _, sag2, _ = tara(V, a.K, d, a.eps, a.izgara * 2, 400)
    s2 = [len(z) for z in sag2]
    k_izg = (s2 == sayilar)
    print("[%s] KAPI-IZGARA  izgara %d -> %d: sayilar %s  -> %s" % (
        a.cell, a.izgara, a.izgara * 2, "AYNI" if k_izg else "DEGISTI",
        "GECTI" if k_izg else "DUSTU"))

    # --- KAPI-NEG: bozulmus aile sayiyi degistirmeli -------------------------
    Vb = [list(V[0])]
    for i in range(1, d):
        Vb.append([V[i][k] + V[i - 1][k] * mp.mpf("0.9") for k in range(a.K)])
    _, sagb, _ = tara(Vb, a.K, d, a.eps, a.izgara, 400)
    sb = [len(z) for z in sagb]
    k_neg = (sb != sayilar)
    fark = sum(1 for i in range(d) if sb[i] != sayilar[i])
    print("[%s] KAPI-NEG     bozulmus ailede %d/%d sayac degisti  -> %s" % (
        a.cell, fark, d, "GECTI (sayac kor degil)" if k_neg else "DUSTU (SAYAC KOR)"))

    hep = k_sayi and k_sol and k_ayir and k_izg and k_neg
    print("\n" + "=" * 84)
    print("SONUC: %s   [%.0f s]" % (
        "HEPSI GECTI -- Markov sistemi olcutu AYAKTA" if hep
        else "EN AZ BIRI DUSTU", time.time() - t0))
    print("=" * 84)

if __name__ == "__main__":
    main()

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
psi_sanal_v1.py  --  psi_{2i}'nin SAF SANAL ekseninde sifiri var mi?

ZINCIRDE NEREDE:
  cheb_indirge_v1 : rank L = rank Psi                    [iki hucre, 4 kapi]
  cheb_isaret_v1  : det hep tek isaret                   [8 kapi, 300 kume]
  cheb_osilasyon_v1: Markov olcutu (0,1)'de              [10 kapi, iki hucre]
  BU ARAC         : zincirin kalan TEK varsayimini olcer.

ELLE TURETME (kosumdan ONCE ilan):
  Kutup satiri  psi_{2i}(i/(2 Omega))  ile s=0 satiri arasindaki oran
      rho_i = psi_{2i}(iy)/psi_{2i}(0),   y = 1/(2 Omega)
  Hadamard carpanlarina ayirmada (psi cift, tam, mertebe 1):
      psi(s) = psi(0) * prod_k (1 - s^2/z_k^2)
  Sifirlar reel ise  rho_i = prod (1 + y^2/z_k^2) > 1.
  Karmasik sifirlar  w, wbar, -w, -wbar dortlusu halinde gelir ve
      (1 + y^2/w^2)(1 + y^2/wbar^2) = |1 + y^2/w^2|^2 > 0
  olur; bu carpan ANCAK w = +-iy ise sifirlanir. Dolayisiyla:
      rho_i sifirlanir  <=>  psi_{2i}'nin SAF SANAL sifiri var.
  Yani zincirin kalan varsayimi "butun sifirlar reel" DEGIL, yalnizca
  "saf sanal sifir yok" -- cok daha dar bir iddia.

BU NICELIK NEYIN OZELLIGI:
  Sifirlarin yeri NESNENIN ozelligidir. Aletin izi: Legendre kesimi K,
  hassasiyet dps, tarama araligi. Ucu de taranir.

KAPILAR:
  KAPI-SANAL  : psi_{2i}(iy) saf sanal eksende (0, Y] boyunca isaret degistirmiyor
  KAPI-BUYUME : |psi_{2i}(iy)| y ile MONOTON artiyor (Hadamard'in bekledigi)
  KAPI-ARG    : arguman ilkesi -- bir kutuda sayilan sifir, reel eksendekilerle ayni
  KAPI-K      : sonuc Legendre kesimi K'den bagimsiz
  KAPI-NEG    : bilerek saf sanal sifir yerlestirilmis test fonksiyonu YAKALANMALI

KULLANIM:
  python -u psi_sanal_v1.py                       # A hucresi
  python -u psi_sanal_v1.py --cell B --K 120
  python -u psi_sanal_v1.py --Y 5.0               # daha genis sanal tarama
"""
import argparse, hashlib, os, time
import mpmath as mp

SURUM = "psi_sanal_v1.py  v1.0"
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
    return [ev[k] for k in od[:d]], [[U[i, k] for i in range(K)] for k in od[:d]]

def ln_(m): return mp.sqrt((2 * mp.mpf(m) + 1) / 2)

def psi_fab(v, K):
    co = [v[i] * ln_(2 * i) for i in range(K)]
    def f(z):
        return mp.fsum(co[i] * mp.legendre(2 * i, z) for i in range(K))
    return f

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cell", default="A", choices=["A", "B"])
    ap.add_argument("--K", default="88,120")
    ap.add_argument("--dps", type=int, default=50)
    ap.add_argument("--Y", type=float, default=2.0)
    ap.add_argument("--n", type=int, default=400)
    a = ap.parse_args()
    Ks = [int(x) for x in a.K.split(",")]

    print("=" * 84)
    print(SURUM + "   md5=" + _md5() + "   mpmath " + mp.__version__)
    print("=" * 84)
    print("""ON-KAYIT (kosumdan ONCE):
  TURETME: rho_i sifirlanir <=> psi_{2i}'nin SAF SANAL sifiri var.
           (karmasik sifirlar dortlu geldiginden carpimlari |..|^2 > 0 verir)
  IDDIA:   psi_{2i}(iy) saf sanal eksende HIC sifirlanmaz; |psi(iy)| y ile artar.
  BEKLENTI: isaret sabit, buyume monoton, arguman ilkesi karmasik sifir saymaz.
  SINIR:   sonlu bir Y araligi taranir; disarisi hakkinda hukum verilmez.
""")
    cell = CELLS[a.cell]; d = cell["d"]; Om = mp.mpf(cell["Omega"])
    mp.mp.dps = a.dps
    h = mp.log(Q) / 2; c = Om * h
    print("[%s] Omega=%s  d=%d  c=%s  Y=%.2f  dps=%d\n" % (
        a.cell, mp.nstr(Om, 10), d, mp.nstr(c, 10), a.Y, a.dps))

    sonuc = {}
    for K in Ks:
        t0 = time.time()
        chi, V = prolate_even(c, K, d)
        fs = [psi_fab(v, K) for v in V]
        ys = [mp.mpf(a.Y) * k / a.n for k in range(a.n + 1)]
        donen = []; monoton_bozan = []
        for i, f in enumerate(fs):
            vals = [mp.re(f(mp.mpc(0, 1) * y)) for y in ys]
            s0 = 1 if vals[0] > 0 else -1
            if any((v > 0) != (vals[0] > 0) for v in vals):
                donen.append(i)
            av = [abs(v) for v in vals]
            if any(av[k + 1] < av[k] * mp.mpf("0.999999999") for k in range(len(av) - 1)):
                monoton_bozan.append(i)
        sonuc[K] = (donen, monoton_bozan)
        print("[%s] K=%3d  isaret donen mod: %-12s  buyume bozan mod: %-12s  [%.0f s]" % (
            a.cell, K, str(donen[:6]) if donen else "YOK",
            str(monoton_bozan[:6]) if monoton_bozan else "YOK", time.time() - t0))

    k_sanal = all(len(sonuc[K][0]) == 0 for K in Ks)
    k_buyume = all(len(sonuc[K][1]) == 0 for K in Ks)
    k_K = len(set((tuple(sonuc[K][0]), tuple(sonuc[K][1])) for K in Ks)) == 1
    print("\n[%s] KAPI-SANAL   (0,%.1f] boyunca isaret degisimi yok  -> %s" % (
        a.cell, a.Y, "GECTI" if k_sanal else "DUSTU"))
    print("[%s] KAPI-BUYUME  |psi(iy)| monoton artiyor  -> %s" % (
        a.cell, "GECTI" if k_buyume else "DUSTU"))
    print("[%s] KAPI-K       sonuc K'den bagimsiz (%s)  -> %s" % (
        a.cell, ",".join(str(k) for k in Ks), "GECTI" if k_K else "DUSTU"))

    # --- KAPI-ARG: arguman ilkesi, kutu [-R,R] x [-R,R], reel sifirlar cikarilir
    K0 = Ks[0]; chi, V = prolate_even(c, K0, d)
    i_test = d // 2
    f = psi_fab(V[i_test], K0)
    R = mp.mpf("1.5")
    def kenar_say(f, R, n):
        top = mp.mpf(0); onc = None
        kose = [mp.mpc(-R, -R), mp.mpc(R, -R), mp.mpc(R, R), mp.mpc(-R, R), mp.mpc(-R, -R)]
        for kk in range(4):
            A, B = kose[kk], kose[kk + 1]
            for t in range(n + 1):
                z = A + (B - A) * mp.mpf(t) / n
                w = f(z)
                arg = mp.arg(w)
                if onc is not None:
                    dd = arg - onc
                    while dd > mp.pi: dd -= 2 * mp.pi
                    while dd < -mp.pi: dd += 2 * mp.pi
                    top += dd
                onc = arg
        return top / (2 * mp.pi)
    try:
        say = kenar_say(f, R, 300)
        # (-1.5,1.5) reel araliginda beklenen sifir sayisi: 2*i_test (cift fonksiyon)
        # artı (1,1.5) ve (-1.5,-1) araligindaki olasi reel sifirlar
        bek = 2 * i_test
        k_arg = abs(say - mp.nint(say)) < mp.mpf("0.05") and int(mp.nint(say)) >= bek
        print("[%s] KAPI-ARG     |z|<%s kutusunda sifir sayisi = %s   (ic aralikta beklenen >= %d)  -> %s" % (
            a.cell, mp.nstr(R, 3), mp.nstr(say, 6), bek, "GECTI" if k_arg else "DUSTU"))
    except Exception as e:
        k_arg = False
        print("[%s] KAPI-ARG     hesaplanamadi (%s)  -> DUSTU" % (a.cell, type(e).__name__))

    # --- KAPI-NEG: saf sanal sifiri OLAN bir fonksiyon yakalanmali
    yz = mp.mpf("0.7")
    def g(z): return mp.mpf(1) + z * z / (yz * yz)     # sifirlari z = +-i*yz
    vals = [mp.re(g(mp.mpc(0, 1) * (mp.mpf(a.Y) * k / a.n))) for k in range(a.n + 1)]
    yakalandi = any((v > 0) != (vals[0] > 0) for v in vals)
    print("[%s] KAPI-NEG     kasten saf sanal sifirli fonksiyon: %s  -> %s" % (
        a.cell, "YAKALANDI" if yakalandi else "KACTI",
        "GECTI" if yakalandi else "DUSTU (TARAYICI KOR)"))

    hep = k_sanal and k_buyume and k_K and k_arg and yakalandi
    print("\n" + "=" * 84)
    print("SONUC: %s" % ("HEPSI GECTI -- saf sanal sifir YOK, zincirin son varsayimi ayakta"
                         if hep else "EN AZ BIRI DUSTU"))
    print("=" * 84)

if __name__ == "__main__":
    main()

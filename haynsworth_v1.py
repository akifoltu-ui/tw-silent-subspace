#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
haynsworth_v1.py  --  HEDEF 1: kappa(G_geom) = 1  ->  kutup dikinde kappa = 0

NEDEN BU DOSYA:
  Kutupsuz geometrik form G_geom = sa*W - Pr icin kayitta kappa = 1 (tek negatif
  ozdeger), on bir pencerede sabit. Bu bir engel degil, Weil formulundeki s=1
  kutbunun urettigi HIPERBOLIK yondur. Haynsworth atalet toplanabilirligi:

    M simetrik, kappa(M) = 1, v != 0, M tersinir,
    s := <v, M^{-1} v> < 0   ==>   kappa( M |_{v^perp} ) = 0.

  Yani kutup kosulu eklendigi anda negatif yon TAM OLARAK tuketilir ve kalan
  altuzayda form pozitif tanimli olur. Bu, 8 Ekim calismasindaki lam_min > 0
  kilidinin cebirsel aciklamasidir.

ONEMLI -- BU ARAC SIFIRDAN KURMUYOR:
  Konvansiyon (arsimed isareti, asal normalizasyonu, Legendre tabani, kutup
  vektorleri vp/vm) kapi6b_fast_v19.py'de OTURMUS durumda. Bu arac onu import
  eder ve YALNIZCA Haynsworth hesabini ekler. Sifirdan kurma denemesi
  2026-10-30'da kappa = 3..8 verdi (yanlis konvansiyon) ve DUSTU; o yuzden
  mevcut alet kullaniliyor.

KAPILAR:
  KAPI-KAPPA : kappa(Q_geom) = 1   (kayitla uyum)
  KAPI-S     : s = <w, Q_geom^{-1} w> < 0   (Haynsworth kosulu)
  KAPI-PERP  : kappa(Q_geom|_{w^perp}) = 0  VE  lam_min > 0
  KAPI-NEG   : w yerine RASTGELE vektor -> kappa_perp = 1 KALMALI
               (dusmezse mekanizma kutupa ozgu degil, arac kabuk)

KULLANIM (kapi6b_fast_v19.py ile ayni dizinde):
  python -u haynsworth_v1.py --d 21 --cc 0.5
  python -u haynsworth_v1.py --d 21 --cc 0.5 --dlist 13,17,21,25
"""
import sys, os, json, argparse, hashlib, time
import mpmath as mp
from mpmath import mpf, matrix, eigsy, sqrt, fabs

SURUM = "haynsworth_v1.py  v1.0"

def _md5():
    try: return hashlib.md5(open(os.path.abspath(__file__), "rb").read()).hexdigest()
    except Exception: return "N/A"

# --- mevcut aleti kullan (sifirdan kurma YOK) ---------------------------------
try:
    import kapi6b_fast_v19 as M
except Exception as e:
    print("DUR: kapi6b_fast_v19.py bulunamadi/yuklenemedi (%s)." % type(e).__name__)
    print("     Bu arac konvansiyonu O dosyadan alir; sifirdan kurmaz.")
    sys.exit(2)

def G_geom(W, SP, vp, vm, sa, asal_sec=None):
    """KUTUPSUZ geometrik matris:  G = sa*W - Pr.
       (kapi6b _K_kur ile ayni, yalnizca sp*(vm vp^T + vp vm^T) terimi YOK)"""
    nb = len(vp)
    Pr = matrix(nb, nb)
    for (n, p) in M.primepowers(M.Q_KESME):
        if asal_sec is not None and n not in asal_sec: continue
        if SP.get(str(n)) is None: continue
        cfa = mp.log(mpf(p)) / sqrt(mpf(n)); M2 = SP[str(n)]
        for a in range(nb):
            for b in range(nb): Pr[a, b] += cfa * M2[a, b]
    G = matrix(nb, nb)
    for a in range(nb):
        for b in range(nb):
            G[a, b] = mpf(sa) * W[a, b] - Pr[a, b]
    return G

def hucreye_indir(G, C, d, nb):
    """nb-boyutlu G'yi d-boyutlu hucre tabanina indir."""
    Q = matrix(d, d)
    for i in range(d):
        Gi = [sum(G[a, b] * C[i][a] for a in range(nb)) for b in range(nb)]
        for j in range(i, d):
            v = sum(Gi[b] * C[j][b] for b in range(nb)); Q[i, j] = v; Q[j, i] = v
    return Q

def vek_indir(v, C, d, nb):
    return [sum(C[i][a] * v[a] for a in range(nb)) for i in range(d)]

def dik_kisitla(Q, w, d):
    """w'ye dik (d-1)-boyutlu altuzayda Q'nun ozdegerleri."""
    n2 = sqrt(sum(x * x for x in w))
    u = [x / n2 for x in w]
    tab = []
    for i in range(d):
        e = [mpf(1) if k == i else mpf(0) for k in range(d)]
        c = sum(u[k] * e[k] for k in range(d)); e = [e[k] - c * u[k] for k in range(d)]
        for b in tab:
            c2 = sum(b[k] * e[k] for k in range(d)); e = [e[k] - c2 * b[k] for k in range(d)]
        nn = sqrt(sum(x * x for x in e))
        if nn > mpf(10) ** (-mp.mp.dps + 8): tab.append([x / nn for x in e])
        if len(tab) == d - 1: break
    Qp = matrix(d - 1, d - 1)
    for a in range(d - 1):
        for b in range(a, d - 1):
            v = sum(tab[a][i] * sum(Q[i, j] * tab[b][j] for j in range(d)) for i in range(d))
            Qp[a, b] = v; Qp[b, a] = v
    E = eigsy(Qp, eigvals_only=True)
    return [E[i] for i in range(d - 1)]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--d", type=int, default=21)
    ap.add_argument("--cc", type=float, default=0.5)
    ap.add_argument("--dlist", default="")
    ap.add_argument("--sa", type=int, default=-1)
    ap.add_argument("--path", default=None)
    a = ap.parse_args()

    print("=" * 84)
    print(SURUM + "   md5=" + _md5() + "   kapi6b=" + getattr(M, "__file__", "?"))
    print("=" * 84)
    print("""ON-KAYIT (kosumdan ONCE):
  IDDIA: G_geom = sa*W - Pr  icin kappa = 1 (kayit). Kutup vektoru w (= C vp) ile
     s := <w, Q^{-1} w> < 0   ==>   kappa(Q|_{w^perp}) = 0   (Haynsworth)
  BEKLENTI: her d'de kappa=1, s<0, dik altuzayda kappa=0 ve lam_min>0.
  NEGATIF KONTROL: w yerine rastgele vektor -> kappa_perp = 1 KALMALI.
  SINIR: bu arac kappa SAYAR; buyukluk (lam_min) N ile eriyor, o ayri bir duvar.
""")
    path = a.path if a.path else M.CEK_FAST
    Kleg, W, SP, vp, vm = M.yukle(path)
    nb = len(vp)
    print("kurulum: nb=%d  q=%s  L=%s  cc=%s  sa=%d" % (
        nb, M.Q_KESME, mp.nstr(M._L(), 10), a.cc, a.sa))

    G = G_geom(W, SP, vp, vm, a.sa)
    ds = [int(x) for x in a.dlist.split(",")] if a.dlist else [a.d]
    print("\n%-5s %-5s %-18s %-18s %-7s %-10s" % (
        "d", "kap", "s=<w,Q^-1 w>", "lam_min(perp)", "kap_p", "hukum"))
    rnd = mp.rand
    for d in ds:
        t0 = time.time()
        C, tail = M.C_matrisi(d, mpf(str(a.cc)), Kleg)
        Q = hucreye_indir(G, C, d, nb)
        E = eigsy(Q, eigvals_only=True); evs = [E[i] for i in range(d)]
        kap = sum(1 for x in evs if x < 0)
        w = vek_indir(vp, C, d, nb)
        try:
            Qi = Q ** -1
            s = sum(w[i] * sum(Qi[i, j] * w[j] for j in range(d)) for i in range(d))
        except Exception:
            s = None
        ep = dik_kisitla(Q, w, d)
        kap_p = sum(1 for x in ep if x < 0); lmin = min(ep)
        ok = (kap == 1) and (s is not None and s < 0) and (kap_p == 0) and (lmin > 0)
        print("%-5d %-5d %-18s %-18s %-7d %-10s  [%.0fs]" % (
            d, kap, (mp.nstr(s, 8) if s is not None else "tekil"),
            mp.nstr(lmin, 8), kap_p, "GECTI" if ok else "DUSTU", time.time() - t0))
        # KAPI-NEG: rastgele vektor
        wr = [mpf(str(rnd())) - mpf("0.5") for _ in range(d)]
        epr = dik_kisitla(Q, wr, d)
        kap_r = sum(1 for x in epr if x < 0)
        print("      KAPI-NEG rastgele vektor -> kappa_perp = %d (beklenen %d)  -> %s" % (
            kap_r, kap, "GECTI" if kap_r == kap else "DUSTU (mekanizma kutupa ozgu DEGIL)"))

if __name__ == "__main__":
    main()

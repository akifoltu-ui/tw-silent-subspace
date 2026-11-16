# tw-silent-subspace

M. A. Oltulu, "Weil kuadratik formunun sonlu-örnekleme kesmelerinde sessiz altuzayların boyutu" ("The dimension of silent subspaces in finite-sampling truncations of the Weil quadratic form"), Zenodo, kavram DOI'si [10.5281/zenodo.22730006](https://doi.org/10.5281/zenodo.22730006) (sürüm 4: [10.5281/zenodo.23778611](https://doi.org/10.5281/zenodo.23778611)) için yeniden üretim kodu ve Lean 4 formel doğrulaması.

Bu yazılım kaydı: kavram DOI'si [10.5281/zenodo.23724476](https://doi.org/10.5281/zenodo.23724476); en son sürüme yönlenir.

İngilizce sürüm: [README.md](README.md).

## Sürümler

| Sürüm | Etiket tarihi | DOI | İçerik |
|---|---|---|---|
| v2.0.0 | 2026-10-28 | [10.5281/zenodo.23724477](https://doi.org/10.5281/zenodo.23724477) | Makalenin altı sonucunun tamamı Lean 4 / Mathlib'de makine tarafından denetlendi; Bölüm 5'in canlı yeniden üretimi |
| v2.1.0 | 2026-10-28 | [10.5281/zenodo.23725248](https://doi.org/10.5281/zenodo.23725248) | İfade sadakati denetimi: Teorem 3'ün eşitlik koşulu, Önerme 8'de minimallik |
| v2.2.0 | 2026-10-29 | [10.5281/zenodo.23777007](https://doi.org/10.5281/zenodo.23777007) | Teorem 3 için eşitlik sertifikası: iki hücrede aralık LDL; Lean rank bağı ve karşı örnek |
| v2.3.0 | 2026-10-30 | [10.5281/zenodo.24291599](https://doi.org/10.5281/zenodo.24291599) | Kutup uysallığı (pole-tameness) lemması, formel olarak doğrulandı; örnekleme matrisinin Chebyshev indirgemesi |
| v2.4.0 | 2026-10-30 | [10.5281/zenodo.24291617](https://doi.org/10.5281/zenodo.24291617) | Kutup deflasyonu: kutupsuz formun tek negatif yönünü kutup koşulu tüketir |
| v2.5.0 | 2026-11-03 | [10.5281/zenodo.24291670](https://doi.org/10.5281/zenodo.24291670) | Kör bölge payı: sabit bir test vektöründe `delta*` okuması |
| v2.5.1 | 2026-11-17 | bu sürüm | v2.2.0-v2.5.0 belgelendirmesi; belgelerin Türkçe sürümü |

## Yeniden üretim araçları

`mpmath` üzerinde tek dosyalık Python araçları; `haynsworth_v1.py` ayrıca aşağıda belirtilen motoru içe aktarır. Test hücreleri (q = 13): A için Omega = 75.5524, N = 18, d = 21; B için Omega = 103.7255, N = 30, d = 33.

| Dosya | Ne hesaplar | Koşum logları |
|---|---|---|
| `tw_reproduce.py` | Bölüm 5: iki hücrede rank L ve dim W = d - rank L; G1-G5 denetimleri, negatif kontroller `--dup-zero` ve `--inject-odd`, sınır okuması `--basis firstd` | `run_AB_canli.log`, `run_AB_canli.json`, `run_neg__dup_zero.log`, `run_neg__inject_odd.log` |
| `tw_sigma_sert_v1.py` | Teorem 3 için eşitlik sertifikası: G = L L^T üzerinde aralık LDL, her pivot için pozitif alt sınır; tekrarlanan ordinatla negatif kontrol | `run_sertifika_canli.log` |
| `cheb_indirge_v1.py` | Örnekleme matrisinin indirgenmesi: L[j,i] = h mu_{2i} psi_{2i}(s_j), dolayısıyla rank L = rank Psi | `run_cheb_indirge.log` |
| `cheb_isaret_v1.py` | phi_i(w) = psi_{2i}(sqrt w) ailesinin Chebyshev (Haar) özelliği: rastgele nokta kümeleri üzerinde det[phi_i(w_j)] işareti, iki Legendre kesiminde ve iki hassasiyette; tekrarlanan noktayla negatif kontrol | `run_cheb_isaret_A.log`, `run_cheb_isaret_B.log` |
| `cheb_osilasyon_v1.py` | Markov ölçütü: phi_i'nin (0,1) üzerinde tam i sıfırı vardır, ardışık sıfır kümeleri birbirini ayırır, (-eps, 0] aralığı sıfırsızdır; bozulmuş aileyle negatif kontrol | `run_cheb_osilasyon_A.log`, `run_cheb_osilasyon_B.log` |
| `psi_sanal_v1.py` | Kutup tarafı: psi_{2i}(iy) sanal eksen boyunca işaretini korur ve monoton büyür; yerleştirilmiş sanal sıfırla negatif kontrol | `run_psi_sanal_A.log`, `run_psi_sanal_B.log` |
| `haynsworth_v1.py` | Kutupsuz geometrik form üzerinde Haynsworth eylemsizlik ölçütü: kappa = 1, s = <w, G^-1 w> = -exp(L/2)/2 < 0, kutup vektörünün dik tümleyeninde kappa = 0; rastgele vektörle negatif kontrol | `run_haynsworth.log`, `run_haynsworth_cok.log` |
| `kor_bolge_v2.py` | `delta*` dışlama sınırları için geçerlilik denetimi: kappa(d, L) = 2 sinh(dL)/d - 2L üzerinden kör bölge derinliği d_0 (Eberwein, Teorem 7.1, Zenodo kaydı 23177438); mu her test vektörü için ölçülür | `run_kor_bolge_v2.log` |
| `tavan_v1_2.py` | Sabit test vektörlerinde `delta*`, d_0 ve `delta*`/d_0 payı | `run_tavan_v1_2.log` |

Ek log: `run_cheb_B_K120.log` (B hücresi, Legendre kesimi K = 120).

`haynsworth_v1.py`, uzlaşımların (arşimet işareti, asal normalizasyonu, Legendre tabanı, kutup vektörleri) sabitlendiği Weil-form motoru `kapi6b_fast_v19.py` dosyasını içe aktarır; motor bu deponun dışındadır ve iki koşumun çıktıları yukarıdaki loglarda kayıtlıdır.

Örnek koşumlar:

    python -u tw_reproduce.py
    python -u tw_sigma_sert_v1.py --ivdps 80,140
    python -u cheb_indirge_v1.py
    python -u cheb_isaret_v1.py --cell B --kume 300
    python -u cheb_osilasyon_v1.py --cell B --K 120
    python -u psi_sanal_v1.py --cell B --K 120
    python -u haynsworth_v1.py --d 21 --cc 0.5 --dlist 13,17,21,25
    python -u kor_bolge_v2.py
    python -u tavan_v1_2.py

## Lean 4 formel doğrulama

Makalenin altı sonucunun tamamı Lean 4 / Mathlib'de makine tarafından denetlenmiştir; aksiyom denetimi temizdir ve negatif kontroller eşlik eder. 2.2.0-2.4.0 sürümleri rank bağını, minör ölçütünü, eşleniksizlik (disconjugacy) argümanını ve kutup deflasyonunun cebirsel çekirdeğini ekler. Ayrıntı aşağıda ve [lean/README.md](lean/README.md) dosyasındadır.

---

# Lean 4 formel doğrulama: lean/README.md dosyasının Türkçesi

Bu bölümdeki dosya yolları `lean/` klasörüne görelidir.

Makalenin altı sonucunun tamamı (Teorem 3, Sonuç 4, Önerme 5, 7, 8 ve min-maks sayım eşitsizliği) Lean 4 / Mathlib'de makine tarafından denetlenmiştir. Araç zinciri: leanprover/lean4:v4.35.0-rc3.

| Dosya | Teoremler | Derleme ve aksiyom denetimi |
|---|---|---|
| `TwBoyut_v1.lean` | `TW.boyut, TW.tasarim, TW.sessizlik` | geçti |
| `TwKeskinlik_v1.lean` | `TW.K_eq, TW.ozvektor, TW.H_disinda, TW.B_rayleigh_pozitif` | geçti |
| `TwCekirdekDisi_v1.lean` | `TW.cekirdek_disi` | geçti |
| `TwMinMaks_v2.lean` | `TW.sayim, TW.minmaks` | geçti |

Aksiyom denetimi: yalnız propext, Classical.choice ve Quot.sound; ispatlar sorry'siz tamamlanmıştır. Her temel dosyanın `kontrol/` altında bilerek yanlış kurulmuş bir karşılığı vardır; dördü de derleyici tarafından reddedilir. Denetlenen koşumun logları `denetim/` altındadır.

Kontrol: `lean/` klasöründe `lake env lean <dosya>`.

## v2.1 ekleri: ifade sadakati denetimi (2026-10-28)

Makalenin her ifadesi kendi Lean teoremiyle satır satır eşleştirildi. İki parça eklendi; v1 teoremlerinin tamamı v2 dosyalarında aynen korunur.

* `TwBoyut_v2.lean`: `TW.esitlik`, her d >= N+1 için Teorem 3'ün eşitlik koşulunu verir (dim W = d-(N+1) <=> rank L = N+1, yani N+1 koşul bağımsızdır); `TW.esitlik_kucuk` d <= N+1 durumunu kapsar: orada alt sınır 0'dır ve eşitlik rank L = d (L birebir) anlamına gelir. Negatif kontrol `kontrol/TwBoyutYanlis_v2.lean`: d >= N+1 hipotezi kaldırılınca denklik reddedilir (d = 1, N = 5).
* `TwKeskinlik_v2.lean`: `TW.C_psd` (C >= 0; böylece örnek Önerme 7'nin hipotezlerini sağlar), `TW.rayleigh` (her x için (3-sqrt 5)/2 <x,x> <= <x,Kx>) ve `TW.en_kucuk` (K'nin her özdeğeri >= (3-sqrt 5)/2); dolayısıyla Önerme 8'in özvektörü en küçük özdeğere aittir. Negatif kontroller `kontrol/TwKeskinlikYanlis_v2a.lean` (sınır 1/100 yükseltilmiş) ve `kontrol/TwKeskinlikYanlis_v2b.lean` (belirsiz matris) reddedilir.

v2 dosyalarının aksiyom denetimi: yalnız propext, Classical.choice ve Quot.sound; loglar `denetim/` altındadır.

## v2.2-v2.4 ekleri: rank bağı, minör ölçütü, eşleniksizlik, kutup deflasyonu (2026-10-29 ile 2026-10-30 arası)

| Dosya | Teoremler | Sürüm |
|---|---|---|
| `TwRank_v1_2.lean` | `TW.rank_of_gram_posDef`, `TW.dimW_eq_of_gram_posDef`: pozitif tanımlı bir L L^T Gram matrisi tam satır rankı verir, dolayısıyla dim W = d - n | v2.2.0 |
| `kontrol/TwRankKarsiOrnek_v1.lean` | `TWKontrol.posSemidef_yetmez`: hipotezin keskinliği, pozitif yarı-tanımlılık yeterli olmaz (karşı örnek L = 0), `sorry` kullanılmadan kanıtlandı | v2.2.0 |
| `TwRankMinor_v1_3.lean` | `TWMinor.rank_of_submatrix_det_ne_zero`, `TWMinor.dimW_eq_of_submatrix_det_ne_zero`: sıfırdan farklı tek bir maksimal minör tam satır rankı verir; `TWMinorKontrol.det_ne_zero_gerekli`: hipotezin keskinliği | v2.3.0 |
| `TwDisconj_v2_3.lean` | `TWDisconj.deriv_pos_of_pos_on`, `TWDisconj.pos_of_deriv_pos_bootstrap`, `TWDisconj.pos_of_integral_eq`: kutup uysallığı lemmasının dayandığı pozitiflik (eşleniksizlik) argümanı | v2.3.0 |
| `TwHaynsworth_v2_1.lean` | `TWHayn.B_symm`, `TWHayn.Q_lin_comb`, `TWHayn.neg_plane_of_two_dirs`, `TWHayn.no_second_neg_dir`: kutup deflasyonunun cebirsel çekirdeği; eylemsizlik indisi hipotezi açıkça taşınır | v2.4.0 |

Bu dosyaların aksiyom denetimi: yalnız propext, Classical.choice ve Quot.sound; loglar `denetim/TwRank_v1_2_denetim.log`, `denetim/TwRankKarsiOrnek_v1_denetim.log`, `denetim/TwRankMinor_v1_3_denetim.log`, `denetim/TwDisconj_v2_3_denetim.log`, `denetim/TwHaynsworth_v2_1_denetim.log`. `TwFormal.lean`, Lake projesinin kütüphane köküdür.

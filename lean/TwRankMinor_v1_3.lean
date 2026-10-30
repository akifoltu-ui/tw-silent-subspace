/-
  TwRankMinor_v1_3.lean  --  M. A. Oltulu, "The dimension of silent subspaces in
  finite-sampling truncations of the Weil quadratic form"
  (Zenodo 10.5281/zenodo.22730006).

  TwRank_v1_2.lean'in GENELLEMESI.

  Orada halka su idi:   G = L Lᵀ pozitif tanimli  =>  rank L = N+1.
  Bu, ARALIK LDL sertifikasina bagliydi ve hucre hucre calisiyordu.

  Burada halka daha genel:  L'nin HERHANGI bir (N+1)x(N+1) alt matrisinin
  determinanti sifirdan farkliysa  =>  rank L = N+1.

  Neden onemli: Chebyshev (T-) sistemi argumani tam olarak bunu uretir.
  {phi_0,...,phi_N} bir T-sistemi ve noktalar farkli ise, ilgili alt
  determinant sifirdan farklidir -- Gram matrisine, pozitif tanimliliga,
  aralik aritmetigine gerek kalmaz.

  Hipotezin GEREKLILIGI de kanitli (asagida, `sorry` yok).

  v1 -> v1.1 : Mathlib.Data.Real.Basic import edilmedigi icin `ℝ` serbest
               degisken olarak baglanmisti; import eklendi.
  v1.1 -> v1.2 : import adi guncellendi (Mathlib.Basic.Real.Basic);
               `rank_submatrix_le` adlandirilmis argumansiz cagriliyor;
               karsi ornekte kullanilmayan `f` -> `_f`.
  v1.2 -> v1.3 : kullanilmayan [DecidableEq d] bildirimden cikarildi
               (linter temiz).
-/
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace TWMinor

open Matrix

variable {n d : Type*} [Fintype n] [DecidableEq n] [Fintype d]

/-- `L`'nin bir sutun secimi `f : n → d` ile olusan kare alt matrisinin
    determinanti sifirdan farkliysa, `L` tam satir rankina sahiptir. -/
theorem rank_of_submatrix_det_ne_zero
    (L : Matrix n d ℝ) (f : n → d)
    (hdet : (L.submatrix id f).det ≠ 0) :
    L.rank = Fintype.card n := by
  have hU : IsUnit (L.submatrix id f) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hdet
  have h1 : (L.submatrix id f).rank = Fintype.card n :=
    Matrix.rank_of_isUnit _ hU
  have h2 : (L.submatrix id f).rank ≤ L.rank :=
    Matrix.rank_submatrix_le L id f
  have h3 : L.rank ≤ Fintype.card n := Matrix.rank_le_card_height _
  omega

/-- Teorem 3'un esitlik hali, alt determinant hipoteziyle:
    cekirdek boyutu TAM olarak `d - n`. -/
theorem dimW_eq_of_submatrix_det_ne_zero
    (L : Matrix n d ℝ) (f : n → d)
    (hdet : (L.submatrix id f).det ≠ 0) :
    Fintype.card d - L.rank = Fintype.card d - Fintype.card n := by
  rw [rank_of_submatrix_det_ne_zero L f hdet]

#print axioms TWMinor.rank_of_submatrix_det_ne_zero
#print axioms TWMinor.dimW_eq_of_submatrix_det_ne_zero

end TWMinor

namespace TWMinorKontrol

open Matrix

/-- KARSI ORNEK: determinantin sifirdan farkli olmasi hipotezi GEREKLIDIR.
    `L = 0` icin her alt determinant sifirdir ve rank 0'dir, `card n = 1` degil. -/
theorem det_ne_zero_gerekli :
    ¬ (∀ (L : Matrix (Fin 1) (Fin 1) ℝ) (_f : Fin 1 → Fin 1),
        L.rank = Fintype.card (Fin 1)) := by
  intro h
  have h0 : (0 : Matrix (Fin 1) (Fin 1) ℝ).rank = 1 := by
    simpa using h 0 id
  simp at h0

#print axioms TWMinorKontrol.det_ne_zero_gerekli

end TWMinorKontrol

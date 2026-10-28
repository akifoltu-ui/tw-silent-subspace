import Mathlib

/-!
# NEGATIF KONTROL (TwKeskinlikYanlis_v1.lean) -- bu dosyanin IKI teoremi de DUSMELI.
(1) Yanlis ozdeger: v_min'e (3 + sqrt 5)/2 (buyuk ozdeger) yakistirmak.
(2) Yanlis icerilme: v_min'in H = ker B icinde oldugunu (B v_min = 0) iddia etmek.
Ayni kanit adimlari ikisinde de hata vermeli.
-/

open Matrix

noncomputable def Bm' : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
noncomputable def Km' : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 1]
noncomputable def vmin' : Fin 2 → ℝ := ![1, -(1 + Real.sqrt 5) / 2]

theorem yanlis_ozdeger : Km' *ᵥ vmin' = ((3 + Real.sqrt 5) / 2) • vmin' := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  ext i
  fin_cases i <;> simp [Km', vmin', Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> nlinarith [h5]

theorem yanlis_icerilme : Bm' *ᵥ vmin' = 0 := by
  ext i
  fin_cases i <;> simp [Bm', vmin', Matrix.mulVec, dotProduct, Fin.sum_univ_two]

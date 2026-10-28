import Mathlib

/-!
# T-W Onerme 8: keskinlik ornegi  (TwKeskinlik_v2.lean)

Kaynak: M. A. Oltulu (2026), Onerme 8.
B = [[1,0],[0,0]],  C = [[1,1],[1,1]],  K = B + C = [[2,1],[1,1]],  H = ker B = span{(0,1)}.
En kucuk ozdeger lambda_min = (3 - sqrt 5)/2 icin bir ozvektor v_min H'nin DISINDADIR:
B v_min != 0 ve <v_min, B v_min> > 0. Onerme 7'deki "yakinlik" sinirinin "icerilme"ye
yukseltilemeyecegini gosterir.

v2 (2026-10-28, ifade sadakati denetimi): v1'in dort teoremi AYNEN korundu; eklenenler:
  * `C_psd`          : C >= 0 (ornek, Onerme 7'nin C >= 0 varsayimini saglar);
  * `rayleigh_koord`, `rayleigh` : her x icin (3 - sqrt 5)/2 * <x,x> <= <x, K x>;
  * `en_kucuk`       : K'nin HER ozdegeri >= (3 - sqrt 5)/2, yani (3 - sqrt 5)/2 = lambda_min.
Kanit anahtari:  (1 + s) * 2 * (<x,Kx> - lambda <x,x>) = ((1+s) a + 2 b)^2 + (s^2 - 5) b^2,  s = sqrt 5.
-/

open Matrix

namespace TW

noncomputable def Bm : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
noncomputable def Cm : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 1]
noncomputable def Km : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 1]
/-- lambda_min = (3 - sqrt 5)/2 icin (normlanmamis) ozvektor. -/
noncomputable def vmin : Fin 2 → ℝ := ![1, -(1 + Real.sqrt 5) / 2]

/-- K = B + C. -/
theorem K_eq : Km = Bm + Cm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Km, Bm, Cm] <;> norm_num

/-- K v_min = lambda_min v_min,  lambda_min = (3 - sqrt 5)/2. -/
theorem ozvektor : Km *ᵥ vmin = ((3 - Real.sqrt 5) / 2) • vmin := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  ext i
  fin_cases i <;> simp [Km, vmin, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> nlinarith [h5]

/-- v_min, H = ker B'nin icinde DEGIL. -/
theorem H_disinda : Bm *ᵥ vmin ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [Bm, vmin, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this

/-- <v_min, B v_min> > 0 (normlanmamis vektorde deger 1). -/
theorem B_rayleigh_pozitif : 0 < vmin ⬝ᵥ (Bm *ᵥ vmin) := by
  simp [Bm, vmin, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- C >= 0: her x icin <x, C x> = (x0 + x1)^2 >= 0. -/
theorem C_psd (x : Fin 2 → ℝ) : 0 ≤ x ⬝ᵥ (Cm *ᵥ x) := by
  simp [Cm, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    nlinarith [sq_nonneg (x 0 + x 1)]

/-- Koordinat bicimi: (3 - sqrt 5)/2 * (a^2 + b^2) <= 2a^2 + 2ab + b^2  (= x^T K x). -/
theorem rayleigh_koord (a b : ℝ) :
    (3 - Real.sqrt 5) / 2 * (a ^ 2 + b ^ 2) ≤ 2 * a ^ 2 + 2 * a * b + b ^ 2 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hpos : 0 < 1 + Real.sqrt 5 := by linarith
  have key : (1 + Real.sqrt 5) *
      (2 * (2 * a ^ 2 + 2 * a * b + b ^ 2 - (3 - Real.sqrt 5) / 2 * (a ^ 2 + b ^ 2)))
      = ((1 + Real.sqrt 5) * a + 2 * b) ^ 2 + (Real.sqrt 5 ^ 2 - 5) * b ^ 2 := by
    ring
  simp only [h5, sub_self, zero_mul, add_zero] at key
  have hsq := sq_nonneg ((1 + Real.sqrt 5) * a + 2 * b)
  by_contra hneg
  push_neg at hneg
  have hD : 2 * (2 * a ^ 2 + 2 * a * b + b ^ 2 - (3 - Real.sqrt 5) / 2 * (a ^ 2 + b ^ 2)) < 0 := by
    linarith
  have hm := mul_neg_of_pos_of_neg hpos hD
  linarith

/-- Rayleigh alt siniri: her x icin  (3 - sqrt 5)/2 * <x,x> <= <x, K x>. -/
theorem rayleigh (x : Fin 2 → ℝ) :
    (3 - Real.sqrt 5) / 2 * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Km *ᵥ x) := by
  have hk := rayleigh_koord (x 0) (x 1)
  simp [Km, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> nlinarith [hk]

/-- En kucuklik: K'nin her ozdegeri mu (K y = mu y, y != 0) icin  (3 - sqrt 5)/2 <= mu. -/
theorem en_kucuk (μ : ℝ) (y : Fin 2 → ℝ) (hy : y ≠ 0) (he : Km *ᵥ y = μ • y) :
    (3 - Real.sqrt 5) / 2 ≤ μ := by
  have e0 := congrFun he 0
  have e1 := congrFun he 1
  simp [Km, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
  have hk := rayleigh_koord (y 0) (y 1)
  have hq : 2 * y 0 ^ 2 + 2 * y 0 * y 1 + y 1 ^ 2 = μ * (y 0 ^ 2 + y 1 ^ 2) := by
    linear_combination y 0 * e0 + y 1 * e1
  have hne : 0 < y 0 ^ 2 + y 1 ^ 2 := by
    rcases (show y 0 ≠ 0 ∨ y 1 ≠ 0 by
      by_contra hc
      push_neg at hc
      apply hy
      ext i
      fin_cases i <;> simp [hc.1, hc.2]) with h | h
    · have h2 : 0 < y 0 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h))
      nlinarith [sq_nonneg (y 1)]
    · have h2 : 0 < y 1 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h))
      nlinarith [sq_nonneg (y 0)]
  by_contra hlt
  push_neg at hlt
  have hm := mul_lt_mul_of_pos_right hlt hne
  linarith [hk, hq]

end TW

#print axioms TW.K_eq
#print axioms TW.ozvektor
#print axioms TW.H_disinda
#print axioms TW.B_rayleigh_pozitif
#print axioms TW.C_psd
#print axioms TW.rayleigh_koord
#print axioms TW.rayleigh
#print axioms TW.en_kucuk

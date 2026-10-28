import Mathlib

/-!
# T-W Onerme 8: keskinlik ornegi  (TwKeskinlik_v1.lean)

Kaynak: M. A. Oltulu (2026), Onerme 8.
B = [[1,0],[0,0]],  C = [[1,1],[1,1]],  K = B + C = [[2,1],[1,1]],  H = ker B = span{(0,1)}.
En kucuk ozdeger lambda_min = (3 - sqrt 5)/2 icin bir ozvektor v_min H'nin DISINDADIR:
B v_min != 0 ve <v_min, B v_min> > 0. Onerme 7'deki "yakinlik" sinirinin "icerilme"ye
yukseltilemeyecegini gosterir.
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

end TW

#print axioms TW.K_eq
#print axioms TW.ozvektor
#print axioms TW.H_disinda
#print axioms TW.B_rayleigh_pozitif

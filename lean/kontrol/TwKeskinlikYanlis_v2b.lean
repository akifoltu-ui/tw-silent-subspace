import Mathlib

/-!
# NEGATIF KONTROL (TwKeskinlikYanlis_v2b.lean) -- derleme DUSMELI

C_psd'nin kaniti her matriste "geciyor" olmamali: [[1,2],[2,1]] belirsizdir
(ozdegerler 3 ve -1; x = (1,-1)'de deger -2). Ayni kanit adimlari reddedilmeli.
-/

open Matrix

namespace TW

theorem psd_yanlis (x : Fin 2 → ℝ) :
    0 ≤ x ⬝ᵥ ((!![1, 2; 2, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x) := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1)]

end TW

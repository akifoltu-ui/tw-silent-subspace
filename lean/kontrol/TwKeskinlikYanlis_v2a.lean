import Mathlib

/-!
# NEGATIF KONTROL (TwKeskinlikYanlis_v2a.lean) -- derleme DUSMELI

Rayleigh alt siniri (3 - sqrt 5)/2 KESKINDIR (v_min'de esitlik). Sinir 1/100 kadar
buyutulurse ifade yanlis olur; v_min = (1, -(1+sqrt 5)/2)'de sol taraf sagdan buyuk.
-/

namespace TW

theorem rayleigh_koord_yanlis (a b : ℝ) :
    ((3 - Real.sqrt 5) / 2 + 1 / 100) * (a ^ 2 + b ^ 2) ≤ 2 * a ^ 2 + 2 * a * b + b ^ 2 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith [sq_nonneg ((1 + Real.sqrt 5) * a + 2 * b), h5, hs, sq_nonneg a, sq_nonneg b]

end TW

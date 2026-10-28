import Mathlib

/-!
# NEGATIF KONTROL (TwBoyutYanlis_v2.lean) -- derleme DUSMELI

`TW.esitlik`'in d >= N + 1 varsayimi atilirsa denklik YANLIS olur:
d = 1, N = 5, L birebir: dim W = 0 = max(0, d - N - 1) (esitlik var) ama rank L = 1 != 6.
omega bu dogal sayi karsi ornegi yuzunden kaniti kuramamali.
-/

open Module

namespace TW

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem esitlik_yanlis (N : ℕ) (L : V →ₗ[ℝ] (Fin (N + 1) → ℝ)) :
    finrank ℝ (LinearMap.ker L) = finrank ℝ V - (N + 1) ↔
      finrank ℝ (LinearMap.range L) = N + 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker L
  have hr : finrank ℝ (LinearMap.range L) ≤ N + 1 := by
    have := (LinearMap.range L).finrank_le
    rwa [Module.finrank_fin_fun] at this
  constructor <;> intro hh <;> omega

end TW

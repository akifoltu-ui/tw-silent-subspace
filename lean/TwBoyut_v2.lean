import Mathlib

/-!
# T-W: sessiz altuzayin boyutu  (TwBoyut_v2.lean)

Kaynak: M. A. Oltulu, "The dimension of silent subspaces in finite-sampling truncations
of the Weil quadratic form" (2026), Teorem 3, Sonuc 4, Onerme 5.

v2 (2026-10-28, ifade sadakati denetimi): v1'in uc teoremi AYNEN korundu; Teorem 3'un
esitlik kosulu ("alt sinirda esitlik <-> kosullar bagimsiz") genel d icin eklendi:
  * `esitlik`        : d >= N + 1 iken  dim W = d - (N+1)  <->  rank L = N + 1;
  * `esitlik_kucuk`  : d <= N + 1 iken alt sinir 0'dir ve esitlik  <->  rank L = d (L birebir).
"Kosullar bagimsiz" = L'nin N+1 satiri dogrusal bagimsiz = rank L = N + 1.
d <= N araliginda N+1 kosul d boyutta bagimsiz olamaz; esitlik orada L'nin birebirligi demektir
(negatif kontrol: kontrol/TwBoyutYanlis_v2.lean -- niteleyicisiz denklik reddedilir).

Soyut kurulum: V gercel, sonlu boyutlu (d = finrank V); L : V -> R^(N+1) dogrusal
(N ornekleme kosulu + 1 kutup kosulu); W = ker L sessiz altuzay.
Dogal sayi cikarmasi kesik oldugu icin `d - (N+1)` ifadesi makaledeki
max(0, d - N - 1) alt sinirinin birebir aynisidir.
-/

open Module

namespace TW

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- Teorem 3: dim W = d - rank L  ve  dim W >= max(0, d - N - 1). -/
theorem boyut (N : ℕ) (L : V →ₗ[ℝ] (Fin (N + 1) → ℝ)) :
    finrank ℝ (LinearMap.ker L) = finrank ℝ V - finrank ℝ (LinearMap.range L) ∧
    finrank ℝ V - (N + 1) ≤ finrank ℝ (LinearMap.ker L) := by
  have h := LinearMap.finrank_range_add_finrank_ker L
  have hr : finrank ℝ (LinearMap.range L) ≤ N + 1 := by
    have := (LinearMap.range L).finrank_le
    rwa [Module.finrank_fin_fun] at this
  constructor <;> omega

/-- Teorem 3, esitlik kosulu (d >= N + 1): dim W = d - (N + 1)  <->  rank L = N + 1. -/
theorem esitlik (N : ℕ) (L : V →ₗ[ℝ] (Fin (N + 1) → ℝ)) (hd : N + 1 ≤ finrank ℝ V) :
    finrank ℝ (LinearMap.ker L) = finrank ℝ V - (N + 1) ↔
      finrank ℝ (LinearMap.range L) = N + 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker L
  have hr : finrank ℝ (LinearMap.range L) ≤ N + 1 := by
    have := (LinearMap.range L).finrank_le
    rwa [Module.finrank_fin_fun] at this
  constructor <;> intro hh <;> omega

/-- Teorem 3, esitlik kosulu (d <= N + 1): alt sinir 0; esitlik  <->  rank L = d (L birebir). -/
theorem esitlik_kucuk (N : ℕ) (L : V →ₗ[ℝ] (Fin (N + 1) → ℝ)) (hd : finrank ℝ V ≤ N + 1) :
    finrank ℝ (LinearMap.ker L) = finrank ℝ V - (N + 1) ↔
      finrank ℝ (LinearMap.range L) = finrank ℝ V := by
  have h := LinearMap.finrank_range_add_finrank_ker L
  constructor <;> intro hh <;> omega

/-- Sonuc 4 (tasarim kurali d = N + 3): dim W >= 2, ve dim W = 2  <->  rank L = N + 1. -/
theorem tasarim (N : ℕ) (L : V →ₗ[ℝ] (Fin (N + 1) → ℝ)) (hd : finrank ℝ V = N + 3) :
    2 ≤ finrank ℝ (LinearMap.ker L) ∧
    (finrank ℝ (LinearMap.ker L) = 2 ↔ finrank ℝ (LinearMap.range L) = N + 1) := by
  have h := LinearMap.finrank_range_add_finrank_ker L
  have hr : finrank ℝ (LinearMap.range L) ≤ N + 1 := by
    have := (LinearMap.range L).finrank_le
    rwa [Module.finrank_fin_fun] at this
  exact ⟨by omega, ⟨fun _ => by omega, fun _ => by omega⟩⟩

/-- Onerme 5 (sessizlik): ornekleme haritasinin cekirdeginde
agirlikli ic-bant toplami  sum_j a_j * (E eta)_j^2  sifirdir. -/
theorem sessizlik {N : ℕ} (E : V →ₗ[ℝ] (Fin N → ℝ)) (a : Fin N → ℝ) (η : V)
    (hη : η ∈ LinearMap.ker E) : ∑ j, a j * (E η j) ^ 2 = 0 := by
  rw [LinearMap.mem_ker] at hη
  simp [hη]

end TW

-- Hangi aksiyomlara dayaniyor? Beklenen: yalniz [propext, Classical.choice, Quot.sound]
#print axioms TW.boyut
#print axioms TW.esitlik
#print axioms TW.esitlik_kucuk
#print axioms TW.tasarim
#print axioms TW.sessizlik

import Mathlib

/-!
# NEGATIF KONTROL (TwMinMaksYanlis_v2.lean) -- bu dosya DERLENMEMELI.
Sayim lemmasini bilerek bir fazla iddia ediyoruz: (c'yi asmayan ozdeger sayisi) >= dim H + 1.
Yanlis (ornek: H = E iken sayi en fazla n = dim H). Ayni kanit adimlarinda boyut sayimi
(omega) kesisimin bos olmadigini artik gosteremez; hata beklenir.
-/

open InnerProductSpace Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem sayim_yanlis {n : ℕ} (hn : finrank ℝ E = n) (K : E →ₗ[ℝ] E) (hK : K.IsSymmetric)
    (H : Submodule ℝ E) (c : ℝ) (hH : ∀ w ∈ H, ⟪K w, w⟫_ℝ ≤ c * ‖w‖ ^ 2) :
    finrank ℝ H + 1 ≤ (Finset.univ.filter (fun i => hK.eigenvalues hn i ≤ c)).card := by
  classical
  -- dusuk (c'yi asmayan) indisler ve koordinat haritasi P x = (<e_i, x>)_{i dusuk}
  let low := Finset.univ.filter (fun i => hK.eigenvalues hn i ≤ c)
  let P : E →ₗ[ℝ] (low → ℝ) :=
    { toFun := fun x j => ⟪hK.eigenvectorBasis hn j.1, x⟫_ℝ
      map_add' := fun x y => by ext j; simp [inner_add_right]
      map_smul' := fun r x => by ext j; simp [real_inner_smul_right] }
  have hrange : finrank ℝ (LinearMap.range P) ≤ low.card := by
    have := (LinearMap.range P).finrank_le
    simpa using this
  have hrn := LinearMap.finrank_range_add_finrank_ker P
  by_contra hcon
  have hcon' := not_le.mp hcon
  -- omega icin: let ile adlandirilan low.card ile filtre sayisi ayni
  have hlc : low.card = (Finset.univ.filter (fun i => hK.eigenvalues hn i ≤ c)).card := rfl
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq H (LinearMap.ker P)
  have hsup := (H ⊔ LinearMap.ker P).finrank_le
  have hpos : 1 ≤ finrank ℝ (H ⊓ LinearMap.ker P : Submodule ℝ E) := by omega
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp (Submodule.one_le_finrank_iff.mp hpos)
  obtain ⟨hxH, hxP⟩ := Submodule.mem_inf.mp hx
  -- dusuk indislerde koordinat sifir
  have hlow0 : ∀ i, hK.eigenvalues hn i ≤ c → ⟪hK.eigenvectorBasis hn i, x⟫_ℝ = 0 := by
    intro i hi
    have hmem : i ∈ low := by simp [low, hi]
    have := congrFun (LinearMap.mem_ker.mp hxP) ⟨i, hmem⟩
    simpa [P] using this
  -- K e_i = lambda_i e_i
  have hKe : ∀ i, ⟪hK.eigenvectorBasis hn i, K x⟫_ℝ
      = hK.eigenvalues hn i * ⟪hK.eigenvectorBasis hn i, x⟫_ℝ := by
    intro i
    rw [← hK (hK.eigenvectorBasis hn i) x, hK.apply_eigenvectorBasis hn i]
    simp [real_inner_smul_left]
  -- Parseval
  have hKxx : ⟪K x, x⟫_ℝ = ∑ i, hK.eigenvalues hn i * ⟪hK.eigenvectorBasis hn i, x⟫_ℝ ^ 2 := by
    rw [← (hK.eigenvectorBasis hn).sum_inner_mul_inner (K x) x]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [real_inner_comm (hK.eigenvectorBasis hn i) (K x), hKe i]
    ring
  have hxx : ‖x‖ ^ 2 = ∑ i, ⟪hK.eigenvectorBasis hn i, x⟫_ℝ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← (hK.eigenvectorBasis hn).sum_inner_mul_inner x x]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [real_inner_comm (hK.eigenvectorBasis hn i) x]
    ring
  -- x != 0 ise sifir olmayan bir koordinat var
  have hex : ∃ i, ⟪hK.eigenvectorBasis hn i, x⟫_ℝ ≠ 0 := by
    by_contra hall
    have hall' : ∀ i, ⟪hK.eigenvectorBasis hn i, x⟫_ℝ = 0 := fun i => by
      by_contra h
      exact hall ⟨i, h⟩
    apply hx0
    have h0 : ‖x‖ ^ 2 = 0 := by rw [hxx]; simp [hall']
    simpa using h0
  obtain ⟨i0, hi0⟩ := hex
  have hgt : 0 < ∑ i, (hK.eigenvalues hn i - c) * ⟪hK.eigenvectorBasis hn i, x⟫_ℝ ^ 2 := by
    apply Finset.sum_pos'
    · intro i _
      by_cases hi : hK.eigenvalues hn i ≤ c
      · simp [hlow0 i hi]
      · have hd : 0 < hK.eigenvalues hn i - c := by linarith [not_le.mp hi]
        exact mul_nonneg hd.le (sq_nonneg _)
    · refine ⟨i0, Finset.mem_univ _, ?_⟩
      have hi0' : ¬ hK.eigenvalues hn i0 ≤ c := fun h => hi0 (hlow0 i0 h)
      have h1 : 0 < hK.eigenvalues hn i0 - c := by linarith [not_le.mp hi0']
      have h2 : 0 < ⟪hK.eigenvectorBasis hn i0, x⟫_ℝ ^ 2 := by positivity
      exact mul_pos h1 h2
  have hrw : ∑ i, (hK.eigenvalues hn i - c) * ⟪hK.eigenvectorBasis hn i, x⟫_ℝ ^ 2
      = ⟪K x, x⟫_ℝ - c * ‖x‖ ^ 2 := by
    rw [hKxx, hxx, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hb := hH x hxH
  linarith [hgt, hrw, hb]


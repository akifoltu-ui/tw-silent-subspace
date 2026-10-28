import Mathlib

/-!
# T-W (1): min-maks siniri, sayim bicimi  (TwMinMaks_v2.lean)

v2: v1'de omega, let ile adlandirilan low.card ile filtre sayisini ayri sandi (tek hata);
`hlc := rfl` eklendi. push_neg (kaldirilmasi onerilen) yerine elle yazilmis esdegerler.

Kaynak: M. A. Oltulu (2026), Bolum 4, esitsizlik (1):  lambda_{k-1}(K) <= max_{w in H, |w|=1} <w, C w>,
K = B + C, H = ker B, k = dim H.

Courant-Fischer'e gerek birakmayan esdeger bicim:
  K'nin c'yi ASMAYAN ozdegerlerinin sayisi >= dim H     (ozdegerler artan siradaysa: lambda_{k-1} <= c).
Genel lemma `sayim`: H uzerinde <Kw,w> <= c |w|^2 ise sonuc tutar.
Kanit: c'yi asan ozvektorlerin altuzayi >= n - m boyutlu (rank-nullity); dim H > m olsaydi H ile kesisirdi;
kesisimde x != 0 icin  <Kx,x> - c|x|^2 = sum (lambda_i - c) a_i^2 > 0  (Parseval)  -- celiski.
-/

open InnerProductSpace Module

namespace TW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Genel sayim lemmasi. -/
theorem sayim {n : ℕ} (hn : finrank ℝ E = n) (K : E →ₗ[ℝ] E) (hK : K.IsSymmetric)
    (H : Submodule ℝ E) (c : ℝ) (hH : ∀ w ∈ H, ⟪K w, w⟫_ℝ ≤ c * ‖w‖ ^ 2) :
    finrank ℝ H ≤ (Finset.univ.filter (fun i => hK.eigenvalues hn i ≤ c)).card := by
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

/-- Makaledeki (1): K = B + C, H = ker B. <w, C w> <= c |w|^2 (w in ker B) ise
K'nin c'yi asmayan ozdeger sayisi >= dim ker B, yani (artan sirada) lambda_{k-1}(K) <= c. -/
theorem minmaks {n : ℕ} (hn : finrank ℝ E = n) (B C : E →ₗ[ℝ] E)
    (hK : (B + C).IsSymmetric) (c : ℝ)
    (hC : ∀ w ∈ LinearMap.ker B, ⟪C w, w⟫_ℝ ≤ c * ‖w‖ ^ 2) :
    finrank ℝ (LinearMap.ker B) ≤ (Finset.univ.filter (fun i => hK.eigenvalues hn i ≤ c)).card := by
  apply sayim hn (B + C) hK (LinearMap.ker B) c
  intro w hw
  have hBw : B w = 0 := LinearMap.mem_ker.mp hw
  rw [LinearMap.add_apply, hBw, zero_add]
  exact hC w hw

end TW

#print axioms TW.sayim
#print axioms TW.minmaks

import Mathlib

/-!
# NEGATIF KONTROL (TwCekirdekDisiYanlis_v1.lean) -- bu dosya DERLENMEMELI.
Onerme 7'yi C >= 0 varsayimi OLMADAN ayni kanitla deniyoruz.
C negatif deger alabilirse lambda, <Bw,w>'nin altina dusebilir ve sinir coker;
son adim (nlinarith) basarisiz olmali.
-/

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem cekirdek_disi_yanlis (B C : E →ₗ[ℝ] E) (hBsym : B.IsSymmetric)
    {b lam : ℝ} (hb : 0 < b)
    (hbound : ∀ x ∈ (LinearMap.ker B)ᗮ, b * ‖x‖ ^ 2 ≤ ⟪B x, x⟫_ℝ)
    {v h w : E} (hv : (B + C) v = lam • v) (hn : ‖v‖ = 1)
    (hdec : v = h + w) (hh : h ∈ LinearMap.ker B) (hw : w ∈ (LinearMap.ker B)ᗮ) :
    ‖w‖ ^ 2 ≤ lam / b := by
  have hBh : B h = 0 := LinearMap.mem_ker.mp hh
  have h1 : ⟪(B + C) v, v⟫_ℝ = lam := by
    rw [hv, real_inner_smul_left, real_inner_self_eq_norm_sq, hn]
    ring
  have h2 : ⟪(B + C) v, v⟫_ℝ = ⟪B v, v⟫_ℝ + ⟪C v, v⟫_ℝ := by
    rw [LinearMap.add_apply, inner_add_left]
  have h3 : ⟪B v, v⟫_ℝ = ⟪B w, w⟫_ℝ := by
    have hsym : ⟪B w, h⟫_ℝ = 0 := by
      rw [hBsym w h, hBh, inner_zero_right]
    rw [hdec, map_add, hBh, zero_add, inner_add_right, hsym, zero_add]
  have h4 := hbound w hw
  rw [le_div_iff₀ hb]
  nlinarith [h1, h2, h3, h4]

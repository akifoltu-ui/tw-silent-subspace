import Mathlib

/-!
# T-W Onerme 7: cekirdek disi sinir  (TwCekirdekDisi_v1.lean)

Kaynak: M. A. Oltulu (2026), Onerme 7.
K = B + C, B simetrik, C >= 0, H = ker B, H'nin dik tumleyeninde B >= b > 0.
K v = lambda v, ||v|| = 1 ise  ||P_{H-dik} v||^2 <= lambda / b.

Izdusum yerine esdeger ayrisim: v = h + w, h in ker B, w dik ker B.
Bu ayrisim tektir; w = P_{H-dik} v.
Kanit: lambda = <Bv,v> + <Cv,v> >= <Bw,w> >= b ||w||^2   (<Bw,h> = <w,Bh> = 0).
-/

open InnerProductSpace

namespace TW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem cekirdek_disi (B C : E →ₗ[ℝ] E) (hBsym : B.IsSymmetric)
    (hC : ∀ x, 0 ≤ ⟪C x, x⟫_ℝ) {b lam : ℝ} (hb : 0 < b)
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
  have h5 := hC v
  rw [le_div_iff₀ hb]
  nlinarith [h1, h2, h3, h4, h5]

end TW

#print axioms TW.cekirdek_disi

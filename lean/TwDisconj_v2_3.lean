/-
  TwDisconj_v2_3.lean  --  M. A. Oltulu.

  KUTUP EVCILLIGI LEMMASI, TAM HALI.

  v1 birinci parcayi kanitliyordu: Phi (0,y)'de pozitifse Phi' y > 0.
  v2 BOOTSTRAP'i ekler: oradan "Phi hic sifirlanmaz" sonucuna gecis.

  Arka plan: prolate denklemi saf sanal eksende
        ((1 + y^2) Phi')' = (chi + c^2 y^2) Phi,   katsayi POZITIF
  haline gelir; denklem disconjugate'tir. Integre edilmis hali:
        p y * Phi' y = integral_0^y q u * Phi u du,   p > 0, q > 0.

  ISPAT FIKRI (bootstrap): Phi sifirlanirsa ilk sifirlanma noktasi y1 vardir
  (kapali kume + kompaktlik). [0,y1) uzerinde Phi > 0 oldugundan birinci parca
  (0,y1) icinde Phi' > 0 verir; o zaman Phi [0,y1] uzerinde KESIN ARTANDIR,
  yani Phi y1 > Phi 0 > 0 -- Phi y1 <= 0 ile celisir.

  v2 -> v2.1 : push_neg -> push Not.
  v2.1 -> v2.2 : `apply` ile parcalandi, tipler acik yazildi.
  v2.2 -> v2.3 : asil sorun IMPORT yolu idi. `strictMonoOn_of_deriv_pos`
               Mathlib/Analysis/Calculus/Deriv/MeanValue.lean icinde, yani
               modul adi Mathlib.Analysis.Calculus.Deriv.MeanValue.

  `sorry` YOKTUR.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.Compact

namespace TWDisconj

open Set intervalIntegral

variable {p q Φ : ℝ → ℝ}

/-- BIRINCI PARCA (v1'den): `Φ` acik `(0,y)` araliginda pozitifse `Φ' y > 0`. -/
theorem deriv_pos_of_pos_on
    (hp : ∀ u, 0 < p u) (hq : ∀ u, 0 < q u)
    (hqc : Continuous q) (hΦc : Continuous Φ)
    (hint : ∀ y, p y * deriv Φ y = ∫ u in (0:ℝ)..y, q u * Φ u)
    {y : ℝ} (hy : 0 < y) (hpos : ∀ u ∈ Ioo (0:ℝ) y, 0 < Φ u) :
    0 < deriv Φ y := by
  have hinteg : IntervalIntegrable (fun u => q u * Φ u) MeasureTheory.volume 0 y :=
    (hqc.mul hΦc).intervalIntegrable 0 y
  have hI : 0 < ∫ u in (0:ℝ)..y, q u * Φ u := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hinteg ?_ hy
    intro x hx
    exact mul_pos (hq x) (hpos x hx)
  have hey := hint y
  nlinarith [hp y, hI, hey]

/-- BOOTSTRAP (soyut): `Φ 0 > 0` ve "pozitif kaldikca turev pozitif" ozelligi
    verildiginde `Φ` hic sifirlanmaz. -/
theorem pos_of_deriv_pos_bootstrap
    (hΦc : Continuous Φ) (h0 : 0 < Φ 0)
    (hd : ∀ y : ℝ, 0 < y → (∀ u ∈ Ioo (0:ℝ) y, 0 < Φ u) → 0 < deriv Φ y) :
    ∀ y : ℝ, 0 ≤ y → 0 < Φ y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y₀, hy₀0, hy₀le⟩ := hcon
  -- sifirlanma kumesi
  set Z : Set ℝ := Icc (0:ℝ) y₀ ∩ Φ ⁻¹' (Iic 0) with hZdef
  have hZsub : Z ⊆ Icc (0:ℝ) y₀ := inter_subset_left
  have hZne : Z.Nonempty := ⟨y₀, ⟨⟨hy₀0, le_refl _⟩, hy₀le⟩⟩
  have hZcl : IsClosed Z :=
    isClosed_Icc.inter (IsClosed.preimage hΦc isClosed_Iic)
  have hZcp : IsCompact Z := isCompact_Icc.of_isClosed_subset hZcl hZsub
  obtain ⟨y₁, hy₁mem, hy₁least⟩ := hZcp.exists_isLeast hZne
  have hy₁I : y₁ ∈ Icc (0:ℝ) y₀ := hZsub hy₁mem
  have hy₁le : Φ y₁ ≤ 0 := hy₁mem.2
  -- y₁ > 0, cunku Φ 0 > 0
  have hy₁pos : 0 < y₁ := by
    rcases lt_or_eq_of_le hy₁I.1 with h | h
    · exact h
    · exfalso; rw [← h] at hy₁le; linarith
  -- [0,y₁) uzerinde Φ > 0
  have hposlt : ∀ u, 0 ≤ u → u < y₁ → 0 < Φ u := by
    intro u hu0 hul
    by_contra hneg
    push Not at hneg
    have : u ∈ Z := ⟨⟨hu0, le_trans (le_of_lt hul) hy₁I.2⟩, hneg⟩
    exact absurd (hy₁least this) (not_le.mpr hul)
  -- (0,y₁) uzerinde turev pozitif
  have hderiv : ∀ x ∈ interior (Icc (0:ℝ) y₁), 0 < deriv Φ x := by
    intro x hx
    rw [interior_Icc] at hx
    exact hd x hx.1 (fun u hu => hposlt u (le_of_lt hu.1) (lt_trans hu.2 hx.2))
  -- kesin artan
  have hconv : Convex ℝ (Icc (0:ℝ) y₁) := convex_Icc (0:ℝ) y₁
  have hcont : ContinuousOn Φ (Icc (0:ℝ) y₁) := hΦc.continuousOn
  have hmono : StrictMonoOn Φ (Icc (0:ℝ) y₁) := by
    apply strictMonoOn_of_deriv_pos hconv hcont
    exact hderiv
  have : Φ 0 < Φ y₁ :=
    hmono (left_mem_Icc.mpr (le_of_lt hy₁pos)) (right_mem_Icc.mpr (le_of_lt hy₁pos)) hy₁pos
  linarith

/-- TAM LEMMA: integral hipotezi + `Φ 0 > 0`  =>  `Φ` her `y >= 0` icin pozitif. -/
theorem pos_of_integral_eq
    (hp : ∀ u, 0 < p u) (hq : ∀ u, 0 < q u)
    (hqc : Continuous q) (hΦc : Continuous Φ)
    (hint : ∀ y, p y * deriv Φ y = ∫ u in (0:ℝ)..y, q u * Φ u)
    (h0 : 0 < Φ 0) :
    ∀ y : ℝ, 0 ≤ y → 0 < Φ y :=
  pos_of_deriv_pos_bootstrap hΦc h0
    (fun _y hy hpos => deriv_pos_of_pos_on hp hq hqc hΦc hint hy hpos)

#print axioms TWDisconj.deriv_pos_of_pos_on
#print axioms TWDisconj.pos_of_deriv_pos_bootstrap
#print axioms TWDisconj.pos_of_integral_eq

end TWDisconj

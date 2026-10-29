/-
  TwRank_v1_2.lean  --  M. A. Oltulu, "The dimension of silent subspaces in finite-
  sampling truncations of the Weil quadratic form" (Zenodo 10.5281/zenodo.22730006).

  Teorem 3'un ESITLIK kosulunu sayisal sertifikaya baglayan halka:
      G = L * L^T  pozitif tanimli  =>  rank L = (satir sayisi)  =>  dim W = d - n.
  Aralik LDL sertifikasi tam olarak G'nin pozitif tanimliligini verir.
  Hipotezin GEREKLILIGI ayri dosyada kanitli: TwRankKarsiOrnek_v1.lean.

  v1   -> v1.1 : linter uyarisi (kullanilmayan DecidableEq d)
  v1.1 -> v1.2 : `omit ... in` docstring'den SONRA gelemez (sozdizimi hatasi).
                 Cozum: [DecidableEq d] hic bildirilmiyor -- zaten kullanilmiyor.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank

namespace TW

open Matrix

variable {n d : Type*} [Fintype n] [DecidableEq n] [Fintype d]

/-- Gram matrisi `L * Lᵀ` pozitif tanimli ise `L` tam satir rankina sahiptir. -/
theorem rank_of_gram_posDef (L : Matrix n d ℝ) (hG : (L * Lᵀ).PosDef) :
    L.rank = Fintype.card n := by
  have hdet : (L * Lᵀ).det ≠ 0 := ne_of_gt hG.det_pos
  have hU : IsUnit (L * Lᵀ) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hdet
  have h1 : (L * Lᵀ).rank = Fintype.card n := Matrix.rank_of_isUnit _ hU
  have h2 : (L * Lᵀ).rank ≤ L.rank := Matrix.rank_mul_le_left _ _
  have h3 : L.rank ≤ Fintype.card n := Matrix.rank_le_card_height _
  omega

/-- Teorem 3'un esitlik hali: Gram pozitif tanimli ise cekirdek boyutu TAM olarak
    `d - n`. Makalede `rank L = N+1` ile `dim W = d - N - 1`. -/
theorem dimW_eq_of_gram_posDef (L : Matrix n d ℝ) (hG : (L * Lᵀ).PosDef) :
    Fintype.card d - L.rank = Fintype.card d - Fintype.card n := by
  rw [rank_of_gram_posDef L hG]

#print axioms TW.rank_of_gram_posDef
#print axioms TW.dimW_eq_of_gram_posDef

end TW

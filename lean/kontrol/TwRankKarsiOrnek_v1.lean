/-
  TwRankKarsiOrnek_v1.lean  --  NEGATIF KONTROL, `sorry` YOK.

  TwRank_v1_1'deki PosDef hipotezi GEREKLIDIR: yari-tanimli (PosSemidef) ile
  ayni sonuc YANLIStir. Asagidaki teorem bunu KANITLAR (L = 0 karsi ornegi).
  Bu dosya hatasiz derlenirse negatif kontrol gecmis demektir:
  hipotez gevsetildiginde iddia coker.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank

namespace TWKontrol

open Matrix

/-- PosSemidef hipotezi YETMEZ: sifir matris karsi ornektir. -/
theorem posSemidef_yetmez :
    ¬ (∀ L : Matrix (Fin 1) (Fin 1) ℝ,
        (L * Lᵀ).PosSemidef → L.rank = Fintype.card (Fin 1)) := by
  intro h
  have hps : ((0 : Matrix (Fin 1) (Fin 1) ℝ) * (0 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ).PosSemidef := by
    simpa using (Matrix.PosSemidef.zero (n := Fin 1) (R := ℝ))
  have := h 0 hps
  simp at this

#print axioms TWKontrol.posSemidef_yetmez

end TWKontrol

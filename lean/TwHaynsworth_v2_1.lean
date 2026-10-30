/-
  TwHaynsworth_v2_1.lean  --  M. A. Oltulu.

  KUTUP INDIRGEMESI (Haynsworth / Schur tumleyeni) -- cebirsel cekirdek.

  Olculen olgu (haynsworth_v1.py, 2026-10-30, dort hucre d = 13,17,21,25):
    kutupsuz geometrik form G = -W - Pr icin kappa(G) = 1 (tek negatif yon);
    kutup vektoru w ile  s := <w, G^-1 w> = -e^{L/2}/2 < 0  (d'den BAGIMSIZ,
    KAPALI FORM); kutup kosulunun dik altuzayinda kappa = 0 ve lam_min > 0.
    Negatif kontrol: rastgele vektorde kappa_perp = 1 KALDI (mekanizma kutupa ozgu).

  Cebirsel icerik: TEK negatif yon, kutup kosulu tarafindan TAM OLARAK tuketilir.

  v1 -> v2 : v1'de toplamlar `congr`/`rfl` ile elle acilmaya calisildi ve
             `ring_nf` zinciri koptu. Burada once BILINEERLIK ayri lemmalarla
             kurulur, acilim ondan cikar.
  v2 -> v2.1 : `linarith` bu Mathlib surumunde yok; `add_nonpos` kullanildi.
             `sorry` YOK.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric

namespace TWHayn

open Matrix Finset

variable {n : Type*} [Fintype n]

/-- Bilineer form: `B M x y = ∑_{i,j} x_i M_{ij} y_j`. -/
def B (M : Matrix n n ℝ) (x y : n → ℝ) : ℝ := ∑ i, ∑ j, x i * M i j * y j

/-- Kuadratik form. -/
def Q (M : Matrix n n ℝ) (x : n → ℝ) : ℝ := B M x x

theorem B_add_left (M : Matrix n n ℝ) (x y z : n → ℝ) :
    B M (fun i => x i + y i) z = B M x z + B M y z := by
  simp only [B, add_mul, Finset.sum_add_distrib]

theorem B_smul_left (M : Matrix n n ℝ) (c : ℝ) (x z : n → ℝ) :
    B M (fun i => c * x i) z = c * B M x z := by
  simp only [B, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem B_add_right (M : Matrix n n ℝ) (x y z : n → ℝ) :
    B M x (fun j => y j + z j) = B M x y + B M x z := by
  simp only [B, mul_add, Finset.sum_add_distrib]

theorem B_smul_right (M : Matrix n n ℝ) (c : ℝ) (x z : n → ℝ) :
    B M x (fun j => c * z j) = c * B M x z := by
  simp only [B, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Simetrik matriste bilineer form simetriktir. -/
theorem B_symm (M : Matrix n n ℝ) (hM : M.IsSymm) (x y : n → ℝ) :
    B M x y = B M y x := by
  have hs : ∀ a b : n, M a b = M b a := fun a b => congrFun (congrFun hM.eq b) a
  simp only [B]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hs b a]; ring

/-- ACILIM: `Q M (a·x + b·z) = a² Q M x + 2ab B M x z + b² Q M z`. -/
theorem Q_lin_comb (M : Matrix n n ℝ) (hM : M.IsSymm) (x z : n → ℝ) (a b : ℝ) :
    Q M (fun i => a * x i + b * z i)
      = a ^ 2 * Q M x + 2 * (a * b) * B M x z + b ^ 2 * Q M z := by
  have e1 : B M (fun i => a * x i + b * z i) (fun i => a * x i + b * z i)
      = B M (fun i => a * x i) (fun i => a * x i + b * z i)
        + B M (fun i => b * z i) (fun i => a * x i + b * z i) := B_add_left _ _ _ _
  have e2 : B M (fun i => a * x i) (fun i => a * x i + b * z i)
      = a * (b * B M x z) + a * (a * B M x x) := by
    rw [B_smul_left, B_add_right, B_smul_right, B_smul_right]; ring
  have e3 : B M (fun i => b * z i) (fun i => a * x i + b * z i)
      = b * (a * B M z x) + b * (b * B M z z) := by
    rw [B_smul_left, B_add_right, B_smul_right, B_smul_right]; ring
  have e4 : B M z x = B M x z := B_symm M hM z x
  simp only [Q]
  rw [e1, e2, e3, e4]; ring

/-- ANA CEKIRDEK: M-dik iki yon, biri `Q ≤ 0` digeri `Q < 0` ise, gerdikleri
    duzlemin HER noktasinda form `≤ 0`'dir -- yani negatif indeks en az 2. -/
theorem neg_plane_of_two_dirs
    (M : Matrix n n ℝ) (hM : M.IsSymm) (x z : n → ℝ)
    (hxz : B M x z = 0) (hx : Q M x ≤ 0) (hz : Q M z < 0) (a b : ℝ) :
    Q M (fun i => a * x i + b * z i) ≤ 0 := by
  rw [Q_lin_comb M hM x z a b, hxz, mul_zero, add_zero]
  have h1 : a ^ 2 * Q M x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) hx
  have h2 : b ^ 2 * Q M z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg b) (le_of_lt hz)
  exact add_nonpos h1 h2

/-- KUTUP INDIRGEMESI (soyut hal): `kappa(M) = 1` hipotezi altinda, kutup
    yonune M-dik hicbir yonde form `≤ 0` olamaz -- yani dik altuzayda
    `kappa = 0`. Hipotez, "ikinci bagimsiz negatif yon yoktur" biciminde. -/
theorem no_second_neg_dir
    (M : Matrix n n ℝ) (x z : n → ℝ)
    (hxz : B M x z = 0) (hz : Q M z < 0)
    (hkappa1 : ∀ u w : n → ℝ, B M u w = 0 → Q M u ≤ 0 → Q M w < 0 → u = 0) :
    Q M x ≤ 0 → x = 0 :=
  fun hx => hkappa1 x z hxz hx hz

#print axioms TWHayn.B_symm
#print axioms TWHayn.Q_lin_comb
#print axioms TWHayn.neg_plane_of_two_dirs
#print axioms TWHayn.no_second_neg_dir

end TWHayn

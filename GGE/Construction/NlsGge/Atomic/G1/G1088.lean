                                                                                                                                                                                                                                         
                                                                                                                                                  
import Mathlib
import NlsGge.Atomic.G1.G1062
import NlsGge.Atomic.G1.G1087

set_option autoImplicit false

open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.GK38.GradEigen38
  NlsGge.GK38.PoissonMixed38 NlsGge.GK38.PoissonDirichlet38 NlsGge.GK38.PoissonSpectral38
  NlsGge.Atomic.G1087S2.P6 NlsGge.Atomic.G1087S2.P8
open scoped Matrix.Norms.L2Operator

/- ===== verbatim definitions of DEFINITIONS/G1.lean.md used by the statement ===== -/
namespace NlsGge.GKDefinitionDesign
open NlsGge.Atomic.G1062S2 NlsGge.Atomic.G1061S1
noncomputable section

def normingError (φ : PotPair) (n : ℤ) (t : Time) : PairVec38 :=
  Complex.I • kappaKernel38 φ (muSeq φ n) t - (ePlus n t-eMinus n t)

def normingErrorTail (N : ℕ) (φ : PotPair) (n : ℤ) (t : Time) : PairVec38 :=
  if N ≤ n.natAbs then normingError φ n t else 0

end
end NlsGge.GKDefinitionDesign

namespace NlsGge.Atomic.G1088S1
noncomputable section

theorem mul_le3 {x y : ℂ} {A B : ℝ} (hx : ‖x‖ ≤ A) (hy : ‖y‖ ≤ B) : ‖x * y‖ ≤ A * B :=
  norm_mul_le_of_le hx hy

/-- algebraic core: the two gradient combinations at the entrywise-small perturbation of the free matrices. -/
theorem alg_core (a b σ M00 M01 M10 M11 L00 L01 L10 L11 : ℂ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hσ : ‖σ‖ = 1)
    (h00 : ‖M00 - a‖ ≤ s) (h01 : ‖M01‖ ≤ s) (h10 : ‖M10‖ ≤ s) (h11 : ‖M11 - b‖ ≤ s)
    (l00 : ‖L00 - σ‖ ≤ s) (l01 : ‖L01‖ ≤ s) (l10 : ‖L10‖ ≤ s) (l11 : ‖L11 - σ‖ ≤ s) :
    ‖L01 * (M10 * M10) + (L11 - L00) * (M10 * M11) - L10 * (M11 * M11)‖ ≤ 16 * s ∧
    ‖L01 * (M00 * M00) + (L11 - L00) * (M00 * M01) - L10 * (M01 * M01)‖ ≤ 16 * s ∧
    ‖L11 * (M10 * M10) + (L01 - L10) * (M10 * M11) - L00 * (M11 * M11) - σ * (-(b * b))‖ ≤ 16 * s ∧
    ‖L11 * (M00 * M00) + (L01 - L10) * (M00 * M01) - L00 * (M01 * M01) - σ * (a * a)‖ ≤ 16 * s := by
  have nM00 : ‖M00‖ ≤ 2 := by
    calc ‖M00‖ = ‖(M00 - a) + a‖ := by ring_nf
      _ ≤ ‖M00 - a‖ + ‖a‖ := norm_add_le _ _
      _ ≤ 2 := by linarith
  have nM11 : ‖M11‖ ≤ 2 := by
    calc ‖M11‖ = ‖(M11 - b) + b‖ := by ring_nf
      _ ≤ ‖M11 - b‖ + ‖b‖ := norm_add_le _ _
      _ ≤ 2 := by linarith
  have nL00 : ‖L00‖ ≤ 2 := by
    calc ‖L00‖ = ‖(L00 - σ) + σ‖ := by ring_nf
      _ ≤ ‖L00 - σ‖ + ‖σ‖ := norm_add_le _ _
      _ ≤ 2 := by linarith
  have nL11 : ‖L11‖ ≤ 2 := by
    calc ‖L11‖ = ‖(L11 - σ) + σ‖ := by ring_nf
      _ ≤ ‖L11 - σ‖ + ‖σ‖ := norm_add_le _ _
      _ ≤ 2 := by linarith
  have dLL : ‖L11 - L00‖ ≤ 2 * s := by
    calc ‖L11 - L00‖ = ‖(L11 - σ) - (L00 - σ)‖ := by ring_nf
      _ ≤ ‖L11 - σ‖ + ‖L00 - σ‖ := norm_sub_le _ _
      _ ≤ 2 * s := by linarith
  have dLO : ‖L01 - L10‖ ≤ 2 * s := by
    calc ‖L01 - L10‖ ≤ ‖L01‖ + ‖L10‖ := norm_sub_le _ _
      _ ≤ 2 * s := by linarith
  have pM10 : ‖M10 * M10‖ ≤ s * s := mul_le3 h10 h10
  have pM01 : ‖M01 * M01‖ ≤ s * s := mul_le3 h01 h01
  have pM10_11 : ‖M10 * M11‖ ≤ s * 2 := mul_le3 h10 nM11
  have pM00_01 : ‖M00 * M01‖ ≤ 2 * s := mul_le3 nM00 h01
  have pM00 : ‖M00 * M00‖ ≤ 2 * 2 := mul_le3 nM00 nM00
  have pM11 : ‖M11 * M11‖ ≤ 2 * 2 := mul_le3 nM11 nM11
  have s2 : s * s ≤ s := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc ‖L01 * (M10 * M10) + (L11 - L00) * (M10 * M11) - L10 * (M11 * M11)‖
        ≤ ‖L01 * (M10 * M10)‖ + ‖(L11 - L00) * (M10 * M11)‖ + ‖L10 * (M11 * M11)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ s * (s * s) + 2 * s * (s * 2) + s * (2 * 2) := by
          gcongr
          · exact mul_le3 l01 pM10
          · exact mul_le3 dLL pM10_11
          · exact mul_le3 l10 pM11
      _ ≤ 16 * s := by nlinarith [mul_nonneg hs0 hs0, mul_nonneg (mul_nonneg hs0 hs0) hs0]
  · calc ‖L01 * (M00 * M00) + (L11 - L00) * (M00 * M01) - L10 * (M01 * M01)‖
        ≤ ‖L01 * (M00 * M00)‖ + ‖(L11 - L00) * (M00 * M01)‖ + ‖L10 * (M01 * M01)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ s * (2 * 2) + 2 * s * (2 * s) + s * (s * s) := by
          gcongr
          · exact mul_le3 l01 pM00
          · exact mul_le3 dLL pM00_01
          · exact mul_le3 l10 pM01
      _ ≤ 16 * s := by nlinarith [mul_nonneg hs0 hs0, mul_nonneg (mul_nonneg hs0 hs0) hs0]
  · have e : L11 * (M10 * M10) + (L01 - L10) * (M10 * M11) - L00 * (M11 * M11) - σ * (-(b * b))
        = L11 * (M10 * M10) + (L01 - L10) * (M10 * M11) - (L00 - σ) * (M11 * M11)
          - σ * ((M11 - b) * (M11 + b)) := by ring
    have hp : ‖M11 + b‖ ≤ 3 := by
      calc ‖M11 + b‖ ≤ ‖M11‖ + ‖b‖ := norm_add_le _ _
        _ ≤ 3 := by linarith
    rw [e]
    calc ‖L11 * (M10 * M10) + (L01 - L10) * (M10 * M11) - (L00 - σ) * (M11 * M11)
            - σ * ((M11 - b) * (M11 + b))‖
        ≤ ‖L11 * (M10 * M10)‖ + ‖(L01 - L10) * (M10 * M11)‖ + ‖(L00 - σ) * (M11 * M11)‖
            + ‖σ * ((M11 - b) * (M11 + b))‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ 2 * (s * s) + 2 * s * (s * 2) + s * (2 * 2) + 1 * (s * 3) := by
          gcongr
          · exact mul_le3 nL11 pM10
          · exact mul_le3 dLO pM10_11
          · exact mul_le3 l00 pM11
          · rw [norm_mul, hσ, one_mul, one_mul]
            exact mul_le3 h11 hp
      _ ≤ 16 * s := by nlinarith [mul_nonneg hs0 hs0]
  · have e : L11 * (M00 * M00) + (L01 - L10) * (M00 * M01) - L00 * (M01 * M01) - σ * (a * a)
        = (L11 - σ) * (M00 * M00) + σ * ((M00 - a) * (M00 + a)) + (L01 - L10) * (M00 * M01)
          - L00 * (M01 * M01) := by ring
    have hp : ‖M00 + a‖ ≤ 3 := by
      calc ‖M00 + a‖ ≤ ‖M00‖ + ‖a‖ := norm_add_le _ _
        _ ≤ 3 := by linarith
    rw [e]
    calc ‖(L11 - σ) * (M00 * M00) + σ * ((M00 - a) * (M00 + a)) + (L01 - L10) * (M00 * M01)
            - L00 * (M01 * M01)‖
        ≤ ‖(L11 - σ) * (M00 * M00)‖ + ‖σ * ((M00 - a) * (M00 + a))‖ + ‖(L01 - L10) * (M00 * M01)‖
            + ‖L00 * (M01 * M01)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ s * (2 * 2) + 1 * (s * 3) + 2 * s * (2 * s) + 2 * (s * s) := by
          gcongr
          · exact mul_le3 l11 pM00
          · rw [norm_mul, hσ, one_mul, one_mul]
            exact mul_le3 h00 hp
          · exact mul_le3 dLO pM00_01
          · exact mul_le3 nL00 pM01
      _ ≤ 16 * s := by nlinarith [mul_nonneg hs0 hs0]


theorem lead_step (G σ ev lead : ℂ) {a b : ℝ} (hσσ : σ * σ = 1) (hσ : ‖σ‖ = 1)
    (h1 : ‖G - σ * ev‖ ≤ a) (h2 : ‖σ * lead - ev‖ ≤ b) : ‖G - lead‖ ≤ a + b := by
  have e : G - lead = (G - σ * ev) - σ * (σ * lead - ev) := by linear_combination lead * hσσ
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, hσ, one_mul]
  linarith

theorem norm_cexp_real_mul_I (x : ℝ) : ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

theorem sgn_neg (n : ℤ) : (-1 : ℂ) ^ n = Complex.exp ((n : ℂ) * (-((Real.pi : ℂ) * Complex.I))) := by
  rw [Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]; simp

theorem sgn_pos (n : ℤ) : (-1 : ℂ) ^ n = Complex.exp ((n : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
  rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem gd_sup (φ : PotPair) (z : ℂ) (n : ℤ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hM : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 → ∀ i j : Fin 2,
      ‖(∑' m : ℕ, potentialVolterraTerm38 φ z m u) i j -
        freeZsFundamentalComplex ((n : ℂ) * (Real.pi : ℂ)) u i j‖ ≤ s)
    (ε : ℂ) (hε : ‖ε‖ ≤ 1) (hzε : z = (n : ℂ) * (Real.pi : ℂ) + ε)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (k : Fin 2) :
    ‖GDf φ z t k‖ ≤ 16 * s ∧ ‖Gdf φ z t k - leadf z t k‖ ≤ 16 * s + 2 * ‖ε‖ := by
  set E : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun u => freeZsFundamentalComplex ((n : ℂ) * (Real.pi : ℂ)) u with hE
  set M : Matrix (Fin 2) (Fin 2) ℂ := ∑' m : ℕ, potentialVolterraTerm38 φ z m t with hMdef
  set L : Matrix (Fin 2) (Fin 2) ℂ := monodromyPair φ z with hLdef
  have hL : L = ∑' m : ℕ, potentialVolterraTerm38 φ z m 1 :=
    (NlsGge.Atomic.G1087S2.P5.bridge1 φ z).symm
  have hMt : ∀ i j : Fin 2, ‖M i j - E t i j‖ ≤ s := fun i j => hM t ht i j
  have hL1 : ∀ i j : Fin 2, ‖L i j - E 1 i j‖ ≤ s := by
    intro i j; rw [hL]; exact hM 1 ⟨zero_le_one, le_rfl⟩ i j
  have e00 : E t 0 0 = Complex.exp (((-(t * n * Real.pi) : ℝ) : ℂ) * Complex.I) := by
    rw [hE]; simp only []
    rw [NlsGge.Atomic.G1061S1.freeZs_00]; congr 1; push_cast; ring
  have e11 : E t 1 1 = Complex.exp (((t * n * Real.pi : ℝ) : ℂ) * Complex.I) := by
    rw [hE]; simp only []
    rw [NlsGge.Atomic.G1061S1.freeZs_11]; congr 1; push_cast; ring
  have e01 : E t 0 1 = 0 := NlsGge.Atomic.G1061S1.freeZs_01 _ _
  have e10 : E t 1 0 = 0 := NlsGge.Atomic.G1061S1.freeZs_10 _ _
  have f00 : E 1 0 0 = (-1 : ℂ) ^ n := by
    rw [hE]; simp only []
    rw [NlsGge.Atomic.G1061S1.freeZs_00, sgn_neg]; congr 1; push_cast; ring
  have f11 : E 1 1 1 = (-1 : ℂ) ^ n := by
    rw [hE]; simp only []
    rw [NlsGge.Atomic.G1061S1.freeZs_11, sgn_pos]; congr 1; push_cast; ring
  have f01 : E 1 0 1 = 0 := NlsGge.Atomic.G1061S1.freeZs_01 _ _
  have f10 : E 1 1 0 = 0 := NlsGge.Atomic.G1061S1.freeZs_10 _ _
  have nσ : ‖(-1 : ℂ) ^ n‖ = 1 := by simp
  have h00 : ‖M 0 0 - E t 0 0‖ ≤ s := hMt 0 0
  have h01 : ‖M 0 1‖ ≤ s := by simpa [e01] using hMt 0 1
  have h10 : ‖M 1 0‖ ≤ s := by simpa [e10] using hMt 1 0
  have h11 : ‖M 1 1 - E t 1 1‖ ≤ s := hMt 1 1
  have l00 : ‖L 0 0 - (-1 : ℂ) ^ n‖ ≤ s := by simpa [f00] using hL1 0 0
  have l01 : ‖L 0 1‖ ≤ s := by simpa [f01] using hL1 0 1
  have l10 : ‖L 1 0‖ ≤ s := by simpa [f10] using hL1 1 0
  have l11 : ‖L 1 1 - (-1 : ℂ) ^ n‖ ≤ s := by simpa [f11] using hL1 1 1
  have core := alg_core (E t 0 0) (E t 1 1) ((-1 : ℂ) ^ n) (M 0 0) (M 0 1) (M 1 0) (M 1 1)
    (L 0 0) (L 0 1) (L 1 0) (L 1 1) s hs0 hs1
    (by rw [e00]; exact norm_cexp_real_mul_I _) (by rw [e11]; exact norm_cexp_real_mul_I _) nσ
    h00 h01 h10 h11 l00 l01 l10 l11
  have bb : E t 1 1 * E t 1 1 = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)) := by
    rw [e11, ← Complex.exp_add]; congr 1; push_cast; ring
  have aa : E t 0 0 * E t 0 0 = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) * (t : ℂ)) := by
    rw [e00, ← Complex.exp_add]; congr 1; push_cast; ring
  have hlead := NlsGge.Atomic.G1087S2.U3.lead_diff_c n ε hε t ht z hzε k
  have σσ : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := NlsGge.Atomic.G1087S2.P3.neg_one_zpow_mul_self n
  fin_cases k
  · have ev0 : evec n t 0 = -(E t 1 1 * E t 1 1) := by
      rw [bb]; simp [evec]
    refine ⟨?_, ?_⟩
    · show ‖L 0 1 * (M 1 0 * M 1 0) + (L 1 1 - L 0 0) * (M 1 0 * M 1 1) - L 1 0 * (M 1 1 * M 1 1)‖ ≤ _
      exact core.1
    · show ‖L 1 1 * (M 1 0 * M 1 0) + (L 0 1 - L 1 0) * (M 1 0 * M 1 1) - L 0 0 * (M 1 1 * M 1 1) -
        leadf z t 0‖ ≤ _
      exact lead_step _ _ (evec n t 0) _ σσ nσ (by rw [ev0]; exact core.2.2.1) hlead
  · have ev1 : evec n t 1 = E t 0 0 * E t 0 0 := by
      rw [aa]; simp [evec]
    refine ⟨?_, ?_⟩
    · show ‖L 0 1 * (M 0 0 * M 0 0) + (L 1 1 - L 0 0) * (M 0 0 * M 0 1) - L 1 0 * (M 0 1 * M 0 1)‖ ≤ _
      exact core.2.1
    · show ‖L 1 1 * (M 0 0 * M 0 0) + (L 0 1 - L 1 0) * (M 0 0 * M 0 1) - L 0 0 * (M 0 1 * M 0 1) -
        leadf z t 1‖ ≤ _
      exact lead_step _ _ (evec n t 1) _ σσ nσ (by rw [ev1]; exact core.2.2.2) hlead

theorem E_entry_diff (n : ℤ) (ε z : ℂ) (hε : ‖ε‖ ≤ 1) (hz : z = (n : ℂ) * (Real.pi : ℂ) + ε) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    ‖freeZsFundamentalComplex z u i j - freeZsFundamentalComplex ((n : ℂ) * (Real.pi : ℂ)) u i j‖ ≤ 2 * ‖ε‖ := by
  have hε0 := norm_nonneg ε
  have hw : ∀ c : ℂ, c = Complex.I ∨ c = -Complex.I → ‖Complex.exp ((u : ℂ) * (c * ε)) - 1‖ ≤ 2 * ‖ε‖ := by
    intro c hc
    have hcn : ‖c‖ = 1 := by rcases hc with rfl | rfl <;> simp
    have h1 : ‖(u : ℂ) * (c * ε)‖ ≤ 1 := by
      rw [norm_mul, norm_mul, hcn, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1]
      nlinarith [hu.2]
    have := Complex.norm_exp_sub_one_le h1
    refine this.trans ?_
    rw [norm_mul, norm_mul, hcn, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1]
    nlinarith [hu.2]
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta]
    rw [NlsGge.Atomic.G1061S1.freeZs_00, NlsGge.Atomic.G1061S1.freeZs_00]
    have e : Complex.exp ((u : ℂ) * (-Complex.I * z)) =
        Complex.exp ((u : ℂ) * (-Complex.I * ((n : ℂ) * (Real.pi : ℂ)))) *
          Complex.exp ((u : ℂ) * (-Complex.I * ε)) := by
      rw [← Complex.exp_add, hz]; congr 1; ring
    have hn1 : ‖Complex.exp ((u : ℂ) * (-Complex.I * ((n : ℂ) * (Real.pi : ℂ))))‖ = 1 := by
      have : (u : ℂ) * (-Complex.I * ((n : ℂ) * (Real.pi : ℂ))) = ((-(u * n * Real.pi) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this]; exact Complex.norm_exp_ofReal_mul_I _
    rw [e]
    have : Complex.exp ((u : ℂ) * (-Complex.I * ((n : ℂ) * (Real.pi : ℂ)))) *
          Complex.exp ((u : ℂ) * (-Complex.I * ε)) - Complex.exp ((u : ℂ) * (-Complex.I * ((n : ℂ) * (Real.pi : ℂ)))) =
        Complex.exp ((u : ℂ) * (-Complex.I * ((n : ℂ) * (Real.pi : ℂ)))) *
          (Complex.exp ((u : ℂ) * (-Complex.I * ε)) - 1) := by ring
    rw [this, norm_mul, hn1, one_mul]
    have := hw (-Complex.I) (Or.inr rfl)
    simpa [mul_assoc] using this
  · simp [NlsGge.Atomic.G1061S1.freeZs_01]
  · simp [NlsGge.Atomic.G1061S1.freeZs_10]
  · simp only [Fin.mk_one]
    rw [NlsGge.Atomic.G1061S1.freeZs_11, NlsGge.Atomic.G1061S1.freeZs_11]
    have e : Complex.exp ((u : ℂ) * (Complex.I * z)) =
        Complex.exp ((u : ℂ) * (Complex.I * ((n : ℂ) * (Real.pi : ℂ)))) *
          Complex.exp ((u : ℂ) * (Complex.I * ε)) := by
      rw [← Complex.exp_add, hz]; congr 1; ring
    have hn1 : ‖Complex.exp ((u : ℂ) * (Complex.I * ((n : ℂ) * (Real.pi : ℂ))))‖ = 1 := by
      have : (u : ℂ) * (Complex.I * ((n : ℂ) * (Real.pi : ℂ))) = (((u * n * Real.pi) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this]; exact Complex.norm_exp_ofReal_mul_I _
    rw [e]
    have : Complex.exp ((u : ℂ) * (Complex.I * ((n : ℂ) * (Real.pi : ℂ)))) *
          Complex.exp ((u : ℂ) * (Complex.I * ε)) - Complex.exp ((u : ℂ) * (Complex.I * ((n : ℂ) * (Real.pi : ℂ)))) =
        Complex.exp ((u : ℂ) * (Complex.I * ((n : ℂ) * (Real.pi : ℂ)))) *
          (Complex.exp ((u : ℂ) * (Complex.I * ε)) - 1) := by ring
    rw [this, norm_mul, hn1, one_mul]
    exact hw Complex.I (Or.inl rfl)

open NlsGge.Atomic.G1062S2 in
theorem sup_M (B : ℝ) (hB : 0 ≤ B) :
    ∃ CS Cε : ℝ, ∀ φ : PotPair, H1B B φ →
      ∃ S : ℤ → ℝ, (∀ n, 0 ≤ S n) ∧ SB (fun n : ℤ => S n ^ 2) CS ∧
        (∀ n : ℤ, ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
          ‖(∑' m : ℕ, potentialVolterraTerm38 φ (muSeq φ n) m t) -
            freeZsFundamentalComplex ((n : ℂ) * (Real.pi : ℂ)) t‖ ≤ S n) ∧
        SB (fun n : ℤ => ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) Cε := by
  obtain ⟨R2c, hR2c⟩ := unif_l2 B hB
  set R0 : ℝ := Real.sqrt (1 + (2 * Real.pi) ^ 2) * B with hR0
  set R2 : ℝ := Real.sqrt (|R2c|) with hR2
  obtain ⟨CG, hCG⟩ := (NlsGge.Atomic.G1021S2.G1021_whole).2 R0 R2
  refine ⟨|CG|, R2c, fun φ hφ => ?_⟩
  have hK : φ ∈ NlsGge.Atomic.G1049S1.Cset B := NlsGge.Atomic.G1049S1.mem_Cset φ hφ.1 hφ.2
  obtain ⟨h1, h2, hsob⟩ := H1B_sob hφ
  obtain ⟨a, b, hpa, hpb, hAa, hAb, hint, hH1, hterm⟩ := pair_rep φ h1 h2
  obtain ⟨hsum, hle⟩ := hR2c φ hK
  have hH1R : Real.sqrt (∫ s in (0 : ℝ)..1,
      (‖a s‖ ^ 2 + ‖deriv a s‖ ^ 2 + ‖b s‖ ^ 2 + ‖deriv b s‖ ^ 2)) ≤ R0 := by
    rw [hR0]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    calc _ ≤ (1 + (2 * Real.pi) ^ 2) * (‖physicalSobolevL2 1 φ.1 h1‖ ^ 2 + ‖physicalSobolevL2 1 φ.2 h2‖ ^ 2) := hH1
      _ ≤ (1 + (2 * Real.pi) ^ 2) * B ^ 2 :=
        mul_le_mul_of_nonneg_left hsob (by positivity)
  have hξ : Summable (fun n : ℤ => ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ∧
      Real.sqrt (∑' n : ℤ, ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ≤ R2 := by
    refine ⟨hsum, ?_⟩
    rw [hR2]
    exact Real.sqrt_le_sqrt (hle.trans (le_abs_self _))
  obtain ⟨S, hSs, hSC, hSb⟩ := (hCG a b hpa hpb hAa hAb hint hH1R (muSeq φ) hξ).1
  have hsq : ∀ n : ℤ, |S n| ^ 2 = S n ^ 2 := fun n => sq_abs _
  refine ⟨fun n => |S n|, fun n => abs_nonneg _, ⟨?_, ?_⟩, ?_, ⟨hsum, hle⟩⟩
  · simpa only [hsq] using hSs
  · simp only [hsq]; exact hSC.trans (le_abs_self _)
  · intro n t ht
    have hb := hSb n t ht.1 ht.2
    have hM : (∑' m : ℕ, freeKernelVolterraTerm38 a b (muSeq φ n) m t) =
        ∑' m : ℕ, potentialVolterraTerm38 φ (muSeq φ n) m t :=
      tsum_congr fun m => hterm (muSeq φ n) m t ht
    rw [hM] at hb
    exact hb.trans (le_abs_self _)

open NlsGge.Atomic.G1049S1 in
theorem unif_err (B : ℝ) (hB : 0 ≤ B) :
    ∃ N : ℕ, ∀ φ ∈ Cset B, ∀ n : ℤ, N < n.natAbs →
      muSeq φ n ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4) ∧ dirichletChar φ (muSeq φ n) = 0 ∧
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        ‖(∑' m : ℕ, potentialVolterraTerm38 φ (muSeq φ n) m t) -
          freeZsFundamentalComplex (muSeq φ n) t‖ ≤ 3 / 200 := by
  choose V hV N hN using fun φ₀ : PotPair =>
    NlsGge.Atomic.G1087S2.Uniform.err_small φ₀ (3 / 200) (by norm_num)
  obtain ⟨t, -, hcov⟩ := (isCompact_Cset hB).elim_nhds_subcover V (fun x _ => hV x)
  refine ⟨∑ x ∈ t, N x, fun φ hφ n hn => ?_⟩
  obtain ⟨x, hx, hφx⟩ := Set.mem_iUnion₂.1 (hcov hφ)
  refine hN x φ hφx n (lt_of_le_of_lt ?_ hn)
  exact Finset.single_le_sum (f := fun x => N x) (fun _ _ => Nat.zero_le _) hx

theorem sq4 (a b c d : ℝ) : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d),
    sq_nonneg (c - d)]

open NlsGge.GKDefinitionDesign in
theorem per_phi_sup (φ : PotPair) (N : ℕ) (C19 C20 C29 CS Cε : ℝ)
    (hEd : ∀ z : ℂ, DifferentiableAt ℂ (fun w : ℂ => freeZsFundamentalComplex w 1) z)
    (hroot : ∀ n : ℤ, N < n.natAbs → dirichletChar φ (muSeq φ n) = 0 ∧
      muSeq φ n ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4))
    (hsm : ∀ n : ℤ, N < n.natAbs → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ‖(∑' m : ℕ, potentialVolterraTerm38 φ (muSeq φ n) m t) - freeZsFundamentalComplex (muSeq φ n) t‖ ≤ 3 / 200)
    (h19 : SB (fun n : ℤ => ‖(∑' m : ℕ, potentialVolterraTerm38 φ (muSeq φ n) m 1) -
      freeZsFundamentalComplex (muSeq φ n) 1‖ ^ 2) C19)
    (h20a : ∀ n : ℤ, DifferentiableAt ℂ (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m 1) (muSeq φ n))
    (h20b : SB (fun n : ℤ => ‖deriv (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m 1) (muSeq φ n) -
      deriv (fun w : ℂ => freeZsFundamentalComplex w 1) (muSeq φ n)‖ ^ 2) C20)
    (h29 : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ k : Fin 2,
      SB (fun n : ℤ => ‖GDf φ (muSeq φ n) t k‖ ^ 2) C29 ∧
      SB (fun n : ℤ => ‖Gdf φ (muSeq φ n) t k - leadf (muSeq φ n) t k‖ ^ 2) C29)
    (S : ℤ → ℝ) (hS0 : ∀ n, 0 ≤ S n) (hSS : SB (fun n : ℤ => S n ^ 2) CS)
    (hSM : ∀ n : ℤ, ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ‖(∑' m : ℕ, potentialVolterraTerm38 φ (muSeq φ n) m t) -
        freeZsFundamentalComplex ((n : ℂ) * (Real.pi : ℂ)) t‖ ≤ S n)
    (hεS : SB (fun n : ℤ => ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) Cε) :
    (∀ n : ℤ, N < n.natAbs → parity n * normingFactor φ (muSeq φ n) ∈ Complex.slitPlane) ∧
    (∀ n : ℤ, BddAbove (Set.range (fun t : Time => ‖normingErrorTail (N + 1) φ n t‖))) ∧
    SB (fun n : ℤ => (kernelSup (normingErrorTail (N + 1) φ n)) ^ 2)
      (16 * (172 ^ 2 * max C20 0 + 214 ^ 2 * max C19 0 + 32 ^ 2 * max CS 0 + 4 * max Cε 0)) := by
  have hbr := NlsGge.Atomic.G1087S2.P5.bridge1 φ
  have hpc := NlsGge.Atomic.G1087S2.U5c.per_phi_c φ N (muSeq φ) C19 C20 C29 hEd hroot hsm h19 h20a h20b h29
  have e2 : (fun w : ℂ => ∑' m : ℕ, potentialVolterraTerm38 φ w m 1) = fun w : ℂ => monodromyPair φ w :=
    funext hbr
  rw [e2] at h20a h20b
  obtain ⟨d, hdeq⟩ : ∃ d : ℤ → ℝ, ∀ n, d n = ‖monodromyPair φ (muSeq φ n) -
      freeZsFundamentalComplex (muSeq φ n) 1‖ := ⟨_, fun _ => rfl⟩
  obtain ⟨g, hgeq⟩ : ∃ g : ℤ → ℝ, ∀ n, g n = ‖deriv (fun w : ℂ => monodromyPair φ w) (muSeq φ n) -
      deriv (fun w : ℂ => freeZsFundamentalComplex w 1) (muSeq φ n)‖ := ⟨_, fun _ => rfl⟩
  have hd1 : SB (fun n : ℤ => d n ^ 2) C19 := by
    have e : (fun n : ℤ => ‖(∑' m : ℕ, potentialVolterraTerm38 φ (muSeq φ n) m 1) -
        freeZsFundamentalComplex (muSeq φ n) 1‖ ^ 2) = fun n : ℤ => d n ^ 2 := by
      funext n; rw [hdeq n, hbr]
    rw [e] at h19; exact h19
  have hg1 : SB (fun n : ℤ => g n ^ 2) C20 := by
    have e : (fun n : ℤ => ‖deriv (fun w : ℂ => monodromyPair φ w) (muSeq φ n) -
        deriv (fun w : ℂ => freeZsFundamentalComplex w 1) (muSeq φ n)‖ ^ 2) = fun n : ℤ => g n ^ 2 := by
      funext n; rw [hgeq n]
    rw [e] at h20b; exact h20b
  have hd0 : ∀ n, 0 ≤ d n := fun n => by rw [hdeq n]; exact norm_nonneg _
  have hg0 : ∀ n, 0 ≤ g n := fun n => by rw [hgeq n]; exact norm_nonneg _
  have hdsm : ∀ n : ℤ, N < n.natAbs → d n ≤ 3 / 200 := by
    intro n hn
    have := hsm n hn 1 ⟨zero_le_one, le_rfl⟩
    rw [hbr] at this
    rw [hdeq n]; exact this
  have hεd : ∀ n : ℤ, N < n.natAbs → ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 10 * d n := by
    intro n hn
    obtain ⟨h0, hb⟩ := hroot n hn
    obtain ⟨-, heps⟩ := NlsGge.Atomic.G1087S2.U2.root_facts φ hb h0
    rw [hdeq n]; exact heps
  set W : ℤ → ℝ := fun n => 2 * (172 * g n + 214 * d n + 32 * S n + 2 * ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖)
    with hWdef
  have hW0 : ∀ n, 0 ≤ W n := fun n => by
    have := hg0 n; have := hd0 n; have := hS0 n
    have := norm_nonneg (muSeq φ n - (n : ℂ) * (Real.pi : ℂ))
    simp only [hWdef]; positivity
  have hpt : ∀ (n : ℤ) (t : Time), ‖normingErrorTail (N + 1) φ n t‖ ≤ W n := by
    intro n t
    by_cases hn : N < n.natAbs
    · have hn' : N + 1 ≤ n.natAbs := hn
      have htail : normingErrorTail (N + 1) φ n t = normingError φ n t := by
        simp only [normingErrorTail, if_pos hn']
      rw [htail]
      have hne : normingError φ n t =
          Complex.I • pairKernelExt38 (kappaKernel38 φ (muSeq φ n)) t.1 - evec n t.1 := by
        rw [normingError, NlsGge.GKDefinitionDesign.time_ext (kappaKernel38 φ (muSeq φ n)) t]
        funext k
        fin_cases k
        · simp [ePlus, eMinus, evec]
        · simp [ePlus, eMinus, evec]
      rw [hne]
      refine (pi_norm_le_iff_of_nonneg (hW0 n)).2 (fun k => ?_)
      obtain ⟨h0, hb⟩ := hroot n hn
      have hεn := hεd n hn
      have hdn := hdsm n hn
      have hε1 : ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 1 := by linarith
      have hk := NlsGge.Atomic.G1087S2.U5b.grad_term_c φ (muSeq φ n) n t.2 k (d n) (g n) (hdeq n).ge hdn h0 hb
        (hsm n hn) (h20a n) (hEd _) (hgeq n).ge
      have hMent : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) 1 → ∀ i j : Fin 2,
          ‖(∑' m : ℕ, potentialVolterraTerm38 φ (muSeq φ n) m u) i j -
            freeZsFundamentalComplex ((n : ℂ) * (Real.pi : ℂ)) u i j‖ ≤ min (S n) 1 := by
        intro u hu i j
        refine le_min ?_ ?_
        · have := NlsGge.Atomic.G1061S1.norm_entry_le_l2
            ((∑' m : ℕ, potentialVolterraTerm38 φ (muSeq φ n) m u) -
              freeZsFundamentalComplex ((n : ℂ) * (Real.pi : ℂ)) u) i j
          simp only [Matrix.sub_apply] at this
          exact this.trans (hSM n u hu)
        · have h1 := NlsGge.Atomic.G1061S1.norm_entry_le_l2
            ((∑' m : ℕ, potentialVolterraTerm38 φ (muSeq φ n) m u) -
              freeZsFundamentalComplex (muSeq φ n) u) i j
          simp only [Matrix.sub_apply] at h1
          have h2 := h1.trans (hsm n hn u hu)
          have h3 := E_entry_diff n (muSeq φ n - (n : ℂ) * (Real.pi : ℂ)) (muSeq φ n) hε1
            (by ring) hu i j
          calc _ = ‖((∑' m : ℕ, potentialVolterraTerm38 φ (muSeq φ n) m u) i j -
                  freeZsFundamentalComplex (muSeq φ n) u i j) +
                (freeZsFundamentalComplex (muSeq φ n) u i j -
                  freeZsFundamentalComplex ((n : ℂ) * (Real.pi : ℂ)) u i j)‖ := by ring_nf
            _ ≤ _ := norm_add_le _ _
            _ ≤ 1 := by linarith
      have hgd := gd_sup φ (muSeq φ n) n (min (S n) 1) (le_min (hS0 n) zero_le_one) (min_le_right _ _)
        hMent (muSeq φ n - (n : ℂ) * (Real.pi : ℂ)) hε1 (by ring) t.2 k
      have hs : min (S n) 1 ≤ S n := min_le_left _ _
      refine hk.trans ?_
      simp only [hWdef]
      nlinarith [hgd.1, hgd.2, hs, hS0 n, hd0 n, hg0 n]
    · have hn' : ¬ (N + 1 ≤ n.natAbs) := hn
      have htail : normingErrorTail (N + 1) φ n t = 0 := by
        simp only [normingErrorTail, if_neg hn']
      rw [htail, norm_zero]; exact hW0 n
  have hks : ∀ n : ℤ, BddAbove (Set.range (fun t : Time => ‖normingErrorTail (N + 1) φ n t‖)) ∧
      0 ≤ kernelSup (normingErrorTail (N + 1) φ n) ∧ kernelSup (normingErrorTail (N + 1) φ n) ≤ W n :=
    fun n => NlsGge.GKDefinitionDesign.kernelSup_le_of _ (hW0 n) (hpt n)
  have hmaj : SB (fun n : ℤ => 16 * (172 ^ 2 * g n ^ 2 + 214 ^ 2 * d n ^ 2 + 32 ^ 2 * S n ^ 2 +
      4 * ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2))
      (16 * (172 ^ 2 * max C20 0 + 214 ^ 2 * max C19 0 + 32 ^ 2 * max CS 0 + 4 * max Cε 0)) := by
    have h := ((((hg1.weak (le_max_left C20 (0 : ℝ))).smul (172 ^ 2) (by positivity)).add
      ((hd1.weak (le_max_left C19 (0 : ℝ))).smul (214 ^ 2) (by positivity))).add
      ((hSS.weak (le_max_left CS (0 : ℝ))).smul (32 ^ 2) (by positivity))).add
      ((hεS.weak (le_max_left Cε (0 : ℝ))).smul 4 (by norm_num))
    exact h.smul 16 (by norm_num)
  refine ⟨hpc.1, fun n => (hks n).1, ?_⟩
  refine SB.mono (fun n => sq_nonneg _) (fun n => ?_) hmaj
  have hk0 := (hks n).2.1
  have hkW := (hks n).2.2
  have h1 : kernelSup (normingErrorTail (N + 1) φ n) ^ 2 ≤ W n ^ 2 := pow_le_pow_left₀ hk0 hkW 2
  refine h1.trans ?_
  have h4 := sq4 (172 * g n) (214 * d n) (32 * S n) (2 * ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖)
  simp only [hWdef]
  nlinarith [h4]

open NlsGge.GKDefinitionDesign NlsGge.Atomic.G1062S2 in
theorem G1_088_main (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ φ : PotPair,
      pairSobolev 1 φ → pairSobolevNorm 1 φ ≤ B →
      (∀ n : ℤ, N ≤ n.natAbs →
        simpleDirichlet φ (muSeq φ n) ∧
        parity n * normingFactor φ (muSeq φ n) ∈ Complex.slitPlane) ∧
      (∀ n : ℤ,
        BddAbove (Set.range (fun t : Time => ‖normingErrorTail N φ n t‖))) ∧
      Summable (fun n : ℤ => (kernelSup (normingErrorTail N φ n))^2) ∧
      (∑' n : ℤ, (kernelSup (normingErrorTail N φ n))^2) ≤ C := by
  obtain ⟨C62, hC62, N62, h62⟩ := NlsGge.GKDefinitionDesign.G1_062 B hB
  obtain ⟨NU, hNU⟩ := unif_err B hB
  obtain ⟨CS, Cε, hSup⟩ := sup_M B hB
  obtain ⟨R0', hR0'⟩ := (NlsGge.Atomic.G1049S1.isCompact_Cset hB).isBounded.exists_norm_le
  obtain ⟨R2c, hR2c⟩ := unif_l2 B hB
  set R0 : ℝ := 2 * max R0' 0 with hR0
  set R1 : ℝ := Real.sqrt (max Cε 0) with hR1
  obtain ⟨C19, h19⟩ := NlsGge.Atomic.G1087S2.K29.K20.K19.G1019_whole R0 R1
  obtain ⟨C20, h20⟩ := NlsGge.Atomic.G1087S2.K29.K20.G1020_whole R0 R1
  obtain ⟨C29, h29⟩ := NlsGge.Atomic.G1087S2.K29.G1029_main R0 R1
  set CC : ℝ := 16 * (172 ^ 2 * max C20 0 + 214 ^ 2 * max C19 0 + 32 ^ 2 * max CS 0 + 4 * max Cε 0) with hCC
  refine ⟨max CC 0 + 1, by positivity, max N62 NU + 1, fun φ hs hn => ?_⟩
  have hH : H1B B φ := pro_to_H1B B φ hs hn
  have hK : φ ∈ NlsGge.Atomic.G1049S1.Cset B := NlsGge.Atomic.G1049S1.mem_Cset φ hH.1 hH.2
  obtain ⟨S, hS0, hSS, hSM, hεS⟩ := hSup φ hH
  have hφR : Real.sqrt (‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2) ≤ R0 := by
    have hφn : ‖φ‖ ≤ R0' := hR0' φ hK
    have h1 : ‖φ.1‖ ≤ ‖φ‖ := norm_fst_le φ
    have h2 : ‖φ.2‖ ≤ ‖φ‖ := norm_snd_le φ
    have hm : R0' ≤ max R0' 0 := le_max_left _ _
    have := norm_nonneg φ.1; have := norm_nonneg φ.2; have := norm_nonneg φ
    refine Real.sqrt_le_iff.2 ⟨by rw [hR0]; positivity, ?_⟩
    rw [hR0]; nlinarith
  have hξb : ∀ n : ℤ, ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ R1 := by
    intro n
    have := SB.le_sqrt hεS n
    simpa [hR1, abs_of_nonneg (norm_nonneg _)] using this
  have hroot : ∀ n : ℤ, max N62 NU < n.natAbs → dirichletChar φ (muSeq φ n) = 0 ∧
      muSeq φ n ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4) := fun n hn => by
    obtain ⟨hb, h0, -⟩ := hNU φ hK n (lt_of_le_of_lt (le_max_right _ _) hn)
    exact ⟨h0, hb⟩
  have hsm : ∀ n : ℤ, max N62 NU < n.natAbs → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ‖(∑' m : ℕ, potentialVolterraTerm38 φ (muSeq φ n) m t) -
        freeZsFundamentalComplex (muSeq φ n) t‖ ≤ 3 / 200 := fun n hn t ht => by
    obtain ⟨-, -, hs'⟩ := hNU φ hK n (lt_of_le_of_lt (le_max_right _ _) hn)
    exact hs' t ht
  have h19v : SB (fun n : ℤ => ‖(∑' m : ℕ, potentialVolterraTerm38 φ (muSeq φ n) m 1) -
      freeZsFundamentalComplex (muSeq φ n) 1‖ ^ 2) C19 := h19 φ (muSeq φ) hφR hξb 1 zero_le_one le_rfl
  have h20v := h20 φ (muSeq φ) hφR hξb 1 zero_le_one le_rfl
  have h29v : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ k : Fin 2,
      SB (fun n : ℤ => ‖GDf φ (muSeq φ n) t k‖ ^ 2) C29 ∧
      SB (fun n : ℤ => ‖Gdf φ (muSeq φ n) t k - leadf (muSeq φ n) t k‖ ^ 2) C29 := by
    obtain ⟨-, -, -, h29'⟩ := h29 φ (muSeq φ) hφR hξb
    exact fun t h0 h1 k => h29' t h0 h1 k
  have hEd : ∀ z : ℂ, DifferentiableAt ℂ (fun w : ℂ => freeZsFundamentalComplex w 1) z :=
    fun z => (NlsGge.Atomic.G1087S2.K29.K20.differentiable_E 1) z
  obtain ⟨hslit, hbdd, hsumb⟩ := per_phi_sup φ (max N62 NU) C19 C20 C29 CS Cε hEd hroot hsm h19v h20v.1
    h20v.2 h29v S hS0 hSS hSM hεS
  obtain ⟨hsd, -⟩ := h62 φ hs hn
  refine ⟨fun n hn' => ⟨(hsd n (le_trans (le_trans (le_max_left _ _) (Nat.le_succ _)) hn')).1,
    hslit n (Nat.lt_of_succ_le hn')⟩, hbdd, hsumb.1, hsumb.2.trans ?_⟩
  linarith [le_max_left CC 0]

end
end NlsGge.Atomic.G1088S1

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G1_088 (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ φ : PotPair,
      pairSobolev 1 φ → pairSobolevNorm 1 φ ≤ B →
      (∀ n : ℤ, N ≤ n.natAbs →
        simpleDirichlet φ (muSeq φ n) ∧
        parity n * normingFactor φ (muSeq φ n) ∈ Complex.slitPlane) ∧
      (∀ n : ℤ,
        BddAbove (Set.range (fun t : Time => ‖normingErrorTail N φ n t‖))) ∧
      Summable (fun n : ℤ => (kernelSup (normingErrorTail N φ n))^2) ∧
      (∑' n : ℤ, (kernelSup (normingErrorTail N φ n))^2) ≤ C :=
  NlsGge.Atomic.G1088S1.G1_088_main B hB

end
end NlsGge.GKDefinitionDesign

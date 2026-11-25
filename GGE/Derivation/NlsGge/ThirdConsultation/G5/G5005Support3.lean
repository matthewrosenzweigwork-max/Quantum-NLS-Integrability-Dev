import Mathlib
import NlsGge.Atomic.G5.G5005Host
import NlsGge.ThirdConsultation.G5.G5005Support1
import NlsGge.Atomic.G1.G1087

/- G5-005 SUPPORT3 (proof development, AUTHOR; not self-reviewed, not accepted). Target
   NlsGge/ThirdConsultation/G5/G5005Support3.lean, namespace NlsGge.ThirdConsultation.G5005Support3.
   Fixed-time algebra for the fifth conjunct of G5-005 (q_n * grad delta(mu_n) - (i/2)(fourier difference)):
   * the kernel gradAntiDiscrim38 equals -i times the G1-029 star-product expression Gdf;
   * |leadf x - leadf y| <= |x - y| for real x, y and t in [0,1];
   * leadf (n pi) = (-1)^n * fkD n;
   * the pointwise three-term estimate. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.G5005Support1

namespace NlsGge.ThirdConsultation.G5005Support3
noncomputable section

theorem gradAnti_eq_Gdf (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (k : Fin 2) :
    gradAntiDiscrim38 φ z t k = -Complex.I * NlsGge.Atomic.G1087S2.P6.Gdf φ z t k := by
  have hM : ∀ i j, (∑' m : ℕ, NlsGge.Atomic.Volterra.potentialVolterraTerm38 φ z m t) i j =
      fundPair φ z ⟨t, ht⟩ i j := NlsGge.Atomic.G1087S2.P1.series_eq_fundPair φ z ht
  have hc : ∀ i j, fundColumn38 φ z t j i = fundPair φ z ⟨t, ht⟩ i j :=
    NlsGge.Atomic.G1087S2.P1.fundColumn_eq φ z ht
  unfold NlsGge.Atomic.G1087S2.P6.Gdf gradAntiDiscrim38 starProd38
  simp only [hM, hc]
  fin_cases k <;> simp

theorem expI_diff (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ |a - b| := by
  have h : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) =
      Complex.exp (Complex.I * (b : ℂ)) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    have e : Complex.I * (b : ℂ) + Complex.I * ((a - b : ℝ) : ℂ) = Complex.I * (a : ℂ) := by
      push_cast; ring
    rw [mul_sub, ← Complex.exp_add, e, mul_one]
  rw [h, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, Complex.norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs, abs_mul, abs_two]
  have := Real.abs_sin_le_abs (x := (a - b) / 2)
  rw [abs_div, abs_two] at this
  linarith

theorem lead_dist (x y t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (k : Fin 2) :
    ‖NlsGge.Atomic.G1087S2.P6.leadf (x : ℂ) t k - NlsGge.Atomic.G1087S2.P6.leadf (y : ℂ) t k‖ ≤
      |x - y| := by
  have habs : |1 - 2 * t| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hx : ∀ w : ℝ, Complex.I * (w : ℂ) * (1 - 2 * (t : ℂ)) = Complex.I * ((w * (1 - 2 * t) : ℝ) : ℂ) := by
    intro w; push_cast; ring
  have hx' : ∀ w : ℝ, -(Complex.I * (w : ℂ) * (1 - 2 * (t : ℂ))) =
      Complex.I * ((-(w * (1 - 2 * t)) : ℝ) : ℂ) := by
    intro w; push_cast; ring
  have key : ∀ a b : ℝ, |a * (1 - 2 * t) - b * (1 - 2 * t)| ≤ |a - b| := by
    intro a b
    have : a * (1 - 2 * t) - b * (1 - 2 * t) = (a - b) * (1 - 2 * t) := by ring
    rw [this, abs_mul]
    calc |a - b| * |1 - 2 * t| ≤ |a - b| * 1 := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
      _ = |a - b| := mul_one _
  fin_cases k
  · show ‖NlsGge.Atomic.G1087S2.P6.leadf (x : ℂ) t 0 - NlsGge.Atomic.G1087S2.P6.leadf (y : ℂ) t 0‖ ≤ |x - y|
    simp only [NlsGge.Atomic.G1087S2.P6.leadf, Matrix.cons_val_zero, hx' x, hx' y]
    rw [neg_sub_neg]
    refine (expI_diff _ _).trans ?_
    rw [neg_sub_neg]
    exact key x y
  · show ‖NlsGge.Atomic.G1087S2.P6.leadf (x : ℂ) t 1 - NlsGge.Atomic.G1087S2.P6.leadf (y : ℂ) t 1‖ ≤ |x - y|
    simp only [NlsGge.Atomic.G1087S2.P6.leadf, Matrix.cons_val_one, hx x, hx y]
    refine (expI_diff _ _).trans ?_
    exact key x y

theorem lead0_eq (n : ℤ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (k : Fin 2) :
    NlsGge.Atomic.G1087S2.P6.leadf ((n : ℂ) * (Real.pi : ℂ)) t k =
      (-1 : ℂ) ^ n * pairKernelExt38 (fkD n) t k := by
  have hpi : Complex.exp ((n : ℂ) * (-((Real.pi : ℂ) * Complex.I))) = (-1 : ℂ) ^ n := by
    rw [Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
    simp
  have hpi' : Complex.exp ((n : ℂ) * ((Real.pi : ℂ) * Complex.I)) = (-1 : ℂ) ^ n := by
    rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
  fin_cases k
  · show NlsGge.Atomic.G1087S2.P6.leadf ((n : ℂ) * (Real.pi : ℂ)) t 0 =
      (-1 : ℂ) ^ n * pairKernelExt38 (fkD n) t 0
    rw [fkD_apply0 n ht]
    simp only [NlsGge.Atomic.G1087S2.P6.leadf, Matrix.cons_val_zero]
    have e : -(Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * (1 - 2 * (t : ℂ))) =
        (n : ℂ) * (-((Real.pi : ℂ) * Complex.I)) + 2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I := by ring
    rw [e, Complex.exp_add, hpi]
    ring
  · show NlsGge.Atomic.G1087S2.P6.leadf ((n : ℂ) * (Real.pi : ℂ)) t 1 =
      (-1 : ℂ) ^ n * pairKernelExt38 (fkD n) t 1
    rw [fkD_apply1 n ht]
    simp only [NlsGge.Atomic.G1087S2.P6.leadf, Matrix.cons_val_one, Matrix.cons_val_zero]
    have e : Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * (1 - 2 * (t : ℂ)) =
        (n : ℂ) * ((Real.pi : ℂ) * Complex.I) + -(2 * (Real.pi : ℂ) * (n : ℂ) * (t : ℂ) * Complex.I) := by ring
    rw [e, Complex.exp_add, hpi']

theorem norm_lead0 (n : ℤ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (k : Fin 2) :
    ‖NlsGge.Atomic.G1087S2.P6.leadf ((n : ℂ) * (Real.pi : ℂ)) t k‖ = 1 := by
  rw [lead0_eq n ht k]
  fin_cases k
  · show ‖(-1 : ℂ) ^ n * pairKernelExt38 (fkD n) t 0‖ = 1
    rw [fkD_apply0 n ht, norm_mul, norm_neg, Complex.norm_exp]
    simp
  · show ‖(-1 : ℂ) ^ n * pairKernelExt38 (fkD n) t 1‖ = 1
    rw [fkD_apply1 n ht, norm_mul, Complex.norm_exp]
    simp

/-- Three-term estimate behind the fifth conjunct. -/
theorem core_bound (q q0 Gd L L0 D s : ℂ) (M a e r : ℝ) (hD : D = s * L0) (hq0 : q0 = -s / 2)
    (hq : ‖q‖ ≤ M) (hG : ‖Gd - L‖ ≤ a) (hL : ‖L - L0‖ ≤ e) (hr : ‖q - q0‖ ≤ r) (hL0 : ‖L0‖ = 1) :
    ‖q * (-Complex.I * Gd) - (Complex.I / 2) * D‖ ≤ M * a + M * e + r := by
  have h : q * (-Complex.I * Gd) - (Complex.I / 2) * D =
      -Complex.I * (q * (Gd - L) + q * (L - L0) + (q - q0) * L0) := by
    subst hD; subst hq0; ring
  have hM : 0 ≤ M := le_trans (norm_nonneg _) hq
  rw [h, norm_mul, norm_neg, Complex.norm_I, one_mul]
  refine (norm_add_le _ _).trans ?_
  refine add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_
  · rw [norm_mul]; exact mul_le_mul hq hG (norm_nonneg _) hM
  · rw [norm_mul]; exact mul_le_mul hq hL (norm_nonneg _) hM
  · rw [norm_mul, hL0, mul_one]; exact hr

end
end NlsGge.ThirdConsultation.G5005Support3

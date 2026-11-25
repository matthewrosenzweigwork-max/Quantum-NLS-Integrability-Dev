import NlsGge.Definitions.PilotInterfaces
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Abstract change of variables and Gaussian/disk volume bound (S-CV, F05.08-.10)

Source: `paper/v2.tex` lines 1224-1312 (F:prop:ball).  Abstract statement: if `Ψ` is injective
on a measurable set `B`, has real Jacobian `|det| ≥ 1/2` there, fixes the low coordinates
(which lie in the disk of radius `R`), and `E` dominates the high weighted quadratic energy of
`Ψ`, then `∫_B e^{-E} ≤ 2 ∏_{low} π R² ∏_{high} π/(ρ a)`.  All integrals are `ℝ≥0∞`.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace NlsGge.Schur

open NlsGge.Pilot

instance planeVolume_isAddHaar38 (N : ℕ) : (planeVolume N).IsAddHaarMeasure := by
  unfold planeVolume; infer_instance

/-- Product formula for the lintegral of a product of single-coordinate nonneg integrable
functions over the plane. -/
theorem lintegral_plane_prod38 (N : ℕ) (h : Fin (2 * N + 1) → ℂ → ℝ)
    (hnn : ∀ i x, 0 ≤ h i x) (hint : ∀ i, Integrable (h i)) :
    ∫⁻ z, ∏ i, ENNReal.ofReal (h i (z i)) ∂planeVolume N
      = ∏ i, ENNReal.ofReal (∫ x, h i x) := by
  have hI : Integrable (fun z : Fin (2 * N + 1) → ℂ => ∏ i, h i (z i)) (planeVolume N) :=
    Integrable.fintype_prod (f := h) hint
  have h1 : ∫⁻ z, ∏ i, ENNReal.ofReal (h i (z i)) ∂planeVolume N
      = ∫⁻ z, ENNReal.ofReal (∏ i, h i (z i)) ∂planeVolume N := by
    congr 1; ext z
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hnn i _)]
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun z => Finset.prod_nonneg fun i _ => hnn i _)]
  unfold planeVolume
  rw [integral_fintype_prod_eq_prod (fun i x => h i x)]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hnn i))]

theorem integrable_ballIndicator38 (R : ℝ) :
    Integrable (fun x : ℂ => (ball (0:ℂ) R).indicator (fun _ => (1:ℝ)) x) := by
  rw [integrable_indicator_iff measurableSet_ball]
  exact integrableOn_const measure_ball_lt_top.ne

theorem integrable_gauss38 {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℂ => Real.exp (-b * ‖x‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := ℂ) (b := (b : ℂ)) (by simpa using hb) 0 0).norm
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [Complex.norm_exp, ← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul]

theorem integral_gauss38 {b : ℝ} (hb : 0 < b) :
    ∫ x : ℂ, Real.exp (-b * ‖x‖ ^ 2) = Real.pi / b := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, Complex.finrank_real_complex]
  norm_num

theorem integral_ball38 (R : ℝ) (hR : 0 < R) :
    ∫ x : ℂ, (ball (0:ℂ) R).indicator (fun _ => (1:ℝ)) x = Real.pi * R ^ 2 := by
  rw [integral_indicator_const _ measurableSet_ball, Measure.real, Complex.volume_ball]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR.le]
  simp
  ring

/-- Single-coordinate factor: disk indicator on low modes, Gaussian on high modes. -/
noncomputable def ballFactor38 (R : ℝ) (b : ℝ) (high : Prop) [Decidable high] (x : ℂ) : ℝ :=
  if high then Real.exp (-b * ‖x‖ ^ 2) else (ball (0:ℂ) R).indicator (fun _ => (1:ℝ)) x

theorem ballFactor38_nonneg (R b : ℝ) (high : Prop) [Decidable high] (x : ℂ) :
    0 ≤ ballFactor38 R b high x := by
  unfold ballFactor38
  split_ifs
  · exact (Real.exp_pos _).le
  · exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- Gaussian/disk volume of the product region. -/
theorem lintegral_ballFactor_prod38 (N M : ℕ) (a ρ : Fin (2 * N + 1) → ℝ)
    (ha : ∀ i, 0 < a i) (hρ : ∀ i, 0 < ρ i) (R : ℝ) (hR : 0 < R) :
    ∫⁻ w, ∏ i, ENNReal.ofReal
        (ballFactor38 R (ρ i * a i) ((M : ℤ) < |modeIndex N i|) (w i)) ∂planeVolume N
      = (∏ i ∈ Finset.univ.filter (fun i => |modeIndex N i| ≤ (M : ℤ)),
            ENNReal.ofReal (Real.pi * R ^ 2))
        * ∏ i ∈ Finset.univ.filter (fun i => (M : ℤ) < |modeIndex N i|),
            ENNReal.ofReal (Real.pi / (ρ i * a i)) := by
  rw [lintegral_plane_prod38 N (fun i x => ballFactor38 R (ρ i * a i) ((M : ℤ) < |modeIndex N i|) x)
    (fun _ x => ballFactor38_nonneg _ _ _ _)]
  · have hi : ∀ i, ENNReal.ofReal (∫ x, ballFactor38 R (ρ i * a i) ((M : ℤ) < |modeIndex N i|) x)
        = if (M : ℤ) < |modeIndex N i| then ENNReal.ofReal (Real.pi / (ρ i * a i))
          else ENNReal.ofReal (Real.pi * R ^ 2) := by
      intro i
      unfold ballFactor38
      by_cases h : (M : ℤ) < |modeIndex N i|
      · simp only [h, ite_true]
        rw [integral_gauss38 (mul_pos (hρ i) (ha i))]
      · simp only [h, ite_false]
        rw [integral_ball38 R hR]
    simp_rw [hi]
    rw [Finset.prod_ite, mul_comm]
    congr 1
    · apply Finset.prod_congr _ (fun _ _ => rfl)
      ext _; simp
  · intro i
    unfold ballFactor38
    split_ifs
    · exact integrable_gauss38 (mul_pos (hρ i) (ha i))
    · exact integrable_ballIndicator38 R

/-- F05.08-.10: abstract change of variables plus Gaussian/disk bound. -/
theorem ballChangeOfVariables38 (N M : ℕ) (hM : M ≤ N)
    (B : Set (FourierPlane N)) (hB : MeasurableSet B)
    (Ψ : FourierPlane N → FourierPlane N)
    (Ψ' : FourierPlane N → (FourierPlane N →L[ℝ] FourierPlane N))
    (a ρ : Fin (2 * N + 1) → ℝ) (ha : ∀ i, 0 < a i) (hρ : ∀ i, 0 < ρ i)
    (hρ1 : ∀ i, ρ i ≤ 1) (E : FourierPlane N → ℝ) (hEm : Measurable E) (hE0 : ∀ z, 0 ≤ E z)
    (R : ℝ) (hR : 0 < R)
    (hinj : Set.InjOn Ψ B)
    (hder : ∀ z ∈ B, HasFDerivWithinAt Ψ (Ψ' z) B z)
    (hdet : ∀ z ∈ B, (1 / 2 : ℝ) ≤ |(Ψ' z).det|)
    (hlow : ∀ z ∈ B, ∀ i, |modeIndex N i| ≤ (M : ℤ) → Ψ z i = z i ∧ ‖z i‖ < R)
    (hE : ∀ z ∈ B, ∑ i ∈ Finset.univ.filter (fun i => (M : ℤ) < |modeIndex N i|),
        ρ i * a i * ‖Ψ z i‖ ^ 2 ≤ E z) :
    ∫⁻ z in B, ENNReal.ofReal (Real.exp (-E z)) ∂planeVolume N
      ≤ 2 * ((∏ i ∈ Finset.univ.filter (fun i => |modeIndex N i| ≤ (M : ℤ)),
            ENNReal.ofReal (Real.pi * R ^ 2))
        * ∏ i ∈ Finset.univ.filter (fun i => (M : ℤ) < |modeIndex N i|),
            ENNReal.ofReal (Real.pi / (ρ i * a i))) := by
  set g : FourierPlane N → ENNReal := fun w => ∏ i, ENNReal.ofReal
        (ballFactor38 R (ρ i * a i) ((M : ℤ) < |modeIndex N i|) (w i)) with hg
  have hgz : ∀ z ∈ B, g (Ψ z) = ENNReal.ofReal (Real.exp (-∑ i ∈ Finset.univ.filter
      (fun i => (M : ℤ) < |modeIndex N i|), ρ i * a i * ‖Ψ z i‖ ^ 2)) := by
    intro z hz
    simp only [hg]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => ballFactor38_nonneg _ _ _ _)]
    congr 1
    have hf : ∀ i, ballFactor38 R (ρ i * a i) ((M : ℤ) < |modeIndex N i|) (Ψ z i)
        = if (M : ℤ) < |modeIndex N i| then Real.exp (-(ρ i * a i * ‖Ψ z i‖ ^ 2)) else 1 := by
      intro i
      unfold ballFactor38
      by_cases h : (M : ℤ) < |modeIndex N i|
      · simp only [h, ite_true]; rw [neg_mul]
      · simp only [h, ite_false]
        obtain ⟨h1, h2⟩ := hlow z hz i (not_lt.1 h)
        rw [h1]
        simp [h2]
    simp_rw [hf]
    rw [← Finset.prod_filter, ← Real.exp_sum, Finset.sum_neg_distrib]
  have step1 : ∫⁻ z in B, ENNReal.ofReal (Real.exp (-E z)) ∂planeVolume N
      ≤ ∫⁻ z in B, 2 * (ENNReal.ofReal |(Ψ' z).det| * g (Ψ z)) ∂planeVolume N := by
    refine setLIntegral_mono' hB fun z hz => ?_
    have h1 : ENNReal.ofReal (Real.exp (-E z)) ≤ g (Ψ z) := by
      rw [hgz z hz]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg (hE z hz)))
    have h2 : (1 : ENNReal) ≤ 2 * ENNReal.ofReal |(Ψ' z).det| := by
      have : ENNReal.ofReal 1 ≤ ENNReal.ofReal (2 * |(Ψ' z).det|) :=
        ENNReal.ofReal_le_ofReal (by linarith [hdet z hz])
      rw [ENNReal.ofReal_mul (by norm_num)] at this
      simpa using this
    calc _ ≤ g (Ψ z) := h1
      _ = 1 * g (Ψ z) := (one_mul _).symm
      _ ≤ (2 * ENNReal.ofReal |(Ψ' z).det|) * g (Ψ z) := by gcongr
      _ = _ := by ring
  have step2 : ∫⁻ z in B, 2 * (ENNReal.ofReal |(Ψ' z).det| * g (Ψ z)) ∂planeVolume N
      = 2 * ∫⁻ w in Ψ '' B, g w ∂planeVolume N := by
    rw [lintegral_const_mul' _ _ (by simp),
      lintegral_image_eq_lintegral_abs_det_fderiv_mul (planeVolume N) hB hder hinj g]
  calc _ ≤ _ := step1
    _ = _ := step2
    _ ≤ 2 * ∫⁻ w, g w ∂planeVolume N := by
        exact mul_le_mul_right (setLIntegral_le_lintegral _ _) _
    _ = _ := by rw [hg, lintegral_ballFactor_prod38 N M a ρ ha hρ R hR]

/-- The no-map case (identity `Ψ`, all modes low): `∫_B e^{-E} ≤ ∏ π R²`. -/
theorem ballVolumeBound38 (N : ℕ) (B : Set (FourierPlane N)) (hB : MeasurableSet B)
    (E : FourierPlane N → ℝ) (hE0 : ∀ z, 0 ≤ E z) (R : ℝ) (hR : 0 < R)
    (hBR : ∀ z ∈ B, ∀ i, ‖z i‖ < R) :
    ∫⁻ z in B, ENNReal.ofReal (Real.exp (-E z)) ∂planeVolume N
      ≤ ∏ _i : Fin (2 * N + 1), ENNReal.ofReal (Real.pi * R ^ 2) := by
  calc ∫⁻ z in B, ENNReal.ofReal (Real.exp (-E z)) ∂planeVolume N
      ≤ ∫⁻ _z in B, 1 ∂planeVolume N := by
        refine setLIntegral_mono' hB fun z _ => ?_
        exact ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 (by linarith [hE0 z]))
    _ = planeVolume N B := by simp
    _ ≤ planeVolume N (Set.pi Set.univ fun _ => ball (0:ℂ) R) :=
        measure_mono fun z hz i _ => by simpa using hBR z hz i
    _ = _ := by
        unfold planeVolume
        rw [Measure.pi_pi]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Complex.volume_ball]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hR.le, mul_comm]
        rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]


end NlsGge.Schur

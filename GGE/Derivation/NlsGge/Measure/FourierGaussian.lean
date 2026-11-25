import NlsGge.Measure.FiniteGaussian
import NlsGge.Definitions.PilotInterfaces
import NlsGge.Weights.Entire

/-! Actual finite Fourier Gaussian references for v2.tex lines 79–88, 177–194,
313–320 and 938. Full rates retain every hierarchy term. This module does not
construct the nonlinear Gibbs law or assert a Gaussian change of variables. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Measure

def fourierPlaneGaussian (N : ℕ) (q : ℤ → ℝ) :
    MeasureTheory.Measure (NlsGge.Pilot.FourierPlane N) :=
  finiteComplexGaussian (fun i => q (NlsGge.Pilot.modeIndex N i))

instance fourierPlaneGaussian_probability (N : ℕ) (q : ℤ → ℝ) :
    IsProbabilityMeasure (fourierPlaneGaussian N q) := by
  unfold fourierPlaneGaussian
  infer_instance

lemma integrable_fourierPlaneGaussianKernel (N : ℕ) (q : ℤ → ℝ) (hq : ∀ n, 0 < q n) :
    Integrable (fun z : NlsGge.Pilot.FourierPlane N => ∏ i,
      Real.exp (-q (NlsGge.Pilot.modeIndex N i) * ‖z i‖ ^ 2))
      (NlsGge.Pilot.planeVolume N) :=
  integrable_finiteComplexGaussianKernel _ (fun i => hq _)

lemma integral_fourierPlaneGaussianKernel (N : ℕ) (q : ℤ → ℝ) (hq : ∀ n, 0 < q n) :
    (∫ z : NlsGge.Pilot.FourierPlane N, ∏ i,
      Real.exp (-q (NlsGge.Pilot.modeIndex N i) * ‖z i‖ ^ 2)
      ∂NlsGge.Pilot.planeVolume N) = ∏ i, Real.pi / q (NlsGge.Pilot.modeIndex N i) := by
  have _hi := integrable_fourierPlaneGaussianKernel N q hq
  exact integral_finiteComplexGaussianKernel _ (fun i => hq _)

lemma fourierPlaneGaussian_density (N : ℕ) (q : ℤ → ℝ) (hq : ∀ n, 0 < q n) :
    fourierPlaneGaussian N q = (NlsGge.Pilot.planeVolume N).withDensity
      (fun z : NlsGge.Pilot.FourierPlane N => ENNReal.ofReal
        (∏ i, (q (NlsGge.Pilot.modeIndex N i) / Real.pi) *
          Real.exp (-q (NlsGge.Pilot.modeIndex N i) * ‖z i‖ ^ 2))) := by
  exact finiteComplexGaussian_density _ (fun i => hq _)

lemma integrable_fourierPlaneGaussian_zeroMode (N : ℕ) (q : ℤ → ℝ) :
    Integrable
      (fun z : NlsGge.Pilot.FourierPlane N => ‖z (NlsGge.Pilot.zeroMode N)‖ ^ 2)
      (fourierPlaneGaussian N q) :=
  integrable_finiteComplexGaussian_sqNorm _ (NlsGge.Pilot.zeroMode N)

lemma integral_fourierPlaneGaussian_zeroMode (N : ℕ) (q : ℤ → ℝ)
    (hq : ∀ n, 0 < q n) :
    (∫ z : NlsGge.Pilot.FourierPlane N, ‖z (NlsGge.Pilot.zeroMode N)‖ ^ 2
      ∂fourierPlaneGaussian N q) = 1 / q 0 := by
  have _hi := integrable_fourierPlaneGaussian_zeroMode N q
  have h := integral_finiteComplexGaussian_sqNorm
    (fun i => q (NlsGge.Pilot.modeIndex N i)) (fun i => hq _) (NlsGge.Pilot.zeroMode N)
  simpa only [fourierPlaneGaussian, NlsGge.Pilot.modeIndex_zero] using h

theorem measurable_reflectModes (N : ℕ) :
    Measurable (fun z : NlsGge.Pilot.FourierPlane N =>
      fun i => z (NlsGge.Pilot.reflectMode N i)) := by fun_prop

theorem measurable_reflectPlane (N : ℕ) : Measurable (NlsGge.Pilot.reflectPlane N) := by
  unfold NlsGge.Pilot.reflectPlane
  fun_prop

/-- Reindexing by the actual mode reflection preserves every even-rate product law. -/
theorem fourierPlaneGaussian_map_reflectModes (N : ℕ) (q : ℤ → ℝ)
    (heven : ∀ n : ℤ, q (-n) = q n) :
    (fourierPlaneGaussian N q).map
      (fun z : NlsGge.Pilot.FourierPlane N => fun i => z (NlsGge.Pilot.reflectMode N i)) =
      fourierPlaneGaussian N q := by
  let e : Equiv.Perm (Fin (2 * N + 1)) :=
    (NlsGge.Pilot.reflectMode_involutive N).toPerm (NlsGge.Pilot.reflectMode N)
  have hf : (fun i => complexGaussian (q (NlsGge.Pilot.modeIndex N (e i)))) =
      (fun i => complexGaussian (q (NlsGge.Pilot.modeIndex N i))) := by
    funext i
    change complexGaussian (q (NlsGge.Pilot.modeIndex N (NlsGge.Pilot.reflectMode N i))) = _
    rw [NlsGge.Pilot.modeIndex_reflect, heven]
  have hm : (MeasurableEquiv.piCongrLeft (fun _ : Fin (2 * N + 1) => ℂ) e :
      NlsGge.Pilot.FourierPlane N → NlsGge.Pilot.FourierPlane N) =
      (fun z : NlsGge.Pilot.FourierPlane N => fun i => z (NlsGge.Pilot.reflectMode N i)) := by
    funext z i
    have h := MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin (2 * N + 1) => ℂ) e z (NlsGge.Pilot.reflectMode N i)
    simpa only [e, Function.Involutive.coe_toPerm, NlsGge.Pilot.reflectMode_involutive N i] using h
  have h := Measure.pi_map_piCongrLeft e
    (fun i => complexGaussian (q (NlsGge.Pilot.modeIndex N i)))
  rw [hf, hm] at h
  exact h

/-- Exact minus reflection used by the physical reflected Fourier convention. -/
theorem fourierPlaneGaussian_map_reflectPlane (N : ℕ) (q : ℤ → ℝ)
    (heven : ∀ n : ℤ, q (-n) = q n) :
    (fourierPlaneGaussian N q).map (NlsGge.Pilot.reflectPlane N) = fourierPlaneGaussian N q := by
  have hf : NlsGge.Pilot.reflectPlane N =
      (fun z : NlsGge.Pilot.FourierPlane N => fun i => -z i) ∘
        (fun z : NlsGge.Pilot.FourierPlane N => fun i => z (NlsGge.Pilot.reflectMode N i)) := rfl
  rw [hf, ← Measure.map_map measurable_finiteComplexNeg (measurable_reflectModes N),
    fourierPlaneGaussian_map_reflectModes N q heven]
  exact finiteComplexGaussian_map_neg _


/-- Full source hierarchy rate, with no hierarchy truncation. -/
def fullWeightRate (c : ℕ → ℝ) (n : ℤ) : ℝ :=
  NlsGge.Weights.weight c (2 * Real.pi * (n : ℝ))

lemma fullWeightRate_even (c : ℕ → ℝ) (n : ℤ) : fullWeightRate c (-n) = fullWeightRate c n := by
  simp only [fullWeightRate, Int.cast_neg, mul_neg, NlsGge.Weights.weight_even]

lemma fullWeightRate_pos (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j, lower ≤ c j) (hupper : ∀ j, c j ≤ upper) (n : ℤ) :
    0 < fullWeightRate c n := by
  have _hsum := NlsGge.Weights.weightTerm_summable lower upper c hlower hbound hupper
    (2 * Real.pi * (n : ℝ))
  exact NlsGge.Weights.weight_pos lower upper c hlower hbound hupper _

/-- Actual Measure.pi law with source rates on every signed mode, including zero. -/
def fullWeightFourierGaussian (N : ℕ) (c : ℕ → ℝ) :
    MeasureTheory.Measure (NlsGge.Pilot.FourierPlane N) :=
  finiteComplexGaussian (fun i => fullWeightRate c (NlsGge.Pilot.modeIndex N i))

instance fullWeightFourierGaussian_probability (N : ℕ) (c : ℕ → ℝ) :
    IsProbabilityMeasure (fullWeightFourierGaussian N c) := by
  unfold fullWeightFourierGaussian
  infer_instance

lemma measurable_fullWeightFourierGaussianPDF (N : ℕ) (c : ℕ → ℝ) :
    Measurable (fun z : NlsGge.Pilot.FourierPlane N =>
      ∏ i, (fullWeightRate c (NlsGge.Pilot.modeIndex N i) / Real.pi) *
        Real.exp (-fullWeightRate c (NlsGge.Pilot.modeIndex N i) * ‖z i‖ ^ 2)) :=
  measurable_finiteGaussianPDF _

lemma integrable_fullWeightFourierGaussianPDF (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j, lower ≤ c j) (hupper : ∀ j, c j ≤ upper) (N : ℕ) :
    Integrable (fun z : NlsGge.Pilot.FourierPlane N =>
      ∏ i, (fullWeightRate c (NlsGge.Pilot.modeIndex N i) / Real.pi) *
        Real.exp (-fullWeightRate c (NlsGge.Pilot.modeIndex N i) * ‖z i‖ ^ 2))
      (NlsGge.Pilot.planeVolume N) :=
  integrable_finiteGaussianPDF _ (fun i => fullWeightRate_pos lower upper c hlower hbound hupper _)

lemma integral_fullWeightFourierGaussianPDF (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j, lower ≤ c j) (hupper : ∀ j, c j ≤ upper) (N : ℕ) :
    (∫ z : NlsGge.Pilot.FourierPlane N,
      ∏ i, (fullWeightRate c (NlsGge.Pilot.modeIndex N i) / Real.pi) *
        Real.exp (-fullWeightRate c (NlsGge.Pilot.modeIndex N i) * ‖z i‖ ^ 2)
      ∂NlsGge.Pilot.planeVolume N) = 1 := by
  have _hi := integrable_fullWeightFourierGaussianPDF lower upper c hlower hbound hupper N
  exact integral_finiteGaussianPDF _
    (fun i => fullWeightRate_pos lower upper c hlower hbound hupper _)

theorem fullWeightFourierGaussian_density (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j, lower ≤ c j) (hupper : ∀ j, c j ≤ upper) (N : ℕ) :
    fullWeightFourierGaussian N c = (NlsGge.Pilot.planeVolume N).withDensity
      (fun z : NlsGge.Pilot.FourierPlane N => ENNReal.ofReal
        (∏ i, (fullWeightRate c (NlsGge.Pilot.modeIndex N i) / Real.pi) *
          Real.exp (-fullWeightRate c (NlsGge.Pilot.modeIndex N i) * ‖z i‖ ^ 2))) :=
  finiteComplexGaussian_density _
    (fun i => fullWeightRate_pos lower upper c hlower hbound hupper _)

lemma integrable_fullWeightFourierGaussianKernel (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j, lower ≤ c j) (hupper : ∀ j, c j ≤ upper) (N : ℕ) :
    Integrable (fun z : NlsGge.Pilot.FourierPlane N => ∏ i,
      Real.exp (-fullWeightRate c (NlsGge.Pilot.modeIndex N i) * ‖z i‖ ^ 2))
      (NlsGge.Pilot.planeVolume N) :=
  integrable_finiteComplexGaussianKernel _
    (fun i => fullWeightRate_pos lower upper c hlower hbound hupper _)

lemma integral_fullWeightFourierGaussianKernel (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j, lower ≤ c j) (hupper : ∀ j, c j ≤ upper) (N : ℕ) :
    (∫ z : NlsGge.Pilot.FourierPlane N, ∏ i,
      Real.exp (-fullWeightRate c (NlsGge.Pilot.modeIndex N i) * ‖z i‖ ^ 2)
      ∂NlsGge.Pilot.planeVolume N) =
      ∏ i, Real.pi / fullWeightRate c (NlsGge.Pilot.modeIndex N i) := by
  have _hi := integrable_fullWeightFourierGaussianKernel lower upper c
    hlower hbound hupper N
  exact integral_finiteComplexGaussianKernel _
    (fun i => fullWeightRate_pos lower upper c hlower hbound hupper _)

lemma integrable_fullWeightFourierGaussian_zeroMode (N : ℕ) (c : ℕ → ℝ) :
    Integrable
      (fun z : NlsGge.Pilot.FourierPlane N => ‖z (NlsGge.Pilot.zeroMode N)‖ ^ 2)
      (fullWeightFourierGaussian N c) :=
  integrable_finiteComplexGaussian_sqNorm _ (NlsGge.Pilot.zeroMode N)

lemma integral_fullWeightFourierGaussian_zeroMode (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j, lower ≤ c j) (hupper : ∀ j, c j ≤ upper) (N : ℕ) :
    (∫ z : NlsGge.Pilot.FourierPlane N, ‖z (NlsGge.Pilot.zeroMode N)‖ ^ 2
      ∂fullWeightFourierGaussian N c) = 1 / NlsGge.Weights.weight c 0 := by
  have _hi := integrable_fullWeightFourierGaussian_zeroMode N c
  have h := integral_finiteComplexGaussian_sqNorm
    (fun i => fullWeightRate c (NlsGge.Pilot.modeIndex N i))
    (fun i => fullWeightRate_pos lower upper c hlower hbound hupper _)
    (NlsGge.Pilot.zeroMode N)
  simpa only [fullWeightFourierGaussian, NlsGge.Pilot.modeIndex_zero, fullWeightRate,
    Int.cast_zero, mul_zero] using h

theorem fullWeightFourierGaussian_map_reflectPlane (N : ℕ) (c : ℕ → ℝ) :
    (fullWeightFourierGaussian N c).map (NlsGge.Pilot.reflectPlane N) =
      fullWeightFourierGaussian N c :=
  fourierPlaneGaussian_map_reflectPlane N (fullWeightRate c) (fullWeightRate_even c)


end NlsGge.Measure

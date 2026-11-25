import NlsGge.Measure.FiniteScalarGaussian
import NlsGge.Measure.ScalarGaussianMoments
import NlsGge.Measure.ModeDualCovariance
import Mathlib.Probability.Moments.Variance

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace NlsGge.Measure

private lemma integral_fullWeightSequenceGaussian_modeScalar {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (L : NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ) (n : ℤ) :
    (∫ z : ℤ → ℂ, L (fullWeightedModeMap c s n (z n))
      ∂fullWeightSequenceGaussian c.val) = 0 := by
  let M : ℂ →L[ℝ] NlsGge.Pilot.FullWeightedHilbert c s := fullWeightedModeMap c s n
  have hmeas : AEStronglyMeasurable (fun w : ℂ => (L.comp M) w)
      ((fullWeightSequenceGaussian c.val).map (fun z : ℤ → ℂ => z n)) := by
    fun_prop
  have hmapInt := integral_map
    (μ := fullWeightSequenceGaussian c.val)
    (φ := fun z : ℤ → ℂ => z n)
    (f := fun w : ℂ => (L.comp M) w)
    (measurable_pi_apply n).aemeasurable hmeas
  calc
    (∫ z : ℤ → ℂ, L (M (z n)) ∂fullWeightSequenceGaussian c.val) =
        ∫ w : ℂ, (L.comp M) w
          ∂(fullWeightSequenceGaussian c.val).map (fun z : ℤ → ℂ => z n) := by
            simpa only [ContinuousLinearMap.comp_apply] using
              hmapInt.symm
    _ = ∫ w : ℂ, (L.comp M) w ∂complexGaussian (fullWeightRate c.val n) := by
          rw [fullWeightSequenceGaussian_map_eval]
    _ = 0 := integral_complexGaussian_realLinear _ _

private lemma variance_fullWeightSequenceGaussian_modeScalar {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (L : NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ) (n : ℤ) :
    ProbabilityTheory.variance
      (fun z : ℤ → ℂ => L (fullWeightedModeMap c s n (z n)))
      (fullWeightSequenceGaussian c.val) =
        fullWeightedDualCovarianceTerm c s L L n := by
  let M : ℂ →L[ℝ] NlsGge.Pilot.FullWeightedHilbert c s := fullWeightedModeMap c s n
  have hrate : 0 < fullWeightRate c.val n := by
    simpa [fullWeightRate, NlsGge.Pilot.sourceRate] using
      NlsGge.Pilot.sourceRate_pos c n
  have hrateEq : NlsGge.Pilot.sourceRate c n = fullWeightRate c.val n := rfl
  calc
    ProbabilityTheory.variance (fun z : ℤ → ℂ => L (M (z n)))
        (fullWeightSequenceGaussian c.val) =
      ProbabilityTheory.variance (L.comp M)
        ((fullWeightSequenceGaussian c.val).map (fun z : ℤ → ℂ => z n)) := by
          simpa only [ContinuousLinearMap.comp_apply, Function.comp_def] using
            (ProbabilityTheory.variance_map
              (X := L.comp M) (Y := fun z : ℤ → ℂ => z n)
              (by fun_prop) (measurable_pi_apply n).aemeasurable).symm
    _ = ProbabilityTheory.variance (L.comp M)
        (complexGaussian (fullWeightRate c.val n)) := by
          rw [fullWeightSequenceGaussian_map_eval]
    _ = fullWeightedDualCovarianceTerm c s L L n := by
          rw [variance_complexGaussian_realLinear_of_pos _ hrate (L.comp M)]
          unfold fullWeightedDualCovarianceTerm
          rw [hrateEq]
          simp only [ContinuousLinearMap.comp_apply]
          ring

private lemma fullWeightSequenceGaussian_partialScalar_eq_sumModes {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (N : ℕ)
    (L : NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ) :
    (fun z : ℤ → ℂ => L (fullWeightedSequencePartial c s N z)) =
      (fun z : ℤ → ℂ =>
        ∑ n ∈ NlsGge.Pilot.symmetricModes N,
          L (fullWeightedModeMap c s n (z n))) := by
  funext z
  rw [fullWeightedSequencePartial_eq_sumModeMaps]
  simp only [map_sum]

private lemma iIndepFun_fullWeightSequenceGaussian_modeScalars {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (L : NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ) :
    iIndepFun
      (fun n : ℤ => fun z : ℤ → ℂ => L (fullWeightedModeMap c s n (z n)))
      (fullWeightSequenceGaussian c.val) := by
  have hcoord : iIndepFun (fun n : ℤ => fun z : ℤ → ℂ => z n)
      (fullWeightSequenceGaussian c.val) := by
    simpa [fullWeightSequenceGaussian, countableComplexGaussian] using
      (ProbabilityTheory.iIndepFun_infinitePi
        (P := fun n : ℤ => complexGaussian (fullWeightRate c.val n))
        (X := fun n (z : ℂ) => z) (by fun_prop))
  exact hcoord.comp (fun n w => L (fullWeightedModeMap c s n w)) (by
    intro n
    fun_prop)

lemma integrable_fullWeightSequenceGaussian_partialScalar {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (N : ℕ)
    (L : NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ) :
    MeasureTheory.Integrable
      (fun z : ℤ → ℂ => L (fullWeightedSequencePartial c s N z))
      (fullWeightSequenceGaussian c.val) :=
  (hasGaussianLaw_fullWeightSequenceGaussian_partialScalar c s N L).integrable

lemma integral_fullWeightSequenceGaussian_partialScalar {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (N : ℕ)
    (L : NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ) :
    (∫ z : ℤ → ℂ,
      L (fullWeightedSequencePartial c s N z)
      ∂fullWeightSequenceGaussian c.val) = 0 := by
  rw [fullWeightSequenceGaussian_partialScalar_eq_sumModes]
  rw [MeasureTheory.integral_finsetSum]
  · simp_rw [integral_fullWeightSequenceGaussian_modeScalar]
    simp
  · intro n hn
    exact (hasGaussianLaw_fullWeightSequenceGaussian_modeScalar c s L n).integrable

lemma variance_fullWeightSequenceGaussian_partialScalar {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (N : ℕ)
    (L : NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ) :
    ProbabilityTheory.variance
      (fun z : ℤ → ℂ => L (fullWeightedSequencePartial c s N z))
      (fullWeightSequenceGaussian c.val) =
        ∑ n ∈ NlsGge.Pilot.symmetricModes N,
          fullWeightedDualCovarianceTerm c s L L n := by
  let X : ℤ → (ℤ → ℂ) → ℝ :=
    fun n z => L (fullWeightedModeMap c s n (z n))
  have hindep := iIndepFun_fullWeightSequenceGaussian_modeScalars c s L
  have hpair : Set.Pairwise (↑(NlsGge.Pilot.symmetricModes N))
      (fun n m => X n ⟂ᵢ[fullWeightSequenceGaussian c.val] X m) := by
    intro n hn m hm hnm
    exact hindep.indepFun hnm
  have hvarSum : ProbabilityTheory.variance
      (∑ n ∈ NlsGge.Pilot.symmetricModes N, X n)
      (fullWeightSequenceGaussian c.val) =
        ∑ n ∈ NlsGge.Pilot.symmetricModes N,
          ProbabilityTheory.variance (X n) (fullWeightSequenceGaussian c.val) := by
    exact ProbabilityTheory.IndepFun.variance_sum
      (μ := fullWeightSequenceGaussian c.val) (X := X)
      (s := NlsGge.Pilot.symmetricModes N)
      (fun n hn =>
        (hasGaussianLaw_fullWeightSequenceGaussian_modeScalar c s L n).memLp_two)
      hpair
  have hsumFun : (∑ n ∈ NlsGge.Pilot.symmetricModes N, X n) =
      (fun z : ℤ → ℂ => ∑ n ∈ NlsGge.Pilot.symmetricModes N, X n z) := by
    funext z
    simp
  rw [fullWeightSequenceGaussian_partialScalar_eq_sumModes]
  rw [← hsumFun]
  rw [hvarSum]
  apply Finset.sum_congr rfl
  intro n hn
  exact variance_fullWeightSequenceGaussian_modeScalar c s L n

end NlsGge.Measure

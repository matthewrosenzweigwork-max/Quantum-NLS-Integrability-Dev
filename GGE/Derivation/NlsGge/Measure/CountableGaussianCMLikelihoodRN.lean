import NlsGge.Measure.CommonSourceLikelihoodL2LimitAllFiniteCylinders
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Actual common-source CM likelihood limit realizes the countable translated
Gaussian law. This is the raw-coordinate RN identity only; strict positivity,
reverse absolute continuity and physical pushforward identification remain open. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal BigOperators
namespace NlsGge.Measure

theorem exists_actualSourceCMCommonLikelihoodL2Limit_countableRN
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c)) :
    ∃ L : Lp ℝ 2 (fullWeightSequenceGaussian c.val),
      Tendsto (commonSourceLikelihoodLpSequenceOfMemLp lower upper c
        (actualSourceCMSequence c x)
        (fun N => memLp_commonSourceLikelihoodReal c N
          (actualSourceCMSequence c x))) atTop (nhds L) ∧
      (∀ᵐ z ∂fullWeightSequenceGaussian c.val, 0 ≤ L z) ∧
      (∫ z : ℤ → ℂ, L z ∂fullWeightSequenceGaussian c.val) = 1 ∧
      (fullWeightSequenceGaussian c.val).map
        (fun z : ℤ → ℂ => fun n => z n + actualSourceCMSequence c x n) =
      (fullWeightSequenceGaussian c.val).withDensity
        (fun z => ENNReal.ofReal (L z)) := by
  classical
  obtain ⟨L, hconv, hnonneg, hmass, hcyl⟩ :=
    exists_actualSourceCMCommonLikelihoodL2Limit_allFiniteCylinders c x
  let μ : Measure (ℤ → ℂ) := fullWeightSequenceGaussian c.val
  let h : ℤ → ℂ := actualSourceCMSequence c x
  let factors : ℤ → Measure ℂ := fun n =>
    (complexGaussian (fullWeightRate c.val n)).map (fun z : ℂ => z + h n)
  have hbox : μ.withDensity (fun z => ENNReal.ofReal (L z)) =
      Measure.infinitePi factors := by
    apply Measure.eq_infinitePi
    intro U t ht
    obtain ⟨M, hM⟩ := (Filter.tendsto_atTop.1
      NlsGge.Pilot.symmetricModes_tendsto U).exists
    have hU : ∀ n ∈ U, n ∈ NlsGge.Pilot.symmetricModes M :=
      fun n hn => hM hn
    let B : Set ((u : U) → ℂ) := Set.univ.pi (fun u : U => t u.1)
    have hB : MeasurableSet B := MeasurableSet.univ_pi (fun u => ht u.1)
    have hevent :
        (fun z : ℤ → ℂ => fun u : U => z u.1) ⁻¹' B = Set.pi U t := by
      ext z
      simp [B]
    have hcy := hcyl M U hU B hB
    rw [hevent] at hcy
    have hmeas : MeasurableSet (Set.pi U t) :=
      MeasurableSet.pi U.countable_toSet (fun n _ => ht n)
    have hreal : ENNReal.ofReal (∫ z in Set.pi U t, L z ∂μ) =
        ∫⁻ z in Set.pi U t, ENNReal.ofReal (L z) ∂μ := by
      apply ofReal_integral_eq_lintegral_ofReal
      · exact ((Lp.memLp L).integrable (by norm_num)).restrict
      · exact ae_restrict_of_ae hnonneg
    rw [MeasureTheory.withDensity_apply _ hmeas, ← hreal]
    calc
      ENNReal.ofReal (∫ z in Set.pi U t, L z ∂μ) =
          (Measure.pi (fun u : U => factors u.1)) B := by
        simpa only [μ, h, factors] using hcy
      _ = ∏ n ∈ U, factors n (t n) := by
        rw [Measure.pi_pi]
        change (∏ i ∈ U.attach, factors i.1 (t i.1)) = _
        exact Finset.prod_attach U (fun n => factors n (t n))
  have hmap : μ.map (fun z : ℤ → ℂ => fun n => z n + h n) =
      Measure.infinitePi factors := by
    simpa only [μ, h, factors, fullWeightSequenceGaussian, countableComplexGaussian] using
      (Measure.infinitePi_map_pi
        (μ := fun n : ℤ => complexGaussian (fullWeightRate c.val n))
        (f := fun n : ℤ => fun z : ℂ => z + h n) (fun _ => by fun_prop))
  refine ⟨L, hconv, hnonneg, hmass, ?_⟩
  exact hmap.trans hbox.symm

end NlsGge.Measure

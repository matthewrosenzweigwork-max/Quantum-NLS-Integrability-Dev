import Mathlib
import NlsGge.Sobolev.SourceWeighted
import NlsGge.ThirdConsultation.I.LimitLaws
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.T.ECarrier98
import NlsGge.ThirdConsultation.T.TDefsHost
import NlsGge.ThirdConsultation.T.TDefs2Host
import NlsGge.ThirdConsultation.T.T026Host
import NlsGge.Atomic.T.T008
import NlsGge.Atomic.T.T009
import NlsGge.Birkhoff.F09Limit38
import NlsGge.Birkhoff.W06Jacobian38
import NlsGge.Birkhoff.W11Equivalence38

/- T-010 production draft. The public pushforward lemma is the explicit
   physical-law bridge required by DEFINITIONS/T.lean.md:328-333. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators ContDiff
open scoped BoundedContinuousFunction
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.Common

namespace NlsGge.ThirdConsultation.T
noncomputable section

theorem fullFourierLawE_map_fullFourierLaw
    (lo up : ℝ) (c : BoundedCoefficients lo up)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (N : ℕ) :
    (fullFourierLawE c s N).map (physicalInclusion c s) = fullFourierLaw c N := by
  -- Use the imported ECarrier98 measurable structure without shadowing the instance
  -- captured in the literal finite-law definition.
  obtain ⟨_, _, ⟨zmin, hzmin, hlow⟩⟩ :=
    fullFourier_normalizers_limit_lower lo up c
  have hpos : 0 < relativePartition c N := lt_of_lt_of_le hzmin (hlow N)
  have hpos38 : 0 < relativePartition38 c N := by
    simpa [relativePartition] using hpos
  have hscale38 : ENNReal.ofReal (relativePartition38 c N)⁻¹ =
      ENNReal.ofReal (1 / relativePartition38 c N) := by
    calc
      ENNReal.ofReal (relativePartition38 c N)⁻¹ =
          (ENNReal.ofReal (relativePartition38 c N))⁻¹ :=
        ENNReal.ofReal_inv_of_pos hpos38
      _ = ENNReal.ofReal (1 / relativePartition38 c N) := by
        rw [one_div]
        exact (ENNReal.ofReal_inv_of_pos hpos38).symm
  have hphys : Measurable (physOfE38 c s) :=
    (measurableEmbedding_physOfE38 c s).measurable
  have hproj : Measurable (projE38 c s N) :=
    (projE38 c s N).continuous.measurable
  rw [fullFourierLawE, fullFourierLaw, physicalInclusion]
  simp only [relativePartition]
  have hmapcomp :
      Measure.map (physOfE38 c s)
        (Measure.map (⇑(projE38 c s N))
          ((fullWeightedSequenceGaussian c s).withDensity
            (fun x => ENNReal.ofReal (fN38 c s N x)))) =
      Measure.map (fun x : FullWeightedHilbert c s =>
          physOfE38 c s (projE38 c s N x))
        ((fullWeightedSequenceGaussian c s).withDensity
          (fun x => ENNReal.ofReal (fN38 c s N x))) := by
    exact Measure.map_map hphys hproj
  rw [Measure.map_smul (ENNReal.ofReal (relativePartition38 c N)⁻¹) hphys.aemeasurable]
  simp only [hmapcomp]
  rw [hscale38]
  exact (NlsGge.Birkhoff.nuWN38_eq_map c s hs N).symm

theorem fullFourier_weak_weighted
    (lo up : ℝ) (c : BoundedCoefficients lo up)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    (∀ N : ℕ, IsProbabilityMeasure (fullFourierLawE c s N)) ∧
    IsProbabilityMeasure (muWE c s hs hs') ∧
    ∀ F : ECarrier38 c s →ᵇ ℝ,
      Tendsto (fun N : ℕ => ∫ x, F x ∂fullFourierLawE c s N) atTop
        (𝓝 (∫ x, F x ∂muWE c s hs hs')) := by
  -- ECarrier98 supplies the measurable structure on ECarrier38.
  have hEmbed : MeasurableEmbedding (physicalInclusion c s) := by
    simpa [physicalInclusion] using (measurableEmbedding_physOfE38 c s)
  have hfullProbability : ∀ N : ℕ, IsProbabilityMeasure (fullFourierLawE c s N) := by
    intro N
    have hmap := fullFourierLawE_map_fullFourierLaw lo up c s hs N
    have htarget : IsProbabilityMeasure (fullFourierLaw c N) := by
      simpa [fullFourierLaw] using
        (NlsGge.Birkhoff.isProbabilityMeasure_nuWN38 c N)
    have hmass : (fullFourierLawE c s N) Set.univ =
        ((fullFourierLawE c s N).map (physicalInclusion c s)) Set.univ := by
      rw [Measure.map_apply hEmbed.measurable MeasurableSet.univ]
      simp
    refine ⟨?_⟩
    calc
      (fullFourierLawE c s N) Set.univ =
          ((fullFourierLawE c s N).map (physicalInclusion c s)) Set.univ := hmass
      _ = (fullFourierLaw c N) Set.univ := by rw [hmap]
      _ = 1 := htarget.measure_univ
  have hlimitMap : (muWE c s hs hs').map (physicalInclusion c s) =
      I.physicalLaw (weight c.val) :=
    muWE_map_physicalLaw lo up c s hs hs'
  have hlimitTarget : IsProbabilityMeasure (I.physicalLaw (weight c.val)) := by
    rw [← (I.actual_ensemble_eq_I lo up c).2.2.1]
    exact PDE.actualBirkhoffInput38.isProbabilityMeasure_muW38 lo up c.val
      c.property.1 (coef_bound38 c) (coef_upper38 c)
  have hlimitProbability : IsProbabilityMeasure (muWE c s hs hs') := by
    have hmass : (muWE c s hs hs') Set.univ =
        ((muWE c s hs hs').map (physicalInclusion c s)) Set.univ := by
      rw [Measure.map_apply hEmbed.measurable MeasurableSet.univ]
      simp
    refine ⟨?_⟩
    calc
      (muWE c s hs hs') Set.univ =
          ((muWE c s hs hs').map (physicalInclusion c s)) Set.univ := hmass
      _ = (I.physicalLaw (weight c.val)) Set.univ := by rw [hlimitMap]
      _ = 1 := hlimitTarget.measure_univ
  refine ⟨hfullProbability, hlimitProbability, ?_⟩
  intro F
  obtain ⟨_, hUnnormalized⟩ :=
    fullFourier_unnormalized_test_limit lo up c s hs hs' F
  have hFfinite : ∀ N : ℕ, Integrable F (fullFourierLawE c s N) := by
    intro N
    letI : IsProbabilityMeasure (fullFourierLawE c s N) := hfullProbability N
    exact BoundedContinuousFunction.integrable _ F
  classical
  let G : PhysicalL2 → ℝ := Function.extend (physicalInclusion c s) F (fun _ => 0)
  have hG : ∀ y : ECarrier38 c s, G (physicalInclusion c s y) = F y := by
    intro y
    simpa [G, physicalInclusion] using
      (physOfE38_injective c s).extend_apply F _ y
  have hGrestrict : (fun y : ECarrier38 c s => G (physOfE38 c s y)) = F := by
    funext y
    exact hG y
  have hGc : Continuous (fun y : ECarrier38 c s => G (physOfE38 c s y)) := by
    rw [hGrestrict]
    exact F.continuous
  have hIntegralMap (N : ℕ) :
      (∫ x, F x ∂fullFourierLawE c s N) = ∫ u, G u ∂fullFourierLaw c N := by
    rw [← fullFourierLawE_map_fullFourierLaw lo up c s hs N, hEmbed.integral_map]
    simp only [hG]
  have hGproj (N : ℕ) (x : FullWeightedHilbert c s) :
      G (physOfE38 c s (projE38 c s N x)) = F (projE38 c s N x) := by
    simpa [physicalInclusion] using hG (projE38 c s N x)
  have hIntegralRaw (N : ℕ) :
      (∫ x, G (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
        ∂fullWeightedSequenceGaussian c s) = unnormalizedTest c s (fun y => F y) N := by
    rw [unnormalizedTest]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hGproj N x]
  have hIntegral (N : ℕ) :
      (∫ x, F x ∂fullFourierLawE c s N) =
        (1 / relativePartition c N) * unnormalizedTest c s (fun y => F y) N := by
    rw [hIntegralMap N, fullFourierLaw]
    rw [NlsGge.Birkhoff.integral_nuWN38 c s hs N G hGc]
    rw [hIntegralRaw N]
    simp only [relativePartition]
  obtain ⟨hZWpos, hZlimit, _⟩ := fullFourier_normalizers_limit_lower lo up c
  have hQuotient := hUnnormalized.div hZlimit hZWpos.ne'
  have hCancel :
      (ZW c * ∫ x, F x ∂muWE c s hs hs') / ZW c =
        ∫ x, F x ∂muWE c s hs hs' :=
    mul_div_cancel_left₀ (∫ x, F x ∂muWE c s hs hs') hZWpos.ne'
  have hPointwise :
      (fun N : ℕ => unnormalizedTest c s (fun y => F y) N / relativePartition c N) =
        ((fun N : ℕ => unnormalizedTest c s (⇑F) N) / relativePartition c) := by
    funext N
    rfl
  have hQuotientPointwise : Tendsto
      (fun N : ℕ => unnormalizedTest c s (fun y => F y) N / relativePartition c N)
      atTop (𝓝 ((ZW c * ∫ x, F x ∂muWE c s hs hs') / ZW c)) := by
    rw [hPointwise]
    exact hQuotient
  have hLimit : Tendsto
      (fun N : ℕ => unnormalizedTest c s (fun y => F y) N / relativePartition c N)
      atTop (𝓝 (∫ x, F x ∂muWE c s hs hs')) := by
    simpa only [hCancel] using hQuotientPointwise
  have hSequence :
      (fun N : ℕ => ∫ x, F x ∂fullFourierLawE c s N) =
        fun N : ℕ => unnormalizedTest c s (fun y => F y) N / relativePartition c N := by
    funext N
    rw [hIntegral N, one_div, div_eq_mul_inv]
    ring
  rw [hSequence]
  exact hLimit

end
end NlsGge.ThirdConsultation.T

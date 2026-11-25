import NlsGge.Hierarchy.A01Spectral38
import NlsGge.Hierarchy.FullEnergyPlaneConvergence38
import NlsGge.ThirdConsultation.PDE.ActualEnsemble
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.I.I030Core
import NlsGge.Atomic.PDE.PDE067
import NlsGge.Birkhoff.S04NlsInvariance38

                                                                                    
                                                                          
                                                                               
                                                                       
                                                                         
                                                                                        
                                                                                  
                                                
                                                                            
                                                                     
                                                                              
                                                                           
                                                                                 
set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff BoundedContinuousFunction
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.SpectralFoundations NlsGge.NLS38
open NlsGge.ThirdConsultation.PDE

namespace NlsGge.ThirdConsultation.Main

/-- The actual finite-gap GGE, with the full charge energy and uncut Gaussian
construction, arbitrary increasing finite exhaustion, smooth support, all
finite real Sobolev/charge moments, positive actions and actual NLS invariance. -/
theorem periodic_infinite_charge_finite_gap_gge
    (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) :
    (∀ j : ℕ, NlsGge.coefficient c j = c j / (Nat.factorial j : ℝ) ^ 4) ∧
    (Measurable (actualBirkhoffTop38.Rbar38 c) ∧ MeasurableSet (Omega038 c) ∧
      fullWeightSequenceGaussian c (Omega038 c)ᶜ = 0 ∧
      (∀ z ∈ Omega038 c,
        Summable (fun n : ℤ => remainderSummand38 c (actualBirkhoffTop38.cleanΦinv z) n) ∧
        actualBirkhoffTop38.Rbar38 c z = remainder38 c (actualBirkhoffTop38.cleanΦinv z)) ∧
      (∀ z ∉ Omega038 c, actualBirkhoffTop38.Rbar38 c z = 0) ∧
      (∀ z, 0 ≤ actualBirkhoffTop38.Rbar38 c z)) ∧
    ((∀ z, 0 < Real.exp (-(actualBirkhoffTop38.Rbar38 c z)) ∧
        Real.exp (-(actualBirkhoffTop38.Rbar38 c z)) ≤ 1) ∧
      0 < actualBirkhoffTop38.ZW38 c ∧ actualBirkhoffTop38.ZW38 c ≤ 1) ∧
    (IsProbabilityMeasure (actualBirkhoffTop38.muHatW38 c) ∧
      actualBirkhoffTop38.muHatW38 c = (fullWeightSequenceGaussian c).withDensity
        (fun z => ENNReal.ofReal
          (Real.exp (-(actualBirkhoffTop38.Rbar38 c z)) / actualBirkhoffTop38.ZW38 c)) ∧
      (actualBirkhoffTop38.muHatW38 c ≪ fullWeightSequenceGaussian c ∧
        fullWeightSequenceGaussian c ≪ actualBirkhoffTop38.muHatW38 c) ∧
      IsProbabilityMeasure (actualMuW c) ∧
      actualMuW c = (actualBirkhoffTop38.muHatW38 c).map actualBirkhoffTop38.cleanΦinv ∧
      ∀ᵐ z ∂(actualBirkhoffTop38.muHatW38 c), ∃ hz : z ∈ seqSobolev38 0,
        actualBirkhoffTop38.cleanΦinv z = actualBirkhoffTop38.Φinv z hz ∧
        actualBirkhoffTop38.Φ (actualBirkhoffTop38.cleanΦinv z) = z) ∧
    (∀ Λ : Finset ℤ,
      actualNu c Λ = ((finiteComplexVolume Λ).withDensity
        (fun w => ENNReal.ofReal (Real.exp (-(energyW38 c (finiteGapField Λ w))) /
          actualBirkhoffTop38.ZcalΛ38 c Λ))).map (finiteGapField Λ) ∧
      IsProbabilityMeasure (actualNu c Λ) ∧
      (0 < actualBirkhoffTop38.ZcalΛ38 c Λ ∧
        actualBirkhoffTop38.ZcalΛ38 c Λ ≤ ∏ i : Λ, Real.pi / rateΛ38 c Λ i) ∧
      actualBirkhoffTop38.nuHat38 c Λ = (gammaΛ38 c Λ).withDensity
        (fun w => ENNReal.ofReal
          (Real.exp (-(actualBirkhoffTop38.Rbar38 c (extZero38 Λ w))) /
            actualBirkhoffTop38.ZΛ38 c Λ))) ∧
    (∀ (Λ : Finset ℤ) (z : ℤ → ℂ),
      ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
        NlsGge.HierarchyRiccati.Core.smoothL2_38 U hU hper = actualBirkhoffTop38.cleanΦinv (projFin38 Λ z) ∧
        Summable (fun j : ℕ => NlsGge.coefficient c j * NlsGge.HierarchyRiccati.Core.localCharge38 U j) ∧
        energyW38 c (actualBirkhoffTop38.cleanΦinv (projFin38 Λ z)) =
          ∑' j : ℕ, NlsGge.coefficient c j * NlsGge.HierarchyRiccati.Core.localCharge38 U j) ∧
    (∀ (Λ : ℕ → Finset ℤ), IsExhaustion38 Λ →
      ((Tendsto (fun N : ℕ => actualBirkhoffTop38.ZΛ38 c (Λ N)) atTop
          (𝓝 (actualBirkhoffTop38.ZW38 c)) ∧ 0 < actualBirkhoffTop38.ZW38 c) ∧
        ∀ (m : ℕ) (F : SobolevCarrier38 (m : ℝ) →ᵇ ℝ),
          Tendsto (fun N : ℕ => ∫ u, F (physH38 m u) ∂(actualNu c (Λ N))) atTop
            (𝓝 (∫ u, F (physH38 m u) ∂(actualMuW c)))) ∧
      Tendsto (fun N : ℕ => ∫ z,
        |Real.exp (-(actualBirkhoffTop38.Rbar38 c (projFin38 (Λ N) z))) /
            actualBirkhoffTop38.ZΛ38 c (Λ N) -
          Real.exp (-(actualBirkhoffTop38.Rbar38 c z)) / actualBirkhoffTop38.ZW38 c|
          ∂(fullWeightSequenceGaussian c)) atTop (𝓝 0)) ∧
    (∀ᵐ u : PhysicalL2 ∂(actualMuW c),
      ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
        NlsGge.HierarchyRiccati.Core.smoothL2_38 U hU hper = u ∧
        ∀ j : ℕ, chargeFn38 (j + 2) j u = NlsGge.HierarchyRiccati.Core.localCharge38 U j) ∧
    (∀ᵐ u : PhysicalL2 ∂(actualMuW c),
      ∀ m : ℕ, SobolevSquareSummable (m : ℝ) (physicalFourier u)) ∧
    (∀ (m : ℕ) (q : ℝ), 0 ≤ q →
      Integrable (fun u : PhysicalL2 => ‖physH38 m u‖ ^ q) (actualMuW c)) ∧
    (∀ (j : ℕ) (q : ℝ), 0 ≤ q →
      Integrable (fun u : PhysicalL2 => |chargeFn38 (j + 2) j u| ^ q) (actualMuW c)) ∧
    (∀ᵐ u : PhysicalL2 ∂(actualMuW c), ∀ n : ℤ,
      0 < actualGapActionAllE02_38 u n ∧
        actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n) ∧
    (∀ᵐ u : PhysicalL2 ∂(actualMuW c),
      ¬ {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite) ∧
    (∀ t : ℝ,
      ((actualMuW c).map (nlsFlowL2 t) = actualMuW c) ∧
      ∀ Λ : Finset ℤ, (actualNu c Λ).map (nlsFlowL2 t) = actualNu c Λ) ∧
    (∀ (m : ℕ) (hm : 1 ≤ m) (t : ℝ),
      Continuous (nlsFlowC m hm t) ∧
      ∀ F : SobolevCarrier38 (m : ℝ) →ᵇ ℝ,
        ∫ u, F (nlsFlowC m hm t (physH38 m u)) ∂(actualMuW c) =
          ∫ u, F (physH38 m u) ∂(actualMuW c)) ∧
    actualMuW c {u : PhysicalL2 | ¬ SobolevSquareSummable 1 (physicalFourier u)} = 0 := by
  have hM : BirkhoffMolnar38 actualBirkhoffTop38 := actualBirkhoffInput38.toMolnar
  let cc : BoundedCoefficients lower upper :=
    ⟨c, hlower, (hbound 0).trans (hupper 0), fun j => ⟨hbound j, hupper j⟩⟩
  have hcharges := NlsGge.ThirdConsultation.I030Aux.i030_of lower upper cc
    actualBirkhoffTop38 hM (actualMuW c) rfl
  have hconstruction := actualBirkhoffTop38.S04_01_03_38 lower upper c hlower hbound hupper
  refine ⟨(fun _ => rfl), hconstruction.1, hconstruction.2.1, hconstruction.2.2,
    ?_, ?_, ?_, hcharges.2.2, ?_, ?_, hcharges.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro Λ
    exact ⟨rfl,
      actualBirkhoffTop38.isProbabilityMeasure_nu38 lower upper c hlower hbound hupper Λ,
      actualBirkhoffTop38.ZcalΛ38_pos_le lower upper c hlower hbound hupper Λ,
      actualBirkhoffTop38.nuHat38_eq_relative lower upper c hlower hbound hupper Λ⟩
  · intro Λ z
    exact actualBirkhoffTop38.energy_finiteGap_charge_series38 lower upper c hlower hbound hupper Λ z
  · intro Λ hΛ
    exact ⟨actualBirkhoffTop38.weak_convergence_S04_38 lower upper c hlower hbound hupper hΛ,
      actualBirkhoffTop38.l1_density_convergence38 lower upper c hlower hbound hupper hΛ⟩
  · exact actualBirkhoffTop38.ae_muW38_allSobolev lower upper c hlower hbound hupper
  · intro m q hq
    let _ : MeasurableSpace (SobolevCarrier38 (m : ℝ)) := borel _
    have : BorelSpace (SobolevCarrier38 (m : ℝ)) := ⟨rfl⟩
    haveI := actualBirkhoffTop38.isProbabilityMeasure_muW38
      lower upper c hlower hbound hupper
    have hp := actualBirkhoffTop38.integrable_muW38_sobolev_pow
      lower upper c hlower hbound hupper hM m ⌈q⌉₊
    have hmeas : Measurable (fun u : PhysicalL2 => ‖physH38 m u‖ ^ q) :=
      ((measurable_physH38 m).norm).pow_const q
    refine ((integrable_const (1 : ℝ)).add hp).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact NlsGge.ThirdConsultation.I030Aux.rpow_le_one_add_pow_ceil _ q (norm_nonneg _) hq
  · exact actualBirkhoffTop38.ae_muW38_actions_pos lower upper c hlower hbound hupper
  · exact actualBirkhoffTop38.ae_muW38_not_finiteGap lower upper c hlower hbound hupper
  · intro t
    exact ⟨actualBirkhoffTop38.S04_08_nlsFlow_invariant_muW lower upper c hlower hbound hupper
        actualBirkhoffNLSFlowInput38 t,
      fun Λ => actualBirkhoffTop38.S04_07_nlsFlow_invariant_nu lower upper c hlower hbound hupper
        actualBirkhoffNLSFlowInput38 Λ t⟩
  · intro m hm t
    exact ⟨(continuous_nlsFlowC_uncurry m hm).comp (continuous_const.prodMk continuous_id),
      fun F => actualBirkhoffTop38.S04_08_nlsFlow_integral_Hm lower upper c hlower hbound hupper
        actualBirkhoffNLSFlowInput38 m hm t F⟩
  · exact actualBirkhoffTop38.muW38_junk_null_physical38 lower upper c hlower hbound hupper

end NlsGge.ThirdConsultation.Main

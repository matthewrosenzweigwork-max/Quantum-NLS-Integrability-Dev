import Mathlib
import NlsGge.Atomic.G5.G5019Sup3
import NlsGge.Atomic.G5.G5025Sup3

                                                                                
                                                                                                
                                                                                                                         
                                                                                                                           
                                                                                                                                  
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
namespace G5029Sup4Aux
noncomputable section

theorem continuousAt_fderiv_comp_realSlice (f : PotPair → ℂ) (U : Set PotPair) (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (u : PhysicalL2) (hu : realSlice u ∈ U) :
    ContinuousAt (fun w : PhysicalL2 => fderiv ℂ f (realSlice w)) u :=
  (hf.fderiv.continuousOn.continuousAt (hU.mem_nhds hu)).comp realSlice.continuous.continuousAt

theorem continuousAt_comp_realSlice (f : PotPair → ℂ) (U : Set PotPair) (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (u : PhysicalL2) (hu : realSlice u ∈ U) :
    ContinuousAt (fun w : PhysicalL2 => f (realSlice w)) u :=
  (hf.continuousOn.continuousAt (hU.mem_nhds hu)).comp realSlice.continuous.continuousAt

theorem continuousAt_angleDerivative (n : ℤ) (u : PhysicalL2)
    (hX : AnalyticOnNhd ℂ (cartesianX n) sourceBetaW)
    (hY : AnalyticOnNhd ℂ (cartesianY n) sourceBetaW)
    (hn : gamma2 (realSlice u) n ≠ 0) :
    ContinuousAt (fun w : PhysicalL2 => angleDerivative n (realSlice w)) u := by
  have hB : realSlice u ∈ sourceBetaW := sourceFamily.V_real (Set.mem_range_self u)
  have cX := continuousAt_comp_realSlice _ _ sourceFamily.V_open hX u hB
  have cY := continuousAt_comp_realSlice _ _ sourceFamily.V_open hY u hB
  have dX := continuousAt_fderiv_comp_realSlice _ _ sourceFamily.V_open hX u hB
  have dY := continuousAt_fderiv_comp_realSlice _ _ sourceFamily.V_open hY u hB
  have hr := G5025Sup3.radius_ne_zero u n hn
  have hinv : ContinuousAt (fun w : PhysicalL2 =>
      (cartesianX n (realSlice w) ^ 2 + cartesianY n (realSlice w) ^ 2)⁻¹) u :=
    ((cX.pow 2).add (cY.pow 2)).inv₀ hr
  exact hinv.smul ((cX.smul dY).sub (cY.smul dX))

theorem continuousAt_angleIntegralDerivative (k m : ℤ) (u : PhysicalL2)
    (hX : AnalyticOnNhd ℂ (cartesianX m) sourceBetaW)
    (hY : AnalyticOnNhd ℂ (cartesianY m) sourceBetaW)
    (hS : AnalyticOnNhd ℂ (betaSum m) sourceBetaW)
    (hT : AnalyticOnNhd ℂ (offDiagonalBeta m k) sourceW)
    (hm : gamma2 (realSlice u) m ≠ 0) :
    ContinuousAt (fun w : PhysicalL2 => angleIntegralDerivative k m (realSlice w)) u := by
  by_cases hkm : k = m
  · subst hkm
    have hB : realSlice u ∈ sourceBetaW := sourceFamily.V_real (Set.mem_range_self u)
    have hS' := continuousAt_fderiv_comp_realSlice _ _ sourceFamily.V_open hS u hB
    have h := (continuousAt_angleDerivative k u hX hY hm).sub hS'
    refine h.congr (Eventually.of_forall fun w => ?_)
    simp only [angleIntegralDerivative, ite_true, Pi.sub_apply]
  · exact G5019Sup3.continuousAt_angleIntegralDerivative_offDiag k m hkm hT u

theorem continuousOn_bracket_core (k l m n : ℤ)
    (hXY : ∀ j : ℤ, AnalyticOnNhd ℂ (cartesianX j) sourceBetaW ∧
      AnalyticOnNhd ℂ (cartesianY j) sourceBetaW)
    (hS : ∀ j : ℤ, AnalyticOnNhd ℂ (betaSum j) sourceBetaW)
    (hT : ∀ i j : ℤ, AnalyticOnNhd ℂ (offDiagonalBeta i j) sourceW) :
  ContinuousOn
    (fun u : PhysicalL2 =>
      pairPoissonCLM (angleIntegralDerivative k m (realSlice u))
        (angleIntegralDerivative l n (realSlice u)))
    {u : PhysicalL2 | gamma2 (realSlice u) m ≠ 0 ∧
      gamma2 (realSlice u) n ≠ 0} := by
  intro u hu
  have h1 := continuousAt_angleIntegralDerivative k m u (hXY m).1 (hXY m).2 (hS m) (hT m k) hu.1
  have h2 := continuousAt_angleIntegralDerivative l n u (hXY n).1 (hXY n).2 (hS n) (hT n l) hu.2
  have hP : ContinuousAt (fun w : PhysicalL2 =>
      pairPoissonCLM (angleIntegralDerivative k m (realSlice w))
        (angleIntegralDerivative l n (realSlice w))) u :=
    (G5019Sup3.continuous_pairPoissonCLM.continuousAt).comp (f := fun w : PhysicalL2 =>
      (angleIntegralDerivative k m (realSlice w), angleIntegralDerivative l n (realSlice w)))
      (h1.prodMk h2)
  exact hP.continuousWithinAt

end
end G5029Sup4Aux
end NlsGge.GKDefinitionDesign

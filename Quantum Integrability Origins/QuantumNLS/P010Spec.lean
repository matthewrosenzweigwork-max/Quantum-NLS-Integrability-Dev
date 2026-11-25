import QuantumNLS.Prop010SingleContourR17
/-! integrator-authored trusted spec for PROP-010 lem:B4-condensate-reconstruction (review record r23 FULL): headline statement(s) copied verbatim from Prop010SingleContourR17 (QuantumNLS.Prop010SingleContourR17). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open Set Filter Topology Complex MeasureTheory
open scoped ContDiff
namespace QuantumNLS.P010Spec
open QuantumNLS.Prop010SingleContourR17
open PhysicalTensor (L2T)
open RootCauchyFullBracketR8 (G)
open RootMassInvolutionR8 (mass)
open RootScalarPeriodR8 (cut)
open RootScalarPeriodR10 (symbol lambda exponent exponential)
open PeriodReconstructionCore PeriodReconstruction PeriodTwoTerm
open Prop010ContourBindingR11
open Prop010RectangleTransportR17
open LabelExactPeriod (rectIntegral)
variable {L κ : ℝ} [Fact (0<L)]

set_option maxHeartbeats 8000000 in
theorem condensate_reconstruction_spec (hκ : 0<κ) (u : L2T L) (hu : ‖u‖=1) (n : ℤ)
    {h : ℝ} (hh : 0<h) :
    ∃ F : ℂ × ℂ → ℂ,∃ H : ℂ × (ℂ × ℂ) → ℂ,
    ∃ hF : ContDiff ℝ ∞ F,∃ hFc : HasCompactSupport F,
    ∃ hH : ContDiff ℝ ∞ H,∃ hHc : HasCompactSupport H,∃ r>0,
      (∀ z ∈ Gam (cut hκ u (n-1)) (cut hκ u n) h,∀ w,
        ‖w-sf L κ (fun z => G hκ z u) z‖<r → F (z,w)=localLog L κ (fun z => G hκ z u) z w) ∧
      (∀ z ∈ Gam (cut hκ u (n-1)) (cut hκ u n) h,∀ w v,
        ‖w-sf L κ (fun z => G hκ z u) z‖<r → ‖v‖≤MixedQuadratures.Rbd L κ (h+1) →
        H (z,(w,v))=localCorrection L κ (fun z => G hκ z u) z w v) ∧
      (let f := Extension.ofSmooth F hF hFc
       let g := Extension.ofSmooth H hH hHc
       ∃ D≥0,∃ N₀ : ℕ,∀ (N : ℕ) (hN : 0<N),N₀≤N →
         IsSelfAdjoint (C L hκ hN f g (cut hκ u (n-1)) (cut hκ u n) h) ∧
         ‖C L hκ hN f g (cut hκ u (n-1)) (cut hκ u n) h‖≤K κ (cut hκ u (n-1)) (cut hκ u n) h f g ∧
         ‖(B L hκ hN n-C L hκ hN f g (cut hκ u (n-1)) (cut hκ u n) h)
           (HighMomentsOps.wvec N u)‖≤D*((N:ℝ)⁻¹)^2) ∧
      (∃ U : Set (L2T L),IsOpen U ∧ u ∈ U ∧
        (∀ v ∈ U,leadingSymbol hκ u n h F v=mass hκ n v) ∧
        (∀ v ∈ U,AnalyticAt ℝ (leadingSymbol hκ u n h F) v) ∧
        (∀ v ∈ U,fderiv ℝ (leadingSymbol hκ u n h F) v=fderiv ℝ (mass hκ n) v)) ∧
      (∀ v : L2T L,fderiv ℝ (mass hκ n) u v= -(2*Real.pi*κ)⁻¹*
        (rectIntegral (fun z => fderiv ℝ (fun w : L2T L => symbol κ w z) u v /
          Df L κ (fun z => G hκ z u) z) (cut hκ u (n-1)) (cut hκ u n) h).re) := by
  exact QuantumNLS.Prop010SingleContourR17.condensate_reconstruction hκ u hu n hh

end QuantumNLS.P010Spec
#print axioms QuantumNLS.P010Spec.condensate_reconstruction_spec

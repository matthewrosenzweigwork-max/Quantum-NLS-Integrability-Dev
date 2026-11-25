import QuantumNLS.RootH1Ratio
/-! integrator-authored trusted spec for R-D24009D4 lem:root-H1-ratio (terra_review r196 PASS): headline statement(s) copied verbatim from RootH1Ratio (QuantumNLS.RootH1Ratio). -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory Set Filter Topology ComplexConjugate
open scoped InnerProductSpace
open QuantumNLS.PhysicalTensor QuantumNLS.RootH1RatioOperator
  QuantumNLS.RootH1RatioNonlinear QuantumNLS.RootH1RatioContraction
  QuantumNLS.RootH1RatioBounds QuantumNLS.RootH1RatioConvergence
namespace QuantumNLS.RD24Spec
open QuantumNLS.RootH1Ratio
variable {L : ℝ} [hLf : Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem root_H1_ratio_spec {κ : ℝ} (hκ : 0 < κ) (u : L2T L) (hu : u ≠ 0) :
    (∀ Y : ℝ, ∀ hY0 : max 1 (max (Real.log 3/L) (16*κ*‖u‖^2)) ≤ Y,
      let hY := (height_spec u hY0).1
      let hlog := (height_spec u hY0).2.1
      ‖ratioInfAt hκ.le u Y‖ ≤ 2*Real.sqrt (‖u‖^2/Y) ∧
      (infinityResolvent hY hlog u - (κ:ℂ) • infinityResolvent hY hlog (cubic u (ratioInfAt hκ.le u Y))) = ratioInfAt hκ.le u Y ∧
      (∀ s : Linfty L, ‖s‖ ≤ 2*Real.sqrt (‖u‖^2/Y) → (infinityResolvent hY hlog u - (κ:ℂ) • infinityResolvent hY hlog (cubic u s)) = s →
        s = ratioInfAt hκ.le u Y) ∧
      (ratioAt hκ.le u Y =ᵐ[volume] ratioInfAt hκ.le u Y) ∧
      (∃ g d : ℝ → ℂ,
        HaarResolvent.IsH1Rep L (ratioAt hκ.le u Y) g d ∧ g L = g 0 ∧
        ∀ᵐ x : AddCircle L, d (HaarResolvent.rep1 L x) = u x-(Y:ℂ)*ratioAt hκ.le u Y x-
          (κ:ℂ)*conj (u x)*(ratioAt hκ.le u Y x)^2) ∧
      κ*‖ratioInfAt hκ.le u Y‖^2 ≤ 1/4 ∧
      ‖ratioAt hκ.le u Y‖ ≤ 5*‖u‖/(4*Y) ∧
      CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) ((Y:ℂ)*Complex.I) =
        -Complex.I*(∫ t in (0:ℝ)..L, conj (u (t:AddCircle L))*ratioAt hκ.le u Y (t:AddCircle L))) ∧
    Tendsto (fun Y : ℝ => (Y:ℂ) • ratioAt hκ.le u Y) atTop (nhds u) := by
  exact QuantumNLS.RootH1Ratio.root_H1_ratio hκ u hu

end QuantumNLS.RD24Spec
#print axioms QuantumNLS.RD24Spec.root_H1_ratio_spec

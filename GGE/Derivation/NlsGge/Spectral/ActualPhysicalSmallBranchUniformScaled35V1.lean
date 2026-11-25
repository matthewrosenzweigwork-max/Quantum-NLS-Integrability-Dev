import NlsGge.Spectral.ActualPhysicalSmallBranchUniformHighHeight35V1
import NlsGge.Spectral.ComplexInverseNearOneBound35V1
set_option autoImplicit false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot

/-- The actual small multiplier has uniform complex scaling, with one branch
chosen before every error tolerance, height and real frequency. This is the
high-height region only; it does not claim bounded-height escape, the source
full infinity condition, boundary extension or spectral labels. -/
theorem exists_actualPhysicalSmallBranch_uniformScaledHighHeight35 (u : PhysicalL2) :
    ∃ s ℓ : ℂ → ℂ,
      AnalyticOnNhd ℂ s {z : ℂ | 0 < z.im} ∧
      AnalyticOnNhd ℂ ℓ {z : ℂ | 0 < z.im} ∧
      (∀ z : ℂ, 0 < z.im → s z^2=actualPhysicalUnitHalfTrace32 u z^2-1) ∧
      (∀ z : ℂ, 0 < z.im → Complex.exp (ℓ z)=actualPhysicalUnitHalfTrace32 u z+s z) ∧
      (∀ z : ℂ, 0 < z.im → ‖actualPhysicalUnitHalfTrace32 u z+s z‖ < 1) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
        ∀ Y : ℝ, R ≤ Y → ∀ x : ℝ,
          ‖(actualPhysicalUnitHalfTrace32 u ((x : ℂ)+Complex.I*(Y : ℂ))+
              s ((x : ℂ)+Complex.I*(Y : ℂ)))/
            Complex.exp (Complex.I*((x : ℂ)+Complex.I*(Y : ℂ)))-1‖ < ε) := by
  obtain ⟨s,ℓ,hs,hl,hsq,he,hsmall,hu⟩ := exists_actualPhysicalSmallBranch_uniformHighHeight35 u
  refine ⟨s,ℓ,hs,hl,hsq,he,hsmall,?_⟩
  intro ε hε
  let η : ℝ := min (1/4) (ε/4)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  obtain ⟨R,hR,hbound⟩ := hu η hη
  refine ⟨R,hR,?_⟩
  intro Y hY x
  have h := complexInverse_near_one_bound35
    (((actualPhysicalUnitHalfTrace32 u ((x : ℂ)+Complex.I*(Y : ℂ))+
        s ((x : ℂ)+Complex.I*(Y : ℂ)))/
      Complex.exp (Complex.I*((x : ℂ)+Complex.I*(Y : ℂ))))⁻¹) η
    ((min_le_left (1/4) (ε/4)).trans (by norm_num)) (hbound Y hY x).le
  simp only [inv_inv] at h
  have hηε : η ≤ ε/4 := min_le_right _ _
  exact h.trans_lt (by linarith)

end NlsGge.SpectralFoundations
end

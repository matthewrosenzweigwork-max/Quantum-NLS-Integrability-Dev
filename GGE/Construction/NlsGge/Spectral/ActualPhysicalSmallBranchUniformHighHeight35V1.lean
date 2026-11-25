import NlsGge.Spectral.ActualPhysicalSmallRootUniformInverseBound35V2
import NlsGge.Spectral.ActualDysonGeometricCoefficientLimits34V3
import NlsGge.Spectral.ActualPhysicalUnitAnalyticSmallBranch33V5
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot

/-- A single actual UHP small branch has uniformly small scaled inverse error
above one height chosen BEFORE every real frequency. This only treats high
height; bounded-height escape and full source infinity remain open. -/
theorem exists_actualPhysicalSmallBranch_uniformHighHeight35 (u : PhysicalL2) :
    ∃ s ℓ : ℂ → ℂ,
      AnalyticOnNhd ℂ s {z : ℂ | 0 < z.im} ∧
      AnalyticOnNhd ℂ ℓ {z : ℂ | 0 < z.im} ∧
      (∀ z : ℂ, 0 < z.im → s z^2=actualPhysicalUnitHalfTrace32 u z^2-1) ∧
      (∀ z : ℂ, 0 < z.im → Complex.exp (ℓ z)=actualPhysicalUnitHalfTrace32 u z+s z) ∧
      (∀ z : ℂ, 0 < z.im → ‖actualPhysicalUnitHalfTrace32 u z+s z‖ < 1) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
        ∀ Y : ℝ, R ≤ Y → ∀ x : ℝ,
          ‖((actualPhysicalUnitHalfTrace32 u ((x : ℂ)+Complex.I*(Y : ℂ))+
              s ((x : ℂ)+Complex.I*(Y : ℂ)))/
            Complex.exp (Complex.I*((x : ℂ)+Complex.I*(Y : ℂ))))⁻¹-1‖ < ε) := by
  obtain ⟨s,ℓ,hs,hl,hsq,he,hsmall⟩ := exists_actualPhysicalUnitAnalyticSmallBranch33 u
  refine ⟨s,ℓ,hs,hl,hsq,he,hsmall,?_⟩
  let E : ℝ → ℝ := fun Y =>
    2*((‖u‖*Real.sqrt (‖u‖^2/(4*Y)))/(1-‖u‖*Real.sqrt (‖u‖^2/(4*Y))))+
      Real.exp (-2*Y)+Real.exp (-Y)
  have htwo : Tendsto (fun Y : ℝ => Real.exp (-2*Y)) atTop (𝓝 0) := by
    have hm : Tendsto (fun Y : ℝ => 2*Y) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_id
    simpa only [Function.comp_def,neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hm
  have hE : Tendsto E atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add] using
      (((actualDysonGeometricTailCoefficient_tendsto_zero34 u).const_mul 2).add htwo).add
        Real.tendsto_exp_neg_atTop_nhds_zero
  intro ε hε
  obtain ⟨r,hr⟩ := eventually_atTop.1
    ((actualDysonGeometricCoefficient_eventually_small34 u).and
      (hE.eventually (gt_mem_nhds hε)))
  refine ⟨max 1 r,lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _),?_⟩
  intro Y hY x
  have h := hr Y ((le_max_right 1 r).trans hY)
  have hz : 0 < ((x : ℂ)+Complex.I*(Y : ℂ)).im := by simpa using h.1.1
  exact (actualPhysicalSmallRoot_scaled_uniformInverseErrorBound35 u x Y h.1.1 h.1.2
    (s ((x : ℂ)+Complex.I*(Y : ℂ)))
    (hsq _ hz) (hsmall _ hz).le).trans_lt h.2

end NlsGge.SpectralFoundations
end

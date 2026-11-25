import NlsGge.GK38.GradFundamentalPotential

/-! # K1: vanishing-factor remainder estimate. -/
set_option autoImplicit false
open Filter Topology Asymptotics
namespace NlsGge.GK38
noncomputable section

/-- A bounded linear-order remainder with a vanishing factor is little-o. -/
theorem k1LittleO_norm_factor38 {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : E → F) (q : E → ℝ) (K : ℝ) (hK : 0 ≤ K) (hq0 : ∀ h, 0 ≤ q h)
    (hq : Tendsto q (𝓝 0) (𝓝 0)) (hb : ∀ h, ‖f h‖ ≤ K * ‖h‖ * q h) :
    f =o[𝓝 0] (fun h : E => h) := by
  apply isLittleO_iff.mpr
  intro ε hε
  have hK1 : 0 < K + 1 := by positivity
  have hsmall := (tendsto_order.1 hq).2 (ε / (K + 1)) (div_pos hε hK1)
  filter_upwards [hsmall] with h hh
  have hscaled : K * q h ≤ ε := by
    have hh' := (lt_div_iff₀ hK1).mp hh
    nlinarith [hq0 h]
  calc
    ‖f h‖ ≤ K * ‖h‖ * q h := hb h
    _ = (K * q h) * ‖h‖ := by ring
    _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right hscaled (norm_nonneg _)


/-- The Fréchet criterion, isolated before the concrete potential application. -/
theorem k1HasFDerivAt_of_remainder38 {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E → F) (D : E →L[𝕜] F) (x : E)
    (hr : (fun h : E => f (x + h) - f x - D h) =o[𝓝 0] (fun h : E => h)) :
    HasFDerivAt f D x := hasFDerivAt_iff_isLittleO_nhds_zero.mpr hr

end
end NlsGge.GK38

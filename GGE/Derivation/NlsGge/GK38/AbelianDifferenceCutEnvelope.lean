import NlsGge.GK38.AbelianPaddedJacobianColumns
import NlsGge.GK38.AbelianCutEnvelope

/-! UNCOMPILED actual cut bounds for the finite difference factor. These are
the actual zero-input row envelope, not new spectral/tail hypotheses. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p6CutCenter_envelope38 (φ : PotPair) (hφ : φ ∈ gkW) (m : ℤ)
    (z : ℂ) (hz : z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m)) :
    ‖z-(m : ℂ)*(Real.pi : ℂ)‖ ≤ p2RowEnvelope38 φ 0 m := by
  have h := p2Sigma_cut_envelope38 φ hφ (0 : Lib.L2Seq) m z hz
  simpa only [Lib.sigmaOf,lp.coeFn_zero,Pi.zero_apply,add_zero,norm_sub_rev] using h

theorem p6CutCenter_envelope_summable38 (φ : PotPair) (hφ : φ ∈ gkW) :
    Summable (fun m : ℤ => p2RowEnvelope38 φ 0 m^2) := by
  obtain ⟨U,hU,_hUW,V,hV,B,_hB,h⟩ := p2RowEnvelope_common_l2_bound38 φ hφ 0
  exact (h φ (mem_of_mem_nhds hU) 0 (mem_of_mem_nhds hV)).1

theorem p6Difference_cut_factor_bound38 (φ : PotPair) (hφ : φ ∈ gkW)
    (s : Lib.L2Seq) (n m : ℤ) (z : ℂ)
    (hz : z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m)) :
    ‖(z-(m : ℂ)*(Real.pi : ℂ)-s n)/(Real.pi : ℂ)‖ ≤
      (‖s n‖+p2RowEnvelope38 φ 0 m)/Real.pi := by
  have h := (norm_sub_le (z-(m : ℂ)*(Real.pi : ℂ)) (s n)).trans
    (add_le_add (p6CutCenter_envelope38 φ hφ m z hz) le_rfl)
  rw [norm_div,Complex.norm_of_nonneg Real.pi_pos.le]
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  linarith

end
end NlsGge.GK38

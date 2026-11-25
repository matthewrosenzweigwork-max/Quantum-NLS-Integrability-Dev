import NlsGge.GK38.AbelianRowEnvelope
import Mathlib.Analysis.Normed.Module.Convex

/-! Actual complex cut-to-row envelope. UNCOMPILED prospective source.
No real-endpoint, open-gap, or nonzero-amplitude restriction occurs. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

 theorem p2Segment_midpoint_norm_le38 (a b z : ℂ) (hz : z ∈ segment ℝ a b) :
    ‖z-(a+b)/2‖ ≤ ‖b-a‖/2 := by
  have ha : a ∈ closedBall ((a+b)/2) (‖b-a‖/2) := by
    rw [mem_closedBall_iff_norm]
    have he : a-(a+b)/2=-(b-a)/2 := by ring
    rw [he,norm_div,norm_neg,Complex.norm_ofNat]
  have hb : b ∈ closedBall ((a+b)/2) (‖b-a‖/2) := by
    rw [mem_closedBall_iff_norm]
    have he : b-(a+b)/2=(b-a)/2 := by ring
    rw [he,norm_div,Complex.norm_ofNat]
  exact mem_closedBall_iff_norm.mp
    ((convex_closedBall ((a+b)/2) (‖b-a‖/2)).segment_subset ha hb hz)

/-- The actual spectral cut is controlled by the actual labelled midpoint and width. -/
theorem p2Actual_cut_midpoint_norm_le38 (φ : PotPair) (hφ : φ ∈ gkW) (m : ℤ) (z : ℂ)
    (hz : z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m)) :
    ‖z-tauN φ m‖ ≤ ‖lamPlus φ m-lamMinus φ m‖/2 := by
  rw [tauN_value38 φ hφ m,add_comm (lamPlus φ m)]
  exact p2Segment_midpoint_norm_le38 (lamMinus φ m) (lamPlus φ m) z hz

/-- The numerator estimate is valid at EVERY point of the actual complex cut. -/
theorem p2Sigma_cut_envelope38 (φ : PotPair) (hφ : φ ∈ gkW) (s : Lib.L2Seq)
    (m : ℤ) (z : ℂ) (hz : z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m)) :
    ‖Lib.sigmaOf s m-z‖ ≤ p2RowEnvelope38 φ s m := by
  have he : Lib.sigmaOf s m-z = s m-(tauN φ m-(m:ℂ)*(Real.pi:ℂ))+(tauN φ m-z) := by
    unfold Lib.sigmaOf
    ring
  have hcut := p2Actual_cut_midpoint_norm_le38 φ hφ m z hz
  rw [norm_sub_rev] at hcut
  rw [he]
  exact (norm_add_le _ _).trans
    ((add_le_add (norm_sub_le _ _) hcut).trans_eq (by rfl))

#print axioms p2Segment_midpoint_norm_le38
#print axioms p2Actual_cut_midpoint_norm_le38
#print axioms p2Sigma_cut_envelope38
end
end NlsGge.GK38

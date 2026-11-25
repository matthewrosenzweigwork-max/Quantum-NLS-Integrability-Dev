import NlsGge.GK38.AbelianNumeratorVariation
import NlsGge.GK38.Lib.EntireProductsC34h
import NlsGge.Analysis.AnalyticTsum38

/-! A parameter Cauchy estimate transfers the accepted genuine product bound
to its actual directional variation, before finite-head/direction-tail decay.
This does not itself assert o(1) or interpolation uniqueness. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38.P4NumeratorVariation
noncomputable section

theorem variation_counting_circle_bound (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Lib.L2Seq, ‖s‖ ≤ K → ∀ h : Lib.L2Seq,
      ∀ n : ℤ, ∀ N : ℕ, ∀ z : ℂ, ‖z‖ = N*Real.pi+Real.pi/2 →
        ‖p4NumeratorVariation38 n s h z‖*‖z-(n : ℂ)*(Real.pi : ℂ)‖ ≤
          C*‖h‖*‖Complex.sin z‖ := by
  obtain ⟨C,hC,hprod⟩ := Lib.omitProd_circle_bound_dist (K+1)
  refine ⟨2*C,by positivity,?_⟩
  intro s hs h n N z hz
  let d : ℂ := z-(n : ℂ)*(Real.pi : ℂ)
  let g : Lib.L2Seq → ℂ := fun q => p2FullNumerator38 n q z*d
  have hg : AnalyticOnNhd ℂ g univ := by
    intro q _
    have ha := AnalyticAt.comp
      (g := fun p : ℂ × Lib.L2Seq => p2FullNumerator38 n p.2 p.1)
      (f := fun q : Lib.L2Seq => (z,q))
      (p2FullNumerator_joint_analytic38 n (z,q) (mem_univ _))
      (analyticAt_const.prod analyticAt_id)
    exact ha.mul analyticAt_const
  have hb : ∀ q ∈ closedBall s (1 : ℝ), ‖g q‖ ≤ 2*C*‖Complex.sin z‖ := by
    intro q hq
    have hdist : ‖q-s‖ ≤ 1 := by simpa only [mem_closedBall,dist_eq_norm] using hq
    have hnorm : ‖q‖ ≤ K+1 := by
      have he := norm_add_le (q-s) s
      rw [sub_add_cancel] at he
      linarith
    have hp := mul_le_mul_of_nonneg_left (hprod q hnorm n N z hz)
      (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [g,p2FullNumerator38,norm_mul,norm_neg,Complex.norm_ofNat,mul_assoc] using hp
  have hbound : ‖fderiv ℂ g s‖ ≤ 2*C*‖Complex.sin z‖ := by
    have hb' := NlsGge.AnalyticTsum38.norm_fderiv_le_of_closedBall38
      (hg.mono (subset_univ (closedBall s (1 : ℝ)))) hb
      (y := s) (r' := 0) (R := 1) (by simp) (by norm_num) (by norm_num)
    simpa only [div_one] using hb'
  have hline : HasDerivAt (fun t : ℂ => s+t • h) h 0 := by
    simpa only [one_smul] using! (((hasDerivAt_id (0 : ℂ)).smul_const h).const_add s)
  have hd := ((hg s (mem_univ _)).differentiableAt.hasFDerivAt).comp_hasDerivAt_of_eq
    0 hline (by simp)
  have hv := (variation_hasDerivAt n s h z).mul_const d
  have he : (fderiv ℂ g s) h = p4NumeratorVariation38 n s h z*d := hd.unique hv
  calc
    _ = ‖p4NumeratorVariation38 n s h z*d‖ := (norm_mul _ _).symm
    _ = ‖(fderiv ℂ g s) h‖ := congrArg norm he.symm
    _ ≤ ‖fderiv ℂ g s‖*‖h‖ := (fderiv ℂ g s).le_opNorm h
    _ ≤ (2*C*‖Complex.sin z‖)*‖h‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
    _ = _ := by ring

end
end NlsGge.GK38.P4NumeratorVariation

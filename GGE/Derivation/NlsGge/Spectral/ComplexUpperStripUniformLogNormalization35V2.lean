import NlsGge.Spectral.ComplexLogarithmUpperStripIntegerConstancy35V1
import Mathlib.Topology.MetricSpace.Pseudo.Defs
set_option autoImplicit false
noncomputable section
open Set
namespace NlsGge.SpectralFoundations

/-- Scalar logarithm normalization with one integer on a whole high upper
strip. Uniform convergence of the scaled exponential is an explicit scalar
hypothesis; this lemma supplies no NLS operator or full-infinity assertion. -/
theorem complexUpperStrip_uniformLogNormalization35V2
    (L : ℂ → ℂ) (hL : ContinuousOn L {z : ℂ | 0 < z.im})
    (hu : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ Y : ℝ, R ≤ Y → ∀ x : ℝ,
        ‖Complex.exp (L ((x : ℂ)+Complex.I*(Y : ℂ))-
          Complex.I*((x : ℂ)+Complex.I*(Y : ℂ)))-1‖ < ε) :
    ∃ m : ℤ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ Y : ℝ, R ≤ Y → ∀ x : ℝ,
        ‖L ((x : ℂ)+Complex.I*(Y : ℂ))-
          Complex.I*((x : ℂ)+Complex.I*(Y : ℂ))-
          (m : ℂ)*(2*Real.pi*Complex.I)‖ < ε := by
  let w : ℂ → ℂ := fun z => Complex.exp (L z-Complex.I*z)
  obtain ⟨a, ha, hnear⟩ := hu (1/2) (by norm_num)
  have hp : ∀ z ∈ {z : ℂ | a < z.im}, w z ∈ Complex.slitPlane := by
    intro z hz
    have hn : ‖w z-1‖ < (1/2 : ℝ) := by
      have h := hnear z.im (le_of_lt hz) z.re
      have heq : (z.re : ℂ)+Complex.I*(z.im : ℂ)=z := by
        rw [mul_comm Complex.I, Complex.re_add_im]
      rw [heq] at h
      exact h
    have hr : |(w z-1).re| ≤ ‖w z-1‖ := Complex.abs_re_le_norm _
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Complex.sub_re, Complex.one_re] at hr
    have hneg := neg_abs_le ((w z).re-1)
    linarith
  have hpos : {z : ℂ | a < z.im} ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    exact ha.trans hz
  have hc : ContinuousOn (fun z : ℂ => L z-Complex.I*z) {z : ℂ | a < z.im} :=
    (hL.mono hpos).sub (continuous_const.mul continuous_id).continuousOn
  have hw : ContinuousOn w {z : ℂ | a < z.im} :=
    Complex.continuous_exp.comp_continuousOn hc
  have hlog : ContinuousOn (fun z => Complex.log (w z)) {z : ℂ | a < z.im} := by
    intro z hz
    exact (_root_.continuousAt_clog (hp z hz)).comp_continuousWithinAt (hw z hz)
  let g : ℂ → ℂ := fun z => L z-Complex.I*z-Complex.log (w z)
  have hg : ContinuousOn g {z : ℂ | a < z.im} := hc.sub hlog
  have he : ∀ z ∈ {z : ℂ | a < z.im}, Complex.exp (g z)=1 := by
    intro z hz
    dsimp [g]
    rw [Complex.exp_sub, Complex.exp_log (Complex.slitPlane_ne_zero (hp z hz))]
    exact div_self (Complex.exp_ne_zero (L z-Complex.I*z))
  obtain ⟨m, hm⟩ := complexLogarithmUpperStrip_integer_constant35 a g hg he
  refine ⟨m, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hδlog⟩ := Metric.continuousAt_iff.mp
    (_root_.continuousAt_clog Complex.one_mem_slitPlane) ε hε
  obtain ⟨r, hr, hbound⟩ := hu δ hδ
  refine ⟨max r (a+1), lt_of_lt_of_le hr (le_max_left _ _), ?_⟩
  intro Y hY x
  let z : ℂ := (x : ℂ)+Complex.I*(Y : ℂ)
  have hz : a < z.im := by
    have hb : a+1 ≤ Y := (le_max_right r (a+1)).trans hY
    dsimp [z]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add]
    linarith
  have hdist : dist (w z) 1 < δ := by
    rw [dist_eq_norm]
    exact hbound Y ((le_max_left r (a+1)).trans hY) x
  have hsmall : ‖Complex.log (w z)‖ < ε := by
    simpa only [Complex.log_one, dist_zero_right] using hδlog hdist
  have heq : L z-Complex.I*z-(m : ℂ)*(2*Real.pi*Complex.I)=Complex.log (w z) := by
    have h := hm z hz
    dsimp [g] at h
    linear_combination h
  change ‖L z-Complex.I*z-(m : ℂ)*(2*Real.pi*Complex.I)‖ < ε
  rwa [heq]

end NlsGge.SpectralFoundations
end

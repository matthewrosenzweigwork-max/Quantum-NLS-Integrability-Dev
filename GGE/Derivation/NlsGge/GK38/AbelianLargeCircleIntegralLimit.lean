import NlsGge.GK38.AbelianLargeCircleQuotientError
import NlsGge.GK38.AbelianLargeCircleCutComplement
import Mathlib.Analysis.Complex.CauchyIntegral

/-! The large-circle step of the book's period argument. Genuine contour
integrability precedes subtraction and evaluation. No finite-hole excision or
small-cycle period identity is asserted here. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p6LargeCircle_model_kernel38 (w : ℂ) (r : ℝ) (hr : 0 < r)
    (hw : ‖w‖ < r) :
    CircleIntegrable (fun z : ℂ => Complex.I/(w-z)) 0 r ∧
      (∮ z in C(0,r), Complex.I/(w-z))=2*(Real.pi : ℂ) := by
  have hden : ∀ z ∈ sphere (0 : ℂ) r, w-z ≠ 0 := by
    intro z hz he
    have hzw : z=w := (sub_eq_zero.mp he).symm
    have hn : ‖z‖=r := mem_sphere_zero_iff_norm.mp hz
    exact (ne_of_lt hw) (hzw ▸ hn)
  have hci : CircleIntegrable (fun z : ℂ => Complex.I/(w-z)) 0 r :=
    (continuousOn_const.div (continuousOn_const.sub continuousOn_id) hden).circleIntegrable hr.le
  refine ⟨hci,?_⟩
  have he : (fun z : ℂ => Complex.I/(w-z))=
      (fun z : ℂ => (-Complex.I)*(z-w)⁻¹) := by
    funext z
    rw [div_eq_mul_inv,← neg_sub z w,inv_neg]
    ring
  rw [he,circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_zero_iff.mpr hw)]
  ring_nf
  simp [Complex.I_sq]

theorem p6LargeCircle_integral_error38 (f : ℂ → ℂ) (w : ℂ) (r δ : ℝ)
    (hr : 0 < r) (hw : ‖w‖ ≤ r/2)
    (hf : CircleIntegrable f 0 r)
    (herr : ∀ z ∈ sphere (0 : ℂ) r, ‖(w-z)*f z-Complex.I‖ ≤ δ) :
    ‖(∮ z in C(0,r), f z)-2*(Real.pi : ℂ)‖ ≤ 4*Real.pi*δ := by
  have hwr : ‖w‖ < r := by linarith
  obtain ⟨hk,hki⟩ := p6LargeCircle_model_kernel38 w r hr hwr
  have hp : ∀ z ∈ sphere (0 : ℂ) r,
      ‖f z-Complex.I/(w-z)‖ ≤ 2*δ/r := by
    intro z hz
    have hn : ‖z‖=r := mem_sphere_zero_iff_norm.mp hz
    have hlow : r/2 ≤ ‖w-z‖ := by
      have ht := norm_sub_norm_le z w
      rw [norm_sub_rev z w,hn] at ht
      linarith
    have hden : w-z ≠ 0 := norm_pos_iff.mp (by linarith)
    have he : (w-z)*(f z-Complex.I/(w-z))=(w-z)*f z-Complex.I := by
      field_simp [hden]
    have hm : ‖w-z‖*‖f z-Complex.I/(w-z)‖ ≤ δ := by
      rw [← norm_mul,he]
      exact herr z hz
    apply (le_div_iff₀ hr).mpr
    nlinarith [norm_nonneg (f z-Complex.I/(w-z))]
  rw [← hki,← circleIntegral.integral_sub hf hk]
  calc
    _ ≤ 2*Real.pi*r*(2*δ/r) :=
      circleIntegral.norm_integral_le_of_norm_le_const hr.le hp
    _ = 4*Real.pi*δ := by
      rw [← mul_div_assoc]
      apply (div_eq_iff (ne_of_gt hr)).mpr
      ring

theorem p6Actual_large_circle_full_quotient_integral_limit38
    (φ : PotPair) (hφ : φ ∈ gkW) (s : Lib.L2Seq) (n : ℤ) :
    ∀ ε > 0, ∃ N : ℕ, ∀ ν : ℕ, N ≤ ν →
      CircleIntegrable (fun z : ℂ => p2FullNumerator38 n s z/canonRoot38 φ z)
        0 (ν*Real.pi+Real.pi/2) ∧
      ‖(∮ z in C(0,ν*Real.pi+Real.pi/2),
        p2FullNumerator38 n s z/canonRoot38 φ z)-2*(Real.pi : ℂ)‖ ≤ ε := by
  intro ε hε
  let δ : ℝ := ε/(4*Real.pi)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨NE,hNE⟩ := p6Actual_full_numerator_root_large_circle_weighted_error38 φ hφ s δ hδ
  obtain ⟨NI,hNI⟩ := p6Actual_large_circle_full_quotient_integrable38 φ hφ s
  obtain ⟨NS,hNS⟩ := exists_nat_gt (2*‖Lib.sigmaOf s n‖/Real.pi)
  refine ⟨max NE (max NI NS),fun ν hν => ?_⟩
  have he : NE ≤ ν := (le_max_left _ _).trans hν
  have hi : NI ≤ ν := (le_max_left NI NS).trans ((le_max_right _ _).trans hν)
  have hs : NS ≤ ν := (le_max_right NI NS).trans ((le_max_right _ _).trans hν)
  have hsc : (NS : ℝ) ≤ ν := by exact_mod_cast hs
  have hsize : ‖Lib.sigmaOf s n‖ ≤ (ν*Real.pi+Real.pi/2)/2 := by
    have hNS := (div_lt_iff₀ Real.pi_pos).mp hNS
    nlinarith [Real.pi_pos]
  refine ⟨hNI ν hi n,?_⟩
  have hb := p6LargeCircle_integral_error38
    (fun z : ℂ => p2FullNumerator38 n s z/canonRoot38 φ z)
    (Lib.sigmaOf s n) (ν*Real.pi+Real.pi/2) δ (by positivity) hsize
    (hNI ν hi n) (fun z hz => hNE ν he z (mem_sphere_zero_iff_norm.mp hz) n)
  have hscale : 4*Real.pi*δ=ε := by
    dsimp only [δ]
    rw [← mul_div_assoc,mul_div_cancel_left₀ ε (by positivity : (4*Real.pi : ℝ) ≠ 0)]
  exact hb.trans_eq hscale

end
end NlsGge.GK38

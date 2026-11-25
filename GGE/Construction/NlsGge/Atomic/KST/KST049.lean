import Mathlib
import NlsGge.Atomic.KST.KST004
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST019
import NlsGge.Atomic.KST.KST020
import NlsGge.ThirdConsultation.KST.KST047Host
import NlsGge.Atomic.KST.KST047
import NlsGge.Atomic.KST.KST048
import NlsGge.Analysis.EvenLogDisk38

                                                                                                        
                                                                                                    
                                                            
                                                                                                              
                                                                                                                    
                                                                                                   
                                                                 
set_option autoImplicit false
noncomputable section
open NlsGge.Atomic.KST004

namespace NlsGge.ThirdConsultation.KST

theorem kst049 (n : ℤ) (a b c : ℂ → ℂ) (σ ξ : ℂ)
    (h : Balanced n a b c σ) (hξ : ξ^2 = b σ*c σ) :
  ∃ q : ℂ → ℂ,
    AnalyticOnNhd ℂ q (Metric.ball σ (2*rootRadius b c σ)) ∧ q σ = ξ ∧
    ∀ z ∈ Metric.ball σ (2*rootRadius b c σ),
      q z^2 = b z*c z ∧ q z ≠ 0 ∧
      HasDerivAt q (deriv q z) z ∧ ‖deriv q z‖ ≤ (4/21 : ℝ) := by
  obtain ⟨hr0, -, -, -, -, hdisc⟩ := kst047 n a b c σ h
  have h48 := kst048 n a b c σ h
  obtain ⟨⟨-, hb, hc, -⟩, -, -, hbc, -, -⟩ := h
  set r := rootRadius b c σ with hr
  have hσb : b σ ≠ 0 := left_ne_zero_of_mul hbc
  have hσc : c σ ≠ 0 := right_ne_zero_of_mul hbc
  have hξ0 : ξ ≠ 0 := by
    intro h0
    rw [h0] at hξ
    exact hbc (by rw [← hξ]; ring)
  have hballstrip : Metric.ball σ (2 * r) ⊆ spectralStrip n := fun z hz =>
    closedBall_subset_strip_of_le n (r := Real.pi / 3) (by linarith [Real.pi_pos])
      (Metric.ball_subset_closedBall (hdisc (Metric.ball_subset_closedBall hz)))
  have hbA : AnalyticOnNhd ℂ b (Metric.ball σ (2 * r)) := hb.mono hballstrip
  have hcA : AnalyticOnNhd ℂ c (Metric.ball σ (2 * r)) := hc.mono hballstrip
  have hr2 : (0 : ℝ) < 2 * r := by linarith
  have hr2C : ((2 * r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr2.ne'
  -- affine chart  T : unit disc -> root disc,  S = T⁻¹
  set T : ℂ → ℂ := fun ζ => σ + ((2 * r : ℝ) : ℂ) * ζ with hT
  set S : ℂ → ℂ := fun z => (z - σ) / ((2 * r : ℝ) : ℂ) with hS
  have hTan : AnalyticOnNhd ℂ T Set.univ := fun ζ _ =>
    analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have hSan : AnalyticOnNhd ℂ S Set.univ := fun z _ =>
    (analyticAt_id.sub analyticAt_const).div analyticAt_const hr2C
  have hTS : ∀ z, T (S z) = z := fun z => by
    simp only [hT, hS]; field_simp; ring
  have hST : ∀ ζ, S (T ζ) = ζ := fun ζ => by
    simp only [hT, hS]; field_simp; ring
  have hTmaps : Set.MapsTo T (Metric.ball 0 1) (Metric.ball σ (2 * r)) := by
    intro ζ hζ
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hζ
    rw [Metric.mem_ball, dist_eq_norm]
    have : T ζ - σ = ((2 * r : ℝ) : ℂ) * ζ := by simp only [hT]; ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr2.le]
    nlinarith
  have hSmaps : Set.MapsTo S (Metric.ball σ (2 * r)) (Metric.ball 0 1) := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    simp only [hS]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr2.le, div_lt_one hr2]
    exact hz
  -- the product on the unit disc
  set g : ℂ → ℂ := fun ζ => b (T ζ) * c (T ζ) with hg
  have hgA : AnalyticOnNhd ℂ g (Metric.ball 0 1) := by
    have h1 : AnalyticOnNhd ℂ (b ∘ T) (Metric.ball 0 1) :=
      hbA.comp (hTan.mono (Set.subset_univ _)) hTmaps
    have h2 : AnalyticOnNhd ℂ (c ∘ T) (Metric.ball 0 1) :=
      hcA.comp (hTan.mono (Set.subset_univ _)) hTmaps
    exact fun ζ hζ => (h1 ζ hζ).mul (h2 ζ hζ)
  have hgne : ∀ ζ ∈ Metric.ball (0 : ℂ) 1, g ζ ≠ 0 := by
    intro ζ hζ
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hbne, hcne, -, -⟩ :=
      h48 (T ζ) (Metric.ball_subset_closedBall (hTmaps hζ))
    exact mul_ne_zero hbne hcne
  have hT0 : T 0 = σ := by simp [hT]
  have hg0 : g 0 = b σ * c σ := by simp only [hg, hT0]
  have hℓ₀ : Complex.exp (2 * Complex.log ξ) = g 0 := by
    rw [hg0, ← hξ, two_mul, Complex.exp_add, Complex.exp_log hξ0, sq]
  obtain ⟨ℓ, hℓA, hℓexp, hℓ0⟩ :=
    NlsGge.Analysis.exists_analytic_log_ball38 hgA.differentiableOn hgne hℓ₀
  -- the square root
  set q : ℂ → ℂ := fun z => Complex.exp (ℓ (S z) / 2) with hq
  have hqA : AnalyticOnNhd ℂ q (Metric.ball σ (2 * r)) := by
    intro z hz
    have h1 : AnalyticAt ℂ (fun w => ℓ (S w)) z :=
      (hℓA (S z) (hSmaps hz)).comp (hSan z (Set.mem_univ _))
    exact (h1.div analyticAt_const two_ne_zero).cexp'
  have hqsq : ∀ z ∈ Metric.ball σ (2 * r), q z ^ 2 = b z * c z := by
    intro z hz
    have e1 : q z ^ 2 = Complex.exp (ℓ (S z)) := by
      simp only [hq]
      rw [sq, ← Complex.exp_add]
      congr 1; ring
    rw [e1, hℓexp (S z) (hSmaps hz)]
    simp only [hg, hTS]
  have hqσ : q σ = ξ := by
    have hS0 : S σ = 0 := by simp [hS]
    simp only [hq, hS0, hℓ0]
    rw [show (2 * Complex.log ξ) / 2 = Complex.log ξ by ring, Complex.exp_log hξ0]
  refine ⟨q, hqA, hqσ, fun z hz => ?_⟩
  have hzc : z ∈ Metric.closedBall σ (2 * r) := Metric.ball_subset_closedBall hz
  obtain ⟨-, hbd, hcd, -, hb'', hc'', -, -, -, -, hbne, hcne, hbc13, hcb13⟩ := h48 z hzc
  have hqne : q z ≠ 0 := by
    intro h0
    have := hqsq z hz
    rw [h0] at this
    exact mul_ne_zero hbne hcne (by rw [← this]; ring)
  have hqd : HasDerivAt q (deriv q z) z :=
    ((hqA z hz).differentiableAt).hasDerivAt
  refine ⟨hqsq z hz, hqne, hqd, ?_⟩
  -- differentiate q^2 = b c
  have hnhds : Metric.ball σ (2 * r) ∈ nhds z := Metric.isOpen_ball.mem_nhds hz
  have hD1 : HasDerivAt (fun w => b w * c w) (deriv b z * c z + b z * deriv c z) z :=
    hbd.mul hcd
  have hD2 : HasDerivAt (fun w => q w ^ 2) (2 * q z * deriv q z) z := by
    have h1 := hqd.mul hqd
    have e : (fun w => q w ^ 2) = fun w => q w * q w := funext fun w => sq (q w)
    rw [e]
    convert h1 using 1
    ring
  have hD3 : HasDerivAt (fun w => q w ^ 2) (deriv b z * c z + b z * deriv c z) z :=
    hD1.congr_of_eventuallyEq
      (Filter.eventually_of_mem hnhds (fun w hw => hqsq w hw))
  have hkey : 2 * q z * deriv q z = deriv b z * c z + b z * deriv c z := hD2.unique hD3
  -- norms
  set x := ‖b z‖ with hx
  set y := ‖c z‖ with hy
  have hxpos : 0 < x := norm_pos_iff.2 hbne
  have hypos : 0 < y := norm_pos_iff.2 hcne
  have hqn : ‖q z‖ ^ 2 = x * y := by
    rw [← norm_pow, hqsq z hz, norm_mul]
  have hqpos : 0 < ‖q z‖ := norm_pos_iff.2 hqne
  have hxy1 : y ≤ 13 * x := by
    have := hbc13
    rw [norm_div, div_le_iff₀ hypos] at this
    have h2 := hcb13
    rw [norm_div, div_le_iff₀ hxpos] at h2
    linarith
  have hxy2 : x ≤ 13 * y := by
    have := hbc13
    rw [norm_div, div_le_iff₀ hypos] at this
    linarith
  have hsum : x + y ≤ 8 * ‖q z‖ := by
    by_contra hcon
    push_neg at hcon
    have h3 : (8 * ‖q z‖) * (8 * ‖q z‖) < (x + y) * (x + y) :=
      mul_self_lt_mul_self (by positivity) hcon
    nlinarith [mul_nonneg (sub_nonneg.2 hxy1) (sub_nonneg.2 hxy2)]
  have hnorm : 2 * ‖q z‖ * ‖deriv q z‖ ≤ (x + y) / 21 := by
    calc 2 * ‖q z‖ * ‖deriv q z‖ = ‖2 * q z * deriv q z‖ := by
          rw [norm_mul, norm_mul]; norm_num
      _ = ‖deriv b z * c z + b z * deriv c z‖ := by rw [hkey]
      _ ≤ ‖deriv b z * c z‖ + ‖b z * deriv c z‖ := norm_add_le _ _
      _ = ‖deriv b z‖ * y + x * ‖deriv c z‖ := by rw [norm_mul, norm_mul]
      _ ≤ (1 / 21) * y + x * (1 / 21) := by
          gcongr
      _ = (x + y) / 21 := by ring
  by_contra hcon
  push_neg at hcon
  nlinarith [mul_lt_mul_of_pos_left hcon hqpos]

end NlsGge.ThirdConsultation.KST
end

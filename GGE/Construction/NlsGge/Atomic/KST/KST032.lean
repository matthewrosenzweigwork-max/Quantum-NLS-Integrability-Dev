import Mathlib
import NlsGge.ThirdConsultation.KST.KST032Host
import NlsGge.Atomic.KST.KST031

                                                                                                        
                                                                                                    
                                                                                              
                                                                                                            
                                                                                                               
                                                                                                          
                                                                                      
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ENNReal
open NlsGge.Atomic.KST004

namespace NlsGge.ThirdConsultation.KST

attribute [local instance] Classical.propDecidable

namespace KST032S

theorem closedBall_sub_strip (n : ℤ) (z : ℂ)
    (hz : z ∈ Metric.closedBall (center n) (Real.pi/48)) (r : ℝ) (hr : r ≤ 23 * Real.pi / 48) :
    Metric.closedBall z r ⊆ spectralStrip n := by
  intro u hu
  have h1 : ‖u - z‖ ≤ r := by simpa [dist_eq_norm] using Metric.mem_closedBall.1 hu
  have h2 : ‖z - center n‖ ≤ Real.pi / 48 := by simpa [dist_eq_norm] using Metric.mem_closedBall.1 hz
  have h3 : ‖u - center n‖ ≤ Real.pi / 2 := by
    calc ‖u - center n‖ = ‖(u - z) + (z - center n)‖ := by ring_nf
      _ ≤ ‖u - z‖ + ‖z - center n‖ := norm_add_le _ _
      _ ≤ Real.pi / 2 := by linarith
  have hre : (u - center n).re = u.re - (n : ℝ) * Real.pi := by simp [center]
  have h4 : |u.re - (n : ℝ) * Real.pi| ≤ ‖u - center n‖ := by
    have := Complex.abs_re_le_norm (u - center n)
    rwa [hre] at this
  simp only [spectralStrip, Set.mem_setOf_eq]
  linarith

/-- Cauchy estimate: derivative of a bounded-by-π/48 function analytic on the strip. -/
theorem deriv_bound (n : ℤ) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (spectralStrip n))
    (hb : ∀ z ∈ spectralStrip n, ‖f z‖ ≤ Real.pi / 48)
    (z : ℂ) (hz : z ∈ Metric.closedBall (center n) (Real.pi/48)) :
    ‖deriv f z‖ ≤ 1 / 23 := by
  have hR : (0 : ℝ) < 23 * Real.pi / 48 := by positivity
  have hsub := closedBall_sub_strip n z hz (23 * Real.pi / 48) le_rfl
  have hd : DiffContOnCl ℂ f (Metric.ball z (23 * Real.pi / 48)) := by
    have : DifferentiableOn ℂ f (Metric.closedBall z (23 * Real.pi / 48)) :=
      fun u hu => (hf u (hsub hu)).differentiableAt.differentiableWithinAt
    exact this.diffContOnCl_ball (le_refl _)
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hd
    (C := Real.pi / 48) (fun u hu => hb u (hsub (Metric.sphere_subset_closedBall hu)))
  have e : Real.pi / 48 / (23 * Real.pi / 48) = 1 / 23 := by
    field_simp
  rwa [e] at this

theorem lipschitz_on (n : ℤ) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (spectralStrip n))
    (hb : ∀ z ∈ spectralStrip n, ‖f z‖ ≤ Real.pi / 48)
    (z ζ : ℂ) (hz : z ∈ Metric.closedBall (center n) (Real.pi/48))
    (hζ : ζ ∈ Metric.closedBall (center n) (Real.pi/48)) :
    ‖(center n + f z) - (center n + f ζ)‖ ≤ (1/23 : ℝ) * ‖z - ζ‖ := by
  have hs : Metric.closedBall (center n) (Real.pi/48) ⊆ spectralStrip n := by
    intro u hu
    exact closedBall_sub_strip n (center n) (Metric.mem_closedBall_self (by positivity)) (Real.pi/48)
      (by nlinarith [Real.pi_pos]) hu
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (C := (1/23 : ℝ))
    (s := Metric.closedBall (center n) (Real.pi/48))
    (fun u hu => (hf u (hs hu)).differentiableAt)
    (fun u hu => deriv_bound n f hf hb u hu) (convex_closedBall _ _) hζ hz
  have e : (center n + f z) - (center n + f ζ) = f z - f ζ := by ring
  rw [e]
  exact this

theorem exists_unique_fixed (n : ℤ) (f : ℂ → ℂ)
    (hmaps : Set.MapsTo (fun z => center n + f z)
      (Metric.closedBall (center n) (Real.pi/48)) (Metric.closedBall (center n) (Real.pi/48)))
    (hlip : ∀ z ∈ Metric.closedBall (center n) (Real.pi/48),
      ∀ ζ ∈ Metric.closedBall (center n) (Real.pi/48),
        ‖(center n + f z) - (center n + f ζ)‖ ≤ (1/23 : ℝ) * ‖z - ζ‖) :
    ∃! z, z ∈ Metric.closedBall (center n) (Real.pi/48) ∧ z = center n + f z := by
  set B : Set ℂ := Metric.closedBall (center n) (Real.pi/48) with hB
  haveI : Nonempty B := ⟨⟨center n, Metric.mem_closedBall_self (by positivity)⟩⟩
  haveI : CompleteSpace B := (Metric.isClosed_closedBall).completeSpace_coe
  let g : B → B := fun z => ⟨center n + f z, hmaps z.2⟩
  have hg : ContractingWith (1/23 : NNReal) g := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    · rw [show (1/23 : NNReal) = ((1:NNReal)/23) from rfl]
      exact_mod_cast (by norm_num : ((1:ℝ)/23) < 1)
    · have := hlip x x.2 y y.2
      simpa [g, dist_eq_norm, Subtype.dist_eq] using this
  obtain ⟨z0, hz0⟩ : ∃ z : B, g z = z := ⟨ContractingWith.fixedPoint g hg, hg.fixedPoint_isFixedPt⟩
  refine ⟨(z0 : ℂ), ⟨z0.2, ?_⟩, ?_⟩
  · have := congrArg Subtype.val hz0
    simpa [g] using this.symm
  · rintro y ⟨hy, hfy⟩
    have h1 := hlip y hy z0 z0.2
    have h2 : center n + f z0 = (z0 : ℂ) := by simpa [g] using congrArg Subtype.val hz0
    rw [← hfy, h2] at h1
    have h3 : ‖y - z0‖ ≤ (1/23 : ℝ) * ‖y - z0‖ := by
      have : (center n + f y) = y := hfy.symm
      simpa [this] using h1
    have h4 : ‖y - (z0 : ℂ)‖ = 0 := by
      have := norm_nonneg (y - (z0 : ℂ))
      linarith
    exact sub_eq_zero.1 (norm_eq_zero.1 h4)

end KST032S

theorem kst032 (w : ℤ → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hw : UnboundedWeight w) (φ : Potential)
    (hφ : φ ∈ physicalComponentBall w (2*M))
    (n : ℤ) (hn : diagonalThreshold w M ≤ n.natAbs) :
  Set.MapsTo (fun z => center n+a φ n z)
    (Metric.closedBall (center n) (Real.pi/48))
    (Metric.closedBall (center n) (Real.pi/48)) ∧
  (∀ z ∈ Metric.closedBall (center n) (Real.pi/48),
    ∀ ζ ∈ Metric.closedBall (center n) (Real.pi/48),
      ‖(center n+a φ n z)-(center n+a φ n ζ)‖ ≤ (1/23 : ℝ)*‖z-ζ‖) ∧
  diagonalZero n φ ∈ Metric.closedBall (center n) (Real.pi/48) ∧
  diagonalZero n φ = center n+a φ n (diagonalZero n φ) ∧
  (∀ z ∈ Metric.closedBall (center n) (Real.pi/48),
    z = center n+a φ n z → z = diagonalZero n φ) := by
  have hk := (kst031 w M hM hw).2.1
  obtain ⟨-, hall⟩ := hk
  obtain ⟨⟨ha, -, -, hbd⟩, -, -⟩ := hall φ hφ n hn
  have hb : ∀ z ∈ spectralStrip n, ‖a φ n z‖ ≤ Real.pi / 48 := fun z hz => (hbd z hz).1
  have hs : Metric.closedBall (center n) (Real.pi/48) ⊆ spectralStrip n := fun u hu =>
    KST032S.closedBall_sub_strip n (center n) (Metric.mem_closedBall_self (by positivity))
      (Real.pi/48) (by nlinarith [Real.pi_pos]) hu
  have hmaps : Set.MapsTo (fun z => center n + a φ n z)
      (Metric.closedBall (center n) (Real.pi/48)) (Metric.closedBall (center n) (Real.pi/48)) := by
    intro z hz
    have := hb z (hs hz)
    simpa [dist_eq_norm] using this
  have hlip := fun z hz ζ hζ => KST032S.lipschitz_on n (a φ n) ha hb z ζ hz hζ
  obtain ⟨z0, ⟨hz0, hfix⟩, huniq⟩ := KST032S.exists_unique_fixed n (a φ n) hmaps hlip
  have hex : ∃ z : ℂ, z ∈ Metric.closedBall (center n) (Real.pi/48) ∧
      z = center n + a φ n z := ⟨z0, hz0, hfix⟩
  have hspec := Classical.choose_spec hex
  have hdz : diagonalZero n φ = Classical.choose hex := by
    unfold diagonalZero
    rw [dif_pos hex]
  have heq : diagonalZero n φ = z0 := by
    rw [hdz]; exact huniq _ hspec
  refine ⟨hmaps, hlip, ?_, ?_, ?_⟩
  · rw [heq]; exact hz0
  · rw [heq]; exact hfix
  · intro z hz hzf
    rw [heq]; exact huniq z ⟨hz, hzf⟩

end NlsGge.ThirdConsultation.KST
end

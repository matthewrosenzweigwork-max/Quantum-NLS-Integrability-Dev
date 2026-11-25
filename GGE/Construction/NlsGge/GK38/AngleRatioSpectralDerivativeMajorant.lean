import NlsGge.GK38.AbelianRatioMajorant
import Mathlib.Analysis.Complex.Liouville

/-! Source-only actual square-summable SPECTRAL derivative majorant for the
arbitrary-input omitted ratio. This is the scalar-z Cauchy step in GK I.14.12;
it does not replace the contour/fundamental-solution proof of K4a gradients.
No uniform vanishing tails on a fixed open lp2 ball are asserted. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem angleInnerRatio_closed_ball_subset38 (m : ℤ) (z : ℂ)
    (hz : z ∈ ball ((m : ℂ)*(Real.pi : ℂ)) (Real.pi/8)) :
    closedBall z (Real.pi/16) ⊆ Lib.Dn m := by
  intro w hw
  have htri := dist_triangle w z ((m : ℂ)*(Real.pi : ℂ))
  have hw' : dist w z ≤ Real.pi/16 := mem_closedBall.mp hw
  have hz' : dist z ((m : ℂ)*(Real.pi : ℂ)) < Real.pi/8 := mem_ball.mp hz
  change dist w ((m : ℂ)*(Real.pi : ℂ)) < Real.pi/4
  linarith [Real.pi_pos]

/-- ONE complex potential/input neighborhood and square-mass bound precede
every varying tuple and signed far label. The actual scalar derivative exists
on a genuine neighborhood before Cauchy's derivative identity is invoked. -/
theorem angleOmittedRatio_spectral_derivative_l2_majorant38
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) (s₀ : Lib.L2Seq) :
    ∃ U : Set PotPair, U ∈ nhds φ₀ ∧ U ⊆ gkW ∧
      ∃ V : Set Lib.L2Seq, V ∈ nhds s₀ ∧ ∃ N : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        ∀ φ ∈ U, ∀ s ∈ V, ∃ b : ℤ → ℝ,
          (∀ m, 0 ≤ b m) ∧ Summable (fun m : ℤ => b m^2) ∧
          (∑' m : ℤ, b m^2) ≤ B ∧
          ∀ m : ℤ, (N : ℤ) < |m| →
            ∀ z ∈ ball ((m : ℂ)*(Real.pi : ℂ)) (Real.pi/8),
              DifferentiableAt ℂ (fun w => p2OmittedRatio38 m ((φ,s),w)) z ∧
              ‖deriv (fun w => p2OmittedRatio38 m ((φ,s),w)) z‖ ≤ b m := by
  obtain ⟨U,hU,hUW,V,hV,N,B,hB,hval⟩ := p2OmittedRatio_Dn_l2_majorant38 φ₀ hφ₀ s₀
  obtain ⟨Ud,hUd,_hUdW,Nd,hdom⟩ := a5TailDn_omitted_domain38 φ₀ hφ₀
  let k : ℝ := 16/Real.pi
  have hk : 0 ≤ k := by dsimp [k]; positivity
  refine ⟨U ∩ Ud,inter_mem hU hUd,fun φ hφ => hUW hφ.1,
    V,hV,max N Nd,k^2*B,mul_nonneg (sq_nonneg _) hB,?_⟩
  intro φ hφ s hs
  obtain ⟨a,ha0,has,haB,ha⟩ := hval φ hφ.1 s hs
  have hbs : Summable (fun m : ℤ => (k*a m)^2) := by
    simpa only [mul_pow] using has.mul_left (k^2)
  refine ⟨fun m => k*a m,fun m => mul_nonneg hk (ha0 m),hbs,?_,?_⟩
  · simp_rw [mul_pow]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left haB (sq_nonneg _)
  · intro m hm z hz
    have hmN : (N : ℤ) < |m| := by have h := le_max_left N Nd; omega
    have hmD : (Nd : ℤ) < |m| := by have h := le_max_right N Nd; omega
    have hsub := angleInnerRatio_closed_ball_subset38 m z hz
    let F : ℂ → ℂ := fun w => p2OmittedRatio38 m ((φ,s),w)-1
    have hA : AnalyticOnNhd ℂ F (closedBall z (Real.pi/16)) := by
      intro w hw
      have hratio := (p2OmittedRatio_analytic38 m ((φ,s),w)
        (hdom φ hφ.2 m hmD w (hsub hw))).comp
          (analyticAt_const.prod analyticAt_id)
      exact hratio.sub analyticAt_const
    have hDC : DiffContOnCl ℂ F (ball z (Real.pi/16)) :=
      (hA.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl
    have hC : ∀ w ∈ sphere z (Real.pi/16), ‖F w‖ ≤ a m :=
      fun w hw => ha m hmN w (hsub (sphere_subset_closedBall hw))
    have hdiff : DifferentiableAt ℂ (fun w => p2OmittedRatio38 m ((φ,s),w)) z := by
      have hratio := p2OmittedRatio_analytic38 m ((φ,s),z)
        (hdom φ hφ.2 m hmD z (hsub (mem_closedBall_self (by positivity))))
      exact (hratio.comp (analyticAt_const.prod analyticAt_id)).differentiableAt
    have hder := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (by positivity : (0 : ℝ)<Real.pi/16) hDC hC
    refine ⟨hdiff,?_⟩
    have hcoef : a m/(Real.pi/16)=k*a m := by
      dsimp only [k]
      field_simp [Real.pi_ne_zero]
    simpa only [F,deriv_sub_const,hcoef] using hder

end
end NlsGge.GK38

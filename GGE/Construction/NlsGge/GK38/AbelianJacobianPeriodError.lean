import NlsGge.GK38.AbelianJacobianFactorError
import NlsGge.GK38.AbelianStdRootAverage

/-! Actual complex diagonal period minus 2, on every original own cut.
UNCOMPILED source preparation. Complex cosine averaging is used, never a complex
singlepoint mean. Genuine circle and interval integrability precede identities. -/
set_option autoImplicit false
open Set Metric MeasureTheory
namespace NlsGge.GK38.P3JacobianColumns
noncomputable section

theorem diagonal_period_complex_average (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (s : Lib.L2Seq) (n m : ℤ) (hnm : n ≠ m)
    (hσ : Lib.sigmaOf s n ∈ closedBall (C n) (R n)) :
    IntervalIntegrable (fun θ : ℝ => p3DiagonalFactor38 n m φ s
      ((lamMinus φ m+lamPlus φ m)/2+
        ((lamPlus φ m-lamMinus φ m)/2)*(Real.cos θ : ℂ))) volume 0 (2*Real.pi) ∧
    (((n-m : ℤ) : ℂ))*abelianPeriod38 m φ (p3NumeratorColumn38 n m s) =
      ∫ θ in (0 : ℝ)..2*Real.pi, p3DiagonalFactor38 n m φ s
        ((lamMinus φ m+lamPlus φ m)/2+
          ((lamPlus φ m-lamMinus φ m)/2)*(Real.cos θ : ℂ)) := by
  let G : ℂ → ℂ := p3DiagonalFactor38 n m φ s
  let S : ℂ → ℂ := stdRoot38 ((lamMinus φ m+lamPlus φ m)/2)
    ((lamPlus φ m-lamMinus φ m)^2)
  have hr : 0 < R m := isolating_radius_pos38 hfam m
  have hcut : segment ℝ (lamMinus φ m) (lamPlus φ m) ⊆ ball (C m) (R m) := by
    obtain ⟨c,N,hg,hsp⟩ := hfam
    exact (hsp.1 m).1
  have hG : AnalyticOnNhd ℂ G (closedBall (C m) (R m)) :=
    diagonalFactor_analytic φ hφ C R hfam n m hnm s hσ
  have hd : ∀ z ∈ closedBall (C m) (R m), Lib.sigmaOf s n-z ≠ 0 := by
    obtain ⟨c,N,hg,hsp⟩ := hfam
    intro z hz
    exact (p2OwnSigma_denominator38 C R c N hg n m hnm s hσ z hz).1
  have hτ : tauN φ m = (lamMinus φ m+lamPlus φ m)/2 := by
    rw [tauN_value38 φ hφ m]
    ring
  have hγ := gamma2_value38 φ hφ m
  have hfamily := abelianPeriod_fullfamily_realization38 φ hφ (discC φ) C (discR φ) R
    (isolating_family38 φ hφ) hfam m (p3NumeratorColumn38 n m s)
    (column_entire n m s)
  have heq : EqOn
      (fun z => (((n-m : ℤ) : ℂ))*(p3NumeratorColumn38 n m s z/canonRoot38 φ z))
      (fun z => Complex.I*(G z/S z)) (sphere (C m) (R m)) := by
    intro z hz
    have he := weighted_column_diagonal_integrand n m hnm.symm s φ z
      ⟨hφ,fixed_sphere_subset φ C R hfam m hz⟩ (hd z (sphere_subset_closedBall hz))
    simpa only [hτ,hγ,mul_div_assoc] using he
  have hperiod : (((n-m : ℤ) : ℂ))*abelianPeriod38 m φ (p3NumeratorColumn38 n m s) =
      Complex.I*circleIntegral (fun z => G z/S z) (C m) (R m) := by
    unfold abelianPeriod38
    rw [hfamily.2.2,← circleIntegral.integral_const_mul,
      circleIntegral.integral_congr hr.le heq,circleIntegral.integral_const_mul]
  have havg := p2StdRoot_cosine_average38 (lamMinus φ m) (lamPlus φ m)
    (C m) (R m) hr hcut G hG
  refine ⟨havg.2.1,?_⟩
  rw [hperiod,havg.2.2]
  simp only [G,← mul_assoc,mul_neg,Complex.I_mul_I,neg_neg,one_mul]

theorem diagonal_period_sub_two_bound (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hgeom : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 φ C R)
    (s : Lib.L2Seq) (n m : ℤ) (hnm : n ≠ m)
    (hσ : Lib.sigmaOf s n ∈ closedBall (C n) (R n))
    (H b : ℝ) (hH : 0 ≤ H) (hb : 0 ≤ b)
    (hbound : ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      ‖p2OmittedRatio38 m ((φ,s),z)‖ ≤ H)
    (herror : ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      ‖p2OmittedRatio38 m ((φ,s),z)-1‖ ≤ b) :
    ‖(((n-m : ℤ) : ℂ))*abelianPeriod38 m φ (p3NumeratorColumn38 n m s)-2‖ ≤
      2*Real.pi*((c*H/Real.pi)*(p2RowEnvelope38 φ s m+p3InputRowEnvelope38 s m)+b/Real.pi) := by
  let x : ℝ → ℂ := fun θ => (lamMinus φ m+lamPlus φ m)/2+
    ((lamPlus φ m-lamMinus φ m)/2)*(Real.cos θ : ℂ)
  let A : ℝ := (c*H/Real.pi)*(p2RowEnvelope38 φ s m+p3InputRowEnvelope38 s m)+b/Real.pi
  have havg := diagonal_period_complex_average φ hφ C R hfam s n m hnm hσ
  have hi : IntervalIntegrable (fun θ : ℝ => p3DiagonalFactor38 n m φ s (x θ))
      volume 0 (2*Real.pi) := havg.1
  have hic : IntervalIntegrable (fun _θ : ℝ => 1/(Real.pi : ℂ))
      volume 0 (2*Real.pi) := intervalIntegrable_const
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hconstant : (∫ _θ in (0 : ℝ)..2*Real.pi, 1/(Real.pi : ℂ)) = 2 := by
    rw [intervalIntegral.integral_const,sub_zero,Complex.real_smul]
    push_cast
    field_simp [hpi]
  have hsubtract :
      (((n-m : ℤ) : ℂ))*abelianPeriod38 m φ (p3NumeratorColumn38 n m s)-2 =
        ∫ θ in (0 : ℝ)..2*Real.pi,
          (p3DiagonalFactor38 n m φ s (x θ)-1/(Real.pi : ℂ)) := by
    rw [intervalIntegral.integral_sub hi hic,hconstant]
    exact congrArg (fun w : ℂ => w-2) havg.2
  rw [hsubtract]
  have hpoint : ∀ θ : ℝ, ‖p3DiagonalFactor38 n m φ s (x θ)-1/(Real.pi : ℂ)‖ ≤ A := by
    intro θ
    have hx : x θ ∈ segment ℝ (lamMinus φ m) (lamPlus φ m) :=
      p2Cosine_mem_segment38 (lamMinus φ m) (lamPlus φ m) θ
    exact diagonalFactor_error φ hφ C R c N hgeom hfam s n m hnm hσ (x θ) hx
      H b hH hb (hbound _ hx) (herror _ hx)
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 2*Real.pi)
    (f := fun θ => p3DiagonalFactor38 n m φ s (x θ)-1/(Real.pi : ℂ))
    (fun θ _ => hpoint θ)
  simpa only [sub_zero,abs_of_pos (by positivity : 0 < 2*Real.pi),mul_comm A] using hn

end
end NlsGge.GK38.P3JacobianColumns

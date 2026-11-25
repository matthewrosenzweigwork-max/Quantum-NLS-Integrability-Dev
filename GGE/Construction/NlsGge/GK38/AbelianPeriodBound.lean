import NlsGge.GK38.AbelianRatioCutBound
import NlsGge.GK38.AbelianCutEnvelope
import NlsGge.GK38.AbelianStdRootAverage

/-! Actual canonical-period estimate from an earned own-disc denominator and cut ratio.
These are explicit intermediate geometric premises, not an assumed P2 bound. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem p2Period_bound_of_denominator38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (s : Lib.L2Seq) (n m : ℤ) (B H : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hden : ∀ z ∈ closedBall (C m) (R m), Lib.sigmaOf s n-z ≠ 0)
    (hratio : ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      ‖(((n-m:ℤ):ℂ))/(Lib.sigmaOf s n-z)‖ ≤ B)
    (hHcut : ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      ‖p2OmittedRatio38 m ((φ,s),z)‖ ≤ H) :
    ‖(((n-m:ℤ):ℂ))*abelianPeriod38 m φ (p2FullNumerator38 n s)‖ ≤
      2*Real.pi*(B*H)*p2RowEnvelope38 φ s m := by
  let G : ℂ → ℂ := fun z => Complex.I*(((n-m:ℤ):ℂ))*(Lib.sigmaOf s m-z)*
    p2OmittedRatio38 m ((φ,s),z)/(Lib.sigmaOf s n-z)
  have hG : AnalyticOnNhd ℂ G (closedBall (C m) (R m)) := by
    apply AnalyticOnNhd.div
    · exact ((analyticOnNhd_const.mul (analyticOnNhd_const.sub analyticOnNhd_id)).mul
        (p2OmittedRatio_own_disc_analytic38 m φ hφ C R hfam s))
    · exact analyticOnNhd_const.sub analyticOnNhd_id
    · exact hden
  have hcut : segment ℝ (lamMinus φ m) (lamPlus φ m) ⊆ ball (C m) (R m) := by
    obtain ⟨c,N,hg,hs⟩ := hfam
    exact (hs.1 m).1
  have hE := p2RowEnvelope_nonneg38 φ s m
  have hGB : ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      ‖G z‖ ≤ (B*H)*p2RowEnvelope38 φ s m := by
    intro z hz
    have he : ‖G z‖ =
        (‖(((n-m:ℤ):ℂ))/(Lib.sigmaOf s n-z)‖*‖Lib.sigmaOf s m-z‖)*
          ‖p2OmittedRatio38 m ((φ,s),z)‖ := by
      dsimp [G]
      simp only [norm_div,norm_mul,Complex.norm_I,one_mul]
      ring
    rw [he]
    calc
      _ ≤ (B*p2RowEnvelope38 φ s m)*H :=
        mul_le_mul (mul_le_mul (hratio z hz) (p2Sigma_cut_envelope38 φ hφ s m z hz)
          (norm_nonneg _) hB) (hHcut z hz) (norm_nonneg _) (mul_nonneg hB hE)
      _ = (B*H)*p2RowEnvelope38 φ s m := by ring
  have hr := isolating_radius_pos38 hfam m
  have hτ : tauN φ m=(lamMinus φ m+lamPlus φ m)/2 := by
    rw [tauN_value38 φ hφ m]
    ring
  have hγ := gamma2_value38 φ hφ m
  have hbound := p2StdRoot_integral_norm_bound38 (lamMinus φ m) (lamPlus φ m)
    (C m) (R m) ((B*H)*p2RowEnvelope38 φ s m) hr hcut G hG
    (mul_nonneg (mul_nonneg hB hH) hE) hGB
  have hfamily := abelianPeriod_fullfamily_realization38 φ hφ (discC φ) C (discR φ) R
    (isolating_family38 φ hφ) hfam m (p2FullNumerator38 n s)
    (p2FullNumerator_entire38 n s)
  have hEq : EqOn
      (fun z => (((n-m:ℤ):ℂ))*(p2FullNumerator38 n s z/canonRoot38 φ z))
      (fun z => G z/stdRoot38 ((lamMinus φ m+lamPlus φ m)/2)
        ((lamPlus φ m-lamMinus φ m)^2) z) (sphere (C m) (R m)) := by
    intro z hz
    change (((n-m:ℤ):ℂ))*(p2FullNumerator38 n s z/canonRoot38 φ z)=_
    rw [p2FullNumerator_div_root38 n m s φ z
      ⟨hφ,fixed_sphere_subset φ C R hfam m hz⟩ (hden z (sphere_subset_closedBall hz)),hτ,hγ]
    dsimp [G]
    ring
  have hperiod : (((n-m:ℤ):ℂ))*abelianPeriod38 m φ (p2FullNumerator38 n s) =
      circleIntegral (fun z => G z/stdRoot38 ((lamMinus φ m+lamPlus φ m)/2)
        ((lamPlus φ m-lamMinus φ m)^2) z) (C m) (R m) := by
    unfold abelianPeriod38
    rw [hfamily.2.2,← circleIntegral.integral_const_mul]
    exact circleIntegral.integral_congr hr.le hEq
  rw [hperiod]
  simpa only [mul_assoc] using hbound.2

#print axioms p2Period_bound_of_denominator38
end
end NlsGge.GK38

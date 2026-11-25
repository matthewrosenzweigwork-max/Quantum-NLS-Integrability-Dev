import NlsGge.GK38.AngleCutTaylor

/-! Actual zero-period centering plus earned weighted cosine Taylor control
and a positive weighted mean yields a quadratic gap bound. No division by a
possibly zero gap occurs; the estimate includes collapsed gaps. -/
set_option autoImplicit false
open Set Metric MeasureTheory
namespace NlsGge.GK38
noncomputable section

theorem angleActual_weighted_zero_period_centering38
    (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (n m : ℤ) (hnm : n ≠ m) (s : Lib.L2Seq)
    (hσ : Lib.sigmaOf s n ∈ closedBall (C n) (R n))
    (hzero : abelianPeriod38 m φ (p2FullNumerator38 n s)=0) :
    let x : ℝ → ℂ := fun θ => (lamMinus φ m+lamPlus φ m)/2+
      ((lamPlus φ m-lamMinus φ m)/2)*(Real.cos θ : ℂ)
    let F : ℝ → ℂ := fun θ => (((n-m : ℤ) : ℂ))*angleRegularFactor38 n m ((φ,s),x θ)
    IntervalIntegrable F volume 0 (2*Real.pi) ∧
    IntervalIntegrable (fun θ : ℝ => (Real.cos θ : ℂ)*F θ) volume 0 (2*Real.pi) ∧
    (Lib.sigmaOf s m-tauN φ m)*(∫ θ : ℝ in (0 : ℝ)..2*Real.pi,F θ)=
      ((lamPlus φ m-lamMinus φ m)/2)*
        (∫ θ : ℝ in (0 : ℝ)..2*Real.pi,(Real.cos θ : ℂ)*F θ) := by
  let x : ℝ → ℂ := fun θ => (lamMinus φ m+lamPlus φ m)/2+
    ((lamPlus φ m-lamMinus φ m)/2)*(Real.cos θ : ℂ)
  let Z : ℝ → ℂ := fun θ => angleRegularFactor38 n m ((φ,s),x θ)
  let w : ℂ := (((n-m : ℤ) : ℂ))
  have h := angleActual_zero_period_centering38 φ hφ C R hfam n m hnm s hσ hzero
  have hi0 : IntervalIntegrable (fun θ => w*Z θ) volume 0 (2*Real.pi) := h.1.const_mul w
  have he : (fun θ : ℝ => (Real.cos θ : ℂ)*(w*Z θ))=
      (fun θ : ℝ => w*((Real.cos θ : ℂ)*Z θ)) := by funext θ; ring
  have hi1 : IntervalIntegrable (fun θ : ℝ => (Real.cos θ : ℂ)*(w*Z θ))
      volume 0 (2*Real.pi) := by rw [he]; exact h.2.1.const_mul w
  refine ⟨hi0,hi1,?_⟩
  change (Lib.sigmaOf s m-tauN φ m)*(∫ θ : ℝ in (0 : ℝ)..2*Real.pi,w*Z θ)=
    ((lamPlus φ m-lamMinus φ m)/2)*
      (∫ θ : ℝ in (0 : ℝ)..2*Real.pi,(Real.cos θ : ℂ)*(w*Z θ))
  rw [he,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have hh := congrArg (fun q : ℂ => w*q) h.2.2
  simpa only [mul_assoc,mul_left_comm] using hh

theorem angleActual_weighted_quadratic_bound38
    (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (n m : ℤ) (hnm : n ≠ m) (s : Lib.L2Seq)
    (hσ : Lib.sigmaOf s n ∈ closedBall (C n) (R n))
    (hzero : abelianPeriod38 m φ (p2FullNumerator38 n s)=0)
    (b D : ℝ) (hb : 0 ≤ b) (hD : 0 < D)
    (hder : ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      DifferentiableAt ℂ (fun w => angleRegularFactor38 n m ((φ,s),w)) z ∧
      ‖(((n-m : ℤ) : ℂ))*deriv (fun w => angleRegularFactor38 n m ((φ,s),w)) z‖ ≤ b)
    (hmean : D ≤ ‖∫ θ : ℝ in (0 : ℝ)..2*Real.pi,
      (((n-m : ℤ) : ℂ))*angleRegularFactor38 n m ((φ,s),
        (lamMinus φ m+lamPlus φ m)/2+
          ((lamPlus φ m-lamMinus φ m)/2)*(Real.cos θ : ℂ))‖) :
    ‖Lib.sigmaOf s m-tauN φ m‖ ≤ ((Real.pi/(2*D))*b)*‖gamma2 φ m‖ := by
  let d : ℂ := (lamPlus φ m-lamMinus φ m)/2
  let x : ℝ → ℂ := fun θ => (lamMinus φ m+lamPlus φ m)/2+d*(Real.cos θ : ℂ)
  let F : ℝ → ℂ := fun θ => (((n-m : ℤ) : ℂ))*angleRegularFactor38 n m ((φ,s),x θ)
  let J₀ : ℂ := ∫ θ : ℝ in (0 : ℝ)..2*Real.pi,F θ
  let J₁ : ℂ := ∫ θ : ℝ in (0 : ℝ)..2*Real.pi,(Real.cos θ : ℂ)*F θ
  have hcenter := (angleActual_weighted_zero_period_centering38
    φ hφ C R hfam n m hnm s hσ hzero).2.2
  have hmoment := (angleWeighted_actual_cosine_moment_bound38
    φ hφ C R hfam n m hnm s hσ b hb hder).2
  have hnorm : ‖Lib.sigmaOf s m-tauN φ m‖*‖J₀‖=‖d‖*‖J₁‖ := by
    simpa only [norm_mul] using congrArg norm hcenter
  have hmul : ‖Lib.sigmaOf s m-tauN φ m‖*D ≤ ((2*Real.pi)*b)*‖d‖^2 := by
    calc
      _ ≤ ‖Lib.sigmaOf s m-tauN φ m‖*‖J₀‖ :=
        mul_le_mul_of_nonneg_left hmean (norm_nonneg _)
      _ = ‖d‖*‖J₁‖ := hnorm
      _ ≤ ‖d‖*((2*Real.pi)*b*‖d‖) := mul_le_mul_of_nonneg_left hmoment (norm_nonneg _)
      _ = _ := by ring
  have hd2 : ‖d‖^2=‖gamma2 φ m‖/4 := by
    rw [gamma2_value38 φ hφ m]
    dsimp only [d]
    rw [norm_div,norm_pow]
    norm_num
    ring
  have hdiv := (le_div_iff₀ hD).mpr hmul
  calc
    _ ≤ (((2*Real.pi)*b)*‖d‖^2)/D := hdiv
    _ = ((Real.pi/(2*D))*b)*‖gamma2 φ m‖ := by rw [hd2]; ring

end
end NlsGge.GK38

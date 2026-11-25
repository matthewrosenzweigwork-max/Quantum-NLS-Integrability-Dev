import NlsGge.GK38.AbelianFullNumeratorColumns
import NlsGge.GK38.AbelianPeriodBound

/-! Actual full-Jacobian scalar columns. The off-diagonal estimate is obtained
from the already proved actual P2 period estimate, after earning integrability.
No Hilbert-valued full period map or Jacobian is assumed in this leaf. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38.P6FullJacobian
noncomputable section

def fullColumn (r : ℤ) (s : Lib.L2Seq) (z : ℂ) : ℂ :=
  (-2/(Real.pi : ℂ))*Lib.omitProd r s z

theorem fullColumn_eq_omittedNumerator (r : ℤ) (s : Lib.L2Seq) (z : ℂ) :
    fullColumn r s z=(1/(Real.pi : ℂ))*p2FullNumerator38 r s z := by
  unfold fullColumn p2FullNumerator38
  ring

theorem fullColumn_entire (r : ℤ) (s : Lib.L2Seq) :
    AnalyticOnNhd ℂ (fullColumn r s) univ := by
  have he : fullColumn r s=
      (fun z => (1/(Real.pi : ℂ))*p2FullNumerator38 r s z) :=
    funext (fullColumn_eq_omittedNumerator r s)
  rw [he]
  exact analyticOnNhd_const.mul (p2FullNumerator_entire38 r s)

theorem fullColumn_circleIntegrable (m r : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (s : Lib.L2Seq) :
    CircleIntegrable (fun z => fullColumn r s z/canonRoot38 φ z)
      (discC φ m) (discR φ m) :=
  (abelianPeriod_fullfamily_realization38 φ hφ (discC φ) (discC φ)
    (discR φ) (discR φ) (isolating_family38 φ hφ) (isolating_family38 φ hφ)
    m (fullColumn r s) (fullColumn_entire r s)).1

theorem fullColumn_period (m r : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (s : Lib.L2Seq) :
    abelianPeriod38 m φ (fullColumn r s)=
      (1/(Real.pi : ℂ))*abelianPeriod38 m φ (p2FullNumerator38 r s) := by
  have _hc := fullColumn_circleIntegrable m r φ hφ s
  have _ho := p2Period_integrable38 m r φ hφ s
  have he : (fun z => fullColumn r s z/canonRoot38 φ z)=
      (fun z => (1/(Real.pi : ℂ))*(p2FullNumerator38 r s z/canonRoot38 φ z)) := by
    funext z
    rw [fullColumn_eq_omittedNumerator]
    ring
  unfold abelianPeriod38
  rw [he,circleIntegral.integral_const_mul]

theorem fullColumn_offDiagonal_period_bound (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hfam : IsolatingFamily38 φ C R)
    (s : Lib.L2Seq) (m r : ℤ) (hrm : r ≠ m)
    (hσr : Lib.sigmaOf s r ∈ closedBall (C r) (R r))
    (H : ℝ) (hH : 0 ≤ H)
    (hbound : ∀ z ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      ‖p2OmittedRatio38 m ((φ,s),z)‖ ≤ H) :
    ‖abelianPeriod38 m φ (fullColumn r s)‖ ≤
      (2*c*H)*p2RowEnvelope38 φ s m*Lib.c3w m r := by
  have hc : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1).trans hg.2.2.1
  have hden : ∀ z ∈ closedBall (C m) (R m), Lib.sigmaOf s r-z ≠ 0 :=
    fun z hz => (p2OwnSigma_denominator38 C R c N hg r m hrm s hσr z hz).1
  have hcut : segment ℝ (lamMinus φ m) (lamPlus φ m) ⊆ ball (C m) (R m) := by
    obtain ⟨d,M,hg',hsp⟩ := hfam
    exact (hsp.1 m).1
  have hp := p2Period_bound_of_denominator38 φ hφ C R hfam s r m c H hc hH hden
    (fun z hz => (p2OwnSigma_denominator38 C R c N hg r m hrm s hσr z
      (ball_subset_closedBall (hcut hz))).2) hbound
  have hi : (((r-m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hrm
  have hw : ‖(((r-m : ℤ) : ℂ))‖⁻¹=Lib.c3w m r := by
    rw [Complex.norm_intCast]
    simp only [Int.cast_sub,Lib.c3w,one_div]
  have he : abelianPeriod38 m φ (fullColumn r s)=
      (1/(Real.pi : ℂ))*
        (((((r-m : ℤ) : ℂ))*abelianPeriod38 m φ (p2FullNumerator38 r s))/
          (((r-m : ℤ) : ℂ))) := by
    rw [fullColumn_period m r φ hφ s]
    field_simp [hi]
  rw [he,norm_mul,norm_div,norm_div,norm_one,Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le,
    div_eq_mul_inv _ ‖(((r-m : ℤ) : ℂ))‖,hw]
  calc
    _ ≤ (1/Real.pi)*((2*Real.pi*(c*H)*p2RowEnvelope38 φ s m)*Lib.c3w m r) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hp (Lib.c3w_nonneg m r)) (by positivity)
    _ = _ := by field_simp [Real.pi_ne_zero]

end
end NlsGge.GK38.P6FullJacobian

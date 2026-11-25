import Armstrong.Work.QuadraticCircleODE
import NlsGge.GK38.XiSqLocal
import NlsGge.GK38.AbelianPsiNumerator

/-! Prospective same-supplied-numerator coefficient realization.

The actual omitted product is analytic and nonzero on the original filled
closed ball.  The actual canonical/standard-root factorization is used only
on its boundary circle.  Ordinary Cauchy formulas extend the squared identity
to the filled open ball before it is differentiated.  Thus the total standard
root is never incorrectly squared on its removed segment.

Root owns compilation, import-path assignment, and integration.  No new
numerator family, extra source hypothesis, or frozen-source weakening occurs.
-/

set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped Topology

namespace NlsGge.GK38
noncomputable section

private theorem rawBetaAnalyticEqOnBallOfCircle38
    (c : ℂ) (r : ℝ) (hr : 0 < r) (f g : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall c r))
    (hg : AnalyticOnNhd ℂ g (closedBall c r))
    (he : EqOn f g (sphere c r)) : EqOn f g (ball c r) := by
  intro z hz
  have hC : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hi : circleIntegral (fun w => (w-z)⁻¹ • f w) c r =
      circleIntegral (fun w => (w-z)⁻¹ • g w) c r := by
    apply circleIntegral.integral_congr hr.le
    intro w hw
    change (w-z)⁻¹ • f w = (w-z)⁻¹ • g w
    rw [he hw]
  rw [hf.differentiableOn.circleIntegral_sub_inv_smul hz,
    hg.differentiableOn.circleIntegral_sub_inv_smul hz] at hi
  exact mul_left_cancel₀ hC (by simpa only [smul_eq_mul] using hi)

/-- The same supplied entire numerator and its actual zero Abelian period
produce an analytic coefficient on the original filled ball.  In particular,
the conclusion applies at every point of the original slit required by the
literal rooted-path primitive assembly. -/
theorem rawBetaPsiCoefficientOfZeroPeriod38
    (n m : ℤ) (F : PotPair → P2Space38 n) (φ : PotPair) (hφ : φ ∈ gkW)
    (hperiod : abelianPeriod38 m φ (p6PsiNumerator38 n F φ) = 0) :
    ∃ R : ℂ → ℂ,
      AnalyticOnNhd ℂ R (ball (discC φ m) (discR φ m)) ∧
      ∀ z ∈ ball (discC φ m) (discR φ m),
        perChar φ z * deriv R z + (deriv (perChar φ) z / 2) * R z =
          p6PsiNumerator38 n F φ z := by
  let a : ℂ := lamMinus φ m
  let b : ℂ := lamPlus φ m
  let τ : ℂ := (a+b)/2
  let C : ℤ → ℂ := discC φ
  let ρ : ℤ → ℝ := discR φ
  let Ψ : ℂ → ℂ := p6PsiNumerator38 n F φ
  let D : ℂ → ℂ := fun z => a5OmittedRootProduct38 m (φ,z)
  let K : ℂ := (2 * Complex.I) / (Lib.piN m : ℂ)
  let S : ℂ → ℂ := stdRoot38 τ ((b-a)^2)
  let f : ℂ → ℂ := fun z => Ψ z / (K * D z)
  let H : ℂ → ℂ := fun z => K^2 * ((z-a)*(z-b)) * D z^2
  have hfam : IsolatingFamily38 φ C ρ := isolating_family38 φ hφ
  have hρ : 0 < ρ m := isolating_radius_pos38 hfam m
  have hcut : segment ℝ a b ⊆ ball (C m) (ρ m) := by
    obtain ⟨c,N,hgeom,hspec⟩ := hfam
    exact (hspec.1 m).1
  have hK : K ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero m))
  have hdom : ∀ z ∈ closedBall (C m) (ρ m),
      (φ,z) ∈ a5OmittedRootDomain38 m :=
    fun z hz => a5OwnClosedBall_omittedDomain38 φ hφ C ρ hfam m z hz
  have hD : AnalyticOnNhd ℂ D (closedBall (C m) (ρ m)) := by
    intro z hz
    exact (a5OmittedRoot_analytic38 m (φ,z) (hdom z hz)).comp
      (analyticAt_const.prod analyticAt_id)
  have hDn : ∀ z ∈ closedBall (C m) (ρ m), D z ≠ 0 :=
    fun z hz => a5OmittedRoot_ne_zero38 m (φ,z) (hdom z hz)
  have hΨ : AnalyticOnNhd ℂ Ψ (closedBall (C m) (ρ m)) :=
    (p6PsiNumerator_entire38 n F φ).mono (subset_univ _)
  have hf : AnalyticOnNhd ℂ f (closedBall (C m) (ρ m)) :=
    hΨ.div (analyticOnNhd_const.mul hD) (fun z hz => mul_ne_zero hK (hDn z hz))
  have hH : AnalyticOnNhd ℂ H (closedBall (C m) (ρ m)) := by
    intro z hz
    exact (analyticAt_const.mul
      ((analyticAt_id.sub analyticAt_const).mul
        (analyticAt_id.sub analyticAt_const))).mul ((hD z hz).pow 2)
  have hτ : tauN φ m = τ := by
    rw [tauN_value38 φ hφ m]
    dsimp [τ, a, b]
    ring
  have hgap : gamma2 φ m = (b-a)^2 := gamma2_value38 φ hφ m
  have hactual : ∀ z ∈ sphere (C m) (ρ m),
      canonRoot38 φ z = K * S z * D z := by
    intro z hz
    have hp : (φ,z) ∈ rootDomain38 :=
      ⟨hφ, fixed_sphere_subset φ C ρ hfam m hz⟩
    have he := a5CanonRoot_omitted_factorization38 m (φ,z) hp
    rw [rootFactor38, hτ, hgap] at he
    calc
      canonRoot38 φ z = 2 * Complex.I * (S z / (Lib.piN m : ℂ)) * D z := he
      _ = K * S z * D z := by dsimp [K]; ring
  have hSn : ∀ z ∈ sphere (C m) (ρ m), S z ≠ 0 := by
    intro z hz
    apply stdRoot_ne_zero38 a b z
    intro hseg
    exact (not_lt.mpr (mem_sphere.mp hz).ge) (mem_ball.mp (hcut hseg))
  have hEqPeriod : EqOn (fun z => Ψ z / canonRoot38 φ z)
      (fun z => f z / S z) (sphere (C m) (ρ m)) := by
    intro z hz
    change Ψ z / canonRoot38 φ z = f z / S z
    rw [hactual z hz]
    dsimp [f]
    field_simp [hK, hDn z (sphere_subset_closedBall hz), hSn z hz] <;> ring
  have hstd : circleIntegral (fun z => f z / S z) (C m) (ρ m) = 0 := by
    have he := circleIntegral.integral_congr hρ.le hEqPeriod
    change circleIntegral (fun z => Ψ z / canonRoot38 φ z) (C m) (ρ m) = 0
      at hperiod
    exact he.symm.trans hperiod
  obtain ⟨T, hT, hTode⟩ := rawBetaQuadraticODEOfZeroStdRootPeriod38
    a b (C m) (ρ m) hρ hcut f hf hstd
  have hPHcircle : EqOn (perChar φ) H (sphere (C m) (ρ m)) := by
    intro z hz
    have hp : (φ,z) ∈ rootDomain38 :=
      ⟨hφ, fixed_sphere_subset φ C ρ hfam m hz⟩
    have hSq : S z^2 = (z-a)*(z-b) := by
      change stdRoot38 ((a+b)/2) ((b-a)^2) z ^ 2 = _
      rw [stdRoot_sq38 a b z (rootDomain_avoids38 hp m)]
      ring
    calc
      perChar φ z = canonRoot38 φ z^2 := (canonRoot_sq38 φ hφ z hp.2).symm
      _ = (K * S z * D z)^2 := by rw [hactual z hz]
      _ = H z := by
        dsimp [H]
        rw [mul_pow, mul_pow, hSq]
  have hPH : EqOn (perChar φ) H (ball (C m) (ρ m)) :=
    rawBetaAnalyticEqOnBallOfCircle38 (C m) (ρ m) hρ (perChar φ) H
      ((analyticOnNhd_perChar_z φ).mono (subset_univ _)) hH hPHcircle
  let R : ℂ → ℂ := fun z => T z / (K * D z)
  have hR : AnalyticOnNhd ℂ R (ball (C m) (ρ m)) :=
    hT.div (analyticOnNhd_const.mul (hD.mono ball_subset_closedBall))
      (fun z hz => mul_ne_zero hK (hDn z (ball_subset_closedBall hz)))
  refine ⟨R, hR, ?_⟩
  intro z hz
  have hzcl : z ∈ closedBall (C m) (ρ m) := ball_subset_closedBall hz
  have hDd : HasDerivAt D (deriv D z) z := (hD z hzcl).differentiableAt.hasDerivAt
  have hTd : HasDerivAt T (deriv T z) z := (hT z hz).differentiableAt.hasDerivAt
  have hDsq : HasDerivAt (fun w => D w^2) (2*D z*deriv D z) z := by
    simpa using! hDd.pow 2
  have hq : HasDerivAt (fun w : ℂ => (w-a)*(w-b)) (2*(z-τ)) z := by
    apply (((hasDerivAt_id z).sub_const a).mul
      ((hasDerivAt_id z).sub_const b)).congr_deriv
    dsimp [τ]
    ring
  have hHd : HasDerivAt H
      (2*K^2*((z-τ)*D z^2 + ((z-a)*(z-b))*D z*deriv D z)) z := by
    apply ((hq.const_mul (K^2)).mul hDsq).congr_deriv
    ring
  have hPE : perChar φ =ᶠ[nhds z] H := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact hPH hw
  have hPd : HasDerivAt (perChar φ)
      (2*K^2*((z-τ)*D z^2 + ((z-a)*(z-b))*D z*deriv D z)) z :=
    hHd.congr_of_eventuallyEq hPE
  have hRd : HasDerivAt R
      ((deriv T z * (K*D z) - T z * (K*deriv D z)) / (K*D z)^2) z :=
    hTd.div (hDd.const_mul K) (mul_ne_zero hK (hDn z hzcl))
  rw [hPH hz, hPd.deriv, hRd.deriv]
  change (K^2*((z-a)*(z-b))*D z^2) *
      ((deriv T z*(K*D z) - T z*(K*deriv D z))/(K*D z)^2) +
    ((2*K^2*((z-τ)*D z^2 + ((z-a)*(z-b))*D z*deriv D z))/2) *
      (T z/(K*D z)) = Ψ z
  calc
    _ = K*D z * (((z-a)*(z-b))*deriv T z + (z-τ)*T z) := by
      field_simp [hK, hDn z hzcl] <;> ring
    _ = K*D z * f z := by rw [hTode z hz]
    _ = Ψ z := by
      dsimp [f]
      field_simp [hK, hDn z hzcl] <;> ring

#check @NlsGge.GK38.rawBetaPsiCoefficientOfZeroPeriod38
#print axioms rawBetaPsiCoefficientOfZeroPeriod38

end
end NlsGge.GK38

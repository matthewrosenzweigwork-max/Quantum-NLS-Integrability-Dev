import Armstrong.Work.QuadraticCircleODE
import NlsGge.GK38.XiSqLocal
import NlsGge.GK38.AbelianPsiNumerator

/-! Explicit fixed-circle same-numerator coefficients for the reviewed
ALT15.2 route. This module uses the additive literal-witness extraction in
QuadraticCircleODE. It changes no frozen source statement and selects no
new numerator family. Root owns every compiler and integration operation. -/

set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped Topology

namespace NlsGge.GK38
noncomputable section

/-- Literal primitive of the SAME numerator over the actual canonical root.
All analytic uses below establish genuine circle integrability first. -/
def rawBetaFixedBoundaryPrimitive38 (n m : ℤ)
    (F : PotPair → P2Space38 n) (φ : PotPair) (c : ℂ) (r θ : ℝ) : ℂ :=
  ∫ t in (0:ℝ)..θ,
    deriv (circleMap c r) t *
      (p6PsiNumerator38 n F φ (circleMap c r t) /
        canonRoot38 φ (circleMap c r t))

/-- Literal nested Cauchy coefficient. S is the existing standard branch
in symmetric tau/gamma² data; K retains the actual piN zero-mode convention.
This total formula has no analyticity assertion outside the certified use. -/
def rawBetaFixedCoefficient38 (n m : ℤ)
    (F : PotPair → P2Space38 n) (φ : PotPair) (c : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  rawBetaBoundaryCauchy38
    (fun θ => rawBetaFixedBoundaryPrimitive38 n m F φ c r θ /
      stdRoot38 (tauN φ m) (gamma2 φ m) (circleMap c r θ)) c r z /
    (((2 * Complex.I) / (Lib.piN m : ℂ)) *
      a5OmittedRootProduct38 m (φ,z))

/-- Actual original selectors are certified pointwise from the inherited
W-to-gkW inclusion. The original choice is never differentiated. -/
theorem rawBetaOriginalFamilyCertificate38
    (W : Set PotPair) (hW : W ⊆ gkW) (φ : PotPair) (hφ : φ ∈ W) :
    IsolatingFamily38 φ (discC φ) (discR φ) :=
  isolating_family38 φ (hW hφ)

/-- The genuine original normalized period transfers only after BOTH
complete family certificates are supplied. Both integrabilities are returned. -/
theorem rawBetaFixedFamilyZeroPeriod38
    (n m : ℤ) (F : PotPair → P2Space38 n) (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (ρ : ℤ → ℝ) (hfam : IsolatingFamily38 φ C ρ)
    (hperiod : abelianPeriod38 m φ (p6PsiNumerator38 n F φ) = 0) :
    CircleIntegrable (fun z => p6PsiNumerator38 n F φ z / canonRoot38 φ z)
      (discC φ m) (discR φ m) ∧
    CircleIntegrable (fun z => p6PsiNumerator38 n F φ z / canonRoot38 φ z)
      (C m) (ρ m) ∧
    circleIntegral (fun z => p6PsiNumerator38 n F φ z / canonRoot38 φ z)
      (C m) (ρ m) = 0 := by
  have horiginal : IsolatingFamily38 φ (discC φ) (discR φ) :=
    rawBetaOriginalFamilyCertificate38 gkW (fun _ h => h) φ hφ
  obtain ⟨hI0,hI1,he⟩ := abelianPeriod_fullfamily_realization38 φ hφ
    (discC φ) C (discR φ) ρ horiginal hfam m (p6PsiNumerator38 n F φ)
    (p6PsiNumerator_entire38 n F φ)
  refine ⟨hI0,hI1,?_⟩
  exact he.symm.trans hperiod

/-- The linear branch identity, including its actual sign and K, is earned
from the existing canonical omitted-product factorization, not its square. -/
theorem rawBetaFixedBoundaryRoot38
    (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (ρ : ℤ → ℝ) (hfam : IsolatingFamily38 φ C ρ) (m : ℤ) :
    let K : ℂ := (2 * Complex.I) / (Lib.piN m : ℂ)
    let D : ℂ → ℂ := fun z => a5OmittedRootProduct38 m (φ,z)
    let S : ℂ → ℂ := stdRoot38 (tauN φ m) (gamma2 φ m)
    K ≠ 0 ∧
      (∀ z ∈ closedBall (C m) (ρ m), D z ≠ 0) ∧
      ∀ z ∈ sphere (C m) (ρ m),
        S z ≠ 0 ∧ canonRoot38 φ z = K * S z * D z := by
  let K : ℂ := (2 * Complex.I) / (Lib.piN m : ℂ)
  let D : ℂ → ℂ := fun z => a5OmittedRootProduct38 m (φ,z)
  let S : ℂ → ℂ := stdRoot38 (tauN φ m) (gamma2 φ m)
  have hK : K ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero m))
  have hDn : ∀ z ∈ closedBall (C m) (ρ m), D z ≠ 0 :=
    fun z hz => a5OmittedRoot_ne_zero38 m (φ,z)
      (a5OwnClosedBall_omittedDomain38 φ hφ C ρ hfam m z hz)
  have hcut : segment ℝ (lamMinus φ m) (lamPlus φ m) ⊆
      ball (C m) (ρ m) := by
    obtain ⟨c,N,hgeom,hspec⟩ := hfam
    exact (hspec.1 m).1
  have hτ : tauN φ m = (lamMinus φ m+lamPlus φ m)/2 := by
    rw [tauN_value38 φ hφ m]
    ring
  refine ⟨hK,hDn,?_⟩
  intro z hz
  have hp : (φ,z) ∈ rootDomain38 :=
    ⟨hφ,fixed_sphere_subset φ C ρ hfam m hz⟩
  have hSn : S z ≠ 0 := by
    change stdRoot38 (tauN φ m) (gamma2 φ m) z ≠ 0
    rw [hτ,gamma2_value38 φ hφ m]
    apply stdRoot_ne_zero38 (lamMinus φ m) (lamPlus φ m) z
    intro hseg
    exact (not_lt.mpr (mem_sphere.mp hz).ge) (mem_ball.mp (hcut hseg))
  refine ⟨hSn,?_⟩
  have he := a5CanonRoot_omitted_factorization38 m (φ,z) hp
  rw [rootFactor38] at he
  calc
    canonRoot38 φ z =
        2 * Complex.I * (S z / (Lib.piN m : ℂ)) * D z := he
    _ = K * S z * D z := by dsimp [K]; ring

private theorem rawBetaFixedAnalyticEqOnBallOfCircle38
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

/-- Full Q factorization extends to the CLOSED filled own disc.
Canonical-root analyticity and the branch square are used only on its circle. -/
theorem rawBetaFixedFilledFactorization38
    (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (ρ : ℤ → ℝ) (hfam : IsolatingFamily38 φ C ρ) (m : ℤ) :
    ∀ z ∈ closedBall (C m) (ρ m),
      perChar φ z = ((2 * Complex.I) / (Lib.piN m : ℂ))^2 *
        ((z-lamMinus φ m)*(z-lamPlus φ m)) *
          a5OmittedRootProduct38 m (φ,z)^2 := by
  let a : ℂ := lamMinus φ m
  let b : ℂ := lamPlus φ m
  let K : ℂ := (2 * Complex.I) / (Lib.piN m : ℂ)
  let D : ℂ → ℂ := fun z => a5OmittedRootProduct38 m (φ,z)
  let S : ℂ → ℂ := stdRoot38 (tauN φ m) (gamma2 φ m)
  let H : ℂ → ℂ := fun z => K^2 * ((z-a)*(z-b)) * D z^2
  have hρ : 0 < ρ m := isolating_radius_pos38 hfam m
  have hD : AnalyticOnNhd ℂ D (closedBall (C m) (ρ m)) := by
    intro z hz
    exact (a5OmittedRoot_analytic38 m (φ,z)
      (a5OwnClosedBall_omittedDomain38 φ hφ C ρ hfam m z hz)).comp
        (analyticAt_const.prod analyticAt_id)
  have hH : AnalyticOnNhd ℂ H (closedBall (C m) (ρ m)) := by
    intro z hz
    exact (analyticAt_const.mul
      ((analyticAt_id.sub analyticAt_const).mul
        (analyticAt_id.sub analyticAt_const))).mul ((hD z hz).pow 2)
  have hboundary := (rawBetaFixedBoundaryRoot38 φ hφ C ρ hfam m).2.2
  have hτ : tauN φ m = (a+b)/2 := by
    rw [tauN_value38 φ hφ m]
    dsimp [a,b]
    ring
  have hPHcircle : EqOn (perChar φ) H (sphere (C m) (ρ m)) := by
    intro z hz
    have hp : (φ,z) ∈ rootDomain38 :=
      ⟨hφ,fixed_sphere_subset φ C ρ hfam m hz⟩
    have hSq : S z^2 = (z-a)*(z-b) := by
      change stdRoot38 (tauN φ m) (gamma2 φ m) z^2 = _
      rw [hτ,gamma2_value38 φ hφ m]
      rw [stdRoot_sq38 a b z (rootDomain_avoids38 hp m)]
      ring
    calc
      perChar φ z = canonRoot38 φ z^2 :=
        (canonRoot_sq38 φ hφ z hp.2).symm
      _ = (K * S z * D z)^2 := by rw [(hboundary z hz).2]
      _ = H z := by
        dsimp [H]
        rw [mul_pow,mul_pow,hSq]
  have hPH : EqOn (perChar φ) H (ball (C m) (ρ m)) :=
    rawBetaFixedAnalyticEqOnBallOfCircle38 (C m) (ρ m) hρ (perChar φ) H
      ((analyticOnNhd_perChar_z φ).mono (subset_univ _)) hH hPHcircle
  intro z hz
  change perChar φ z = H z
  by_cases hi : z ∈ ball (C m) (ρ m)
  · exact hPH hi
  · have he : dist z (C m) = ρ m :=
      le_antisymm (mem_closedBall.mp hz)
        (le_of_not_gt (fun ht => hi (mem_ball.mpr ht)))
    exact hPHcircle (mem_sphere.mpr he)

/-- The literal fixed-circle coefficient, including both genuine contour
integrabilities, realizes the full-Q ODE for the SAME supplied numerator. -/
theorem rawBetaFixedCoefficientOfZeroPeriod38
    (n m : ℤ) (F : PotPair → P2Space38 n) (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (ρ : ℤ → ℝ) (hfam : IsolatingFamily38 φ C ρ)
    (hperiod : abelianPeriod38 m φ (p6PsiNumerator38 n F φ) = 0) :
    CircleIntegrable (fun z => p6PsiNumerator38 n F φ z / canonRoot38 φ z)
      (discC φ m) (discR φ m) ∧
    CircleIntegrable (fun z => p6PsiNumerator38 n F φ z / canonRoot38 φ z)
      (C m) (ρ m) ∧
    AnalyticOnNhd ℂ (rawBetaFixedCoefficient38 n m F φ (C m) (ρ m))
      (ball (C m) (ρ m)) ∧
    ∀ z ∈ ball (C m) (ρ m),
      perChar φ z *
          deriv (rawBetaFixedCoefficient38 n m F φ (C m) (ρ m)) z +
        (deriv (perChar φ) z / 2) *
          rawBetaFixedCoefficient38 n m F φ (C m) (ρ m) z =
        p6PsiNumerator38 n F φ z := by
  let a : ℂ := lamMinus φ m
  let b : ℂ := lamPlus φ m
  let τ : ℂ := (a+b)/2
  let Ψ : ℂ → ℂ := p6PsiNumerator38 n F φ
  let D : ℂ → ℂ := fun z => a5OmittedRootProduct38 m (φ,z)
  let K : ℂ := (2 * Complex.I) / (Lib.piN m : ℂ)
  let S : ℂ → ℂ := stdRoot38 τ ((b-a)^2)
  let f : ℂ → ℂ := fun z => Ψ z / (K * D z)
  let H : ℂ → ℂ := fun z => K^2 * ((z-a)*(z-b)) * D z^2
  have hρ : 0 < ρ m := isolating_radius_pos38 hfam m
  have hcut : segment ℝ a b ⊆ ball (C m) (ρ m) := by
    obtain ⟨c,N,hgeom,hspec⟩ := hfam
    exact (hspec.1 m).1
  have hτ : tauN φ m = τ := by
    rw [tauN_value38 φ hφ m]
    dsimp [τ,a,b]
    ring
  have hgap : gamma2 φ m = (b-a)^2 := gamma2_value38 φ hφ m
  obtain ⟨hK,hDn,hboundary⟩ := rawBetaFixedBoundaryRoot38 φ hφ C ρ hfam m
  change K ≠ 0 at hK
  change ∀ z ∈ closedBall (C m) (ρ m), D z ≠ 0 at hDn
  have hactual : ∀ z ∈ sphere (C m) (ρ m),
      canonRoot38 φ z = K * S z * D z := by
    intro z hz
    simpa only [hτ,hgap] using (hboundary z hz).2
  have hSn : ∀ z ∈ sphere (C m) (ρ m), S z ≠ 0 := by
    intro z hz
    simpa only [hτ,hgap] using (hboundary z hz).1
  have hD : AnalyticOnNhd ℂ D (closedBall (C m) (ρ m)) := by
    intro z hz
    exact (a5OmittedRoot_analytic38 m (φ,z)
      (a5OwnClosedBall_omittedDomain38 φ hφ C ρ hfam m z hz)).comp
        (analyticAt_const.prod analyticAt_id)
  have hΨ : AnalyticOnNhd ℂ Ψ (closedBall (C m) (ρ m)) :=
    (p6PsiNumerator_entire38 n F φ).mono (subset_univ _)
  have hf : AnalyticOnNhd ℂ f (closedBall (C m) (ρ m)) :=
    hΨ.div (analyticOnNhd_const.mul hD)
      (fun z hz => mul_ne_zero hK (hDn z hz))
  obtain ⟨hI0,hI1,hfixedZero⟩ :=
    rawBetaFixedFamilyZeroPeriod38 n m F φ hφ C ρ hfam hperiod
  have hEqPeriod : EqOn (fun z => Ψ z / canonRoot38 φ z)
      (fun z => f z / S z) (sphere (C m) (ρ m)) := by
    intro z hz
    change Ψ z / canonRoot38 φ z = f z / S z
    rw [hactual z hz]
    dsimp [f]
    field_simp [hK,hDn z (sphere_subset_closedBall hz),hSn z hz] <;> ring
  have hstd : circleIntegral (fun z => f z / S z) (C m) (ρ m) = 0 := by
    have he := circleIntegral.integral_congr hρ.le hEqPeriod
    exact he.symm.trans hfixedZero
  let T : ℂ → ℂ := rawBetaStdCauchyCoefficient38 a b (C m) (ρ m) f
  obtain ⟨hT,hTode⟩ := rawBetaQuadraticODEOfZeroStdRootPeriodExplicit38
    a b (C m) (ρ m) hρ hcut f hf hstd
  have hPH : EqOn (perChar φ) H (ball (C m) (ρ m)) :=
    fun z hz => rawBetaFixedFilledFactorization38 φ hφ C ρ hfam m z
      (ball_subset_closedBall hz)
  let R : ℂ → ℂ := fun z => T z / (K * D z)
  have hR : AnalyticOnNhd ℂ R (ball (C m) (ρ m)) :=
    hT.div (analyticOnNhd_const.mul (hD.mono ball_subset_closedBall))
      (fun z hz => mul_ne_zero hK (hDn z (ball_subset_closedBall hz)))
  have hDensity :
      (fun t : ℝ => deriv (circleMap (C m) (ρ m)) t *
        (Ψ (circleMap (C m) (ρ m) t) /
          canonRoot38 φ (circleMap (C m) (ρ m) t))) =
      (fun t : ℝ => deriv (circleMap (C m) (ρ m)) t *
        (f (circleMap (C m) (ρ m) t) /
          S (circleMap (C m) (ρ m) t))) := by
    funext t
    exact congrArg (fun q : ℂ => deriv (circleMap (C m) (ρ m)) t * q)
      (hEqPeriod (circleMap_mem_sphere (C m) hρ.le t))
  have hB :
      (fun θ : ℝ => rawBetaFixedBoundaryPrimitive38 n m F φ (C m) (ρ m) θ /
        stdRoot38 (tauN φ m) (gamma2 φ m) (circleMap (C m) (ρ m) θ)) =
      (fun θ : ℝ => (∫ t in (0:ℝ)..θ,
        deriv (circleMap (C m) (ρ m)) t *
          (f (circleMap (C m) (ρ m) t) /
            S (circleMap (C m) (ρ m) t))) /
        S (circleMap (C m) (ρ m) θ)) := by
    funext θ
    rw [hτ,hgap]
    change (∫ t in (0:ℝ)..θ,
      deriv (circleMap (C m) (ρ m)) t *
        (Ψ (circleMap (C m) (ρ m) t) /
          canonRoot38 φ (circleMap (C m) (ρ m) t))) /
        S (circleMap (C m) (ρ m) θ) = _
    rw [hDensity]
  have hRliteral :
      rawBetaFixedCoefficient38 n m F φ (C m) (ρ m) = R := by
    funext z
    change rawBetaBoundaryCauchy38
      (fun θ => rawBetaFixedBoundaryPrimitive38 n m F φ (C m) (ρ m) θ /
        stdRoot38 (tauN φ m) (gamma2 φ m) (circleMap (C m) (ρ m) θ))
      (C m) (ρ m) z / (K * D z) = _
    rw [hB]
    rfl
  rw [hRliteral]
  refine ⟨hI0,hI1,hR,?_⟩
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

/-- The arbitrary full family may be fixed over a parameter neighborhood.
The SAME supplied W and F are retained; only actual certified membership and
its genuine normalized zero period are instantiated pointwise. -/
theorem rawBetaFixedCoefficientOnFamily38
    (W V : Set PotPair) (hW : W ⊆ gkW)
    (C : ℤ → ℂ) (ρ : ℤ → ℝ)
    (hfamily : ∀ φ ∈ V, IsolatingFamily38 φ C ρ)
    (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (hperiod : ∀ φ ∈ W,
      abelianPeriod38 m φ (p6PsiNumerator38 n (F n) φ) = 0) :
    ∀ φ ∈ V ∩ W,
      AnalyticOnNhd ℂ (rawBetaFixedCoefficient38 n m (F n) φ (C m) (ρ m))
        (ball (C m) (ρ m)) ∧
      ∀ z ∈ ball (C m) (ρ m),
        perChar φ z *
            deriv (rawBetaFixedCoefficient38 n m (F n) φ (C m) (ρ m)) z +
          (deriv (perChar φ) z / 2) *
            rawBetaFixedCoefficient38 n m (F n) φ (C m) (ρ m) z =
          p6PsiNumerator38 n (F n) φ z := by
  intro φ hφ
  exact (rawBetaFixedCoefficientOfZeroPeriod38 n m (F n) φ (hW hφ.2)
    C ρ (hfamily φ hφ.1) (hperiod φ hφ.2)).2.2

end
end NlsGge.GK38

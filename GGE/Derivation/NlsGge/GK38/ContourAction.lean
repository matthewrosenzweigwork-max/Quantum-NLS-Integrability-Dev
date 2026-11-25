import NlsGge.GK38.ContourActionDeformation
import NlsGge.GK38.Lib.ParamCircleAnalytic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring

/-! Analyticity and free normalization of the concrete contour actions.
Fixed local isolating families transfer analyticity to the selected contours;
free normalization uses boundary equality with an integrable polynomial. -/
set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.GK38
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

def LocalFixedAgreement38 : Prop :=
  ∀ (V : Set PotPair), V ⊆ gkW →
    ∀ (C : ℤ → ℂ) (R : ℤ → ℝ),
      (∀ φ ∈ V, IsolatingFamily38 φ C R) →
      ∀ φ ∈ V, ∀ n : ℤ,
        gkActionC38 φ n = contourAction38 φ (C n) (R n)

def ActionAnalytic38 : Prop :=
  ∀ n : ℤ, AnalyticOnNhd ℂ (fun φ : PotPair => gkActionC38 φ n) gkW

def FreeAction38 : Prop :=
  ∀ n : ℤ, gkActionC38 (0 : PotPair) n = 0

def ContourOffCuts38 : Prop :=
  ∀ (φ : PotPair), φ ∈ gkW →
    ∀ (C : ℤ → ℂ) (R : ℤ → ℝ), IsolatingFamily38 φ C R →
      ∀ (n : ℤ) (z : ℂ), z ∈ sphere (C n) (R n) → z ∉ gapSegments38 φ

theorem fixed_sphere_subset (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    sphere (C n) (R n) ⊆ actionCutDomain38 φ := by
  simpa only [sub_zero, one_smul, zero_smul, add_zero, one_mul, zero_mul] using
    (action_contour_sphere_subset38 φ C C R R hf hf n 0 ⟨le_rfl, zero_le_one⟩)

theorem contour_off_cuts38 : ContourOffCuts38 := by
  intro φ _ C R hf n z hz
  exact fixed_sphere_subset φ C R hf n hz

theorem local_fixed_agreement38 : LocalFixedAgreement38 := by
  intro V hV C R hf φ hφ n
  exact action_contour_independence38 φ (hV hφ)
    (discC φ) C (discR φ) R (isolating_family38 φ (hV hφ)) (hf φ hφ) n

theorem fixed_boundary_joint_analytic (V : Set PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hV : V ⊆ gkW) (hf : ∀ φ ∈ V, IsolatingFamily38 φ C R) (n : ℤ) :
    AnalyticOnNhd ℂ (Function.uncurry actionIntegrand38)
      (V ×ˢ sphere (C n) (R n)) := by
  intro p hp
  exact actionIntegrand_joint_analytic38 p
    ⟨hV hp.1, fixed_sphere_subset p.1 C R (hf p.1 hp.1) n hp.2⟩

-- The result retains genuine integrability as well as the fixed-action analytic map.
theorem fixed_action_integrable_analytic (V : Set PotPair)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hVo : IsOpen V) (hV : V ⊆ gkW)
    (hf : ∀ φ ∈ V, IsolatingFamily38 φ C R)
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ V) (n : ℤ) :
    (∀ φ ∈ V, CircleIntegrable (actionIntegrand38 φ) (C n) (R n)) ∧
      AnalyticOnNhd ℂ (fun φ => contourAction38 φ (C n) (R n)) V := by
  have h := Lib.parametricCircleAnalytic38 PotPair V (C n) (R n)
    actionIntegrand38 hVo (isolating_radius_pos38 (hf φ₀ hφ₀) n)
    (fixed_boundary_joint_analytic V C R hV hf n)
  exact ⟨h.1, analyticOnNhd_const.mul h.2⟩

theorem action_analytic38 : ActionAnalytic38 := by
  intro n φ hφ
  obtain ⟨V, hV, hVW, hVo, _, C, R, hf⟩ := local_isolatingFamily φ hφ
  have hφV := mem_of_mem_nhds hV
  have h := fixed_action_integrable_analytic V C R hVo hVW hf φ hφV n
  apply (h.2 φ hφV).congr
  filter_upwards [hV] with ψ hψ
  exact (local_fixed_agreement38 V hVW C R hf ψ hψ n).symm

theorem free_mem_gkW : (0 : PotPair) ∈ gkW := by
  simpa only [realSlice_zero] using realSlice_mem_gkW (0 : PhysicalL2)

-- Actual HasDerivAt is constructed before rewriting any totalized spectral deriv.
theorem free_discrim_hasDeriv (z : ℂ) :
    HasDerivAt (discrim (0 : PotPair)) (-2 * Complex.sin z) z := by
  have he : discrim (0 : PotPair) = fun w => 2 * Complex.cos w := funext discrim_zero
  rw [he]
  simpa only [mul_neg, neg_mul] using (Complex.hasDerivAt_cos z).const_mul (2 : ℂ)

theorem free_integrand_off_cuts (z : ℂ) (hz : z ∉ gapSegments38 (0 : PotPair)) :
    actionIntegrand38 (0 : PotPair) z = -Complex.I * z := by
  have hroot := canonRoot_ne_zero38 (0 : PotPair) free_mem_gkW z hz
  have hr := canonRoot_free38 z hz
  have hden : (-2 : ℂ) * Complex.I * Complex.sin z ≠ 0 := by
    rw [← hr]
    exact hroot
  have hd := free_discrim_hasDeriv z
  unfold actionIntegrand38
  rw [hd.deriv, hr]
  apply (div_eq_iff hden).2
  calc
    z * (-2 * Complex.sin z) = (2 * (Complex.I ^ 2)) * (z * Complex.sin z) := by
      rw [Complex.I_sq]
      ring
    _ = (-Complex.I * z) * (-2 * Complex.I * Complex.sin z) := by ring

-- Polynomial integrability is retained before the primitive circle-integral identity.
theorem free_polynomial_integrable_zero (c : ℂ) (r : ℝ) (hr : 0 ≤ r) :
    CircleIntegrable (fun z : ℂ => -Complex.I * z) c r ∧
      circleIntegral (fun z : ℂ => -Complex.I * z) c r = 0 := by
  have hc : Continuous (fun z : ℂ => -Complex.I * z) :=
    continuous_const.mul continuous_id
  have hi : CircleIntegrable (fun z : ℂ => -Complex.I * z) c r :=
    hc.continuousOn.circleIntegrable hr
  have hd (z : ℂ) :
      HasDerivAt (fun w : ℂ => (-Complex.I / 2) * w ^ 2) (-Complex.I * z) z := by
    convert (hasDerivAt_pow 2 z).const_mul (-Complex.I / 2) using 1; ring
  refine ⟨hi, ?_⟩
  exact circleIntegral.integral_eq_zero_of_hasDerivWithinAt hr
    (fun z _ => (hd z).hasDerivWithinAt)

theorem free_fixed_action_zero (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hf : IsolatingFamily38 (0 : PotPair) C R) (n : ℤ) :
    CircleIntegrable (actionIntegrand38 (0 : PotPair)) (C n) (R n) ∧
      contourAction38 (0 : PotPair) (C n) (R n) = 0 := by
  have hi := action_circle_integrable38 (0 : PotPair) free_mem_gkW C R hf n
  have hr := isolating_radius_pos38 hf n
  have hs := fixed_sphere_subset (0 : PotPair) C R hf n
  have hb : EqOn (actionIntegrand38 (0 : PotPair))
      (fun z : ℂ => -Complex.I * z) (sphere (C n) (R n)) := by
    intro z hz
    exact free_integrand_off_cuts z (hs hz)
  have hp := free_polynomial_integrable_zero (C n) (R n) hr.le
  have he := circleIntegral.integral_congr hr.le hb
  refine ⟨hi, ?_⟩
  unfold contourAction38
  rw [he, hp.2, mul_zero]

theorem free_action38 : FreeAction38 := by
  intro n
  exact (free_fixed_action_zero (discC (0 : PotPair)) (discR (0 : PotPair))
    (isolating_family38 (0 : PotPair) free_mem_gkW) n).2

end
end NlsGge.GK38

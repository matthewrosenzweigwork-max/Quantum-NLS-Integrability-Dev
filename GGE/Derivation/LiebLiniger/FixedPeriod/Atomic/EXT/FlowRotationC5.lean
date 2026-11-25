import LiebLiniger.FixedPeriod.Atomic.EXT.FlowRotationC4

/-! # Integration of the actual finite-gap scalar ODE

Actual action conservation freezes the entire zero-extended action vector.
An integrating factor for the existing actual finite-plane ODE gives rotation
at every real time, without a further PDE uniqueness input.
-/

set_option autoImplicit false
noncomputable section
namespace LiebLiniger.FixedPeriod.EXT

open NlsGge.Birkhoff NlsGge.NLS38

local notation "B0" =>
  NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.toBirkhoffTop38

/-- The full zero-extended action sequence of the actual finite-plane
trajectory is constant, including coordinates outside the plane. -/
theorem finiteGap_extended_actions38 (Λ : Finset ℤ) (w : Λ → ℂ) (t : ℝ) :
    (fun k => ‖extZero38 Λ (ZΛ Λ w t) k‖ ^ 2) =
      fun k => ‖extZero38 Λ w k‖ ^ 2 := by
  have hu := finiteSupport_physicalSobolev_all38 ((B0).finiteGapField38 Λ w)
    ((B0).finite_support_Φ_finiteGapField38 Λ w) 3
  funext k
  rw [← actualPhi_eq_extZero_ZΛ38 Λ w t, actualPhi_normSq_nlsFlow38 _ hu,
    (B0).Φ_finiteGapField38]

set_option maxHeartbeats 400000 in
/-- Integrating the scalar ODE along the actual trajectory gives the exact
negative-exponential rotation with the initial actions frozen at every time. -/
theorem finiteGap_actualRotation38 :
    ∀ (Ω : ℤ → (ℤ → ℝ) → ℝ),
      (∀ (Λ : Finset ℤ) (w : Λ → ℂ) (i : Λ),
        YΛ Λ w i = -Complex.I *
          (Ω i.1 (fun k => ‖extZero38 Λ w k‖ ^ 2) : ℂ) * w i) →
      ∀ (Λ : Finset ℤ) (w : Λ → ℂ) (t : ℝ) (i : Λ),
        ZΛ Λ w t i =
          Complex.exp (-(((t * Ω i.1 (fun k => ‖extZero38 Λ w k‖ ^ 2) : ℝ) : ℂ) *
            Complex.I)) * w i := by
  intro Ω hΩ Λ w t i
  let a : ℤ → ℝ := fun k => ‖extZero38 Λ w k‖ ^ 2
  let c : ℂ := (Ω i.1 a : ℂ) * Complex.I
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => ZΛ Λ w r i)
      (-Complex.I * (Ω i.1 a : ℂ) * ZΛ Λ w s i) s := by
    have hh := hasDerivAt_pi.1 (finiteGap_actualODE38 Λ w s) i
    rw [hΩ Λ (ZΛ Λ w s) i, finiteGap_extended_actions38 Λ w s] at hh
    exact hh
  let f : ℝ → ℂ := fun s => Complex.exp ((s : ℂ) * c) * ZΛ Λ w s i
  have hf (s : ℝ) : HasDerivAt f 0 s := by
    have hs : HasDerivAt (fun r : ℝ => (r : ℂ)) (1 : ℂ) s :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_id s)
    have hh := ((hs.mul_const c).cexp).mul (hd s)
    convert hh using 1
    dsimp only [f, c]
    ring
  have hconst := is_const_of_deriv_eq_zero (fun s => (hf s).differentiableAt)
    (fun s => (hf s).deriv) t 0
  have he : Complex.exp ((t : ℂ) * c) * ZΛ Λ w t i = w i := by
    simpa only [f, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, ZΛ_zero38] using hconst
  calc
    ZΛ Λ w t i = Complex.exp (-((t : ℂ) * c)) *
        (Complex.exp ((t : ℂ) * c) * ZΛ Λ w t i) := by
      rw [← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
    _ = Complex.exp (-((t : ℂ) * c)) * w i := congrArg
      (fun z : ℂ => Complex.exp (-((t : ℂ) * c)) * z) he
    _ = Complex.exp (-(((t * Ω i.1 (fun k => ‖extZero38 Λ w k‖ ^ 2) : ℝ) : ℂ) *
          Complex.I)) * w i := by
      congr 2
      dsimp only [c, a]
      push_cast
      ring

end LiebLiniger.FixedPeriod.EXT

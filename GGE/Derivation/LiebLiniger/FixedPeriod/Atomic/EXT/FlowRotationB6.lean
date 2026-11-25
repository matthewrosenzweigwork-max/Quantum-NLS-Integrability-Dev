import LiebLiniger.FixedPeriod.Atomic.EXT.FlowRotationB5

/-! # Phase invariance of the literal finite-plane Hamiltonian

Actual spectral-action conservation, differentiated along the actual trajectory,
annuls the angular differential of HΛ. Integrating one phase at a time gives
invariance under every finite coordinate phase, with no nonzero-coordinate premise.
-/

set_option autoImplicit false
noncomputable section
namespace LiebLiniger.FixedPeriod.EXT

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
local notation "B0" =>
  NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.toBirkhoffTop38

set_option maxHeartbeats 400000 in
/-- The actual trajectory has zero radial action derivative at its initial
finite-plane point, including at zero coordinates. -/
theorem actual_finitePlane_action_tangent38 (Λ : Finset ℤ) (w : Λ → ℂ) (i : Λ) :
    2 * (starRingEnd ℂ (w i) * deriv (ZΛ Λ w) 0 i).re = 0 := by
  have hu := finiteSupport_physicalSobolev_all38 ((B0).finiteGapField38 Λ w)
    ((B0).finite_support_Φ_finiteGapField38 Λ w) 3
  have he : (fun t : ℝ => ‖ZΛ Λ w t i‖ ^ 2) = fun _ : ℝ => ‖w i‖ ^ 2 := by
    funext t
    unfold ZΛ
    rw [actualPhi_normSq_nlsFlow38 _ hu, (B0).Φ_finiteGapField38,
      extZero38_apply_of_mem _ i.2]
  have hd := (hasDerivAt_pi.1 (finiteGap_actualODE38 Λ w 0) i).norm_sq
  have hder := (differentiable_ZΛ38 Λ w 0).hasDerivAt.unique (finiteGap_actualODE38 Λ w 0)
  rw [← hder] at hd
  have hzero := ZΛ_zero38 Λ w
  rw [hzero] at hd
  rw [he] at hd
  have hh := hd.unique (hasDerivAt_const (0 : ℝ) (‖w i‖ ^ 2))
  simpa only [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply, RCLike.re_eq_complex_re, mul_comm] using hh

set_option maxHeartbeats 400000 in
/-- Every individual negative coordinate-phase curve has zero HΛ derivative
at zero, obtained from conservation of its actual action and the finite
Hamiltonian pairing. -/
theorem HLambda_singlePhase_derivative_zero38 :
    ∀ (Λ : Finset ℤ) (w : Λ → ℂ) (i : Λ),
      HasDerivAt (fun θ : ℝ => HΛ Λ (fun j => if j = i then
        Complex.exp (-(θ : ℂ) * Complex.I) * w j else w j)) 0 0 := by
  intro Λ w i
  classical
  have hp := HΛ_fderiv_actual38 Λ w 0 (Pi.single i (-Complex.I * w i))
  rw [ZΛ_zero38] at hp
  have hs : fderiv ℝ (HΛ Λ) w (Pi.single i (-Complex.I * w i)) = 0 := by
    calc
      fderiv ℝ (HΛ Λ) w (Pi.single i (-Complex.I * w i)) =
          2 * (starRingEnd ℂ (deriv (ZΛ Λ w) 0 i) * (-Complex.I * w i)).im := by
        rw [finitePlane_symplectic_single38] at hp
        exact hp
      _ = -(2 * (starRingEnd ℂ (w i) * deriv (ZΛ Λ w) 0 i).re) := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
          Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
        ring
      _ = 0 := by rw [actual_finitePlane_action_tangent38, neg_zero]
  have hphase : HasDerivAt (fun θ : ℝ => fun j : Λ => if j = i then
      Complex.exp (-(θ : ℂ) * Complex.I) * w j else w j)
      (Pi.single i (-Complex.I * w i)) 0 := by
    apply hasDerivAt_pi.2
    intro j
    by_cases hj : j = i
    · subst j
      have hc : HasDerivAt (fun θ : ℝ => (θ : ℂ)) (1 : ℂ) 0 :=
        Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_id (0 : ℝ))
      simpa only [Pi.neg_apply, ite_true, Pi.single_eq_same, Complex.ofReal_zero, neg_zero,
        zero_mul, Complex.exp_zero, neg_mul, one_mul] using
        ((hc.neg.mul_const Complex.I).cexp.mul_const (w i))
    · simpa only [hj, ite_false, Pi.single_eq_of_ne hj] using
        (hasDerivAt_const (0 : ℝ) (w j))
  have hbase : (fun j : Λ => if j = i then
      Complex.exp (-(0 : ℂ) * Complex.I) * w j else w j) = w := by
    simp only [neg_zero, zero_mul, Complex.exp_zero, one_mul, ite_self]
  have hf : HasFDerivAt (HΛ Λ) (fderiv ℝ (HΛ Λ) w)
      (fun j : Λ => if j = i then Complex.exp (-(0 : ℂ) * Complex.I) * w j else w j) := by
    rw [hbase]
    exact (analytic_HLambda38 Λ w (Set.mem_univ _)).differentiableAt.hasFDerivAt
  have hh := hf.comp_hasDerivAt 0 hphase
  rw [hs] at hh
  exact hh

end LiebLiniger.FixedPeriod.EXT

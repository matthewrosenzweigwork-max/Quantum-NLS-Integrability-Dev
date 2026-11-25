import NlsGge.ThirdConsultation.PDE.Round4

/- PDE027 PRODUCTION01 (proof development, AUTHOR; not reviewed).  Heads verbatim from PRO_DEFINITION_RESPONSE_FP80_04.md. -/
set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
open NlsGge.ThirdConsultation.PDE
namespace NlsGge.ThirdConsultation.PDE

theorem quartic_derivative
    (x : H1C38) :
    HasFDerivAt quartH1 (quarticDifferential x) x := by
  have hq : quartH1 = fun z : H1C38 => ‖convC38 z z‖ ^ 2 := by
    funext z; exact quart_coe_eq z
  have hc : HasFDerivAt (fun z : H1C38 => convC38 z z)
      ((convC38 x).comp (ContinuousLinearMap.id ℝ H1C38) + convC38.flip x) x :=
    convC38.hasFDerivAt.clm_apply (hasFDerivAt_id x)
  have h := hc.norm_sq
  rw [hq]
  refine h.congr_fderiv ?_
  ext v
  simp only [quarticDifferential, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_id', id_eq,
    ContinuousLinearMap.flip_apply, convC38_comm v x, inner_add_right, smul_eq_mul, nsmul_eq_mul,
    Nat.cast_ofNat]
  ring

theorem quarticDifferential_apply
    (x v : H1C38) :
    quarticDifferential x v =
      2 * (∑' n : ℤ,
        star (nonlin (carrierCoe38 ((1 : ℕ) : ℝ) x) n) *
          carrierCoe38 ((1 : ℕ) : ℝ) v n).re := by
  let γ : ℝ → H1C38 := fun s => x + s • v
  have hγ : HasDerivAt γ v 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    simpa [γ] using this
  have hF : HasFDerivAt quartH1 (quarticDifferential x) (γ 0) := by
    simpa [γ] using quartic_derivative x
  have h1 := hF.comp_hasDerivAt (0 : ℝ) hγ
  have h2 := hasDerivAt_quart hγ
  have h3 := h1.unique h2
  have e : γ 0 = x := by simp [γ]
  rw [e] at h3
  exact h3

theorem hamiltonianGradient0_coordinate
    (x : HamiltonianCore38) (n : ℤ) :
    carrierCoe38 ((0 : ℕ) : ℝ) (hamiltonianGradient0 x) n =
      ((disp n : ℝ) : ℂ) *
          carrierCoe38 (((1 : ℕ) : ℝ) + 2) x n +
        nonlin (carrierCoe38 (((1 : ℕ) : ℝ) + 2) x) n := by
  unfold hamiltonianGradient0
  rw [coe_incl01, coe_add, Pi.add_apply, carrierCoe38_J38, carrierCoe38_lam,
    carrierCoe38_nonlinC, hamiltonianBase, carrierCoe38_incl38]
  have hI : Complex.I * (-(Complex.I * ((disp n : ℝ) : ℂ))) = ((disp n : ℝ) : ℂ) := by
    linear_combination (-((disp n : ℝ) : ℂ)) * Complex.I_mul_I
  rw [← mul_assoc, hI]

theorem hamiltonianDifferential_apply
    (x : HamiltonianCore38) (v : H1C38) :
    hamiltonianDifferential x v =
      2 * (∑' n : ℤ,
        star
          (((disp n : ℝ) : ℂ) *
              carrierCoe38 (((1 : ℕ) : ℝ) + 2) x n +
            nonlin (carrierCoe38 (((1 : ℕ) : ℝ) + 2) x) n) *
          carrierCoe38 ((1 : ℕ) : ℝ) v n).re := by
  have h : hamiltonianDifferential x v = 2 * inner ℝ (hamiltonianGradient0 x) (incl01 v) := by
    simp [hamiltonianDifferential, innerSL_apply_apply]
  rw [h, inner_eq_re_tsum_zero]
  congr 2
  refine tsum_congr fun n => ?_
  rw [hamiltonianGradient0_coordinate, coe_incl01]
  rfl

theorem hamiltonian_derivative
    (x : HamiltonianCore38) :
    HasFDerivAt hamH1 (hamiltonianDifferential x) (hamiltonianBase x) := by
  set b := hamiltonianBase x with hb
  have hfun : hamH1 = fun y : H1C38 =>
      4 * Real.pi ^ 2 * (‖y‖ ^ 2 - ‖incl01 y‖ ^ 2) + quartH1 y := by
    funext y
    unfold hamH1 quartH1
    rw [ham_def, kin_coe_eq]
  have hA : HasFDerivAt (fun y : H1C38 => ‖y‖ ^ 2) (2 • innerSL ℝ b) b :=
    (hasStrictFDerivAt_norm_sq b).hasFDerivAt
  have hB : HasFDerivAt (fun y : H1C38 => ‖incl01 y‖ ^ 2)
      ((2 • innerSL ℝ (incl01 b)).comp incl01) b :=
    ((hasStrictFDerivAt_norm_sq (incl01 b)).hasFDerivAt).comp b incl01.hasFDerivAt
  have hh := (((hA.sub hB).const_mul (4 * Real.pi ^ 2)).add (quartic_derivative b))
  rw [hfun]
  refine hh.congr_fderiv ?_
  ext v
  have hq := quarticDifferential_apply b v
  have hk := re_tsum_disp b v
  have hG : hamiltonianDifferential x v =
      2 * inner ℝ (incl01 (J38 ((1 : ℕ) : ℝ) (lam ((1 : ℕ) : ℝ) x))) (incl01 v) +
        2 * inner ℝ (incl01 (nonlinC 1 (show 1 ≤ (1 : ℕ) from le_rfl) b)) (incl01 v) := by
    simp only [hamiltonianDifferential, hamiltonianGradient0, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, map_add, ContinuousLinearMap.add_apply, inner_add_left, smul_eq_mul, hb]
    ring
  rw [hG, inner_incl01, inner_incl01]
  have hT : (∑' n : ℤ, (starRingEnd ℂ) (carrierCoe38 ((1 : ℕ) : ℝ)
        (J38 ((1 : ℕ) : ℝ) (lam ((1 : ℕ) : ℝ) x)) n) * carrierCoe38 ((1 : ℕ) : ℝ) v n) =
      ∑' n : ℤ, ((disp n : ℝ) : ℂ) *
        ((starRingEnd ℂ) (carrierCoe38 ((1 : ℕ) : ℝ) b n) * carrierCoe38 ((1 : ℕ) : ℝ) v n) := by
    refine tsum_congr fun n => ?_
    have hbn : carrierCoe38 ((1 : ℕ) : ℝ) b n = carrierCoe38 (((1 : ℕ) : ℝ) + 2) x n := by
      rw [hb, hamiltonianBase, carrierCoe38_incl38]
    rw [hbn, carrierCoe38_J38, carrierCoe38_lam]
    have hI : Complex.I * (-(Complex.I * ((disp n : ℝ) : ℂ))) = ((disp n : ℝ) : ℂ) := by
      linear_combination (-((disp n : ℝ) : ℂ)) * Complex.I_mul_I
    rw [← mul_assoc, hI, map_mul, Complex.conj_ofReal]
    ring
  have hN : (carrierCoe38 ((1 : ℕ) : ℝ) (nonlinC 1 (show 1 ≤ (1 : ℕ) from le_rfl) b)) =
      nonlin (carrierCoe38 ((1 : ℕ) : ℝ) b) := rfl
  have hq' : quarticDifferential b v =
      2 * (∑' n : ℤ, (starRingEnd ℂ) (nonlin (carrierCoe38 ((1 : ℕ) : ℝ) b) n) *
        carrierCoe38 ((1 : ℕ) : ℝ) v n).re := hq
  rw [hT, hN, hk]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, hq']
  ring

end NlsGge.ThirdConsultation.PDE

import Mathlib
import NlsGge.Atomic.G6.G6042Sup
import NlsGge.ThirdConsultation.Common.FiniteSupport
import NlsGge.ThirdConsultation.G6.Energy031A
import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.ThirdConsultation.PDE.Round14ActionRaw

                                                                                                                             
                                                                                                                
                                                                                                                            
                                                                                                                         
                                                                                          
                                                                                              
                                                                                                               
                                                                                                                
                                                                                   
                                                                                                                         
                                                                                 
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE

open NlsGge.ThirdConsultation.G6042S in
theorem dir_finiteSupport (n : ℤ) (a : ℂ) :
    FiniteSupportSequence (sequenceSobolevEmbed 1 (coordinateDirection n a)) := by
  refine (Set.finite_singleton n).subset (fun k hk => ?_)
  by_contra hkn
  apply hk
  change carrierCoe38 0 (carrierIncl38 (Nat.cast_nonneg 1) (coordinateDirection n a)) k = 0
  rw [carrierCoe38_incl38, coe_dir]
  simp [Pi.single_apply, show k ≠ n from hkn]

open NlsGge.ThirdConsultation.G6042S in
theorem symp_dir (x : ℤ → ℂ) (n : ℤ) (a : ℂ) :
    stdSymplectic38 x (carrierCoe38 ((1 : ℕ) : ℝ) (coordinateDirection n a)) =
      ((starRingEnd ℂ) (x n) * a).im := by
  unfold stdSymplectic38
  rw [coe_dir, tsum_eq_single n (fun k hk => by simp [Pi.single_apply, hk])]
  simp

theorem normsq_line (z a : ℂ) (t : ℝ) :
    ‖z + (t : ℂ) * a‖ ^ 2 = ‖z‖ ^ 2 + (2 * ((starRingEnd ℂ) z * a).re * t + ‖a‖ ^ 2 * t ^ 2) := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

open NlsGge.ThirdConsultation.G6042S in
/-- The line derivative of H in the direction e_n a. -/
theorem line_deriv (H : SobolevCarrier38 ((1 : ℕ) : ℝ) → ℝ) (z : SobolevCarrier38 ((1 : ℕ) : ℝ))
    (hdiff : DifferentiableAt ℝ H z)
    (hfac : ∀ z', H z' = actionHamiltonian (coordinateActionsPositive z'))
    (F : WeightedActionSpace → ℝ) (hF : LocalActionExtension F (coordinateActionsPositive z))
    (n : ℤ) (a : ℂ) :
    fderiv ℝ H z (coordinateDirection n a) =
      2 * ((starRingEnd ℂ) (carrierCoe38 ((1 : ℕ) : ℝ) z n) * a).re *
        (actionWeight n * fderiv ℝ F (coordinateActionsPositive z).val (lp.single 1 n (1 : ℝ))) := by
  obtain ⟨U, hU, hIU, hFa, hFag⟩ := hF
  set I := coordinateActionsPositive z with hI
  set e : WeightedActionSpace := lp.single 1 n (1 : ℝ) with he
  set c : ℝ := ((starRingEnd ℂ) (carrierCoe38 ((1 : ℕ) : ℝ) z n) * a).re with hc
  set q : ℝ := ‖a‖ ^ 2 with hq
  set φ : ℝ → ℝ := fun t => actionWeight n * (2 * c * t + q * t ^ 2) with hφ
  set γ : ℝ → SobolevCarrier38 ((1 : ℕ) : ℝ) := fun t => z + t • coordinateDirection n a with hγdef
  set ψ : ℝ → WeightedActionSpace := fun t => I.val + φ t • e with hψdef
  -- the actions along the line
  have hCA : ∀ t : ℝ, coordinateActions (γ t) = ψ t := by
    intro t
    apply lp.ext
    funext k
    show actionWeight k * ‖carrierCoe38 ((1 : ℕ) : ℝ) (z + t • coordinateDirection n a) k‖ ^ 2 =
      (I.val + φ t • e) k
    rw [carrierCoe38_add, carrierCoe38_smul, coe_dir, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, he, lp.single_apply]
    by_cases hk : k = n
    · subst hk
      simp only [Pi.single_eq_same, mul_one]
      rw [normsq_line]
      show _ = actionWeight k * ‖carrierCoe38 ((1 : ℕ) : ℝ) z k‖ ^ 2 + _
      simp only [hφ]
      ring
    · simp only [Pi.single_apply, hk, if_false, mul_zero, add_zero]
      rfl
  -- derivatives
  have hγ : HasDerivAt γ (coordinateDirection n a) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateDirection n a)).const_add z
    rw [one_smul] at h
    exact h
  have hγ0 : γ 0 = z := by simp [hγdef]
  have hL : HasDerivAt (H ∘ γ) (fderiv ℝ H z (coordinateDirection n a)) 0 :=
    hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ hγ0.symm
  have hφd : HasDerivAt φ (actionWeight n * (2 * c)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * c * t + q * t ^ 2) (2 * c * 1 + q * (2 * 0 ^ 1 * 1)) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_mul (2 * c)).add
        (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul q)
    have h2 := h1.const_mul (actionWeight n)
    simpa using h2
  have hψ : HasDerivAt ψ ((actionWeight n * (2 * c)) • e) 0 :=
    (hφd.smul_const e).const_add I.val
  have hψ0 : ψ 0 = I.val := by simp [hψdef, hφ]
  have hR : HasDerivAt (F ∘ ψ) (fderiv ℝ F I.val ((actionWeight n * (2 * c)) • e)) 0 :=
    (hFa I.val hIU).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hψ hψ0.symm
  have hψc : Continuous ψ := continuous_const.add
    ((continuous_const.mul ((continuous_const.mul continuous_id).add
      (continuous_const.mul (continuous_id.pow 2)))).smul continuous_const)
  have hnb : ψ ⁻¹' U ∈ 𝓝 (0 : ℝ) :=
    hψc.continuousAt.preimage_mem_nhds (by rw [hψ0]; exact hU.mem_nhds hIU)
  have hev : (H ∘ γ) =ᶠ[𝓝 0] (F ∘ ψ) := by
    filter_upwards [hnb] with t ht
    show H (γ t) = F (ψ t)
    rw [hfac (γ t), ← hCA t]
    have ht' : ψ t ∈ U := ht
    rw [← hCA t] at ht'
    exact (hFag (coordinateActionsPositive (γ t)) ht').symm
  have huniq := hL.unique (hR.congr_of_eventuallyEq hev)
  rw [huniq, map_smul, smul_eq_mul]
  ring

open NlsGge.ThirdConsultation.G6042S in
theorem coord_field_of (H : SobolevCarrier38 ((1 : ℕ) : ℝ) → ℝ) (z w : SobolevCarrier38 ((1 : ℕ) : ℝ))
    (hdiff : DifferentiableAt ℝ H z)
    (hfac : ∀ z', H z' = actionHamiltonian (coordinateActionsPositive z'))
    (hpair : ∀ v : SobolevCarrier38 ((1 : ℕ) : ℝ), FiniteSupportSequence (sequenceSobolevEmbed 1 v) →
      stdSymplectic38 (carrierCoe38 ((1 : ℕ) : ℝ) w) (carrierCoe38 ((1 : ℕ) : ℝ) v) =
        fderiv ℝ (fun z' => H z' / 2) z v)
    (F : WeightedActionSpace → ℝ) (hF : LocalActionExtension F (coordinateActionsPositive z))
    (n : ℤ) :
    carrierCoe38 ((1 : ℕ) : ℝ) w n =
      -Complex.I * ((actionWeight n *
        fderiv ℝ F (coordinateActionsPositive z).val (lp.single 1 n (1 : ℝ)) : ℝ) : ℂ) *
        carrierCoe38 ((1 : ℕ) : ℝ) z n := by
  set ω := actionWeight n * fderiv ℝ F (coordinateActionsPositive z).val (lp.single 1 n (1 : ℝ)) with hω
  have hhalf : ∀ v, fderiv ℝ (fun z' => H z' / 2) z v = fderiv ℝ H z v / 2 := by
    intro v
    have h := (hdiff.hasFDerivAt.mul_const (1 / 2 : ℝ))
    have e : (fun z' => H z' / 2) = fun z' => H z' * (1 / 2 : ℝ) := by funext z'; ring
    rw [e, h.fderiv]
    simp [div_eq_mul_inv]
    ring
  have h1 := hpair _ (dir_finiteSupport n 1)
  have hI := hpair _ (dir_finiteSupport n Complex.I)
  rw [symp_dir, hhalf, line_deriv H z hdiff hfac F hF] at h1 hI
  set x := (carrierCoe38 ((1 : ℕ) : ℝ) z n).re
  set y := (carrierCoe38 ((1 : ℕ) : ℝ) z n).im
  simp only [mul_one, Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_sub, mul_neg, neg_neg, zero_add] at h1 hI
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    linarith
  · simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    linarith

theorem raw_actions_mem (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    (fun k : ℤ => ‖carrierCoe38 ((1 : ℕ) : ℝ) z k‖ ^ 2) ∈ positiveActionCone := by
  refine ⟨fun k => sq_nonneg _, ?_⟩
  have h := (lp.memℓp (coordinateActions z)).summable (by norm_num : 0 < (1 : ENNReal).toReal)
  simp only [ENNReal.toReal_one, Real.rpow_one] at h
  refine h.congr (fun k => ?_)
  show ‖actionWeight k * ‖carrierCoe38 ((1 : ℕ) : ℝ) z k‖ ^ 2‖ = _
  have h0 : 0 ≤ actionWeight k * ‖carrierCoe38 ((1 : ℕ) : ℝ) z k‖ ^ 2 :=
    mul_nonneg (sobolevModeWeight_pos 1 k).le (sq_nonneg _)
  rw [Real.norm_of_nonneg h0]

theorem raw_actions_eq (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    rawActionToPositive (fun k : ℤ => ‖carrierCoe38 ((1 : ℕ) : ℝ) z k‖ ^ 2) (raw_actions_mem z) =
      coordinateActionsPositive z := rfl

end NlsGge.ThirdConsultation.PDE

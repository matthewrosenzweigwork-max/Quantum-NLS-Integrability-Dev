import NlsGge.Spectral.ActualQuasimomentumDecayE02_38
import NlsGge.Spectral.ActualQuasimomentumImaginaryAxisRiccatiE02_38
import NlsGge.Herglotz38.HerglotzMomentsE02_38
import NlsGge.Hierarchy.RiccatiPeriodicSolutionAsymptotic38
import NlsGge.Hierarchy.RiccatiQuasimomentumCoefficients38
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core

/-! # E02.05/.06 (campaign 38): the trace formula `Q_{2j}(u) = (2/π) ∫ (2λ)^{2j} v(λ) dλ`

Route: S1 (exact periodic Riccati solution with asymptotics, hierarchy) + S2 (Floquet link) give
the expansion of `k(iη)` with the local coefficients `riccatiQuasiCoeff38`; HB + HD give the
Herglotz representation; HM extracts the moments. -/

/-- Asymptotic expansion of `k(iη)` along the imaginary axis with the local coefficients. -/
theorem actualQuasimomentum_imaginaryAxis_expansion_E02_38 (u : PhysicalL2) (U : ℝ → ℂ)
    (hUs : ContDiff ℝ ∞ U) (hUp : Function.Periodic U 1)
    (hae : (fun s : ℝ => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      =ᵐ[volume.restrict (Set.Ioc (0:ℝ) 2)] U)
    (K : ℕ) :
    ∃ η₁ B : ℝ, 1 < η₁ ∧ ∀ η : ℝ, η₁ ≤ η →
      ‖(actualQuasimomentumE02_38 u (Complex.I*η) - Complex.I*η) -
        ∑ m ∈ Finset.Icc 1 K, riccatiQuasiCoeff38 U m * (η:ℂ)⁻¹ ^ m‖ ≤ B * η⁻¹ ^ (K+1) := by
  have hUc : Continuous U := hUs.continuous
  obtain ⟨η₀, C, hη₀, hS1⟩ := riccatiPeriodicSolution_asymptotic38 U hUs hUp K
  obtain ⟨Ub, hUb⟩ := isCompact_Icc.exists_bound_of_continuousOn (hUc.continuousOn (s := Set.Icc (0:ℝ) 1))
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  obtain ⟨Rh, hRh, hhigh⟩ := hk.2.2.2 1 one_pos
  set Sb : ℝ := ∑ m ∈ Finset.Icc 1 K, ‖riccatiQuasiCoeff38 U m‖
  have hSb : 0 ≤ Sb := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  set Ub' := |Ub|
  set C' := |C|
  set η₁ : ℝ := max (max η₀ Rh) (2 * (Sb + Ub' * C') + 2)
  have h0 : 0 ≤ Sb + Ub' * C' := by positivity
  refine ⟨η₁, Ub' * C', by
    have : 2 ≤ 2 * (Sb + Ub' * C') + 2 := by linarith
    exact lt_of_lt_of_le (by linarith) (le_trans this (le_max_right _ _)), ?_⟩
  intro η hη
  have hη0 : η₀ ≤ η := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hη
  have hηR : Rh ≤ η := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hη
  have hη2 : 2 * (Sb + Ub' * C') + 2 ≤ η := le_trans (le_max_right _ _) hη
  have hηpos : 0 < η := by linarith
  have hη1 : 1 ≤ η := by linarith
  obtain ⟨Γ, hΓc, hΓp, hΓd, hΓa⟩ := hS1 η hη0
  have hUb' : ∀ x ∈ Set.Icc (0:ℝ) 1, ‖U x‖ ≤ Ub' := fun x hx => (hUb x hx).trans (le_abs_self _)
  have hΓa' : ∀ x, ‖Γ x - ∑ k ∈ Finset.Icc 1 K,
      riccatiJetEvaluation U x (p k) * ((-2 * η : ℂ))⁻¹ ^ k‖ ≤ C' * η⁻¹ ^ (K + 1) := by
    intro x
    refine (hΓa x).trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have hexp := riccati_integral_expansion_Icc38 U hUs K η C' Ub' hηpos hUb' Γ hΓc hΓa'
  -- smallness of ∫ U Γ
  have hinvle : η⁻¹ ^ (K+1) ≤ η⁻¹ := by
    apply pow_le_of_le_one (by positivity) (inv_le_one_of_one_le₀ hη1) (by omega)
  have hsum : ‖∑ m ∈ Finset.Icc 1 K, riccatiQuasiCoeff38 U m * (η:ℂ)⁻¹ ^ m‖ ≤ Sb * η⁻¹ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro m hm
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hηpos]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    exact pow_le_of_le_one (by positivity) (inv_le_one_of_one_le₀ hη1) (by omega)
  set J := ∫ x in (0:ℝ)..1, U x * Γ x
  set Sumb := ∑ m ∈ Finset.Icc 1 K, riccatiQuasiCoeff38 U m * (η:ℂ)⁻¹ ^ m
  have hIJ : ‖Complex.I * J‖ ≤ Sb * η⁻¹ + Ub' * C' * η⁻¹ := by
    have h1 : ‖Complex.I * J‖ ≤ ‖Complex.I * J - Sumb‖ + ‖Sumb‖ := by
      have := norm_add_le (Complex.I * J - Sumb) Sumb; simpa using this
    have h2 : Ub' * (C' * η⁻¹ ^ (K + 1)) ≤ Ub' * C' * η⁻¹ := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hinvle (by positivity)
    linarith
  have hJ : ‖J‖ < 1 := by
    have hn : ‖Complex.I * J‖ = ‖J‖ := by simp
    rw [hn] at hIJ
    have : (Sb + Ub' * C') * η⁻¹ ≤ 1/2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hηpos]; linarith
    nlinarith
  have hk1 : ‖actualQuasimomentumE02_38 u (Complex.I*η) - Complex.I*η‖ < 1 := by
    have := hhigh η hηR 0
    simpa using this
  have hΓ1 : Γ 1 = Γ 0 := by simpa using hΓp 0
  have hS2 := actualQuasimomentum_imaginaryAxis_riccati_E02_38 u U hUc hae η
    (by linarith) Γ hΓc hΓ1 (fun x => by
      convert hΓd x using 1; ring) hJ hk1
  rw [hS2, add_sub_cancel_left, mul_assoc]
  exact hexp


theorem complex_I_pow_two_mul_E02_38 (i : ℕ) : Complex.I ^ (2*i) = (-1:ℂ)^i := by
  rw [pow_mul, Complex.I_sq]

/-- E02.05/.06, v2 A:eq:trace: for every H¹ class `u` with a smooth 1-periodic representative
`U` and every `j`, the even spectral moment is finite and equals the local charge:
`∫₀¹ (formal charge integrand j)(U) = (2/π) ∫ (2λ)^{2j} v(λ) dλ`. -/
theorem actualTraceFormula_complex_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (U : ℝ → ℂ) (hUs : ContDiff ℝ ∞ U) (hUp : Function.Periodic U 1)
    (hae : (fun s : ℝ => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      =ᵐ[volume.restrict (Set.Ioc (0:ℝ) 2)] U)
    (j : ℕ) :
    Integrable (fun t : ℝ => (2*t)^(2*j) * actualGapHeightE02_38 u t) ∧
    (∫ x in (0:ℝ)..1, riccatiJetEvaluation U x (formalChargeIntegrand j)) =
      (((2/Real.pi) * ∫ t : ℝ, (2*t)^(2*j) * actualGapHeightE02_38 u t : ℝ) : ℂ) := by
  set v := actualGapHeightE02_38 u with hvdef
  set K := 2*j+1 with hK
  have hvc : Continuous v := continuous_actualGapHeightE02_38 u
  have hv0 : ∀ t, 0 ≤ v t := actualGapHeightE02_38_nonneg u
  have hherg := actualQuasimomentum_herglotz_E02_38 u hu
  -- integrability of v/(1+|t|)
  have hvi : Integrable (fun t => v t / (1 + |t|)) := by
    have hI := (hherg Complex.I (by simp)).1
    refine hI.norm.mono' ((hvc.div (continuous_const.add continuous_abs)
      (fun t => ne_of_gt (show (0:ℝ) < 1 + |t| by have := abs_nonneg t; linarith))).aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
    have hpos : 0 < 1 + |t| := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hv0 t) hpos.le), norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hv0 t)]
    apply div_le_div_of_nonneg_left (hv0 t)
    · rw [norm_pos_iff, sub_ne_zero]; intro h; have := congrArg Complex.im h; simp at this
    · calc ‖(t:ℂ) - Complex.I‖ ≤ ‖(t:ℂ)‖ + ‖Complex.I‖ := norm_sub_le _ _
        _ = 1 + |t| := by rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_I]; ring
  -- coefficients
  let a : ℕ → ℂ := fun m => riccatiQuasiCoeff38 U (m+1) * Complex.I ^ (m+1)
  have ha : ∀ m ≤ 2*j, (a m).im = 0 := by
    intro m _
    rcases Nat.even_or_odd m with ⟨i, hi⟩ | ⟨i, hi⟩
    · -- m = 2i: b_{2i+1} purely imaginary
      have hb := riccatiQuasiCoeff38_odd_re U hUs hUp i
      have hm : m + 1 = 2*i + 1 := by omega
      set b := riccatiQuasiCoeff38 U (2*i+1)
      have hbI : b = (b.im : ℂ) * Complex.I := Complex.ext (by simp [hb]) (by simp)
      have hm2 : m = 2*i := by omega
      have hae' : a m = b * (Complex.I^(2*i) * Complex.I) := by
        simp only [a, pow_succ, hm2]
        rfl
      rw [hae', complex_I_pow_two_mul_E02_38, hbI]
      rcases neg_one_pow_eq_or ℂ i with h | h <;>
        simp [h, Complex.mul_im, Complex.mul_re]
    · -- m = 2i+1: b_{2i+2} real
      have hb := riccatiQuasiCoeff38_even_im U hUs hUp (i+1)
      have hm : m + 1 = 2*(i+1) := by omega
      simp only [a, hm, complex_I_pow_two_mul_E02_38]
      rcases neg_one_pow_eq_or ℂ (i+1) with h | h <;>
        simp [h, Complex.mul_im, hb]
  -- the expansion
  obtain ⟨η₁, B, hη₁, hB⟩ := actualQuasimomentum_imaginaryAxis_expansion_E02_38 u U hUs hUp hae K
  have hsum_eq : ∀ y : ℝ, 0 < y →
      ∑ m ∈ Finset.range (2*j+1), a m / (Complex.I * y) ^ (m+1) =
        ∑ m ∈ Finset.Icc 1 K, riccatiQuasiCoeff38 U m * (y:ℂ)⁻¹ ^ m := by
    intro y hy
    have hy0 : (y:ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, hK]
    apply Finset.sum_congr rfl
    intro m _
    simp only [a, mul_pow]
    rw [add_comm 1 m, inv_pow]
    field_simp
  have hexp : Tendsto (fun y : ℝ => (y:ℂ)^(2*j+1) * ((1/Real.pi : ℂ) *
      (∫ t, (v t : ℂ)/((t:ℂ) - Complex.I*y)) -
      ∑ m ∈ Finset.range (2*j+1), a m / (Complex.I*y)^(m+1))) atTop (𝓝 0) := by
    have hlim : Tendsto (fun y : ℝ => B / y) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop η₁] with y hy
    have hypos : 0 < y := by linarith
    have hz : 0 < (Complex.I * (y:ℂ)).im := by simp [hypos]
    have hk := (hherg (Complex.I*y) hz).2
    have hrep : (1/Real.pi : ℂ) * (∫ t, (v t : ℂ)/((t:ℂ) - Complex.I*y)) =
        actualQuasimomentumE02_38 u (Complex.I*y) - Complex.I*y := by
      rw [hk]; ring
    rw [hrep, hsum_eq y hypos, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hypos]
    calc y^(2*j+1) * ‖_‖ ≤ y^(2*j+1) * (B * y⁻¹ ^ (K+1)) :=
          mul_le_mul_of_nonneg_left (hB y hy) (by positivity)
      _ = B / y := by
          simp only [hK, inv_pow]
          field_simp
          ring
  have hHM := herglotz_moments_of_expansion_E02_38 v hv0 hvc.measurable hvi j a ha hexp
  obtain ⟨hint, hval⟩ := hHM (2*j) le_rfl
  -- identify a_{2j} with the local charge
  have hodd := riccatiQuasiCoeff38_odd U j
  set Qc := ∫ x in (0:ℝ)..1, riccatiJetEvaluation U x (formalChargeIntegrand j)
  have ha2j : a (2*j) = -((2:ℂ)^(2*j+1))⁻¹ * Qc := by
    simp only [a, hodd, pow_succ, complex_I_pow_two_mul_E02_38]
    have h1 : ((-1:ℂ)^j) * (-1)^j = 1 := by rw [← mul_pow]; norm_num
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (-((2:ℂ)^(2*j+1))⁻¹ * Qc) * h1 +
      ((-1:ℂ)^j * ((2:ℂ)^(2*j+1))⁻¹ * Qc * (-1)^j) * hI
  have hpow : ∀ t : ℝ, (2*t)^(2*j) * v t = 4^j * (t^(2*j) * v t) := by
    intro t; rw [mul_pow, pow_mul]; norm_num; ring
  refine ⟨?_, ?_⟩
  · have := hint.const_mul (4^j : ℝ)
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [hpow]
  · have hint2 : ∫ t : ℝ, (2*t)^(2*j) * v t = 4^j * ∫ t : ℝ, t^(2*j) * v t := by
      simp_rw [hpow]; exact integral_const_mul _ _
    rw [ha2j] at hval
    rw [hint2]
    have h2 : (2:ℂ)^(2*j+1) ≠ 0 := pow_ne_zero _ two_ne_zero
    have hQ : Qc = (2:ℂ)^(2*j+1) * ((1/Real.pi : ℂ) * ((∫ t, t^(2*j) * v t : ℝ) : ℂ)) := by
      field_simp at hval ⊢
      linear_combination -hval
    rw [hQ]
    push_cast
    rw [pow_succ, pow_mul]
    norm_num
    ring


/-- v2 A:eq:trace in the hierarchy's real normalization (`localCharge = Re ∫₀¹ formal charge`). -/
theorem actualTraceFormula_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (U : ℝ → ℂ) (hUs : ContDiff ℝ ∞ U) (hUp : Function.Periodic U 1)
    (hae : (fun s : ℝ => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      =ᵐ[volume.restrict (Set.Ioc (0:ℝ) 2)] U)
    (j : ℕ) :
    Integrable (fun t : ℝ => (2*t)^(2*j) * actualGapHeightE02_38 u t) ∧
    (∫ x in (0:ℝ)..1, riccatiJetEvaluation U x (formalChargeIntegrand j)).re =
      (2/Real.pi) * ∫ t : ℝ, (2*t)^(2*j) * actualGapHeightE02_38 u t := by
  obtain ⟨h1, h2⟩ := actualTraceFormula_complex_E02_38 u hu U hUs hUp hae j
  exact ⟨h1, by rw [h2, Complex.ofReal_re]⟩

end NlsGge.SpectralFoundations
end

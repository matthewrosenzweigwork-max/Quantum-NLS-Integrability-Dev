import NlsGge.Spectral.R3cIdentification38
import NlsGge.Spectral.R3cQuadIdentity38
import NlsGge.Spectral.QuadraticRiccatiRemainder38
import NlsGge.Hierarchy.RiccatiQuasimomentumExpansion38
import NlsGge.Hierarchy.FullEnergyPlaneConvergence38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter
open scoped Topology ContDiff
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core

/-! # T9: identification of the uniform expansion coefficients with the charges

`asymp_coeff_unique38`: uniqueness of finite asymptotic expansions in `1/η`.
`nonlin_coeff_ident38`: for a fixed Fourier plane, any real expansion of the nonlinear part
`n_η = Im k(iη) - η - q_η` to order `2k+1` has the coefficients `(-1)^j/(2·4^j) (Q_{2j} - Σ (2πn)^{2j}|z|²)`
at `η^{-(2j+1)}` and `0` at even powers. -/

/-- Uniqueness of finite asymptotic expansions. -/
theorem asymp_coeff_unique38 (K : ℕ) (a b : ℕ → ℂ) (C η₀ : ℝ)
    (h : ∀ η ≥ η₀, ‖∑ w ∈ Finset.range (K+1), (a w - b w) * (η:ℂ)⁻¹ ^ w‖ ≤ C * η⁻¹ ^ (K+1)) :
    ∀ w ≤ K, a w = b w := by
  set p : ℕ → ℂ := fun w => a w - b w with hp
  have key : ∀ m, m ≤ K + 1 → ∀ w < m, p w = 0 := by
    intro m
    induction m with
    | zero => intro _ w hw; omega
    | succ m ih =>
      intro hm w hw
      have hmK : m ≤ K := by omega
      have ih' := ih (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hw' | hwm
      · exact ih' w hw'
      · subst hwm
        by_contra hne
        set g : ℝ → ℂ := fun t => p w + ∑ v ∈ Finset.Ico (w + 1) (K + 1),
          p v * (t : ℂ) ^ (v - w) with hg
        have hgc : Continuous g := by
          simp only [hg]
          fun_prop
        have hbd : ∀ η : ℝ, max η₀ 1 ≤ η → ‖g η⁻¹‖ ≤ C * η⁻¹ ^ (K + 1 - w) := by
          intro η hη
          have hη1 : 1 ≤ η := (le_max_right _ _).trans hη
          have hηpos : 0 < η := by linarith
          have h1 := h η ((le_max_left _ _).trans hη)
          have hsplit : ∑ v ∈ Finset.range (K+1), p v * (η:ℂ)⁻¹ ^ v =
              ((η⁻¹ : ℝ) : ℂ) ^ w * g η⁻¹ := by
            rw [← Finset.sum_range_add_sum_Ico _ (show w ≤ K + 1 by omega),
              Finset.sum_eq_zero (fun v hv => by
                rw [ih' v (Finset.mem_range.mp hv), zero_mul]), zero_add,
              Finset.sum_eq_sum_Ico_succ_bot (by omega : w < K + 1)]
            simp only [hg, mul_add, Finset.mul_sum]
            congr 1
            · push_cast; ring
            · refine Finset.sum_congr rfl (fun v hv => ?_)
              have hv' := Finset.mem_Ico.mp hv
              have : v = w + (v - w) := by omega
              conv_lhs => rw [this]
              push_cast
              rw [pow_add]
              rw [← this]
              ring
          have h2 : ‖((η⁻¹ : ℝ) : ℂ) ^ w * g η⁻¹‖ ≤ C * η⁻¹ ^ (K + 1) := by
            rw [← hsplit]; exact h1
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hηpos)] at h2
          have hpos : 0 < η⁻¹ ^ w := pow_pos (inv_pos.mpr hηpos) w
          have : η⁻¹ ^ (K + 1) = η⁻¹ ^ w * η⁻¹ ^ (K + 1 - w) := by
            rw [← pow_add]; congr 1; omega
          rw [this, ← mul_assoc, mul_comm C, mul_assoc] at h2
          rw [mul_comm C]
          nlinarith [mul_comm (η⁻¹ ^ w) ‖g η⁻¹‖]
        have hT1 : Tendsto (fun η : ℝ => ‖g η⁻¹‖) atTop (𝓝 ‖g 0‖) :=
          (hgc.norm.tendsto 0).comp tendsto_inv_atTop_zero
        have hg0 : g 0 = p w := by
          simp only [hg]
          rw [Finset.sum_eq_zero (fun v hv => by
            have hv' := Finset.mem_Ico.mp hv
            have : v - w ≠ 0 := by omega
            simp [this]), add_zero]
        have hT2 : Tendsto (fun η : ℝ => C * η⁻¹ ^ (K + 1 - w)) atTop (𝓝 0) := by
          have h3 : Tendsto (fun η : ℝ => η⁻¹ ^ (K + 1 - w)) atTop (𝓝 (0 ^ (K + 1 - w))) :=
            tendsto_inv_atTop_zero.pow _
          rw [zero_pow (by omega)] at h3
          simpa using h3.const_mul C
        have hle : ‖g 0‖ ≤ 0 := by
          refine le_of_tendsto_of_tendsto hT1 hT2 ?_
          filter_upwards [eventually_ge_atTop (max η₀ 1)] with η hη
          exact hbd η hη
        rw [hg0] at hle
        exact hne (norm_le_zero_iff.mp hle)
  intro w hw
  have := key (K + 1) le_rfl w (by omega)
  exact sub_eq_zero.mp this


/-! ## The quadratic part: exact expansion for a plane -/

theorem quad_term_bound38 (k : ℕ) {a t η : ℝ} (ha : 0 ≤ a) (hη : 1 ≤ η) :
    |a * (2 * η / (4 * η ^ 2 + 4 * t ^ 2)) -
      ∑ j ∈ Finset.range (k + 1), (-1:ℝ) ^ j / (2 * 4 ^ j * η ^ (2 * j + 1)) *
        ((2 * t) ^ (2 * j) * a)| ≤ (1 / 2) * (t ^ (2 * k + 2) * a) * η⁻¹ ^ (2 * k + 3) := by
  have hηpos : 0 < η := by linarith
  have hid := quad_term_identity38 k a t η hηpos
  set X : ℝ := a * (2 * η / (4 * η ^ 2 + 4 * t ^ 2)) -
      ∑ j ∈ Finset.range (k + 1), (-1:ℝ) ^ j / (2 * 4 ^ j * η ^ (2 * j + 1)) *
        ((2 * t) ^ (2 * j) * a) with hX
  have hpow : 0 < η ^ (2 * k + 1) := pow_pos hηpos _
  have hXe : X = (η ^ (2 * k + 1))⁻¹ * ((1 / 2) * (-1) ^ (k + 1) *
      (t ^ (2 * k) * a * ((t / η) ^ 2 / (1 + (t / η) ^ 2)))) := by
    rw [← hid]; field_simp
  set x : ℝ := (t / η) ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hfrac : x / (1 + x) ≤ x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hfrac0 : 0 ≤ x / (1 + x) := by positivity
  rw [hXe, abs_mul, abs_of_pos (inv_pos.mpr hpow)]
  have h1 : |(1 / 2 : ℝ) * (-1) ^ (k + 1) * (t ^ (2 * k) * a * (x / (1 + x)))| ≤
      (1 / 2) * (t ^ (2 * k) * a * x) := by
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
      abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have : 0 ≤ t ^ (2 * k) * a := by
      have : 0 ≤ t ^ (2 * k) := by rw [pow_mul]; positivity
      positivity
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hfrac this
  calc (η ^ (2 * k + 1))⁻¹ * |(1 / 2 : ℝ) * (-1) ^ (k + 1) * (t ^ (2 * k) * a * (x / (1 + x)))|
      ≤ (η ^ (2 * k + 1))⁻¹ * ((1 / 2) * (t ^ (2 * k) * a * x)) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hpow.le)
    _ = (1 / 2) * (t ^ (2 * k + 2) * a) * η⁻¹ ^ (2 * k + 3) := by
        rw [hx, div_pow, inv_pow]
        field_simp
        ring

theorem quad_weight_nonneg38 (k N : ℕ) (z : FourierPlane N) (i : Fin (2 * N + 1)) :
    0 ≤ (Real.pi * (modeIndex N i : ℤ)) ^ (2 * k + 2) * ‖z i‖ ^ 2 := by
  have : 0 ≤ (Real.pi * (modeIndex N i : ℤ)) ^ (2 * k + 2) :=
    Even.pow_nonneg ⟨k + 1, by ring⟩ _
  positivity

theorem quad_expansion38 (k N : ℕ) (z : FourierPlane N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 1 ≤ η →
      |quadRiccati38 (planeL2 N z) η -
        ∑ j ∈ Finset.range (k + 1), (-1:ℝ) ^ j / (2 * 4 ^ j * η ^ (2 * j + 1)) *
          ∑ i : Fin (2 * N + 1), (2 * Real.pi * (modeIndex N i : ℤ)) ^ (2 * j) * ‖z i‖ ^ 2| ≤
        C * η⁻¹ ^ (2 * k + 2) := by
  refine ⟨(1 / 2) * ∑ i : Fin (2 * N + 1),
    (Real.pi * (modeIndex N i : ℤ)) ^ (2 * k + 2) * ‖z i‖ ^ 2,
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => quad_weight_nonneg38 k N z i),
    fun η hη => ?_⟩
  have hηpos : 0 < η := by linarith
  have hsum : quadRiccati38 (planeL2 N z) η -
        ∑ j ∈ Finset.range (k + 1), (-1:ℝ) ^ j / (2 * 4 ^ j * η ^ (2 * j + 1)) *
          ∑ i : Fin (2 * N + 1), (2 * Real.pi * (modeIndex N i : ℤ)) ^ (2 * j) * ‖z i‖ ^ 2 =
      ∑ i : Fin (2 * N + 1), (‖z i‖ ^ 2 * (2 * η / (4 * η ^ 2 +
          4 * (Real.pi * (modeIndex N i : ℤ)) ^ 2)) -
        ∑ j ∈ Finset.range (k + 1), (-1:ℝ) ^ j / (2 * 4 ^ j * η ^ (2 * j + 1)) *
          ((2 * (Real.pi * (modeIndex N i : ℤ))) ^ (2 * j) * ‖z i‖ ^ 2)) := by
    rw [quadRiccati38_planeL2_eq_sum, Finset.sum_sub_distrib]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      congr 2
      ring
    · simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [mul_assoc 2 Real.pi]
  rw [hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin (2 * N + 1))),
      |‖z i‖ ^ 2 * (2 * η / (4 * η ^ 2 + 4 * (Real.pi * (modeIndex N i : ℤ)) ^ 2)) -
        ∑ j ∈ Finset.range (k + 1), (-1:ℝ) ^ j / (2 * 4 ^ j * η ^ (2 * j + 1)) *
          ((2 * (Real.pi * (modeIndex N i : ℤ))) ^ (2 * j) * ‖z i‖ ^ 2)| ≤
      (1 / 2) * ((Real.pi * (modeIndex N i : ℤ)) ^ (2 * k + 2) * ‖z i‖ ^ 2) *
        η⁻¹ ^ (2 * k + 3) := fun i _ => quad_term_bound38 k (by positivity) hη
  refine (Finset.sum_le_sum hle).trans ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hS : 0 ≤ (1 / 2 : ℝ) * ∑ i : Fin (2 * N + 1),
      (Real.pi * (modeIndex N i : ℤ)) ^ (2 * k + 2) * ‖z i‖ ^ 2 :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => quad_weight_nonneg38 k N z i)
  refine mul_le_mul_of_nonneg_left ?_ hS
  exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hη) (by omega)


/-! ## The true expansion of `Im k(iη) - η` for a plane -/

theorem im_sum_coeff38 (K : ℕ) (b : ℕ → ℂ) (η : ℝ) :
    (∑ m ∈ Finset.Icc 1 K, b m * (η : ℂ)⁻¹ ^ m).im =
      ∑ m ∈ Finset.Icc 1 K, (b m).im * η⁻¹ ^ m := by
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.im_mul_ofReal]

theorem riccati_true_expansion38 (N : ℕ) (z : FourierPlane N) (K : ℕ) :
    ∃ η₁ C₁ : ℝ, 1 ≤ η₁ ∧ ∀ η : ℝ, η₁ ≤ η →
      |((actualQuasimomentumE02_38 (planeL2 N z) (Complex.I * η)).im - η) -
        ∑ m ∈ Finset.range (K + 1),
          (riccatiQuasiCoeff38 (planeReal N z) m).im * η⁻¹ ^ m| ≤ C₁ * η⁻¹ ^ (K + 1) := by
  classical
  set U : ℝ → ℂ := planeReal N z with hUdef
  have hu : ContDiff ℝ ∞ U := planeReal_smooth38 N z
  have hper : Function.Periodic U 1 := planeReal_periodic N z
  have hUc : Continuous U := hu.continuous
  set S1 : ℝ := ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 * ‖z i‖ ^ 2 with hS1
  have hS10 : 0 ≤ S1 := Finset.sum_nonneg (fun i _ => by positivity)
  set B : ℝ := Real.sqrt S1 with hBdef
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hSB : S1 ≤ B ^ 2 := (Real.sq_sqrt hS10).ge
  obtain ⟨ηP, hηP, hP⟩ := r3c_im_eq_pair38 B hB
  set A : ℝ := Real.sqrt bracketSumE02_38 * B with hAdef
  have hA0 : 0 ≤ A := mul_nonneg (Real.sqrt_nonneg _) hB
  have hUb : ∀ x, ‖U x‖ ≤ A := by
    intro x
    refine (plane_sup_le_r3c N z x).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    calc Real.sqrt S1 ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt hSB
      _ = B := Real.sqrt_sq hB
  obtain ⟨ηA, CA, hηA, hAs⟩ := riccatiPeriodicSolution_asymptotic38 U hu hper K
  choose bd hbd0 hbd using fun P : Poly => evalJet_bound38 U hu hper P
  set Mb : ℝ := ∑ m ∈ Finset.Icc 1 K, bd (p m) with hMb
  have hMb0 : 0 ≤ Mb := Finset.sum_nonneg (fun m _ => hbd0 _)
  set b : ℝ := max (A / 2 + A ^ 3 / 4) (Mb + |CA|) with hbdef
  obtain ⟨ηU, hηU, huniq⟩ := riccatiPeriodicSolution_unique38 U hu hper b
  refine ⟨max (max (max ηP ηA) ηU) 1, A * CA, le_max_right _ _, fun η hη => ?_⟩
  have hηP' : ηP ≤ η := ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hη
  have hηA' : ηA ≤ η := ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hη
  have hηU' : ηU ≤ η := ((le_max_right _ _).trans (le_max_left _ _)).trans hη
  have hη1 : 1 ≤ η := (le_max_right _ _).trans hη
  have hηpos : 0 < η := by linarith
  obtain ⟨Γu, hΓuc, hΓup, hΓud, hΓub, hk⟩ := hP N z hSB η hηP'
  obtain ⟨ΓK, hΓKc, hΓKp, hΓKd, hasym⟩ := hAs η hηA'
  -- sup bound of Γu
  have hUbar : Continuous (fun y => star (U y)) := hUc.star
  have hRb : ∀ x, ‖resolv38 η (fun y => star (U y)) x‖ ≤ A / (2 * η) :=
    fun x => resolv38_bound hηpos hUbar (fun y => by simpa using hUb y) x
  have hη1' : η⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hη1
  have hΓusup : ∀ x, ‖Γu x‖ ≤ b := by
    intro x
    have h1 := hΓub x
    have h2 := hRb x
    have h3 : ‖Γu x‖ ≤ ‖Γu x - resolv38 η (fun y => star (U y)) x‖ +
        ‖resolv38 η (fun y => star (U y)) x‖ := by
      have := norm_add_le (Γu x - resolv38 η (fun y => star (U y)) x)
        (resolv38 η (fun y => star (U y)) x)
      simpa using this
    have h4 : A / (2 * η) ≤ A / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h5 : (A * B) ^ 0 = 1 := pow_zero _
    have h6 : A ^ 3 / (4 * η ^ 3) ≤ A ^ 3 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 1 ≤ η ^ 3 := one_le_pow₀ hη1
      have : 0 ≤ A ^ 3 := by positivity
      nlinarith
    have h7 : (Real.sqrt bracketSumE02_38 * B) ^ 3 / (4 * η ^ 3) = A ^ 3 / (4 * η ^ 3) := rfl
    have : ‖Γu x‖ ≤ A / 2 + A ^ 3 / 4 := by linarith
    exact this.trans (le_max_left _ _)
  -- sup bound of ΓK
  have hΓKsup : ∀ x, ‖ΓK x‖ ≤ b := by
    intro x
    have h1 := hasym x
    have h3 : ‖ΓK x‖ ≤ ‖ΓK x - ∑ m ∈ Finset.Icc 1 K,
        riccatiJetEvaluation U x (p m) * (-2 * (η : ℂ))⁻¹ ^ m‖ +
        ‖∑ m ∈ Finset.Icc 1 K, riccatiJetEvaluation U x (p m) * (-2 * (η : ℂ))⁻¹ ^ m‖ := by
      have := norm_add_le (ΓK x - ∑ m ∈ Finset.Icc 1 K,
        riccatiJetEvaluation U x (p m) * (-2 * (η : ℂ))⁻¹ ^ m)
        (∑ m ∈ Finset.Icc 1 K, riccatiJetEvaluation U x (p m) * (-2 * (η : ℂ))⁻¹ ^ m)
      simpa using this
    have hw : ‖(-2 * (η : ℂ))⁻¹‖ ≤ 1 := by
      rw [norm_inv, norm_mul]
      simp only [norm_neg, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hηpos]
      rw [inv_le_one₀ (by positivity)]
      linarith
    have h4 : ‖∑ m ∈ Finset.Icc 1 K, riccatiJetEvaluation U x (p m) * (-2 * (η : ℂ))⁻¹ ^ m‖ ≤
        Mb := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m _ => ?_))
      rw [norm_mul, norm_pow]
      calc ‖riccatiJetEvaluation U x (p m)‖ * ‖(-2 * (η : ℂ))⁻¹‖ ^ m
          ≤ bd (p m) * 1 := by
            refine mul_le_mul (hbd _ x) (pow_le_one₀ (norm_nonneg _) hw) (by positivity)
              (hbd0 _)
        _ = bd (p m) := mul_one _
    have h5 : CA * η⁻¹ ^ (K + 1) ≤ |CA| := by
      have : η⁻¹ ^ (K + 1) ≤ 1 := pow_le_one₀ (inv_nonneg.mpr hηpos.le) hη1'
      calc CA * η⁻¹ ^ (K + 1) ≤ |CA| * η⁻¹ ^ (K + 1) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |CA| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = |CA| := mul_one _
    have : ‖ΓK x‖ ≤ Mb + |CA| := by linarith
    exact this.trans (le_max_right _ _)
  have hΓeq : Γu = ΓK :=
    huniq η hηU' Γu ΓK hΓuc hΓKc hΓup hΓKp hΓud hΓKd hΓusup hΓKsup
  subst hΓeq
  have hexp := riccati_integral_expansion_Icc38 U hu K η CA A hηpos
    (fun x _ => hUb x) Γu hΓuc hasym
  have hre : (∫ x in (0:ℝ)..1, U x * Γu x).re =
      (Complex.I * (∫ x in (0:ℝ)..1, U x * Γu x)).im := by simp
  have hpair : (pair38 (planeReal N z) Γu).re = (∫ x in (0:ℝ)..1, U x * Γu x).re := rfl
  rw [hk, hpair, hre, sum_range_succ_eq_Icc38
    (fun m => (riccatiQuasiCoeff38 U m).im * η⁻¹ ^ m) (by simp [riccatiQuasiCoeff38_zero]),
    ← im_sum_coeff38 K (fun m => riccatiQuasiCoeff38 U m) η, ← Complex.sub_im]
  refine (Complex.abs_im_le_norm _).trans (hexp.trans (le_of_eq ?_))
  ring


/-! ## Coefficients -/

/-- the nonlinear part `n_η(U) = Im k(iη) - η - q_η` for the plane `U = planeReal N z` -/
def nonlinPart38 (N : ℕ) (z : FourierPlane N) (η : ℝ) : ℝ :=
  (actualQuasimomentumE02_38 (planeL2 N z) (Complex.I * η)).im - η -
    quadRiccati38 (planeL2 N z) η

/-- the coefficient of `η^{-m}` in the expansion of `q_η` -/
def quadCoeff38 (N : ℕ) (z : FourierPlane N) (m : ℕ) : ℝ :=
  if Even m then 0 else (-1:ℝ) ^ ((m - 1) / 2) / (2 * 4 ^ ((m - 1) / 2)) *
    ∑ i : Fin (2 * N + 1), (2 * Real.pi * (modeIndex N i : ℤ)) ^ (m - 1) * ‖z i‖ ^ 2

theorem sum_range_odd38 (g : ℕ → ℝ) (hg : ∀ j, g (2 * j) = 0) (k : ℕ) :
    ∑ m ∈ Finset.range (2 * k + 2), g m = ∑ j ∈ Finset.range (k + 1), g (2 * j + 1) := by
  induction k with
  | zero => simpa [Finset.sum_range_succ] using hg 0
  | succ k ih =>
    rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ _ (k + 1)]
    have := hg (k + 1)
    rw [show 2 * (k + 1) = 2 * k + 2 by ring] at this
    rw [this, add_zero]
    congr 2

theorem quadCoeff38_sum (N : ℕ) (z : FourierPlane N) (k : ℕ) (η : ℝ) :
    ∑ m ∈ Finset.range (2 * k + 2), quadCoeff38 N z m * η⁻¹ ^ m =
      ∑ j ∈ Finset.range (k + 1), (-1:ℝ) ^ j / (2 * 4 ^ j * η ^ (2 * j + 1)) *
        ∑ i : Fin (2 * N + 1), (2 * Real.pi * (modeIndex N i : ℤ)) ^ (2 * j) * ‖z i‖ ^ 2 := by
  rw [sum_range_odd38 (fun m => quadCoeff38 N z m * η⁻¹ ^ m) (fun j => by
    simp [quadCoeff38]) k]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have h1 : ¬ Even (2 * j + 1) := by simp [Nat.even_add_one]
  have h2 : (2 * j + 1 - 1) / 2 = j := by omega
  have h3 : 2 * j + 1 - 1 = 2 * j := by omega
  simp only [quadCoeff38]
  rw [if_neg h1, h2, h3, inv_pow]
  field_simp

theorem riccatiCoeff_im38 (N : ℕ) (z : FourierPlane N) (m : ℕ) :
    (riccatiQuasiCoeff38 (planeReal N z) m).im =
      if Even m then 0 else (-1:ℝ) ^ ((m - 1) / 2) / (2 * 4 ^ ((m - 1) / 2)) *
        localCharge38 (planeReal N z) ((m - 1) / 2) := by
  have hu : ContDiff ℝ ∞ (planeReal N z) := planeReal_smooth38 N z
  have hper : Function.Periodic (planeReal N z) 1 := planeReal_periodic N z
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' m
  · subst hj
    have : Even (2 * j) := ⟨j, by ring⟩
    rw [if_pos this]
    exact riccatiQuasiCoeff38_even_im _ hu hper j
  · subst hj
    have h1 : ¬ Even (2 * j + 1) := by simp [Nat.even_add_one]
    have h2 : (2 * j + 1 - 1) / 2 = j := by omega
    rw [if_neg h1, h2, riccatiQuasiCoeff38_odd, formalChargeIntegrand_integral_eq_re38 j _ hu hper]
    unfold localCharge38
    set Q : ℝ := (∫ x in (0 : ℝ)..1, riccatiJetEvaluation (planeReal N z) x
      (formalChargeIntegrand j)).re
    have : Complex.I * (-1 : ℂ) ^ j * ((2 : ℂ) ^ (2 * j + 1))⁻¹ * (Q : ℂ) =
        Complex.I * (((-1 : ℝ) ^ j / (2 * 4 ^ j) * Q : ℝ) : ℂ) := by
      push_cast
      rw [pow_succ, pow_mul]
      norm_num
      ring
    rw [this, Complex.I_mul_im, Complex.ofReal_re]

/-- identification of the expansion coefficients of the nonlinear part with the charges -/
theorem nonlin_coeff_ident38 (k : ℕ) (N : ℕ) (z : FourierPlane N) (c : ℕ → ℂ) (C η₀ : ℝ)
    (h : ∀ η ≥ η₀, |nonlinPart38 N z η - ∑ w ∈ Finset.Icc 3 (2*k+1), (c w).re * η⁻¹ ^ w| ≤
      C * η⁻¹ ^ (2*k+2)) :
    ∀ w ∈ Finset.Icc 3 (2*k+1), (c w).re =
      if Even w then 0 else (-1:ℝ)^((w-1)/2) / (2 * 4^((w-1)/2)) *
        (localCharge38 (planeReal N z) ((w-1)/2) -
          ∑ i : Fin (2*N+1), (2*Real.pi*(modeIndex N i : ℤ))^(w-1) * ‖z i‖^2) := by
  obtain ⟨η₁, C₁, hη₁, hT⟩ := riccati_true_expansion38 N z (2 * k + 1)
  obtain ⟨Cq, hCq0, hQ⟩ := quad_expansion38 k N z
  set a : ℕ → ℝ := fun w => if 3 ≤ w ∧ w ≤ 2 * k + 1 then (c w).re else 0 with ha
  set tgt : ℕ → ℝ := fun w => (riccatiQuasiCoeff38 (planeReal N z) w).im - quadCoeff38 N z w
    with htgt
  have htgt' : ∀ w, tgt w =
      if Even w then 0 else (-1:ℝ)^((w-1)/2) / (2 * 4^((w-1)/2)) *
        (localCharge38 (planeReal N z) ((w-1)/2) -
          ∑ i : Fin (2*N+1), (2*Real.pi*(modeIndex N i : ℤ))^(w-1) * ‖z i‖^2) := by
    intro w
    simp only [htgt, riccatiCoeff_im38, quadCoeff38]
    split_ifs <;> ring
  have hsa : ∀ η : ℝ, ∑ w ∈ Finset.range (2 * k + 1 + 1), a w * η⁻¹ ^ w =
      ∑ w ∈ Finset.Icc 3 (2 * k + 1), (c w).re * η⁻¹ ^ w := by
    intro η
    have : ∀ w, a w * η⁻¹ ^ w = if 3 ≤ w ∧ w ≤ 2 * k + 1 then (c w).re * η⁻¹ ^ w else 0 := by
      intro w; simp only [ha]; split_ifs <;> simp
    simp_rw [this]
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext w
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  have hmain := asymp_coeff_unique38 (2 * k + 1) (fun w => ((a w : ℝ) : ℂ))
    (fun w => ((tgt w : ℝ) : ℂ)) (C + C₁ + Cq) (max η₀ (max η₁ 1)) (fun η hη => by
      have hηη₀ : η₀ ≤ η := (le_max_left _ _).trans hη
      have hηη₁ : η₁ ≤ η := ((le_max_left _ _).trans (le_max_right _ _)).trans hη
      have hη1 : 1 ≤ η := ((le_max_right _ _).trans (le_max_right _ _)).trans hη
      have hηpos : 0 < η := by linarith
      have hreal : (∑ w ∈ Finset.range (2 * k + 1 + 1),
          (((a w : ℝ) : ℂ) - ((tgt w : ℝ) : ℂ)) * (η : ℂ)⁻¹ ^ w) =
          ((∑ w ∈ Finset.range (2 * k + 1 + 1), (a w - tgt w) * η⁻¹ ^ w : ℝ) : ℂ) := by
        push_cast; rfl
      rw [hreal, Complex.norm_real, Real.norm_eq_abs]
      have e1 := hT η hηη₁
      have e2 := hQ η hη1
      have e3 := h η hηη₀
      rw [← quadCoeff38_sum] at e2
      rw [← hsa η] at e3
      have hid : ∑ w ∈ Finset.range (2 * k + 1 + 1), (a w - tgt w) * η⁻¹ ^ w =
          (((actualQuasimomentumE02_38 (planeL2 N z) (Complex.I * η)).im - η) -
            ∑ m ∈ Finset.range (2 * k + 1 + 1),
              (riccatiQuasiCoeff38 (planeReal N z) m).im * η⁻¹ ^ m) -
          (quadRiccati38 (planeL2 N z) η -
            ∑ m ∈ Finset.range (2 * k + 2), quadCoeff38 N z m * η⁻¹ ^ m) -
          (nonlinPart38 N z η - ∑ w ∈ Finset.range (2 * k + 1 + 1), a w * η⁻¹ ^ w) := by
        simp only [nonlinPart38, htgt, sub_mul, Finset.sum_sub_distrib]
        ring
      rw [hid]
      set E1 := ((actualQuasimomentumE02_38 (planeL2 N z) (Complex.I * η)).im - η) -
            ∑ m ∈ Finset.range (2 * k + 1 + 1),
              (riccatiQuasiCoeff38 (planeReal N z) m).im * η⁻¹ ^ m with hE1
      set E2 := quadRiccati38 (planeL2 N z) η -
            ∑ m ∈ Finset.range (2 * k + 2), quadCoeff38 N z m * η⁻¹ ^ m with hE2
      set E3 := nonlinPart38 N z η - ∑ w ∈ Finset.range (2 * k + 1 + 1), a w * η⁻¹ ^ w
        with hE3
      have t1 := abs_sub (E1 - E2) E3
      have t2 := abs_sub E1 E2
      calc |E1 - E2 - E3| ≤ |E1| + |E2| + |E3| := by linarith
        _ ≤ C₁ * η⁻¹ ^ (2 * k + 2) + Cq * η⁻¹ ^ (2 * k + 2) + C * η⁻¹ ^ (2 * k + 2) := by
            linarith
        _ = (C + C₁ + Cq) * η⁻¹ ^ (2 * k + 2) := by ring)
  intro w hw
  have hw' := Finset.mem_Icc.mp hw
  have := hmain w hw'.2
  rw [← htgt' w]
  have h3 : a w = (c w).re := by simp only [ha]; rw [if_pos ⟨hw'.1, hw'.2⟩]
  have h4 : ((a w : ℝ) : ℂ) = ((tgt w : ℝ) : ℂ) := this
  rw [← h3]
  exact_mod_cast h4

end NlsGge.SpectralFoundations

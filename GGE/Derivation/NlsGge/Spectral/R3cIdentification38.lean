import NlsGge.Spectral.R3cResolventCore38
import NlsGge.Spectral.R3cUniformRiccati38
import NlsGge.Spectral.R3cPlaneSobolev38
import NlsGge.Spectral.ActualQuasimomentumImaginaryAxisRiccatiE02_38
import NlsGge.Spectral.ActualQuasimomentumUniformExteriorE02_38
import NlsGge.Hierarchy.PlaneCoverIdentification38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core

/-! # R3c piece P4a: identification `Im (k(iη) - iη) = Re ⟪U, Γ⟫` with the uniform Riccati solution

For a Fourier plane `z` in an `H¹` ball of radius `B`, and `η ≥ η₀(B)`, the uniform Riccati solution
`Γ` of piece P2 (with `A = A₀ = √κ B`, by piece P3) satisfies
`Im (k(iη) - iη) = Re ∫₀¹ U Γ`. -/

theorem r3c_pair_bound_aux38 {η A : ℝ} (_hη : 0 < η) (hA0 : 0 ≤ A) {U Γ : ℝ → ℂ}
    (hUb : ∀ x, ‖U x‖ ≤ A) (hΓb : ∀ x, ‖Γ x‖ ≤ A / (2 * η) + A ^ 3 / (4 * η ^ 3)) :
    ‖pair38 U Γ‖ ≤ A * (A / (2 * η) + A ^ 3 / (4 * η ^ 3)) := by
  unfold pair38
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (f := fun x => U x * Γ x)
    (C := A * (A / (2 * η) + A ^ 3 / (4 * η ^ 3))) (fun x _ => by
      rw [norm_mul]
      exact mul_le_mul (hUb x) (hΓb x) (norm_nonneg _) hA0)
  simpa using h

theorem r3c_small_aux38 {η A : ℝ} (_hA0 : 0 ≤ A) (hη : 2 * A ^ 2 + 1 ≤ η) :
    A * (A / (2 * η) + A ^ 3 / (4 * η ^ 3)) < 1 := by
  have hη1 : 1 ≤ η := by nlinarith [sq_nonneg A]
  have hηpos : 0 < η := by linarith
  have h1 : A * (A / (2 * η)) ≤ 1 / 4 := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have h2 : A * (A ^ 3 / (4 * η ^ 3)) ≤ 1 / 16 := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    have hA2 : A ^ 2 ≤ η / 2 := by linarith
    have hA4 : A ^ 4 ≤ η ^ 2 / 4 := by nlinarith [sq_nonneg A]
    have hη3 : η ^ 2 ≤ η ^ 3 := by nlinarith [sq_nonneg η]
    nlinarith
  rw [mul_add]
  linarith

theorem r3c_im_eq_pair38 (B : ℝ) (hB : 0 ≤ B) : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ (N : ℕ) (z : FourierPlane N),
    ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 * ‖z i‖ ^ 2 ≤ B ^ 2 →
    ∀ η : ℝ, η₀ ≤ η → ∃ Γ : ℝ → ℂ, Continuous Γ ∧ Function.Periodic Γ 1 ∧
      (∀ x, HasDerivAt Γ (-(2*η) * Γ x + star (planeReal N z x) -
          planeReal N z x * Γ x ^ 2) x) ∧
      (∀ x, ‖Γ x - resolv38 η (fun y => star (planeReal N z y)) x‖ ≤
          (Real.sqrt bracketSumE02_38 * B) ^ 3 / (4 * η ^ 3)) ∧
      (actualQuasimomentumE02_38 (planeL2 N z) (Complex.I * η)).im - η =
        (pair38 (planeReal N z) Γ).re := by
  classical
  set A : ℝ := Real.sqrt bracketSumE02_38 * B with hAdef
  have hA0 : 0 ≤ A := mul_nonneg (Real.sqrt_nonneg _) hB
  obtain ⟨X, hX, hext⟩ := actualQuasimomentum_uniformExterior_E02_38 (max B 1) (le_max_right _ _)
  refine ⟨4 * A + X + 2 * A ^ 2 + 2, by positivity, ?_⟩
  intro N z hS η hη
  have hηA : max (4 * A) 1 ≤ η := max_le (by nlinarith [sq_nonneg A]) (by nlinarith [sq_nonneg A])
  have hη1 : 1 < η := by nlinarith [sq_nonneg A]
  have hηpos : 0 < η := by linarith
  have hηX : X ≤ η := by nlinarith [sq_nonneg A]
  have hηS : 2 * A ^ 2 + 1 ≤ η := by nlinarith [sq_nonneg A]
  -- the plane
  set U : ℝ → ℂ := planeReal N z with hUdef
  have hUc : Continuous U := (planeReal_smooth38 N z).continuous
  have hUp : Function.Periodic U 1 := planeReal_periodic N z
  have hUb : ∀ x, ‖U x‖ ≤ A := by
    intro x
    refine (plane_sup_le_r3c N z x).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    calc Real.sqrt (∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 * ‖z i‖ ^ 2)
        ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt hS
      _ = B := Real.sqrt_sq hB
  obtain ⟨Γ, hΓc, hΓp, hΓd, hΓb⟩ := riccati_exists_uniform38 (η := η) (A := A) U hUc hUp hA0 hUb hηA
  refine ⟨Γ, hΓc, hΓp, hΓd, hΓb, ?_⟩
  -- sup bound of Γ
  have hUbar : Continuous (fun y => star (U y)) := hUc.star
  have hRb : ∀ x, ‖resolv38 η (fun y => star (U y)) x‖ ≤ A / (2 * η) :=
    fun x => resolv38_bound hηpos hUbar (fun y => by simpa using hUb y) x
  have hΓsup : ∀ x, ‖Γ x‖ ≤ A / (2 * η) + A ^ 3 / (4 * η ^ 3) := by
    intro x
    have h1 := hΓb x
    have h2 := hRb x
    have h3 : ‖Γ x‖ ≤ ‖Γ x - resolv38 η (fun y => star (U y)) x‖ +
        ‖resolv38 η (fun y => star (U y)) x‖ := by
      have := norm_add_le (Γ x - resolv38 η (fun y => star (U y)) x)
        (resolv38 η (fun y => star (U y)) x)
      simpa using this
    linarith
  have hsmall : ‖∫ x in (0:ℝ)..1, U x * Γ x‖ < 1 :=
    lt_of_le_of_lt (r3c_pair_bound_aux38 hηpos hA0 hUb hΓsup) (r3c_small_aux38 hA0 hηS)
  -- the H¹ hypothesis
  have hfour : physicalFourier (planeL2 N z) = physicalFourier (planeField N z) :=
    funext (physicalFourier_planeL2 N z)
  have hu : SobolevSquareSummable 1 (physicalFourier (planeL2 N z)) := by
    rw [hfour]; exact sobolevSquareSummable_planeField N z 1
  have hnorm : ‖physicalSobolevL2 1 (planeL2 N z) hu‖ ≤ max B 1 := by
    have hsq := plane_h1_norm_sq_r3c N z hu
    have hB1 : B ^ 2 ≤ (max B 1) ^ 2 :=
      pow_le_pow_left₀ hB (le_max_left _ _) 2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (le_trans hB (le_max_left _ _))
      two_ne_zero).1 (by rw [hsq]; exact hS.trans hB1)
  have hk : ‖actualQuasimomentumE02_38 (planeL2 N z) (Complex.I * η) - Complex.I * η‖ < 1 := by
    have hzim : 0 < (Complex.I * (η:ℂ)).im := by simpa using hηpos
    have hzn : X ≤ ‖Complex.I * (η:ℂ)‖ := by
      rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hηpos, one_mul]
      exact hηX
    have := hext (planeL2 N z) hu hnorm (Complex.I * η) hzim hzn
    linarith
  have hΓ1 : Γ 1 = Γ 0 := by simpa using hΓp 0
  have hS2 := actualQuasimomentum_imaginaryAxis_riccati_E02_38 (planeL2 N z) U hUc
    (planeReal_cover_ae38 N z) η hη1 Γ hΓc hΓ1 (fun x => by
      have h := hΓd x
      rwa [show -(2 * η) * Γ x = -2 * η * Γ x by ring] at h) hsmall hk
  have hJ : (pair38 U Γ) = ∫ x in (0:ℝ)..1, U x * Γ x := rfl
  rw [hS2, hJ]
  simp


end NlsGge.SpectralFoundations

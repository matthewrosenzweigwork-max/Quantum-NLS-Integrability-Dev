import NlsGge.Spectral.ActualActionSumE02_38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology Interval
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core

/-! # R3c piece P3: plane Sobolev bounds (campaign 38)

With `S j := ∑ i, (1 + (modeIndex N i)^2)^j * ‖z i‖^2`: sup bounds of `U` and `U'` by `S 1` and `S 2`,
`L²` bounds of iterated plane derivatives, monotonicity of `S j` and the identification of `S 1` with
the squared `H¹` norm. The `L²` squared norm `l2sq38` of piece P1a is written out as an integral. -/

/-- Cauchy-Schwarz: `(∑ ‖z i‖)² ≤ K * S 1`. -/
theorem plane_sum_norm_sq_le_r3c (N : ℕ) (z : FourierPlane N) :
    (∑ i, ‖z i‖) ^ 2 ≤ bracketSumE02_38 *
      ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 * ‖z i‖ ^ 2 := by
  set c : Fin (2 * N + 1) → ℝ := fun i => 1 + ((modeIndex N i : ℤ) : ℝ) ^ 2 with hcdef
  have hc : ∀ i, 0 < c i := fun i => by positivity
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin (2 * N + 1) => 1 / Real.sqrt (c i)) (fun i => Real.sqrt (c i) * ‖z i‖)
  have hprod : ∀ i : Fin (2 * N + 1),
      1 / Real.sqrt (c i) * (Real.sqrt (c i) * ‖z i‖) = ‖z i‖ := by
    intro i
    have : 0 < Real.sqrt (c i) := Real.sqrt_pos.mpr (hc i)
    field_simp
  have hsq1 : ∀ i : Fin (2 * N + 1), (1 / Real.sqrt (c i)) ^ 2 =
      Real.rpow (japaneseBracket (modeIndex N i)) (-2) := by
    intro i
    rw [rpow_bracket_neg_two_E02_38, div_pow, Real.sq_sqrt (hc i).le, one_pow]
  have hsq2 : ∀ i : Fin (2 * N + 1), (Real.sqrt (c i) * ‖z i‖) ^ 2 =
      (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 * ‖z i‖ ^ 2 := by
    intro i
    rw [mul_pow, Real.sq_sqrt (hc i).le, pow_one]
  simp only [hprod, hsq1, hsq2] at hcs
  have hKs : Summable (fun n : ℤ => Real.rpow (japaneseBracket n) (-2)) :=
    NlsGge.Measure.summable_japaneseBracket_rpow_neg 2 (by norm_num)
  have hK1 := plane_sum_le_tsum_E02_38 N _
    (fun n => Real.rpow_nonneg (japaneseBracket_pos n).le _) hKs
  have hS0 : 0 ≤ ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 * ‖z i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => by positivity
  exact hcs.trans (mul_le_mul_of_nonneg_right hK1 hS0)

theorem plane_sup_le_r3c (N : ℕ) (z : FourierPlane N) (x : ℝ) :
    ‖planeReal N z x‖ ≤ Real.sqrt bracketSumE02_38 *
      Real.sqrt (∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 * ‖z i‖ ^ 2) := by
  have hK0 : 0 ≤ bracketSumE02_38 :=
    tsum_nonneg fun n => Real.rpow_nonneg (japaneseBracket_pos n).le _
  rw [← Real.sqrt_mul hK0]
  exact (norm_planeReal_le38 N z x).trans
    (Real.le_sqrt_of_sq_le (plane_sum_norm_sq_le_r3c N z))

/-- Squared Sobolev weights of the derivative plane. -/
theorem derivativePlane_S1_le_r3c (N : ℕ) (z : FourierPlane N) :
    ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 * ‖derivativePlane N z i‖ ^ 2 ≤
      (2 * Real.pi) ^ 2 *
        ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 2 * ‖z i‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hn : ‖derivativePlane N z i‖ ^ 2 =
      (2 * Real.pi) ^ 2 * ((modeIndex N i : ℤ) : ℝ) ^ 2 * ‖z i‖ ^ 2 := by
    simp only [derivativePlane, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_intCast]
    rw [mul_pow, mul_pow, mul_pow, sq_abs]
    ring
  rw [hn]
  have hm : 0 ≤ ((modeIndex N i : ℤ) : ℝ) ^ 2 := sq_nonneg _
  have hz : 0 ≤ ‖z i‖ ^ 2 := sq_nonneg _
  have hp : 0 ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
  have h1 : ((modeIndex N i : ℤ) : ℝ) ^ 2 ≤ 1 + ((modeIndex N i : ℤ) : ℝ) ^ 2 := by linarith
  have h2 : (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 *
      (((modeIndex N i : ℤ) : ℝ) ^ 2) ≤ (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 2 := by
    rw [pow_one]
    nlinarith [hm]
  calc (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 *
        ((2 * Real.pi) ^ 2 * ((modeIndex N i : ℤ) : ℝ) ^ 2 * ‖z i‖ ^ 2)
      = (2 * Real.pi) ^ 2 * ((1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 *
          ((modeIndex N i : ℤ) : ℝ) ^ 2) * ‖z i‖ ^ 2 := by ring
    _ ≤ (2 * Real.pi) ^ 2 * (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 2 * ‖z i‖ ^ 2 := by
        gcongr
    _ = _ := by ring

theorem plane_deriv_sup_le_r3c (N : ℕ) (z : FourierPlane N) (x : ℝ) :
    ‖planeReal N (derivativePlane N z) x‖ ≤ 2 * Real.pi * Real.sqrt bracketSumE02_38 *
      Real.sqrt (∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 2 * ‖z i‖ ^ 2) := by
  refine (plane_sup_le_r3c N (derivativePlane N z) x).trans ?_
  have h := Real.sqrt_le_sqrt (derivativePlane_S1_le_r3c N z)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)] at h
  have hK : 0 ≤ Real.sqrt bracketSumE02_38 := Real.sqrt_nonneg _
  calc Real.sqrt bracketSumE02_38 * _ ≤ Real.sqrt bracketSumE02_38 * _ :=
        mul_le_mul_of_nonneg_left h hK
    _ = _ := by ring

/-- Coordinates of iterated derivatives. -/
theorem iterate_derivativePlane_apply_r3c (N : ℕ) (z : FourierPlane N) (j : ℕ)
    (i : Fin (2 * N + 1)) :
    ((derivativePlane N)^[j] z) i =
      z i * (2 * (Real.pi : ℂ) * Complex.I * ((modeIndex N i : ℤ) : ℂ)) ^ j := by
  induction j generalizing z with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [derivativePlane]
    ring

theorem plane_l2_le_r3c (N : ℕ) (z : FourierPlane N) (j : ℕ) :
    ∫ x in (0:ℝ)..1, ‖planeReal N ((derivativePlane N)^[j] z) x‖ ^ 2 ≤
      (2 * Real.pi) ^ (2 * j) *
        ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ j * ‖z i‖ ^ 2 := by
  rw [planeReal_integral_norm_sq38, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [iterate_derivativePlane_apply_r3c]
  have hn : ‖z i * (2 * (Real.pi : ℂ) * Complex.I * ((modeIndex N i : ℤ) : ℂ)) ^ j‖ ^ 2 =
      ‖z i‖ ^ 2 * ((2 * Real.pi) ^ 2 * ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ j := by
    rw [norm_mul, norm_pow, mul_pow, ← pow_mul, mul_comm j 2, pow_mul]
    congr 2
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_intCast]
    rw [mul_pow, mul_pow, sq_abs]
  rw [hn]
  have h1 : ((modeIndex N i : ℤ) : ℝ) ^ 2 ≤ 1 + ((modeIndex N i : ℤ) : ℝ) ^ 2 := by
    have := sq_nonneg ((modeIndex N i : ℤ) : ℝ); linarith
  have h2 : ((2 * Real.pi) ^ 2 * ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ j ≤
      (2 * Real.pi) ^ (2 * j) * (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ j := by
    rw [mul_pow, ← pow_mul]
    gcongr
  calc ‖z i‖ ^ 2 * ((2 * Real.pi) ^ 2 * ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ j
      ≤ ‖z i‖ ^ 2 * ((2 * Real.pi) ^ (2 * j) * (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ j) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = _ := by ring

theorem plane_S_mono_r3c (N : ℕ) (z : FourierPlane N) {j k : ℕ} (hjk : j ≤ k) :
    ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ j * ‖z i‖ ^ 2 ≤
      ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ k * ‖z i‖ ^ 2 := by
  refine Finset.sum_le_sum fun i _ => ?_
  have hb : 1 ≤ 1 + ((modeIndex N i : ℤ) : ℝ) ^ 2 := by
    have := sq_nonneg ((modeIndex N i : ℤ) : ℝ); linarith
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb hjk) (sq_nonneg _)

theorem plane_h1_norm_sq_r3c (N : ℕ) (z : FourierPlane N)
    (h : SobolevSquareSummable 1 (physicalFourier (planeL2 N z))) :
    ‖physicalSobolevL2 1 (planeL2 N z) h‖ ^ 2 =
      ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) ^ 1 * ‖z i‖ ^ 2 := by
  classical
  rw [physicalSobolevL2_norm_sq]
  have hz : ∀ n : ℤ, n ∉ Finset.univ.image (modeIndex N) →
      Real.rpow (japaneseBracket n) (2 * 1) * ‖physicalFourier (planeL2 N z) n‖ ^ 2 = 0 := by
    intro n hn
    have hout : n < -(N : ℤ) ∨ (N : ℤ) < n := by
      by_contra hh
      have hb : -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ) := by omega
      obtain ⟨i, hi⟩ := modeIndex_covers N n hb.1 hb.2
      exact hn (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩)
    rw [physicalFourier_planeL2, physicalFourier_planeField_outside N z n hout]
    simp
  rw [tsum_eq_sum hz, Finset.sum_image (fun a _ b _ hab => modeIndex_injective N hab)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rpow_bracket_two_E02_38, physicalFourier_planeL2, physicalFourier_planeField, pow_one]

end NlsGge.SpectralFoundations

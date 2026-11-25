import NlsGge.Spectral.PlaneMomentInequality38V1
import NlsGge.Spectral.ReservedCoercivityAbstract38V1
import NlsGge.Schur.ActualSchurBallMap38V1

/-!
# NEW-F06 (F:lem:coercivity): superpolynomial coercivity of the reserved energy

`E_B(u) = Σ_{j≥0} β_{j+1} Q_{2j}(u)` (v2 F:eq:B, `β_j = c_j/(j!)^4`) on every Fourier plane.
For `‖u‖_{H¹} ≥ R ≥ R₀`: `E_B(u) ≥ g exp(g R^{1/4})`, with `g, R₀` depending only on `c_±`.
-/

set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Schur

namespace NlsGge.HierarchyRiccati.Core

/-- v2 F:eq:B: the reserved energy `E_B = Σ_{j≥0} β_{j+1} Q_{2j}` on the plane. -/
def reservedEnergy38 {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ)
    (z : FourierPlane N) : ℝ :=
  ∑' j : ℕ, NlsGge.coefficient c.val (j + 1) * localCharge38 (planeReal N z) j

theorem coefficient_nonneg38 {lo up : ℝ} (c : BoundedCoefficients lo up) (j : ℕ) :
    0 ≤ NlsGge.coefficient c.val j := by
  unfold NlsGge.coefficient
  have := lt_of_lt_of_le c.property.1 (c.property.2.2 j).1
  positivity

/-- The reserved series converges on every plane (majorant `β_{j+1} ≤ (c₊/c₋) β_j`). -/
theorem reservedEnergy38_summable {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ)
    (z : FourierPlane N) :
    Summable fun j : ℕ => NlsGge.coefficient c.val (j + 1) * localCharge38 (planeReal N z) j := by
  have hl : 0 < lo := c.property.1
  have hb : ∀ j, lo ≤ c.val j := fun j => (c.property.2.2 j).1
  have hu : ∀ j, c.val j ≤ up := fun j => (c.property.2.2 j).2
  refine Summable.of_nonneg_of_le
    (fun j => mul_nonneg (coefficient_nonneg38 c _) (localCharge38_plane_nonneg N z j))
    (fun j => ?_) ((fullEnergy38_summable c N z).mul_left (up / lo))
  have hQ := localCharge38_plane_nonneg N z j
  calc NlsGge.coefficient c.val (j + 1) * localCharge38 (planeReal N z) j
      ≤ (up / lo * NlsGge.coefficient c.val j) * localCharge38 (planeReal N z) j :=
        mul_le_mul_of_nonneg_right
          (NlsGge.Weights.coefficient_succ_le38 lo up c.val hl hb hu j) hQ
    _ = up / lo * (c.val j / ((j.factorial : ℝ)) ^ 4 * localCharge38 (planeReal N z) j) := by
        unfold NlsGge.coefficient; ring

theorem reservedEnergy38_nonneg {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ)
    (z : FourierPlane N) : 0 ≤ reservedEnergy38 c N z :=
  tsum_nonneg fun j => mul_nonneg (coefficient_nonneg38 c _) (localCharge38_plane_nonneg N z j)

/-- NEW-F06.04: `‖u‖_{H¹} ≥ R ≥ 1` forces `Q₂ ≥ R²/4` (mass/derivative split of v2). -/
theorem planeQ2_ge_H1_sq38 (N : ℕ) (z : FourierPlane N) (R : ℝ) (hR : 1 ≤ R)
    (hz : R ≤ planeH1Norm38 N z) :
    R ^ 2 / 4 ≤ localCharge38 (planeReal N z) 1 := by
  set M := ∑ i : Fin (2 * N + 1), ‖z i‖ ^ 2 with hM
  set D := ∑ i : Fin (2 * N + 1), (modeIndex N i : ℝ) ^ 2 * ‖z i‖ ^ 2 with hD
  have hnorm : R ^ 2 ≤ M + D := by
    have h1 : R ^ 2 ≤ planeH1Norm38 N z ^ 2 := pow_le_pow_left₀ (by linarith) hz 2
    have h2 := planeH1Embedding38_norm_sq N z
    have h3 : ∑ i : Fin (2 * N + 1), (1 + (modeIndex N i : ℝ) ^ 2) * ‖z i‖ ^ 2 = M + D := by
      rw [hM, hD, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    unfold planeH1Norm38 at h1
    linarith
  have hMeq : localCharge38 (planeReal N z) 0 = M := localCharge38_zero_plane N z
  have hHM : M ^ 2 ≤ localCharge38 (planeReal N z) 1 := hMeq ▸ planeQ2_ge_mass_sq38 N z
  -- the derivative part
  have hDeriv : (2 * Real.pi) ^ 2 * D ≤ localCharge38 (planeReal N z) 1 := by
    have hc := continuous_planeReal38 N z
    have hcd := continuous_planeReal38 N (derivativePlane N z)
    have hDint : ∫ x in (0:ℝ)..1, ‖planeReal N (derivativePlane N z) x‖ ^ 2 =
        (2 * Real.pi) ^ 2 * D := by
      rw [← planeQ0_local38, localCharge38_zero_plane, hD, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [derivativePlane, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Complex.norm_I, Complex.norm_intCast, Real.norm_eq_abs]
      rw [abs_of_pos Real.pi_pos]
      rw [mul_pow, mul_pow, mul_pow, sq_abs]
      ring
    rw [planeQ2_local38, ← hDint]
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact ((continuous_norm.comp hcd).pow 2).intervalIntegrable _ _
    · exact (((continuous_norm.comp hcd).pow 2).add
        ((continuous_norm.comp hc).pow 4)).intervalIntegrable _ _
    · intro x _
      have : 0 ≤ ‖planeReal N z x‖ ^ 4 := by positivity
      linarith
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun i _ => by positivity
  have hpi : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by
    have := Real.pi_gt_three; nlinarith
  by_cases hcase : R ^ 2 / 2 ≤ M
  · have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
    have : (R ^ 2 / 2) ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (by positivity) hcase 2
    nlinarith
  · have : R ^ 2 / 2 ≤ D := by linarith
    nlinarith

/-- **NEW-F06, F:lem:coercivity.**  There are `g > 0` and `R₀ ≥ 1`, depending only on the
coefficient bounds `lo, up`, such that for every admitted `c`, every cutoff `N`, every plane
point `z` (a Fourier polynomial) and every `R` with `R₀ ≤ R ≤ ‖z‖_{H¹}`,
`E_B(z) ≥ g exp(g R^{1/4})`. -/
theorem reservedEnergy_coercive38 (lo up : ℝ) (hl : 0 < lo) (hlu : lo ≤ up) :
    ∃ g R₀ : ℝ, 0 < g ∧ 1 ≤ R₀ ∧
      ∀ (c : BoundedCoefficients lo up) (N : ℕ) (z : FourierPlane N) (R : ℝ),
        R₀ ≤ R → R ≤ planeH1Norm38 N z →
        g * Real.exp (g * R ^ (1 / 4 : ℝ)) ≤ reservedEnergy38 c N z := by
  obtain ⟨g, R₀, hg, hR₀, h⟩ :=
    NlsGge.Weights.reservedCoercivityAbstract38 lo up hl hlu (1 / 4) (by norm_num)
  refine ⟨g, R₀, hg, hR₀, fun c N z R hR hz => ?_⟩
  have hR1 : 1 ≤ R := hR₀.trans hR
  have hH : 1 / 4 * R ^ 2 ≤ localCharge38 (planeReal N z) 1 := by
    have := planeQ2_ge_H1_sq38 N z R hR1 hz; linarith
  exact h c.val (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2) R _ hR hH
    (fun j => localCharge38 (planeReal N z) j) (fun j => localCharge38_plane_nonneg N z j)
    (fun j hj => planeMoment_sqrt38 N z j hj) (reservedEnergy38_summable c N z)

end NlsGge.HierarchyRiccati.Core

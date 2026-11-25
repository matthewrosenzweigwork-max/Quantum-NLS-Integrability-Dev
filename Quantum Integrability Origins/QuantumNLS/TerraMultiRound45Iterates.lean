import QuantumNLS.TerraMultiRound44Picard

/-! All-order Picard truncation bounds for the physical Riccati branch.
This is a partial result toward REG-007, not the scalar expansion. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound45Iterates
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.TerraMultiRound38SignedPicard QuantumNLS.TerraMultiRound39PhysicalBall
open QuantumNLS.TerraMultiRound44Picard

/-- Iteration starts at the free resolvent. -/
def iterate {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (hY : 0 < |Y|)
    (κ : ℝ) (u : Ell2) : ℕ → Ell2
  | 0 => signedCLM L Y hY u
  | n + 1 => physicalT hL ha hY κ u (iterate hL ha hY κ u n)

/-- Every iterate stays in the explicit larger ball when the spectral
parameter satisfies the existing contraction threshold. -/
theorem iterate_ball {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u : Ell2)
    (hsmall : 16 * |κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 ≤ |Y| ^ 2) :
    ∀ n : ℕ, ‖iterate hL ha hY κ u n‖ ≤ 4 * ‖u‖ / |Y| := by
  have e4 : 4 * ‖u‖ / |Y| = 4 * (‖u‖ / |Y|) := by ring
  have hradius : 0 ≤ 4 * ‖u‖ / |Y| := by positivity
  have hfree : ‖signedCLM L Y hY u‖ ≤ ‖u‖ / |Y| := by
    simpa [div_eq_mul_inv, mul_comm] using norm_signedCLM_le L Y hY u
  have hq := signed_contract_const_le hY (κ / L) ‖u‖ hsmall
  have hq' : 8 * |κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 / |Y| ^ 2 ≤ 1 / 2 := by
    have he : (|κ / L| * |Y|⁻¹ * Cmul L a ^ 2 * ‖u‖) *
        (2 * (4 * ‖u‖ / |Y|)) =
        8 * |κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 / |Y| ^ 2 := by
      field_simp
      <;> ring
    rw [← he]
    exact hq
  intro n
  induction n with
  | zero =>
      simpa [iterate] using hfree.trans (by rw [e4]; nlinarith [div_nonneg (norm_nonneg u) hY.le])
  | succ n ih =>
      have h := signed_lipschitz hL ha hY (κ / L) ‖u‖ u (jEll u)
        (iterate hL ha hY κ u n) 0 (by rw [norm_jEll]) ih (by simpa using hradius)
      change ‖physicalT hL ha hY κ u (iterate hL ha hY κ u n) -
        physicalT hL ha hY κ u 0‖ ≤ _ at h
      have h0 : physicalT hL ha hY κ u 0 = signedCLM L Y hY u := by
        exact signedT_zero hL ha hY (κ / L) u (jEll u)
      rw [h0, sub_zero] at h
      have hhalf : ‖physicalT hL ha hY κ u (iterate hL ha hY κ u n) -
          signedCLM L Y hY u‖ ≤ (1 / 2) * ‖iterate hL ha hY κ u n‖ :=
        h.trans (mul_le_mul_of_nonneg_right hq' (norm_nonneg _))
      have htri : ‖physicalT hL ha hY κ u (iterate hL ha hY κ u n)‖ ≤
          ‖physicalT hL ha hY κ u (iterate hL ha hY κ u n) - signedCLM L Y hY u‖ +
          ‖signedCLM L Y hY u‖ := by
        calc
          _ = ‖(physicalT hL ha hY κ u (iterate hL ha hY κ u n) - signedCLM L Y hY u) +
              signedCLM L Y hY u‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      change ‖physicalT hL ha hY κ u (iterate hL ha hY κ u n)‖ ≤ _
      rw [e4] at ih ⊢
      nlinarith [div_nonneg (norm_nonneg u) hY.le]

/-- After n nonlinear Picard steps, the small fixed point has a cubic
initial error multiplied by n factors of the quadratic contraction rate. -/
theorem iterate_error {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u r : Ell2)
    (hsmall : 16 * |κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 ≤ |Y| ^ 2)
    (hr : physicalT hL ha hY κ u r = r)
    (hn : ‖r‖ ≤ 2 * ‖u‖ / |Y|) :
    ∀ n : ℕ, ‖r - iterate hL ha hY κ u n‖ ≤
      (8 * |κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 / |Y| ^ 2) ^ n *
      ((4 * |κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 3) * |Y|⁻¹ ^ 3) := by
  have hR : ‖r‖ ≤ 4 * ‖u‖ / |Y| := by
    have hnonneg : 0 ≤ ‖u‖ / |Y| := by positivity
    have e2 : 2 * ‖u‖ / |Y| = 2 * (‖u‖ / |Y|) := by ring
    have e4 : 4 * ‖u‖ / |Y| = 4 * (‖u‖ / |Y|) := by ring
    rw [e2] at hn
    rw [e4]
    linarith
  have hq : 0 ≤ 8 * |κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 / |Y| ^ 2 := by positivity
  intro n
  induction n with
  | zero => simpa [iterate] using nonlinear_cubic_bound hL ha hY κ u r hr hn
  | succ n ih =>
      have h := signed_lipschitz hL ha hY (κ / L) ‖u‖ u (jEll u)
        r (iterate hL ha hY κ u n) (by rw [norm_jEll]) hR
        (iterate_ball hL ha hY κ u hsmall n)
      change ‖physicalT hL ha hY κ u r -
        physicalT hL ha hY κ u (iterate hL ha hY κ u n)‖ ≤ _ at h
      rw [hr] at h
      change ‖r - physicalT hL ha hY κ u (iterate hL ha hY κ u n)‖ ≤ _
      calc
        _ ≤ (8 * |κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 / |Y| ^ 2) *
            ‖r - iterate hL ha hY κ u n‖ := h
        _ ≤ (8 * |κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 / |Y| ^ 2) *
            ((8 * |κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 / |Y| ^ 2) ^ n *
            ((4 * |κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 3) * |Y|⁻¹ ^ 3)) :=
          mul_le_mul_of_nonneg_left ih hq
        _ = _ := by rw [pow_succ]; ring

#print axioms iterate_ball
#print axioms iterate_error
end QuantumNLS.TerraMultiRound45Iterates

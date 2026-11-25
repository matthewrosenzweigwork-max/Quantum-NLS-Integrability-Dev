import QuantumNLS.Interpolation
/-!
Trusted statement for PROP-015 `Q7A:lem:interp`, written by the integrator (not the prover) directly from
`source/chapters/propagation/window_reconstruction.tex:57–65` (sha256 a7259e38…3799819).
The Lagrange basis is defined here independently by its textbook product, not by the prover's `lagrangeValue`.
-/
open Finset

/-- ℓ_j(z) for nodes z_0,…,z_m (independent spec definition). -/
noncomputable def specLagrange {m : ℕ} (zs : Fin (m + 1) → ℂ) (j : Fin (m + 1)) (z : ℂ) : ℂ :=
  ∏ k ∈ univ.erase j, (z - zs k) / (zs j - zs k)

/-- Printed remainder (right side of eq. Q7A:eq:interp). -/
noncomputable def specRHS {m : ℕ} (zs : Fin (m + 1) → ℂ) (q z : ℂ) : ℂ :=
  (-1 : ℂ) ^ (m + 1) * (∏ j, (z - zs j)) / ((z - q) * ∏ j, (zs j - q))

/-- Clause 1 (identity): distinct nodes; q different from the nodes and from z. -/
def Prop015Identity : Prop :=
  ∀ (m : ℕ) (zs : Fin (m + 1) → ℂ), Function.Injective zs → ∀ q z : ℂ,
    (∀ j, zs j ≠ q) → z ≠ q →
    1 / (z - q) - ∑ j, specLagrange zs j z / (zs j - q) = specRHS zs q z

/-- Clause 2 (printed existential form): for fixed m,H,H₁ there is C_{m,H,H₁} such that for all
sufficiently large R, real a ≥ 2R, |z-a| ≤ H, |z_j-a| ≤ H₁, |q| ≤ R give |RHS| ≤ C R^{-m-2}. -/
def Prop015Bound : Prop :=
  ∀ (m : ℕ) (H H1 : ℝ), ∃ C R0 : ℝ, ∀ R : ℝ, R0 ≤ R →
    ∀ (a : ℝ) (zs : Fin (m + 1) → ℂ) (q z : ℂ),
      2 * R ≤ a → ‖z - (a : ℂ)‖ ≤ H → (∀ j, ‖zs j - (a : ℂ)‖ ≤ H1) → ‖q‖ ≤ R →
      ‖specRHS zs q z‖ ≤ C * (R ^ (m + 2))⁻¹

theorem prop015_identity : Prop015Identity := by
  intro m zs hz q z hq hzq
  have h := QuantumNLS.Interpolation.cauchy_remainder zs hz q z hq hzq
  simpa [specLagrange, specRHS, QuantumNLS.Interpolation.lagrangeValue_eq_prod] using h

theorem prop015_bound : Prop015Bound := by
  intro m H H1
  refine ⟨2 ^ (m + 2) * (H + H1) ^ (m + 1), max 1 (max (2 * H) (2 * H1)), ?_⟩
  intro R hR a zs q z ha hza hzsa hq
  have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
  have hH : 2 * H ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
  have hH1 : 2 * H1 ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR
  have ha' : 2 * R ≤ ‖(a : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact le_trans ha (le_abs_self a)
  have h := QuantumNLS.Interpolation.cauchy_remainder_bound zs q z (a : ℂ) R H H1 hRpos hH hH1
    hza hzsa hq ha'
  simpa [specRHS, div_eq_mul_inv] using h

#print axioms prop015_identity
#print axioms prop015_bound
set_option pp.explicit true in
#check @QuantumNLS.Interpolation.cauchy_remainder

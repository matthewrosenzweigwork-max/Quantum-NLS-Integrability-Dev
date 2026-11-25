import Mathlib
import QuantumNLS.Local002Rank
import QuantumNLS.Local002SA
import QuantumNLS.Local002Analytic

/-! LOCAL-002 `lem:reset-analytic-projections` (spectral_reduction.tex:57), one named theorem.

Source: "There is `ρ > 0`, independent of `n`, such that for `‖u‖₂ < ρ` the operator `𝓛_u` on `𝓓_{(-1)^n}` is
self-adjoint and every `Γ_n` is in its resolvent set.  The spectral projection `P_n(u) = (2πi)⁻¹∮_{Γ_n}(z-𝓛_u)⁻¹dz`
has rank two, is real-analytic, and satisfies `sup_n ‖P_n(u) - P_n(0)‖ ≤ C ‖u‖₂`."

Encoding (frozen DEF-049, `LocalSpectralOperator`): `𝓛_u` on `D_σ` is the graph `LuGraph L κ u σ`; the resolvent set
is expressed by `IsResolvent`; `P_n(u) = perturbedProj L κ u n r`, `P_n(0) = freeProj L κ n r`.  Self-adjointness is
`IsSelfAdjointGraph` (dense domain and graph equal to its adjoint graph).  The potential `u` ranges over
`L²(0,L) = Lp ℂ 2 (μI L)` (the profile enters through its a.e.-class).  Real-analyticity is
`AnalyticOnNhd ℝ` of `u ↦ P_n(u)` on the ball `‖u‖₂ < ρ` of the real Banach space `L²(0,L)`.

The ONLY hypothesis besides `L > 0` and the contour radius `0 < r < d/2 = 2π/L` is `FreeResolventHyp L κ`, the printed
LOCAL-001 (`lem:reset-free-resolvent`).  The orthonormal basis `χ_{m,j}` of `H_σ` used for the rank and the
self-adjointness is PROVED in `Local002Basis`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local002Final
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002Rank QuantumNLS.Local002SA

variable {L κ : ℝ}

/-- **LOCAL-002 `lem:reset-analytic-projections`.** -/
theorem reset_analytic_projections (hyp : FreeResolventHyp L κ) (hL : 0 < L) {r : ℝ}
    (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ n : ℤ,
      (∀ u : Lp ℂ 2 (μI L), ‖u‖ < ρ →
        IsSelfAdjointGraph (LuGraph L κ (u : ℝ → ℂ) (parity n)) ∧
        (∀ z : ℂ, ‖z - (pm L n : ℂ)‖ = r →
          ∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ (u : ℝ → ℂ) (parity n) z R) ∧
        Module.finrank ℂ (LinearMap.range
          (perturbedProj L κ (u : ℝ → ℂ) n r : H2 L →ₗ[ℂ] H2 L)) = 2 ∧
        ‖perturbedProj L κ (u : ℝ → ℂ) n r - freeProj L κ n r‖ ≤ C * ‖u‖) ∧
      AnalyticOnNhd ℝ (fun u : Lp ℂ 2 (μI L) => perturbedProj L κ (u : ℝ → ℂ) n r) (ball 0 ρ) := by
  set a : ℝ := Real.sqrt κ * Cmax L (r / 2) with ha
  have ha0 : 0 ≤ a := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨1 / (4 * (a + 1)), by positivity, 4 * a, fun n => ⟨fun u hu => ?_, ?_⟩⟩
  · have hu' : ‖u‖ < 1 / (4 * (a + 1)) := by simpa using hu
    have hK : 2 * Real.sqrt κ * Cmax L (r / 2) * ‖u‖ < 1 / 2 := by
      have h1 : 2 * Real.sqrt κ * Cmax L (r / 2) * ‖u‖ = 2 * a * ‖u‖ := by rw [ha]; ring
      rw [h1]
      calc 2 * a * ‖u‖ ≤ 2 * a * (1 / (4 * (a + 1))) :=
            mul_le_mul_of_nonneg_left hu'.le (by positivity)
        _ < 1 / 2 := by
            rw [div_eq_mul_inv]
            have : (0 : ℝ) < a + 1 := by linarith
            field_simp
            linarith
    have hqle : qpar κ L r u ≤ 2 * Real.sqrt κ * Cmax L (r / 2) * ‖u‖ := by
      have hC : Cconst L r ≤ Cmax L (r / 2) := Cconst_le hL (by positivity) (by linarith) hr2
      unfold qpar
      have : 0 ≤ 2 * Real.sqrt κ := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC this) (norm_nonneg _)
    have hq1 : qpar κ L r u < 1 := by linarith
    refine ⟨local_selfadjoint hyp hL hr hr2 n u hq1, ?_, proj_rank hyp hL hr hr2 n u hK, ?_⟩
    · intro z hz
      obtain ⟨R0, R, -, hR, -, -, -⟩ := perturbed_resolvent hyp hr hr2 n hz u hq1
      exact ⟨R, hR⟩
    · have hd := proj_diff_bound hyp hr hr2 n u hq1
      have hq0 := qpar_nonneg κ L r u
      have hq12 : qpar κ L r u ≤ 1 / 2 := by linarith
      have h2 : qpar κ L r u / (1 - qpar κ L r u) ≤ 2 * qpar κ L r u := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      refine hd.trans (h2.trans ?_)
      have : 2 * qpar κ L r u ≤ 2 * (2 * Real.sqrt κ * Cmax L (r / 2) * ‖u‖) := by linarith
      calc 2 * qpar κ L r u ≤ 2 * (2 * Real.sqrt κ * Cmax L (r / 2) * ‖u‖) := this
        _ = 4 * a * ‖u‖ := by rw [ha]; ring
  · refine proj_analytic hyp hr hr2 n (ρ := 1 / (4 * (a + 1))) ?_
    have hC : Cconst L r ≤ Cmax L (r / 2) := Cconst_le hL (by positivity) (by linarith) hr2
    have h1 : 2 * Real.sqrt κ * Cconst L r * (1 / (4 * (a + 1))) ≤
        2 * Real.sqrt κ * Cmax L (r / 2) * (1 / (4 * (a + 1))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC (by positivity)) (by positivity)
    refine h1.trans ?_
    have h2 : 2 * Real.sqrt κ * Cmax L (r / 2) * (1 / (4 * (a + 1))) = 2 * a * (1 / (4 * (a + 1))) := by
      rw [ha]; ring
    rw [h2]
    have : (0 : ℝ) < a + 1 := by linarith
    rw [div_eq_mul_inv]
    field_simp
    linarith

end QuantumNLS.Local002Final
#print axioms QuantumNLS.Local002Final.reset_analytic_projections

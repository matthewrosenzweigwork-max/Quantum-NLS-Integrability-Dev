import Mathlib
import QuantumNLS.RB01Bridge
import QuantumNLS.RootInteractionL1
import QuantumNLS.DiscParamContinuity

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-9: the interaction picture for the actual DEF-013/DEF-014
transfer `L2SpatialTransfer.spatialTransfer κ u z = L1SpatialTransfer.transfer (balCoef κ (profile u) z)`
(source `collective_actions.tex`, "Expanding the spatial integral equation in the interaction representation").

* `freeE z x = diag(e^{-izx/2}, e^{izx/2})` is the free diagonal factor: it *is* the transfer of the zero field
  (`transfer_zero_field`), and `freeE z x` is inverse to `RootInteractionL1.Dc z x` (`freeE_mul_Dc`, `Dc_mul_freeE`).
* `gauge κ u z = transfer (Bc κ (profile u) z)` with the off-diagonal coefficient
  `Bc = [[0, √κ ū e^{izx}], [√κ u e^{-izx}, 0]] = E_z⁻¹ (A_u − A_0) E_z` (`Bc_eq_conj`);
  `norm_Bc_le_pointwise`: `‖Bc(x)‖ ≤ √κ e^{|Im z| x} |u(x)|` for `x ≥ 0`.
* `gauge_integral_eq` (Volterra equation `W = 1 + ∫₀ˣ Bc W`, `L1SpatialTransfer.transfer_integral_eq`) and
  `gauge_unique` (every continuous solution is `W`, `L1SpatialTransfer.integral_solution_unique`).
* **`gauge_eq`**: `W(x) = E_z(x)⁻¹ T(x)` on `[0,L]`; **`spatialTransfer_eq_gauge`**: `T(x) = E_z(x) W(x)`.
* **`discriminant_eq_gauge`**: `Δ_u(z) = tr(E_z(L) W(L)) = e^{-izL/2} W₀₀(L) + e^{izL/2} W₁₁(L)`.
The identity `E_z⁻¹ T = W` itself is `RootInteractionL1.Nc_eq_transfer` (frozen, read-only). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set ComplexConjugate
open scoped Matrix Interval
open QuantumNLS.SpatialTransfer QuantumNLS.L1SpatialTransfer QuantumNLS.LinearFundamental
  QuantumNLS.RootInteractionL1
open QuantumNLS.RootDiscriminantBound (P1 P2 norm_le_of_row_sums row_sum_le_norm norm_one_mat2_le)

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

local instance instPseudoMetrizableMat2RB01TG : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))

local instance instENormedAddMonoidMat2RB01TG : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid

namespace QuantumNLS.RB01TraceGauge

variable {L : ℝ}

/-- The free diagonal factor `E_z(x) = diag(e^{-izx/2}, e^{izx/2})`. -/
def freeE (z : ℂ) (x : ℝ) : Mat2 := E2c z x • P1 + E1c z x • P2

theorem freeE_apply (z : ℂ) (x : ℝ) :
    freeE z x = !![Complex.exp (-(Complex.I * z / 2 * x)), 0; 0, Complex.exp (Complex.I * z / 2 * x)] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [freeE, P1, P2, E1c, E2c, a1c]

theorem freeE_mul_Dc (z : ℂ) (x : ℝ) : freeE z x * Dc z x = 1 := by
  have h := E1c_mul_E2c z x
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [freeE, Dc, P1, P2, Matrix.mul_apply, Fin.sum_univ_two, h, mul_comm (E2c z x)]

theorem Dc_mul_freeE (z : ℂ) (x : ℝ) : Dc z x * freeE z x = 1 := by
  have h := E1c_mul_E2c z x
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [freeE, Dc, P1, P2, Matrix.mul_apply, Fin.sum_univ_two, h, mul_comm (E2c z x)]

/-- The constant coefficient `A_0 = diag(-iz/2, iz/2)` of the zero field. -/
theorem balCoef_zero (κ : ℝ) (z : ℂ) (x : ℝ) :
    balCoef κ (fun _ => 0) z x = !![-(Complex.I * z) / 2, 0; 0, Complex.I * z / 2] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [balCoef, coef]

/-- The off-diagonal coefficient is the conjugated perturbation: `E_z(x) Bc(x) = (A_u(x) − A_0) E_z(x)`. -/
theorem freeE_mul_Bc (κ : ℝ) (v : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    freeE z x * Bc κ v z x = (balCoef κ v z x - balCoef κ (fun _ => 0) z x) * freeE z x := by
  have h := E1c_mul_E2c z x
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [freeE, Bc, P1, P2, balCoef, coef, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
      | linear_combination ((Real.sqrt κ : ℂ) * conj (v x) * E1c z x) * h
      | linear_combination ((Real.sqrt κ : ℂ) * v x * E2c z x) * h

theorem Bc_eq_conj (κ : ℝ) (v : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    Bc κ v z x = Dc z x * (balCoef κ v z x - balCoef κ (fun _ => 0) z x) * freeE z x := by
  rw [mul_assoc, ← freeE_mul_Bc, ← mul_assoc, Dc_mul_freeE, one_mul]

/-- Pointwise bound of the interaction coefficient: `‖Bc(x)‖ ≤ √κ e^{|Im z| x} |u(x)|`, `x ≥ 0`. -/
theorem norm_Bc_le_pointwise (κ : ℝ) (v : ℝ → ℂ) (z : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    ‖Bc κ v z x‖ ≤ Real.sqrt κ * Real.exp (|z.im| * x) * ‖v x‖ := by
  have hs : ‖((Real.sqrt κ : ℝ) : ℂ)‖ = Real.sqrt κ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 := norm_E1c_sq_le z (L := x) ⟨hx, le_rfl⟩
  have h2 := norm_E2c_sq_le z (L := x) ⟨hx, le_rfl⟩
  have hp : 0 ≤ Real.sqrt κ * ‖v x‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hC : 0 ≤ Real.sqrt κ * Real.exp (|z.im| * x) * ‖v x‖ := by positivity
  refine norm_offdiag_le _ _ ?_ ?_ hC
  · rw [norm_mul, norm_mul, hs, Complex.norm_conj]
    nlinarith [mul_le_mul_of_nonneg_left h1 hp]
  · rw [norm_mul, norm_mul, hs]
    nlinarith [mul_le_mul_of_nonneg_left h2 hp]

/-- `‖E_z(x)‖ ≤ e^{|Im z| L/2}` on `[0,L]`. -/
theorem norm_freeE_le (z : ℂ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) : ‖freeE z x‖ ≤ Real.exp (|z.im| * L / 2) := by
  have h1 : ‖E1c z x‖ ≤ Real.exp (|z.im| * L / 2) := by
    rw [norm_E1c]; apply Real.exp_le_exp.2
    have : -(z.im * x) ≤ |z.im| * L := by
      calc -(z.im * x) = (-z.im) * x := by ring
        _ ≤ |z.im| * x := mul_le_mul_of_nonneg_right (neg_le_abs _) hx.1
        _ ≤ |z.im| * L := mul_le_mul_of_nonneg_left hx.2 (abs_nonneg _)
    linarith
  have h2 : ‖E2c z x‖ ≤ Real.exp (|z.im| * L / 2) := by
    rw [norm_E2c]; apply Real.exp_le_exp.2
    have : z.im * x ≤ |z.im| * L := by
      calc z.im * x ≤ |z.im| * x := mul_le_mul_of_nonneg_right (le_abs_self _) hx.1
        _ ≤ |z.im| * L := mul_le_mul_of_nonneg_left hx.2 (abs_nonneg _)
    linarith
  have hC : 0 ≤ Real.exp (|z.im| * L / 2) := (Real.exp_pos _).le
  refine norm_le_of_row_sums _ hC (fun i => ?_)
  fin_cases i <;> simp [freeE, P1, P2, h1, h2]

/-- The transfer of the zero coefficient is the identity. -/
theorem transfer_zero (hL : 0 ≤ L) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) :
    transfer (fun _ : ℝ => (0 : Mat2)) x = 1 := by
  have h := integral_solution_unique (A := fun _ : ℝ => (0 : Mat2)) (N := fun _ : ℝ => (1 : Mat2))
    hL intervalIntegrable_const
    (continuousOn_transfer hL intervalIntegrable_const) continuousOn_const
    (fun _ hx => transfer_integral_eq hL intervalIntegrable_const hx) (fun _ _ => by simp) hx
  exact h

/-- The free factor is the transfer of the zero field. -/
theorem transfer_zero_field (hL : 0 < L) (κ : ℝ) (z : ℂ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) :
    transfer (balCoef κ (fun _ => 0) z) x = freeE z x := by
  have h := Nc_eq_transfer hL (v := fun _ => (0 : ℂ)) intervalIntegrable_const κ z hx
  have hB : Bc κ (fun _ => (0 : ℂ)) z = fun _ => (0 : Mat2) := by
    funext s; ext i j; fin_cases i <;> fin_cases j <;> simp [Bc]
  rw [hB, transfer_zero hL.le hx] at h
  have h2 := congrArg (fun m => freeE z x * m) h
  simp only [mul_one, ← mul_assoc, freeE_mul_Dc, one_mul] at h2
  exact h2

variable [Fact (0 < L)]

/-- The interaction-picture transfer `W = transfer(Bc)` of the physical profile. -/
def gauge (κ : ℝ) (u : PhysicalTensor.L2T L) (z : ℂ) : ℝ → Mat2 :=
  transfer (Bc κ (L2SpatialTransfer.profile u) z)

theorem intervalIntegrable_gaugeCoef (κ : ℝ) (u : PhysicalTensor.L2T L) (z : ℂ) :
    IntervalIntegrable (Bc κ (L2SpatialTransfer.profile u) z) volume 0 L :=
  intervalIntegrable_Bc (L2SpatialTransfer.intervalIntegrable_profile u) κ z

/-- `W` solves the Volterra equation `W(x) = 1 + ∫₀ˣ Bc(s) W(s) ds` on `[0,L]`. -/
theorem gauge_integral_eq (κ : ℝ) (u : PhysicalTensor.L2T L) (z : ℂ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) :
    gauge κ u z x = 1 + ∫ s in (0 : ℝ)..x, Bc κ (L2SpatialTransfer.profile u) z s * gauge κ u z s :=
  transfer_integral_eq (Fact.out : 0 < L).le (intervalIntegrable_gaugeCoef κ u z) hx

theorem continuousOn_gauge (κ : ℝ) (u : PhysicalTensor.L2T L) (z : ℂ) :
    ContinuousOn (gauge κ u z) (Icc 0 L) :=
  continuousOn_transfer (Fact.out : 0 < L).le (intervalIntegrable_gaugeCoef κ u z)

/-- Uniqueness: every continuous solution of the Volterra equation is `W`. -/
theorem gauge_unique (κ : ℝ) (u : PhysicalTensor.L2T L) (z : ℂ) {M : ℝ → Mat2}
    (hM : ContinuousOn M (Icc 0 L))
    (hMe : ∀ x ∈ Icc (0 : ℝ) L, M x = 1 + ∫ s in (0 : ℝ)..x, Bc κ (L2SpatialTransfer.profile u) z s * M s) :
    EqOn M (gauge κ u z) (Icc 0 L) :=
  integral_solution_unique (Fact.out : 0 < L).le (intervalIntegrable_gaugeCoef κ u z) hM
    (continuousOn_gauge κ u z) hMe (fun _ hx => gauge_integral_eq κ u z hx)

/-- **Interaction picture**: `W(x) = E_z(x)⁻¹ T(x)` on `[0,L]`. -/
theorem gauge_eq (κ : ℝ) (u : PhysicalTensor.L2T L) (z : ℂ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) :
    gauge κ u z x = Dc z x * L2SpatialTransfer.spatialTransfer κ u z x :=
  (Nc_eq_transfer (Fact.out : 0 < L) (L2SpatialTransfer.intervalIntegrable_profile u) κ z hx).symm

theorem spatialTransfer_eq_gauge (κ : ℝ) (u : PhysicalTensor.L2T L) (z : ℂ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) :
    L2SpatialTransfer.spatialTransfer κ u z x = freeE z x * gauge κ u z x := by
  rw [gauge_eq κ u z hx, ← mul_assoc, freeE_mul_Dc, one_mul]

/-- **Trace in the interaction picture**: `Δ_u(z) = tr(E_z(L) W(L))`. -/
theorem discriminant_eq_gauge (κ : ℝ) (u : PhysicalTensor.L2T L) (z : ℂ) :
    L2SpatialTransfer.discriminant κ u z = Matrix.trace (freeE z L * gauge κ u z L) := by
  unfold L2SpatialTransfer.discriminant
  rw [spatialTransfer_eq_gauge κ u z ⟨(Fact.out : 0 < L).le, le_rfl⟩]

theorem discriminant_eq_gauge_entries (κ : ℝ) (u : PhysicalTensor.L2T L) (z : ℂ) :
    L2SpatialTransfer.discriminant κ u z = E2c z L * gauge κ u z L 0 0 + E1c z L * gauge κ u z L 1 1 := by
  rw [discriminant_eq_gauge, Matrix.trace_fin_two]
  simp [freeE, P1, P2, Matrix.mul_apply, Fin.sum_univ_two]

/-- `L¹` bound of the interaction coefficient on the period. -/
theorem integral_norm_gaugeCoef_le (κ : ℝ) (u : PhysicalTensor.L2T L) (z : ℂ) :
    ∫ s in (0 : ℝ)..L, ‖Bc κ (L2SpatialTransfer.profile u) z s‖ ≤
      Real.sqrt κ * Real.exp (|z.im| * L) * (Real.sqrt L * ‖u‖) := by
  refine (integral_norm_Bc_le (Fact.out : 0 < L).le (L2SpatialTransfer.intervalIntegrable_profile u) κ z).trans ?_
  exact mul_le_mul_of_nonneg_left (DiscParamContinuity.integral_profile_le u) (by positivity)

end QuantumNLS.RB01TraceGauge

#print axioms QuantumNLS.RB01TraceGauge.freeE_apply
#print axioms QuantumNLS.RB01TraceGauge.freeE_mul_Dc
#print axioms QuantumNLS.RB01TraceGauge.freeE_mul_Bc
#print axioms QuantumNLS.RB01TraceGauge.Bc_eq_conj
#print axioms QuantumNLS.RB01TraceGauge.norm_Bc_le_pointwise
#print axioms QuantumNLS.RB01TraceGauge.norm_freeE_le
#print axioms QuantumNLS.RB01TraceGauge.transfer_zero_field
#print axioms QuantumNLS.RB01TraceGauge.gauge_integral_eq
#print axioms QuantumNLS.RB01TraceGauge.gauge_unique
#print axioms QuantumNLS.RB01TraceGauge.gauge_eq
#print axioms QuantumNLS.RB01TraceGauge.spatialTransfer_eq_gauge
#print axioms QuantumNLS.RB01TraceGauge.discriminant_eq_gauge
#print axioms QuantumNLS.RB01TraceGauge.discriminant_eq_gauge_entries
#print axioms QuantumNLS.RB01TraceGauge.integral_norm_gaugeCoef_le

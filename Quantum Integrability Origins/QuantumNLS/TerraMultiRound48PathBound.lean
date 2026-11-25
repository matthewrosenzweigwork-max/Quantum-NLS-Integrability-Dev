import QuantumNLS.TerraMultiRound48Leading
import QuantumNLS.TerraMultiRound48OrthantMoment

/-! Path-size bound and reverse spatial Fubini for the finite tree kernel. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set AddCircle
namespace QuantumNLS.TerraMultiRound48PathBound
open QuantumNLS.TranslatedCorrelation QuantumNLS.TerraMultiRound48TreeFubini
open QuantumNLS.TerraMultiRound48Leading

variable {L : ℝ} [Fact (0 < L)]

/-- Each path shift is bounded by the total time, with no sign restriction
on the variables. This gives the printed bound on the positive orthant. -/
theorem scaled_path_abs_le {n q : ℕ} (paths : Fin q → Finset (Fin n))
    (z : ℝ) (t : Fin n → ℝ) (j : Fin q) :
    |scaledShift paths z t j| ≤ |z| * ∑ i, |t i| := by
  have hp : |∑ i ∈ paths j, t i| ≤ ∑ i, |t i| := by
    calc
      _ ≤ ∑ i ∈ paths j, |t i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |t i| := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun i _ _ => abs_nonneg _)
  simp only [scaledShift, abs_mul, abs_neg]
  calc
    _ ≤ (∑ i, |t i|) * |z| := mul_le_mul_of_nonneg_right hp (abs_nonneg _)
    _ = _ := mul_comm _ _

/-- The time integral and spatial torus integral commute, using the joint
integrability proved for arbitrary finite path families. -/
theorem tree_fubini_swap {n q k : ℕ} (hk : 1 ≤ k) (f : Fin q → Hk L k)
    (paths : Fin q → Finset (Fin n)) (Y : ℝ) :
    (∫ t : Fin n → ℝ, ∫ x : AddCircle L, treeIntegrand hk f paths Y (t,x)
      ∂(volume : Measure (AddCircle L)) ∂
      (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ))))) =
    ∫ x : AddCircle L, ∫ t : Fin n → ℝ, treeIntegrand hk f paths Y (t,x) ∂
      (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ)))) ∂
      (volume : Measure (AddCircle L)) := by
  exact integral_integral_swap (tree_integrable hk f paths Y)

#print axioms scaled_path_abs_le
#print axioms tree_fubini_swap
end QuantumNLS.TerraMultiRound48PathBound

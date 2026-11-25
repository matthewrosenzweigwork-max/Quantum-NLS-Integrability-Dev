import QuantumNLS.ActualModelQuantumR52a
import QuantumNLS.ActualModelTargetR53a
import QuantumNLS.HighAngleEvolutionBridge

/-! Bounded representatives of finite circle angles and their exact signs on
the physical count rotations. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace
open QuantumNLS.CountRotations QuantumNLS.HighAngleRotations
open QuantumNLS.BetheCoefficientTransform QuantumNLS.ActualModelQuantumR52a
open QuantumNLS.HighAngleEvolutionBridge QuantumNLS.HighAngleReconstruction
namespace QuantumNLS.TerraMultiRound89FiniteAngle
variable {L κ : ℝ} [Fact (0 < L)]

def representative (θ : AngleTorus) (n : ℤ) : ℝ := (θ n : ℂ).arg

theorem representative_bound (θ : AngleTorus) (n : ℤ) :
    |representative θ n| ≤ Real.pi := by
  exact Complex.abs_arg_le_pi _

theorem classical_angle (I : Finset ℤ) (θ : AngleTorus) :
    ActualModelTargetR53a.angle I (fun n => -representative θ n) = truncate I θ := by
  classical
  funext n
  by_cases hn : n ∈ I
  · simp [ActualModelTargetR53a.angle, truncate, hn, representative, Circle.exp_arg]
  · simp [ActualModelTargetR53a.angle, truncate, hn]

/-- The same real parameter gives the inverse circle phase on the classical
coordinates, matching the quantum character's inverse. -/
theorem classical_angle_same_parameter (I : Finset ℤ) (θ : AngleTorus) :
    ActualModelTargetR53a.angle I (representative θ) = (truncate I θ)⁻¹ := by
  classical
  funext n
  by_cases hn : n ∈ I
  · simp [ActualModelTargetR53a.angle, truncate, hn, representative,
      Circle.exp_neg, Circle.exp_arg]
  · simp [ActualModelTargetR53a.angle, truncate, hn]

/-- The finite count unitary uses the positive argument, because countPhase
contains the inverse circle character. -/
theorem count_unitary_eq_rotation (hκ : 0 < κ) (I : Finset ℤ)
    (θ : AngleTorus) (N : ℕ) (ψ : HN L (N+1)) :
    countUnitary hκ I (representative θ) N ψ =
      quantumRotation (Def044D1SpectralR51a.basis (L := L) hκ N) (truncate I θ) ψ := by
  let b := Def044D1SpectralR51a.basis (L := L) hκ N
  apply b.repr.injective
  ext m
  simp only [HilbertBasis.repr_apply_apply]
  change ⟪b m, BetheSpectralCharges.evolution b (countSymbol I (representative θ) N) 1 ψ⟫_ℂ = _
  have hsym : countSymbol I (representative θ) N m = Real.pi * countEigen I (unitAngle θ) m := by
    unfold countSymbol countEigen unitAngle representative
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hm : (BetheCoefficientTransform.marrArr (N + 1) m).1 = m.1 := rfl
    rw [hm]
    field_simp
  rw [BetheSpectralCharges.evolution_coord, rotation_coeff, countPhase_exp]
  simp only [DiagonalMultiplier.phase, one_mul, hsym]

#print axioms representative_bound
#print axioms classical_angle
#print axioms classical_angle_same_parameter
#print axioms count_unitary_eq_rotation
end QuantumNLS.TerraMultiRound89FiniteAngle

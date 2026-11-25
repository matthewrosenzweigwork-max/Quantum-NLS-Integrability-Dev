import QuantumNLS.HighAngleRotations
import QuantumNLS.FullCharacterProjection
import QuantumNLS.BetheSpectralCharges

/-! Algebra of low and high count-angle rotations for R-B2E70586.
The tail angle is literally one on the chosen finite low set. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open QuantumNLS.CountRotations QuantumNLS.HighAngleRotations
open QuantumNLS.BetheLabels QuantumNLS.BetheCoefficientTransform
namespace QuantumNLS.TerraMultiRound87Rotations

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

lemma countPhase_mul (θ φ : AngleTorus) (m : MArr N) :
    countPhase (θ * φ) m = countPhase θ m * countPhase φ m := by
  classical
  simp [countPhase, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, mul_comm]

/-- The actual Bethe-diagonal rotations form a representation on every vector. -/
theorem quantumRotation_mul (b : BetheBasis L N) (θ φ : AngleTorus) (x : HN L N) :
    quantumRotation b (θ * φ) x = quantumRotation b θ (quantumRotation b φ x) := by
  apply b.repr.injective
  ext m
  rw [QuantumNLS.FullCharacterProjection.rotation_coeff,
    QuantumNLS.FullCharacterProjection.rotation_coeff,
    QuantumNLS.FullCharacterProjection.rotation_coeff, countPhase_mul]
  simp only [Circle.coe_mul]
  ring

/-- A spectral charge evolution and every count rotation commute exactly. -/
theorem quantumRotation_evolution_commute (b : BetheBasis L N)
    (θ : AngleTorus) (ev : MArr N → ℝ) (t : ℝ) (x : HN L N) :
    quantumRotation b θ (QuantumNLS.BetheSpectralCharges.evolution b ev t x) =
      QuantumNLS.BetheSpectralCharges.evolution b ev t (quantumRotation b θ x) := by
  apply b.repr.injective
  ext m
  simp only [HilbertBasis.repr_apply_apply]
  change ⟪b m, quantumRotation b θ (QuantumNLS.BetheSpectralCharges.evolution b ev t x)⟫_ℂ =
    ⟪b m, QuantumNLS.BetheSpectralCharges.evolution b ev t (quantumRotation b θ x)⟫_ℂ
  rw [HighAngleRotations.rotation_coeff, QuantumNLS.BetheSpectralCharges.evolution_coord,
    QuantumNLS.BetheSpectralCharges.evolution_coord, HighAngleRotations.rotation_coeff]
  ring

/-- A diagonal projection is preserved by every count rotation. -/
theorem projection_rotation_commute (b : BetheBasis L N) (P : HN L N →L[ℂ] HN L N)
    (μ : MArr N → ℂ) (hP : ∀ m, P (b m) = μ m • b m)
    (θ : AngleTorus) (x : HN L N) :
    P (quantumRotation b θ x) = quantumRotation b θ (P x) := by
  apply b.repr.injective
  ext m
  simp only [HilbertBasis.repr_apply_apply]
  change ⟪b m, P (quantumRotation b θ x)⟫_ℂ = ⟪b m, quantumRotation b θ (P x)⟫_ℂ
  rw [QuantumNLS.HilbertDiagOp.eig_coeff b P μ hP, HighAngleRotations.rotation_coeff,
    HighAngleRotations.rotation_coeff, QuantumNLS.HilbertDiagOp.eig_coeff b P μ hP]
  ring

/-- A diagonal projection is preserved by every spectral charge evolution. -/
theorem projection_evolution_commute (b : BetheBasis L N) (P : HN L N →L[ℂ] HN L N)
    (μ : MArr N → ℂ) (hP : ∀ m, P (b m) = μ m • b m)
    (ev : MArr N → ℝ) (t : ℝ) (x : HN L N) :
    P (QuantumNLS.BetheSpectralCharges.evolution b ev t x) =
      QuantumNLS.BetheSpectralCharges.evolution b ev t (P x) := by
  apply b.repr.injective
  ext m
  simp only [HilbertBasis.repr_apply_apply]
  change ⟪b m, P (QuantumNLS.BetheSpectralCharges.evolution b ev t x)⟫_ℂ =
    ⟪b m, QuantumNLS.BetheSpectralCharges.evolution b ev t (P x)⟫_ℂ
  rw [QuantumNLS.HilbertDiagOp.eig_coeff b P μ hP,
    QuantumNLS.BetheSpectralCharges.evolution_coord,
    QuantumNLS.BetheSpectralCharges.evolution_coord,
    QuantumNLS.HilbertDiagOp.eig_coeff b P μ hP]
  ring

/-- The residual high-angle factor is one on every low coordinate. -/
def tailAngle (a : Finset ℤ) (θ : AngleTorus) : AngleTorus :=
  θ * (truncate a θ)⁻¹

lemma tailAngle_eq_one (a : Finset ℤ) (θ : AngleTorus) (n : ℤ) (hn : n ∈ a) :
    tailAngle a θ n = 1 := by
  classical
  simp [tailAngle, truncate, hn]

lemma tailAngle_mul_low (a : Finset ℤ) (θ : AngleTorus) :
    tailAngle a θ * truncate a θ = θ := by
  simp [tailAngle, mul_assoc]

#print axioms quantumRotation_evolution_commute
#print axioms projection_rotation_commute
#print axioms projection_evolution_commute
#print axioms countPhase_mul
#print axioms quantumRotation_mul
#print axioms tailAngle_eq_one
#print axioms tailAngle_mul_low
end QuantumNLS.TerraMultiRound87Rotations

import QuantumNLS.RootMassPlane

/-! A physical plane-wave second-derivative constituent of R-EC25334D.
This does not assert the sequence-valued theorem. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.TerraMultiRound28PlaneSecond
open QuantumNLS.Fourier (modeLp)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The literal indexed mass, restricted to a real plane-wave amplitude. -/
def planeAction (hκ : 0 < κ) (k n : ℤ) (s : ℝ) : ℝ :=
  (RootIndexedMasses.masses hκ (((s : ℂ) • modeLp L k))).1 n

/-- Exact scalar restriction, including every off-diagonal index. -/
theorem planeAction_eq (hκ : 0 < κ) (k n : ℤ) (s : ℝ) :
    planeAction (L := L) hκ k n s = if n = k then s ^ 2 else 0 := by
  rw [planeAction, RootMassPlane.masses_plane]
  split_ifs <;> simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- First scalar derivative of the actual action along the physical mode. -/
theorem planeAction_hasDerivAt (hκ : 0 < κ) (k n : ℤ) (s : ℝ) :
    HasDerivAt (planeAction (L := L) hκ k n) (if n = k then 2 * s else 0) s := by
  by_cases h : n = k
  · simp only [ite_eq_left h]
    have heq : planeAction (L := L) hκ k n = fun t : ℝ => t ^ 2 := by
      funext t
      simp [planeAction_eq (L := L), h]
    rw [heq]
    convert (hasDerivAt_id s).pow 2 using 1 <;> simp [funext_iff, Pi.pow_apply, id_eq, mul_comm]
  · simp only [ite_eq_right h]
    have heq : planeAction (L := L) hκ k n = fun _ : ℝ => 0 := by
      funext t
      simp [planeAction_eq (L := L), h]
    rw [heq]
    exact hasDerivAt_const s 0

/-- Its second scalar derivative is two on the diagonal and zero elsewhere. -/
theorem planeAction_second (hκ : 0 < κ) (k n : ℤ) (s : ℝ) :
    HasDerivAt (deriv (planeAction (L := L) hκ k n)) (if n = k then 2 else 0) s := by
  have hd : deriv (planeAction (L := L) hκ k n) = fun t => if n = k then 2 * t else 0 := by
    funext t
    exact (planeAction_hasDerivAt (L := L) hκ k n t).deriv
  rw [hd]
  by_cases h : n = k
  · simp only [ite_eq_left h]
    convert (hasDerivAt_const s (2 : ℝ)).mul (hasDerivAt_id s) using 1 <;> simp [funext_iff, Pi.mul_apply, id_eq, mul_comm]
  · simp only [ite_eq_right h]
    exact hasDerivAt_const s 0

/-- No finite set of labels contains all diagonal second-derivative witnesses. -/
theorem planeAction_second_outside (hκ : 0 < κ) (S : Finset ℤ) :
    ∃ k : ℤ, k ∉ S ∧ HasDerivAt (deriv (planeAction (L := L) hκ k k)) 2 0 := by
  obtain ⟨k, hk⟩ := S.finite_toSet.exists_notMem
  exact ⟨k, hk, by simpa using planeAction_second (L := L) hκ k k 0⟩

end QuantumNLS.TerraMultiRound28PlaneSecond
#print axioms QuantumNLS.TerraMultiRound28PlaneSecond.planeAction_eq
#print axioms QuantumNLS.TerraMultiRound28PlaneSecond.planeAction_hasDerivAt
#print axioms QuantumNLS.TerraMultiRound28PlaneSecond.planeAction_second
#print axioms QuantumNLS.TerraMultiRound28PlaneSecond.planeAction_second_outside

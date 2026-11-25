import QuantumNLS.TerraMultiRound89PhysicalCore
import QuantumNLS.Fidelity

/-! Shifted contact form as an ordinary Hilbert-space inner product. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped InnerProductSpace
open QuantumNLS.ContactOperator QuantumNLS.ContactForm
namespace QuantumNLS.TerraMultiRound90Shifted
variable {L : ℝ} [Fact (0 < L)] {N : ℕ} {c : ℝ}

theorem mop_positive (hc : 0 ≤ c) : (Mop (L := L) (N := N) c hc).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).2
  intro x
  have h := coercive_Mop hc x
  constructor
  · apply Complex.conj_eq_iff_re.mp
    rw [inner_conj_symm, ← Mop_symm hc x x]
  · rw [Mop_symm hc x x]
    exact (sq_nonneg ‖x‖).trans h

section GenericRoot
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def genericRoot (A : E →L[ℂ] E) : E →L[ℂ] E := CFC.sqrt A

theorem genericRoot_selfadjoint (A : E →L[ℂ] E) : IsSelfAdjoint (genericRoot A) :=
  (CFC.sqrt_nonneg A).isSelfAdjoint

theorem genericRoot_sq (A : E →L[ℂ] E) (hA : A.IsPositive) :
    genericRoot A * genericRoot A = A :=
  CFC.sqrt_mul_sqrt_self A (ContinuousLinearMap.nonneg_iff_isPositive.mpr hA)
end GenericRoot

def shiftRoot (hc : 0 ≤ c) : VSym L N →L[ℂ] VSym L N := genericRoot (Mop c hc)

theorem shiftRoot_selfadjoint (hc : 0 ≤ c) : IsSelfAdjoint (shiftRoot (L := L) (N := N) hc) :=
  genericRoot_selfadjoint _

theorem shiftRoot_sq (hc : 0 ≤ c) :
    shiftRoot (L := L) (N := N) hc * shiftRoot hc = Mop c hc :=
  genericRoot_sq _ (mop_positive hc)

theorem inner_shiftRoot (hc : 0 ≤ c) (x y : VSym L N) :
    ⟪shiftRoot hc x, shiftRoot hc y⟫_ℂ = Bform c x y := by
  rw [← ContinuousLinearMap.adjoint_inner_left, (shiftRoot_selfadjoint hc).adjoint_eq,
    ← ContinuousLinearMap.mul_apply, shiftRoot_sq, inner_Mop_left]

theorem shiftRoot_surjective (hc : 0 ≤ c) : Function.Surjective (shiftRoot (L := L) (N := N) hc) := by
  intro x
  refine ⟨shiftRoot hc (Minv c hc x), ?_⟩
  rw [← ContinuousLinearMap.mul_apply, shiftRoot_sq, Mop_Minv]

theorem shifted_pairing (hc : 0 ≤ c) (y z : VSym L N) (b : SymL2 L N) (e : ℝ)
    (hy : valSym y = b)
    (hpair : ∀ x : VSym L N, q c x.1 y.1 = (e : ℂ) * ⟪valSym x, b⟫_ℂ) :
    ⟪shiftRoot hc z, shiftRoot hc y⟫_ℂ = ((e + 1 : ℝ) : ℂ) * ⟪valSym z, b⟫_ℂ := by
  rw [inner_shiftRoot, Bform, hpair, ← hy]
  change (e : ℂ) * ⟪valSym z, valSym y⟫_ℂ + ⟪valSym z, valSym y⟫_ℂ = _
  push_cast
  ring

#print axioms mop_positive
#print axioms shiftRoot_selfadjoint
#print axioms shiftRoot_sq
#print axioms inner_shiftRoot
#print axioms shiftRoot_surjective
#print axioms shifted_pairing
end QuantumNLS.TerraMultiRound90Shifted

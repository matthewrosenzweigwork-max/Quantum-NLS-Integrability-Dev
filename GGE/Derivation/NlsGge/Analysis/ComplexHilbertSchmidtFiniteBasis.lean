import NlsGge.Analysis.ComplexHilbertSchmidtNorm

/-! NEW-F02.06: finiteness iff every Hilbert-basis sum is summable, and a
concrete matrix-energy bound implies HS membership and the actual HS norm bound.
The matrix inequality is an honest reusable prerequisite, not assumed NLS
completion; the concrete potential and DVD estimate are proved separately. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal BigOperators InnerProduct InnerProductSpace
namespace NlsGge.Pilot
variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem summable_basis_of_isComplexHilbertSchmidt {ι : Type*}
    {T : E →L[ℂ] F} (b : HilbertBasis ι ℂ E)
    (hT : IsComplexHilbertSchmidt T) :
    Summable (fun i : ι => ‖T (b i)‖ ^ 2) := by
  have hfinite : (∑' i : ι, ENNReal.ofReal (‖T (b i)‖ ^ 2)) ≠ ∞ := by
    rw [← complexHilbertSchmidtEnergy_eq_basis T b]
    exact hT
  have hfinite_nn :
      (∑' i : ι, (Real.toNNReal (‖T (b i)‖ ^ 2) : ℝ≥0∞)) ≠ ∞ := by
    simpa only [← ENNReal.ofNNReal_toNNReal] using hfinite
  have hnn : Summable (fun i : ι => Real.toNNReal (‖T (b i)‖ ^ 2)) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp hfinite_nn
  have hcoe : Summable (fun i : ι => (Real.toNNReal (‖T (b i)‖ ^ 2) : ℝ)) :=
    NNReal.summable_coe.mpr hnn
  refine hcoe.congr fun i => ?_
  simp [Real.coe_toNNReal', max_eq_left (sq_nonneg _)]

theorem isComplexHilbertSchmidt_iff_summable_basis {ι : Type*}
    (T : E →L[ℂ] F) (b : HilbertBasis ι ℂ E) :
    IsComplexHilbertSchmidt T ↔ Summable (fun i : ι => ‖T (b i)‖ ^ 2) :=
  ⟨summable_basis_of_isComplexHilbertSchmidt b,
    isComplexHilbertSchmidt_of_summable_basis b⟩

theorem complexHilbertSchmidt_of_matrix_bound {ι κ : Type*}
    {T : E →L[ℂ] F} (b : HilbertBasis ι ℂ E) (d : HilbertBasis κ ℂ F)
    {R : ℝ} (hR : 0 ≤ R)
    (h : (∑' i : ι, ∑' k : κ, ENNReal.ofReal (‖⟪d k, T (b i)⟫_ℂ‖ ^ 2)) ≤
      ENNReal.ofReal (R ^ 2)) :
    IsComplexHilbertSchmidt T ∧ complexHilbertSchmidtNorm T ≤ R := by
  have he : complexHilbertSchmidtEnergy T ≤ ENNReal.ofReal (R ^ 2) := by
    rw [complexHilbertSchmidtEnergy_eq_matrix T b d]
    exact h
  exact ⟨isComplexHilbertSchmidt_of_energy_le he,
    complexHilbertSchmidtNorm_le_of_energy_le hR he⟩
end NlsGge.Pilot

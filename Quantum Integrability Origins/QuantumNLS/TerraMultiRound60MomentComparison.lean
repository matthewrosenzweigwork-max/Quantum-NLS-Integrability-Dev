import QuantumNLS.TerraMultiRound60KernelBound

/-! Bounded displacements preserve all positive integer moment finiteness. -/
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open scoped ENNReal
namespace QuantumNLS.TerraMultiRound60MomentComparison

theorem integrable_norm_pow_iff_memLp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : ℕ) (hp : 0 < p) (f : α → ℝ)
    (hf : AEStronglyMeasurable f μ) :
    Integrable (fun x => ‖f x‖^p) μ ↔ MemLp f (p : ℝ≥0∞) μ := by
  have h := integrable_norm_rpow_iff hf (p := (p : ℝ≥0∞))
    (by exact_mod_cast hp.ne') (by simp)
  simpa using h

theorem bounded_displacement_moments {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (p : ℕ) (hp : 0 < p)
    (f g : α → ℝ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ‖f x - g x‖ ≤ C) :
    Integrable (fun x => ‖f x‖^p) μ ↔ Integrable (fun x => ‖g x‖^p) μ := by
  rw [integrable_norm_pow_iff_memLp μ p hp f hf,
    integrable_norm_pow_iff_memLp μ p hp g hg]
  have hd : MemLp (fun x => f x - g x) (p : ℝ≥0∞) μ :=
    MemLp.of_bound (hf.sub hg) C hbound
  constructor
  · intro h
    have hg' := h.sub hd
    convert hg' using 1
    funext x
    simp
  · intro h
    have hf' := hd.add h
    convert hf' using 1
    funext x
    simp

#print axioms integrable_norm_pow_iff_memLp
#print axioms bounded_displacement_moments
end QuantumNLS.TerraMultiRound60MomentComparison

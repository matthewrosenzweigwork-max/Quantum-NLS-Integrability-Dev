import LiebLiniger.FixedPeriod.Quantum.MixedTensorCore
import LiebLiniger.FixedPeriod.Quantum.FockSpace
import LiebLiniger.FixedPeriod.Quantum.Polarization

/-! Exponential-vector totality on the genuine mixed-kernel foundation. -/
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

@[simp] theorem symmetricTensorContinuousMultilinear_diagonal (n : ℕ) (u : Lp ℂ 2 μ) :
    symmetricTensorContinuousMultilinear μ n (fun _ => u) = pureSymmetricTensor μ n u := by
  apply Subtype.ext
  change symmetrizeL2 μ (mixedTensorL2 μ (fun _ : Fin n => u)) = pureTensorL2 μ u
  rw [mixedTensorL2_diagonal, symmetrizeL2_pureTensorL2]

/-- Pairing with a symmetric vector absorbs the genuine orthogonal projection. -/
theorem inner_symmetricSector_symmetrize (n : ℕ) (f : SymmetricSector μ n)
    (g : ProductL2 μ (Fin n)) :
    inner ℂ (f : ProductL2 μ (Fin n)) (symmetrizeL2 μ g) =
      inner ℂ (f : ProductL2 μ (Fin n)) g := by
  have hs := symmetrizeL2_isSymmetric (ι := Fin n) μ
    (f : ProductL2 μ (Fin n)) g
  change inner ℂ (symmetrizeL2 μ (f : ProductL2 μ (Fin n))) g =
    inner ℂ (f : ProductL2 μ (Fin n)) (symmetrizeL2 μ g) at hs
  rw [symmetricSector_fixed μ n f] at hs
  exact hs.symm

/-- Orthogonality to every exponential vector forces orthogonality to every
actual symmetrized elementary kernel, by the packet's polarization step. -/
theorem exponentialVector_orthogonal_symmetricMixedTensor (ψ : FockSpace μ)
    (hψ : ∀ u : Lp ℂ 2 μ, inner ℂ ψ (exponentialVector μ u) = 0)
    (n : ℕ) (u : Fin n → Lp ℂ 2 μ) :
    inner ℂ (ψ n) (symmetricTensorContinuousMultilinear μ n u) = 0 := by
  let f : ContinuousMultilinearMap ℂ (fun _ : Fin n => Lp ℂ 2 μ) ℂ :=
    (innerSL ℂ (ψ n)).compContinuousMultilinearMap
      (symmetricTensorContinuousMultilinear μ n)
  have hs (σ : Equiv.Perm (Fin n)) (v : Fin n → Lp ℂ 2 μ) :
      f (fun i => v (σ i)) = f v := by
    change inner ℂ (ψ n) (symmetricTensorContinuousMultilinear μ n (fun i => v (σ i))) =
      inner ℂ (ψ n) (symmetricTensorContinuousMultilinear μ n v)
    rw [symmetricTensorContinuousMultilinear_permutation]
  have hd (v : Lp ℂ 2 μ) : f (fun _ => v) = 0 := by
    change inner ℂ (ψ n) (symmetricTensorContinuousMultilinear μ n (fun _ => v)) = 0
    rw [symmetricTensorContinuousMultilinear_diagonal]
    exact exponentialVector_orthogonal_pureSymmetricTensor μ ψ hψ v n
  have hf : f = 0 := continuousMultilinearMap_eq_zero_of_diagonal f hs hd
  exact congrArg (fun g => g u) hf

section FiniteMeasureTotality
variable [IsFiniteMeasure μ]

/-- The full coherent family is total in the genuine Hilbert sum. -/
theorem exponentialVector_total :
    (Submodule.span ℂ (Set.range (exponentialVector μ))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro ψ hψ
  have hp (u : Lp ℂ 2 μ) : inner ℂ ψ (exponentialVector μ u) = 0 :=
    (Submodule.span ℂ (Set.range (exponentialVector μ))).inner_left_of_mem_orthogonal
      (Submodule.subset_span ⟨u, rfl⟩) hψ
  apply lp.ext
  funext n
  apply Subtype.ext
  apply mixedTensorL2_eq_zero_of_inner μ
  intro u
  have hc := exponentialVector_orthogonal_symmetricMixedTensor μ ψ hp n u
  change inner ℂ (ψ n : ProductL2 μ (Fin n))
    (symmetrizeL2 μ (mixedTensorL2 μ u)) = 0 at hc
  exact (inner_symmetricSector_symmetrize μ n (ψ n) (mixedTensorL2 μ u)).symm.trans hc

end FiniteMeasureTotality
end LiebLiniger.FixedPeriod.Quantum

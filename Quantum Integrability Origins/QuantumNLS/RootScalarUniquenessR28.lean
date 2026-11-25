import QuantumNLS.RootScalarContinuityR28

/-!
R-063C168E, `thm:root-scalar-uniqueness`,
`source-text/chapters/foundations/ROOT_scalar_uniqueness.tex:136-226`.
Every input is an arbitrary physical L2 class. The realized domain is a subtype
of the actual positive ell1 carrier with its inherited norm topology. The entire
finite scalar law is determined, and continuity is explicitly in the Jordan
total-variation norm. No statement identifies physical fields or their phases.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
namespace QuantumNLS.RootScalarUniquenessR28
open PhysicalTensor (L2T)
open RootScalarContinuityR28
open TotalVariation (tvNorm)
variable {L κ : ℝ} [Fact (0 < L)]

/-- All-L2 determination by all indexed masses, and the unique continuous
finite-measure-valued function on the realized ell1 subset. -/
theorem root_scalar_uniqueness (hκ : 0 < κ) :
    (∀ u v : L2T L,
      (∀ n : ℤ,(RootIndexedMasses.masses hκ u).1 n = (RootIndexedMasses.masses hκ v).1 n) →
        PhysicalQuantumMeasure.measure hκ u = PhysicalQuantumMeasure.measure hκ v) ∧
    (∃! F : realized (L := L) hκ → FiniteMeasure ℝ,
      (∀ u : L2T L,(F (realizedPoint hκ u) : Measure ℝ) = PhysicalQuantumMeasure.measure hκ u) ∧
      (∀ a : realized (L := L) hκ,
        Tendsto (fun b : realized (L := L) hκ => tvNorm (F b : Measure ℝ) (F a : Measure ℝ))
          (𝓝 a) (𝓝 0))) := by
  refine ⟨?_,scalarLaw hκ,⟨scalarLaw_realizedPoint hκ,scalarLaw_tv_continuous hκ⟩,?_⟩
  · intro u v he
    apply RootScalarUniqueR28.uniqueness hκ
    apply Subtype.ext
    exact lp.ext (funext he)
  · intro F hF
    funext a
    apply FiniteMeasure.toMeasure_injective
    have hp : realizedPoint hκ (realizer hκ a) = a := Subtype.ext (realizer_spec hκ a)
    calc
      (F a : Measure ℝ) = (F (realizedPoint hκ (realizer hκ a)) : Measure ℝ) :=
        congrArg (fun b => (F b : Measure ℝ)) hp.symm
      _ = PhysicalQuantumMeasure.measure hκ (realizer hκ a) := hF.1 _
      _ = (scalarLaw hκ a : Measure ℝ) := rfl

end QuantumNLS.RootScalarUniquenessR28
#print axioms QuantumNLS.RootScalarUniquenessR28.root_scalar_uniqueness

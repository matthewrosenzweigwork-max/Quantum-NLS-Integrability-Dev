import LiebLiniger.FixedPeriod.Quantum.WickRealContractionKernel

/-!
# Q2-026: norm of the actual real derivative contraction kernel

Source: LLFP-Q2-026, lines 1052–1057 of the pinned LLFP TeX. The kernel here is
exactly the same actual bounded tensor operator identified with the real
Wirtinger derivative contraction in Q2-025. The bound comes from the already
proved Hilbert tensor/symmetrizer contraction estimates, not a norm assumption.
The original-degree consumer transports only natural equalities and retains
the original A1/A2 norms. All degrees and j=0, including vacuum degrees, remain.
-/
noncomputable section
open MeasureTheory
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- The same kernel as the actual real derivative contraction has precisely
the source falling-factorial operator norm estimate. -/
theorem wickRealDerivativeContraction_kernel_norm {r j s qb pc : ℕ}
    (A1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s)) :
    (∀ u : Lp ℂ 2 μ, wickRealDerivativeContraction μ A1 A2 u =
      wickKernelPolynomial μ (tensorDerivativeContraction μ A1 A2) u) ∧
    ‖tensorDerivativeContraction μ A1 A2‖ ≤
      ((r + j).descFactorial j : ℝ) * ((j + s).descFactorial j : ℝ) * ‖A1‖ * ‖A2‖ := by
  exact ⟨wickRealDerivativeContraction_kernel μ A1 A2,
    norm_tensorDerivativeContraction_le μ A1 A2⟩

/-- Source-facing Q2-026 consumer for every original pb,qc and j≤min(pb,qc).
The two equality transports are the same ones as the checked Q2-025 consumer;
they introduce neither a new physical kernel nor an additional assumption. -/
theorem wickRealDerivativeContraction_kernel_norm_degrees {pb qb pc qc j : ℕ}
    (hj : j ≤ min pb qc)
    (A1 : SymmetricSector μ pb →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ qc) :
    ∃ (r s : ℕ) (hpb : pb = r + j) (hqc : qc = j + s),
      let B1 : SymmetricSector μ (r + j) →L[ℂ] SymmetricSector μ qb := hpb ▸ A1
      let B2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ (j + s) := hqc ▸ A2
      (∀ u : Lp ℂ 2 μ, wickRealDerivativeContraction μ B1 B2 u =
        wickKernelPolynomial μ (tensorDerivativeContraction μ B1 B2) u) ∧
      ‖tensorDerivativeContraction μ B1 B2‖ ≤
        (pb.descFactorial j : ℝ) * (qc.descFactorial j : ℝ) * ‖A1‖ * ‖A2‖ := by
  obtain ⟨r, s, hpb, hqc⟩ := (contractionDegrees_coverage pb qc j).mp hj
  subst pb
  subst qc
  exact ⟨r, s, rfl, rfl, wickRealDerivativeContraction_kernel_norm μ A1 A2⟩

end LiebLiniger.FixedPeriod.Quantum

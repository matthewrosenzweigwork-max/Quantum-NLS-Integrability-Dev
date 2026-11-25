import QuantumNLS.Gelfand
import QuantumNLS.ContactFormTheorem
import QuantumNLS.RootPlacementBound
import QuantumNLS.TraceIdeal

/-!+# EXT-025 A: named frozen-repository consequences

These wrappers preserve the hypotheses of the cited frozen theorems.
GP-07 below is the actual contact form, not a purported general Kato theorem.
GP-09 supplies the proved ideal bounds and positive-trace basis independence;
completion, cyclicity, general partial trace, and energy sandwiches remain gaps.
ROOT-01 supplies the full normalized Fourier unitary, Parseval and synthesis;
the arbitrary-exponent Sobolev consequences remain separate obligations.
ROOT-03 supplies the finite bounded-kernel Schur theorem and the exact physical
consumer bound. The arbitrary measurable-kernel sqrt(A B) theorem is not
replaced by this equal-bound special case.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped InnerProductSpace ComplexConjugate LinearPMap ENNReal ComplexOrder

namespace QuantumNLS.Ext025A

/-- GP-02 mathematical wrapper: the sequence quotient norm is exactly
the limsup, for varying C-star fibers. -/
theorem gp02_quotient_limsup (B : ℕ → Type*) [∀ n, CStarAlgebra (B n)]
    [∀ n, Nontrivial (B n)]
    (x : Gelfand.BoundedSequence B) :
    ‖Ideal.Quotient.mk (Gelfand.normNullIdeal B) x‖ =
      limsup (fun n => ‖x n‖) atTop :=
  Gelfand.sequenceQuotient_norm B x

/-- GP-02 mathematical wrapper: the generated algebra's commutative
C-star structure and isometry follow from star and commutator identities. -/
theorem gp02_generated_isometry {ι A : Type*} [CStarAlgebra A]
    (E : ι → ι → A) (hs : ∀ a b, star (E a b) = E b a)
    (hc : ∀ a b c d, Commute (E a b) (E c d)) :
    Isometry (Gelfand.generatedGelfand E hs hc) :=
  Gelfand.generatedGelfand_isometry E hs hc

/-- GP-02 mathematical wrapper: positivity, trace at most one, and the
exact minor identity imply evaluation at a vector of the finite Hilbert unit ball. -/
theorem gp02_rank_one_unit_ball {ι : Type*} [Fintype ι] {C : Matrix ι ι ℂ}
    (hC : C.PosSemidef) (ht : ∑ a, (C a a).re ≤ 1)
    (hm : ∀ a b c d, C a b * C c d = C a d * C c b) :
    ∃ z : EuclideanSpace ℂ ι,
      (∀ a b, C a b = z a * conj (z b)) ∧ ‖z‖ ≤ 1 :=
  Gelfand.exists_unitBall_vector_of_posSemidef_minors hC ht hm

section Contact
open ContactOperator ContactFormTheorem
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- GP-07 contact application: existence and uniqueness of the actual
associated selfadjoint operator. `IsAssociated` literally includes the
ambient-vector/test-vector domain characterization. -/
theorem «FIN-EXT025-GP-07» {c : ℝ} (hc : 0 ≤ c) :
    ∃! T : SymL2 L N →ₗ.[ℂ] SymL2 L N,
      IsSelfAdjoint T ∧ IsAssociated c T := by
  refine ⟨Hop c hc, ⟨Hop_isSelfAdjoint hc, Hop_isAssociated hc⟩, ?_⟩
  intro T hT
  exact eq_Hop_of_isAssociated hc T hT.1 hT.2
end Contact

section Trace
open TraceClass TraceIdeal TraceCompact
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- GP-09 proved ideal-norm clauses: two-sided bounds and adjoint
invariance in the repository's ENNReal trace-norm convention. -/
theorem «FIN-EXT025-GP-09» (W T V : E →L[ℂ] E) :
    traceNorm (W * T * V) ≤ ENNReal.ofReal ‖W‖ * traceNorm T * ENNReal.ofReal ‖V‖ ∧
      traceNorm (ContinuousLinearMap.adjoint T) = traceNorm T :=
  ⟨traceNorm_mul_mul_le W T V, traceNorm_adjoint T⟩

/-- GP-09 basis independence for positive operators, including infinite trace. -/
theorem gp09_positive_trace_basis_independent {ι κ : Type*}
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    {T : E →L[ℂ] E} (hT : T.IsPositive) : traceIn b T = traceIn c T :=
  traceIn_eq_of_basis b c hT
end Trace

section PeriodicFourier
open QuantumNLS.Fourier
variable (L : ℝ) [Fact (0 < L)]

/-- ROOT-01 normalized Fourier foundation. The domain uses physical
Lebesgue measure of mass L, not Haar probability. The inverse is onto
all of l2, and the modes have exactly the square-root normalization. -/
theorem «FIN-EXT025-ROOT-01» :
    ∃ U : Lp ℂ 2 (volume : Measure (AddCircle L)) ≃ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2,
      (∀ u n, U u n = coeff L (u : AddCircle L → ℂ) n) ∧
      (∀ u : Lp ℂ 2 (volume : Measure (AddCircle L)),
        hsNormSq L 0 (fun n => U u n) = ‖u‖ ^ 2) ∧
      (∀ u : Lp ℂ 2 (volume : Measure (AddCircle L)),
        HasSum (fun n : ℤ => coeff L (u : AddCircle L → ℂ) n • modeLp L n) u) ∧
      ∀ n : ℤ, ∀ x : ℝ, mode L n (x : AddCircle L) =
        (((Real.sqrt L)⁻¹ : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * n * x / L) := by
  exact ⟨fourierL2 L, fourierL2_apply L, hsNormSq_zero_fourierL2 L,
    hasSum_coeff_smul_modeLp L, mode_coe L⟩

/-- ROOT-01 fixed finite-sector kinetic compact embedding. This
restricts to the actual symmetric form space, retaining the physical measure. -/
theorem root01_symmetric_kinetic_embedding (N : ℕ) :
    IsCompactOperator (ContactOperator.valSym (L := L) (N := N)) :=
  ContactOperator.isCompactOperator_valSym
end PeriodicFourier

section Schur
open BetheIntegralOperator RootPlacementBound

/-- ROOT-03 bounded finite-measure equal-row/column Schur bound.
This special case suffices for the actual interlacing kernels below;
the receipt keeps the more general stated foundation OPEN. -/
theorem «FIN-EXT025-ROOT-03» {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (k : Kernel μ) (a : ℝ) (ha : 0 ≤ a)
    (hrow : ∀ x, ∫ y, ‖k.fn (x, y)‖ ∂μ ≤ a)
    (hcol : ∀ y, ∫ x, ‖k.fn (x, y)‖ ∂μ ≤ a) : ‖k.operator‖ ≤ a :=
  norm_operator_le_schur k a ha hrow hcol

/-- ROOT-03 precise application wrapper, with both kernels summed and
compressed by the physical symmetrizers, for every r at least one. -/
theorem root03_physical_interlacing_bound (L : ℝ) [Fact (0 < L)]
    {r : ℕ} (hr : 1 ≤ r) (z : ℂ) (hη : 0 < z.im) :
    ‖BethePhysicalTransfer.physicalKernel L r z‖ ≤ 2 * (z.im)⁻¹ ^ r :=
  norm_physicalKernel_le hr z hη
end Schur

end QuantumNLS.Ext025A

#print axioms QuantumNLS.Ext025A.gp02_quotient_limsup
#print axioms QuantumNLS.Ext025A.gp02_generated_isometry
#print axioms QuantumNLS.Ext025A.gp02_rank_one_unit_ball
#print axioms QuantumNLS.Ext025A.«FIN-EXT025-GP-07»
#print axioms QuantumNLS.Ext025A.«FIN-EXT025-GP-09»
#print axioms QuantumNLS.Ext025A.gp09_positive_trace_basis_independent
#print axioms QuantumNLS.Ext025A.«FIN-EXT025-ROOT-01»
#print axioms QuantumNLS.Ext025A.root01_symmetric_kinetic_embedding
#print axioms QuantumNLS.Ext025A.«FIN-EXT025-ROOT-03»
#print axioms QuantumNLS.Ext025A.root03_physical_interlacing_bound

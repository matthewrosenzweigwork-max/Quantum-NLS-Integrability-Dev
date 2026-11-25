import Mathlib
import QuantumNLS.Prop022GTensor
import QuantumNLS.Ext006KernelHilbertSchmidt
import QuantumNLS.Ext025B3PhysicalSectors
import QuantumNLS.BetheCoefficientTransform

/-! PROP-022 general-scope transport, stage G2 (fluctuations.tex:10, "All Hilbert spaces below are
complex and separable").

* `orthonormal_countable`: in a separable complex inner-product space every orthonormal family is
  countable (packing argument: distinct orthonormal vectors are at distance `√2`).
* `exists_hilbertBasis_int`: a complex separable infinite-dimensional Hilbert space has a Hilbert
  basis indexed by `ℤ`.
* `exists_unitary_L2T`: such a space is unitarily equivalent to the physical carrier `L2T L`
  (complex-linear isometric equivalence), via the fixed Fourier basis `physicalBasis L`.
* `fockSpace_L2T_eq`: the generic Fock space of G1 over `L2T L` is, definitionally, the physical
  Fock space `Ext025B3PhysicalSectors.Fock L` used by the frozen PROP-022 modules.

No basis of `H` is fixed in any later statement: the unitary is only used for transport. -/

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace

namespace QuantumNLS.Prop022GHilbert
open PhysicalTensor

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Every orthonormal family in a separable complex inner-product space is countable. -/
lemma orthonormal_countable [TopologicalSpace.SeparableSpace H] {ι : Type*} {v : ι → H}
    (hv : Orthonormal ℂ v) : Countable ι := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense H
  choose f hfD hdist using fun i => hDd.exists_dist_lt (v i) (by norm_num : (0 : ℝ) < 1 / 2)
  haveI : Countable D := hDc.to_subtype
  have hinj : Function.Injective (fun i => (⟨f i, hfD i⟩ : D)) := by
    intro i j hij
    have hfe : f i = f j := congrArg Subtype.val hij
    by_contra hne
    have h0 : ⟪v i, v j⟫_ℂ = 0 := hv.2 hne
    have hsq : ‖v i - v j‖ ^ 2 = 2 := by
      rw [@norm_sub_sq ℂ, hv.1 i, hv.1 j, h0]
      norm_num
    have h1 : dist (v i) (f i) < 1 / 2 := hdist i
    have h2 : dist (v j) (f j) < 1 / 2 := hdist j
    have htri : dist (v i) (v j) < 1 := by
      have t1 := dist_triangle (v i) (f i) (v j)
      have t2 : dist (f i) (v j) = dist (v j) (f j) := by rw [hfe, dist_comm]
      linarith
    rw [dist_eq_norm] at htri
    nlinarith [norm_nonneg (v i - v j)]
  exact Function.Injective.countable hinj

/-- A complex separable infinite-dimensional Hilbert space has a Hilbert basis indexed by `ℤ`. -/
theorem exists_hilbertBasis_int [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (hH : ¬ FiniteDimensional ℂ H) : Nonempty (HilbertBasis ℤ ℂ H) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  haveI : Countable w := orthonormal_countable b.orthonormal
  haveI : Infinite w := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    haveI := Fintype.ofFinite w
    exact hH (Module.Finite.of_basis b.toOrthonormalBasis.toBasis)
  obtain ⟨e⟩ : Nonempty (w ≃ ℤ) := nonempty_equiv_of_countable
  exact ⟨BetheCoefficientTransform.reindexBasis e b⟩

/-- **G2.** Every complex separable infinite-dimensional Hilbert space is unitarily equivalent
(complex-linear isometric equivalence) to the physical carrier `L2T L`. -/
theorem exists_unitary_L2T (L : ℝ) [Fact (0 < L)] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (hH : ¬ FiniteDimensional ℂ H) :
    Nonempty (H ≃ₗᵢ[ℂ] L2T L) := by
  obtain ⟨b⟩ := exists_hilbertBasis_int hH
  exact ⟨b.repr.trans (Ext006KernelHilbertSchmidt.physicalBasis L).repr.symm⟩

/-- Conversely `L2T L` itself is complex, separable (it has a countable Hilbert basis) and
infinite-dimensional, so G2 is exactly the class of carriers covered by transport. -/
theorem L2T_not_finiteDimensional (L : ℝ) [Fact (0 < L)] : ¬ FiniteDimensional ℂ (L2T L) := by
  intro hfin
  have hli := (Ext006KernelHilbertSchmidt.physicalBasis L).orthonormal.linearIndependent
  haveI : Finite ℤ := hli.finite
  exact (not_finite ℤ)

/-- The generic Fock space of stage G1 over `L2T L` is definitionally the physical Fock space. -/
theorem fockSpace_L2T_eq (L : ℝ) [Fact (0 < L)] :
    Prop022GTensor.FockSpace (L2T L) = Ext025B3PhysicalSectors.Fock L := rfl

/-- The identification is the identity map, sector by sector and in norm. -/
example (L : ℝ) [Fact (0 < L)] (x : Ext025B3PhysicalSectors.Fock L) :
    ‖(x : Prop022GTensor.FockSpace (L2T L))‖ = ‖x‖ := rfl

end QuantumNLS.Prop022GHilbert

#print axioms QuantumNLS.Prop022GHilbert.orthonormal_countable
#print axioms QuantumNLS.Prop022GHilbert.exists_hilbertBasis_int
#print axioms QuantumNLS.Prop022GHilbert.exists_unitary_L2T
#print axioms QuantumNLS.Prop022GHilbert.L2T_not_finiteDimensional
#print axioms QuantumNLS.Prop022GHilbert.fockSpace_L2T_eq

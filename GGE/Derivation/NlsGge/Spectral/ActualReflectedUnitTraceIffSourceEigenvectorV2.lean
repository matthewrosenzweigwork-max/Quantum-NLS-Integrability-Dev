import NlsGge.Spectral.ActualSourceEigenvectorIsReflectedMonodromyColumnV3
import NlsGge.Spectral.ActualPhysicalL2UnitEndpointRealityV1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
open scoped Matrix
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis TransportBridgeV4

/-- A nonzero graph eigenvector has nonzero initial data, proved through
the actual ODE column and source classes rather than assumed regularity. -/
theorem actualSourceEigenvector_initial_ne_zero
    (n : ℤ) (u : PhysicalL2) (z : ℂ)
    (X : recoveredActualSourceFreeWeightedDomain n) (hX : X.val ≠ 0)
    (heigen : actualSourcePerturbedDiracPMapAfterAE n u (star u) X = z • X.val) :
    actualSourceGraphContinuousVector n X 0 ≠ 0 := by
  intro hzero
  have hcolumn := actualSourceEigenvector_eq_reflectedMonodromyColumn n u z X heigen
  apply hX
  apply PiLp.ext
  intro b
  apply Lp.ext
  have hstate : ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      actualSourceGraphContinuousRepresentative n X b t = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have he := hcolumn t ⟨ht.1.le, ht.2⟩
    rw [hzero] at he
    have hi := congrArg (fun v : Fin 2 → ℂ => v (if b then 0 else 1)) he
    cases b <;> simpa only [actualSourceGraphContinuousVector,
      actualReflectedPhysicalL2ZsColumn, Matrix.mulVec_zero,
      Bool.false_eq_true, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] using hi
  filter_upwards [actualSourceGraphContinuousRepresentative_ae_source_class n X b,
    hstate, Lp.coeFn_zero ℂ 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))] with t hg hz h0
  exact hg.symm.trans (hz.trans h0.symm)

theorem actualSourceGraphContinuousVector_twisted_endpoint
    (n : ℤ) (X : recoveredActualSourceFreeWeightedDomain n) :
    actualSourceGraphContinuousVector n X 1 =
      spectralSign n • actualSourceGraphContinuousVector n X 0 := by
  funext i
  fin_cases i
  · exact (freeDomainContinuousComponent_integral_and_twistedTrace n
      (sourcePairRepr n X.val) X.property true).2
  · exact (freeDomainContinuousComponent_integral_and_twistedTrace n
      (sourcePairRepr n X.val) X.property false).2

/-- The reverse direction of the actual graph/monodromy correspondence,
with the original reflected (-u,-z) convention retained explicitly. -/
theorem actualSourceEigenvector_reflected_unit_trace
    (n : ℤ) (u : PhysicalL2) (z : ℂ)
    (X : recoveredActualSourceFreeWeightedDomain n) (hX : X.val ≠ 0)
    (heigen : actualSourcePerturbedDiracPMapAfterAE n u (star u) X = z • X.val) :
    Matrix.trace (actualComplexZsDysonTsum
      (fun t => naturalPhysicalCoverL2 (-u) (t : SpectralCircle)) (-z) 1) =
      2 * spectralSign n := by
  let v := actualSourceGraphContinuousVector n X 0
  have hv : v ≠ 0 := actualSourceEigenvector_initial_ne_zero n u z X hX heigen
  have hb : actualReflectedPhysicalL2ZsColumn u z v 1 = spectralSign n • v := by
    rw [← actualSourceEigenvector_eq_reflectedMonodromyColumn n u z X heigen 1 (by norm_num)]
    exact actualSourceGraphContinuousVector_twisted_endpoint n X
  by_cases hn : n % 2 = 0
  · have ht := (actualPhysicalL2ZsDysonTsum_fixed_vector_iff_trace_two
      (-u) (-z) 1 (by norm_num)).mp
      ⟨v, hv, by simpa [actualReflectedPhysicalL2ZsColumn, spectralSign, hn] using hb⟩
    simpa [spectralSign, hn] using ht
  · have ht := (actualPhysicalL2ZsDysonTsum_negative_vector_iff_trace_neg_two
      (-u) (-z) 1 (by norm_num)).mp
      ⟨v, hv, by simpa [actualReflectedPhysicalL2ZsColumn, spectralSign, hn] using hb⟩
    simpa [spectralSign, hn] using ht

/-- Exact correspondence between signed unit trace and a nonzero eigenvector
of the actual rough physical source operator on its genuine weighted domain.
No compact-spectrum, labeling, gap, or action conclusion is asserted. -/
theorem actualReflectedPhysicalL2UnitTrace_iff_source_eigenvector
    (n : ℤ) (u : PhysicalL2) (z : ℂ) :
    Matrix.trace (actualComplexZsDysonTsum
      (fun t => naturalPhysicalCoverL2 (-u) (t : SpectralCircle)) (-z) 1) =
      2 * spectralSign n ↔
    ∃ X : recoveredActualSourceFreeWeightedDomain n, X.val ≠ 0 ∧
      actualSourcePerturbedDiracPMapAfterAE n u (star u) X = z • X.val := by
  constructor
  · exact actualReflectedPhysicalL2UnitTrace_exists_source_eigenvector n u z
  · rintro ⟨X, hX, heigen⟩
    exact actualSourceEigenvector_reflected_unit_trace n u z X hX heigen

end NlsGge.SpectralFoundations
end

import NlsGge.Spectral.ActualReflectedPhysicalL2ColumnOperatorEigenpairV2
import NlsGge.Spectral.ActualPhysicalL2ZsEndpointTraceCriterionV2
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis
open NlsGge.Schur.TransportBridgeV4

/-- Actual rough-potential source eigenvalues are real by the proved formal
symmetry on the proper weighted domain, without a compactness hypothesis. -/
theorem actualSourcePerturbedDirac_eigenvalue_im_eq_zero
    (n : ℤ) (u : PhysicalL2) (z : ℂ)
    (x : recoveredActualSourceFreeWeightedDomain n) (hx : x.val ≠ 0)
    (heigen : actualSourcePerturbedDiracPMapAfterAE n u (star u) x = z • x.val) :
    z.im = 0 := by
  have hsym := actualSourcePerturbedDirac_formalSelfAdjoint_of_physical_slice
    n u (star u) rfl x x
  rw [heigen, inner_smul_left, inner_smul_right] at hsym
  have hi : inner ℂ x.val x.val ≠ 0 := inner_self_ne_zero.mpr hx
  have hz : star z = z := mul_right_cancel₀ hi hsym
  exact Complex.conj_eq_iff_im.mp hz

/-- The actual reflected unit monodromy signed endpoint trace produces a
nonzero vector in the genuine source graph domain and its true eigenaction.
This is the forward implication; no reverse spectrum/gap labeling assumed. -/
theorem actualReflectedPhysicalL2UnitTrace_exists_source_eigenvector
    (n : ℤ) (u : PhysicalL2) (z : ℂ)
    (htrace : Matrix.trace (actualComplexZsDysonTsum
      (fun t => naturalPhysicalCoverL2 (-u) (t : SpectralCircle)) (-z) 1) =
      2 * spectralSign n) :
    ∃ x : recoveredActualSourceFreeWeightedDomain n, x.val ≠ 0 ∧
      actualSourcePerturbedDiracPMapAfterAE n u (star u) x = z • x.val := by
  have hvec : ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
      actualReflectedPhysicalL2ZsColumn u z v 1 = spectralSign n • v := by
    by_cases hn : n % 2 = 0
    · have ht : Matrix.trace (actualComplexZsDysonTsum
          (fun t => naturalPhysicalCoverL2 (-u) (t : SpectralCircle)) (-z) 1) = 2 := by
        simpa [spectralSign, hn] using htrace
      obtain ⟨v, hv, hb⟩ :=
        (actualPhysicalL2ZsDysonTsum_fixed_vector_iff_trace_two
          (-u) (-z) 1 (by norm_num)).mpr ht
      exact ⟨v, hv, by simpa [actualReflectedPhysicalL2ZsColumn, spectralSign, hn] using hb⟩
    · have ht : Matrix.trace (actualComplexZsDysonTsum
          (fun t => naturalPhysicalCoverL2 (-u) (t : SpectralCircle)) (-z) 1) = -2 := by
        simpa [spectralSign, hn] using htrace
      obtain ⟨v, hv, hb⟩ :=
        (actualPhysicalL2ZsDysonTsum_negative_vector_iff_trace_neg_two
          (-u) (-z) 1 (by norm_num)).mpr ht
      exact ⟨v, hv, by simpa [actualReflectedPhysicalL2ZsColumn, spectralSign, hn] using hb⟩
  obtain ⟨v, hv, hb⟩ := hvec
  exact ⟨actualReflectedPhysicalL2ColumnSourceDomainElement n u z v hb,
    actualReflectedPhysicalL2ColumnSourcePair_ne_zero u z v hv,
    actualReflectedPhysicalL2Column_actualSourceOperator_eigenaction n u z v hb⟩

theorem actualReflectedPhysicalL2UnitTrace_endpoint_im_eq_zero
    (n : ℤ) (u : PhysicalL2) (z : ℂ)
    (htrace : Matrix.trace (actualComplexZsDysonTsum
      (fun t => naturalPhysicalCoverL2 (-u) (t : SpectralCircle)) (-z) 1) =
      2 * spectralSign n) : z.im = 0 := by
  obtain ⟨x, hx, heigen⟩ := actualReflectedPhysicalL2UnitTrace_exists_source_eigenvector n u z htrace
  exact actualSourcePerturbedDirac_eigenvalue_im_eq_zero n u z x hx heigen

/-- Every signed unit endpoint of the original, unreflected physical L²
Zakharov-Shabat trace is real. The (-u,-z) sign bridge is applied twice; the
manuscript operator convention is not silently changed. -/
theorem actualPhysicalL2UnitTrace_endpoint_im_eq_zero
    (n : ℤ) (u : PhysicalL2) (z : ℂ)
    (htrace : Matrix.trace (actualComplexZsDysonTsum
      (fun t => naturalPhysicalCoverL2 u (t : SpectralCircle)) z 1) =
      2 * spectralSign n) : z.im = 0 := by
  have h := actualReflectedPhysicalL2UnitTrace_endpoint_im_eq_zero n (-u) (-z)
    (by simpa only [neg_neg] using htrace)
  simpa only [Complex.neg_im, neg_eq_zero] using h

end NlsGge.SpectralFoundations
end

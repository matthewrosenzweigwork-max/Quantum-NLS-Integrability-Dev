/-
QuantumNLS.PlacementCovariance — slot transport for the LOCAL-011 grouping.

This file records the operator-level covariance needed to regroup the frozen
actual pair-placement sum.  The transport is derived from the pinned tensor
permutation representation and the existing subset-placement definition.
-/
import QuantumNLS.PlacementProduct

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct

noncomputable section

namespace QuantumNLS.PlacementCovariance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem permHilbertIsometry_mul_apply {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) (x : HilbertTensorPower ℂ H n) :
    permHilbertIsometry (𝕜 := ℂ) (E := H) σ
        (permHilbertIsometry (𝕜 := ℂ) (E := H) τ x) =
      permHilbertIsometry (𝕜 := ℂ) (E := H) (σ * τ) x := by
  have h := map_mul (permHom ℂ H n) σ τ
  simpa [permHom] using (congrArg (fun f : _ ≃ₗᵢ[ℂ] _ => f x) h).symm

/-- Conjugating a concrete placement carries its slot permutation along by
left multiplication.  This is the operator transport used below; it is
proved from the frozen permutation representation, not postulated. -/
theorem permutedPlacement_transport {p q : ℕ}
    [CompleteSpace H]
    (σ τ : Equiv.Perm (Fin (p + q)))
    (A : BoundedSymmetricKernel H p) :
    (permRep ℂ H (p + q) σ :
      HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q)).comp
        (permutedPlacement τ A) =
      (permutedPlacement (σ * τ) A).comp
        (permRep ℂ H (p + q) σ :
          HilbertTensorPower ℂ H (p + q) →L[ℂ] HilbertTensorPower ℂ H (p + q)) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, permutedPlacement, permRep_apply]
  rw [permHilbertIsometry_mul_apply]
  congr 2
  rw [permHilbertIsometry_mul_apply]
  simp [mul_assoc]

/-! The next lemma is the form needed for the finite overlap fibers: once an
ordered product has been moved to the union slots, compression to the global
symmetric sector removes the choice of slot labels. -/

/-- The symmetric-sector compression of a full-tensor operator is unchanged
by conjugating that operator with a slot permutation. -/
theorem symmetricCompression_conj_eq {n : ℕ}
    (σ : Equiv.Perm (Fin n))
    (T : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) :
    (symProjToSector n).comp
      ((((permRep ℂ H n σ :
          HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n).comp T).comp
        ((permRep ℂ H n σ⁻¹ :
          HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n).comp
          (SymSector ℂ H n).subtypeL))) =
      (symProjToSector n).comp (T.comp (SymSector ℂ H n).subtypeL) := by
  let U : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n :=
    permRep ℂ H n σ
  let Ui : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n :=
    permRep ℂ H n σ⁻¹
  change (symProjToSector n).comp ((U.comp T).comp
      (Ui.comp (SymSector ℂ H n).subtypeL)) =
    (symProjToSector n).comp (T.comp (SymSector ℂ H n).subtypeL)
  ext x
  have hinput : Ui x.1 = x.1 := x.property σ⁻¹
  have hproject (y : HilbertTensorPower ℂ H n) :
      symProjToSector n (U y) =
        symProjToSector n y := by
    apply Subtype.ext
    change symProj ℂ H n (U y) = symProj ℂ H n y
    have h := congrArg (fun F : HilbertTensorPower ℂ H n →L[ℂ]
        HilbertTensorPower ℂ H n => F y)
      (TensorCarrier.groupAverage_mul_rep (permRep ℂ H n) σ)
    simpa [symProj] using h
  have hcompressed := hproject (T (Ui x.1))
  rw [congrArg T hinput] at hcompressed
  simpa [ContinuousLinearMap.comp_apply, hinput] using
    congrArg Subtype.val hcompressed

end QuantumNLS.PlacementCovariance

#print axioms QuantumNLS.PlacementCovariance.permutedPlacement_transport
#print axioms QuantumNLS.PlacementCovariance.symmetricCompression_conj_eq

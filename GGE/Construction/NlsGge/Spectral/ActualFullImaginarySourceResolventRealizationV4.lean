import NlsGge.Spectral.ActualFullImaginaryFreeSourceResolventV3
import NlsGge.Schur.SourcePhysicalFreeResolventRealizationV1

set_option autoImplicit false

noncomputable section

namespace NlsGge.Schur

/-- The all-mode imaginary resolvent output has actual source weak derivatives
in both reflected components, by the existing exact free-domain
characterization. -/
theorem sourceFullImaginaryResolventSquare_actual_twisted_weak_domain
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SectorSquare n) :
    ∃ G : Bool → SourceIntervalL2, ∀ upper, SourceTwistedWeakDerivative n
      (sourceCoordinateComponent n (sourceFullImaginaryResolventSquare n y hy x) upper)
      (G upper) :=
  (sourceFreeDomain_twisted_weak_derivative_iff n
    (sourceFullImaginaryResolventSquare n y hy x)).mp
    (sourceFullImaginaryResolventSquare_mem_freeWeightedDomain n y hy x)

/-- Actual right inverse of `i y - L₀` on every reflected source component.
The all-mode sequence resolvent is transferred through the existing source
coordinate representation and the actual weak derivative, with no resonant
mode exception. -/
theorem sourceFullImaginaryResolventSquare_source_right_inverse
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y) (x : SectorSquare n) (upper : Bool) :
    (Complex.I * (y : ℂ)) •
        sourceCoordinateComponent n
          (sourceFullImaginaryResolventSquare n y hy x) upper -
      sourceFreeDiracAction n (sourceFullImaginaryResolventSquare n y hy x)
        (sourceFullImaginaryResolventSquare_mem_freeWeightedDomain n y hy x) upper =
      sourceCoordinateComponent n x upper := by
  have hc := sourceFullImaginaryResolventSquare_right_inverse n y hy x
  have h := congrArg (fun v : SectorSquare n => sourceCoordinateComponent n v upper) hc
  change sourceCoordinateComponent n
      ((Complex.I * (y : ℂ)) • sourceFullImaginaryResolventSquare n y hy x -
        freeCoordinateDirac n
          ⟨sourceFullImaginaryResolventSquare n y hy x,
            sourceFullImaginaryResolventSquare_mem_freeWeightedDomain n y hy x⟩)
        upper = _ at h
  rw [sourceCoordinateComponent_sub, sourceCoordinateComponent_smul,
    ← sourceFreeDiracAction_eq_coordinate] at h
  exact h

/-- Actual left inverse on the precise source weak-derivative domain, stated
componentwise in the source realization. -/
theorem sourceFullImaginaryResolventSquare_source_left_inverse
    (n : ℤ) (y : ℝ) (hy : 1 ≤ y)
    (x : freeWeightedDomainPointwise n) (upper : Bool) :
    sourceCoordinateComponent n
      (sourceFullImaginaryResolventSquare n y hy
        (freeShiftedCoordinateDirac n (Complex.I * (y : ℂ)) x)) upper =
      sourceCoordinateComponent n x.val upper := by
  exact congrArg (fun v : SectorSquare n => sourceCoordinateComponent n v upper)
    (sourceFullImaginaryResolventSquare_left_inverse n y hy x)

end NlsGge.Schur

end

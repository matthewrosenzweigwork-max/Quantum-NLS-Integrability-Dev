import NlsGge.Schur.SourceFreeDomainTwistedWeakDerivativeIffV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.Schur

/-- Actual source Dirac action: -i d/dt on the upper component, +i d/dt
on the reflected lower component. It is defined only on the proper domain. -/
def sourceFreeDiracAction (n : ℤ) (x : SectorSquare n)
    (hx : x ∈ freeWeightedDomainPointwise n) (upper : Bool) : SourceIntervalL2 :=
  (if upper then -Complex.I else Complex.I) •
    sourceFreeCoordinateDerivative n x hx upper

lemma sourceFreeDiracAction_eq_coordinate (n : ℤ) (x : SectorSquare n)
    (hx : x ∈ freeWeightedDomainPointwise n) (upper : Bool) :
    sourceFreeDiracAction n x hx upper =
      sourceCoordinateComponent n (freeCoordinateDirac n ⟨x,hx⟩) upper := by
  cases upper <;>
    simp [sourceFreeDiracAction, sourceFreeCoordinateDerivative, smul_smul,
      neg_mul, mul_neg, Complex.I_mul_I]

lemma sourceCoordinateComponent_sub (n : ℤ) (x y : SectorSquare n) (upper : Bool) :
    sourceCoordinateComponent n (x-y) upper =
      sourceCoordinateComponent n x upper - sourceCoordinateComponent n y upper := by
  unfold sourceCoordinateComponent
  rw [(parityPairRepr n).symm.map_sub]
  change scalarParityRestrict n (((parityPairRepr n).symm x upper) -
    ((parityPairRepr n).symm y upper)) = _
  exact (scalarParityRestrict n).map_sub _ _

/-- The constructed complementary diagonal maps every actual L² field to
an actual source weak-derivative domain, rather than merely a sequence space. -/
theorem freeResolventSquare_actual_twisted_weak_domain
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (x : SectorSquare n) :
    ∃ G : Bool → SourceIntervalL2, ∀ upper, SourceTwistedWeakDerivative n
      (sourceCoordinateComponent n (freeResolventSquare n z hz x) upper) (G upper) :=
  (sourceFreeDomain_twisted_weak_derivative_iff n (freeResolventSquare n z hz x)).mp
    (freeResolventSquare_mem_freeWeightedDomain n z hz x)

/-- Actual right inverse of z-L0 on the complementary source field, with
L0 realized by its genuine weak derivative in both reflected components. -/
theorem freeResolventSquare_source_right_inverse
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (x : SectorSquare n) (upper : Bool) :
    z • sourceCoordinateComponent n (freeResolventSquare n z hz x) upper -
      sourceFreeDiracAction n (freeResolventSquare n z hz x)
        (freeResolventSquare_mem_freeWeightedDomain n z hz x) upper =
      sourceCoordinateComponent n (complementarySquare n x) upper := by
  have hc := freeShiftedCoordinateDirac_right_inverse_complement n z hz x
  have h := congrArg (fun y : SectorSquare n => sourceCoordinateComponent n y upper) hc
  change sourceCoordinateComponent n
    (z • freeResolventSquare n z hz x - freeCoordinateDirac n
      ⟨freeResolventSquare n z hz x, freeResolventSquare_mem_freeWeightedDomain n z hz x⟩) upper = _ at h
  rw [sourceCoordinateComponent_sub, sourceCoordinateComponent_smul,
    ← sourceFreeDiracAction_eq_coordinate] at h
  exact h

/-- Actual left inverse on the proper source domain. The coordinate argument
is the source z-L0 action by the equality already proved above. -/
theorem freeResolventSquare_source_left_inverse
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (x : freeWeightedDomainPointwise n) (upper : Bool) :
    sourceCoordinateComponent n
      (freeResolventSquare n z hz (freeShiftedCoordinateDirac n z x)) upper =
      sourceCoordinateComponent n (complementarySquare n x.val) upper := by
  exact congrArg (fun y : SectorSquare n => sourceCoordinateComponent n y upper)
    (freeShiftedCoordinateDirac_left_inverse_complement n z hz x)

end NlsGge.Schur

import NlsGge.Schur.SourceTwistedWeakDerivativeFourierCriterionV1
import NlsGge.Schur.FreeResolventRealRpowTwoIdentity
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NlsGge.Schur

lemma sourceCoordinateComponent_scalarCoefficient
    (n : ℤ) (x : SectorSquare n) (upper : Bool) (m : Sector n) :
    sourceScalarCoefficient n (sourceCoordinateComponent n x upper)
      (mixedIndex n (upper,m)) = x (upper,m) := by
  unfold sourceScalarCoefficient sourceCoordinateComponent
  change scalarParityRepr n
      ((scalarParityIntervalEquiv n).symm
        ((scalarParityIntervalEquiv n) ((parityPairRepr n).symm x upper)))
      (mixedIndex n (upper,m)) = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  calc
    _ = parityPairRepr n ((parityPairRepr n).symm x) (upper,m) :=
      (parityPairRepr_apply n ((parityPairRepr n).symm x) (upper,m)).symm
    _ = _ := congrArg (fun y : SectorSquare n => y (upper,m))
      ((parityPairRepr n).apply_symm_apply x)

lemma spectralCenter_neg_identity (m : ℤ) :
    spectralCenter (-m) = -spectralCenter m := by
  simp [spectralCenter]

/-- The actual weak derivative in both reflected source channels forces the
proper free coordinate domain. Square-summability is proved, not assumed. -/
theorem sourceFreeDomain_of_twisted_weak_derivatives
    (n : ℤ) (x : SectorSquare n) (G : Bool → SourceIntervalL2)
    (hweak : ∀ upper, SourceTwistedWeakDerivative n
      (sourceCoordinateComponent n x upper) (G upper)) :
    x ∈ freeWeightedDomainPointwise n := by
  have hs (upper : Bool) : Summable (fun m : Sector n =>
      ‖spectralCenter m.val * sourceScalarCoefficient n
        (sourceCoordinateComponent n x upper) m‖ ^ 2) := by
    have h := sourceTwistedWeakDerivative_weighted_coordinates_memLp n
      (sourceCoordinateComponent n x upper) (G upper) (hweak upper)
    have hh := h.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, real_rpow_two_eq_pow] using hh
  have hcomponent (upper : Bool) : Summable (fun m : Sector n =>
      ‖spectralCenter m.val * x (upper,m)‖ ^ 2) := by
    cases upper
    · have hr := (hs false).comp_injective (negateEquiv n).injective
      apply hr.congr
      intro m
      have hc := sourceCoordinateComponent_scalarCoefficient n x false m
      simp only [mixedIndex, Bool.false_eq_true, if_false] at hc
      change ‖spectralCenter (negateIndex n m).val *
        sourceScalarCoefficient n (sourceCoordinateComponent n x false) (negateIndex n m)‖ ^ 2 = _
      have he := congrArg (fun z : ℂ => ‖spectralCenter (-m.val) * z‖ ^ 2) hc
      simpa only [negateIndex_val, spectralCenter_neg_identity, neg_mul, norm_neg] using! he
    · apply (hs true).congr
      intro m
      have hc := sourceCoordinateComponent_scalarCoefficient n x true m
      have hc' : sourceScalarCoefficient n (sourceCoordinateComponent n x true) m =
          x (true,m) := by simpa only [mixedIndex, if_true] using! hc
      exact congrArg (fun z : ℂ => ‖spectralCenter m.val * z‖ ^ 2) hc' 
  have hsum : Summable (fun i : Bool × Sector n =>
      ‖spectralCenter i.2.val * x i‖ ^ 2) := by
    apply (summable_prod_of_nonneg (fun i => sq_nonneg _)).2
    exact ⟨hcomponent, (hasSum_fintype _).summable⟩
  change Memℓp (freeWeightedCoordinates n x) 2
  apply (memℓp_gen_iff (p := (2 : ℝ≥0∞))
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2
  simpa only [freeWeightedCoordinates, ENNReal.toReal_ofNat, real_rpow_two_eq_pow] using hsum

/-- Exact iff between the proper free domain and the existence of actual L²
weak derivatives against all twisted source tests, in both reflected channels.
This is a concrete domain realization; it does not claim global NLS spectral
or action-coordinate results. -/
theorem sourceFreeDomain_twisted_weak_derivative_iff
    (n : ℤ) (x : SectorSquare n) :
    x ∈ freeWeightedDomainPointwise n ↔
      ∃ G : Bool → SourceIntervalL2, ∀ upper, SourceTwistedWeakDerivative n
        (sourceCoordinateComponent n x upper) (G upper) := by
  constructor
  · intro hx
    exact ⟨fun upper => sourceFreeCoordinateDerivative n x hx upper,
      fun upper => sourceFreeDomain_has_twisted_weak_derivative n x hx upper⟩
  · rintro ⟨G,hG⟩
    exact sourceFreeDomain_of_twisted_weak_derivatives n x G hG

end NlsGge.Schur

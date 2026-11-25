import NlsGge.Atomic.LIB.LIB035
import NlsGge.Atomic.LIB.LIB038

/-! Every bounded resolvent of the actual complex-potential ZS realization factors
through the genuine interval H1 graph. The graph estimate proves boundedness of
the lift; compactness follows from the accepted no-boundary interval inclusion. -/

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace NlsGge.Atomic.LIB040
open NlsGge.Schur NlsGge.Atomic.Interval
open NlsGge.Atomic.LIB031 NlsGge.Atomic.LIB032 NlsGge.Atomic.LIB033
open NlsGge.Atomic.LIB035 NlsGge.Atomic.LIB038

/-- Identify the actual graph norm with the already proved squared-energy norm. -/
lemma intervalPairOfLiteral_norm (g : H1Pair) :
    ‖intervalPairOfLiteral g‖ = h1Norm g := by
  apply (sq_eq_sq₀ (norm_nonneg _) (show 0 ≤ h1Norm g from Real.sqrt_nonneg _)).1
  rw [intervalPairOfLiteral_energy, h1Norm_sq, pairValue_norm_sq, pairDerivative_norm_sq]
  simp only [Fintype.sum_bool]
  ring

lemma intervalPairToLiteral_value (f : IntervalPairH1) :
    h1PairValue (intervalPairLiteralEquiv.symm f) = intervalH1ToL2 f := by
  have h := intervalPairOfLiteral_value (intervalPairLiteralEquiv.symm f)
  rw [show intervalPairOfLiteral (intervalPairLiteralEquiv.symm f) = f from
    intervalPairLiteralEquiv.apply_symm_apply f] at h
  exact h.symm

/-- The inclusion is injective because the actual L2 value determines its weak derivative. -/
lemma intervalH1ToL2_injective : Function.Injective intervalH1ToL2 := by
  intro f g h
  apply intervalPairLiteralEquiv.symm.injective
  apply h1PairValue_injective
  rw [intervalPairToLiteral_value, intervalPairToLiteral_value]
  exact h

section RightInverse
variable (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ)
  (T : SourcePairL2 →L[ℂ] SourcePairL2)
  (hr : ∀ f : SourcePairL2, ∃ hf : T f ∈ (zsRealization φ bc).domain,
    z • T f - zsRealization φ bc ⟨T f, hf⟩ = f)

/-- The same actual domain witness supplied by the right inverse, lifted to its unique weak graph. -/
def rightInverseLiteral (f : SourcePairL2) : H1Pair :=
  domainLift (⟨T f, (hr f).choose⟩ : (zsRealization φ bc).domain)

lemma rightInverseLiteral_value (f : SourcePairL2) :
    h1PairValue (rightInverseLiteral φ bc z T hr f) = T f :=
  domainLift_value _

lemma rightInverseLiteral_boundary (f : SourcePairL2) :
    HasZSBoundaryCondition bc (rightInverseLiteral φ bc z T hr f) :=
  domainLift_boundary _

lemma rightInverseLiteral_equation (f : SourcePairL2) :
    z • T f - zsApply φ (rightInverseLiteral φ bc z T hr f) = f :=
  (hr f).choose_spec

lemma rightInverseLiteral_action (f : SourcePairL2) :
    zsApply φ (rightInverseLiteral φ bc z T hr f) = z • T f - f := by
  have h := rightInverseLiteral_equation φ bc z T hr f
  apply eq_sub_iff_add_eq.mpr
  exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp h).symm

/-- Actual normed-H1 lift, constructed from domain membership before any boundedness claim. -/
def rightInverseH1Value (f : SourcePairL2) : IntervalPairH1 :=
  intervalPairOfLiteral (rightInverseLiteral φ bc z T hr f)

lemma rightInverseH1Value_value (f : SourcePairL2) :
    intervalH1ToL2 (rightInverseH1Value φ bc z T hr f) = T f := by
  rw [rightInverseH1Value, intervalPairOfLiteral_value, rightInverseLiteral_value]

lemma rightInverseH1Value_add (f g : SourcePairL2) :
    rightInverseH1Value φ bc z T hr (f + g) =
      rightInverseH1Value φ bc z T hr f + rightInverseH1Value φ bc z T hr g := by
  apply intervalH1ToL2_injective
  rw [intervalH1ToL2.map_add, rightInverseH1Value_value, rightInverseH1Value_value,
    rightInverseH1Value_value, T.map_add]

lemma rightInverseH1Value_smul (c : ℂ) (f : SourcePairL2) :
    rightInverseH1Value φ bc z T hr (c • f) = c • rightInverseH1Value φ bc z T hr f := by
  apply intervalH1ToL2_injective
  rw [intervalH1ToL2.map_smul, rightInverseH1Value_value, rightInverseH1Value_value, T.map_smul]

lemma rightInverseH1Value_norm_le (f : SourcePairL2) :
    ‖rightInverseH1Value φ bc z T hr f‖ ≤
      (graphBoundConstant ‖φ‖ * ((‖z‖ + 1) * ‖T‖ + 1)) * ‖f‖ := by
  let g := rightInverseLiteral φ bc z T hr f
  have hC : 0 ≤ graphBoundConstant ‖φ‖ := graphBoundConstant_nonneg (norm_nonneg φ)
  have hg := zs_h1Norm_le_graph (norm_nonneg φ) φ le_rfl g
  have hv : h1PairValue g = T f := rightInverseLiteral_value φ bc z T hr f
  have ha : zsApply φ g = z • T f - f := rightInverseLiteral_action φ bc z T hr f
  calc
    _ = h1Norm g := intervalPairOfLiteral_norm g
    _ ≤ graphBoundConstant ‖φ‖ * (‖zsApply φ g‖ + ‖h1PairValue g‖) := hg
    _ = graphBoundConstant ‖φ‖ * (‖z • T f - f‖ + ‖T f‖) := by rw [hv, ha]
    _ ≤ graphBoundConstant ‖φ‖ * ((‖z‖ * ‖T f‖ + ‖f‖) + ‖T f‖) := by
      have haBound : ‖z • T f - f‖ ≤ ‖z‖ * ‖T f‖ + ‖f‖ := by
        simpa only [norm_smul] using norm_sub_le (z • T f) f
      exact mul_le_mul_of_nonneg_left (_root_.add_le_add haBound (le_refl ‖T f‖)) hC
    _ = graphBoundConstant ‖φ‖ * ((‖z‖ + 1) * ‖T f‖ + ‖f‖) := by ring
    _ ≤ graphBoundConstant ‖φ‖ * ((‖z‖ + 1) * (‖T‖ * ‖f‖) + ‖f‖) := by
      exact mul_le_mul_of_nonneg_left
        (_root_.add_le_add (mul_le_mul_of_nonneg_left (T.le_opNorm f)
          (show 0 ≤ ‖z‖ + 1 by positivity)) (le_refl ‖f‖)) hC
    _ = _ := by ring

/-- The bounded complex-linear H1 lift at an arbitrary complex point z. -/
def rightInverseH1Lift : SourcePairL2 →L[ℂ] IntervalPairH1 :=
  LinearMap.mkContinuous
    { toFun := rightInverseH1Value φ bc z T hr
      map_add' := rightInverseH1Value_add φ bc z T hr
      map_smul' := by intro c f; exact rightInverseH1Value_smul φ bc z T hr c f }
    (graphBoundConstant ‖φ‖ * ((‖z‖ + 1) * ‖T‖ + 1))
    (fun f => by
      change ‖rightInverseH1Value φ bc z T hr f‖ ≤ _
      exact rightInverseH1Value_norm_le φ bc z T hr f)

@[simp] lemma rightInverseH1Lift_value (f : SourcePairL2) :
    intervalH1ToL2 (rightInverseH1Lift φ bc z T hr f) = T f :=
  rightInverseH1Value_value φ bc z T hr f

lemma rightInverseH1Lift_norm_le (f : SourcePairL2) :
    ‖rightInverseH1Lift φ bc z T hr f‖ ≤
      (graphBoundConstant ‖φ‖ * ((‖z‖ + 1) * ‖T‖ + 1)) * ‖f‖ :=
  rightInverseH1Value_norm_le φ bc z T hr f

lemma rightInverse_factorization :
    intervalH1ToL2.comp (rightInverseH1Lift φ bc z T hr) = T := by
  apply ContinuousLinearMap.ext
  intro f
  exact rightInverseH1Lift_value φ bc z T hr f

include hr in
/-- Every bounded right inverse has the genuine compact H1 factorization. -/
theorem zs_bounded_rightInverse_isCompact : IsCompactOperator T := by
  have h := interval_h1_l2_compact.comp_clm (rightInverseH1Lift φ bc z T hr)
  change IsCompactOperator (intervalH1ToL2.comp (rightInverseH1Lift φ bc z T hr)) at h
  rwa [rightInverse_factorization] at h

end RightInverse

/-- Actual full inverse witnesses are unique: use the left inverse on the second right inverse. -/
lemma boundedInverse_eq (A : SourcePairL2 →ₗ.[ℂ] SourcePairL2) (z : ℂ)
    (T S : SourcePairL2 →L[ℂ] SourcePairL2)
    (hT : ∀ u : A.domain, T (z • (u : SourcePairL2) - A u) = u)
    (hS : ∀ f : SourcePairL2, ∃ hf : S f ∈ A.domain, z • S f - A ⟨S f, hf⟩ = f) :
    T = S := by
  apply ContinuousLinearMap.ext
  intro f
  obtain ⟨hf, hact⟩ := hS f
  have h := hT ⟨S f, hf⟩
  rw [hact] at h
  exact h

/-- The genuine bounded resolvent at any actual resolvent point; its full inverse properties follow. -/
def zsResolvent (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ)
    (hz : HasBoundedResolvent (zsRealization φ bc) z) : SourcePairL2 →L[ℂ] SourcePairL2 :=
  hz.choose

lemma zsResolvent_right_inverse (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ)
    (hz : HasBoundedResolvent (zsRealization φ bc) z) (f : SourcePairL2) :
    ∃ hf : zsResolvent φ bc z hz f ∈ (zsRealization φ bc).domain,
      z • zsResolvent φ bc z hz f - zsRealization φ bc ⟨zsResolvent φ bc z hz f, hf⟩ = f :=
  hz.choose_spec.1 f

lemma zsResolvent_mem_domain (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ)
    (hz : HasBoundedResolvent (zsRealization φ bc) z) (f : SourcePairL2) :
    zsResolvent φ bc z hz f ∈ (zsRealization φ bc).domain :=
  (zsResolvent_right_inverse φ bc z hz f).choose

lemma zsResolvent_right_apply (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ)
    (hz : HasBoundedResolvent (zsRealization φ bc) z) (f : SourcePairL2) :
    z • zsResolvent φ bc z hz f - zsRealization φ bc
      ⟨zsResolvent φ bc z hz f, zsResolvent_mem_domain φ bc z hz f⟩ = f :=
  (zsResolvent_right_inverse φ bc z hz f).choose_spec

lemma zsResolvent_left_inverse (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ)
    (hz : HasBoundedResolvent (zsRealization φ bc) z)
    (u : (zsRealization φ bc).domain) :
    zsResolvent φ bc z hz (z • (u : SourcePairL2) - zsRealization φ bc u) = u :=
  hz.choose_spec.2 u

/-- Comparison with any other actual bounded right inverse uses the selected full left inverse. -/
lemma zsResolvent_eq_of_rightInverse (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ)
    (hz : HasBoundedResolvent (zsRealization φ bc) z)
    (S : SourcePairL2 →L[ℂ] SourcePairL2)
    (hS : ∀ f : SourcePairL2, ∃ hf : S f ∈ (zsRealization φ bc).domain,
      z • S f - zsRealization φ bc ⟨S f, hf⟩ = f) :
    zsResolvent φ bc z hz = S :=
  boundedInverse_eq _ z _ S (zsResolvent_left_inverse φ bc z hz) hS

lemma zsResolvent_proof_independent (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ)
    (hz hz' : HasBoundedResolvent (zsRealization φ bc) z) :
    zsResolvent φ bc z hz = zsResolvent φ bc z hz' :=
  zsResolvent_eq_of_rightInverse φ bc z hz _ (zsResolvent_right_inverse φ bc z hz')

/-- The actual bounded complex H1 lift for the resolvent at every resolvent point. -/
def zsResolventH1Lift (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ)
    (hz : HasBoundedResolvent (zsRealization φ bc) z) : SourcePairL2 →L[ℂ] IntervalPairH1 :=
  rightInverseH1Lift φ bc z (zsResolvent φ bc z hz) (zsResolvent_right_inverse φ bc z hz)

@[simp] lemma zsResolventH1Lift_value (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ)
    (hz : HasBoundedResolvent (zsRealization φ bc) z) (f : SourcePairL2) :
    intervalH1ToL2 (zsResolventH1Lift φ bc z hz f) = zsResolvent φ bc z hz f :=
  rightInverseH1Lift_value φ bc z _ _ f

lemma zsResolvent_factorization (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ)
    (hz : HasBoundedResolvent (zsRealization φ bc) z) :
    intervalH1ToL2.comp (zsResolventH1Lift φ bc z hz) = zsResolvent φ bc z hz :=
  rightInverse_factorization φ bc z _ _

/-- For every complex L2 potential and all four source domains, EVERY resolvent is compact. -/
theorem zs_resolvent_isCompact (φ : SourcePairL2) (bc : ZSBoundaryCondition) (z : ℂ)
    (hz : HasBoundedResolvent (zsRealization φ bc) z) :
    IsCompactOperator (zsResolvent φ bc z hz) :=
  zs_bounded_rightInverse_isCompact φ bc z _ (zsResolvent_right_inverse φ bc z hz)

end NlsGge.Atomic.LIB040

import NlsGge.Sobolev.PhysicalWeighted
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.UniformSpace.Cauchy

/-! Derived real Hilbert bases and actual weighted norm separability. -/

set_option autoImplicit false
noncomputable section
open scoped ENNReal BigOperators

namespace NlsGge.Pilot

section Generic

variable (w : ℤ → ℝ) [Fact (∀ n : ℤ, 0 < w n)]

instance weightedRealBasisInnerProductSpace :
    @InnerProductSpace ℝ (WeightedRealHilbert w) Real.instRCLike
      (inferInstance : NormedAddCommGroup (WeightedRealHilbert w)).toSeminormedAddCommGroup := by
  letI : SeminormedAddCommGroup (WeightedRealHilbert w) :=
    (inferInstance : NormedAddCommGroup (WeightedRealHilbert w)).toSeminormedAddCommGroup
  letI : NormedSpace ℂ (WeightedRealHilbert w) :=
    weightedHilbertNormedSpace w
  letI : InnerProductSpace ℂ (WeightedRealHilbert w) :=
    weightedHilbertInnerProductSpace w
  exact InnerProductSpace.complexToReal

instance weightedRealBasisCompleteSpace : CompleteSpace (WeightedRealHilbert w) :=
  inferInstanceAs (CompleteSpace (WeightedHilbert w))

/-- One real coordinate direction, transported through the proved sqrt-weight isometry. -/
def weightedRealBasisVector (p : ℤ × Fin 2) : WeightedRealHilbert w :=
  (weightedIsometry w).symm (lp.single 2 p.1 (Complex.orthonormalBasisOneI p.2))

theorem weightedRealBasisVector_apply (p : ℤ × Fin 2) (n : ℤ) :
    (show WeightedHilbert w from weightedRealBasisVector w p) n =
      (if n = p.1 then Complex.orthonormalBasisOneI p.2 else 0) /
        (Real.sqrt (w n) : ℂ) := by
  classical
  rw [weightedRealBasisVector, weightedIsometry_symm_apply]
  simp only [lp.single_apply, Pi.single_apply]

theorem weightedRealBasisVector_inner (p : ℤ × Fin 2) (x : WeightedRealHilbert w) :
    inner ℝ (weightedRealBasisVector w p) x =
      inner ℝ (Complex.orthonormalBasisOneI p.2)
        ((weightedIsometry w) (show WeightedHilbert w from x) p.1) := by
  change (inner ℂ ((weightedIsometry w).symm
    (lp.single 2 p.1 (Complex.orthonormalBasisOneI p.2)))
    (show WeightedHilbert w from x)).re =
      (inner ℂ (Complex.orthonormalBasisOneI p.2)
        ((weightedIsometry w) (show WeightedHilbert w from x) p.1)).re
  have h := (weightedIsometry w).inner_map_map
    ((weightedIsometry w).symm (lp.single 2 p.1 (Complex.orthonormalBasisOneI p.2)))
    (show WeightedHilbert w from x)
  rw [LinearIsometryEquiv.apply_symm_apply, lp.inner_single_left] at h
  exact congrArg Complex.re h.symm

theorem weightedRealBasisVector_orthonormal : Orthonormal ℝ (weightedRealBasisVector w) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨n, j⟩ ⟨m, k⟩
  have h := weightedRealBasisVector_inner w (n, j) (weightedRealBasisVector w (m, k))
  change (inner ℂ (show WeightedHilbert w from weightedRealBasisVector w (n, j))
    (show WeightedHilbert w from weightedRealBasisVector w (m, k))).re =
      if (n, j) = (m, k) then 1 else 0
  change (inner ℂ (show WeightedHilbert w from weightedRealBasisVector w (n, j))
    (show WeightedHilbert w from weightedRealBasisVector w (m, k))).re =
      inner ℝ (Complex.orthonormalBasisOneI j)
        ((weightedIsometry w) (show WeightedHilbert w from weightedRealBasisVector w (m, k)) n) at h
  rw [h]
  change inner ℝ (Complex.orthonormalBasisOneI j)
    (((weightedIsometry w) ((weightedIsometry w).symm
      (lp.single 2 m (Complex.orthonormalBasisOneI k)))) n) =
        if (n, j) = (m, k) then 1 else 0
  rw [LinearIsometryEquiv.apply_symm_apply]
  by_cases hnm : n = m
  · subst m
    rw [lp.single_apply_self]
    simpa only [Prod.mk.injEq, true_and] using
      (orthonormal_iff_ite.mp Complex.orthonormalBasisOneI.orthonormal) j k
  · rw [lp.single_apply_ne _ _ _ hnm]
    have hpair : (n, j) ≠ (m, k) := fun h => hnm (congrArg Prod.fst h)
    simp only [inner_zero_right, if_neg hpair]

theorem weightedRealBasisVector_orthogonal_eq_bot :
    (Submodule.span ℝ (Set.range (weightedRealBasisVector w)))ᗮ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  rw [Submodule.mem_bot]
  change ∀ v ∈ Submodule.span ℝ (Set.range (weightedRealBasisVector w)),
    inner ℝ v x = 0 at hx
  have hcoord (n : ℤ) (j : Fin 2) :
      inner ℝ (Complex.orthonormalBasisOneI j)
        ((weightedIsometry w) (show WeightedHilbert w from x) n) = 0 := by
    rw [← weightedRealBasisVector_inner w (n, j) x]
    exact hx (weightedRealBasisVector w (n, j)) (Submodule.subset_span ⟨(n, j), rfl⟩)
  have hzero : (weightedIsometry w) (show WeightedHilbert w from x) = 0 := by
    apply lp.ext
    funext n
    have hz : Complex.orthonormalBasisOneI.repr
        ((weightedIsometry w) (show WeightedHilbert w from x) n) = 0 := by
      ext j
      rw [OrthonormalBasis.repr_apply_apply]
      exact hcoord n j
    apply Complex.orthonormalBasisOneI.repr.injective
    simpa only [lp.coeFn_zero, Pi.zero_apply, map_zero] using hz
  have hxzero : (show WeightedHilbert w from x) = 0 := by
    apply (weightedIsometry w).injective
    simpa only [map_zero] using hzero
  exact hxzero

/-- A genuine onto real l2 representation, derived from orthonormality and totality. -/
def weightedRealHilbertBasis : HilbertBasis (ℤ × Fin 2) ℝ (WeightedRealHilbert w) :=
  HilbertBasis.mkOfOrthogonalEqBot (weightedRealBasisVector_orthonormal w)
    (weightedRealBasisVector_orthogonal_eq_bot w)

theorem weightedRealHilbertBasis_apply (p : ℤ × Fin 2) :
    weightedRealHilbertBasis w p = weightedRealBasisVector w p := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    (weightedRealBasisVector_orthonormal w) (weightedRealBasisVector_orthogonal_eq_bot w)) p

theorem weightedRealBasisVector_dense_span :
    (Submodule.span ℝ (Set.range (weightedRealBasisVector w))).topologicalClosure = ⊤ := by
  have hfamily : (fun p => weightedRealHilbertBasis w p) = weightedRealBasisVector w :=
    funext (weightedRealHilbertBasis_apply w)
  have h := (weightedRealHilbertBasis w).dense_span
  change (Submodule.span ℝ (Set.range (fun p => weightedRealHilbertBasis w p))).topologicalClosure = ⊤ at h
  rw [hfamily] at h
  exact h

instance weightedRealBasisSeparableSpace : TopologicalSpace.SeparableSpace (WeightedRealHilbert w) := by
  have hrange : TopologicalSpace.IsSeparable (Set.range (weightedRealBasisVector w)) :=
    (Set.countable_range (weightedRealBasisVector w)).isSeparable
  have hspan : TopologicalSpace.IsSeparable
      (Submodule.span ℝ (Set.range (weightedRealBasisVector w)) :
        Set (WeightedRealHilbert w)) := hrange.span
  have hclosure : closure
      (Submodule.span ℝ (Set.range (weightedRealBasisVector w)) :
        Set (WeightedRealHilbert w)) = Set.univ := by
    rw [← Submodule.topologicalClosure_coe, weightedRealBasisVector_dense_span w]
    rfl
  apply TopologicalSpace.isSeparable_univ_iff.mp
  rw [← hclosure]
  exact hspan.closure

instance weightedRealBasisSecondCountableTopology :
    SecondCountableTopology (WeightedRealHilbert w) :=
  UniformSpace.secondCountable_of_separable (WeightedRealHilbert w)

end Generic

section Source

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

def fullWeightedHilbertBasis : HilbertBasis (ℤ × Fin 2) ℝ (FullWeightedHilbert c s) :=
  weightedRealHilbertBasis (fullModeWeight c s)

theorem fullWeightedHilbertBasis_apply (p : ℤ × Fin 2) (n : ℤ) :
    (show WeightedHilbert (fullModeWeight c s) from fullWeightedHilbertBasis c s p) n =
      (if n = p.1 then Complex.orthonormalBasisOneI p.2 else 0) /
        (Real.sqrt (fullModeWeight c s n) : ℂ) := by
  rw [fullWeightedHilbertBasis, weightedRealHilbertBasis_apply]
  exact weightedRealBasisVector_apply (fullModeWeight c s) p n

instance fullWeightedBasisSeparableSpace : TopologicalSpace.SeparableSpace (FullWeightedHilbert c s) :=
  weightedRealBasisSeparableSpace (fullModeWeight c s)

instance fullWeightedBasisSecondCountableTopology :
    SecondCountableTopology (FullWeightedHilbert c s) :=
  weightedRealBasisSecondCountableTopology (fullModeWeight c s)

instance physicalWeightedBasisSeparableSpace : TopologicalSpace.SeparableSpace (PhysicalWeighted c s) :=
  (physicalWeightedFourier c s).symm.surjective.denseRange.separableSpace
    (physicalWeightedFourier c s).symm.continuous

instance physicalWeightedBasisSecondCountableTopology :
    SecondCountableTopology (PhysicalWeighted c s) :=
  UniformSpace.secondCountable_of_separable (PhysicalWeighted c s)

end Source

end NlsGge.Pilot

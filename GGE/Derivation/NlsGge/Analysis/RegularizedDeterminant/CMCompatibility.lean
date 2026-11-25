import NlsGge.Analysis.RegularizedDeterminant.IdealAndTransport
import NlsGge.Sobolev.CMInclusionBasisIndependent
import NlsGge.Sobolev.PhysicalWeighted

/-!
Compatibility with checkpoint20's actual real CM carrier and inclusion.
The weight is the unchanged `cmModeWeight c n = 2 * sourceRate c n`.
The only regularity restriction introduced here is s > 1/2, exactly the existing
basis-image summability hypothesis; no s < 3/4 restriction is added.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace NlsGge.Analysis.RegularizedDeterminant
open NlsGge.Pilot

variable {lower upper : ℝ}

/-- The real basis instance and the original restricted-scalar normed-space
module have the same scalar action.  This is the local coherence bridge needed
to reuse checkpoint20 maps that were elaborated before `RealBasis` was imported. -/
private theorem basisModule_eq_normedSpaceModule
    (w : ℤ → ℝ) [Fact (∀ n : ℤ, 0 < w n)] :
    (NlsGge.Pilot.weightedRealBasisInnerProductSpace w).toModule =
      (inferInstance : NormedSpace ℝ (WeightedRealHilbert w)).toModule := by
  apply Module.ext'
  intro r x
  rfl

/-- Package the actual existing real inclusion, without changing its metric. -/
def cmInclusionHS (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    HilbertSchmidt (WeightedRealHilbert (cmModeWeight c)) (FullWeightedHilbert c s) :=
  HilbertSchmidt.ofCLM
    (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))) (by
      apply isHilbertSchmidt_of_summable (basis (WeightedRealHilbert (cmModeWeight c)))
      exact cmToFullWeightedHilbert_any_sourceBasis_square_summable c s hs _)

@[simp] theorem cmInclusionHS_toCLM (c : BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    (cmInclusionHS c s hs).toCLM =
      cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) := rfl

/-- The exact source basis-energy value is also the new genuine squared HS norm. -/
theorem cmInclusionHS_norm_sq (c : BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    norm (cmInclusionHS c s hs) ^ 2 =
      tsum (fun n : Int => Real.rpow (japaneseBracket n) (-2 * s)) := by
  have h1 := HilbertSchmidt.hasSum_columns_sq (cmInclusionHS c s hs)
  have h2 := cmToFullWeightedHilbert_any_sourceBasis_square_sum c s hs
    (basis (WeightedRealHilbert (cmModeWeight c)))
  exact h1.unique h2

/-- The existing physical/Fourier real isometry supplies the physical inclusion. -/
def physicalCMInclusionHS (c : BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    HilbertSchmidt (WeightedRealHilbert (cmModeWeight c)) (PhysicalWeighted c s) := by
  refine HilbertSchmidt.transport (cmInclusionHS c s hs) ?_ ?_
  · rw [basisModule_eq_normedSpaceModule (cmModeWeight c)]
    exact LinearIsometryEquiv.refl ℝ (WeightedRealHilbert (cmModeWeight c))
  · rw [basisModule_eq_normedSpaceModule (fullModeWeight c s)]
    exact (physicalWeightedFourier c s).symm

@[simp] theorem physicalCMInclusionHS_toCLM (c : BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    (physicalCMInclusionHS c s hs).toCLM =
      (physicalWeightedFourier c s).symm.toLinearIsometry.toContinuousLinearMap.comp
        (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))) := by
  have hcm := basisModule_eq_normedSpaceModule (cmModeWeight c)
  have hfull := basisModule_eq_normedSpaceModule (fullModeWeight c s)
  cases hcm
  cases hfull
  rfl

theorem physicalCMInclusionHS_norm_sq (c : BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    norm (physicalCMInclusionHS c s hs) ^ 2 =
      tsum (fun n : Int => Real.rpow (japaneseBracket n) (-2 * s)) := by
  rw [physicalCMInclusionHS, HilbertSchmidt.norm_transport, cmInclusionHS_norm_sq]

/-- The rectangular factorization needed by a future derivative realization. -/
def cmFactorHS {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (D : FullWeightedHilbert c s →L[ℝ] G) :
    HilbertSchmidt (WeightedRealHilbert (cmModeWeight c)) G := by
  refine HilbertSchmidt.postcompose ?_ (cmInclusionHS c s hs)
  rw [basisModule_eq_normedSpaceModule (fullModeWeight c s)]
  exact D

@[simp] theorem cmFactorHS_toCLM {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [CompleteSpace G]
    (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (D : FullWeightedHilbert c s →L[ℝ] G) :
    (cmFactorHS c s hs D).toCLM =
      D.comp (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))) := by
  have hfull := basisModule_eq_normedSpaceModule (fullModeWeight c s)
  cases hfull
  rfl

theorem cmFactorHS_norm_le {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [CompleteSpace G]
    (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (D : FullWeightedHilbert c s →L[ℝ] G) :
    norm (cmFactorHS c s hs D) ≤ D.opNorm * norm (cmInclusionHS c s hs) := by
  have hfull := basisModule_eq_normedSpaceModule (fullModeWeight c s)
  cases hfull
  exact HilbertSchmidt.norm_postcompose_le D (cmInclusionHS c s hs)

end NlsGge.Analysis.RegularizedDeterminant

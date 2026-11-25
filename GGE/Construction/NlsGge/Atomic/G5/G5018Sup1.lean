import Mathlib
import NlsGge.GK38.GradFundamentalL2
import NlsGge.ThirdConsultation.G5033Host

                                                                                 
                                                                        
                                                                               
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- The bilinear (non-Hermitian) pairing on `PhysicalL2` is symmetric. -/
theorem bilinPair_comm (a b : PhysicalL2) :
    inner ℂ (star a) b = inner ℂ (star b) a := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MeasureTheory.Lp.coeFn_star a, MeasureTheory.Lp.coeFn_star b] with x ha hb
  rw [ha, hb]
  simp only [Pi.star_apply, RCLike.inner_apply, RCLike.star_def, Complex.conj_conj]
  ring

/-- A functional on `PotPair` is the sum of the bilinear pairings of its gradient components. -/
theorem clm_eq_bilinPair (L : PotPair →L[ℂ] ℂ) (x : PotPair) :
    L x = inner ℂ (star (pairGradientCLM L).1) x.1 + inner ℂ (star (pairGradientCLM L).2) x.2 := by
  have h1 : L ((x.1, 0) : PotPair) = inner ℂ (star (pairGradientCLM L).1) x.1 := by
    change _ = inner ℂ (star (star ((InnerProductSpace.toDual ℂ PhysicalL2).symm
      (L.comp (ContinuousLinearMap.inl ℂ PhysicalL2 PhysicalL2))))) x.1
    rw [star_star, InnerProductSpace.toDual_symm_apply]
    rfl
  have h2 : L ((0, x.2) : PotPair) = inner ℂ (star (pairGradientCLM L).2) x.2 := by
    change _ = inner ℂ (star (star ((InnerProductSpace.toDual ℂ PhysicalL2).symm
      (L.comp (ContinuousLinearMap.inr ℂ PhysicalL2 PhysicalL2))))) x.2
    rw [star_star, InnerProductSpace.toDual_symm_apply]
    rfl
  rw [← h1, ← h2, ← map_add]
  congr 1
  ext <;> simp

/-- G5-018 support M1: the Poisson pairing of two continuous linear functionals is antisymmetric. -/
theorem pairPoissonCLM_antisymm (L M : PotPair →L[ℂ] ℂ) :
    pairPoissonCLM L M = -pairPoissonCLM M L := by
  unfold pairPoissonCLM
  rw [clm_eq_bilinPair L, clm_eq_bilinPair M]
  simp only [inner_smul_right,
    bilinPair_comm (pairGradientCLM L).1 (pairGradientCLM M).2,
    bilinPair_comm (pairGradientCLM L).2 (pairGradientCLM M).1]
  ring

end
end NlsGge.GKDefinitionDesign

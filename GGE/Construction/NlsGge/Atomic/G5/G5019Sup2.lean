import Mathlib
import NlsGge.Atomic.G5.G5019Sup1
import NlsGge.GK38.AbelianPsiNumerator
import NlsGge.GK38.DirichletRealDerivative
import NlsGge.GK38.DirichletRealAnalytic
import NlsGge.GK38.PoissonMixedTargets

                                                                                       
                                                                                         
                                                                                                                                 
                                                                                                                                    
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
namespace G5019Sup2
open G5019Sup1
noncomputable section

theorem continuous_muSeq_real (m : ℤ) :
    Continuous (fun w : PhysicalL2 => muSeq (realSlice w) m) := by
  have h : (fun w : PhysicalL2 => muSeq (realSlice w) m) = fun w => (gkMu w m : ℂ) :=
    funext fun w => muSeq_eq_gkMu38 w m
  rw [h]
  exact Complex.continuous_ofReal.comp
    (continuousOn_univ.mp (analyticOnNhd_gkMu38 m).continuousOn)

theorem continuous_dirInterpolation_mu (m : ℤ) (lam : ℂ) :
    Continuous (fun w : PhysicalL2 =>
      PoissonMixed38.dirInterpolation38 (realSlice w) (muSeq (realSlice w) m) lam) := by
  have hmap : Continuous (fun w : PhysicalL2 => (realSlice w, muSeq (realSlice w) m)) :=
    realSlice.continuous.prodMk (continuous_muSeq_real m)
  have hnum : Continuous (fun w : PhysicalL2 =>
      dslope (dirichletChar (realSlice w)) (muSeq (realSlice w) m) lam) := by
    have h := (G5019Sup1.continuous_dslope_fixed_base (fun p : PotPair × ℂ => dirichletChar p.1 p.2)
      analyticOnNhd_dirichletChar lam).comp hmap
    refine h.congr fun w => ?_
    simp only [Function.comp_apply]
    exact (G5019Sup1.dslope_symm _ _ _).symm
  have hden : Continuous (fun w : PhysicalL2 =>
      deriv (dirichletChar (realSlice w)) (muSeq (realSlice w) m)) := by
    have hD : Continuous (fun q : PotPair × ℂ =>
        fderiv ℂ (fun p : PotPair × ℂ => dirichletChar p.1 p.2) q (0, 1)) :=
      (continuousOn_univ.mp analyticOnNhd_dirichletChar.fderiv.continuousOn).clm_apply continuous_const
    refine (hD.comp hmap).congr fun w => ?_
    simp only [Function.comp_apply]
    exact (G5019Sup1.deriv_slice (fun p : PotPair × ℂ => dirichletChar p.1 p.2)
      analyticOnNhd_dirichletChar (realSlice w) _).symm
  refine hnum.div hden fun w => ?_
  rw [muSeq_eq_gkMu38]
  exact dirichlet_root_deriv_ne_zero38 w (gkMu w m) (gkMu_root38 w m)

theorem continuous_comp_realSlice_muSeq (m : ℤ) (W : Set PotPair) (G : PotPair × ℂ → ℂ)
    (hG : ContinuousOn G (W ×ˢ (univ : Set ℂ))) (hW : ∀ w : PhysicalL2, realSlice w ∈ W) :
    Continuous (fun w : PhysicalL2 => G (realSlice w, muSeq (realSlice w) m)) := by
  have hmap : Continuous (fun w : PhysicalL2 => (realSlice w, muSeq (realSlice w) m)) :=
    realSlice.continuous.prodMk (continuous_muSeq_real m)
  exact hG.comp_continuous hmap (fun w => ⟨hW w, mem_univ _⟩)

end
end G5019Sup2
end NlsGge.GKDefinitionDesign

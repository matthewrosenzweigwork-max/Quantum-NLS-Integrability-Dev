import Mathlib
import NlsGge.ThirdConsultation.G5033Host
import NlsGge.Atomic.G5.G5018Host

                                                                                       
                                                                                         
                                                                       
                                                                                                                       
                                                                                                                          
                                                                                                                
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.GKDefinitionDesign
namespace G5019Sup3
noncomputable section

theorem continuous_pairGradientCLM :
    Continuous (fun M : PotPair →L[ℂ] ℂ => pairGradientCLM M) := by
  have h1 : Continuous (fun M : PotPair →L[ℂ] ℂ =>
      M.comp (ContinuousLinearMap.inl ℂ PhysicalL2 PhysicalL2)) :=
    continuous_id.clm_comp continuous_const
  have h2 : Continuous (fun M : PotPair →L[ℂ] ℂ =>
      M.comp (ContinuousLinearMap.inr ℂ PhysicalL2 PhysicalL2)) :=
    continuous_id.clm_comp continuous_const
  have hd : Continuous (InnerProductSpace.toDual ℂ PhysicalL2).symm :=
    (InnerProductSpace.toDual ℂ PhysicalL2).symm.continuous
  have hs : Continuous (fun x : PhysicalL2 => star x) := NlsGge.GK38.starLp.continuous
  exact ((hs.comp (hd.comp h1))).prodMk (hs.comp (hd.comp h2))

theorem continuous_pairPoissonCLM :
    Continuous (fun p : (PotPair →L[ℂ] ℂ) × (PotPair →L[ℂ] ℂ) => pairPoissonCLM p.1 p.2) := by
  have hg : Continuous (fun p : (PotPair →L[ℂ] ℂ) × (PotPair →L[ℂ] ℂ) => pairGradientCLM p.2) :=
    continuous_pairGradientCLM.comp continuous_snd
  have h1 : Continuous (fun p : (PotPair →L[ℂ] ℂ) × (PotPair →L[ℂ] ℂ) =>
      (-Complex.I • (pairGradientCLM p.2).2, Complex.I • (pairGradientCLM p.2).1)) :=
    (((continuous_snd.comp hg).const_smul (-Complex.I)).prodMk
      ((continuous_fst.comp hg).const_smul Complex.I))
  exact continuous_fst.clm_apply h1

theorem continuousAt_angleIntegralDerivative_offDiag (m n : ℤ) (hmn : m ≠ n)
    (hA : AnalyticOnNhd ℂ (offDiagonalBeta n m) sourceW) (u : PhysicalL2) :
    ContinuousAt (fun w : PhysicalL2 => angleIntegralDerivative m n (realSlice w)) u := by
  have hW : realSlice u ∈ sourceW := sourceFamily.W_real (Set.mem_range_self u)
  have hfd : ContinuousOn (fderiv ℂ (offDiagonalBeta n m)) sourceW := hA.fderiv.continuousOn
  have hca : ContinuousAt (fderiv ℂ (offDiagonalBeta n m)) (realSlice u) :=
    hfd.continuousAt (sourceFamily.W_open.mem_nhds hW)
  have hfun : (fun w : PhysicalL2 => angleIntegralDerivative m n (realSlice w)) =
      fun w => fderiv ℂ (offDiagonalBeta n m) (realSlice w) := by
    funext w
    simp [angleIntegralDerivative, hmn, beta]
  rw [hfun]
  exact hca.comp (realSlice.continuous.continuousAt)

theorem continuousAt_angleIntegralDerivative_diag (n : ℤ) (u : PhysicalL2)
    (V : Set PotPair) (e : PotPair → ℂ) (hV : IsOpen V) (hu : realSlice u ∈ V)
    (he : AnalyticOnNhd ℂ e V)
    (hder : ∀ φ ∈ V, angleDerivative n φ - fderiv ℂ (betaSum n) φ = fderiv ℂ e φ) :
    ContinuousAt (fun w : PhysicalL2 => angleIntegralDerivative n n (realSlice w)) u := by
  have hfd : ContinuousOn (fderiv ℂ e) V := he.fderiv.continuousOn
  have hca : ContinuousAt (fderiv ℂ e) (realSlice u) := hfd.continuousAt (hV.mem_nhds hu)
  have hc : ContinuousAt (fun w : PhysicalL2 => fderiv ℂ e (realSlice w)) u :=
    hca.comp realSlice.continuous.continuousAt
  refine hc.congr ?_
  have hev : ∀ᶠ w in 𝓝 u, realSlice w ∈ V :=
    realSlice.continuous.continuousAt.eventually (hV.mem_nhds hu)
  filter_upwards [hev] with w hw
  simp only [angleIntegralDerivative, ite_true]
  exact (hder _ hw).symm

end
end G5019Sup3
end NlsGge.GKDefinitionDesign

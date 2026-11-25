import Mathlib
import NlsGge.Atomic.G3.G3022
import NlsGge.Atomic.G3.G3015
import NlsGge.Atomic.G3.G3016
import NlsGge.Atomic.G3.G3021
import NlsGge.Atomic.G3.G3006
import NlsGge.Atomic.G4.G4010
import NlsGge.GK38.TauGamma
import NlsGge.GK38.TauGammaSpectralDerivatives
import NlsGge.GK38.AngleDirichletAnalytic
import Armstrong.Work.RawBetaSum

                                                                                      
                                                                           
                                                                                                                            
                                                                                                                                   
                                                                              
                                                                                                                                
                                                                                                                    
                                                                                                                                    
                                                                                                          
                                                                                                                           
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G3023Aux
noncomputable section

theorem subvariety_of (g : PotPair → ℂ) (hg : AnalyticOnNhd ℂ g sourceW) :
    NlsGge.GK38.Lib.IsAnalyticSubvariety sourceW {φ : PotPair | φ ∈ sourceW ∧ g φ = 0} := by
  intro x hx
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 sourceFamily.W_open x hx
  refine ⟨r, hr, 1, fun y => fun _ => g y, ?_, fun y hy => ?_⟩
  · intro y hy
    let L : ℂ →L[ℂ] (Fin 1 → ℂ) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ ℂ
    exact (L.analyticAt (g y)).comp (hg y (hrU hy))
  · constructor
    · rintro ⟨-, h0⟩
      funext i
      exact h0
    · intro h
      exact ⟨hrU hy, congrFun h 0⟩

theorem gamma2_analytic_sourceW (m : ℤ) :
    AnalyticOnNhd ℂ (fun φ : PotPair => gamma2 φ m) sourceW :=
  (gamma2_analytic m).mono (fun φ hφ => sourceFamily.W_gk hφ)

theorem endpoint_analytic_sourceW (m : ℤ) :
    AnalyticOnNhd ℂ (fun φ : PotPair => perChar φ (muSeq φ m)) sourceW := by
  intro φ0 hφ0
  have hgk : φ0 ∈ gkW := sourceFamily.W_gk hφ0
  exact AnalyticAt.comp (g := fun p : PotPair × ℂ => perChar p.1 p.2)
    (f := fun ψ : PotPair => (ψ, muSeq ψ m))
    (analyticOnNhd_perChar_joint38 (φ0, muSeq φ0 m) (mem_univ _))
    ((analyticAt_id (𝕜 := ℂ)).prod (analyticOnNhd_muSeq_complex38 m φ0 hgk))

theorem continuousOn_sourceW (n m : ℤ) (hmn : m ≠ n) :
    ContinuousOn (offDiagonalBeta n m) sourceW := by
  intro φ0 hφ0
  by_cases hE : φ0 ∈ endpointSet m
  · exact (G3_016 n m hmn φ0 hE).2.2.continuousWithinAt
  · by_cases hZ : φ0 ∈ collapsedSet m
    · exact (G3_021 n m hmn φ0 ⟨hZ, hE⟩).1.continuousWithinAt
    · have h := (G3_015 n m hmn).1 φ0 ⟨hφ0, fun h => h.elim hZ hE⟩
      exact h.continuousAt.continuousWithinAt

end
end G3023Aux

noncomputable section

theorem G3_023 (n m : ℤ) (hmn : m ≠ n) :
  AnalyticOnNhd ℂ (offDiagonalBeta n m) sourceW ∧
  (∀ u : PhysicalL2, (offDiagonalBeta n m (realSlice u)).im = 0) ∧
  ∀ φ : SourcePotential,
    offDiagonalBeta n m φ.1 =
      gkSourceBeta38 sourceW sourceFamily.W_open sourceFamily.W_real
        sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
        sourceFamily.F_period n m hmn φ := by
  refine ⟨?_, fun u => (G3_006 u).1 n m hmn, fun φ =>
    gk151BetaAmbient_eq_source38 sourceW sourceFamily.W_open sourceFamily.W_real
      sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
      sourceFamily.F_period n m hmn φ⟩
  let V : Bool → Set PotPair := fun b => if b then collapsedSet m else endpointSet m
  have hV : ∀ i, NlsGge.GK38.Lib.IsAnalyticSubvariety sourceW (V i) := by
    intro i
    cases i
    · exact G3023Aux.subvariety_of _ (G3023Aux.endpoint_analytic_sourceW m)
    · exact G3023Aux.subvariety_of _ (G3023Aux.gamma2_analytic_sourceW m)
  have hoff : AnalyticOnNhd ℂ (offDiagonalBeta n m) (sourceW \ ⋃ i, V i) := by
    refine (G3_015 n m hmn).1.mono ?_
    intro φ hφ
    refine ⟨hφ.1, fun h => hφ.2 ?_⟩
    rw [Set.mem_iUnion]
    rcases h with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  refine NlsGge.Atomic.G4.analyticOnNhd_of_subvariety_extension (V := V) sourceFamily.W_open hV
    (G3023Aux.continuousOn_sourceW n m hmn) hoff ?_
  intro i x hx h r hr hdisc
  cases i
  · -- E_m: beta vanishes identically on the disc
    have h0 : ∀ ζ : ℂ, ‖ζ‖ < r → offDiagonalBeta n m (x + ζ • h) = 0 := fun ζ hζ =>
      (G3_016 n m hmn _ (hdisc ζ hζ).1).1
    have hnhds : ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 hr
    refine (analyticAt_const (v := (0 : ℂ))).congr ?_
    filter_upwards [hnhds] with ζ hζ
    exact (h0 ζ (by simpa using hζ)).symm
  · -- Z_m: G3_022
    have hd : ∀ z ∈ ball (0 : ℂ) r, x + z • h ∈ collapsedSet m := fun z hz =>
      (hdisc z (by simpa using hz)).1
    exact (G3_022 n m hmn x h 0 r hr hd).1 0 (mem_ball_self hr)

end
end NlsGge.GKDefinitionDesign

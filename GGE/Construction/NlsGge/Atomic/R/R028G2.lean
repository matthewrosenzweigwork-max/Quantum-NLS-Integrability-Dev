import Mathlib
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Ramer.TruncatedDivergenceLimit
import NlsGge.Ramer.TruncatedFieldConvergence
import NlsGge.Ramer.SpaceTransfer
import NlsGge.Ramer.CylindricalDivergence

                                                                                                            
                                                            

                                                                                                        
                                                                               
                                                                                                       

         
                                                                                                           
                                                                                             
                                                                                                          
                                                                                                         
                                                                                                       
                                                                                                             
  
set_option autoImplicit false

open Set Metric Filter
open scoped Topology

namespace NlsGge.ThirdConsultation.R
noncomputable section

variable {lower upper : ℝ}

/-- `ramerApprox` is local at `x`: it depends on `K` only through the value and derivative at `x`. -/
theorem r028g2_ramerApprox_eq (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (K G : RamerE c s → RamerH c) (x : RamerE c s)
    (hKG : K =ᶠ[𝓝 x] G) (N : ℕ) :
    ramerApprox c s hs K N x = ramerApprox c s hs G N x := by
  have hx : K x = G x := hKG.eq_of_nhds
  have hd : fderiv ℝ K x = fderiv ℝ G x := hKG.fderiv_eq
  unfold NlsGge.ThirdConsultation.R.ramerApprox NlsGge.Ramer.ramerA
  rw [NlsGge.Ramer.realization_coordE, hx, hd]

/-- Finite Gaussian divergence of the truncated fields at a head point depends only on the germ
of the field at the embedded head point. -/
theorem r028g2_truncField_div_eq (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (N : ℕ) (K G : RamerE c s → RamerH c) (v : NlsGge.Ramer.actualCMHead c N)
    (hKG : ∀ᶠ y in 𝓝 (NlsGge.Ramer.headToE c s N v), K y = G y) :
    NlsGge.Ramer.finiteGaussianDivergence (NlsGge.Ramer.truncField c s K N) v =
      NlsGge.Ramer.finiteGaussianDivergence (NlsGge.Ramer.truncField c s G N) v := by
  have hev : ∀ᶠ w in 𝓝 v,
      K (NlsGge.Ramer.headToE c s N w) = G (NlsGge.Ramer.headToE c s N w) :=
    ((NlsGge.Ramer.headToE c s N).continuous.continuousAt :
      ContinuousAt (NlsGge.Ramer.headToE c s N) v).tendsto.eventually hKG
  have hfun : NlsGge.Ramer.truncField c s K N =ᶠ[𝓝 v] NlsGge.Ramer.truncField c s G N := by
    filter_upwards [hev] with w hw
    simp only [NlsGge.Ramer.truncField, hw]
  have hval : NlsGge.Ramer.truncField c s K N v = NlsGge.Ramer.truncField c s G N v :=
    hfun.eq_of_nhds
  have hder : fderiv ℝ (NlsGge.Ramer.truncField c s K N) v =
      fderiv ℝ (NlsGge.Ramer.truncField c s G N) v :=
    hfun.fderiv_eq
  unfold NlsGge.Ramer.finiteGaussianDivergence
  rw [hval, hder]

/-- The head point of the coordinates of `x` converges to `x` in `E_s`. -/
theorem r028g2_headPt_tendsto (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (x : RamerE c s) :
    Tendsto (fun N : ℕ =>
      NlsGge.Ramer.headToE c s N (NlsGge.Ramer.headPt c N (NlsGge.Ramer.coordE c s x)))
      atTop (𝓝 x) := by
  have hz : ∀ n : ℤ, (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.fullModeWeight c s) from
      NlsGge.Measure.fullWeightedSequenceRealization c s (NlsGge.Ramer.coordE c s x)) n =
        NlsGge.Ramer.coordE c s x n := by
    intro n
    rw [NlsGge.Ramer.realization_coordE] <;> rfl
  have h := NlsGge.Ramer.tendsto_headToE_headPt c s (NlsGge.Ramer.coordE c s x) hz
  rw [NlsGge.Ramer.realization_coordE] at h
  exact h

/-- Literal cylindrical divergence is local at the head point of `coordE x`. -/
theorem r028g2_literalCylDiv_eq (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (K G : RamerE c s → RamerH c) (N : ℕ) (x : RamerE c s)
    (hKG : ∀ᶠ y in 𝓝 (NlsGge.Ramer.headToE c s N
      (NlsGge.Ramer.headPt c N (NlsGge.Ramer.coordE c s x))), K y = G y) :
    literalCylDiv c s K N x = literalCylDiv c s G N x := by
  unfold literalCylDiv NlsGge.Ramer.cylDiv
  exact r028g2_truncField_div_eq c s N K G _ hKG

/-- **G2 locality.** If `G = K` on `ball x₀ r`, then for `x ∈ ball x₀ (r/4)`, eventually in `N`,
`ramerApprox` and `literalCylDiv` of `K` and `G` agree at `x`. -/
theorem r028g2_locality (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (x₀ : RamerE c s) (r : ℝ) (K G : RamerE c s → RamerH c)
    (hEq : EqOn K G (ball x₀ r)) (x : RamerE c s) (hx : x ∈ ball x₀ (r / 4)) :
    ∀ᶠ N : ℕ in atTop,
      ramerApprox c s hs K N x = ramerApprox c s hs G N x ∧
        literalCylDiv c s K N x = literalCylDiv c s G N x := by
  have hxr : x ∈ ball x₀ r := by
    rw [mem_ball] at hx ⊢
    have h0 : 0 ≤ dist x x₀ := dist_nonneg
    linarith
  have hnhds : ball x₀ r ∈ 𝓝 x := isOpen_ball.mem_nhds hxr
  have hmem : ∀ᶠ N : ℕ in atTop,
      NlsGge.Ramer.headToE c s N (NlsGge.Ramer.headPt c N (NlsGge.Ramer.coordE c s x)) ∈
        ball x₀ r :=
    (r028g2_headPt_tendsto c s x).eventually (isOpen_ball.mem_nhds hxr)
  filter_upwards [hmem] with N hN
  refine ⟨?_, ?_⟩
  · exact r028g2_ramerApprox_eq c s hs K G x
      (Filter.eventually_of_mem hnhds (fun y hy => hEq hy)) N
  · exact r028g2_literalCylDiv_eq c s K G N x
      (Filter.eventually_of_mem (isOpen_ball.mem_nhds hN) (fun y hy => hEq hy))

end
end NlsGge.ThirdConsultation.R

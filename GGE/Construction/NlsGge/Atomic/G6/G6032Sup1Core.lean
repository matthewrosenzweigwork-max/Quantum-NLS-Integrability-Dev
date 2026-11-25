import Mathlib
import NlsGge.ThirdConsultation.G2.G2042MomentA
import NlsGge.Atomic.G2.G2042
import NlsGge.GK38.PeriodicLabelling
import NlsGge.GK38.TauGamma
import NlsGge.Atomic.G6.G6020

                                                                                       
                                                                                                                    
                                                           
                                                                                                      
                                                                       
                                                                                                                     
                                                                                                 
                                                                                                            
                                                                                                         
                                                                                                                  
                                                              
                                                                                                                        
                                                                                         
                                                                                                                   
                                                                                                                 
                                                        
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.G6032S
noncomputable section

section
variable {φ ψ : PotPair} (hφ : φ ∈ gkW) (hψ : ψ ∈ gkW) (hd : discrim φ = discrim ψ)
include hφ hψ hd

omit hφ hψ in
theorem lamPlus_eq : lamPlus φ = lamPlus ψ := by
  have hp : perChar φ = perChar ψ := by funext z; simp only [perChar, hd]
  have hl := lamSeq_eq_of_perChar_eq38 hp
  funext n; simp only [lamPlus, hl]

omit hφ hψ in
theorem lamMinus_eq : lamMinus φ = lamMinus ψ := by
  have hp : perChar φ = perChar ψ := by funext z; simp only [perChar, hd]
  have hl := lamSeq_eq_of_perChar_eq38 hp
  funext n; simp only [lamMinus, hl]

omit hφ hψ in
theorem lamDot_eq' : lamDot φ = lamDot ψ := lamDot_eq_of_discrimDeriv_eq38 (by rw [hd])

theorem tauN_eq : tauN φ = tauN ψ := by
  funext n
  rw [tauN_value38 φ hφ, tauN_value38 ψ hψ, lamPlus_eq hd, lamMinus_eq hd]

theorem gamma2_eq : gamma2 φ = gamma2 ψ := by
  funext n
  rw [gamma2_value38 φ hφ, gamma2_value38 ψ hψ, lamPlus_eq hd, lamMinus_eq hd]

theorem canonRoot_eq : canonRoot38 φ = canonRoot38 ψ := by
  have hτ := tauN_eq hφ hψ hd
  have hg := gamma2_eq hφ hψ hd
  funext z
  simp only [canonRoot38, rootFactor38, hτ, hg]

theorem shift_eq : a5CriticalShift38 φ = a5CriticalShift38 ψ := by
  apply lp.ext
  funext m
  rw [a5CriticalShift_value38 φ hφ m, a5CriticalShift_value38 ψ hψ m, lamDot_eq' hd]

theorem chi_eq (n : ℤ) (z : ℂ) : a5Chi38 n (φ, z) = a5Chi38 n (ψ, z) := by
  have hτ := tauN_eq hφ hψ hd
  have hg := gamma2_eq hφ hψ hd
  have hs := shift_eq hφ hψ hd
  simp only [a5Chi38, a5CriticalNumerator38, a5OmittedRootProduct38, a5OmittedRootFactor38, rootFactor38,
    hτ, hg, hs]

theorem critArcS_eq (j : ℕ) (n : ℤ) : G2042MomentA.critArcS j φ n = G2042MomentA.critArcS j ψ n := by
  funext t
  unfold G2042MomentA.critArcS
  rw [chi_eq hφ hψ hd]
  simp only [gap, tauN_eq hφ hψ hd, lamDot_eq' hd, lamPlus_eq hd, lamMinus_eq hd]

end

/-- Contour-free value of the `j`-th critical moment on gap `n`. -/
def cutVal (j : ℕ) (φ : PotPair) (n : ℤ) : ℂ :=
  if lamPlus φ n - lamMinus φ n = 0 then 0 else
    2 * ∫ t in (-1 : ℝ)..1, G2042MomentA.critArcS j φ n t / ((Real.sqrt (1 - t^2) : ℝ) : ℂ)

theorem moment_eq_cut (j : ℕ) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    circleIntegral (fun z : ℂ => (z - lamDot φ n)^j * deriv (discrim φ) z / canonRoot38 φ z)
      (discC φ n) (discR φ n) = cutVal j φ n := by
  unfold cutVal
  by_cases hγ : lamPlus φ n - lamMinus φ n = 0
  · rw [if_pos hγ]; exact G2042MomentA.circle_moment_collapsed j φ hφ n hγ
  · rw [if_neg hγ]; exact G2042MomentA.circle_eq_cut j φ hφ n hγ

theorem cutVal_eq {φ ψ : PotPair} (hφ : φ ∈ gkW) (hψ : ψ ∈ gkW) (hd : discrim φ = discrim ψ)
    (j : ℕ) (n : ℤ) : cutVal j φ n = cutVal j ψ n := by
  unfold cutVal
  rw [critArcS_eq hφ hψ hd, lamPlus_eq hd, lamMinus_eq hd]

theorem higherAction_cut (k : ℕ) (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    higherAction k φ n = (1 / (Real.pi : ℂ)) *
      ∑ m ∈ Finset.range (k + 1), ((k.choose m : ℂ) * lamDot φ n ^ (k - m)) * cutVal m φ n := by
  unfold higherAction
  have hfun : (fun z : ℂ => z ^ k * deriv (discrim φ) z / canonRoot38 φ z) = fun z =>
      ∑ m ∈ Finset.range (k + 1), ((k.choose m : ℂ) * lamDot φ n ^ (k - m)) *
        ((z - lamDot φ n) ^ m * deriv (discrim φ) z / canonRoot38 φ z) :=
    funext (G2042Pkt.binom_split k φ n)
  have hs := G2042Pkt.circle_sum_eq (Finset.range (k + 1))
    (fun m z => ((k.choose m : ℂ) * lamDot φ n ^ (k - m)) *
      ((z - lamDot φ n) ^ m * deriv (discrim φ) z / canonRoot38 φ z)) (discC φ n) (discR φ n)
    (fun m _ => IntervalIntegrable.const_mul (G2042MomentA.circleIntegrable_moment m φ hφ n) _)
  beta_reduce at hs
  rw [hfun, hs]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [circleIntegral.integral_const_mul, moment_eq_cut m φ hφ n]

theorem higherAction_eq_of_gkW (k : ℕ) {φ ψ : PotPair} (hφ : φ ∈ gkW) (hψ : ψ ∈ gkW)
    (hd : discrim φ = discrim ψ) (n : ℤ) : higherAction k φ n = higherAction k ψ n := by
  rw [higherAction_cut k φ hφ n, higherAction_cut k ψ hψ n, lamDot_eq' hd]
  exact congrArg (fun S : ℂ => (1 / (Real.pi : ℂ)) * S)
    (Finset.sum_congr rfl fun m _ => congrArg (fun c : ℂ => ((k.choose m : ℂ) * lamDot ψ n ^ (k - m)) * c)
      (cutVal_eq hφ hψ hd m n))

end
end NlsGge.ThirdConsultation.G6032S

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem higherAction_eq_of_isospectral (k : ℕ) {u v : PhysicalL2}
    (hiso : isospectral u v) (n : ℤ) :
  higherAction k (realSlice u) n = higherAction k (realSlice v) n :=
  NlsGge.ThirdConsultation.G6032S.higherAction_eq_of_gkW k (realSlice_mem_gkW u) (realSlice_mem_gkW v)
    (funext fun z => (hiso z).symm) n

end
end NlsGge.GKDefinitionDesign

import Mathlib
import NlsGge.Atomic.KST.KST027
import NlsGge.Atomic.KST.KST032
import NlsGge.ThirdConsultation.KST.KST029Support
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST031Support
import NlsGge.ThirdConsultation.KST.KST032Host
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST033Real
import NlsGge.ThirdConsultation.KST.KST033Support

                                                                                                        
                                                                                                     
                                                                                              
                                                                                                    
                                                                                                                  
                                                                               
set_option autoImplicit false
noncomputable section

namespace NlsGge.ThirdConsultation.KST

theorem kst033 (w : ℤ → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hw : UnboundedWeight w) (v : ℤ → ℝ) (hv : SecondaryWeight v)
    (n : ℤ) (hn : diagonalThreshold w M ≤ n.natAbs) :
  let ω := productWeight w v
  let hω := productOneLe hw.1.1 hv.1.1
  letI := weightFact ω hω
  AnalyticOnNhd ℂ (fun x : Weighted ω => diagonalZero n (weightedPotential ω hω x))
    (componentOpenBall ω (2*M)) ∧
  ∀ x ∈ componentBall ω (2*M), ∀ ε : ℝ,
    RealForm ε (periodicPair (weightedPotential ω hω x)) →
      star (diagonalZero n (weightedPotential ω hω x)) =
        diagonalZero n (weightedPotential ω hω x) := by
  intro ω hω
  letI := weightFact ω hω
  have hball : ∀ x ∈ componentBall ω (2*M),
      weightedPotential ω hω x ∈ physicalComponentBall w (2*M) :=
    fun x hx => KST031S.ball_productWeight_subset w v hw.1.1 hv.1.1 (2*M)
      (KST033S.wp_mem_ball ω hω x (2*M) hx)
  refine ⟨KST033S.diagonalZero_analyticOnNhd w M hM hw n hn ω hω hball, ?_⟩
  intro x hx ε hrf
  obtain ⟨hε, hfalse⟩ := hrf
  exact KST033R.diagonalZero_star w M hM hw (weightedPotential ω hω x) (hball x hx) n hn ε hε
    hfalse

theorem kst033_restriction (ω ν : ℤ → ℝ)
    (hω : ∀ k, 1 ≤ ω k) (hν : ∀ k, 1 ≤ ν k)
    (hων : ∀ k, ν k^2 ≤ ω k^2) :
  letI := weightFact ω hω
  letI := weightFact ν hν
  ∀ (x : Weighted ω) (n : ℤ),
    diagonalZero n (weightedPotential ν hν (weightedRestriction ω ν hων x)) =
      diagonalZero n (weightedPotential ω hω x) := by
  letI := weightFact ω hω
  letI := weightFact ν hν
  intro x n
  exact congrArg (diagonalZero n) (KST033S.wp_restriction ω ν hω hν hων x)

end NlsGge.ThirdConsultation.KST
end

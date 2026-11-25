import Mathlib
import NlsGge.Atomic.DM.DM004
import NlsGge.Atomic.KST.KST003
import NlsGge.Atomic.KST.KST004
import NlsGge.Atomic.KST.KST013
import NlsGge.Atomic.KST.KST016
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST019
import NlsGge.Atomic.KST.KST031
import NlsGge.Atomic.KST.KST032
import NlsGge.Atomic.KST.KST059
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.ThirdConsultation.KST.KST029Support
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST032Host
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST033Real
import NlsGge.ThirdConsultation.KST.KST052Host
import NlsGge.ThirdConsultation.KST.KST052Support

                                                                                                        
                                                                                                    
                                                                                                         
                                                                                                               
                                                                                        
                                                                                                            
set_option autoImplicit false
noncomputable section
open NlsGge.Atomic.KST003 NlsGge.Atomic.KST004 NlsGge.Atomic.KST013 NlsGge.GK38
open NlsGge.Atomic.KST059
open NlsGge.Atomic.KST016 (H)

namespace NlsGge.ThirdConsultation.KST

theorem kst052 (w : ℤ → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hw : UnboundedWeight w) (φ : Potential)
    (hφ : φ ∈ physicalComponentBall w (2*M)) (ε : ℝ)
    (hreal : RealForm ε (periodicPair φ))
    (n : ℤ) (hn : diagonalThreshold w M ≤ n.natAbs)
    (hb : b φ n (diagonalZero n φ) = 0) :
  let σ := diagonalZero n φ
  c φ n σ = 0 ∧
  (∃ hσ : σ ∈ spectralStrip n, reducedS φ n σ hσ = 0) ∧
  (∃ E : eigenspace φ σ ≃ₗ[ℂ] resonantSubspace n,
    ∀ f : eigenspace φ σ, (E f : H) = spectralPn n (f.1 : H)) ∧
  Module.finrank ℂ (eigenspace φ σ) = 2 ∧
  lamMinus (periodicPair φ) n = σ ∧ lamPlus (periodicPair φ) n = σ ∧
  actualGapSequence (periodicPair φ) n = 0 := by
  intro σ
  obtain ⟨-, hall⟩ := (kst031 w M hM hw).2.1
  obtain ⟨⟨hA, hB, hC, -⟩, hQ, hdet⟩ := hall φ hφ n hn
  obtain ⟨-, -, hmem, hfix0, -⟩ := kst032 w M hM hw φ hφ n hn
  obtain ⟨hε, hfalse⟩ := hreal
  have hfix : σ = center n + a φ n σ := hfix0
  have hstar : star σ = σ :=
    KST033R.diagonalZero_star w M hM hw φ hφ n hn ε hε hfalse
  have hσ : σ ∈ spectralStrip n :=
    KST032S.closedBall_sub_strip n (center n) (Metric.mem_closedBall_self (by positivity))
      (Real.pi/48) (by nlinarith [Real.pi_pos]) hmem
  have hb' : b φ n σ = 0 := hb
  have hc0 : c φ n σ = 0 := by
    rw [KST052S.c_eq_eps_star_b φ ε hε hfalse n σ, hstar, hb']
    simp
  have hred := abc_eq_reduced φ n σ hσ
  have hrA : NlsGge.Atomic.KST016.reducedA φ n σ hσ = a φ n σ := (congrArg Prod.fst hred).symm
  have hrB : NlsGge.Atomic.KST016.reducedB φ n σ hσ = b φ n σ :=
    (congrArg (fun p : ℂ × ℂ × ℂ => p.2.1) hred).symm
  have hrC : NlsGge.Atomic.KST016.reducedC φ n σ hσ = c φ n σ :=
    (congrArg (fun p : ℂ × ℂ × ℂ => p.2.2) hred).symm
  have hff : NlsGge.Atomic.KST016.entry φ n σ hσ false false = 0 := by
    have h1 : NlsGge.Atomic.KST016.reducedA φ n σ hσ =
        (σ - (n : ℂ) * Real.pi) - NlsGge.Atomic.KST016.entry φ n σ hσ false false := rfl
    have hc : center n = (n : ℂ) * Real.pi := rfl
    linear_combination h1 - hrA + hfix + hc
  have hft : NlsGge.Atomic.KST016.entry φ n σ hσ false true = 0 := by
    have h1 : NlsGge.Atomic.KST016.reducedB φ n σ hσ =
        -NlsGge.Atomic.KST016.entry φ n σ hσ false true := rfl
    rw [hb'] at hrB
    linear_combination h1 - hrB
  have htf : NlsGge.Atomic.KST016.entry φ n σ hσ true false = 0 := by
    have h1 : NlsGge.Atomic.KST016.reducedC φ n σ hσ =
        -NlsGge.Atomic.KST016.entry φ n σ hσ true false := rfl
    rw [hc0] at hrC
    linear_combination h1 - hrC
  have htt : NlsGge.Atomic.KST016.entry φ n σ hσ true true = 0 :=
    (KST052S.entry_true_true φ n σ hσ).trans hff
  have hS : reducedS φ n σ hσ = 0 :=
    KST052S.reducedS_eq_zero_of_entries φ n σ hσ (by
      intro i j
      cases i <;> cases j
      exacts [hff, hft, htf, htt])
  have hT : ‖NlsGge.Atomic.KST006.qOperator φ n σ hσ ^ 2‖ < 1 :=
    lt_of_le_of_lt (hQ σ hσ).1 (by norm_num)
  obtain ⟨E, hE⟩ := KST052S.eigenspace_equiv φ n σ hσ hT (hQ σ hσ).2 hS
  have hsub : Metric.closedBall (center n) (Real.pi/3) ⊆ spectralStrip n := fun u hu =>
    KST032S.closedBall_sub_strip n (center n) (Metric.mem_closedBall_self (by positivity))
      (Real.pi/3) (by nlinarith [Real.pi_pos]) hu
  have hAn : AnalyticOnNhd ℂ (determinant n (a φ n) (b φ n) (c φ n))
      (Metric.closedBall (center n) (Real.pi/3)) := fun u hu =>
    KST052S.determinant_analyticAt n _ _ _ u (hA u (hsub hu)) (hB u (hsub hu)) (hC u (hsub hu))
  have hσball : σ ∈ Metric.ball (center n) (Real.pi/3) :=
    Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hmem)
      (by nlinarith [Real.pi_pos]))
  have hord := KST052S.determinant_order_ge_two n (a φ n) (b φ n) (c φ n) σ
    (hA σ hσ) (hB σ hσ) (hC σ hσ) hfix hb' hc0
  obtain ⟨hlm, hlp⟩ := KST052S.double_zero_multiset hAn hσball hord hdet
  refine ⟨hc0, ⟨hσ, hS⟩, ⟨E, fun f => hE f⟩, ?_, hlm, hlp, ?_⟩
  · rw [E.finrank_eq]
    exact resonantSubspace_finrank n
  · unfold actualGapSequence
    rw [hlm, hlp]
    ring

end NlsGge.ThirdConsultation.KST
end

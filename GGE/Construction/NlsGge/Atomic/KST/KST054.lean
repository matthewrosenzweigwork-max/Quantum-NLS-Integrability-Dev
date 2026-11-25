import Mathlib
import NlsGge.Atomic.DM.DM004
import NlsGge.Atomic.KST.KST001
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST043
import NlsGge.Atomic.KST.KST045
import NlsGge.Atomic.KST.KST046
import NlsGge.Atomic.KST.KST053
import NlsGge.Atomic.KST.KST059
import NlsGge.GK38.Defs
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST029Support
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST034Host
import NlsGge.ThirdConsultation.KST.KST035Host
import NlsGge.ThirdConsultation.KST.KST046Host

                                                                                                        
                                                                                                    
                                                                                                              
                                                                                                                      
                                        
                                                             
                                                                                                     
                                                                                                          
                                                                                                            
                                                                                                            
                                                                        
                                                                                                                          
                                                                                                        
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ENNReal
open NlsGge.Atomic.KST (SlowWeight)
open NlsGge.Atomic.KST001 NlsGge.Atomic.KST002 NlsGge.Pilot NlsGge.GK38
open NlsGge.Atomic.KST059
open NlsGge.Atomic.KST043 (KSTSubexponentialWeight)

namespace NlsGge.ThirdConsultation.KST

namespace KST054S

/-- A `PotPair` is the periodic pair of a physical `Potential`. -/
def potOfPair (φ : PotPair) : PhysicalPairLp :=
  WithLp.toLp 2 (fun b : Bool => if b then φ.1 else φ.2)

theorem periodicPair_potOfPair (φ : PotPair) : periodicPair (potOfPair φ) = φ := by
  simp [periodicPair, potOfPair]

/-- Channel energies are bounded by the full even-mode pair energy. -/
theorem channel_energy_le (w : ℤ → ℝ) (hw : EvenWeight w) (φ : PotPair) (b : Bool) :
    (∑' m : ℤ, ENNReal.ofReal
      (w (2*m)^2 * ‖physicalFourier ((potOfPair φ) b) m‖^2)) ≤ weightedNormSq₂ w φ := by
  rw [periodOne_weightedPair_norm w φ hw]
  unfold weightedEvenFourierNormSq
  refine ENNReal.tsum_le_tsum (fun m => ?_)
  unfold weightedPairMode
  rw [ENNReal.ofReal_mul (sq_nonneg _)]
  refine mul_le_mul' le_rfl ?_
  cases b
  · exact le_add_self
  · exact le_self_add

theorem mem_ball (w : ℤ → ℝ) (hw : EvenWeight w) (φ : PotPair)
    (hφ : weightedNormSq₂ w φ < ⊤) (M : ℝ)
    (hmargin : 8*Real.sqrt (weightedNormSq₂ w φ).toReal ≤ M) :
    potOfPair φ ∈ physicalComponentBall w M := by
  intro b
  refine (channel_energy_le w hw φ b).trans ?_
  rw [← ENNReal.ofReal_toReal hφ.ne]
  refine ENNReal.ofReal_le_ofReal ?_
  have h0 : 0 ≤ (weightedNormSq₂ w φ).toReal := ENNReal.toReal_nonneg
  have hs := Real.sq_sqrt h0
  have h8 : 0 ≤ 8*Real.sqrt (weightedNormSq₂ w φ).toReal := by positivity
  nlinarith [pow_le_pow_left₀ h8 hmargin 2, Real.sqrt_nonneg (weightedNormSq₂ w φ).toReal]

end KST054S

theorem kst054 (w v : ℤ → ℝ) (Cw : ℝ)
    (hw : SlowWeight w Cw)
    (hunbounded : Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop)
    (hv : SecondaryWeight v) (φ : PotPair)
    (hφ : weightedNormSq₂ w φ < ⊤) (ε : ℝ) (hreal : RealForm ε φ)
    (hgaps : weightedGapEnergy (productWeight w v) (actualGapSequence φ) < ⊤) :
  (KSTSubexponentialWeight v → weightedNormSq₂ (productWeight w v) φ < ⊤) ∧
  (∀ χ : ℝ, ExponentialWeight v χ →
    ∃ δ : ℝ, 0 < δ ∧ δ < χ ∧
      weightedNormSq₂ (productWeight w (expWeight δ)) φ < ⊤) := by
  have hEven : EvenWeight w := ⟨hw.one_le, hw.even⟩
  set M : ℝ := max 1 (8*Real.sqrt (weightedNormSq₂ w φ).toReal) with hMdef
  have hM : 1 ≤ M := le_max_left _ _
  have hmargin : 8*Real.sqrt (weightedNormSq₂ w φ).toReal ≤ M := le_max_right _ _
  set ψ : PhysicalPairLp := KST054S.potOfPair φ with hψ
  have hper : periodicPair ψ = φ := KST054S.periodicPair_potOfPair φ
  have hball : ψ ∈ physicalComponentBall w M := KST054S.mem_ball w hEven φ hφ M hmargin
  have hreal' : RealForm ε (periodicPair ψ) := by rw [hper]; exact hreal
  have hgaps' : weightedGapEnergy (productWeight w v) (actualGapSequence (periodicPair ψ)) < ⊤ := by
    rw [hper]; exact hgaps
  have hφ' : weightedNormSq₂ w (periodicPair ψ) < ⊤ := by rw [hper]; exact hφ
  have hmargin' : 8*Real.sqrt (weightedNormSq₂ w (periodicPair ψ)).toReal ≤ M := by
    rw [hper]; exact hmargin
  have hF := (kst053 w v Cw M hM hw hunbounded hv ψ hball ε hreal' hgaps').2
  refine ⟨fun hsub => ?_, fun χ hχ => ?_⟩
  · have h := (kst045 w v Cw M hM hw hunbounded hsub ψ hφ' hmargin' hF).2
    rw [hper] at h
    exact h
  · obtain ⟨-, -, δ, hδ0, hδχ, -, hfin⟩ :=
      kst046 w v Cw M χ hM hw hunbounded hχ ψ hφ' hmargin' hF
    rw [hper] at hfin
    exact ⟨δ, hδ0, hδχ, hfin⟩

end NlsGge.ThirdConsultation.KST
end

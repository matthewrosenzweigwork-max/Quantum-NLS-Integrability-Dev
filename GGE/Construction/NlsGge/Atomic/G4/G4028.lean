import Mathlib
import NlsGge.Atomic.G4.G4028Host
import NlsGge.Atomic.G4.G4023
import NlsGge.Atomic.G4.G4036
import NlsGge.Atomic.G4.G4017
import NlsGge.Atomic.G5.G5001

                                                                                                                  
                                                                                                                       
                                                                                                                
                                                            
                                                                                                                          
                                                                                                              
                                                                                                             
                                                                                                                        
                                                                                                                     
                                 
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.G4028Support
noncomputable section

/-- The terminal root is the sheet sign times the standard root at the Dirichlet point (off the gap). -/
theorem terminalRoot_eq (n : ℤ) (φ : PotPair) (hφ : φ ∈ offGapSet n) :
    terminalRoot n φ = sheetSign n φ * standardRoot φ n (muSeq φ n) := by
  have hdom : (φ, muSeq φ n) ∈ rootDomain38 := (G4017Aux.mem_offGap_iff n φ hφ.1).1 hφ
  have hfac := a5CanonRoot_omitted_factorization38 n (φ, muSeq φ n) hdom
  have hA : a5OmittedRootProduct38 n (φ, muSeq φ n) ≠ 0 :=
    a5OmittedRoot_ne_zero38 n (φ, muSeq φ n) (g5001_dom φ hφ.1 n)
  have hpi : (Lib.piN n : ℂ) ≠ 0 := by exact_mod_cast Lib.piN_ne_zero n
  have hC : canonRoot38 φ (muSeq φ n) ≠ 0 := ((G4017 n).2.2.2 φ hφ).1
  have hrf : rootFactor38 n (φ, muSeq φ n) = standardRoot φ n (muSeq φ n) / (Lib.piN n : ℂ) := rfl
  have hfac' : canonRoot38 φ (muSeq φ n) =
      2 * Complex.I * (standardRoot φ n (muSeq φ n) / (Lib.piN n : ℂ)) *
        a5OmittedRootProduct38 n (φ, muSeq φ n) := by
    rw [← hrf]; exact hfac
  have hs : standardRoot φ n (muSeq φ n) ≠ 0 := by
    intro h
    apply hC
    rw [hfac', h]; simp
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  unfold terminalRoot sheetSign
  rw [hfac']
  field_simp

/-- Value of the continued Cartesian exponential at a collapsed off-gap potential. -/
theorem value_at_collapse (n a : ℤ) (ha : a = 1 ∨ a = -1) (ψ : PotPair) (hψ : ψ ∈ offGapSet n)
    (hgap : gamma2 ψ n = 0) :
    cartesianZExtended n a ψ = collapsedZValue n a ψ := by
  have hid := NlsGge.G4023Support.collapse_identity n ψ hψ.1 hgap
  have hpm := ((G4017 n).2.2.2 ψ hψ).2.1
  have hstd : standardRoot ψ n (muSeq ψ n) = tauN ψ n - muSeq ψ n := by
    unfold standardRoot
    rw [hgap]
    exact stdRoot_degenerate38 _ _
  have hT := terminalRoot_eq n ψ hψ
  rw [hstd] at hT
  set ε := sheetSign n ψ with hε
  set d := tauN ψ n - muSeq ψ n with hd
  set oc := ownCorrection n ψ (muSeq ψ n) with hoc
  have hexp : ε * (d * oc) = -(ε * chi n ψ) := by linear_combination ε * hid
  rcases ha with rfl | rfl
  · unfold cartesianZExtended collapsedZValue
    rw [if_pos rfl, hT, ← hd, ← hoc, ← hε, mul_assoc ε d oc, hexp]
    rcases hpm with h | h <;> rw [h] <;> push_cast <;> simp <;> ring
  · unfold cartesianZExtended collapsedZValue
    rw [if_neg (by norm_num), hT, ← hd, ← hoc, ← hε, mul_assoc ε d oc, hexp]
    rcases hpm with h | h <;> rw [h] <;> push_cast <;> simp <;> ring

end
end NlsGge.G4028Support

namespace NlsGge.GKDefinitionDesign
noncomputable section

open NlsGge.G4028Support in
theorem G4028 (n a : ℤ) (ha : a = 1 ∨ a = -1)
    (ψ : PotPair) (hψ : ψ ∈ offGapSet n) (hgap : gamma2 ψ n = 0) :
  cartesianZExtended n a ψ = collapsedZValue n a ψ ∧
  Tendsto (cartesianZ n a)
    (𝓝[{φ : PotPair | φ ∈ offGapSet n ∧ gamma2 φ n ≠ 0}] ψ)
    (𝓝 (collapsedZValue n a ψ)) := by
  have heq := value_at_collapse n a ha ψ hψ hgap
  refine ⟨heq, ?_⟩
  have hcont : ContinuousAt (cartesianZExtended n a) ψ := (G4036 n a ha ψ hψ.1).continuousAt
  rw [← heq]
  exact hcont.tendsto.mono_left nhdsWithin_le_nhds

end
end NlsGge.GKDefinitionDesign

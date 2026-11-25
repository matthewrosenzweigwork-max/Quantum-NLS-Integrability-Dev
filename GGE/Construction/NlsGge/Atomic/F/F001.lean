import Mathlib
import NlsGge.Hierarchy.RiccatiFormalChargeRemainderUniformNormalizationRecovery29Fourth
import NlsGge.Hierarchy.RiccatiNormalizedRemainderDerivativeCountAndTopSlotsRecovery33Second

                                                                                                                   
                                                                                                                 
                                                                                                         
                                                                                                                        
                                                                            

set_option autoImplicit false
open NlsGge.HierarchyRiccati.Core

namespace NlsGge.Atomic.F001

theorem nonlinearMonomial_highFactor_count
    (m j : ℕ) (hm : 2 ≤ m) (hj : j ≤ m) (q : Jet →₀ ℕ)
    (hq : q ∈ (formalChargeRemainderNormalizedUniformNativeRecovery29Fourth j).support) :
    ((riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter
      (fun s => s.1.2 = m-1)).card ≤ 2 ∧
    (∀ v ∈ q.support, v.2 ≤ m-1) ∧
    (∀ v ∈ q.support, v.2 ≠ m-1 → v.2 ≤ m-2) ∧
    q.degree ≤ 2*m+2 := by
  obtain ⟨hord, -, -, hdeg⟩ :=
    formalChargeRemainderNormalizedUniform_propertiesNativeRecovery29Fourth j
  have hcard := formalChargeRemainderNormalized_topSlotCard_le_twoRecovery33Second m j hm hj q hq
  have hfilt : (riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter (fun s => s.1.2 = m-1) =
      (riccatiActualMonomialSlotFinsetRecovery31Fourth q).filter (fun s => s.1.2 + 1 = m) :=
    Finset.filter_congr (fun s _ => by omega)
  have hv : ∀ v ∈ q.support, v.2 ≤ m-1 := fun v hvq => by
    have := hord q hq v hvq
    omega
  refine ⟨?_, hv, ?_, ?_⟩
  · rw [hfilt]; exact hcard
  · intro v hvq hne
    have := hv v hvq
    omega
  · have := hdeg q hq
    omega

end NlsGge.Atomic.F001

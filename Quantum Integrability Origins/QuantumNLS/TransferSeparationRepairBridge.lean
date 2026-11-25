import QuantumNLS.TransferSeparation
import QuantumNLS.TransferSeparationContinuityRepair

/-! Explicit binding of the fresh continuity-tail repair to the preserved
original scalar definitions. The repaired proof is rebuilt from source in
its own namespace. No original source or object is replaced, and no real-axis
separation or interacting eigenrelation is asserted by this bridge. -/
noncomputable section
namespace QuantumNLS.TransferSeparationRepairBridge

theorem sFun_correspondence {N : ℕ} (L c : ℝ) (q : Fin N → ℝ) (z : ℂ) :
    TransferSeparationContinuityRepair.sFun L c q z = TransferSeparation.sFun L c q z := rfl

theorem msOf_correspondence {N : ℕ} (q : Fin N → ℝ) :
    TransferSeparationContinuityRepair.msOf q = TransferSeparation.msOf q := rfl

theorem onShell_correspondence {N : ℕ} (L c : ℝ) (q : Fin N → ℝ) :
    TransferSeparationContinuityRepair.OnShell L c q ↔ TransferSeparation.OnShell L c q := Iff.rfl

theorem poles_correspondence {N : ℕ} (p q : Fin N → ℝ) :
    TransferSeparationContinuityRepair.poles p q =
      (Finset.univ.image (fun j => (p j : ℂ)) ∪ Finset.univ.image (fun j => (q j : ℂ))) := rfl

/-- The repaired tail supplies the original complex cofinite separation
statement for the unchanged original scalar definitions. -/
theorem separation_cofinite {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (p q : Fin N → ℝ) (Q : Finset ℂ)
    (h : ∀ z : ℂ, z ∉ TransferSeparationContinuityRepair.poles p q ∪ Q →
      TransferSeparation.sFun L c p z = TransferSeparation.sFun L c q z) :
    TransferSeparation.msOf p = TransferSeparation.msOf q :=
  TransferSeparationContinuityRepair.separation_cofinite hL hc p q Q h

theorem exists_ne_of_msOf_ne {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {p q : Fin N → ℝ} (hne : TransferSeparation.msOf p ≠ TransferSeparation.msOf q) :
    ∃ z : ℂ, z ∉ TransferSeparationContinuityRepair.poles p q ∧
      TransferSeparation.sFun L c p z ≠ TransferSeparation.sFun L c q z :=
  TransferSeparationContinuityRepair.exists_ne_of_msOf_ne hL hc hne

end QuantumNLS.TransferSeparationRepairBridge

#print axioms QuantumNLS.TransferSeparationRepairBridge.sFun_correspondence
#print axioms QuantumNLS.TransferSeparationRepairBridge.msOf_correspondence
#print axioms QuantumNLS.TransferSeparationRepairBridge.onShell_correspondence
#print axioms QuantumNLS.TransferSeparationRepairBridge.poles_correspondence
#print axioms QuantumNLS.TransferSeparationRepairBridge.separation_cofinite
#print axioms QuantumNLS.TransferSeparationRepairBridge.exists_ne_of_msOf_ne

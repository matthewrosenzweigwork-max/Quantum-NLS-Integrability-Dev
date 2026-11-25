import Mathlib
import QuantumNLS.RB7BindMain
import QuantumNLS.RB7HClauses45b

/-!
# R-7B122087: unconditional `HierarchyInputR25m.HierarchyR7B122087Input` (RB7BindFinal)

Discharges the two explicit hypotheses `hO`, `hJ` of `RB7BindMain.hierarchyInputR25m_holds` with the frozen and reviewed
`RB7HBridge.orbitCompactInput_of` and `RB7HBridge.jointContInput_of` (`RB7HClauses45b` sha256 `4c0b15ac`).
Source: `source-text/chapters/core/DYNAMICS_LEMMAS.tex:115-128` (`thm:hierarchy`).
-/

set_option autoImplicit false

namespace QuantumNLS.RB7BindFinal

variable {L κ : ℝ} [Fact (0 < L)]

/-- **`HierarchyInputR25m.HierarchyR7B122087Input hκ`, unconditionally.** -/
theorem hierarchyInputR25m_unconditional (hκ : 0 < κ) :
    QuantumNLS.HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ :=
  QuantumNLS.RB7BindMain.hierarchyInputR25m_holds hκ
    (fun R _ => QuantumNLS.RB7HBridge.orbitCompactInput_of hκ R)
    (fun R _ => QuantumNLS.RB7HBridge.jointContInput_of hκ R)

end QuantumNLS.RB7BindFinal

#print axioms QuantumNLS.RB7BindFinal.hierarchyInputR25m_unconditional

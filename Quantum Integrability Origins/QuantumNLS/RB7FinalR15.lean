import Mathlib
import QuantumNLS.RB7Final
import QuantumNLS.Reg015HFinal

/-!
# R-7B122087 `thm:hierarchy` / DEF-024: REG-015 swap (RB7FinalR15)

`RB7Final.hierarchy_final` has the single named input `REG015Concl hκ`, the conclusion of `Reg015Assembly.REG015Input`.  `Reg015HFinal.REG015_final` (haiku_inventory, conditional on REG-010/011/013 pending
review, independent review PASS recorded by the integrator) is that same proposition with its three inputs discharged; the corollary below is the one-line swap.  No acceptance is claimed here.
-/

set_option autoImplicit false
noncomputable section

namespace QuantumNLS.RB7

variable {L κ : ℝ} [Fact (0 < L)]

/-- **DEF-024 for every order, with `REG015_final` as the input.** -/
theorem hierarchy_of_REG015_final (hκ : 0 < κ) (𝓡 : Finset ℕ) : HierarchyConcl (L := L) hκ 𝓡 :=
  hierarchy_final (QuantumNLS.Reg015HFinal.REG015_final (L := L) hκ) 𝓡

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.hierarchy_of_REG015_final

import Mathlib
import NlsGge.GK38.GradEigenClosedGeneric

/- G1-066 (proof development, AUTHOR; not reviewed).  Statement = Pro's third-consultation signature `G1_066`
   (`root/gpt6pro_defs/handoff/definitions_design_20261027/STATEMENTS/G1.md` line ~93), verbatim.
   Route: the set of all-gaps-open potentials is the countable intersection of the open dense sets (Z n)ᶜ
   (`all_gaps_open_eq_iInter`, `closed_nowhere_dense_target`); dense by Baire (`all_gaps_generic_target`);
   G-delta because ℤ is countable and each (Z n)ᶜ is open. -/

set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38.GradEigen38

namespace NlsGge.Atomic.G1066

theorem G1_066 :
    Dense {u : PhysicalL2 | ∀ n : ℤ,
      actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n} ∧
    IsGδ {u : PhysicalL2 | ∀ n : ℤ,
      actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n} := by
  refine ⟨all_gaps_generic_target, ?_⟩
  rw [all_gaps_open_eq_iInter]
  exact IsGδ.iInter_of_isOpen fun n => (closed_nowhere_dense_target n).2.2.1

end NlsGge.Atomic.G1066


import Mathlib
import NlsGge.Atomic.G4.G4043
import NlsGge.GK38.XiSqCanonical
import NlsGge.GK38.XiSqOmittedRoot

/- G5-025 SUPPORT 3 `G5025Sup3` (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5025Sup3.lean, namespace NlsGge.GKDefinitionDesign.G5025Sup3.
   Nonvanishing of the Cartesian squared radius at a real-slice point with nonzero gamma2:
   X^2 + Y^2 = 2 * action (landed G4043) and gamma2 * xi^2 = 4 * action (xiSq38_multiplied) with xi^2 >= 1 real. -/
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
namespace G5025Sup3
noncomputable section

theorem radius_ne_zero (u : PhysicalL2) (n : ℤ) (hn : gamma2 (realSlice u) n ≠ 0) :
    cartesianX n (realSlice u) ^ 2 + cartesianY n (realSlice u) ^ 2 ≠ 0 := by
  have hB : realSlice u ∈ sourceBetaW := sourceFamily.V_real (Set.mem_range_self u)
  have hgk : realSlice u ∈ gkW := realSlice_mem_gkW u
  have h1 := G4043 n (realSlice u) hB
  have h2 := xiSq38_multiplied n (realSlice u) hgk
  have hxi : xiSq38 n (realSlice u) ≠ 0 := by
    intro h
    have := (xiSq38_real_ge_one u n).2
    rw [h] at this
    simp at this
    linarith
  intro h
  rw [h, zero_div] at h1
  rw [h1, mul_zero] at h2
  exact mul_ne_zero hn hxi h2

end
end G5025Sup3
end NlsGge.GKDefinitionDesign

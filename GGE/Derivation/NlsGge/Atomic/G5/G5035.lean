import Mathlib
import NlsGge.Atomic.G5.G5031Host
import NlsGge.Atomic.G5.G5035Sup1
import NlsGge.Atomic.G5.G5035Sup2
import NlsGge.Atomic.G5.G5025
import NlsGge.Atomic.G5.G5032
import NlsGge.Atomic.G5.G5034

/- G5-035 PACKET (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5035.lean, namespace NlsGge.GKDefinitionDesign.
   Head `G5035` VERBATIM from followup12 STATEMENTS/G5.md section G5-035 (round 14 cluster 5 row G5-035) except the lexical rename
   of the binder `λ` to `lam` (licensed by round 14 cluster 12: "uniform λ→lam ... including doubleAngleDiscriminantBracket").
   Host definitions `anglePoisson`, `doubleAngleDiscriminantBracket` are in the landed G5031Host.
   Proof (GK 18.6): G5035Sup1.core35 (Jacobi + interpolation) with
     (hprim) G5035Sup2.angle_local_primitive;  (h25) landed G5025 (second conjunct);  (h32) landed G5032;  (h34) landed G5034.
   G5023 (interpolation) and LIB081 (Jacobi, via the landed local version G5031Sup1) are used inside G5035Sup1. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5035 (u : PhysicalL2) (m n : ℤ)
    (hm : gamma2 (realSlice u) m ≠ 0) (hn : gamma2 (realSlice u) n ≠ 0) :
  ∀ lam : ℂ, doubleAngleDiscriminantBracket m n (realSlice u) lam = 0 :=
  G5035Sup1.core35 u m n hm hn G5035Sup2.angle_local_primitive
    (fun w j hj => (G5025 w j hj).2) (G5032 u m n hm hn) (fun i j hi => G5034 u i j hi)

end
end NlsGge.GKDefinitionDesign

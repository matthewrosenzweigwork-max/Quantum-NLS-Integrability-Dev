import Mathlib
import NlsGge.Atomic.G5.G5031Host
import NlsGge.Atomic.G5.G5031
import NlsGge.Atomic.G5.G5032Sup1
import NlsGge.Atomic.G4.G4040

/- G5-032 PACKET (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5032.lean, namespace NlsGge.GKDefinitionDesign.
   Head `G5032` VERBATIM from followup12 STATEMENTS/G5.md section G5-032 (round 14 cluster 5: uniform lam lexical binders,
   natural-index real casts; the G5-032 head contains no `λ` token, so no lexical repair is applied).
   Host definitions `anglePoisson`, `doubleAngleDiscriminantBracket` are in G5031Host (proof development).
   Proof (GK 18.6): G5032Sup1.core32 with
     (hXY)  reality of cartesianX/Y on the real slice: landed G4040;
     (hper) vanishing of every Abelian period of the double bracket: G5031 (second conjunct).
   core32 applies G2_046 in each gap (reality and entireness of the double bracket proved in G5032Sup1), picks the zero by choice,
   identifies the gap segment with [actualGapLower, actualGapUpper] (landed lamPlus_real), gets injectivity from the quasimomentum
   level sets (landed actualGapLevelSet_eq_Icc_E02_38) and the l2 bound from G1-052. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5032 (u : PhysicalL2) (m n : ℤ)
    (hm : gamma2 (realSlice u) m ≠ 0) (hn : gamma2 (realSlice u) n ≠ 0) :
  ∃ ν : ℤ → ℝ, Function.Injective ν ∧
    (∀ k : ℤ, ν k ∈ Set.Icc (actualGapLowerAllE02_38 u k)
      (actualGapUpperAllE02_38 u k) ∧
      doubleAngleDiscriminantBracket m n (realSlice u) (ν k : ℂ) = 0) ∧
    Memℓp (fun k : ℤ => ν k - (k : ℝ) * Real.pi) 2 :=
  G5032Sup1.core32 (fun j v => ⟨(G4040 v j).1, (G4040 v j).2.1⟩) u m n
    (fun k => (G5031 u m n k hm hn).2)

end
end NlsGge.GKDefinitionDesign

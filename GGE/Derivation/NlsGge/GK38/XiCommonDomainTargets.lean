import NlsGge.GK38.XiSqCanonical

set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GK38

/-- The actual simultaneous principal-root locus, inside the existing certified W. -/
def xiCommonDomain38 : Set PotPair :=
  {φ | φ ∈ gkW ∧ ∀ n : ℤ, xiSq38 n φ ∈ Complex.slitPlane}

/-- One OPEN complex domain containing EVERY real potential, for EVERY signed label.
This states neither connectedness nor equality with the original maximal gkW.
-/
def XiCommonDomainTarget38 : Prop :=
  IsOpen xiCommonDomain38 ∧
    (∀ u : PhysicalL2, realSlice u ∈ xiCommonDomain38) ∧
    (∀ n : ℤ, AnalyticOnNhd ℂ (xiN38 n) xiCommonDomain38)

end NlsGge.GK38

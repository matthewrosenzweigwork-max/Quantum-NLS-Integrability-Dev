import Mathlib
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Atomic.G6.G6003Sup1Core
import NlsGge.Atomic.G6.G6002
import NlsGge.Atomic.G4.G4042

/- G6-003 PACKET (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6003.lean, namespace NlsGge.GKDefinitionDesign.
   Head `G6003` VERBATIM from followup12 STATEMENTS/G6.md section G6-003 (round 14: "retain the existing complete head"); G6 shared
   context opens copied from that file.  No lexical repair.
   Proof (INSTANTIATE, GK Theorem 19.1 + analytic inverse function theorem): G6003Aux.core6003 (LIB-017/LIB-018 chart) for
   f = realBirkhoffCartesian, analytic on univ by landed G4042, derivative equivalence by G6002. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6003 (u : PhysicalL2) :
  ∃ (U : Set PhysicalL2) (V : Set CartesianReal) (g : CartesianReal → PhysicalL2),
    IsOpen U ∧ u ∈ U ∧ IsOpen V ∧ realBirkhoffCartesian u ∈ V ∧
    AnalyticOnNhd ℝ realBirkhoffCartesian U ∧ AnalyticOnNhd ℝ g V ∧
    Set.MapsTo realBirkhoffCartesian U V ∧ Set.MapsTo g V U ∧
    (∀ v ∈ U, g (realBirkhoffCartesian v) = v) ∧
    (∀ z ∈ V, realBirkhoffCartesian (g z) = z) :=
  G6003Aux.core6003 realBirkhoffCartesian u G4042.2.2 (G6002 u).2

end
end NlsGge.GKDefinitionDesign

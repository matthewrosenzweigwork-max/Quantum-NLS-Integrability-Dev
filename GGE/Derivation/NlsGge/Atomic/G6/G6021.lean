import Mathlib
import NlsGge.Atomic.G6.G6021Sup1Core
import NlsGge.Atomic.G6.G6018
import NlsGge.Atomic.G6.G6013
import NlsGge.Atomic.G6.G6013Sup1
import NlsGge.Atomic.G6.G6014
import NlsGge.Atomic.G6.G6015
import NlsGge.Atomic.G6.G6020

/- G6-021 PACKET (proof development, AUTHOR; not self-reviewed, not accepted).  Target NlsGge/Atomic/G6/G6021.lean.
   Head `G6021` VERBATIM from followup12 STATEMENTS/G6.md "## G6-021"; G6 shared opens; no lexical repair.
   Proof (GK Theorem 20.1): G6021Aux.core21 with G6-018, the G6-013 bijectivity/inverse equations, the G6-014 analytic
   inverse and the G6013Sup1 Cartesian equivalence; landed G6-015 (MapsTo) and G6-020 (closedness) are used inside core21.
   See G6021_ROUTE.md: the G6-019 approximation is carried out directly in the physical coordinates. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6021 (u : PhysicalL2) :
  Set.BijOn realBirkhoffCartesian (isospectralSet u) (actionTorus (actionSequence u)) ∧
  Set.BijOn physicalBirkhoff (isospectralSet u) (physicalActionTorus (actionSequence u)) :=
  G6021Aux.core21 G6018 G6013.1 G6013.2.2.2.2.1 G6013.2.2.2.2.2 G6014.2.2.2.1
    exists_physicalCartesianEquiv u

end
end NlsGge.GKDefinitionDesign

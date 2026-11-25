import Mathlib
import NlsGge.Atomic.G6.G6018Sup1Core
import NlsGge.Atomic.G6.G6017
import NlsGge.Atomic.G6.G6013

/- G6-018 PACKET (proof development, AUTHOR; not self-reviewed, not accepted).  Target NlsGge/Atomic/G6/G6018.lean.
   Head `G6018` VERBATIM from followup12 STATEMENTS/G6.md "## G6-018"; G6 shared opens; no lexical repair.
   Proof (GK Theorem 20.1): G6018Aux.core18 with the G6-013 right inverse and the G6-017 head. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6018 (z w : Lib.L2Z)
    (hrad : ∀ n : ℤ, ‖z n‖^2 = ‖w n‖^2)
    (hfin : {n : ℤ | z n ≠ w n}.Finite) :
  (∃ t : ℤ → ℝ, (Function.support t).Finite ∧
    Function.support t ⊆ {n : ℤ | z n ≠ w n} ∧
    ∀ n : ℤ, z n = Complex.exp (-Complex.I * (t n : ℂ)) * w n) ∧
  physicalInverseBirkhoff z ∈ isospectralSet (physicalInverseBirkhoff w) :=
  G6018Aux.core18 G6013.2.2.2.2.2 G6017 z w hrad hfin

end
end NlsGge.GKDefinitionDesign

import Mathlib
import NlsGge.Atomic.G6.G6028Sup3Core
import NlsGge.Atomic.G6.G6013Sup1
import NlsGge.Atomic.X.X004
import NlsGge.Atomic.G4.G4014
import NlsGge.Atomic.G5.G5011
import NlsGge.Atomic.G5.G5012
import NlsGge.Atomic.G5.G5012Sup3
import NlsGge.Atomic.G5.G5032Sup1
import NlsGge.Atomic.G4.G4040
import NlsGge.Atomic.G5.G5040
import NlsGge.Atomic.G6.G6002

/- G6-028 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6028.lean,
   namespace NlsGge.GKDefinitionDesign. Head `G6028` VERBATIM from followup12 STATEMENTS/G6.md section G6-028 (Pro round 14,
   commit 2d599b57; round-14 row G6-028: split the literal small algebra bridge (landed G6013Sup1) from the assembled theorem).
   G6 shared opens copied from that file. No lexical repair.
   Proof: G6028Aux.assemble6028 (G6028Sup3Core) with each hypothesis discharged by the landed theorem of the same content:
   physicalBirkhoff_eq_cartesian (G6013Sup1), X004.samePhi_cartesian_normalization, G4014Aux.cartZ_minus, G5011, G5012,
   gradient_physicalCoordinate (G5012Sup3), G5032Sup1.star_pairGradientCLM_snd / fderiv_realSlice_im, G4040, G5040, G6002.
   Route note (G6028_ROUTE.md): TASK_INDEX lists KSN-001; it is not consumed (the real symplectic clause follows from the
   real canonical relations G5040 via the G6001 pairing and G6002 injectivity). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G6028 :
  (∀ (u : PhysicalL2) (n : ℤ),
    physicalBirkhoff u n =
      (cartesianX n (realSlice u) - Complex.I * cartesianY n (realSlice u)) /
        (Real.sqrt 2 : ℂ) ∧
    physicalBirkhoff u n = xiN38 n (realSlice u) / 2 *
      cartesianZExtended n (-1) (realSlice u) *
      Complex.exp (-Complex.I * betaSum n (realSlice u)) ∧
    actualGapActionAllE02_38 u n = ‖physicalBirkhoff u n‖^2) ∧
  (∀ u : PhysicalL2, HasSum (fun n : ℤ => actualGapActionAllE02_38 u n) (‖u‖^2)) ∧
  (∀ u h k : PhysicalL2,
    inner ℝ ((Complex.I : ℂ) • fderiv ℝ physicalBirkhoff u h)
      (fderiv ℝ physicalBirkhoff u k) = inner ℝ ((Complex.I : ℂ) • h) k) ∧
  fderiv ℝ physicalBirkhoff 0 =
    reflectedFourierL2.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ ∧
  (∀ (u : PhysicalL2) (n : ℤ),
    fderiv ℝ physicalBirkhoff 0 u n = -physicalFourier u (-n)) :=
  G6028Aux.assemble6028 physicalBirkhoff_eq_cartesian
    NlsGge.Atomic.X004.samePhi_cartesian_normalization G4014Aux.cartZ_minus G5011 G5012
    gradient_physicalCoordinate G5032Sup1.star_pairGradientCLM_snd G5032Sup1.fderiv_realSlice_im
    G4040 G5040 G6002

end
end NlsGge.GKDefinitionDesign

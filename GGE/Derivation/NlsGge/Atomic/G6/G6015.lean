import Mathlib
import NlsGge.GK38.PairRealBridge
import NlsGge.Spectral.ActualPhysicalUnitDiscriminantNonrealZeroFree32V1
import NlsGge.Spectral.ActualQuasimomentumE02_38
import NlsGge.Spectral.ActualQuasimomentumBoundaryFunctionE02_38
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
import NlsGge.Herglotz38.HalfPlaneMinPrincipleLimitsE02_38
import NlsGge.Atomic.X.X006
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G6.BirkhoffBasic
import NlsGge.ThirdConsultation.G6.RealCartesianBirkhoff
import NlsGge.Atomic.G6.G6004
import NlsGge.Atomic.G6.G6020

/- G6-015 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6015.lean.
   Head `G6015`: design STATEMENTS/G6.md G6-015 section (identical in gpt6pro_followup9 and followup10), verbatim; no Pro round 4-12
   entry or BINDING_INDEX touches G6-015.  actionTorus / physicalActionTorus: bodies byte-identical to DEFINITIONS/G6.lean.md:86-90
   (followup10); no landed duplicate (grep NlsGge/, Armstrong/), no other owner; hosted here.
   Route: the labelled action I_n = (2/pi) int_{g_n} v is a functional of the half trace Delta_h only (quasimomentum branch predicate,
   boundary value, level sets, gap height); isospectral u v is equality of discriminants = 2 Delta_h (discrim_realSlice).  Hence
   I_n(v) = I_n(u).  Then (x_n^2+y_n^2)/2 = I_n(v) (landed realX_sq_add_realY_sq) and |Phi_n|^2 = I_n(v) (X-006 field Phi_action). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

def actionTorus (I : ActionSequence) : Set CartesianReal :=
  {z | ∀ n : ℤ, (z (true, n)^2 + z (false, n)^2) / 2 = I n}

def physicalActionTorus (I : ActionSequence) : Set Lib.L2Z :=
  {z | ∀ n : ℤ, ‖z n‖^2 = I n}

namespace G6015Aux

theorem halfTrace_eq_of_isospectral {u v : PhysicalL2} (h : isospectral u v) :
    actualPhysicalUnitHalfTrace32 v = actualPhysicalUnitHalfTrace32 u := by
  funext z
  have h1 := h z
  rw [discrim_realSlice, discrim_realSlice] at h1
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  exact mul_left_cancel₀ h2 h1

theorem quasimomentum_eqOn {u v : PhysicalL2}
    (h : actualPhysicalUnitHalfTrace32 v = actualPhysicalUnitHalfTrace32 u) :
    Set.EqOn (actualQuasimomentumE02_38 v) (actualQuasimomentumE02_38 u) {z : ℂ | 0 < z.im} := by
  have hb : IsActualQuasimomentumBranchE02_38 v (actualQuasimomentumE02_38 u) := by
    have hu := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
    unfold IsActualQuasimomentumBranchE02_38 at hu ⊢
    rw [h]
    exact hu
  exact actualQuasimomentumE02_38_eqOn_of_isBranch v _ hb

theorem boundary_eq {u v : PhysicalL2}
    (h : actualPhysicalUnitHalfTrace32 v = actualPhysicalUnitHalfTrace32 u) (x : ℝ) :
    actualQuasimomentumBoundaryE02_38 v x = actualQuasimomentumBoundaryE02_38 u x := by
  have hNe : (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_upperHalfPlane_E02_38 (by simp))
  have h1 := tendsto_actualQuasimomentumBoundaryE02_38 v x
  have h2 := tendsto_actualQuasimomentumBoundaryE02_38 u x
  have h3 : Tendsto (actualQuasimomentumE02_38 u) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (actualQuasimomentumBoundaryE02_38 v x)) :=
    h1.congr' (eventually_nhdsWithin_of_forall (quasimomentum_eqOn h))
  exact tendsto_nhds_unique h3 h2

theorem gapAction_eq {u v : PhysicalL2} (h : isospectral u v) (n : ℤ) :
    actualGapActionAllE02_38 v n = actualGapActionAllE02_38 u n := by
  have hΔ := halfTrace_eq_of_isospectral h
  have hp : actualQuasimomentumRealPartE02_38 v = actualQuasimomentumRealPartE02_38 u := by
    funext x
    simp only [actualQuasimomentumRealPartE02_38, boundary_eq hΔ x]
  have hset : actualGapLevelSetE02_38 v n = actualGapLevelSetE02_38 u n := by
    simp only [actualGapLevelSetE02_38, hp]
  have hv : actualGapHeightE02_38 v = actualGapHeightE02_38 u := by
    funext x
    simp only [actualGapHeightE02_38, hΔ]
  simp only [actualGapActionAllE02_38, actualGapLowerAllE02_38, actualGapUpperAllE02_38, hset, hv]

end G6015Aux

theorem G6015 (u : PhysicalL2) :
  realBirkhoffCartesian '' isospectralSet u ⊆ actionTorus (actionSequence u) ∧
  physicalBirkhoff '' isospectralSet u ⊆ physicalActionTorus (actionSequence u) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩ n
    rw [realBirkhoffCartesian_true, realBirkhoffCartesian_false, g6_actionSequence_apply,
      ← G6015Aux.gapAction_eq hv n]
    have := realX_sq_add_realY_sq n v
    linarith
  · rintro _ ⟨v, hv, rfl⟩ n
    show ‖sourceFamily.Phi v n‖ ^ 2 = actionSequence u n
    rw [g6_actionSequence_apply, ← G6015Aux.gapAction_eq hv n]
    exact sourceFamily.Phi_action v n

end
end NlsGge.GKDefinitionDesign

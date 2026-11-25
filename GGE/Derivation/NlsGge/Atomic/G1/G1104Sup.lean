import NlsGge.Atomic.G1.G1104Host
import NlsGge.GK38.GradEigenStateL2
import NlsGge.GK38.PairRealBridge

/-!
# G1-104 supports (no root-space content): head as a Prop, clause 2 from clause 1,
# and the legitimacy obligation `sourceIntervalClass_spec`.
-/

set_option autoImplicit false

open NlsGge.Schur NlsGge.Atomic.Interval
open NlsGge.Atomic.LIB033 NlsGge.Atomic.LIB038 NlsGge.Atomic.LIB041
open NlsGge.Atomic.LIB042
open NlsGge.Pilot NlsGge.GK38 MeasureTheory
open NlsGge.GKDefinitionDesign

namespace NlsGge.Atomic.G1104Sup
noncomputable section

/-- Clause 1 of Pro's G1_104 head. -/
def Clause1 (φ : PotPair) : Prop :=
  ∀ bc : ZSBoundaryCondition, ∀ z : ℂ,
    FiniteDimensional ℂ (rootSpace (zsRealization (intervalPotential φ) bc) z) ∧
    analyticOrderAt (boundaryCharacteristic φ bc) z ≠ ⊤ ∧
    (algebraicMultiplicity (zsRealization (intervalPotential φ) bc) z : ℕ∞) =
      analyticOrderAt (boundaryCharacteristic φ bc) z

/-- Clause 2 of Pro's G1_104 head. -/
def Clause2 (φ : PotPair) : Prop :=
  ∀ z : ℂ,
    ((algebraicMultiplicity
        (zsRealization (intervalPotential φ) .periodic) z +
      algebraicMultiplicity
        (zsRealization (intervalPotential φ) .antiperiodic) z : ℕ) : ℕ∞) =
      analyticOrderAt (perChar φ) z

theorem clause2_of_clause1 (φ : PotPair) (h : Clause1 φ) : Clause2 φ := by
  intro z
  have hΔ : AnalyticAt ℂ (discrim φ) z := analyticOnNhd_discrim_z φ z (Set.mem_univ z)
  have hp : AnalyticAt ℂ (fun w => discrim φ w - 2) z := hΔ.sub analyticAt_const
  have ha : AnalyticAt ℂ (fun w => discrim φ w + 2) z := hΔ.add analyticAt_const
  have hper := (h .periodic z).2.2
  have hant := (h .antiperiodic z).2.2
  have hfun : perChar φ = (fun w => discrim φ w - 2) * (fun w => discrim φ w + 2) := by
    funext w
    simp only [perChar_eq, Pi.mul_apply]
    ring
  rw [hfun, analyticOrderAt_mul hp ha, Nat.cast_add]
  exact congrArg₂ (· + ·) hper hant

theorem sourceIntervalClass_spec (f : PhysicalL2) :
    MemLp (coverRep38 f) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
    (fun t : ℝ => sourceIntervalClass f t) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      coverRep38 f := by
  have hmem : MemLp (coverRep38 f) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (NlsGge.GK38.GradEigen38.memLp_coverRep_unit f).mono_measure
      (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
  refine ⟨hmem, ?_⟩
  have h : sourceIntervalClass f = hmem.toLp (coverRep38 f) := by
    simp only [sourceIntervalClass, hmem, dite_true]
  rw [h]
  exact hmem.coeFn_toLp

end
end NlsGge.Atomic.G1104Sup

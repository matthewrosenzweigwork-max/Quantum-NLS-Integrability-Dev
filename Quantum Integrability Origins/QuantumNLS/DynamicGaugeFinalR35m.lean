import QuantumNLS.TerraMultiHeadlineR95
import QuantumNLS.TerraMultiFinalR94
import QuantumNLS.ActualModelCorollaryR60a
import QuantumNLS.FullWickO3
import QuantumNLS.RB7BindFinal

/-! Final binding of R-8362E5EB at the named R-D51987CA witness. -/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

noncomputable section

open Filter Topology
open scoped Classical

namespace QuantumNLS.DynamicGaugeFinalR35m

open Def033HierarchyR24m (Smooth physical)
open ReconstructionR33m (flows RD8362E5EBInput)
open UniformStaticR31m

variable {L κ : ℝ} [Fact (0 < L)]

abbrev hierarchy (hκ : 0 < κ) :=
  RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ

abbrev stage (hκ : 0 < κ) :=
  RetargetSelectionR49b.sectorStage (L := L) hκ

abbrev arrayGauge (hκ : 0 < κ) : FullGauge :=
  RetargetSelectionR49b.sectorGauge (L := L) hκ

abbrev gauge (hκ : 0 < κ) :=
  DynamicGaugePhysicalR34m.physicalGauge (arrayGauge (L := L) hκ)

/-- The R95 physical headline expresses this same scalar on each complete array.
The basis rephasing is the conjugate of the coefficient multiplier. -/
theorem gauge_conj (hκ : 0 < κ) (n : ℕ) (m : BetheLabels.MArr (n+1)) :
    (gauge (L := L) hκ (n+1) m).val =
      star ((RetargetPhysicalR48b.gauge (arrayGauge (L := L) hκ) (n+1) m).val) := rfl

/-- The retargeting clauses in the exact R34m witness format. -/
def RetargetingAt (hκ : 0 < κ) (j : ℕ → ℕ) (q : FullGauge) : Prop :=
  Monotone j ∧ Tendsto j atTop atTop ∧
  (∀ S > 0, UniformError (unitBall (L := L) S)
    (fun n _ => pairs (j n)) (cartesianError hκ q)) ∧
  (∀ S > 0, ∀ α > 0, ∀ ε > 0, ∀ᶠ n in atTop,
    ∀ u ∈ unitBall (L := L) S, ∀ p ∈ eligible hκ (j n) α u,
      phaseError hκ q n u p ≤ ε ∧ missingInitial hκ n u p ≤ ε ∧
      missingFinal hκ n u p ≤ ε ∧ affinityError hκ n u p ≤ ε ∧
      defectError hκ q n u p ≤ ε) ∧
  ExteriorExact

private theorem retargeting_at_named_pair (hκ : 0 < κ) :
    RetargetingAt (L := L) hκ (stage (L := L) hκ) (arrayGauge (L := L) hκ) := by
  obtain ⟨hmono, hlim, -, -, -, -, -, -, -, hcart, hphase, hcoeff⟩ :=
    TerraMultiHeadlineR95.audit_gauge_retargeting (L := L) hκ
  have hs (n : ℕ) :
      RetargetPhysicalR48b.physicalSchedule (stage (L := L) hκ) (n+1) =
        stage (L := L) hκ n := by simp only [RetargetPhysicalR48b.physicalSchedule, Nat.add_sub_cancel]
  have hstage : (fun n : ℕ =>
      RetargetPhysicalR48b.physicalSchedule (stage (L := L) hκ) (n+1)) =
      stage (L := L) hκ := funext hs
  refine ⟨?_, ?_, ?_, ?_, fun n => UniformStaticR49b.exterior_exact (n+1)⟩
  · rw [← hstage]
    exact hmono.comp (fun _ _ hab => Nat.succ_le_succ hab)
  · rw [← hstage]
    exact hlim.comp (tendsto_add_atTop_nat 1)
  · intro S _ ε hε
    filter_upwards [hcart S ε hε] with n hn
    intro u hu p hp
    obtain ⟨a, b, rfl⟩ := (UniformStaticBridgeR50b.mem_pairs_iff_labels _ _).mp hp
    exact hn u hu a b
  · intro S _ α hα ε hε
    filter_upwards [hphase S α (ε/2) hα (half_pos hε), hcoeff S α ε hα hε]
      with n hphys harray
    intro u hu p hp
    obtain ⟨hp, hab, ha, hb⟩ := Finset.mem_filter.mp hp
    obtain ⟨a, b, rfl⟩ := (UniformStaticBridgeR50b.mem_pairs_iff_labels _ _).mp hp
    obtain ⟨hf, hr⟩ := hphys u hu a b hab ha hb
    obtain ⟨_, _, hi, hj, hA, hD, _⟩ := harray u hu a b hab ha hb
    refine ⟨?_, hi, hj, hA, ?_⟩
    · change UniformStaticR49b.phaseError hκ (arrayGauge (L := L) hκ) n u (a.val, b.val) ≤ ε
      unfold UniformStaticR49b.phaseError UniformStaticR49b.W
      rw [UniformStaticR49b.phase_eq_pairPhase]
      exact (add_le_add hf hr).trans (by linarith)
    · change UniformStaticR49b.defectError hκ (arrayGauge (L := L) hκ) n u (a.val, b.val) ≤ ε
      unfold UniformStaticR49b.defectError
      rw [UniformStaticR49b.phase_eq_pairPhase]
      exact hD

private theorem mixed (hκ : 0 < κ) :
    TerraMultiRound88Input.RE679E41DInput hκ (hierarchy (L := L) hκ) := by
  intro u hu I R k Θ T hΘ hT
  exact (ActualModelCorollaryR60a.actual_model hκ u hu I R k Θ T hΘ hT).2

private theorem full_torus (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) :
    DynSeedInputR47b.DynftFullTorusInput hκ (flows hκ (hierarchy hκ)) u R :=
  TerraMultiFinalR94.full_torus_r47 hκ u hu R

private theorem seed (hκ : 0 < κ) :
    DynamicGaugeR34m.R300B8640Input hκ (flows hκ (hierarchy (L := L) hκ)) := by
  intro u hu R lo hi a b hab _
  let C := ActualModelBindingR53a.chart (L := L) hκ
  have hC := ActualModelBindingR53a.printed_chart (L := L) hκ
  have h := (TerraMultiFinalR94.chain_named_final hκ C.Φ hC u hu R lo hi a b hab).1
  simpa only [DynSeedR47b.SeedStatement, DynSeedR47b.boxResidual,
    TerraMultiRound93Flow.selected_orbit_eq hκ C.Φ hC u R] using h

/-- R-8362E5EB, printed as prop:audit-dynamic-gauge. All dynamic symbols
use the single Q06 array gauge from the R-D51987CA headline. -/
theorem audit_dynamic_gauge (hκ : 0 < κ) :
    RD8362E5EBInput hκ (flows hκ (hierarchy (L := L) hκ)) (gauge (L := L) hκ) := by
  obtain ⟨_, hlim, _, hphase, _⟩ := retargeting_at_named_pair (L := L) hκ
  exact FullWickO3.rd8362_of_witness hκ (hierarchy (L := L) hκ) (mixed hκ)
    (full_torus hκ) (seed hκ) (stage (L := L) hκ) (arrayGauge (L := L) hκ) hlim
    (fun S hS α hα ε hε => (hphase S hS α hα ε hε).mono
      (fun _ hn u hu p hp => (hn u hu p hp).1))

/-- The complete R34m result, witnessed by the fixed R-D51987CA pair. -/
theorem dynamic_gauge_conclusion (hκ : 0 < κ) :
    ∃ (j : ℕ → ℕ) (q : FullGauge),
      Monotone j ∧ Tendsto j atTop atTop ∧
      (∀ S > 0, UniformError (unitBall (L := L) S)
        (fun n _ => pairs (j n)) (cartesianError hκ q)) ∧
      (∀ S > 0, ∀ α > 0, ∀ ε > 0, ∀ᶠ n in atTop,
        ∀ u ∈ unitBall (L := L) S, ∀ p ∈ eligible hκ (j n) α u,
          phaseError hκ q n u p ≤ ε ∧ missingInitial hκ n u p ≤ ε ∧
          missingFinal hκ n u p ≤ ε ∧ affinityError hκ n u p ≤ ε ∧
          defectError hκ q n u p ≤ ε) ∧
      ExteriorExact ∧
      RD8362E5EBInput hκ (flows hκ (hierarchy (L := L) hκ))
        (DynamicGaugePhysicalR34m.physicalGauge q) := by
  obtain ⟨hm, ht, hc, hp, he⟩ := retargeting_at_named_pair (L := L) hκ
  exact ⟨stage (L := L) hκ, arrayGauge (L := L) hκ, hm, ht, hc, hp, he,
    audit_dynamic_gauge (L := L) hκ⟩

private theorem retargeting (hκ : 0 < κ) : GaugeRetargetingRD51987CAInput (L := L) hκ :=
  ⟨stage (L := L) hκ, arrayGauge (L := L) hκ, retargeting_at_named_pair (L := L) hκ⟩

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let final ← getConstInfo ``dynamic_gauge_conclusion
  forallTelescope final.type fun domain expected => do
    let atParameters (name : Name) := mkAppN (mkConst name) domain
    let frozen := mkAppN (atParameters ``DynamicGaugeR34m.dynamic_gauge_ofInput)
      #[atParameters ``retargeting, atParameters ``hierarchy, atParameters ``mixed,
        atParameters ``full_torus, atParameters ``seed]
    unless ← isDefEq (← inferType frozen) expected do
      throwError "Final conclusion differs from the instantiated R34m conclusion"
    logInfo "R34M_CONCLUSION_TYPE PASS (definitionally identical after binding the five inputs)"

end QuantumNLS.DynamicGaugeFinalR35m

#print axioms QuantumNLS.DynamicGaugeFinalR35m.audit_dynamic_gauge
#print axioms QuantumNLS.DynamicGaugeFinalR35m.dynamic_gauge_conclusion

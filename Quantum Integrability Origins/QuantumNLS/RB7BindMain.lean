import Mathlib
import QuantumNLS.RB7BindTopology
import QuantumNLS.RB7BindChart

/-!
# R-7B122087 shared-input bridge, part 3: `HierarchyInputR25m.HierarchyR7B122087Input` holds (RB7BindMain)

Source: `source-text/chapters/core/DYNAMICS_LEMMAS.tex:115-128` (`thm:hierarchy`).

`hierarchyInputR25m_holds hκ hO hJ : HierarchyInputR25m.HierarchyR7B122087Input hκ`: for every `w` with the printed
chart hypotheses (and the three further antecedents, which are not needed in the proof: they are consequences of the
accepted theorems, see `RB7BindChart`), the complete printed conclusion `HierarchyConclusion w masses` holds, with
the SINGLE family `Φ r = RB7.chartFlow (REG015_final) (chartFactsOf C)` where `C` is the actual DEF-021 chart with
`w = C.Φ` (`RB7BindChart.actual_chart_of_printed`).

Exactly two inputs are taken, and only for the two clauses haiku_inventory is still proving, as explicit hypotheses in
the frozen `RB7FinalAll` form, for the finite order sets `R` consisting of orders `≥ 2` only:

* `hO R : RB7.OrbitCompactInput L κ R`  (clause (4): closure of the full joint orbit in `∏_k H^k` is compact);
* `hJ R : RB7.JointContInput L κ R`      (clause (5): joint flow continuous on compact `(ℕ → ℝ) × SmoothProf` boxes).

They are transported to the topology of `Def033HierarchyR24m.Smooth` with `RB7BindTopology.smoothHomeo` (the two smooth
topologies coincide) and `RB7BindTopology.isCompact_closure_of` (limits of jets are jets of smooth profiles).
Clause (4) for one order is the case `R = {r}`; the extra finite-joint-orbit clause of `HierarchyConclusion` is the
case of arbitrary `R`.  Everything else (clauses (1), (2), (3), (6), the actions) is proved from `REG015_final`
without further input.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology NNReal ContDiff
open Filter

namespace QuantumNLS.RB7BindMain

open QuantumNLS.RB7 QuantumNLS.RB7BindTopology QuantumNLS.RB7BindChart QuantumNLS.ClassicalCharges
open QuantumNLS.HierarchyFlow QuantumNLS.PhysicalTensor QuantumNLS.Sobolev
open QuantumNLS.Def033HierarchyR24m (Smooth physical jointSmooth smoothStep)
open QuantumNLS.REF88PrintedChart (PrintedChart)

variable {L κ : ℝ} [Fact (0 < L)]

/-! ## Transport of clause (4) to the topology of `Smooth L` -/

/-- Relative compactness of the full joint orbit in `Smooth L`, from `OrbitCompactInput` for the same `R`. -/
theorem joint_orbit_compact {R : Finset ℕ} (hO : OrbitCompactInput L κ R) (F : HamFlows L κ R) (u : Smooth L) :
    IsCompact (closure (Set.range fun t : ℕ → ℝ => jointSmooth F t u)) := by
  let e : Smooth L ≃ₜ SmoothProf L := smoothHomeo
  let g : (ℕ → ℝ) → Smooth L := fun t => jointSmooth F t u
  rw [← e.isCompact_image, e.image_closure]
  refine isCompact_closure_of ?_
  have hfun : (J ∘ (e ∘ g)) = fun t : ℕ → ℝ =>
      (jetOf (L := L) (jointClassicalFlow F t u.val) : ∀ k : ℕ, H02 L (k : ℝ)) := by
    funext t
    show (fun k => jetOf (L := L) (jointSmooth F t u).val k) = _
    rw [jointSmooth_val]
  rw [← Set.range_comp, ← Set.range_comp, hfun]
  exact hO F ⟨u.val, u.property⟩

/-- For `R = {r}` the joint flow is the single flow at time `t r`. -/
theorem joint_singleton {hκ : 0 < κ} (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    (t : ℕ → ℝ) (v : ℝ → ℂ) :
    jointClassicalFlow (chartHamFlows hR C {r}) t v = chartFlow hR C r (t r) v := by
  simp [jointClassicalFlow, Finset.sort_singleton, chartHamFlows]

/-- The orbit of one order is the joint orbit of the family `{r}`. -/
theorem single_range_eq {hκ : 0 < κ} (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    (u : Smooth L) :
    Set.range (fun t : ℝ => (⟨chartFlow hR C r t u.val, ((isHamFlow_chart hR C r u.val u.property).2.2 t).1⟩ :
        Smooth L)) =
      Set.range (fun t : ℕ → ℝ => jointSmooth (chartHamFlows hR C {r}) t u) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨fun _ => t, Subtype.ext ?_⟩
    rw [jointSmooth_val, joint_singleton]
  · rintro ⟨t, rfl⟩
    refine ⟨t r, Subtype.ext ?_⟩
    show _ = (jointSmooth (chartHamFlows hR C {r}) t u).val
    rw [jointSmooth_val, joint_singleton]

/-! ## Transport of clause (5) to the topology of `Smooth L` -/

/-- Joint continuity on compact classes and compact time boxes in the topology of `Smooth L`, from `JointContInput`. -/
theorem joint_continuous {R : Finset ℕ} (hJ : JointContInput L κ R) (F : HamFlows L κ R)
    (K : Set (Smooth L)) (hK : IsCompact K) (B : Set (ℕ → ℝ)) (hB : IsCompact B) :
    ContinuousOn (fun p : Smooth L × (ℕ → ℝ) => jointSmooth F p.2 p.1) (K ×ˢ B) := by
  let e : Smooth L ≃ₜ SmoothProf L := smoothHomeo
  have hKp : IsCompact (e '' K) := hK.image e.continuous
  have h1 := hJ F (e '' K) B hKp hB
  let G : (ℕ → ℝ) × SmoothProf L → SmoothProf L := fun p => e (jointSmooth F p.1 (e.symm p.2))
  have hG : ContinuousOn G (B ×ˢ (e '' K)) := by
    rw [isInducing_J.continuousOn_iff]
    refine h1.congr (fun p _ => ?_)
    funext k
    show jetOf (L := L) (jointSmooth F p.1 (e.symm p.2)).val k =
      jetOf (L := L) (jointClassicalFlow F p.1 p.2.val) k
    rw [jointSmooth_val]
    rfl
  have hin : Continuous fun p : Smooth L × (ℕ → ℝ) => ((p.2, e p.1) : (ℕ → ℝ) × SmoothProf L) :=
    Continuous.prodMk continuous_snd (e.continuous.comp continuous_fst)
  have hmaps : Set.MapsTo (fun p : Smooth L × (ℕ → ℝ) => ((p.2, e p.1) : (ℕ → ℝ) × SmoothProf L))
      (K ×ˢ B) (B ×ˢ (e '' K)) := fun p hp => ⟨hp.2, ⟨p.1, hp.1, rfl⟩⟩
  have h2 := e.symm.continuous.comp_continuousOn (hG.comp hin.continuousOn hmaps)
  refine h2.congr (fun p _ => ?_)
  show jointSmooth F p.2 p.1 = e.symm (e (jointSmooth F p.2 (e.symm (e p.1))))
  simp

/-! ## The complete printed conclusion at an actual chart -/

/-- **The full `HierarchyConclusion` at every actual DEF-021 chart**, from `REG015_final` and the two frozen inputs for
clauses (4) and (5). -/
theorem hierarchyConclusion_of_chart (hκ : 0 < κ) (C0 : Def021ChartR41b.Chart L κ hκ)
    (hO : ∀ R : Finset ℕ, (∀ r ∈ R, 2 ≤ r) → OrbitCompactInput L κ R)
    (hJ : ∀ R : Finset ℕ, (∀ r ∈ R, 2 ≤ r) → JointContInput L κ R) :
    QuantumNLS.HierarchyInputR25m.HierarchyConclusion (κ := κ) C0.Φ
      (fun u n => (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) := by
  have hR : REG015Concl (L := L) hκ := QuantumNLS.Reg015HFinal.REG015_final (L := L) hκ
  let CF : ChartFacts (L := L) hκ := chartFactsOf C0
  refine ⟨fun r => chartFlow hR CF r, fun r _ => isHamFlow_chart hR CF r, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun r _ => unique_chart hR CF r
  · exact fun r s _ _ u t τ => clause_comm hR CF r s u t τ
  · exact fun r _ u n => clause_rotation hR CF r u n
  · intro r hr u
    have h := joint_orbit_compact (hO {r} (by simpa using hr)) (chartHamFlows hR CF {r}) u
    rwa [← single_range_eq hR CF r u] at h
  · intro R hRr F K hK T _
    refine joint_continuous (hJ R hRr) F K hK _ ?_
    refine isCompact_univ_pi (fun r => ?_)
    split_ifs
    · exact isCompact_Icc
    · exact isCompact_singleton
  · intro R hRr u F
    exact joint_orbit_compact (hO R hRr) F u
  · exact fun r _ u t j => clause_charge hR CF r u t j
  · exact fun r _ u t n => clause_action hR CF r u t n

/-- **`HierarchyInputR25m.HierarchyR7B122087Input hκ` holds**, given the two frozen inputs for clauses (4), (5). -/
theorem hierarchyInputR25m_holds (hκ : 0 < κ)
    (hO : ∀ R : Finset ℕ, (∀ r ∈ R, 2 ≤ r) → OrbitCompactInput L κ R)
    (hJ : ∀ R : Finset ℕ, (∀ r ∈ R, 2 ≤ r) → JointContInput L κ R) :
    QuantumNLS.HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ := by
  intro w hw _ _ _
  obtain ⟨C0, rfl⟩ := actual_chart_of_printed hκ hw
  exact hierarchyConclusion_of_chart hκ C0 hO hJ

/-- The printed theorem with all four antecedents PROVED (not assumed): at the actual chart `w`, the printed chart
hypotheses, the Sobolev homeomorphisms, scalar uniqueness and scalar moment identification all hold, and so does the
complete conclusion. -/
theorem printed_theorem_with_antecedents (hκ : 0 < κ)
    (hO : ∀ R : Finset ℕ, (∀ r ∈ R, 2 ≤ r) → OrbitCompactInput L κ R)
    (hJ : ∀ R : Finset ℕ, (∀ r ∈ R, 2 ≤ r) → JointContInput L κ R) :
    ∃ w : L2T L → QuantumNLS.REF88Chart.K, PrintedChart hκ w ∧
      QuantumNLS.HierarchyInputR25m.SobolevHomeomorphisms w ∧
      QuantumNLS.HierarchyInputR25m.ScalarUniqueness (L := L) hκ ∧
      QuantumNLS.HierarchyInputR25m.ScalarMomentIdentification (L := L) hκ ∧
      QuantumNLS.HierarchyInputR25m.HierarchyConclusion (κ := κ) w
        (fun u n => (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) := by
  obtain ⟨C0, hC0, -⟩ := printedChart_antecedent (L := L) hκ
  exact ⟨C0.Φ, hC0, sobolev_antecedent hκ C0.Φ hC0, scalarUniqueness_antecedent hκ,
    scalarMoments_antecedent hκ, hierarchyConclusion_of_chart hκ C0 hO hJ⟩

end QuantumNLS.RB7BindMain

#print axioms QuantumNLS.RB7BindMain.joint_orbit_compact
#print axioms QuantumNLS.RB7BindMain.single_range_eq
#print axioms QuantumNLS.RB7BindMain.joint_continuous
#print axioms QuantumNLS.RB7BindMain.hierarchyConclusion_of_chart
#print axioms QuantumNLS.RB7BindMain.hierarchyInputR25m_holds
#print axioms QuantumNLS.RB7BindMain.printed_theorem_with_antecedents

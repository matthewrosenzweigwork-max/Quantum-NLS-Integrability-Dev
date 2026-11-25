import Mathlib
import QuantumNLS.RB7FinalAll
import QuantumNLS.Def044ChartR28m
import QuantumNLS.Def033SobolevR25m
import QuantumNLS.HierarchyInputR25m

/-!
# R-7B122087 shared-input bridge, part 2: the caller's chart and the clauses that need no input (RB7BindChart)

`HierarchyInputR25m.HierarchyR7B122087Input hκ` quantifies over every `w` with
`REF88PrintedChart.PrintedChart hκ w` (symplectic, analytic, exact moduli, Fourier derivative at `0`,
conjugation-reflection).  The frozen RB7 modules are parametric in an abstract
`RB7.ChartFacts hκ` record, which has no normalization and no equality to the caller's `w`.  This module
closes that gap and proves the clauses of `HierarchyConclusion` that do not involve the smooth topology.

* `chartFactsOf C`: the `RB7.ChartFacts` record of an actual DEF-021 chart `C` (every field is a field of
  `Def021ChartR41b.Chart`; same `Φ`, `Ψ`).
* `actual_chart_of_printed`: for every printed chart `w` there is an actual DEF-021 chart `C` with `w = C.Φ`
  (`Def044ChartR28m.printed_chart_maps`, i.e. the uniqueness clause of `GlobalCompatR47a`).  Hence the RB7 machinery
  instantiated at `chartFactsOf C` is the machinery at the caller's `w`.
* The four R25m antecedents as Lean outputs, in exactly the form of `HierarchyInputR25m`:
  `printedChart_antecedent` (an actual `w`, with all printed hypotheses, exists, and every `w` with them is `C.Φ`),
  `sobolev_antecedent` (`SobolevHomeomorphisms w` for every printed `w`, from `REG015_final`),
  `scalarUniqueness_antecedent`, `scalarMoments_antecedent` (accepted `root_scalar_uniqueness`, `R_275B7656`).
* The clauses of `HierarchyConclusion` at the single family `Φ r = RB7.chartFlow hR C r` that need neither orbit
  compactness nor joint continuity: uniqueness, commutation (all orders `r, s`), the rotation law
  `w (Φ_r t u) n = phase t freq * w u n` with ONE real `freq` independent of `t` (and `phase t ω = exp(-i t ω)`),
  conservation of every DEF-022 charge `charge L κ`, conservation of the indexed masses.

REG-015 enters only through `Reg015HFinal.REG015_final`.  No sorry, no new axiom, no hypothesis on the hierarchy.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology NNReal ContDiff

namespace QuantumNLS.RB7BindChart

open QuantumNLS.RB7 QuantumNLS.ClassicalCharges QuantumNLS.HierarchyFlow QuantumNLS.PhysicalTensor
open QuantumNLS.Reg015Setting QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.Def033HierarchyR24m (Smooth physical)
open QuantumNLS.REF88PrintedChart (PrintedChart)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The `RB7.ChartFacts` record of an actual DEF-021 chart: same maps, every field is a field of `Chart`. -/
def chartFactsOf {hκ : 0 < κ} (C : Def021ChartR41b.Chart L κ hκ) : ChartFacts (L := L) hκ where
  Φ := C.Φ
  Ψ := C.Ψ
  ΦΨ := C.right_inverse
  mass := C.actions
  ana_Φ := C.analytic
  ana_Ψ := C.inverse_analytic
  ΨΦ := C.left_inverse
  symp := C.symplectic
  iso := C.differential

theorem chartFactsOf_Φ {hκ : 0 < κ} (C : Def021ChartR41b.Chart L κ hκ) : (chartFactsOf C).Φ = C.Φ := rfl

/-- Every printed chart is the `Φ` of an actual DEF-021 chart. -/
theorem actual_chart_of_printed (hκ : 0 < κ) {w : L2T L → QuantumNLS.REF88Chart.K} (hw : PrintedChart hκ w) :
    ∃ C : Def021ChartR41b.Chart L κ hκ, w = C.Φ := by
  obtain ⟨C⟩ := Def021ChartR41b.chart_exists L κ hκ
  exact ⟨C, (Def044ChartR28m.printed_chart_maps hκ C w hw).1⟩

/-! ## The four antecedents of `HierarchyInputR25m` as Lean outputs -/

/-- Antecedent 1: a chart with all the printed hypotheses exists (an actual DEF-021 chart), and every chart with them
is its `Φ`. -/
theorem printedChart_antecedent (hκ : 0 < κ) :
    ∃ C : Def021ChartR41b.Chart L κ hκ, PrintedChart hκ C.Φ ∧
      ∀ w : L2T L → QuantumNLS.REF88Chart.K, PrintedChart hκ w → w = C.Φ := by
  obtain ⟨C⟩ := Def021ChartR41b.chart_exists L κ hκ
  exact ⟨C, Def044ChartR28m.printed_chart hκ C, fun w hw =>
    (Def044ChartR28m.printed_chart_maps hκ C w hw).1⟩

/-- Antecedent 2, exactly `HierarchyInputR25m.SobolevHomeomorphisms w`, for every printed chart (`REG015_final`). -/
theorem sobolev_antecedent (hκ : 0 < κ) (w : L2T L → QuantumNLS.REF88Chart.K) (hw : PrintedChart hκ w) :
    QuantumNLS.HierarchyInputR25m.SobolevHomeomorphisms w :=
  QuantumNLS.Def033SobolevR25m.sobolev_homeomorphisms hκ w hw

/-- Antecedent 3, exactly `HierarchyInputR25m.ScalarUniqueness hκ` (accepted `root_scalar_uniqueness`). -/
theorem scalarUniqueness_antecedent (hκ : 0 < κ) :
    QuantumNLS.HierarchyInputR25m.ScalarUniqueness (L := L) hκ :=
  QuantumNLS.HierarchyInputR25m.scalar_uniqueness hκ

/-- Antecedent 4, exactly `HierarchyInputR25m.ScalarMomentIdentification hκ` (accepted `R_275B7656`). -/
theorem scalarMoments_antecedent (hκ : 0 < κ) :
    QuantumNLS.HierarchyInputR25m.ScalarMomentIdentification (L := L) hκ :=
  QuantumNLS.HierarchyInputR25m.scalar_moments hκ

/-! ## Clauses of `HierarchyConclusion` that need neither (4) nor (5) -/

variable {hκ : 0 < κ}

/-- Commutation of any two flows, in the form of `HierarchyConclusion`. -/
theorem clause_comm (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r s : ℕ)
    (u : Smooth L) (t τ : ℝ) :
    chartFlow hR C r t (chartFlow hR C s τ u.val) = chartFlow hR C s τ (chartFlow hR C r t u.val) :=
  comm_chart_pair hR C r s t τ u.property

/-- The rotation law in the chart coordinates, in the form of `HierarchyConclusion`: one real frequency per datum
and coordinate, valid for all real times (`phase t ω = exp(-i t ω)`). -/
theorem clause_rotation (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    (u : Smooth L) (n : ℤ) :
    ∃ freq : ℝ, ∀ t : ℝ,
      C.Φ (physical ⟨chartFlow hR C r t u.val, ((isHamFlow_chart hR C r u.val u.property).2.2 t).1⟩) n =
        QuantumNLS.Def033CoreR24m.phase t freq * C.Φ (physical u) n := by
  refine ⟨FreqSeq ((SOf r : ℝ≥0) : ℝ) (Fd hR C r) (fun m => C.Φ (smoothL2 u.property) m) n, fun t => ?_⟩
  have h := rotation_form hR C r (isHamFlow_chart hR C r) u.property t
    ((isHamFlow_chart hR C r u.val u.property).2.2 t).1 n
  refine h.trans ?_
  show Complex.exp _ * _ = Complex.exp (-((t * _ : ℝ) : ℂ) * Complex.I) * _
  rw [Complex.ofReal_neg]
  rfl

/-- Conservation of every DEF-022 charge `charge L κ · j`, `j : ℕ`. -/
theorem clause_charge (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    (u : Smooth L) (t : ℝ) (j : ℕ) :
    charge L κ (chartFlow hR C r t u.val) j = charge L κ u.val j :=
  charge_conserved hR C r (isHamFlow_chart hR C r) u.property t
    ((isHamFlow_chart hR C r u.val u.property).2.2 t).1 j

/-- Conservation of the indexed actions (masses), in the form of `HierarchyConclusion`. -/
theorem clause_action (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    (u : Smooth L) (t : ℝ) (n : ℤ) :
    (QuantumNLS.RootIndexedMasses.masses hκ
        (physical ⟨chartFlow hR C r t u.val, ((isHamFlow_chart hR C r u.val u.property).2.2 t).1⟩)).1 n =
      (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 n :=
  actions_conserved hR C r (isHamFlow_chart hR C r) u.property t
    ((isHamFlow_chart hR C r u.val u.property).2.2 t).1 n

end QuantumNLS.RB7BindChart

#print axioms QuantumNLS.RB7BindChart.chartFactsOf
#print axioms QuantumNLS.RB7BindChart.actual_chart_of_printed
#print axioms QuantumNLS.RB7BindChart.printedChart_antecedent
#print axioms QuantumNLS.RB7BindChart.sobolev_antecedent
#print axioms QuantumNLS.RB7BindChart.scalarUniqueness_antecedent
#print axioms QuantumNLS.RB7BindChart.scalarMoments_antecedent
#print axioms QuantumNLS.RB7BindChart.clause_comm
#print axioms QuantumNLS.RB7BindChart.clause_rotation
#print axioms QuantumNLS.RB7BindChart.clause_charge
#print axioms QuantumNLS.RB7BindChart.clause_action

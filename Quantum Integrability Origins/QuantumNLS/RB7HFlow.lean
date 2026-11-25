import Mathlib
import QuantumNLS.RB7HJoint
import QuantumNLS.RB7HCurve
import QuantumNLS.HierarchyFlow

/-!
# R-7B122087 `thm:hierarchy`, sub-obligation A7b(b): the function-level flow `Φ_s` in the `IsHamFlow` form (RB7H, haiku_inventory)

`physFlow curveOf s u x := Gfun (curveOf u) (s, x)`: the joint Fourier function of the physical curve `s ↦ curveOf u s` (an `L²(𝕋_L)`-valued
curve, the chart image of the sequence flow).  Its clauses for smooth periodic profiles:

* `Φ_0 u = u` (from the chart identity at `τ = 0`, `eq_of_smoothL2_eq`);
* joint `C^∞` of `(s,x) ↦ Φ_s u (x)` and `SmoothPeriodic (Φ_s u)` for every `s` (`RB7HJoint.joint_smooth`);
* the gradient/derivative clause of `IsHamFlow` is NOT proved here: it is the explicit named input `hgrad` (printed "full Hilbert symplecticity ...
  identifies its derivative with `-i∇I_{r+1}`", own TODO A8/A9).

`isHamFlow_of_chart` instantiates `curveOf u τ = Ψ(Zf τ (z0 u))` with `curve_lift` (RB7HCurve, accepted `lem:loss`) under the named
hypotheses `hZsm` (sequence flow smooth in every level, from `RB7Scale.scale_flow_contDiff`, level compatibility not checked here), `hreg`
(REG-015 clause), `hchart` (chart identity at smooth data) and `hZ0` (flow at time `0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate Topology ContDiff NNReal
open MeasureTheory Filter Set

namespace QuantumNLS.RB7H

open QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.PhysicalTensor QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.ClassicalCharges
open QuantumNLS.WeakDerivatives QuantumNLS.HierarchyFlow QuantumNLS.LossSobolev QuantumNLS.Loss

variable {L : ℝ} [Fact (0 < L)]

/-- Two smooth periodic functions with the same `L²` class are equal (continuity + `IsOpenPosMeasure`). -/
theorem eq_of_smoothL2_eq {f g : ℝ → ℂ} (hf : SmoothPeriodic L f) (hg : SmoothPeriodic L g)
    (h : smoothL2 hf = smoothL2 hg) : f = g := by
  have hcf : Continuous (liftC hf.smooth.continuous hf.periodic : AddCircle L → ℂ) :=
    (liftC hf.smooth.continuous hf.periodic).continuous
  have hcg : Continuous (liftC hg.smooth.continuous hg.periodic : AddCircle L → ℂ) :=
    (liftC hg.smooth.continuous hg.periodic).continuous
  have hae : (liftC hf.smooth.continuous hf.periodic : AddCircle L → ℂ) =ᵐ[volume]
      (liftC hg.smooth.continuous hg.periodic : AddCircle L → ℂ) := by
    have a1 := ContinuousMap.coeFn_toLp (E := ℂ) (𝕜 := ℂ) (p := 2) (μ := (volume : Measure (AddCircle L)))
      (liftC hf.smooth.continuous hf.periodic)
    have a2 := ContinuousMap.coeFn_toLp (E := ℂ) (𝕜 := ℂ) (p := 2) (μ := (volume : Measure (AddCircle L)))
      (liftC hg.smooth.continuous hg.periodic)
    unfold smoothL2 at h
    have h' : (⇑(ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (AddCircle L)) ℂ
        (liftC hf.smooth.continuous hf.periodic)) : AddCircle L → ℂ) =
        ⇑(ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (AddCircle L)) ℂ
        (liftC hg.smooth.continuous hg.periodic)) := congrArg (fun z : L2T L => (z : AddCircle L → ℂ)) h
    exact a1.symm.trans ((EventuallyEq.of_eq h').trans a2)
  have heq := (Continuous.ae_eq_iff_eq volume hcf hcg).1 hae
  funext x
  have hx := congrFun heq (x : AddCircle L)
  rw [liftC_coe, liftC_coe] at hx
  exact hx

/-- The function-level flow of a curve map: `Φ_s u (x) = J(u)(s, x)` with `J(u)` the joint Fourier function of the curve `curveOf u`. -/
def physFlow (curveOf : (ℝ → ℂ) → ℝ → L2T L) : ℝ → (ℝ → ℂ) → (ℝ → ℂ) :=
  fun s u x => Gfun (curveOf u) (s, x)

/-- **A7b(b), `IsHamFlow` form.** Given the physical curve map `curveOf` with `C^∞` lifts into every `H^q` (`hlift`), the chart identity at
`τ = 0` (`hzero`), and the gradient/derivative clause `hgrad` (the named A8/A9 input), `physFlow curveOf` satisfies `IsHamFlow L F`. -/
theorem isHamFlow_physFlow {F : (ℝ → ℂ) → ℝ} (curveOf : (ℝ → ℂ) → ℝ → L2T L)
    (hlift : ∀ u : ℝ → ℂ, SmoothPeriodic L u → ∀ q : ℝ, 0 < q →
      ∃ V : ℝ → H02 L q, ContDiff ℝ ∞ V ∧ ∀ τ, (V τ).val = curveOf u τ)
    (hzero : ∀ (u : ℝ → ℂ) (hu : SmoothPeriodic L u), curveOf u 0 = smoothL2 hu)
    (hgrad : ∀ (u : ℝ → ℂ), SmoothPeriodic L u → ∀ s : ℝ, ∃ g : ℝ → ℂ,
      IsSmoothGradient L F (physFlow curveOf s u) g ∧
        ∀ x : ℝ, HasDerivAt (fun s' => physFlow curveOf s' u x) (-Complex.I * g x) s) :
    IsHamFlow L F (physFlow curveOf) := by
  intro u hu
  obtain ⟨hjoint, -, hsl⟩ := joint_smooth (curveOf u) (hlift u hu)
  refine ⟨?_, ?_, fun s => ⟨?_, hgrad u hu s⟩⟩
  · -- `Φ_0 u = u`
    obtain ⟨hf0, hf0eq⟩ := hsl 0
    have hEq : smoothL2 hf0 = smoothL2 hu := by
      rw [hf0eq, hzero u hu]
    funext x
    exact congrFun (eq_of_smoothL2_eq hf0 hu hEq) x
  · exact hjoint
  · obtain ⟨hfs, -⟩ := hsl s
    exact hfs

/-- **A7b(b), instantiated through the chart.** With `Zf` the sequence flow, `z0 u` the `h^0` coordinates of the chart image of `u`, and `Ψ`
the analytic inverse chart, the curve map is `curveOf u τ = Ψ(Zf τ (z0 u))`; its `C^∞` lifts come from `curve_lift` (accepted `lem:loss`). -/
theorem isHamFlow_of_chart {F : (ℝ → ℂ) → ℝ}
    (Psi : (seqScale L).Y 0 → (fieldScale L).Y 0) (hPsi : AnalyticOnNhd ℝ Psi univ)
    (Zf : ℝ → (seqScale L).Y 0 → (seqScale L).Y 0) (z0 : (ℝ → ℂ) → (seqScale L).Y 0)
    (hZ0 : ∀ z, Zf 0 z = z)
    (hZsm : ∀ (u : ℝ → ℂ), SmoothPeriodic L u → ∀ S : ℝ≥0, ∃ zS : ℝ → (seqScale L).Y S,
      ContDiff ℝ ∞ zS ∧ ∀ τ, (seqScale L).emb S 0 (nn_zero_le S) (zS τ) = Zf τ (z0 u))
    (hreg : ∀ S : ℝ≥0, ∃ g : (seqScale L).Y S → (fieldScale L).Y S, Continuous g ∧
      ∀ x, (fieldScale L).emb S 0 (nn_zero_le S) (g x) = Psi ((seqScale L).emb S 0 (nn_zero_le S) x))
    (hchart : ∀ (u : ℝ → ℂ) (hu : SmoothPeriodic L u), (Psi (z0 u)).val = (smoothL2 hu : L2T L))
    (hgrad : ∀ (u : ℝ → ℂ), SmoothPeriodic L u → ∀ s : ℝ, ∃ g : ℝ → ℂ,
      IsSmoothGradient L F (physFlow (fun u τ => (Psi (Zf τ (z0 u))).val) s u) g ∧
        ∀ x : ℝ, HasDerivAt (fun s' => physFlow (fun u τ => (Psi (Zf τ (z0 u))).val) s' u x)
          (-Complex.I * g x) s) :
    IsHamFlow L F (physFlow (fun u τ => (Psi (Zf τ (z0 u))).val)) := by
  refine isHamFlow_physFlow (fun u τ => (Psi (Zf τ (z0 u))).val) ?_ ?_ hgrad
  · intro u hu q hq
    obtain ⟨V, hV, hVu⟩ := curve_lift Psi hPsi (fun τ => Zf τ (z0 u)) (hZsm u hu) hreg q hq
    exact ⟨V, hV, hVu⟩
  · intro u hu
    show (Psi (Zf 0 (z0 u))).val = (smoothL2 hu : L2T L)
    rw [hZ0]
    exact hchart u hu

end QuantumNLS.RB7H

#print axioms QuantumNLS.RB7H.eq_of_smoothL2_eq
#print axioms QuantumNLS.RB7H.isHamFlow_physFlow
#print axioms QuantumNLS.RB7H.isHamFlow_of_chart

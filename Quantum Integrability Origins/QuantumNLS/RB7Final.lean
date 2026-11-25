import Mathlib
import QuantumNLS.RB7Exist
import QuantumNLS.RB7UniqF
import QuantumNLS.Def024LowEquivariance
import QuantumNLS.Def024Order2Joint

/-!
# R-7B122087 `thm:hierarchy` / DEF-024: the smooth Hamiltonian flows of every order `r`, final assembly (RB7Final)

Conclusion (for every `κ > 0`, every `r : ℕ` including `r ≥ 3`, every finite `𝓡`), with the SINGLE named input `REG015Concl hκ` (the conclusion of `Reg015Assembly.REG015Input`; the final theorem
`hierarchy_of_REG015_final` of `RB7FinalR15` swaps in `Reg015HFinal.REG015_final`):

* `chartFlow hR C r`: `physFlow (curveOf r)`, the function-level flow `Φ^{(r)}_s u (x) = [Ψ(Zf_r(s) Φ(u))](x)`;
* `isHamFlow_chart`: it is a `HierarchyFlow.IsHamFlow L (hamiltonian L κ r)` (A7b, haiku_inventory's `RB7H.isHamFlow_of_chart`, with `hgrad` from `RB7Exist.hgrad_chart`);
* `unique_chart`: it is `Def024LowEquivariance.UniqueHamFlow` (A9': `RB7Const.moduli_const`, `RB7UniqF.isHamFlow_eq`, `RB7Uniq.SeqData.unique_flow`);
* `comm_chart` (D3, `Def024LowEquivariance.comm_low_of_unique`): it commutes with the order-`0` and order-`1` flows (phase and translation), all real times;
* `group_chart` (D4, `Def024Order2Joint.group_of_unique`): `Φ_s ∘ Φ_a = Φ_{s+a}` on smooth data;
* `chartHamFlows hR C 𝓡 : HamFlows L κ 𝓡` and `jointClassicalFlow`: `hierarchy_final`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
noncomputable section

open scoped ComplexConjugate Topology NNReal ContDiff

namespace QuantumNLS.RB7

open QuantumNLS.Reg015Setting QuantumNLS.ClassicalCharges QuantumNLS.HierarchyFlow QuantumNLS.Def024LowFlows
  QuantumNLS.Def024LowEquivariance QuantumNLS.Def024Order2Joint

variable {L κ : ℝ} [Fact (0 < L)] {hκ : 0 < κ}

/-- The order-`r` smooth Hamiltonian flow of `Re I_{r+1}` (function level). -/
def chartFlow (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) :
    ℝ → (ℝ → ℂ) → (ℝ → ℂ) := RB7H.physFlow (curveOf hR C r)

theorem isHamFlow_chart (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) :
    IsHamFlow L (hamiltonian L κ r) (chartFlow hR C r) :=
  RB7H.isHamFlow_of_chart (F := hamiltonian L κ r) (PsiC C) (PsiC_analytic C) (Zf hR C r) (z0 hR C)
    (Zf_zero hR C r) (hZsm_chart hR C r) (hreg_chart hR C) (hchart_chart hR C) (hgrad_chart hR C r)

theorem unique_chart (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) :
    UniqueHamFlow L (hamiltonian L κ r) (chartFlow hR C r) :=
  fun _ hΨ _ hu s => isHamFlow_eq hR C r hΨ hu s

theorem comm_chart (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s a : ℝ) :
    chartFlow hR C r s (phaseFlow a u) = phaseFlow a (chartFlow hR C r s u) ∧
      chartFlow hR C r s (transFlow a u) = transFlow a (chartFlow hR C r s u) :=
  comm_low_of_unique κ r (isHamFlow_chart hR C r) (unique_chart hR C r) hu s a

theorem group_chart (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s a : ℝ) :
    chartFlow hR C r s (chartFlow hR C r a u) = chartFlow hR C r (s + a) u :=
  group_of_unique (isHamFlow_chart hR C r) (unique_chart hR C r) hu s a

/-- The DEF-024 family of Hamiltonian flows for a finite set of orders. -/
def chartHamFlows (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (𝓡 : Finset ℕ) :
    HamFlows L κ 𝓡 where
  Φ := fun r => chartFlow hR C r
  ham := fun r _ => isHamFlow_chart hR C r

theorem smooth_foldr (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (t : ℕ → ℝ) :
    ∀ (l : List ℕ) {u : ℝ → ℂ}, SmoothPeriodic L u →
      SmoothPeriodic L ((l.map fun r => chartFlow hR C r (t r)).foldr (· ∘ ·) id u) := by
  intro l
  induction l with
  | nil => intro u hu; exact hu
  | cons r l ih =>
    intro u hu
    simp only [List.map_cons, List.foldr_cons, Function.comp_apply]
    exact ((isHamFlow_chart hR C r _ (ih hu)).2.2 (t r)).1

/-- The conclusion of the final assembly (DEF-024 for every order `r`, finite `𝓡`). -/
def HierarchyConcl (hκ : 0 < κ) (𝓡 : Finset ℕ) : Prop :=
  ∃ (C : ChartFacts (L := L) hκ) (F : HamFlows L κ 𝓡),
    (∀ r ∈ 𝓡, UniqueHamFlow L (hamiltonian L κ r) (F.Φ r)) ∧
    (∀ r ∈ 𝓡, ∀ u : ℝ → ℂ, SmoothPeriodic L u → ∀ s a : ℝ,
      F.Φ r s (phaseFlow a u) = phaseFlow a (F.Φ r s u) ∧
        F.Φ r s (transFlow a u) = transFlow a (F.Φ r s u)) ∧
    (∀ r ∈ 𝓡, ∀ u : ℝ → ℂ, SmoothPeriodic L u → ∀ s a : ℝ,
      F.Φ r s (F.Φ r a u) = F.Φ r (s + a) u) ∧
    (∀ (t : ℕ → ℝ) (u : ℝ → ℂ), SmoothPeriodic L u → SmoothPeriodic L (jointClassicalFlow F t u))

/-- **Final assembly (DEF-024 for every order).** The only named input is `REG015Concl hκ`. -/
theorem hierarchy_final (hR : REG015Concl (L := L) hκ) (𝓡 : Finset ℕ) : HierarchyConcl (L := L) hκ 𝓡 := by
  obtain ⟨C⟩ := chartFacts_exists (L := L) hκ
  exact ⟨C, chartHamFlows hR C 𝓡, fun r _ => unique_chart hR C r,
    fun r _ u hu s a => comm_chart hR C r hu s a, fun r _ u hu s a => group_chart hR C r hu s a,
    fun t u hu => smooth_foldr hR C t _ hu⟩

/-- The same from the three printed REG-015 predecessor inputs (`REG015Input` form). -/
theorem hierarchy_of_inputs (reg010 : Reg010LowOrdersInput (L := L) hκ)
    (reg011 : Reg011HomeomorphismInput (L := L) hκ) (reg013 : Reg013InductionInput (L := L) hκ)
    (𝓡 : Finset ℕ) : HierarchyConcl (L := L) hκ 𝓡 :=
  hierarchy_final (REG015Concl_of_inputs hκ reg010 reg011 reg013) 𝓡

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.isHamFlow_chart
#print axioms QuantumNLS.RB7.unique_chart
#print axioms QuantumNLS.RB7.comm_chart
#print axioms QuantumNLS.RB7.group_chart
#print axioms QuantumNLS.RB7.hierarchy_final
#print axioms QuantumNLS.RB7.hierarchy_of_inputs

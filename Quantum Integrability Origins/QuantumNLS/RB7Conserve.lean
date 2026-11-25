import Mathlib
import QuantumNLS.RB7Commute

/-!
# R-7B122087 `thm:hierarchy`, clause (6): all local charges and indexed actions are conserved (RB7Conserve)

Printed: "All local charges and indexed actions are conserved" with the proof: "All charges are preserved by modulus invariance".

* `actions_conserved`: for ANY `HierarchyFlow.IsHamFlow` `Ψ'` of `hamiltonian L κ r` and smooth `u`, the indexed actions (the indexed masses `I_n`, equal to `|Φ_n|²` by the chart) are constant along the flow line:
  `masses(Ψ'_s u)_n = masses(u)_n`.  This is `RB7Const.moduli_const` (zero bracket with each action), not the rotation form.
* `charge_conserved`: every local charge `I_j^{(κ)}`, `j : ℕ` (DEF-022 `ClassicalCharges.charge`, complex valued, the real parts `Re I_{r'+1}` included), is conserved along the flow of EVERY order `r`:
  `charge L κ (Ψ'_s u) j = charge L κ u j`.  Proof: equal indexed masses, `RB7Moment.charge_eq_of_masses` (accepted `R_275B7656` for the measure moments, accepted `root_scalar_uniqueness` for the equality of
  the measures; `j = 0` is `v_0 = 0`).
* `joint_smooth_of_family`, `joint_actions_conserved`, `joint_charge_conserved`: the same for the joint classical flow of any family `F : HamFlows L κ 𝓡`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology NNReal ContDiff
open MeasureTheory

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.PhysicalTensor QuantumNLS.Fourier
open QuantumNLS.Reg015Setting QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.HierarchyFlow QuantumNLS.LossSobolev

variable {L κ : ℝ} [Fact (0 < L)] {hκ : 0 < κ}

theorem charge_zero (u : ℝ → ℂ) : charge L κ u 0 = 0 := by
  unfold charge
  have : ∀ x, vseq κ u 0 x = 0 := fun x => by rw [vseq]
  simp [this]

/-- Equal chart-coordinate moduli give equal indexed masses and equal charges of every order. -/
theorem charge_eq_of_norm_eq (C : ChartFacts (L := L) hκ) {f g : ℝ → ℂ} (hf : SmoothPeriodic L f)
    (hg : SmoothPeriodic L g)
    (h : ∀ n, ‖(C.Φ (smoothL2 hf) : ℤ → ℂ) n‖ = ‖(C.Φ (smoothL2 hg) : ℤ → ℂ) n‖) (j : ℕ) :
    charge L κ f j = charge L κ g j := by
  cases j with
  | zero => rw [charge_zero, charge_zero]
  | succ j =>
    refine charge_eq_of_masses hκ hf hg (fun n => ?_) j
    rw [← C.mass, ← C.mass, h n]

theorem masses_eq_of_norm_eq (C : ChartFacts (L := L) hκ) {f g : ℝ → ℂ} (hf : SmoothPeriodic L f)
    (hg : SmoothPeriodic L g)
    (h : ∀ n, ‖(C.Φ (smoothL2 hf) : ℤ → ℂ) n‖ = ‖(C.Φ (smoothL2 hg) : ℤ → ℂ) n‖) (n : ℤ) :
    (QuantumNLS.RootIndexedMasses.masses hκ (smoothL2 hf)).1 n =
      (QuantumNLS.RootIndexedMasses.masses hκ (smoothL2 hg)).1 n := by
  rw [← C.mass, ← C.mass, h n]

/-- Along every smooth Hamiltonian flow line of every order, all chart moduli are constant. -/
theorem norm_const_flow (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    {Ψ' : ℝ → (ℝ → ℂ) → (ℝ → ℂ)} (hΨ : IsHamFlow L (hamiltonian L κ r) Ψ')
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) (hs : SmoothPeriodic L (Ψ' s u)) (n : ℤ) :
    ‖(C.Φ (smoothL2 hs) : ℤ → ℂ) n‖ = ‖(C.Φ (smoothL2 hu) : ℤ → ℂ) n‖ := by
  have h0 : SmoothPeriodic L (Ψ' 0 u) := ((hΨ u hu).2.2 0).1
  have h := moduli_const hR C r hΨ hu n s 0 hs h0
  have e : smoothL2 h0 = smoothL2 hu := smoothL2_congr (hΨ u hu).1 h0 hu
  rw [e] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- **Indexed actions are conserved** along every smooth Hamiltonian flow of order `r`. -/
theorem actions_conserved (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    {Ψ' : ℝ → (ℝ → ℂ) → (ℝ → ℂ)} (hΨ : IsHamFlow L (hamiltonian L κ r) Ψ')
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) (hs : SmoothPeriodic L (Ψ' s u)) (n : ℤ) :
    (QuantumNLS.RootIndexedMasses.masses hκ (smoothL2 hs)).1 n =
      (QuantumNLS.RootIndexedMasses.masses hκ (smoothL2 hu)).1 n :=
  masses_eq_of_norm_eq C hs hu (norm_const_flow hR C r hΨ hu s hs) n

/-- **Every local charge is conserved** along every smooth Hamiltonian flow of every order `r`. -/
theorem charge_conserved (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    {Ψ' : ℝ → (ℝ → ℂ) → (ℝ → ℂ)} (hΨ : IsHamFlow L (hamiltonian L κ r) Ψ')
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) (hs : SmoothPeriodic L (Ψ' s u)) (j : ℕ) :
    charge L κ (Ψ' s u) j = charge L κ u j :=
  charge_eq_of_norm_eq C hs hu (norm_const_flow hR C r hΨ hu s hs) j

/-- The joint classical flow of any family of Hamiltonian flows is smooth periodic on smooth data. -/
theorem joint_smooth_of_family (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) {𝓡 : Finset ℕ}
    (F : HamFlows L κ 𝓡) (t : ℕ → ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    SmoothPeriodic L (jointClassicalFlow F t u) := by
  have hmem' : ∀ r ∈ 𝓡.sort (· ≤ ·), r ∈ 𝓡 := fun r hr => (Finset.mem_sort (· ≤ ·)).1 hr
  have he : jointClassicalFlow F t u = compFlow hR C ((𝓡.sort (· ≤ ·)).map fun r => (r, t r)) u := by
    unfold jointClassicalFlow
    exact foldr_eq_comp hR C F t _ hmem' hu
  rw [he]
  exact (comp_coords hR C _ hu).1

theorem joint_norm_const (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) {𝓡 : Finset ℕ}
    (F : HamFlows L κ 𝓡) (t : ℕ → ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u)
    (hj : SmoothPeriodic L (jointClassicalFlow F t u)) (n : ℤ) :
    ‖(C.Φ (smoothL2 hj) : ℤ → ℂ) n‖ = ‖(C.Φ (smoothL2 hu) : ℤ → ℂ) n‖ := by
  rw [joint_rotation_form hR C F t hu hj n, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem joint_actions_conserved (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) {𝓡 : Finset ℕ}
    (F : HamFlows L κ 𝓡) (t : ℕ → ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u)
    (hj : SmoothPeriodic L (jointClassicalFlow F t u)) (n : ℤ) :
    (QuantumNLS.RootIndexedMasses.masses hκ (smoothL2 hj)).1 n =
      (QuantumNLS.RootIndexedMasses.masses hκ (smoothL2 hu)).1 n :=
  masses_eq_of_norm_eq C hj hu (joint_norm_const hR C F t hu hj) n

theorem joint_charge_conserved (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) {𝓡 : Finset ℕ}
    (F : HamFlows L κ 𝓡) (t : ℕ → ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (j : ℕ) :
    charge L κ (jointClassicalFlow F t u) j = charge L κ u j :=
  charge_eq_of_norm_eq C (joint_smooth_of_family hR C F t hu) hu
    (joint_norm_const hR C F t hu (joint_smooth_of_family hR C F t hu)) j

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.charge_zero
#print axioms QuantumNLS.RB7.norm_const_flow
#print axioms QuantumNLS.RB7.actions_conserved
#print axioms QuantumNLS.RB7.charge_conserved
#print axioms QuantumNLS.RB7.joint_smooth_of_family
#print axioms QuantumNLS.RB7.joint_actions_conserved
#print axioms QuantumNLS.RB7.joint_charge_conserved

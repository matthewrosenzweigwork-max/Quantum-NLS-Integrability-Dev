import QuantumNLS.Def033CoreR24m
import QuantumNLS.Def033LowR24m
import QuantumNLS.Def024Order2Joint
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.ContinuousMap.Compact

/-!
DEF-033 intermediate hierarchy binding. The ONE pending predecessor is
R-7B122087, source-text/chapters/core/DYNAMICS_LEMMAS.tex:117-127.

EXACT PRINTED STATEMENT (HierarchyPrintedInput):
"Assume the new global strong canonical analytic L² chart and its
Sobolev homeomorphisms, the scalar-uniqueness theorem, and the scalar
moment identification in the preceding section. Then every fixed
physical Riccati Hamiltonian I_{r+1}^{(κ)}, r≥2, has a unique
global smooth Hamiltonian flow from every smooth datum. Every finite
family of these flows commutes. In the new coordinates they are
constant-action rotations, their full orbits are relatively compact
in the smooth topology, and they depend continuously in that topology
on compact smooth initial classes and compact boxes of joint times.
All local charges and indexed actions are conserved. No uniformity in
growing order, label sets, or time boxes is asserted."

`HierarchyPrintedInput` below is the complete conclusion at the chart in
those printed hypotheses, not just a frequency or higher-flow premise.
Its printed antecedents remain part of the pending predecessor binding;
this module does not prove them or claim that its formal interface has
already been matched to the predecessor's final Lean API. See gaps.json.
Only the intermediate theorem has this input. No final DEF033 theorem
is declared before the accepted predecessor can replace it.
-/
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Topology
open scoped ENNReal ContDiff
namespace QuantumNLS.Def033HierarchyR24m
open QuantumNLS.ClassicalCharges QuantumNLS.HierarchyFlow
open QuantumNLS.Def024LowEquivariance QuantumNLS.Def024Order2Joint
open QuantumNLS.Def033CoreR24m
open QuantumNLS.PhysicalProductPreparation

/-- Smooth periodic physical profiles; topology is uniform convergence of every
spatial derivative on one closed period, not pointwise convergence of jets. -/
abbrev Smooth (L : ℝ) := {u : ℝ → ℂ // SmoothPeriodic L u}

def jet (L : ℝ) (u : Smooth L) (k : ℕ) : C(Set.Icc (0 : ℝ) L, ℂ) :=
  ⟨fun x => iteratedDeriv k u.val x.val,
    (u.property.smooth.continuous_iteratedDeriv k (by simp)).comp continuous_subtype_val⟩

instance smoothTopology (L : ℝ) : TopologicalSpace (Smooth L) :=
  TopologicalSpace.induced (fun u => jet L u) inferInstance

/-- The physical L² class of a smooth datum, using the established embedding. -/
def physical {L : ℝ} [Fact (0 < L)] (u : Smooth L) : QuantumNLS.PhysicalTensor.L2T L :=
  smoothClass u.property

variable {L κ : ℝ} [Fact (0 < L)]

/-- A flow step as a map between smooth profiles. -/
def smoothStep {R : Finset ℕ} (F : HamFlows L κ R) (r : ℕ) (t : ℝ)
    (u : Smooth L) : Smooth L :=
  if hr : r ∈ R then ⟨F.Φ r t u.val, ((F.ham r hr u.val u.property).2.2 t).1⟩ else u

/-- The joint flow with the full smooth topology on its codomain. -/
def jointSmooth {R : Finset ℕ} (F : HamFlows L κ R) (t : ℕ → ℝ)
    (u : Smooth L) : Smooth L :=
  (R.sort (· ≤ ·)).foldr (fun r v => smoothStep F r (t r) v) u

/-- Complete fixed-hierarchy conclusion, under the printed predecessor's chart,
Sobolev, scalar-uniqueness and scalar-moment hypotheses. No higher-flow existence
is taken as a second input. Arbitrary finite families and compact boxes stay fixed. -/
def HierarchyPrintedInput
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.QuantumFourierSpecification.Coordinates)
    (action : QuantumNLS.PhysicalTensor.L2T L → ℤ → ℝ) : Prop :=
  ∃ (Φ : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
    (hΦ : ∀ r, 2 ≤ r → IsHamFlow L (hamiltonian L κ r) (Φ r)),
    (∀ r (hr : 2 ≤ r), UniqueHamFlow L (hamiltonian L κ r) (Φ r)) ∧
    (∀ r s, 2 ≤ r → 2 ≤ s → ∀ u : Smooth L, ∀ t τ,
      Φ r t (Φ s τ u.val) = Φ s τ (Φ r t u.val)) ∧
    (∀ r (hr : 2 ≤ r) (u : Smooth L) n, ∃ freq : ℝ, ∀ t,
      w (physical ⟨Φ r t u.val, ((hΦ r hr u.val u.property).2.2 t).1⟩) n =
        phase t freq * w (physical u) n) ∧
    (∀ r (hr : 2 ≤ r) (u : Smooth L), IsCompact (closure
      (Set.range fun t => (⟨Φ r t u.val, ((hΦ r hr u.val u.property).2.2 t).1⟩ : Smooth L)))) ∧
    (∀ (R : Finset ℕ) (hR : ∀ r ∈ R, 2 ≤ r),
      let F : HamFlows L κ R := ⟨Φ, fun r hr => hΦ r (hR r hr)⟩
      ∀ (K : Set (Smooth L)), IsCompact K → ∀ (T : ℕ → ℝ), (∀ r, 0 ≤ T r) →
        ContinuousOn (fun p : Smooth L × (ℕ → ℝ) => jointSmooth F p.2 p.1)
          (K ×ˢ (Set.pi Set.univ fun r => if r ∈ R then Set.Icc (-T r) (T r) else {0}))) ∧
    (∀ r (hr : 2 ≤ r) (u : Smooth L) (t : ℝ) j,
      charge L κ (Φ r t u.val) j = charge L κ u.val j) ∧
    (∀ r (hr : 2 ≤ r) (u : Smooth L) (t : ℝ) n,
      action (physical ⟨Φ r t u.val, ((hΦ r hr u.val u.property).2.2 t).1⟩) n = action (physical u) n)

/-- DEF-033 intermediate: the single full hierarchy input supplies real active
frequencies for all r≥2, and their real value is unique. Higher flow existence is
extracted from that same input, never separately assumed. -/
theorem DEF033_higher_intermediate
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.QuantumFourierSpecification.Coordinates)
    (action : QuantumNLS.PhysicalTensor.L2T L → ℤ → ℝ)
    (hact : ∀ u n, ‖w u n‖ ^ 2 = action u n)
    (HierarchyR7B122087Input : HierarchyPrintedInput (κ := κ) w action) :
    ∃ (Φ : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
      (hΦ : ∀ r, 2 ≤ r → IsHamFlow L (hamiltonian L κ r) (Φ r)),
      ∀ r (hr : 2 ≤ r) (u : Smooth L) (n : ℤ), 0 < action (physical u) n →
        ∃! freq : ℝ, ActiveFrequency
          (fun t => w (physical ⟨Φ r t u.val, ((hΦ r hr u.val u.property).2.2 t).1⟩) n)
          (w (physical u) n) freq := by
  obtain ⟨Φ, hΦ, huniq, hcomm, hrot, hcompact, hcont, hcharge, haction⟩ := HierarchyR7B122087Input
  refine ⟨Φ, hΦ, fun r hr u n hn => ?_⟩
  obtain ⟨freq, hfreq⟩ := hrot r hr u n
  have hactive : ActiveFrequency _ (w (physical u) n) freq :=
    ⟨nonzero_of_action (hact _ _) hn, hfreq⟩
  exact ⟨freq, hactive, fun freq' hfreq' => activeFrequency_unique hfreq' hactive⟩

/-- Every finite set of orders has actual Hamiltonian flows: r≤2 uses the staged
DEF-024 theorem; r≥3 is extracted from the SAME hierarchy input. -/
theorem all_order_hamFlows (hκ : 0 ≤ κ)
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.QuantumFourierSpecification.Coordinates)
    (action : QuantumNLS.PhysicalTensor.L2T L → ℤ → ℝ)
    (HierarchyR7B122087Input : HierarchyPrintedInput (κ := κ) w action) (R : Finset ℕ) :
    Nonempty (HamFlows L κ R) := by
  obtain ⟨Φ, hΦ, -⟩ := HierarchyR7B122087Input
  refine ⟨⟨fun r => if r ≤ 2 then flowMap2 L κ r else Φ r, fun r hr => ?_⟩⟩
  by_cases h : r ≤ 2
  · simp only [h, ↓reduceIte]
    apply flowMap2_isHamFlow hκ
    have : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp
  · simp only [h, ↓reduceIte]
    exact hΦ r (by omega)

/-- One commuting family for every order. Orders 0 and 1 are the proved staged
flows; the hierarchy supplies r≥2. Its order-2 map agrees with the staged cubic
flow by the staged uniqueness theorem, included explicitly in the conclusion. -/
theorem all_order_commuting (hκ : 0 ≤ κ)
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.QuantumFourierSpecification.Coordinates)
    (action : QuantumNLS.PhysicalTensor.L2T L → ℤ → ℝ)
    (HierarchyR7B122087Input : HierarchyPrintedInput (κ := κ) w action) :
    ∃ (Ψ : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ)),
      (∀ r, IsHamFlow L (hamiltonian L κ r) (Ψ r)) ∧
      (∀ r, UniqueHamFlow L (hamiltonian L κ r) (Ψ r)) ∧
      (∀ r s, ∀ u : Smooth L, ∀ t τ, Ψ r t (Ψ s τ u.val) = Ψ s τ (Ψ r t u.val)) ∧
      (∀ r, r ≤ 2 → ∀ u : Smooth L, ∀ t, Ψ r t u.val = flowMap2 L κ r t u.val) := by
  obtain ⟨Φ, hΦ, huΦ, hcΦ, -⟩ := HierarchyR7B122087Input
  let Ψ := fun r => if r ≤ 1 then flowMap2 L κ r else Φ r
  have hm : ∀ r, r ≤ 1 → r ∈ ({0, 1, 2} : Finset ℕ) := by
    intro r hr
    have : r = 0 ∨ r = 1 := by omega
    rcases this with rfl | rfl <;> simp
  have hΨ : ∀ r, IsHamFlow L (hamiltonian L κ r) (Ψ r) := by
    intro r
    by_cases hr : r ≤ 1
    · simpa only [Ψ, hr, ↓reduceIte] using flowMap2_isHamFlow hκ (hm r hr)
    · simpa only [Ψ, hr, ↓reduceIte] using hΦ r (by omega)
  have huΨ : ∀ r, UniqueHamFlow L (hamiltonian L κ r) (Ψ r) := by
    intro r
    by_cases hr : r ≤ 1
    · simpa only [Ψ, hr, ↓reduceIte] using flowMap2_unique hκ (hm r hr)
    · simpa only [Ψ, hr, ↓reduceIte] using huΦ r (by omega)
  have hcΨ : ∀ r s, ∀ u : Smooth L, ∀ t τ,
      Ψ r t (Ψ s τ u.val) = Ψ s τ (Ψ r t u.val) := by
    intro r s u t τ
    by_cases hr : r ≤ 1
    · by_cases hs : s ≤ 1
      · simpa only [Ψ, hr, hs, ↓reduceIte] using
          flowMap2_comm hκ (hm r hr) (hm s hs) u.property t τ
      · have h := comm_low_of_unique κ s (hΨ s) (huΨ s) u.property τ t
        have hre : r = 0 ∨ r = 1 := by omega
        rcases hre with rfl | rfl
        · simpa only [Ψ, show 0 ≤ 1 by omega, ↓reduceIte, flowMap2] using h.1.symm
        · simpa only [Ψ, show 1 ≤ 1 by omega, ↓reduceIte, flowMap2] using h.2.symm
    · by_cases hs : s ≤ 1
      · have h := comm_low_of_unique κ r (hΨ r) (huΨ r) u.property t τ
        have hse : s = 0 ∨ s = 1 := by omega
        rcases hse with rfl | rfl
        · simpa only [Ψ, show 0 ≤ 1 by omega, ↓reduceIte, flowMap2] using h.1
        · simpa only [Ψ, show 1 ≤ 1 by omega, ↓reduceIte, flowMap2] using h.2
      · simpa only [Ψ, hr, hs, ↓reduceIte] using hcΦ r s (by omega) (by omega) u t τ
  refine ⟨Ψ, hΨ, huΨ, hcΨ, fun r hr u t => ?_⟩
  have hm2 : r ∈ ({0, 1, 2} : Finset ℕ) := by
    have : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp
  exact flowMap2_unique hκ hm2 (Ψ r) (hΨ r) u.val u.property t

/-- DEF-033 at all nonnegative fixed orders, INTERMEDIATE only. The canonical
chart hypothesis is the printed ambient chart. The sole unaccepted predecessor
input is the complete R-7B122087 conclusion. Orders 0 and 1 use accepted covariance;
order 2 agrees with the staged DEF-024 cubic flow; higher orders use this input. -/
theorem DEF033_intermediate (hκ : 0 < κ)
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.REF88Chart.K)
    (hw : QuantumNLS.REF88PrintedChart.PrintedChart hκ w)
    (HierarchyR7B122087Input : HierarchyPrintedInput (κ := κ) w
      (fun u n => (QuantumNLS.RootIndexedMasses.masses hκ u).1 n)) :
    ∃ (Ψ : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
      (hΨ : ∀ r, IsHamFlow L (hamiltonian L κ r) (Ψ r)),
      (∀ r s, ∀ u : Smooth L, ∀ t τ, Ψ r t (Ψ s τ u.val) = Ψ s τ (Ψ r t u.val)) ∧
      ∀ r (u : Smooth L) n, 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 n →
        ∃! freq : ℝ, ActiveFrequency
          (fun t => w (physical ⟨Ψ r t u.val, ((hΨ r u.val u.property).2.2 t).1⟩) n)
          (w (physical u) n) freq := by
  obtain ⟨Ψ, hΨ, huΨ, hcΨ, hlow⟩ := all_order_commuting hκ.le w _ HierarchyR7B122087Input
  obtain ⟨Φ, hΦ, huΦ, hcΦ, hrot, -⟩ := HierarchyR7B122087Input
  refine ⟨Ψ, hΨ, hcΨ, fun r u n hn => ?_⟩
  have hnonzero : w (physical u) n ≠ 0 := nonzero_of_action (hw.moduli _ _) hn
  have he : ∃ freq : ℝ, ActiveFrequency
      (fun t => w (physical ⟨Ψ r t u.val, ((hΨ r u.val u.property).2.2 t).1⟩) n)
      (w (physical u) n) freq := by
    by_cases hr : 2 ≤ r
    · obtain ⟨freq, hfreq⟩ := hrot r hr u n
      refine ⟨freq, hnonzero, fun t => ?_⟩
      have hsub : (⟨Ψ r t u.val, ((hΨ r u.val u.property).2.2 t).1⟩ : Smooth L) =
          ⟨Φ r t u.val, ((hΦ r hr u.val u.property).2.2 t).1⟩ :=
        Subtype.ext (huΦ r hr (Ψ r) (hΨ r) u.val u.property t)
      exact (congrArg (fun v : Smooth L => w (physical v) n) hsub).trans (hfreq t)
    · have hre : r = 0 ∨ r = 1 := by omega
      rcases hre with rfl | rfl
      · refine ⟨1, hnonzero, fun t => ?_⟩
        have hs : (⟨Ψ 0 t u.val, ((hΨ 0 u.val u.property).2.2 t).1⟩ : Smooth L) =
            ⟨QuantumNLS.Def024LowFlows.phaseFlow t u.val,
              QuantumNLS.Def024LowFlows.phase_smooth u.property t⟩ :=
          Subtype.ext (hlow 0 (by omega) u t)
        exact (congrArg (fun v : Smooth L => w (physical v) n) hs).trans
          ((congrArg (fun v : QuantumNLS.PhysicalTensor.L2T L => w v n)
            (QuantumNLS.Def033LowR24m.smoothClass_phase u.property t)).trans
            ((QuantumNLS.Def033LowR24m.active_zero hκ hw (physical u) n hn).2 t))
      · refine ⟨QuantumNLS.LocalSpectral.pm L n, hnonzero, fun t => ?_⟩
        have hs : (⟨Ψ 1 t u.val, ((hΨ 1 u.val u.property).2.2 t).1⟩ : Smooth L) =
            ⟨QuantumNLS.Def024LowFlows.transFlow t u.val,
              QuantumNLS.Def024LowFlows.trans_smooth u.property t⟩ :=
          Subtype.ext (hlow 1 (by omega) u t)
        exact (congrArg (fun v : Smooth L => w (physical v) n) hs).trans
          ((congrArg (fun v : QuantumNLS.PhysicalTensor.L2T L => w v n)
            (QuantumNLS.Def033LowR24m.smoothClass_trans u.property t)).trans
            ((QuantumNLS.Def033LowR24m.active_one hκ hw (physical u) n hn).2 t))
  obtain ⟨freq, hfreq⟩ := he
  exact ⟨freq, hfreq, fun freq' hfreq' => activeFrequency_unique hfreq' hfreq⟩

#print axioms DEF033_intermediate
#print axioms all_order_commuting
#print axioms jet
#print axioms DEF033_higher_intermediate
#print axioms all_order_hamFlows
end QuantumNLS.Def033HierarchyR24m

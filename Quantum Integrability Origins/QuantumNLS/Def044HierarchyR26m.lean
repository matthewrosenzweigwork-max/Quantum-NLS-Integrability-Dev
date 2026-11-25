import QuantumNLS.Def044ChartR26m
import QuantumNLS.Def044WindowR26m
import QuantumNLS.HierarchyInputR25m
import QuantumNLS.Def033AdjacentR24m

/-! Source-faithful DEF-044 hierarchy binding, intermediate only.
Exact printed R-7B122087 (DYNAMICS_LEMMAS.tex:117-127):
Assume the new global strong canonical analytic L² chart and its
Sobolev homeomorphisms, the scalar-uniqueness theorem, and the scalar
moment identification in the preceding section. Then every fixed
physical Riccati Hamiltonian I_{r+1}^{(κ)}, r≥2, has a unique
global smooth Hamiltonian flow from every smooth datum. Every finite
family of these flows commutes. In the new coordinates they are
constant-action rotations, their full orbits are relatively compact
in the smooth topology, and they depend continuously in that topology
on compact smooth initial classes and compact boxes of joint times.
All local charges and indexed actions are conserved. No uniformity in
growing order, label sets, or time boxes is asserted.

The full R25m conclusion is shared, including compact joint orbits.
The antecedent is the actual DEF-021 chart carrier, rather than adding
PrintedChart's Fourier/conjugation normalization as a new hypothesis.
Reconciliation with the future accepted API is explicitly pending.
No all-order uniqueness, compactness or continuity record is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
open MeasureTheory Filter Topology Set
namespace QuantumNLS.Def044HierarchyR26m
open PhysicalTensor ClassicalCharges HierarchyFlow
open Def033CoreR24m Def033HierarchyR24m HierarchyInputR25m
variable {L κ : ℝ} [Fact (0 < L)]

/-- The full R-7B122087 conditional statement at the actual chart. The
chart carrier supplies its global analytic strong canonical map and inverse;
all other printed antecedents are visible as implications. -/
def HierarchyR7B122087Input (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) : Prop :=
  Def044ChartR51a.SobolevRestrictions hκ C →
    HierarchyInputR25m.ScalarUniqueness (L := L) hκ →
    HierarchyInputR25m.ScalarMomentIdentification (L := L) hκ →
    HierarchyInputR25m.HierarchyConclusion (κ := κ) C.Φ (Def044ChartR51a.action hκ)

/-- All ancillary antecedents are proved, leaving one named predecessor. -/
theorem hierarchy_intermediate (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (HierarchyR7B122087Input : HierarchyR7B122087Input hκ C) :
    HierarchyConclusion (κ := κ) C.Φ (Def044ChartR51a.action hκ) :=
  HierarchyR7B122087Input (Def044ChartR26m.sobolev_restrictions hκ C)
    (HierarchyInputR25m.scalar_uniqueness hκ) (HierarchyInputR25m.scalar_moments hκ)

/-- Clause (3) uses only the printed higher-order scope. Every field of
this conclusion is constructed from the named theorem and proved window bound. -/
structure DynamicsInterface (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) : Prop where
  hierarchy : HierarchyConclusion (κ := κ) C.Φ (Def044ChartR51a.action hκ)
  window_differentials : Def044InterfacesR51a.WindowDifferentials (L := L) hκ

/-- No supplied dynamics record or charge-reality assumption is needed. -/
theorem dynamics_intermediate (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (HierarchyR7B122087Input : HierarchyR7B122087Input hκ C) :
    DynamicsInterface hκ C :=
  ⟨hierarchy_intermediate hκ C HierarchyR7B122087Input,
    Def044WindowR26m.window_differentials hκ⟩

/-- The same supplied higher hierarchy proves unique real active frequencies.
R51a's independent Def033Input record is unnecessary. -/
theorem DEF033_higher_intermediate (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (HierarchyR7B122087Input : HierarchyR7B122087Input hκ C) :
    ∃ (Φ : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
      (hΦ : ∀ r, 2 ≤ r → IsHamFlow L (hamiltonian L κ r) (Φ r)),
      ∀ r (hr : 2 ≤ r) (u : Smooth L) n, 0 < Def044ChartR51a.action hκ (physical u) n →
        ∃! freq : ℝ, ActiveFrequency
          (fun t => C.Φ (physical ⟨Φ r t u.val, ((hΦ r hr u.val u.property).2.2 t).1⟩) n)
          (C.Φ (physical u) n) freq := by
  exact Def033HierarchyR24m.DEF033_higher_intermediate C.Φ _ C.actions
    (HierarchyInputR25m.conclusion_to_r24 C.Φ _
      (hierarchy_intermediate hκ C HierarchyR7B122087Input))

/-- Active endpoints are explicit proofs, tied to one chart and trajectory.
No arbitrary frequency function is silently substituted for their target. -/
structure ActiveEndpoints (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (u : L2T L) (trajectory : ℝ → L2T L) (a b : ℤ) where
  donor : ℝ
  receiver : ℝ
  donor_positive : 0 < Def044ChartR51a.action hκ u a
  receiver_positive : 0 < Def044ChartR51a.action hκ u b
  donor_active : ActiveFrequency (fun t => C.Φ (trajectory t) a) (C.Φ u a) donor
  receiver_active : ActiveFrequency (fun t => C.Φ (trajectory t) b) (C.Φ u b) receiver

/-- The DEF-033 target is defined only for these selected active endpoints. -/
def activeTarget {hκ : 0 < κ} {C : Def021ChartR41b.Chart L κ hκ}
    {u : L2T L} {trajectory : ℝ → L2T L} {a b : ℤ}
    (E : ActiveEndpoints hκ C u trajectory a b) : ℝ := E.receiver - E.donor

/-- Endpoint selection has no ambiguity. -/
theorem activeTarget_unique {hκ : 0 < κ} {C : Def021ChartR41b.Chart L κ hκ}
    {u : L2T L} {trajectory : ℝ → L2T L} {a b : ℤ}
    (E F : ActiveEndpoints hκ C u trajectory a b) : activeTarget E = activeTarget F := by
  have hd := activeFrequency_unique E.donor_active F.donor_active
  have hr := activeFrequency_unique E.receiver_active F.receiver_active
  simp only [activeTarget, hd, hr]

/-- Exact receiver-minus-donor quantum phase agrees with the active target. -/
theorem active_phase_difference {hκ : 0 < κ} {C : Def021ChartR41b.Chart L κ hκ}
    {u : L2T L} {trajectory : ℝ → L2T L} {a b : ℤ}
    (E : ActiveEndpoints hκ C u trajectory a b) (t : ℝ) :
    phase t E.receiver / phase t E.donor = phase t (activeTarget E) :=
  phase_difference t E.receiver E.donor

omit [Fact (0 < L)] in
/-- Real physical charges are proved from the existing moments theorem. -/
theorem real_charges (hκ : 0 < κ) (u : Smooth L) (r : ℕ) :
    ((charge L κ u.val (r+1)).re : ℂ) = charge L κ u.val (r+1) :=
  (Def033AdjacentR24m.hamiltonian_is_physical hκ u.property r)

end QuantumNLS.Def044HierarchyR26m
#print axioms QuantumNLS.Def044HierarchyR26m.hierarchy_intermediate
#print axioms QuantumNLS.Def044HierarchyR26m.dynamics_intermediate
#print axioms QuantumNLS.Def044HierarchyR26m.DEF033_higher_intermediate
#print axioms QuantumNLS.Def044HierarchyR26m.activeTarget_unique
#print axioms QuantumNLS.Def044HierarchyR26m.real_charges
#print QuantumNLS.Def044HierarchyR26m.HierarchyR7B122087Input

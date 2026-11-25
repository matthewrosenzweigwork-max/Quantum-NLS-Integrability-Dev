import QuantumNLS.ActualModelChartR52a
import QuantumNLS.ActualModelScalarR52a

/-!
R-E679E41D: exact named pending hierarchy input. This module only discharges
the accepted antecedents; it does not duplicate the pending hierarchy proof.

EXACT PRINTED R-7B122087 STATEMENT (verbatim after its label):
Assume the new global strong canonical analytic $L^2$ chart and its
Sobolev homeomorphisms, the scalar-uniqueness theorem, and the scalar
moment identification in the preceding section. Then every fixed
physical Riccati Hamiltonian $I_{r+1}^{(\kappa)}$, $r\ge2$, has a unique
global smooth Hamiltonian flow from every smooth datum. Every finite
family of these flows commutes. In the new coordinates they are
constant-action rotations, their full orbits are relatively compact
in the smooth topology, and they depend continuously in that topology
on compact smooth initial classes and compact boxes of joint times.
All local charges and indexed actions are conserved. No uniformity in
growing order, label sets, or time boxes is asserted.

-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Filter Topology Set
namespace QuantumNLS.ActualModelHierarchyR52a
open PhysicalTensor ClassicalCharges HierarchyFlow Def044InterfacesR51a Def044ChartR51a
variable {L κ : ℝ} [Fact (0 < L)]

def smoothStep {R : Finset ℕ} (F : HamFlows L κ R) (r : ℕ) (t : ℝ)
    (u : Smooth L) : Smooth L :=
  if hr : r ∈ R then ⟨F.Φ r t u.val, ((F.ham r hr u.val u.property).2.2 t).1⟩ else u

def jointSmooth {R : Finset ℕ} (F : HamFlows L κ R) (t : ℕ → ℝ)
    (u : Smooth L) : Smooth L :=
  (R.sort (· ≤ ·)).foldr (fun r v => smoothStep F r (t r) v) u

/-- Every printed conclusion, at orders r ≥ 2. In particular full finite
joint orbits, not merely single-flow orbits, have compact smooth closure. -/
def HierarchyConclusion (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) : Prop :=
  ∃ (Φ : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ))
    (hΦ : ∀ r, 2 ≤ r → IsHamFlow L (hamiltonian L κ r) (Φ r)),
    (∀ r, 2 ≤ r → ∀ Ψ, IsHamFlow L (hamiltonian L κ r) Ψ →
      ∀ u : Smooth L, ∀ t, Ψ t u.val = Φ r t u.val) ∧
    (∀ r s, 2 ≤ r → 2 ≤ s → ∀ u : Smooth L, ∀ t τ,
      Φ r t (Φ s τ u.val) = Φ s τ (Φ r t u.val)) ∧
    (∀ r (hr : 2 ≤ r) (u : Smooth L) n, ∃ omega : ℝ, ∀ t,
      C.Φ (physical ⟨Φ r t u.val, ((hΦ r hr u.val u.property).2.2 t).1⟩) n =
        Complex.exp (-((t*omega : ℝ) : ℂ)*Complex.I)*C.Φ (physical u) n) ∧
    (∀ r (hr : 2 ≤ r) (u : Smooth L), IsCompact (closure
      (Set.range fun t => (⟨Φ r t u.val, ((hΦ r hr u.val u.property).2.2 t).1⟩ : Smooth L)))) ∧
    (∀ (R : Finset ℕ) (hR : ∀ r ∈ R, 2 ≤ r),
      let F : HamFlows L κ R := ⟨Φ, fun r hr => hΦ r (hR r hr)⟩
      ∀ K : Set (Smooth L), IsCompact K → ∀ T : ℕ → ℝ, (∀ r, 0 ≤ T r) →
        ContinuousOn (fun p : Smooth L × (ℕ → ℝ) => jointSmooth F p.2 p.1)
          (K ×ˢ Set.pi Set.univ (fun r => if r ∈ R then Set.Icc (-T r) (T r) else {0}))) ∧
    (∀ (R : Finset ℕ) (hR : ∀ r ∈ R, 2 ≤ r) (u : Smooth L),
      let F : HamFlows L κ R := ⟨Φ, fun r hr => hΦ r (hR r hr)⟩
      IsCompact (closure (Set.range fun t : ℕ → ℝ => jointSmooth F t u))) ∧
    (∀ r (_hr : 2 ≤ r) (u : Smooth L) t j,
      charge L κ (Φ r t u.val) j = charge L κ u.val j) ∧
    (∀ r (hr : 2 ≤ r) (u : Smooth L) t n,
      action hκ (physical ⟨Φ r t u.val, ((hΦ r hr u.val u.property).2.2 t).1⟩) n =
        action hκ (physical u) n)

/-- Full scalar uniqueness antecedent, including its unique continuous law
on the realized indexed-action carrier. This is a definition, not an axiom. -/
def ScalarUniqueness (hκ : 0 < κ) : Prop :=
  (∀ u v : L2T L, (∀ n : ℤ, action hκ u n = action hκ v n) →
    PhysicalQuantumMeasure.measure hκ u = PhysicalQuantumMeasure.measure hκ v) ∧
  (∃! F : RootScalarContinuityR28.realized (L := L) hκ → FiniteMeasure ℝ,
    (∀ u : L2T L, (F (RootScalarContinuityR28.realizedPoint hκ u) : Measure ℝ) =
      PhysicalQuantumMeasure.measure hκ u) ∧
    (∀ a : RootScalarContinuityR28.realized (L := L) hκ,
      Tendsto (fun b : RootScalarContinuityR28.realized (L := L) hκ =>
        TotalVariation.tvNorm (F b : Measure ℝ) (F a : Measure ℝ)) (𝓝 a) (𝓝 0)))

def ScalarMoments (hκ : 0 < κ) : Prop :=
  ∀ u : Smooth L, (∀ j : ℕ, (charge L κ u.val j).im = 0) ∧
    ∀ r : ℕ, Integrable (fun t : ℝ => |t|^r) (PhysicalQuantumMeasure.measure hκ (physical u)) ∧
      ((∫ t : ℝ, t^r ∂PhysicalQuantumMeasure.measure hκ (physical u) : ℝ) : ℂ) =
        charge L κ u.val (r+1)

/-- ONE exact named conditional predecessor input at the actual new chart.
Analyticity, strong canonicity, inverse and exact moduli are the fields of C;
the other three printed antecedents remain visible here and are discharged
by the theorem below. No conclusion is treated as an ambient premise. -/
def HierarchyInput (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) : Prop :=
  SobolevRestrictions hκ C → ScalarUniqueness (L := L) hκ →
    ScalarMoments (L := L) hκ → HierarchyConclusion hκ C

/-- INTERMEDIATE ONLY: all accepted antecedents are supplied, and the exact
missing hierarchy theorem remains one visible named input. -/
theorem hierarchy_intermediate (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (HierarchyInput : HierarchyInput hκ C) : HierarchyConclusion hκ C :=
  HierarchyInput (ActualModelChartR52a.sobolev_restrictions hκ C)
    (RootScalarUniquenessR28.root_scalar_uniqueness hκ)
    (ActualModelScalarR52a.smooth_moments hκ)

end QuantumNLS.ActualModelHierarchyR52a
#print axioms QuantumNLS.ActualModelHierarchyR52a.hierarchy_intermediate
#print QuantumNLS.ActualModelHierarchyR52a.HierarchyInput
#print QuantumNLS.ActualModelHierarchyR52a.HierarchyConclusion

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ActualModelHierarchyR52a." ||
        n.toString.startsWith "_private.QuantumNLS.ActualModelHierarchyR52a." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round52 aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard only."

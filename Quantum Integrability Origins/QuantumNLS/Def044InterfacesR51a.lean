import QuantumNLS.Def044ChartR51a
import QuantumNLS.TerraMultiRound12Definitions
import QuantumNLS.Q07GradientRemovalR24
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.ContinuousMap.Compact

/-!
DEF-044, three-clause interface, D1 realization, INTERMEDIATE ONLY.

The ONE unaccepted prerequisite here is DEF-033. Its EXACT PRINTED definition is:
For the fixed smooth hierarchy of Definition~\ref{def:report-24}, the active-coordinate frequency $\omega_{r,n}(u)$ is the real multiplier in $w_n(\Phi_t^{(r)}u)=e^{-it\omega_{r,n}(u)}w_n(u)$ when $a_n(u)>0$. Its existence is proved in Theorem~\ref{thm:hierarchy}. For $m_a\ge1$, the adjacent quantum difference of order $r$ is $\Lambda_{N,r}(m-e_a+e_b)-\Lambda_{N,r}(m)$, receiver minus donor. For fixed positive-action endpoints its target is $\omega_{r,b}(u)-\omega_{r,a}(u)$. Each limit specifies the original Born law and its convention on the missing-donor sector.

`Def033Input` is a named parameter binding these DEFINITION conventions.
It asserts no adjacent limit or moment convergence. Existence of the hierarchy
and rotations belongs to the source's explicit hierarchy requirement, not to an
extra inferred DEF-033 conclusion. No R24m module is imported. The FINAL named
DEF044 theorem is absent until the integrator supplies accepted DEF-033.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
noncomputable section
open MeasureTheory Filter Topology Set
namespace QuantumNLS.Def044InterfacesR51a
open PhysicalTensor BetheLabels BetheCoefficientTransform BetheSpectralCharges
open ClassicalCharges HierarchyFlow Def044D1SpectralR51a Def044ChartR51a
open TerraMultiRound12Definitions
variable {L κ : ℝ} [Fact (0 < L)]

abbrev Smooth (L : ℝ) := {u : ℝ → ℂ // SmoothPeriodic L u}

/-- The full smooth topology: uniform convergence of every spatial derivative
on a closed period. This is stronger than pointwise convergence of jets. -/
def jet (u : Smooth L) (k : ℕ) : C(Set.Icc (0 : ℝ) L, ℂ) :=
  ⟨fun x => iteratedDeriv k u.val x.val,
    (u.property.smooth.continuous_iteratedDeriv k (by simp)).comp continuous_subtype_val⟩

instance smoothTopology : TopologicalSpace (Smooth L) :=
  TopologicalSpace.induced (fun u : Smooth L => jet u) inferInstance

def physical (u : Smooth L) : L2T L := PhysicalProductPreparation.smoothClass u.property

/-- Full smooth physical hierarchy required by clause (3), at the same chart.
These are requirements of DEF-044, not conclusions of this module. -/
structure HierarchyRequirements (hκ : 0 < κ) (C : ChartInterface (L := L) hκ) where
  Φ : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ)
  ham : ∀ r, IsHamFlow L (hamiltonian L κ r) (Φ r)
  unique : ∀ r, ∀ Ψ, IsHamFlow L (hamiltonian L κ r) Ψ →
    ∀ u : Smooth L, ∀ t, Ψ t u.val = Φ r t u.val
  commute : ∀ r s, ∀ u : Smooth L, ∀ t τ,
    Φ r t (Φ s τ u.val) = Φ s τ (Φ r t u.val)
  rotations : ∀ r (u : Smooth L) n, ∃ omega : ℝ, ∀ t,
    C.chart.Φ (physical ⟨Φ r t u.val, ((ham r u.val u.property).2.2 t).1⟩) n =
      Complex.exp (-((t*omega : ℝ) : ℂ)*Complex.I)*C.chart.Φ (physical u) n
  real_charges : ∀ u : Smooth L, ∀ r, ((charge L κ u.val (r+1)).re : ℂ) = charge L κ u.val (r+1)
  charges_conserved : ∀ r, ∀ u : Smooth L, ∀ t j,
    charge L κ (Φ r t u.val) j = charge L κ u.val j
  actions_conserved : ∀ r (u : Smooth L) t n,
    action hκ (physical ⟨Φ r t u.val, ((ham r u.val u.property).2.2 t).1⟩) n =
      action hκ (physical u) n
  compact_orbit : ∀ r (u : Smooth L),
    IsCompact (closure (Set.range fun t =>
      (⟨Φ r t u.val, ((ham r u.val u.property).2.2 t).1⟩ : Smooth L)))
  compact_continuity : ∀ (R : Finset ℕ),
    let step := fun r (t : ℝ) (u : Smooth L) =>
      if r ∈ R then
        (⟨Φ r t u.val, ((ham r u.val u.property).2.2 t).1⟩ : Smooth L) else u
    ∀ K : Set (Smooth L), IsCompact K → ∀ T : ℕ → ℝ, (∀ r, 0 ≤ T r) →
      ContinuousOn (fun p : Smooth L × (ℕ → ℝ) =>
        (R.sort (· ≤ ·)).foldr (fun r u => step r (p.2 r) u) p.1)
        (K ×ˢ Set.pi Set.univ (fun r => if r ∈ R then Set.Icc (-T r) (T r) else {0}))

/-- All orders in a fixed finite family use the common physical dual H^(2d+4). -/
theorem regularity_mono {r d : ℕ} (hr : r ≤ d) :
    Q07TailBindingR24.regularity r ≤ Q07TailBindingR24.regularity d := by
  dsimp [Q07TailBindingR24.regularity]
  exact_mod_cast (show 2*r+4 ≤ 2*d+4 by omega)

/-- Actual charge-minus-window error, restricted by the canonical Sobolev inclusion. -/
def windowError (hκ : 0 < κ) (d r : ℕ) (hr : r ≤ d) (h : ℝ) (l : ℕ)
    (u : Sobolev.H02 L (Q07TailBindingR24.regularity d)) : ℝ :=
  Q07GradientRemovalR24.T (L := L) hκ r h l (Sobolev.H02.mono (regularity_mono hr) u)

/-- Fixed-smooth-profile window differential and exact H^(2d+4) dual rate.
The norm is that of the REAL continuous linear differential, so radial and all
other real directions are tested. Each finite family has one constant and one
cutoff threshold. No uniformity in a growing order or profile is required. -/
def WindowDifferentials (hκ : 0 < κ) : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ B : ℝ, ∀ h : ℝ, 0 < h →
    ∃ C : ℝ, 0 ≤ C ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ r : ℕ, ∀ hr : r ≤ d,
      (∀ u : Sobolev.H02 L (Q07TailBindingR24.regularity d), ‖u‖ ≤ B →
        DifferentiableAt ℝ (windowError hκ d r hr h l) u) ∧
      (∀ u ∈ Q07GradientRemovalR24.smoothBall (L := L) d B,
        ‖fderiv ℝ (windowError hκ d r hr h l) u‖ ≤
          C*(PROP017UniformN.cutSeq L l)^(-(1/2 : ℝ)))

/-- Clause (3) keeps the physical hierarchy and differential requirement
explicit. A definition of an interface does not prove its inhabitance. -/
structure DynamicsInterface (hκ : 0 < κ) (C : ChartInterface (L := L) hκ) where
  hierarchy : HierarchyRequirements hκ C
  window_differentials : WindowDifferentials (L := L) hκ

/-- Named DEF-033 DEFINITION input, with no limit or frequency-existence
conclusion smuggled into it. Each proposed limit explicitly takes the original
Born law and its specified missing-donor values. The higher hierarchy itself is
an explicit DEF-044 dependency above. This input has no implementation here. -/
structure Def033Input (hκ : 0 < κ) (C : ChartInterface (L := L) hκ)
    (H : HierarchyRequirements hκ C) where
  active : ℕ → Smooth L → ℤ → ℝ → Prop
  active_definition : ∀ r (u : Smooth L) n omega,
    active r u n omega ↔ 0 < action hκ (physical u) n ∧ ∀ t,
      C.chart.Φ (physical ⟨H.Φ r t u.val, ((H.ham r u.val u.property).2.2 t).1⟩) n =
        Complex.exp (-((t*omega : ℝ) : ℂ)*Complex.I)*C.chart.Φ (physical u) n
  adjacent : ∀ (N _r : ℕ) (a _b : ℤ) (m : MArr N),
    Occupation.DonorOK a (marrArr N m).1 → ℝ
  adjacent_definition : ∀ N r a b m hd,
    adjacent N r a b m hd = eigenvalue L N (κ/N) r (shifted a b m hd) - eigenvalue L N (κ/N) r m
  target : (ℤ → ℝ) → ℤ → ℤ → ℝ
  target_definition : ∀ omega a b, target omega a b = omega b - omega a
  total : ∀ (N _r : ℕ) (_a _b : ℤ), (MArr N → ℝ) → MArr N → ℝ
  total_definition : ∀ N r a b missing m, total N r a b missing m =
    if hd : Occupation.DonorOK a (marrArr N m).1 then adjacent N r a b m hd else missing m
  limit : ∀ (u : L2T L), ‖u‖ = 1 → ℕ → ℤ → ℤ →
    (ℤ → ℝ) → (∀ N, MArr (N+1) → ℝ) → Prop
  limit_definition : ∀ u hu r a b omega missing, limit u hu r a b omega missing ↔
    ∀ epsilon : ℝ, 0 < epsilon → Tendsto (fun N => originalLaw hκ u hu N
      {m | epsilon < |total (N+1) r a b (missing N) m-target omega a b|}) atTop (𝓝 0)

/-- The three source clauses at the SAME fixed smooth unit profile, chart,
full-mass measure, hierarchy and real-direction conventions. -/
structure MixedInterface (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) where
  spectral : SpectralInterface hκ (physical u) hu
  chart : ChartInterface (L := L) hκ
  dynamics : DynamicsInterface hκ chart

/-- Definition realization, INTERMEDIATE. The DEF-033 input remains named and
visible. This only binds the printed interfaces and conventions; it proves no
mixed propagation conclusion and supplies no upstream existence assumption. -/
theorem DEF044_intermediate (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (M : MixedInterface hκ u hu)
    (DEF033Input : Def033Input hκ M.chart M.dynamics.hierarchy) :
    (∀ N r a b m hd, DEF033Input.adjacent N r a b m hd =
      eigenvalue L N (κ/N) r (shifted a b m hd)-eigenvalue L N (κ/N) r m) ∧
    (∀ omega a b, DEF033Input.target omega a b = omega b-omega a) ∧
    (∀ v n, action hκ v n = ‖M.chart.chart.Φ v n‖^2 ∧
      action hκ v n = ‖Def044ChartR51a.reflected (M.chart.chart.Φ v) (-n)‖^2/2) ∧
    WindowDifferentials (L := L) hκ := by
  exact ⟨DEF033Input.adjacent_definition, DEF033Input.target_definition,
    exact_actions M.chart, M.dynamics.window_differentials⟩

end QuantumNLS.Def044InterfacesR51a
#print axioms QuantumNLS.Def044InterfacesR51a.DEF044_intermediate

#print QuantumNLS.Def044InterfacesR51a.Def033Input
#print QuantumNLS.Def044InterfacesR51a.MixedInterface
#print QuantumNLS.Def044InterfacesR51a.DEF044_intermediate
#print axioms QuantumNLS.Def044InterfacesR51a.regularity_mono

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Def044InterfacesR51a." ||
        n.toString.startsWith "_private.QuantumNLS.Def044InterfacesR51a." then
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
  Lean.logInfo m!"Round51 aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard only."

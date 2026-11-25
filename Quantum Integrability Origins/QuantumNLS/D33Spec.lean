import QuantumNLS.Bind7BDEF033H02
/-! integrator trusted spec: verbatim mirror of DEF033Package plus a field-wise construction from the reviewed DEF033_package. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter MeasureTheory Topology
namespace QuantumNLS.D33Spec
open QuantumNLS.Bind7BDEF033H02
open QuantumNLS.ClassicalCharges QuantumNLS.HierarchyFlow
open QuantumNLS.Def033HierarchyR24m QuantumNLS.Def033CoreR24m
open QuantumNLS.BetheLabels QuantumNLS.BetheCoefficientTransform QuantumNLS.BetheSpectralCharges
open QuantumNLS.TerraMultiRound12Definitions QuantumNLS.Def024Order2Joint QuantumNLS.Def024LowEquivariance
variable {L κ : ℝ} [Fact (0 < L)]

structure MirrorDEF033Package (hκ : 0 < κ)
    (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.REF88Chart.K) : Type where
  /-- (A) the active-coordinate action is the squared modulus of the chart coordinate. -/
  action_modulus : ∀ (v : QuantumNLS.PhysicalTensor.L2T L) (n : ℤ),
    ‖w v n‖ ^ 2 = (QuantumNLS.RootIndexedMasses.masses hκ v).1 n
  /-- (B) the fixed smooth hierarchy: `flow r` is the time map of the flow of `I_{r+1}^{(κ)}`. -/
  flow : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ)
  isFlow : ∀ r, IsHamFlow L (hamiltonian L κ r) (flow r)
  /-- (B) the Hamiltonian is the real part of the physical Riccati charge, for every order. -/
  hamiltonian_physical : ∀ r (u : Smooth L),
    ((hamiltonian L κ r u.val : ℝ) : ℂ) = charge L κ u.val (r + 1)
  /-- (B) it is THE flow: any smooth Hamiltonian flow of the same Hamiltonian coincides with it. -/
  flow_unique : ∀ r, UniqueHamFlow L (hamiltonian L κ r) (flow r)
  flow_commute : ∀ r s, ∀ u : Smooth L, ∀ t τ, flow r t (flow s τ u.val) = flow s τ (flow r t u.val)
  /-- (B) order-0, order-1 and order-2 conventions: the staged flows of DEF-024. -/
  flow_staged : ∀ r, r ≤ 2 → ∀ u : Smooth L, ∀ t, flow r t u.val = flowMap2 L κ r t u.val
  /-- (C) the selected active frequency `ω r u n = ω_{r,n}(u)`. -/
  ω : ℕ → Smooth L → ℤ → ℝ
  /-- (C) `w_n(Φ_t^{(r)} u) = e^{-itω_{r,n}(u)} w_n(u)` when `a_n(u) > 0`. -/
  active : ∀ r (u : Smooth L) n, 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 n →
    ActiveFrequency (fun t => w (physical ⟨flow r t u.val, ((isFlow r u.val u.property).2.2 t).1⟩) n)
      (w (physical u) n) (ω r u n)
  /-- (C) the real multiplier is unique. -/
  active_unique : ∀ r (u : Smooth L) n, 0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 n →
    ∀ freq : ℝ, ActiveFrequency
      (fun t => w (physical ⟨flow r t u.val, ((isFlow r u.val u.property).2.2 t).1⟩) n)
      (w (physical u) n) freq → freq = ω r u n
  /-- (D) the shifted array is `m - e_a + e_b` for an occupied donor `m_a ≥ 1`. -/
  shifted_eq : ∀ (N : ℕ) (a b : ℤ) (m : MArr N) (h : QuantumNLS.Occupation.DonorOK a (marrArr N m).1),
    (marrArr N (shifted a b m h)).1 =
      (marrArr N m).1 - QuantumNLS.Occupation.e a + QuantumNLS.Occupation.e b
  /-- (D) the adjacent quantum difference `Λ_{N,r}(m - e_a + e_b) - Λ_{N,r}(m)`, receiver minus donor. -/
  adjacent_eq : ∀ (N r : ℕ) (a b : ℤ) (m : MArr N) (h : QuantumNLS.Occupation.DonorOK a (marrArr N m).1),
    adjacentDifference L κ N r a b m h =
      eigenvalue L N (κ / N) r (shifted a b m h) - eigenvalue L N (κ / N) r m
  /-- (E) the target at positive-action endpoints is `ω_{r,b}(u) - ω_{r,a}(u)`. -/
  target_eq : ∀ r (u : Smooth L) (a b : ℤ),
    0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 a →
    0 < (QuantumNLS.RootIndexedMasses.masses hκ (physical u)).1 b →
    Def033CoreR24m.target (ω r u) a b = ω r u b - ω r u a
  /-- (F) missing-donor convention: the total variable is the adjacent difference on the occupied sector ... -/
  missing_occupied : ∀ (N r : ℕ) (a b : ℤ) (missing : MArr N → ℝ) (m : MArr N)
    (h : QuantumNLS.Occupation.DonorOK a (marrArr N m).1),
    withMissing L κ N r a b missing m = adjacentDifference L κ N r a b m h
  /-- (F) ... and the caller-specified value on the empty-donor sector. -/
  missing_empty : ∀ (N r : ℕ) (a b : ℤ) (missing : MArr N → ℝ) (m : MArr N),
    ¬ QuantumNLS.Occupation.DonorOK a (marrArr N m).1 → withMissing L κ N r a b missing m = missing m
  /-- (F) the original physical product Born law, at particle number `N+1`, is a probability measure ... -/
  born_probability : ∀ (u : Smooth L) (hu : ‖physical u‖ = 1) (N : ℕ),
    IsProbabilityMeasure (originalBorn hκ (physical u) hu N)
  /-- (F) ... with the Born-law singleton weights. -/
  born_singleton : ∀ (u : Smooth L) (hu : ‖physical u‖ = 1) (N : ℕ) (m : MArr (N + 1)),
    originalBorn hκ (physical u) hu N {m} =
      ENNReal.ofReal (bornLaw
        (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L (N + 1) (by omega) hκ)
        (physical u) m)
  /-- (F) each printed limit is convergence in probability of `|total - target|` under the ORIGINAL law,
  with an explicitly specified missing-donor value; no limit is asserted. -/
  limit_iff : ∀ (u : Smooth L) (hu : ‖physical u‖ = 1) (r : ℕ) (a b : ℤ) (ω' : ℤ → ℝ)
    (missing : ∀ N, MArr (N + 1) → ℝ),
    DifferenceLimit hκ (physical u) hu r a b ω' missing ↔
      ∀ ε : ℝ, 0 < ε → Tendsto (fun N => originalBorn hκ (physical u) hu N
        {m | ε < |withMissing L κ (N + 1) r a b (missing N) m - Def033CoreR24m.target ω' a b|})
        atTop (𝓝 0)

noncomputable def DEF033_package_mirror (hκ : 0 < κ) (w : QuantumNLS.PhysicalTensor.L2T L → QuantumNLS.REF88Chart.K) (hw : QuantumNLS.REF88PrintedChart.PrintedChart hκ w) : MirrorDEF033Package hκ w :=
  let P := QuantumNLS.Bind7BDEF033H02.DEF033_package hκ w hw
  ⟨P.action_modulus, P.flow, P.isFlow, P.hamiltonian_physical, P.flow_unique, P.flow_commute, P.flow_staged, P.ω, P.active, P.active_unique, P.shifted_eq, P.adjacent_eq, P.target_eq, P.missing_occupied, P.missing_empty, P.born_probability, P.born_singleton, P.limit_iff⟩

end QuantumNLS.D33Spec
#print axioms QuantumNLS.D33Spec.DEF033_package_mirror

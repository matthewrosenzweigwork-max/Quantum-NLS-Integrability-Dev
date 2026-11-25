import QuantumNLS.AuditWeightedCommonPacketR50a

/-! INTERMEDIATE assembly for R-115CAA16. This proves the analytical
substitution directly from accepted scalar moments and the authorized
conditional REG-015 import. It does not claim integrator acceptance or
supply the FINAL named theorem, which must bind accepted R-7B122087. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators
namespace QuantumNLS.AuditWeightedAssemblyR50a
open QuantumNLS.PhysicalTensor QuantumNLS.BetheLabels
open QuantumNLS.EmpiricalRapidity QuantumNLS.BulkResponseActual
open QuantumNLS.BetheCoefficientTransform
open QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.CommonBethePacket
open QuantumNLS.AuditWeightedProbabilityR49a QuantumNLS.AuditWeightedSeriesR49a
open QuantumNLS.AuditWeightedValuesR50a QuantumNLS.AuditWeightedTightR50a
open QuantumNLS.AuditWeightedSelectionR50a QuantumNLS.AuditWeightedCommonPacketR50a
variable {L κ : ℝ} [Fact (0 < L)] {f : ℝ → ℂ}

/-- The sequence binder precedes every fixed charge and real weight order.
The original product law is used, and all finite packets have every maximal
spectral charge domain. No untruncated moment expectation is asserted. -/
theorem audit_weighted_intermediate (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (hu : ‖smoothL2 hf‖=1) :
    (∀ p : ℝ, 0 ≤ p → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => bornMeasure (physBasis L hκ N) (smoothL2 hf) hu
        {m | ε < error hκ (smoothL2 hf) p N m}) atTop (𝓝 0)) ∧
    (∀ r : ℕ, QuantumNLS.BornConvergence.TendstoInProbability
      (fun N => bornMeasure (physBasis L hκ N) (smoothL2 hf) hu)
      (fun N m => QuantumNLS.BetheSpectralCharges.eigenvalue L N (κ/N) r m/(N : ℝ))
      (charge L κ f (r+1)).re) ∧
    ∃ P : (N : ℕ) → Packet (physBasis L hκ N),
      Tendsto (fun N => ‖vector (P N)-productVec L N (smoothL2 hf)‖) atTop (𝓝 0) ∧
      (∀ r ε, 0 < ε → ∀ᶠ N in atTop, ∀ m ∈ support (P N),
        |QuantumNLS.BetheSpectralCharges.eigenvalue L N (κ/N) r m/(N : ℝ)-(charge L κ f (r+1)).re| ≤ ε) ∧
      (∀ p : ℝ, 0 ≤ p → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ m ∈ support (P N),
        error hκ (smoothL2 hf) p N m ≤ ε) ∧
      ∀ N (ev : MArr N → ℝ), vector (P N) ∈
        (QuantumNLS.BetheSpectralCharges.multiplier (physBasis L hκ N) ev).domain := by
  classical
  refine ⟨weighted_probability hκ hf hu, charge_probability hκ hf hu, ?_⟩
  let X := fun (k : ℕ) (N : ℕ) (m : MArr N) => max (error hκ (smoothL2 hf) (k : ℝ) N m)
    |average (L := L) (κ := κ) (fun t => t^k) N m-(charge L κ f (k+1)).re|
  have hX : ∀ k ε, 0 < ε → Tendsto (fun N =>
      bornMeasure (physBasis L hκ N) (smoothL2 hf) hu {m | ε < X k N m}) atTop (𝓝 0) := by
    intro k ε hε
    have h1 := weighted_probability hκ hf hu k (Nat.cast_nonneg _) ε hε
    have h2 := power_probability hκ hf hu k ε hε
    have ht := h1.add h2
    rw [add_zero] at ht
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
    intro N
    apply (measure_mono (show {m | ε < X k N m} ⊆
      {m | ε < error hκ (smoothL2 hf) (k : ℝ) N m} ∪
      {m | ε < dist (average (L := L) (κ := κ) (fun t => t^k) N m)
        (charge L κ f (k+1)).re} from by
          intro m hm
          simpa only [X,lt_max_iff,Set.mem_union,Set.mem_ofPred_eq,Real.dist_eq] using hm)).trans
      (measure_union_le _ _)
  obtain ⟨E,hE,hgood⟩ := common_good_events
    (fun N => bornMeasure (physBasis L hκ N) (smoothL2 hf) hu) X hX
  obtain ⟨P,hP,hPE,hdom⟩ := packets_from_events (physBasis L hκ) (smoothL2 hf) hu E hE
  refine ⟨P,hP,?_,?_,hdom⟩
  · intro r ε hε
    filter_upwards [hPE,hgood r ε hε,eventually_ge_atTop 1] with N hPN hGN hN
    intro m hm
    rw [spectral_average_eq hκ (by omega)]
    exact (le_max_right _ _).trans (hGN m (hPN m hm))
  · intro p _hp ε hε
    obtain ⟨k,hk⟩ := exists_nat_ge p
    filter_upwards [hPE,hgood k ε hε] with N hPN hGN
    intro m hm
    have hmon := QuantumNLS.AuditWeightedDiagonalR49a.weighted_error_mono
      (fun n => (m.1 n : ℝ)/N) (QuantumNLS.RootIndexedMasses.masses hκ (smoothL2 hf)).1 hk
      (summable_error hκ hf k (Nat.cast_nonneg _) N m)
    exact hmon.trans ((le_max_left _ _).trans (hGN m (hPN m hm)))

end QuantumNLS.AuditWeightedAssemblyR50a

#print axioms QuantumNLS.AuditWeightedAssemblyR50a.audit_weighted_intermediate

#check QuantumNLS.AuditWeightedAssemblyR50a.audit_weighted_intermediate

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.AuditWeightedAssemblyR50a." ||
        n.toString.startsWith "_private.QuantumNLS.AuditWeightedAssemblyR50a." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
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
  Lean.logInfo m!"Round50 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."

import QuantumNLS.EnergyTraceLimit

/-! R-6EA807B1, physical A_k: one theorem on the source's finite-energy
trace-one densities and continuous form-domain vectors. The arbitrary-A
spectral-representation obligation is explicitly separate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Filter Topology
open scoped InnerProductSpace BigOperators ENNReal LinearPMap
namespace QuantumNLS.EnergyTraceConvergence
open EnergyPreparationDef Ext025B10PhysicalEnergy Ext025B10EnergyFamily
open TraceClass EnergyTracePassage EnergyTraceLimit
variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

theorem pure_energy (f : (AhalfT L k).domain) :
    energyTrace (InnerProductSpace.rankOne ℂ (f : Xk L k) (f : Xk L k)) =
      ENNReal.ofReal (‖AhalfT L k f‖^2) := by
  rw [← vecEnergy_eq f]
  unfold energyTrace
  rw [PhysicalEnergyTrace.physTrace_eq_modes]
  unfold vecEnergy
  apply tsum_congr
  intro w
  have hd : (⟪(eK L k).symm (EnergyRealization.ev w),
      InnerProductSpace.rankOne ℂ (f : Xk L k) (f : Xk L k)
        ((eK L k).symm (EnergyRealization.ev w))⟫_ℂ).re =
        ‖⟪(eK L k).symm (EnergyRealization.ev w),(f : Xk L k)⟫_ℂ‖^2 := by
    rw [InnerProductSpace.rankOne_apply,inner_smul_right,
      ← inner_conj_symm (f : Xk L k) ((eK L k).symm (EnergyRealization.ev w)),
      RCLike.conj_mul]
    norm_cast
  have he : (⟪(eK L k).symm (EnergyRealization.ev w),
      InnerProductSpace.rankOne ℂ (f : Xk L k) (f : Xk L k)
        ((eK L k).symm (EnergyRealization.ev w))⟫_ℂ).re =
        ‖(eK L k (f : Xk L k)) w‖^2 := by
    simpa only [inner_mode] using hd
  exact congrArg (fun a : ℝ => ENNReal.ofReal (Energy.kinWeight L k w*a)) he

def pure (f : (AhalfT L k).domain) : FiniteEnergy L k :=
  ⟨InnerProductSpace.rankOne ℂ (f : Xk L k) (f : Xk L k),InnerProductSpace.isPositive_rankOne_self _,
    by rw [pure_energy]; exact ENNReal.ofReal_ne_top⟩

theorem pure_realization (f : (AhalfT L k).domain) :
    IsFormRealization (pure f).val
      (InnerProductSpace.rankOne ℂ (AhalfT L k f) (AhalfT L k f)) := by
  apply (isFormRealization_iff _ _).mpr
  rw [W_rankOne,W_AhalfT]
  rfl

theorem sandwich_pure (f : (AhalfT L k).domain) :
    sandwich (pure f) = InnerProductSpace.rankOne ℂ (AhalfT L k f) (AhalfT L k f) :=
  formRealization_unique (sandwich_spec (pure f)).2.2.1 (pure_realization f)

/-- The conclusion is literally the source's energy trace norm of the
ordinary density difference, via the unique physical form realization. -/
theorem difference_norm (ρ : FiniteEnergy L k) (f : (AhalfT L k).domain) :
    additiveEnergyTraceNorm (ρ.val-(pure f).val) =
      traceNorm (sandwich ρ-InnerProductSpace.rankOne ℂ (AhalfT L k f) (AhalfT L k f)) := by
  apply additiveEnergyTraceNorm_eq
  apply (isFormRealization_iff _ _).mpr
  rw [mul_sub,sub_mul,← (isFormRealization_iff _ _).mp (sandwich_spec ρ).2.2.1,
    ← (isFormRealization_iff _ _).mp (pure_realization f)]

/-- The entire physical A_k instance of the printed positive energy trace
lemma, with both uniform convergence premises and no convergence conclusion
supplied as a hypothesis. Form continuity is expressed in the graph embedding
f ↦ (f,A_k^(1/2)f); this is precisely the form-norm topology. -/
theorem R_6EA807B1_physical {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (f : T → (AhalfT L k).domain)
    (hf : Continuous (fun t => ((f t : Xk L k),AhalfT L k (f t))))
    (_hunit : ∀ t, ‖(f t : Xk L k)‖ = 1)
    (ρ : ℕ → T → FiniteEnergy L k)
    (_htrace : ∀ n t, posTrace (ρ n t).val = 1)
    (hconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      traceNorm ((ρ n t).val-InnerProductSpace.rankOne ℂ (f t : Xk L k) (f t : Xk L k)) ≤ ENNReal.ofReal ε)
    (henergy : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      |(energyTrace (ρ n t).val).toReal-‖AhalfT L k (f t)‖^2| ≤ ε) :
    Tendsto (fun n => ⨆ t,
      additiveEnergyTraceNorm ((ρ n t).val-InnerProductSpace.rankOne ℂ (f t : Xk L k) (f t : Xk L k)))
        atTop (𝓝 0) := by
  have hg : IsCompact (Set.range (fun t => AhalfT L k (f t))) := isCompact_range hf.snd
  have hB (n : ℕ) (t : T) : (sandwich (ρ n t)).IsPositive ∧ IsTraceClass (sandwich (ρ n t)) :=
    ⟨(sandwich_spec (ρ n t)).1,(sandwich_spec (ρ n t)).2.1⟩
  have ht : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      |total (sandwich (ρ n t))-‖AhalfT L k (f t)‖^2| ≤ ε := by
    intro ε hε
    filter_upwards [henergy ε hε] with n hn
    intro t
    simpa only [total,(sandwich_spec (ρ n t)).2.2.2.1] using hn t
  have hc (m : ℕ) : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      traceNorm (cutoff L k m*(sandwich (ρ n t)-
        InnerProductSpace.rankOne ℂ (AhalfT L k (f t)) (AhalfT L k (f t)))*cutoff L k m) ≤
          ENNReal.ofReal ε := by
    have hh := uniform_compressed_convergence ρ (fun t => pure (f t)) hconv m (Nat.cast_nonneg m)
    simpa only [sandwich_pure] using hh
  have hu := uniform_gentle_limit (basis L k) (spectral L k) spectral_positive
    (fun n t => sandwich (ρ n t)) (fun t => AhalfT L k (f t)) hB hg ht hc
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨r,_,hr0,hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hr : 0 < r := ENNReal.ofReal_pos.mp hr0
  filter_upwards [hu r hr] with n hn
  apply iSup_le
  intro t
  rw [show InnerProductSpace.rankOne ℂ (f t : Xk L k) (f t : Xk L k) = (pure (f t)).val from rfl,
    difference_norm]
  exact (hn t).trans hrε.le
end QuantumNLS.EnergyTraceConvergence

#print axioms QuantumNLS.EnergyTraceConvergence.pure_energy
#print axioms QuantumNLS.EnergyTraceConvergence.sandwich_pure
#print axioms QuantumNLS.EnergyTraceConvergence.difference_norm
#print axioms QuantumNLS.EnergyTraceConvergence.R_6EA807B1_physical
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.EnergyTraceConvergence" then
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
  Lean.logInfo m!"EnergyTraceConvergence audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."

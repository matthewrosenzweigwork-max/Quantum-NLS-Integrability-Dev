import QuantumNLS.AllOrderEnergyLimitsR55a

/-! The compact-form and positive-trace stages of the R-568BCDF8 argument,
with the physical DEF-031 energy norm and complex test forms. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Filter Topology
open scoped ENNReal InnerProductSpace
namespace QuantumNLS.AllOrderEnergyTraceR55a
open EnergyPreparationDef EnergyTraceConvergence TraceClass Ext025B10EnergyFamily
open Ext025B10PhysicalEnergy AllOrderEnergyLimitsR55a
variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

/-- Vanishing supremum is the epsilon form of uniform convergence used by
both accepted trace lemmas. -/
theorem eventually_traceNorm_le {T : Type*} (ρ : ℕ → T → Xk L k →L[ℂ] Xk L k)
    (σ : T → Xk L k →L[ℂ] Xk L k)
    (h : Tendsto (fun n => ⨆ t, traceNorm (ρ n t - σ t)) atTop (𝓝 0)) :
    ∀ δ > (0 : ℝ), ∀ᶠ n in atTop, ∀ t,
      traceNorm (ρ n t - σ t) ≤ ENNReal.ofReal δ := by
  intro δ hδ
  filter_upwards [(tendsto_order.1 h).2 (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)] with n hn
  exact fun t => (le_iSup (fun t => traceNorm (ρ n t - σ t)) t).trans hn.le

/-- An eventual bound suffices for compact form passage, as needed when only
the limsup of the energy per particle is controlled. The replacement on the
finite prefix is the limiting state itself. -/
theorem compact_forms_eventually {T : Type*}
    (ρ : ℕ → T → FiniteEnergy L k) (σ : T → FiniteEnergy L k)
    (B : ℝ) (hB : 0 ≤ B) (hρ : ∀ᶠ n in atTop, ∀ t, energyTrace (ρ n t).val ≤ ENNReal.ofReal B)
    (hσ : ∀ t, energyTrace (σ t).val ≤ ENNReal.ofReal B)
    (hconv : ∀ δ > (0 : ℝ), ∀ᶠ n in atTop, ∀ t,
      traceNorm ((ρ n t).val - (σ t).val) ≤ ENNReal.ofReal δ)
    (C : Xk L k →L[ℂ] Xk L k) (hC : IsCompactOperator C) :
    TendstoUniformly (fun n t => EnergyFormPass.expectation C (ρ n t))
      (fun t => EnergyFormPass.expectation C (σ t)) atTop := by
  obtain ⟨n₀, h₀⟩ := eventually_atTop.1 hρ
  let ρ' : ℕ → T → FiniteEnergy L k := fun n t => if n₀ ≤ n then ρ n t else σ t
  have hρ' (n : ℕ) (t : T) : energyTrace (ρ' n t).val ≤ ENNReal.ofReal B := by
    by_cases hn : n₀ ≤ n
    · simpa only [ρ', if_pos hn] using h₀ n hn t
    · simpa only [ρ', if_neg hn] using hσ t
  have hconv' (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ n in atTop, ∀ t,
      traceNorm ((ρ' n t).val - (σ t).val) ≤ ENNReal.ofReal δ := by
    filter_upwards [eventually_ge_atTop n₀, hconv δ hδ] with n hn h
    simpa only [ρ', if_pos hn] using h
  have h := EnergyFormPassFinal.R_C17D95AA_physical ρ' σ B hB hρ' hσ hconv' C hC
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  filter_upwards [eventually_ge_atTop n₀, Metric.tendstoUniformly_iff.1 h ε hε] with n hn ht
  simpa only [ρ', if_pos hn] using ht

/-- Trace duality for every complex bounded sandwich. A bounded form on
H¹ × H¹ is represented on L² by its bounded sandwich under the unitary
form-norm identification. -/
theorem bounded_form_difference (ρ σ : FiniteEnergy L k) (C : Xk L k →L[ℂ] Xk L k) :
    ‖EnergyFormPass.expectation C ρ - EnergyFormPass.expectation C σ‖ ≤
      ‖C‖ * (additiveEnergyTraceNorm (ρ.val - σ.val)).toReal := by
  have hρ := (sandwich_spec ρ).2.1
  have hσ := (sandwich_spec σ).2.1
  have hnorm : additiveEnergyTraceNorm (ρ.val - σ.val) = traceNorm (sandwich ρ - sandwich σ) := by
    apply additiveEnergyTraceNorm_eq
    apply (isFormRealization_iff _ _).mpr
    rw [mul_sub, sub_mul, ← (isFormRealization_iff _ _).mp (sandwich_spec ρ).2.2.1,
      ← (isFormRealization_iff _ _).mp (sandwich_spec σ).2.2.1]
  have hfin := EnergyFormPass.finite_sub (sandwich ρ) (sandwich σ) hρ.ne hσ.ne
  rw [hnorm, EnergyFormPass.expectation, EnergyFormPass.expectation, ← Ext025B11TracePairing.trace_sub
    (basis L k) (C * sandwich ρ) (C * sandwich σ)
    (Ext025B11TracePairing.finite_left _ _ hρ.ne) (Ext025B11TracePairing.finite_left _ _ hσ.ne), ← mul_sub]
  exact Ext025B11TracePairing.pairing_bound (basis L k) C _ hfin

/-- Convergence in the physical energy trace norm implies uniform convergence
against all bounded test forms, via trace duality without a reality restriction. -/
theorem bounded_form_limit {T : Type*} (ρ : ℕ → T → FiniteEnergy L k) (σ : T → FiniteEnergy L k)
    (h : Tendsto (fun n => ⨆ t, additiveEnergyTraceNorm ((ρ n t).val - (σ t).val)) atTop (𝓝 0))
    (C : Xk L k →L[ℂ] Xk L k) :
    TendstoUniformly (fun n t => EnergyFormPass.expectation C (ρ n t))
      (fun t => EnergyFormPass.expectation C (σ t)) atTop := by
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  let δ := ε / (‖C‖ + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [(tendsto_order.1 h).2 (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)] with n hn
  intro t
  rw [dist_eq_norm, norm_sub_rev]
  have ht := (le_iSup (fun t => additiveEnergyTraceNorm ((ρ n t).val - (σ t).val)) t).trans_lt hn
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht.le
  rw [ENNReal.toReal_ofReal hδ.le] at hb
  apply (bounded_form_difference (ρ n t) (σ t) C).trans_lt
  calc
    _ ≤ ‖C‖ * δ := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ < (‖C‖ + 1) * δ := mul_lt_mul_of_pos_right (by linarith) hδ
    _ = ε := by dsimp [δ]; field_simp

/-- Use the positive-trace predecessor on the rank-k density after uniform
convergence of the rank-one kinetic expectation has been established. -/
theorem fixed_rank_upgrade {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (f : T → (AhalfT L k).domain)
    (hf : Continuous (fun t => ((f t : Xk L k), AhalfT L k (f t))))
    (hunit : ∀ t, ‖(f t : Xk L k)‖ = 1)
    (ρ : ℕ → T → FiniteEnergy L k) (htrace : ∀ n t, posTrace (ρ n t).val = 1)
    (hOrdinary : Tendsto (fun n => ⨆ t, traceNorm ((ρ n t).val - (pure (f t)).val)) atTop (𝓝 0))
    (kinetic : ℕ → T → ℝ) (a : T → ℝ)
    (hKinetic : TendstoUniformly kinetic a atTop)
    (hRank : ∀ᶠ n in atTop, ∀ t, (energyTrace (ρ n t).val).toReal = 1 + (k : ℝ) * kinetic n t)
    (hProduct : ∀ t, ‖AhalfT L k (f t)‖^2 = 1 + (k : ℝ) * a t) :
    Tendsto (fun n => ⨆ t, additiveEnergyTraceNorm ((ρ n t).val - (pure (f t)).val)) atTop (𝓝 0) := by
  apply R_6EA807B1_physical f hf hunit ρ htrace
    (eventually_traceNorm_le (fun n t => (ρ n t).val) (fun t => (pure (f t)).val) hOrdinary)
  intro ε hε
  let δ := ε / ((k : ℝ) + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [hRank, Metric.tendstoUniformly_iff.1 hKinetic δ hδ] with n hn hk
  intro t
  have ht := hk t
  rw [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm (a t)] at ht
  rw [hn t, hProduct t, show 1 + (k : ℝ) * kinetic n t - (1 + (k : ℝ) * a t) =
    (k : ℝ) * (kinetic n t - a t) by ring, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ (k : ℝ) * δ := mul_le_mul_of_nonneg_left ht.le (Nat.cast_nonneg _)
    _ ≤ ((k : ℝ) + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
    _ = ε := by dsimp [δ]; field_simp

/-- Assemble the scalar part of the printed proof and apply the accepted
positive-trace theorem. The inputs to this proof step are the conserved form
identity, initial trace-norm convergence, compact contact passage, and
marginal trace identities. In particular no convergence of the energy traces
is a premise. -/
theorem contact_energy_upgrade {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (E weight : ℕ → ℝ) (hWeight : Tendsto weight atTop (𝓝 1))
    (ρ₀ : ℕ → FiniteEnergy L 1) (σ₀ : FiniteEnergy L 1) (a₀ b₀ : ℝ)
    (ha₀ : 0 ≤ a₀) (hA₀ : energyTrace σ₀.val = ENNReal.ofReal (1 + a₀))
    (hOrd₀ : Tendsto (fun n => traceNorm ((ρ₀ n).val - σ₀.val)) atTop (𝓝 0))
    (contact₀ : ℕ → ℝ) (hContact₀ : Tendsto contact₀ atTop (𝓝 b₀))
    (hIdentity₀ : ∀ᶠ n in atTop,
      E n = (energyTrace (ρ₀ n).val).toReal - 1 + weight n * contact₀ n)
    (hUpper : limsup (fun n => (E n : EReal)) atTop ≤ ((a₀ + b₀ : ℝ) : EReal))
    (f : T → (AhalfT L k).domain) (hf : Continuous (fun t => ((f t : Xk L k), AhalfT L k (f t))))
    (hunit : ∀ t, ‖(f t : Xk L k)‖ = 1)
    (ρ : ℕ → T → FiniteEnergy L k) (htrace : ∀ n t, posTrace (ρ n t).val = 1)
    (hOrdinary : Tendsto (fun n => ⨆ t, traceNorm ((ρ n t).val - (pure (f t)).val)) atTop (𝓝 0))
    (kinetic contact : ℕ → T → ℝ) (a b : T → ℝ)
    (hIdentity : ∀ᶠ n in atTop, ∀ t, E n = kinetic n t + weight n * contact n t)
    (hConservation : ∀ t, a₀ + b₀ = a t + b t)
    (hContact : TendstoUniformly contact b atTop) (B : ℝ) (hB : ∀ t, |b t| ≤ B) (hB₀ : 0 ≤ B)
    (hRank : ∀ᶠ n in atTop, ∀ t, (energyTrace (ρ n t).val).toReal = 1 + (k : ℝ) * kinetic n t)
    (hProduct : ∀ t, ‖AhalfT L k (f t)‖^2 = 1 + (k : ℝ) * a t) :
    (Tendsto E atTop (𝓝 (a₀ + b₀))) ∧
    (Tendsto (fun n => ⨆ t, additiveEnergyTraceNorm ((ρ n t).val - (pure (f t)).val)) atTop (𝓝 0)) ∧
    ∀ C : Xk L k →L[ℂ] Xk L k,
      TendstoUniformly (fun n t => EnergyFormPass.expectation C (ρ n t))
        (fun t => EnergyFormPass.expectation C (pure (f t))) atTop := by
  have hE := energy_limit E (fun n => (energyTrace (ρ₀ n).val).toReal - 1) contact₀ weight
    a₀ b₀ hIdentity₀ (fun ε hε => initial_kinetic_lower hOrd₀ (fun n => (ρ₀ n).2.2) ha₀ hA₀ hε)
    hContact₀ hWeight ((limsup_le_iff E (a₀ + b₀)).1 hUpper)
  have hk := kinetic_limit E kinetic (fun n t => weight n * contact n t) a b (a₀ + b₀)
    hE hIdentity hConservation (weighted_contact_limit contact b weight hWeight hContact B hB hB₀)
  have hlimit := fixed_rank_upgrade f hf hunit ρ htrace hOrdinary kinetic a hk hRank hProduct
  exact ⟨hE, hlimit, bounded_form_limit ρ (fun t => pure (f t)) hlimit⟩

end QuantumNLS.AllOrderEnergyTraceR55a
set_option maxHeartbeats 15000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := env.constants.toList.filterMap fun (n, _) =>
    if n.toString.startsWith "QuantumNLS.AllOrderEnergyTraceR55a." then some n else none
  let roots := pending.length
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := ci.type.getUsedConstants.toList ++ pending
        if let some v := ci.value? (allowOpaque := true) then
          pending := v.getUsedConstants.toList ++ pending
      else throwError "Missing dependency: {n}"
  Lean.logInfo m!"R55a audit PASS: {roots} namespace constants; {seen.size} transitive constants."

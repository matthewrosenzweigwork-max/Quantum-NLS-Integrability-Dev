import QuantumNLS.Ext025B11TracePairing

/-! R-C17D95AA at the physical A_k = 1 + sum D_j^2. Complex form
expectations pair the compact kinetic sandwich K_C with the constructed
positive finite-energy realization. No trace convergence is a premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Filter Topology
open scoped InnerProductSpace BigOperators ENNReal LinearPMap
namespace QuantumNLS.EnergyFormPass
open EnergyPreparationDef Ext025B10PhysicalEnergy Ext025B10EnergyFamily
open Ext025B11TracePairing TraceClass TraceIdeal
variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

/-- Physical bounded-form expectation, including non-Hermitian forms. -/
def expectation (K : Xk L k →L[ℂ] Xk L k) (ρ : FiniteEnergy L k) : ℂ :=
  trace (basis L k) (K*sandwich ρ)

/-- The form whose kinetic sandwich is K, on the exact physical form domain. -/
def form (K : Xk L k →L[ℂ] Xk L k) (f g : (AhalfT L k).domain) : ℂ :=
  ⟪AhalfT L k f,K (AhalfT L k g)⟫_ℂ

theorem kinetic_sandwich (K : Xk L k →L[ℂ] Xk L k) (x y : Xk L k) :
    form K ⟨W L k x,W_mem x⟩ ⟨W L k y,W_mem y⟩ = ⟪x,K y⟫_ℂ := by
  simp only [form,AhalfT_W]

theorem density_finite (ρ : FiniteEnergy L k) : traceNorm ρ.val ≠ ⊤ := by
  obtain ⟨_,_,_,_,_,he⟩ := positive_formRealization ρ.property.1 ρ.property.2
  exact ne_top_of_le_ne_top ρ.property.2 (he ▸ traceNorm_le_additive ρ.val)

theorem finite_sub (S T : Xk L k →L[ℂ] Xk L k)
    (hS : traceNorm S ≠ ⊤) (hT : traceNorm T ≠ ⊤) : traceNorm (S-T) ≠ ⊤ := by
  have hn : traceNorm (-T) = traceNorm T := by
    rw [show -T = (-1 : ℂ) • T from (neg_one_smul ℂ T).symm,traceNorm_smul]
    simp
  rw [sub_eq_add_neg]
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hS,by rwa [hn]⟩)
    (traceNorm_add_le S (-T))

theorem cutoff_basis (M : ℝ) (w : Energy.Mom k) :
    cutoff L k M (basis L k w) =
      (if Energy.kinWeight L k w ∈ Set.Icc 1 M then (1 : ℂ) else 0) • basis L k w :=
  by
    classical
    simpa only [cutoff,spectral,Ext025B10Atomic.resolution,Set.mem_preimage] using
      BoundedBetheTransfer.projection_basis (basis L k)
        (Energy.kinWeight L k ⁻¹' Set.Icc 1 M) w

theorem root_basis (M : ℝ) (w : Energy.Mom k) :
    root L k M (basis L k w) =
      Ext025B8EnergyCompression.rootSymbol M (Energy.kinWeight L k w) • basis L k w :=
  Ext025B10Atomic.bounded_basis (basis L k) _ _ _ _ _ _ w

/-- The truncated form is the actual bounded root-cutoff operator paired
with the ordinary density, proved by diagonal trace cyclicity. -/
theorem truncated_identity (K : Xk L k →L[ℂ] Xk L k)
    (ρ : FiniteEnergy L k) (M : ℝ) :
    expectation (cutoff L k M*K*cutoff L k M) ρ =
      trace (basis L k) ((root L k M*K*root L k M)*ρ.val) := by
  let P := cutoff L k M
  let R := root L k M
  change trace (basis L k) ((P*K*P)*sandwich ρ) = _
  calc
    _ = trace (basis L k) ((K*P*sandwich ρ)*P) := by
      simpa only [mul_assoc] using diagonal_cycle (basis L k) P
        (K*P*sandwich ρ) _ (cutoff_basis M)
    _ = trace (basis L k) (K*(R*ρ.val*R)) := by
      have hb := congrArg (fun Z => trace (basis L k) (K*Z))
        ((sandwich_spec ρ).2.2.2.2 M)
      simpa only [P,R,mul_assoc] using hb
    _ = trace (basis L k) ((R*K*R)*ρ.val) := by
      simpa only [mul_assoc] using (diagonal_cycle (basis L k) R
        (K*R*ρ.val) _ (root_basis M)).symm

/-- Exact uniform form-error bound from the physical energy expectation. -/
theorem error_bound (K J : Xk L k →L[ℂ] Xk L k) (ρ : FiniteEnergy L k) :
    ‖expectation K ρ-expectation J ρ‖ ≤ ‖K-J‖*(energyTrace ρ.val).toReal := by
  have hS := (sandwich_spec ρ).2.1.ne
  have he : expectation K ρ-expectation J ρ = trace (basis L k) ((K-J)*sandwich ρ) := by
    rw [sub_mul,trace_sub _ _ _ (finite_left K _ hS) (finite_left J _ hS)]
    rfl
  rw [he]
  have h := pairing_bound (basis L k) (K-J) (sandwich ρ) hS
  rwa [traceNorm_of_isPositive (sandwich_spec ρ).1,(sandwich_spec ρ).2.2.2.1] at h

/-- Fixed-M passage uses ordinary trace norm and the literal M ||K|| bound. -/
theorem truncated_bound (K : Xk L k →L[ℂ] Xk L k)
    (ρ σ : FiniteEnergy L k) (M : ℝ) (hM : 0 ≤ M) :
    ‖expectation (cutoff L k M*K*cutoff L k M) ρ-
      expectation (cutoff L k M*K*cutoff L k M) σ‖ ≤
      M*‖K‖*(traceNorm (ρ.val-σ.val)).toReal := by
  rw [truncated_identity,truncated_identity]
  have hρ := density_finite ρ
  have hσ := density_finite σ
  rw [← trace_sub _ _ _ (finite_left _ _ hρ) (finite_left _ _ hσ),← mul_sub]
  exact (pairing_bound (basis L k) _ _ (finite_sub _ _ hρ hσ)).trans
    (mul_le_mul_of_nonneg_right (physical_sandwich_norm M hM K) ENNReal.toReal_nonneg)

/-- Full physical application of the printed lemma, uniformly in an arbitrary
parameter set. Energy bounds and ordinary trace convergence are the source
hypotheses; the form passage is derived here. -/
theorem R_C17D95AA_physical {T : Type*}
    (ρ : ℕ → T → FiniteEnergy L k) (σ : T → FiniteEnergy L k)
    (B : ℝ) (hB : 0 ≤ B)
    (hρ : ∀ n t, energyTrace (ρ n t).val ≤ ENNReal.ofReal B)
    (hσ : ∀ t, energyTrace (σ t).val ≤ ENNReal.ofReal B)
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ t,
      traceNorm ((ρ n t).val-(σ t).val) ≤ ENNReal.ofReal δ)
    (K : Xk L k →L[ℂ] Xk L k) (hK : IsCompactOperator K) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      ‖expectation K (ρ n t)-expectation K (σ t)‖ ≤ ε := by
  intro ε hε
  let η := ε/(4*(B+1))
  have hη : 0 < η := div_pos hε (by positivity)
  have ht : ∀ᶠ m : ℕ in atTop,
      ‖K-cutoff L k m*K*cutoff L k m‖ < η :=
    (tendsto_order.mp (compact_compression K hK)).2 η hη
  obtain ⟨m,hm⟩ := ht.exists
  let J := cutoff L k m*K*cutoff L k m
  let D := (m : ℝ)*‖K‖
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg m) (norm_nonneg K)
  let δ := ε/(2*(D+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [hconv δ hδ] with n hn
  intro t
  have heρ : (energyTrace (ρ n t).val).toReal ≤ B :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hρ n t)).trans_eq (ENNReal.toReal_ofReal hB)
  have heσ : (energyTrace (σ t).val).toReal ≤ B :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hσ t)).trans_eq (ENNReal.toReal_ofReal hB)
  have hc : (traceNorm ((ρ n t).val-(σ t).val)).toReal ≤ δ :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hn t)).trans_eq (ENNReal.toReal_ofReal hδ.le)
  have eρ : ‖expectation K (ρ n t)-expectation J (ρ n t)‖ ≤ η*B :=
    (error_bound K J (ρ n t)).trans
      (mul_le_mul hm.le heρ ENNReal.toReal_nonneg hη.le)
  have eσ : ‖expectation J (σ t)-expectation K (σ t)‖ ≤ η*B := by
    rw [norm_sub_rev]
    exact (error_bound K J (σ t)).trans
      (mul_le_mul hm.le heσ ENNReal.toReal_nonneg hη.le)
  have eJ : ‖expectation J (ρ n t)-expectation J (σ t)‖ ≤ D*δ :=
    (truncated_bound K (ρ n t) (σ t) m (Nat.cast_nonneg m)).trans
      (mul_le_mul_of_nonneg_left hc hD)
  have hηB : η*B ≤ ε/4 := by
    have he := div_mul_cancel₀ ε (ne_of_gt (show 0 < 4*(B+1) by positivity))
    change ε/(4*(B+1))*B ≤ ε/4
    nlinarith [div_pos hε (show 0 < 4*(B+1) by positivity)]
  have hδD : D*δ ≤ ε/2 := by
    have he := div_mul_cancel₀ ε (ne_of_gt (show 0 < 2*(D+1) by positivity))
    change D*(ε/(2*(D+1))) ≤ ε/2
    nlinarith [div_pos hε (show 0 < 2*(D+1) by positivity)]
  calc
    _ ≤ ‖expectation K (ρ n t)-expectation J (ρ n t)‖+
        (‖expectation J (ρ n t)-expectation J (σ t)‖+
          ‖expectation J (σ t)-expectation K (σ t)‖) :=
      (norm_sub_le_norm_sub_add_norm_sub _ (expectation J (ρ n t)) _).trans
        (add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub
          (expectation J (ρ n t)) (expectation J (σ t)) (expectation K (σ t))))
    _ ≤ η*B+(D*δ+η*B) := add_le_add eρ (add_le_add eJ eσ)
    _ ≤ ε := by linarith
end QuantumNLS.EnergyFormPass

#print axioms QuantumNLS.EnergyFormPass.R_C17D95AA_physical
#print axioms QuantumNLS.EnergyFormPass.truncated_identity
#print axioms QuantumNLS.EnergyFormPass.kinetic_sandwich
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.EnergyFormPass" then
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
  Lean.logInfo m!"EnergyFormPass audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."

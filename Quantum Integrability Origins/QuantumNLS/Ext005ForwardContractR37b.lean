import QuantumNLS.Ext005SourceLimitR36b
import QuantumNLS.Ext005SmoothedWeakR37b

/-! The actual extracted source limit is an energy-bounded weak solution.
This contract covers forward data at the left endpoint of every finite
interval; it does not assert reversed-time existence from right-end data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ContDiff
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005ForwardContractR37b
open Ext005OperatorFormR113 Ext005SourceIntervalR32b Ext005SourceBoundsR36b
open Ext005GramResolventR112 Ext005GramConvergenceR112 Ext005RegularizedR33b
open Ext005ComplexRieszR113 Ext005ComplexForceR113 Ext005HilbertEnergyR112
open Ext005SourceLimitR36b Ext005SmoothedWeakR37b Ext005LimitRegularityR35b
open Ext005AntidualWeakR113
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : PositiveOperator H) (a b : ℝ) (S : SourceOn A a b)
local instance (priority := 10000) : InnerProductSpace ℝ (FormDomain A) :=
  InnerProductSpace.rclikeToReal ℂ (FormDomain A)

/-- Unconditional original forward existence in the exact owner D3 class.
The original weak equation and the energy bound are conclusions from the
source assumptions, not hypotheses about a supplied solution. -/
theorem source_forward_D3_exists (hab : a ≤ b) (u₀ : FormDomain A) :
    ∃ v : ℝ → FormDomain A,
      v a = u₀ ∧ (∀ t ∈ Icc a b, ‖v t‖ ≤ forwardRadius A a b S u₀) ∧
      D3On A a b S (fun t => inclusion A (v t)) := by
  obtain ⟨u, L, v, hL, hLa, _, hc, hd, hb, hv, hvc, hvi, hve, _, hw⟩ :=
    source_energy_bounded_limit A a b S hab u₀
  let : NeBot L := hL
  let i := (inclusion A).restrictScalars ℝ
  let F := fun t => forceMap (formOperator (sourceForm A a b S t))
  have hF : ContinuousOn F (Icc a b) :=
    forceMap.continuous.comp_continuousOn (coefficient_continuous A a b S)
  have hFb (t : ℝ) (ht : t ∈ Icc a b) : ‖F t‖ ≤ finiteBound A a b S := by
    rw [force_norm]
    exact coefficient_bound A a b S t ht
  have hl := fun n => smoothed_antidual_time_bound i (epsilon n) (epsilon_pos n)
    a b (u n) F (finiteBound A a b S) (forwardRadius A a b S u₀)
    (finiteBound_nonneg A a b S) (hd n) hFb (hb n)
  have he := regularized_weak_limit i (inclusion_injective A) a b hab F u v L hLa
    (forwardRadius A a b S u₀) (finiteBound A a b S)
    (finiteBound A a b S * forwardRadius A a b S u₀)
    (forwardRadius_nonneg A a b S u₀) (finiteBound_nonneg A a b S)
    (mul_nonneg (finiteBound_nonneg A a b S) (forwardRadius_nonneg A a b S u₀))
    hc hd hb hv hl hw hF hFb
  have hea : AntidualWeakOn (Ioo a b)
      (fun t => ambient (inclusion A) (inclusion A (v t)))
      (fun t => (-Complex.I) • sourceForm A a b S t (v t)) := by
    apply (schrodinger_weak_iff (Ioo a b) (inclusion A) (sourceForm A a b S)
      (fun t => inclusion A (v t)) v).mpr
    exact he
  refine ⟨v, hvi, hv, hvc, hve, ?_⟩
  intro z p hp hc hs
  have h := hea z p hp hc hs
  simp only [ambient_apply] at h
  rw [h]
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  by_cases ht : t ∈ Icc a b
  · change p t * ((-Complex.I) * sourceForm A a b S t (v t) z).re = _
    rw [sourceForm_apply A a b S t ht]
    have heq : lift i (inclusion A (v t)) = v t := lift_eq i (inclusion_injective A) (v t)
    change p t * ((-Complex.I) * S.hamiltonian t (v t) z).re =
      p t * (S.hamiltonian t (lift i (inclusion A (v t))) z).im
    rw [heq]
    simp [Complex.mul_re]
  · have hz : p t = 0 := image_eq_zero_of_notMem_tsupport (fun h =>
      ht (Ioo_subset_Icc_self (hs h)))
    simp only [hz, zero_mul]

/-- One named forward EXT-005 contract on every finite nondegenerate
interval: actual source existence, explicit form bound, norm conservation,
and uniqueness against every competitor in D3 on this interval. The data
are posed at the LEFT endpoint; no backward existence is hidden here. -/
theorem EXT005_forward_contract (hab : a < b) (u₀ : FormDomain A) :
    ∃ v : ℝ → FormDomain A,
      v a = u₀ ∧ (∀ t ∈ Icc a b, ‖v t‖ ≤ forwardRadius A a b S u₀) ∧
      D3On A a b S (fun t => inclusion A (v t)) ∧
      ‖inclusion A (v b)‖ = ‖inclusion A u₀‖ ∧
      ∀ y : ℝ → H, D3On A a b S y → y a = inclusion A u₀ →
        ∀ t ∈ Icc a b, y t = inclusion A (v t) := by
  obtain ⟨v, hi, hb, hv⟩ := source_forward_D3_exists A a b S hab.le u₀
  refine ⟨v, hi, hb, hv, ?_, ?_⟩
  · have hn := EXT005_D3_norm_conserved A a b S hab (fun t => inclusion A (v t)) hv
    rw [hi] at hn
    nlinarith [norm_nonneg (inclusion A (v b)), norm_nonneg (inclusion A u₀)]
  · intro y hy hyi
    exact EXT005_D3_finite_interval_unique A a b S a hab ⟨le_rfl, hab.le⟩
      y (fun t => inclusion A (v t)) hy hv (by rw [hi]; exact hyi)

end QuantumNLS.Ext005ForwardContractR37b
#print axioms QuantumNLS.Ext005ForwardContractR37b.source_forward_D3_exists
#print axioms QuantumNLS.Ext005ForwardContractR37b.EXT005_forward_contract

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005ForwardContractR37b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005ForwardContractR37b." then
      pending := pending.push n
  let roots := pending.size
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
  Lean.logInfo m!"R37b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."

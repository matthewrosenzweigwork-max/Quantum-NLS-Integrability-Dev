import QuantumNLS.Ext005WeakSubfilterR36b

/-! Apply genuine compactness to the actual source-controlled approximate
solutions. The resulting candidate has form bounds, an H-continuous
representative and the correct initial trace. Identification of its weak
equation and of the L1-dual limit remains separate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ENNReal
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005SourceLimitR36b
open Ext005OperatorFormR113 Ext005SourceIntervalR32b Ext005SourceBoundsR36b
open Ext005GramResolventR112 Ext005GramConvergenceR112 Ext005RegularizedR33b
open Ext005ComplexRieszR113 Ext005ComplexForceR113 Ext005HilbertEnergyR112
open Ext005WeakStarR36b Ext005WeakSubfilterR36b
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : PositiveOperator H) (a b : ℝ) (S : SourceOn A a b)
local instance (priority := 10000) : InnerProductSpace ℝ (FormDomain A) :=
  InnerProductSpace.rclikeToReal ℂ (FormDomain A)

/-- Actual source approximants and an extracted energy-bounded candidate
on every finite forward interval. The weak equation is NOT a premise or
conclusion of this intermediate theorem. -/
theorem source_energy_bounded_limit (hab : a ≤ b) (u₀ : FormDomain A) :
    ∃ (u : ℕ → ℝ → FormDomain A) (L : Filter ℕ) (v : ℝ → FormDomain A),
      NeBot L ∧ L ≤ atTop ∧
      (∀ n, u n a = u₀) ∧ (∀ n, Continuous (u n)) ∧
      (∀ n t, t ∈ Icc a b → HasDerivAt (u n)
        (generator ((inclusion A).restrictScalars ℝ) (epsilon n) (epsilon_pos n)
          (forceMap (formOperator (sourceForm A a b S t))) (u n t)) t) ∧
      (∀ n t, t ∈ Icc a b →
        ‖C ((inclusion A).restrictScalars ℝ) n (u n t)‖ ≤ forwardRadius A a b S u₀) ∧
      (∀ t ∈ Icc a b, ‖v t‖ ≤ forwardRadius A a b S u₀) ∧
      ContinuousOn (fun t => inclusion A (v t)) (Icc a b) ∧ v a = u₀ ∧
      EnergyBounded ((inclusion A).restrictScalars ℝ) (Icc a b) (fun t => inclusion A (v t)) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        ‖gram ((inclusion A).restrictScalars ℝ) (v t) -
          gram ((inclusion A).restrictScalars ℝ) (v s)‖ ≤
          finiteBound A a b S * forwardRadius A a b S u₀ * ‖t-s‖) ∧
      ∀ t ∈ Icc a b, ∀ z : FormDomain A,
        Tendsto (fun n => (⟪z, C ((inclusion A).restrictScalars ℝ) n (u n t)⟫_ℂ).re)
          L (𝓝 (⟪z, v t⟫_ℂ).re) := by
  obtain ⟨u, hi, hc, hd, _, hb, hl⟩ := source_bounded_approximate_sequence A a b S hab u₀
  let i := (inclusion A).restrictScalars ℝ
  obtain ⟨L, hL, hLa, v, hv, hvc, hvi, hvl, hw⟩ := extract_bounded_continuous_limit
    i (inclusion_injective A) a b hab (fun n t => C i n (u n t)) u₀
    (forwardRadius A a b S u₀) (finiteBound A a b S * forwardRadius A a b S u₀)
    (forwardRadius_nonneg A a b S u₀)
    (mul_nonneg (finiteBound_nonneg A a b S) (forwardRadius_nonneg A a b S u₀))
    hb hl (fun n => by rw [hi n])
  refine ⟨u, L, v, hL, hLa, hi, hc, hd, hb, hv, hvc, hvi, ?_, hvl, hw⟩
  exact ⟨forwardRadius A a b S u₀, forwardRadius_nonneg A a b S u₀,
    ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => ⟨v t, rfl, hv t ht⟩)⟩

/-- The actual source smoothed curves are L-infinity elements and possess
an extracted weak-* L1-dual limit. No solution or assumed bound is supplied. -/
theorem source_linfty_weakStar_limit (hab : a ≤ b) (u₀ : FormDomain A) :
    let μ := volume.restrict (Icc a b)
    ∃ (u : ℕ → ℝ → FormDomain A) (w : ℕ → Lp (FormDomain A) ∞ μ)
      (L : Filter ℕ) (Λ : StrongDual ℝ (Lp (FormDomain A) 1 μ)),
      NeBot L ∧ L ≤ atTop ∧
      (∀ n, u n a = u₀) ∧ (∀ n, Continuous (u n)) ∧
      (∀ n, w n =ᵐ[μ] fun t => C ((inclusion A).restrictScalars ℝ) n (u n t)) ∧
      (∀ n, ‖w n‖ ≤ forwardRadius A a b S u₀) ∧
      ‖Λ‖ ≤ forwardRadius A a b S u₀ ∧
      ∀ x : Lp (FormDomain A) 1 μ,
        Tendsto (fun n => ∫ t, (⟪w n t, x t⟫_ℂ).re ∂μ) L (𝓝 (Λ x)) := by
  dsimp only
  let μ := volume.restrict (Icc a b)
  obtain ⟨u, hi, hc, _, _, hb, _⟩ := source_bounded_approximate_sequence A a b S hab u₀
  let i := (inclusion A).restrictScalars ℝ
  have hm (n : ℕ) : MemLp (fun t => C i n (u n t)) ∞ μ :=
    memLp_top_of_bound ((C i n).continuous.comp (hc n)).aestronglyMeasurable
      (forwardRadius A a b S u₀)
      (ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => hb n t ht))
  let w : ℕ → Lp (FormDomain A) ∞ μ := fun n => (hm n).toLp (fun t => C i n (u n t))
  have heq (n : ℕ) : w n =ᵐ[μ] fun t => C i n (u n t) := (hm n).coeFn_toLp
  have hwb (n : ℕ) : ‖w n‖ ≤ forwardRadius A a b S u₀ := by
    have h := Lp.norm_le_of_ae_bound (f := w n) (forwardRadius_nonneg A a b S u₀)
      (by
        filter_upwards [heq n, ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => hb n t ht)] with t ht hbt
        rw [ht]
        exact hbt)
    simpa using h
  obtain ⟨L, hL, hLa, Λ, hΛ, ht⟩ := linfty_weakStar_subfilter μ atTop w
    (forwardRadius A a b S u₀) hwb
  exact ⟨u, w, L, Λ, hL, hLa, hi, hc, heq, hwb, hΛ, ht⟩

/-- The pointwise form candidate and the weak-* L1-dual limit can be
extracted from the SAME actual source sequence on the SAME subfilter. -/
theorem source_common_limit (hab : a ≤ b) (u₀ : FormDomain A) :
    let μ := volume.restrict (Icc a b)
    ∃ (u : ℕ → ℝ → FormDomain A) (v : ℝ → FormDomain A)
      (w : ℕ → Lp (FormDomain A) ∞ μ) (L : Filter ℕ)
      (Λ : StrongDual ℝ (Lp (FormDomain A) 1 μ)),
      NeBot L ∧ L ≤ atTop ∧
      (∀ n, u n a = u₀) ∧ (∀ n, Continuous (u n)) ∧
      (∀ n t, t ∈ Icc a b → HasDerivAt (u n)
        (generator ((inclusion A).restrictScalars ℝ) (epsilon n) (epsilon_pos n)
          (forceMap (formOperator (sourceForm A a b S t))) (u n t)) t) ∧
      (∀ n t, t ∈ Icc a b →
        ‖C ((inclusion A).restrictScalars ℝ) n (u n t)‖ ≤ forwardRadius A a b S u₀) ∧
      (∀ t ∈ Icc a b, ‖v t‖ ≤ forwardRadius A a b S u₀) ∧
      ContinuousOn (fun t => inclusion A (v t)) (Icc a b) ∧ v a = u₀ ∧
      EnergyBounded ((inclusion A).restrictScalars ℝ) (Icc a b) (fun t => inclusion A (v t)) ∧
      (∀ t ∈ Icc a b, ∀ z : FormDomain A,
        Tendsto (fun n => (⟪z, C ((inclusion A).restrictScalars ℝ) n (u n t)⟫_ℂ).re)
          L (𝓝 (⟪z, v t⟫_ℂ).re)) ∧
      (∀ n, w n =ᵐ[μ] fun t => C ((inclusion A).restrictScalars ℝ) n (u n t)) ∧
      (∀ n, ‖w n‖ ≤ forwardRadius A a b S u₀) ∧
      ‖Λ‖ ≤ forwardRadius A a b S u₀ ∧
      ∀ x : Lp (FormDomain A) 1 μ,
        Tendsto (fun n => ∫ t, (⟪w n t, x t⟫_ℂ).re ∂μ) L (𝓝 (Λ x)) := by
  dsimp only
  let μ := volume.restrict (Icc a b)
  obtain ⟨u, L₀, v, hL₀, hLa, hi, hc, hd, hb, hv, hvc, hvi, hve, _, hw⟩ :=
    source_energy_bounded_limit A a b S hab u₀
  let : NeBot L₀ := hL₀
  let i := (inclusion A).restrictScalars ℝ
  have hm (n : ℕ) : MemLp (fun t => C i n (u n t)) ∞ μ :=
    memLp_top_of_bound ((C i n).continuous.comp (hc n)).aestronglyMeasurable
      (forwardRadius A a b S u₀)
      (ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => hb n t ht))
  let w : ℕ → Lp (FormDomain A) ∞ μ := fun n => (hm n).toLp (fun t => C i n (u n t))
  have heq (n : ℕ) : w n =ᵐ[μ] fun t => C i n (u n t) := (hm n).coeFn_toLp
  have hwb (n : ℕ) : ‖w n‖ ≤ forwardRadius A a b S u₀ := by
    have h := Lp.norm_le_of_ae_bound (f := w n) (forwardRadius_nonneg A a b S u₀)
      (by
        filter_upwards [heq n, ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => hb n t ht)] with t ht hbt
        rw [ht]
        exact hbt)
    simpa using h
  obtain ⟨L, hL, hLL₀, Λ, hΛ, ht⟩ := linfty_weakStar_subfilter μ L₀ w
    (forwardRadius A a b S u₀) hwb
  exact ⟨u, v, w, L, Λ, hL, hLL₀.trans hLa, hi, hc, hd, hb, hv, hvc, hvi, hve,
    fun t ht z => (hw t ht z).mono_left hLL₀, heq, hwb, hΛ, ht⟩

end QuantumNLS.Ext005SourceLimitR36b
#print axioms QuantumNLS.Ext005SourceLimitR36b.source_common_limit
#print axioms QuantumNLS.Ext005SourceLimitR36b.source_energy_bounded_limit
#print axioms QuantumNLS.Ext005SourceLimitR36b.source_linfty_weakStar_limit

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005SourceLimitR36b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005SourceLimitR36b." then
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
  Lean.logInfo m!"R36b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."

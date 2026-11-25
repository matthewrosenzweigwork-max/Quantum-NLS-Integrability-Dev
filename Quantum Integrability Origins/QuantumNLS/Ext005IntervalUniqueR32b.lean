import QuantumNLS.Ext005HilbertD3R112

/-! D3 uniqueness on every finite closed interval, with initial data at any
point of that interval. The proved norm chain rule works in both temporal
directions without assuming an energy identity or a reversed evolution. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ContDiff
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory Function
namespace QuantumNLS.Ext005IntervalUniqueR32b
open Ext005HilbertUniqueR112 Ext005HilbertD3R112 Ext005IntervalChainR111
open Ext005HilbertChainR112 Ext005HilbertEnergyR112
variable {Q H : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem coordinate_distance_conserved (i : Q →L[ℝ] H) (hinj : Function.Injective i)
    (hdense : DenseRange i) (a b : ℝ) (hab : a < b)
    (x y : ℝ → H) (u v : ℝ → Q) (K : ℝ → Q →L[ℝ] Q)
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hu : AEStronglyMeasurable u volume) (hv : AEStronglyMeasurable v volume)
    (hK : AEStronglyMeasurable K volume)
    (hlx : ∀ᵐ t, t ∈ Icc a b → i (u t) = x t)
    (hly : ∀ᵐ t, t ∈ Icc a b → i (v t) = y t)
    (E F M : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F) (hM : 0 ≤ M)
    (hb : ∀ᵐ t, t ∈ Icc a b → ‖u t‖ ≤ E ∧ ‖v t‖ ≤ F ∧ ‖K t‖ ≤ M)
    (hskew : ∀ᵐ t, t ∈ Icc a b → ∀ w : Q, ⟪w, K t w⟫_ℝ = 0)
    (hwx : WeakDerivativeOn (Ioo a b) (fun t => i.adjoint (x t)) (fun t => K t (u t)))
    (hwy : WeakDerivativeOn (Ioo a b) (fun t => i.adjoint (y t)) (fun t => K t (v t)))
    : ‖x b - y b‖ ^ 2 = ‖x a - y a‖ ^ 2 := by
  have hforce (w : ℝ → Q) (hw : AEStronglyMeasurable w volume) (A : ℝ) (_hA : 0 ≤ A)
      (hbw : ∀ᵐ t, t ∈ Icc a b → ‖w t‖ ≤ A) : IntegrableOn (fun t => K t (w t)) (Icc a b) := by
    apply bounded_integrable a b _ (coefficient_measurable K w hK hw) (M * A)
    filter_upwards [hb, hbw] with t ht ht' htI
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (ht htI).2.2 (ht' htI) (norm_nonneg _) hM)
  have hwd := weak_sub_on a b _ _ _ _
    ((i.adjoint.continuous.comp_continuousOn hx).integrableOn_compact isCompact_Icc)
    ((i.adjoint.continuous.comp_continuousOn hy).integrableOn_compact isCompact_Icc)
    (hforce u hu E hE (hb.mono fun t ht htI => (ht htI).1))
    (hforce v hv F hF (hb.mono fun t ht htI => (ht htI).2.1)) hwx hwy
  have he := norm_sq_conserved_on i hinj hdense a b hab
    (fun t => x t - y t) (fun t => u t - v t) (fun t => K t (u t - v t))
    (hx.sub hy) (hu.sub hv) (coefficient_measurable K _ hK (hu.sub hv))
    (by
      filter_upwards [hlx, hly] with t ht ht' htI
      rw [map_sub, ht htI, ht' htI])
    (E + F) (M * (E + F)) (add_nonneg hE hF) (mul_nonneg hM (add_nonneg hE hF))
    (by
      filter_upwards [hb] with t ht htI
      have hw := (norm_sub_le (u t) (v t)).trans (add_le_add (ht htI).1 (ht htI).2.1)
      exact ⟨hw, (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (ht htI).2.2 hw (norm_nonneg _) hM)⟩)
    (hskew.mono fun t ht htI => ht htI (u t - v t))
    (by simpa only [map_sub, Function.comp_apply] using hwd)
  exact he

omit [CompleteSpace Q] [CompleteSpace H] in
/-- Essential energy bounds restrict to any smaller measurable interval. -/
lemma energy_mono (i : Q →L[ℝ] H) {U V : Set ℝ} {x : ℝ → H}
    (h : EnergyBounded i U x) (hVU : V ⊆ U) : EnergyBounded i V x := by
  obtain ⟨E, hE, he⟩ := h
  exact ⟨E, hE, he.filter_mono (ae_mono (Measure.restrict_mono_set volume hVU))⟩

/-- Distance conservation in native D3 coordinates on an arbitrary interval. -/
theorem energy_distance_conserved_on (i : Q →L[ℝ] H) (hinj : Function.Injective i)
    (hdense : DenseRange i) (a b : ℝ) (hab : a < b)
    (x y : ℝ → H) (K : ℝ → Q →L[ℝ] Q)
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hex : EnergyBounded i (Icc a b) x) (hey : EnergyBounded i (Icc a b) y)
    (hK : AEStronglyMeasurable K (volume.restrict (Icc a b)))
    (hKb : ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ t, t ∈ Icc a b → ‖K t‖ ≤ M)
    (hskew : ∀ᵐ t, t ∈ Icc a b → ∀ w : Q, ⟪w, K t w⟫_ℝ = 0)
    (hwx : WeakDerivativeOn (Ioo a b) (fun t => i.adjoint (x t))
      (fun t => K t (lift i (x t))))
    (hwy : WeakDerivativeOn (Ioo a b) (fun t => i.adjoint (y t))
      (fun t => K t (lift i (y t)))) :
    ‖x b - y b‖ ^ 2 = ‖x a - y a‖ ^ 2 := by
  let u := (Icc a b).indicator (fun t => lift i (x t))
  let v := (Icc a b).indicator (fun t => lift i (y t))
  let K' := (Icc a b).indicator K
  obtain ⟨hu, E, hE, hbu⟩ := energy_coordinates i hinj (Icc a b) measurableSet_Icc x
    (hx.aestronglyMeasurable measurableSet_Icc) hex
  obtain ⟨hv, F, hF, hbv⟩ := energy_coordinates i hinj (Icc a b) measurableSet_Icc y
    (hy.aestronglyMeasurable measurableSet_Icc) hey
  have hK' : AEStronglyMeasurable K' volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Icc).mpr hK
  obtain ⟨M, hM, hbm⟩ := hKb
  have hwe (z : ℝ → H)
      (hz : WeakDerivativeOn (Ioo a b) (fun t => i.adjoint (z t))
        (fun t => K t (lift i (z t)))) :
      WeakDerivativeOn (Ioo a b) (fun t => i.adjoint (z t))
        (fun t => K' t ((Icc a b).indicator (fun s => lift i (z s)) t)) := by
    apply weak_congr hz (fun _ _ => rfl)
    intro t ht
    simp only [K', indicator_of_mem (Ioo_subset_Icc_self ht)]
  apply coordinate_distance_conserved i hinj hdense a b hab x y u v K'
    hx hy hu hv hK'
    (hbu.mono fun s hs hsI => (hs hsI).1)
    (hbv.mono fun s hs hsI => (hs hsI).1) E F M hE hF hM
  · filter_upwards [hbu, hbv, hbm] with s hs hs' hsM hsI
    exact ⟨(hs hsI).2, (hs' hsI).2,
      by simpa only [K', indicator_of_mem hsI] using hsM hsI⟩
  · filter_upwards [hskew] with s hs hsI
    simpa only [K', indicator_of_mem hsI] using hs hsI
  · exact hwe x hwx
  · exact hwe y hwy

/-- One uniqueness theorem for positive and negative finite time intervals,
including both endpoints and data posed at any intermediate time. -/
theorem energy_unique_at_on (i : Q →L[ℝ] H) (hinj : Function.Injective i)
    (hdense : DenseRange i) (a b s : ℝ) (hab : a < b) (hs : s ∈ Icc a b)
    (x y : ℝ → H) (K : ℝ → Q →L[ℝ] Q)
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hex : EnergyBounded i (Icc a b) x) (hey : EnergyBounded i (Icc a b) y)
    (hK : AEStronglyMeasurable K (volume.restrict (Icc a b)))
    (hKb : ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ t, t ∈ Icc a b → ‖K t‖ ≤ M)
    (hskew : ∀ᵐ t, t ∈ Icc a b → ∀ w : Q, ⟪w, K t w⟫_ℝ = 0)
    (hwx : WeakDerivativeOn (Ioo a b) (fun t => i.adjoint (x t))
      (fun t => K t (lift i (x t))))
    (hwy : WeakDerivativeOn (Ioo a b) (fun t => i.adjoint (y t))
      (fun t => K t (lift i (y t))))
    (hinit : x s = y s) : ∀ t ∈ Icc a b, x t = y t := by
  have ha : x a = y a := by
    rcases eq_or_lt_of_le hs.1 with heq | has
    · simpa only [← heq] using hinit
    have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc_right hs.2
    have hws : Ioo a s ⊆ Ioo a b := fun t ht => ⟨ht.1, ht.2.trans_le hs.2⟩
    have he := energy_distance_conserved_on i hinj hdense a s has x y K
      (hx.mono hsub) (hy.mono hsub) (energy_mono i hex hsub) (energy_mono i hey hsub)
      (hK.mono_measure (Measure.restrict_mono_set volume hsub))
      (by
        obtain ⟨M, hM, hbM⟩ := hKb
        exact ⟨M, hM, hbM.mono fun t ht htI => ht (hsub htI)⟩)
      (hskew.mono fun t ht htI => ht (hsub htI))
      (weak_mono hwx hws) (weak_mono hwy hws)
    rw [hinit, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at he
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp he.symm))
  exact energy_unique_on i hinj hdense a b hab x y K hx hy hex hey hK hKb hskew hwx hwy ha

end QuantumNLS.Ext005IntervalUniqueR32b
#print axioms QuantumNLS.Ext005IntervalUniqueR32b.energy_unique_at_on

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005IntervalUniqueR32b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005IntervalUniqueR32b." then
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
  Lean.logInfo m!"R32b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."

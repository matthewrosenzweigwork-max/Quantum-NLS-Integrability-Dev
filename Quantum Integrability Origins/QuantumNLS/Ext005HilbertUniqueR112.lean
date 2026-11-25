import QuantumNLS.Ext005HilbertChainR112
import QuantumNLS.Ext005HilbertEnergyR112

/-! R112: two-solution D3 uniqueness for arbitrary Hilbert form domains.
Norm continuity and native essential form bounds supply all competitor
coordinates; the energy identity and difference equation are proved. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open scoped InnerProductSpace Topology ContDiff
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory Function
namespace QuantumNLS.Ext005HilbertUniqueR112
open Ext005GramResolventR112 Ext005GramConvergenceR112 Ext005IntervalChainR111
open Ext005HilbertChainR112 Ext005HilbertEnergyR112
variable {Q H : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace Q] in
lemma weak_mono {U V : Set ℝ} {f g : ℝ → Q}
    (hw : WeakDerivativeOn U f g) (hVU : V ⊆ U) : WeakDerivativeOn V f g := by
  intro v p hp hc hs
  exact hw v p hp hc (hs.trans hVU)

omit [CompleteSpace Q] in
lemma test_integrable (a b : ℝ) (f : ℝ → Q)
    (hf : IntegrableOn f (Icc a b)) (z : Q) (p : ℝ → ℝ)
    (hp : Continuous p) (hc : HasCompactSupport p) (hs : support p ⊆ Icc a b) :
    Integrable (fun t => p t * ⟪z, f t⟫_ℝ) volume := by
  let G := (Icc a b).indicator f
  have hG : Integrable G volume := hf.integrable_indicator measurableSet_Icc
  have hi : Integrable (fun t => p t * ⟪z, G t⟫_ℝ) volume :=
    (Ext005CutoffChainR110.locallyIntegrable_map (innerSL ℝ z) hG.locallyIntegrable).integrable_smul_left_of_hasCompactSupport hp hc
  apply hi.congr
  filter_upwards [] with t
  by_cases ht : t ∈ Icc a b
  · rw [show G t = f t from indicator_of_mem ht f]
  · have hp0 : p t = 0 := by by_contra h; exact ht (hs h)
    simp only [hp0, zero_mul]

omit [CompleteSpace Q] in
lemma coefficient_measurable (K : ℝ → Q →L[ℝ] Q) (u : ℝ → Q)
    (hK : AEStronglyMeasurable K volume) (hu : AEStronglyMeasurable u volume) :
    AEStronglyMeasurable (fun t => K t (u t)) volume := by
  have hc : Continuous (fun p : (Q →L[ℝ] Q) × Q => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  exact hc.comp_aestronglyMeasurable (hK.prodMk hu)

/-- Native essential form bounds and the original local equation give
conservation at the endpoints. Coefficients are local measurable data. -/
theorem energy_norm_conserved_on (i : Q →L[ℝ] H) (hinj : Function.Injective i)
    (hdense : DenseRange i) (a b : ℝ) (hab : a < b)
    (x : ℝ → H) (K : ℝ → Q →L[ℝ] Q)
    (hx : ContinuousOn x (Icc a b)) (he : EnergyBounded i (Icc a b) x)
    (hK : AEStronglyMeasurable K (volume.restrict (Icc a b)))
    (hKb : ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ t, t ∈ Icc a b → ‖K t‖ ≤ M)
    (hskew : ∀ᵐ t, t ∈ Icc a b → ∀ w : Q, ⟪w, K t w⟫_ℝ = 0)
    (hw : WeakDerivativeOn (Ioo a b) (fun t => i.adjoint (x t))
      (fun t => K t (lift i (x t)))) : ‖x b‖ ^ 2 = ‖x a‖ ^ 2 := by
  let u := (Icc a b).indicator (fun t => lift i (x t))
  let K' := (Icc a b).indicator K
  obtain ⟨hu, E, hE, hbu⟩ := energy_coordinates i hinj (Icc a b) measurableSet_Icc x
    (hx.aestronglyMeasurable measurableSet_Icc) he
  obtain ⟨M, hM, hbm⟩ := hKb
  have hK' : AEStronglyMeasurable K' volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Icc).mpr hK
  have hwe : WeakDerivativeOn (Ioo a b) (fun t => i.adjoint (x t))
      (fun t => K' t (u t)) := by
    apply weak_congr hw (fun _ _ => rfl)
    intro t ht
    simp only [K', u, indicator_of_mem (Ioo_subset_Icc_self ht)]
  apply norm_sq_conserved_on i hinj hdense a b hab x u (fun t => K' t (u t)) hx
    hu (coefficient_measurable K' u hK' hu)
    (hbu.mono fun t ht htI => (ht htI).1) E (M * E) hE (mul_nonneg hM hE)
  · filter_upwards [hbu, hbm] with t ht ht' htI
    refine ⟨(ht htI).2, ?_⟩
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    apply mul_le_mul _ (ht htI).2 (norm_nonneg _) hM
    simpa only [K', indicator_of_mem htI] using ht' htI
  · filter_upwards [hskew] with t ht htI
    simpa only [K', indicator_of_mem htI] using ht htI (u t)
  · exact hwe

omit [CompleteSpace Q] in
/-- Weak difference equations are derived using integrability of all test
pairings, including the nonconstant form coordinates. -/
lemma weak_sub_on (a b : ℝ) (f h g k : ℝ → Q)
    (hfi : IntegrableOn f (Icc a b)) (hhi : IntegrableOn h (Icc a b))
    (hgi : IntegrableOn g (Icc a b)) (hki : IntegrableOn k (Icc a b))
    (hf : WeakDerivativeOn (Ioo a b) f g) (hh : WeakDerivativeOn (Ioo a b) h k) :
    WeakDerivativeOn (Ioo a b) (fun t => f t - h t) (fun t => g t - k t) := by
  intro z p hp hc hs
  have hdp : support (deriv p) ⊆ Icc a b :=
    support_deriv_subset.trans (hs.trans Ioo_subset_Icc_self)
  have hpp : support p ⊆ Icc a b := subset_closure.trans (hs.trans Ioo_subset_Icc_self)
  have hi1 := test_integrable a b f hfi z (deriv p)
    (hp.continuous_deriv (by exact_mod_cast le_top)) hc.deriv hdp
  have hi2 := test_integrable a b h hhi z (deriv p)
    (hp.continuous_deriv (by exact_mod_cast le_top)) hc.deriv hdp
  have hi3 := test_integrable a b g hgi z p hp.continuous hc hpp
  have hi4 := test_integrable a b k hki z p hp.continuous hc hpp
  simp only [inner_sub_right, mul_sub]
  rw [integral_sub hi1 hi2, integral_sub hi3 hi4, hf z p hp hc hs, hh z p hp hc hs]
  ring

/-- Equality of endpoints, with measurable form coordinates extracted later
from the native D3 class. -/
theorem coordinate_equal_endpoints (i : Q →L[ℝ] H) (hinj : Function.Injective i)
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
    (hinit : x a = y a) : x b = y b := by
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
  rw [hinit, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at he
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp he))

end QuantumNLS.Ext005HilbertUniqueR112
#print axioms QuantumNLS.Ext005HilbertUniqueR112.energy_norm_conserved_on
#print axioms QuantumNLS.Ext005HilbertUniqueR112.coordinate_equal_endpoints

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005HilbertUniqueR112." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005HilbertUniqueR112." then
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
  Lean.logInfo m!"R112 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."

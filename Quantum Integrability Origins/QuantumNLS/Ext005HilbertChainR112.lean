import QuantumNLS.Ext005GramConvergenceR112

/-! R112: the norm chain rule on an arbitrary Hilbert form/antidual scale.
The real Riesz coordinate of the antidual derivative is g. The only diagonal
hypothesis is the vanishing real pairing supplied by a symmetric Schrodinger
form. No energy identity, absolute continuity or uniqueness is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open scoped InnerProductSpace Topology ContDiff
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005HilbertChainR112
open Ext005GramResolventR112 Ext005GramConvergenceR112 Ext005IntervalChainR111
variable {Q H : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Mapping between different Hilbert spaces preserves the tested equation. -/
lemma weak_map_between (T : Q →L[ℝ] H) {U : Set ℝ} {f g : ℝ → Q}
    (hw : WeakDerivativeOn U f g) :
    WeakDerivativeOn U (fun t => T (f t)) (fun t => T (g t)) := by
  intro v p hp hc hs
  simpa only [ContinuousLinearMap.adjoint_inner_left] using hw (T.adjoint v) p hp hc hs

omit [InnerProductSpace ℝ Q] [CompleteSpace Q] in
lemma bounded_integrable (a b : ℝ) (g : ℝ → Q)
    (hg : AEStronglyMeasurable g volume) (D : ℝ)
    (hb : ∀ᵐ t, t ∈ Icc a b → ‖g t‖ ≤ D) : IntegrableOn g (Icc a b) := by
  have : IsFiniteMeasure (volume.restrict (Icc a b)) := ⟨by simp⟩
  exact ⟨hg.restrict, HasFiniteIntegral.of_bounded ((ae_restrict_iff' measurableSet_Icc).mpr hb)⟩

/-- General form-domain norm conservation, derived by the constructed Gram
regularizers. The form space can differ from the ambient Hilbert space. -/
theorem norm_sq_conserved_on (i : Q →L[ℝ] H) (hinj : Function.Injective i)
    (hdense : DenseRange i) (a b : ℝ) (hab : a < b)
    (x : ℝ → H) (u g : ℝ → Q)
    (hx : ContinuousOn x (Icc a b))
    (hu : AEStronglyMeasurable u volume) (hg : AEStronglyMeasurable g volume)
    (hlift : ∀ᵐ t, t ∈ Icc a b → i (u t) = x t)
    (E D : ℝ) (_hE : 0 ≤ E) (hD : 0 ≤ D)
    (hb : ∀ᵐ t, t ∈ Icc a b → ‖u t‖ ≤ E ∧ ‖g t‖ ≤ D)
    (hdiag : ∀ᵐ t, t ∈ Icc a b → ⟪u t, g t⟫_ℝ = 0)
    (hw : WeakDerivativeOn (Ioo a b) (fun t => i.adjoint (x t)) g) :
    ‖x b‖ ^ 2 = ‖x a‖ ^ 2 := by
  have hgi := bounded_integrable a b g hg D (hb.mono fun t ht htI => (ht htI).2)
  have hid (n : ℕ) : ‖P i n (x b)‖ ^ 2 - ‖P i n (x a)‖ ^ 2 =
      ∫ t in a..b, 2 * ⟪C i n (C i n (u t)), g t⟫_ℝ := by
    have hbR : ∀ᵐ t, t ∈ Icc a b → ‖R i n (g t)‖ ≤ ‖R i n‖ * D := by
      filter_upwards [hb] with t ht htI
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (ht htI).2 (norm_nonneg _))
    have h := weak_norm_sq_identity_on a b hab (fun t => P i n (x t)) (fun t => R i n (g t))
      ((P i n).continuous.comp_continuousOn hx) ((R i n).integrable_comp hgi)
      (weak_map_between (R i n) hw) ⟨‖R i n‖ * D, mul_nonneg (norm_nonneg _) hD⟩ hbR
    rw [h]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hlift] with t ht htI
    rw [uIoc_of_le hab.le] at htI
    rw [← ht (Ioc_subset_Icc_self htI)]
    exact congrArg (2 * ·) (pairing_identity i (epsilon n) (epsilon_pos n) (u t) (g t))
  let μ := volume.restrict (Ioc a b)
  have : IsFiniteMeasure μ := ⟨by simp [μ]⟩
  have hbμ : ∀ᵐ t ∂μ, ‖u t‖ ≤ E ∧ ‖g t‖ ≤ D := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [hb] with t ht htI
    exact ht (Ioc_subset_Icc_self htI)
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun t => 2 * ⟪C i n (C i n (u t)), g t⟫_ℝ) μ := by
    exact aestronglyMeasurable_const.mul
      (((C i n).continuous.comp_aestronglyMeasurable
        ((C i n).continuous.comp_aestronglyMeasurable hu.restrict)).inner hg.restrict)
  have hd (n : ℕ) : ∀ᵐ t ∂μ,
      ‖2 * ⟪C i n (C i n (u t)), g t⟫_ℝ‖ ≤ 2 * E * D := by
    filter_upwards [hbμ] with t ht
    have hc : ‖C i n (C i n (u t))‖ ≤ E :=
      (cutoff_norm_le i _ _ _).trans ((cutoff_norm_le i _ _ _).trans ht.1)
    calc
      _ = 2 * ‖⟪C i n (C i n (u t)), g t⟫_ℝ‖ := by rw [norm_mul]; norm_num
      _ ≤ 2 * (‖C i n (C i n (u t))‖ * ‖g t‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℝ) _ _) (by norm_num)
      _ ≤ 2 * (E * D) := mul_le_mul_of_nonneg_left
        (mul_le_mul hc ht.2 (norm_nonneg _) _hE) (by norm_num)
      _ = _ := by ring
  have hz : ∀ᵐ t ∂μ, ⟪u t, g t⟫_ℝ = 0 := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [hdiag] with t ht htI
    exact ht (Ioc_subset_Icc_self htI)
  have hl : ∀ᵐ t ∂μ, Tendsto (fun n => 2 * ⟪C i n (C i n (u t)), g t⟫_ℝ)
      atTop (𝓝 0) := by
    filter_upwards [hz] with t ht
    have h := (tendsto_const_nhds (x := (2 : ℝ))).mul
      ((CC_tendsto i hinj (u t)).inner (𝕜 := ℝ) (tendsto_const_nhds (x := g t)))
    simpa only [ht, mul_zero] using h
  have hi := tendsto_integral_of_dominated_convergence (fun _ : ℝ => 2 * E * D)
    hm (integrable_const _) hd hl
  simp only [integral_zero] at hi
  have he : (fun n => ∫ t, 2 * ⟪C i n (C i n (u t)), g t⟫_ℝ ∂μ) =
      (fun n => ‖P i n (x b)‖ ^ 2 - ‖P i n (x a)‖ ^ 2) := by
    funext n
    exact (intervalIntegral.integral_of_le hab.le).symm.trans (hid n).symm
  rw [he] at hi
  have hn := ((P_tendsto i hinj hdense (x b)).norm.pow 2).sub
    ((P_tendsto i hinj hdense (x a)).norm.pow 2)
  exact sub_eq_zero.mp (tendsto_nhds_unique hn hi)

end QuantumNLS.Ext005HilbertChainR112
#print axioms QuantumNLS.Ext005HilbertChainR112.norm_sq_conserved_on

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005HilbertChainR112." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005HilbertChainR112." then
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

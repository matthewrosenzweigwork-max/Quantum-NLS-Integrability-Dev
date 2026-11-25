import QuantumNLS.Ext005IntervalPrimitiveR111

/-! Finite-interval weak-to-integral and chain rules. Curves need only be
continuous on the closed interval, and forcing integrable there. Time tests
have compact support in its interior. Endpoint equalities are conclusions. -/
noncomputable section
set_option autoImplicit false
open scoped Topology ContDiff InnerProductSpace
open MeasureTheory Set Filter Function
namespace QuantumNLS.Ext005IntervalChainR111
open Ext005IntervalPrimitiveR111 Ext005WeakPrimitiveR110 Ext005CutoffChainR110
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The distributional equation uses only time tests inside U. Values of
f and g outside U do not enter this condition. -/
def WeakDerivativeOn (U : Set ℝ) (f g : ℝ → E) : Prop :=
  ∀ (v : E) (p : ℝ → ℝ), ContDiff ℝ ∞ p → HasCompactSupport p → tsupport p ⊆ U →
    ∫ t, deriv p t * ⟪v, f t⟫_ℝ = -(∫ t, p t * ⟪v, g t⟫_ℝ)

omit [CompleteSpace E] in
/-- Changing representatives outside the test domain preserves the equation. -/
theorem weak_congr {U : Set ℝ} {f g f' g' : ℝ → E}
    (hw : WeakDerivativeOn U f g) (hf : EqOn f' f U) (hg : EqOn g' g U) :
    WeakDerivativeOn U f' g' := by
  intro v p hp hc hs
  have hl : (fun t => deriv p t * ⟪v, f' t⟫_ℝ) = fun t => deriv p t * ⟪v, f t⟫_ℝ := by
    funext t
    by_cases ht : t ∈ U
    · rw [hf ht]
    · rw [deriv_of_notMem_tsupport (fun h => ht (hs h)), zero_mul, zero_mul]
  have hr : (fun t => p t * ⟪v, g' t⟫_ℝ) = fun t => p t * ⟪v, g t⟫_ℝ := by
    funext t
    by_cases ht : t ∈ U
    · rw [hg ht]
    · have hp0 : p t = 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h => ht (hs h)) |>.self_of_nhds
      rw [hp0, zero_mul, zero_mul]
  rw [hl, hr]
  exact hw v p hp hc hs

private theorem scalar_local_integral (a b : ℝ) (hab : a < b) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : LocallyIntegrable g)
    (hw : ∀ p : ℝ → ℝ, ContDiff ℝ ∞ p → HasCompactSupport p →
      tsupport p ⊆ Ioo a b → ∫ t, deriv p t * f t = -(∫ t, p t * g t))
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    f t - f s = ∫ v in s..t, g v := by
  let P := fun t => ∫ v in 0..t, g v
  have hP : Continuous P := intervalIntegral.continuous_primitive
    (locallyIntegrable_interval hg) 0
  have hwz (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hc : HasCompactSupport p)
      (hsp : tsupport p ⊆ Ioo a b) : ∫ t, deriv p t • (f t - P t) = 0 := by
    have hfli : LocallyIntegrable f volume := hf.locallyIntegrable
    have hPli : LocallyIntegrable P volume := hP.locallyIntegrable
    have hi1 := hfli.integrable_smul_left_of_hasCompactSupport
      (hp.continuous_deriv (by exact_mod_cast le_top)) hc.deriv
    have hi2 := hPli.integrable_smul_left_of_hasCompactSupport
      (hp.continuous_deriv (by exact_mod_cast le_top)) hc.deriv
    simp only [smul_sub]
    rw [integral_sub hi1 hi2]
    simp only [smul_eq_mul]
    rw [hw p hp hc hsp, primitive_weak_form g hg p hp hc, sub_self]
  obtain ⟨c, he⟩ := constant_on_Ioo a b hab (fun t => f t - P t) (hf.sub hP) hwz
  have hec := he.closure (hf.sub hP) continuous_const
  rw [closure_Ioo hab.ne] at hec
  have hpi : P t - P s = ∫ v in s..t, g v :=
    intervalIntegral.integral_interval_sub_left (locallyIntegrable_interval hg 0 t)
      (locallyIntegrable_interval hg 0 s)
  linarith [hec hs, hec ht]

private theorem vector_local_integral (a b : ℝ) (hab : a < b) (f g : ℝ → E)
    (hf : Continuous f) (hg : LocallyIntegrable g) (hw : WeakDerivativeOn (Ioo a b) f g)
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    f t - f s = ∫ v in s..t, g v := by
  apply ext_inner_left ℝ
  intro v
  have h := scalar_local_integral a b hab (fun t => ⟪v, f t⟫_ℝ) (fun t => ⟪v, g t⟫_ℝ)
    ((innerSL ℝ v).continuous.comp hf) (locallyIntegrable_map (innerSL ℝ v) hg)
    (hw v) s t hs ht
  have hm := (innerSL ℝ v).intervalIntegral_comp_comm (locallyIntegrable_interval hg s t)
  simp only [innerSL_apply_apply] at hm
  rw [hm] at h
  simpa only [inner_sub_right] using h

/-- A continuous extension is constructed from the interval curve by clamping
its time argument. This imposes no hypothesis outside the source interval. -/
def extend (a b : ℝ) (f : ℝ → E) (t : ℝ) : E := f (max a (min b t))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma extend_eq (a b : ℝ) (f : ℝ → E) {t : ℝ} (ht : t ∈ Icc a b) :
    extend a b f t = f t := by simp [extend, min_eq_right ht.2, max_eq_right ht.1]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma continuous_extend (a b : ℝ) (hab : a ≤ b) (f : ℝ → E)
    (hf : ContinuousOn f (Icc a b)) : Continuous (extend a b f) := by
  apply hf.comp_continuous (continuous_const.max (continuous_const.min continuous_id))
  intro t
  exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

/-- Finite-interval integral equation, including both endpoints, derived
from interior compact tests and continuity only on the interval. -/
theorem weak_to_integral_on (a b : ℝ) (hab : a < b) (f g : ℝ → E)
    (hf : ContinuousOn f (Icc a b)) (hg : IntegrableOn g (Icc a b))
    (hw : WeakDerivativeOn (Ioo a b) f g)
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    f t - f s = ∫ v in s..t, g v := by
  let F := extend a b f
  let G := (Icc a b).indicator g
  have hF := continuous_extend a b hab.le f hf
  have hG : Integrable G volume := hg.integrable_indicator measurableSet_Icc
  have hwe : WeakDerivativeOn (Ioo a b) F G := by
    apply weak_congr hw
    · intro t ht; exact extend_eq a b f (Ioo_subset_Icc_self ht)
    · intro t ht; exact indicator_of_mem (Ioo_subset_Icc_self ht) g
  have hh := vector_local_integral a b hab F G hF hG.locallyIntegrable hwe s t hs ht
  dsimp only [F] at hh
  rw [extend_eq a b f hs, extend_eq a b f ht] at hh
  rw [hh]
  apply intervalIntegral.integral_congr
  intro v hv
  exact indicator_of_mem ((uIcc_subset_Icc hs ht) hv) g

/-- Essential bounds give a Lipschitz estimate on the original interval. -/
theorem weak_lipschitz_on (a b : ℝ) (hab : a < b) (f g : ℝ → E)
    (hf : ContinuousOn f (Icc a b)) (hg : IntegrableOn g (Icc a b))
    (hw : WeakDerivativeOn (Ioo a b) f g) (M : NNReal)
    (hb : ∀ᵐ t, t ∈ Icc a b → ‖g t‖ ≤ M) : LipschitzOnWith M f (Icc a b) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro s hs t ht
  rw [dist_eq_norm, weak_to_integral_on a b hab f g hf hg hw t s ht hs, Real.dist_eq]
  apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
  filter_upwards [hb] with v hv hvst
  exact hv ((uIcc_subset_Icc ht hs) (uIoc_subset_uIcc hvst))

/-- The a.e. derivative is obtained on the interval interior. -/
theorem weak_ae_hasDerivAt_on (a b : ℝ) (hab : a < b) (f g : ℝ → E)
    (hf : ContinuousOn f (Icc a b)) (hg : IntegrableOn g (Icc a b))
    (hw : WeakDerivativeOn (Ioo a b) f g) :
    ∀ᵐ t, t ∈ Ioo a b → HasDerivAt f (g t) t := by
  let G := (Icc a b).indicator g
  have hG : LocallyIntegrable G volume := (hg.integrable_indicator measurableSet_Icc).locallyIntegrable
  have he (t : ℝ) (ht : t ∈ Icc a b) : f t = (∫ v in a..t, G v) + f a := by
    have h := weak_to_integral_on a b hab f g hf hg hw a t (left_mem_Icc.mpr hab.le) ht
    have hi : (∫ v in a..t, G v) = ∫ v in a..t, g v := by
      apply intervalIntegral.integral_congr
      intro v hv
      exact indicator_of_mem ((uIcc_subset_Icc (left_mem_Icc.mpr hab.le) ht) hv) g
    rw [hi]
    exact sub_eq_iff_eq_add.mp h
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hG] with t ht htI
  have hd := (ht a).add_const (f a)
  have hne : f =ᶠ[𝓝 t] (fun s => (∫ v in a..s, G v) + f a) := by
    filter_upwards [isOpen_Ioo.mem_nhds htI] with s hs
    exact he s (Ioo_subset_Icc_self hs)
  have hgt : G t = g t := indicator_of_mem (Ioo_subset_Icc_self htI) g
  rw [hgt] at hd
  exact hd.congr_of_eventuallyEq hne

/-- The interval squared-norm chain rule is proved from the weak equation,
not added as a hypothesis. No global-time equation is required. -/
theorem weak_norm_sq_identity_on (a b : ℝ) (hab : a < b) (f g : ℝ → E)
    (hf : ContinuousOn f (Icc a b)) (hg : IntegrableOn g (Icc a b))
    (hw : WeakDerivativeOn (Ioo a b) f g) (M : NNReal)
    (hb : ∀ᵐ t, t ∈ Icc a b → ‖g t‖ ≤ M) :
    ‖f b‖ ^ 2 - ‖f a‖ ^ 2 = ∫ t in a..b, 2 * ⟪f t, g t⟫_ℝ := by
  have hl : LipschitzOnWith M f (uIcc a b) := by
    simpa only [uIcc_of_le hab.le] using weak_lipschitz_on a b hab f g hf hg hw M hb
  have hfac := hl.absolutelyContinuousOnInterval
  have hn : AbsolutelyContinuousOnInterval (fun t => ‖f t‖) a b :=
    lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hfac
  have hac : AbsolutelyContinuousOnInterval (fun t => ‖f t‖ ^ 2) a b := by
    simpa only [pow_two] using hn.fun_mul hn
  rw [← hac.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  have hnb : ∀ᵐ t : ℝ, t ≠ b := volume.ae_ne b
  filter_upwards [weak_ae_hasDerivAt_on a b hab f g hf hg hw, hnb] with t ht htb htI
  rw [uIoc_of_le hab.le] at htI
  exact (ht ⟨htI.1, lt_of_le_of_ne htI.2 htb⟩).norm_sq.deriv

/-- A bounded spatial map preserves the interval distributional equation. -/
theorem weak_map_on (T : E →L[ℝ] E) {U : Set ℝ} {f g : ℝ → E}
    (hw : WeakDerivativeOn U f g) :
    WeakDerivativeOn U (fun t => T (f t)) (fun t => T (g t)) := by
  intro v p hp hc hs
  simpa only [ContinuousLinearMap.adjoint_inner_left] using hw (T.adjoint v) p hp hc hs

end QuantumNLS.Ext005IntervalChainR111

#print axioms QuantumNLS.Ext005IntervalChainR111.weak_to_integral_on
#print axioms QuantumNLS.Ext005IntervalChainR111.weak_norm_sq_identity_on

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005IntervalChainR111." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005IntervalChainR111." then
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
  Lean.logInfo m!"R111 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."

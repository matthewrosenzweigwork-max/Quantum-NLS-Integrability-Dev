import QuantumNLS.Ext005WeakPrimitiveR110
import QuantumNLS.Ext005FormCutoffR109
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! R110: a Hilbert-valued distributional chain rule. Smooth scalar time
tests and fixed Hilbert test vectors are the only equation premises.
Local boundedness of the forcing yields absolute continuity of the norm
squared; no norm identity or weak-to-integral equivalence is assumed. -/
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace Topology ContDiff
open MeasureTheory Set Filter Function
namespace QuantumNLS.Ext005CutoffChainR110
open Ext005WeakPrimitiveR110
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The literal distributional equation f'=g, tested against fixed vectors
and smooth compactly supported scalar functions. -/
def WeakDerivative (f g : ℝ → E) : Prop :=
  ∀ (v : E) (p : ℝ → ℝ), ContDiff ℝ ∞ p → HasCompactSupport p →
    ∫ t, deriv p t * ⟪v, f t⟫_ℝ = -(∫ t, p t * ⟪v, g t⟫_ℝ)

omit [CompleteSpace E] in
lemma locallyIntegrable_map {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) {g : ℝ → E} (hg : LocallyIntegrable g) :
    LocallyIntegrable (fun t => T (g t)) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact T.integrable_comp (hg.integrableOn_isCompact hK)

/-- The vector integral equation follows by scalarization and separation
by the Hilbert inner product. -/
theorem weak_to_vector_integral (f g : ℝ → E) (hf : Continuous f)
    (hg : LocallyIntegrable g) (hw : WeakDerivative f g) (s t : ℝ) :
    f t - f s = ∫ v in s..t, g v := by
  apply ext_inner_left ℝ
  intro v
  have h := weak_to_integral (fun t => ⟪v, f t⟫_ℝ) (fun t => ⟪v, g t⟫_ℝ)
    ((innerSL ℝ v).continuous.comp hf) (locallyIntegrable_map (innerSL ℝ v) hg)
    (hw v) s t
  have hm := (innerSL ℝ v).intervalIntegral_comp_comm (locallyIntegrable_interval hg s t)
  simp only [innerSL_apply_apply] at hm
  rw [hm] at h
  simpa only [inner_sub_right] using h

/-- The a.e. strong derivative is a conclusion of the weak equation. -/
theorem weak_ae_hasDerivAt (f g : ℝ → E) (hf : Continuous f)
    (hg : LocallyIntegrable g) (hw : WeakDerivative f g) :
    ∀ᵐ t, HasDerivAt f (g t) t := by
  have he : f = fun t => (∫ v in 0..t, g v) + f 0 := by
    funext t
    exact sub_eq_iff_eq_add.mp (weak_to_vector_integral f g hf hg hw 0 t)
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hg] with t ht
  rw [he]
  exact (ht 0).add_const (f 0)

/-- A local essential bound on the forcing gives a proved local Lipschitz
bound, with the same constant. -/
theorem weak_lipschitz (f g : ℝ → E) (hf : Continuous f)
    (hg : LocallyIntegrable g) (hw : WeakDerivative f g) (a b : ℝ) (M : NNReal)
    (hb : ∀ᵐ t, t ∈ uIcc a b → ‖g t‖ ≤ M) :
    LipschitzOnWith M f (uIcc a b) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro s hs t ht
  rw [dist_eq_norm, weak_to_vector_integral f g hf hg hw t s, Real.dist_eq]
  apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
  filter_upwards [hb] with v hv hvst
  exact hv ((uIcc_subset_uIcc ht hs) (uIoc_subset_uIcc hvst))

/-- Absolute continuity of the squared norm is derived, not postulated. -/
theorem weak_norm_sq_absolutelyContinuous (f g : ℝ → E) (hf : Continuous f)
    (hg : LocallyIntegrable g) (hw : WeakDerivative f g) (a b : ℝ) (M : NNReal)
    (hb : ∀ᵐ t, t ∈ uIcc a b → ‖g t‖ ≤ M) :
    AbsolutelyContinuousOnInterval (fun t => ‖f t‖ ^ 2) a b := by
  have hfac := (weak_lipschitz f g hf hg hw a b M hb).absolutelyContinuousOnInterval
  have hn : AbsolutelyContinuousOnInterval (fun t => ‖f t‖) a b :=
    lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hfac
  simpa only [pow_two] using hn.fun_mul hn

/-- The absolutely continuous squared-norm identity obtained from the
actual distributional weak form. The forcing need only be locally
integrable and essentially bounded on the interval under consideration. -/
theorem weak_norm_sq_identity (f g : ℝ → E) (hf : Continuous f)
    (hg : LocallyIntegrable g) (hw : WeakDerivative f g) (a b : ℝ) (M : NNReal)
    (hb : ∀ᵐ t, t ∈ uIcc a b → ‖g t‖ ≤ M) :
    ‖f b‖ ^ 2 - ‖f a‖ ^ 2 = ∫ t in a..b, 2 * ⟪f t, g t⟫_ℝ := by
  have hac := weak_norm_sq_absolutelyContinuous f g hf hg hw a b M hb
  rw [← hac.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [weak_ae_hasDerivAt f g hf hg hw] with t ht _
  exact ht.norm_sq.deriv

/-- Bounded spatial regularization preserves the distributional equation.
The adjoint supplies the transformed fixed test vector. -/
theorem weak_map (T : E →L[ℝ] E) (f g : ℝ → E) (hw : WeakDerivative f g) :
    WeakDerivative (fun t => T (f t)) (fun t => T (g t)) := by
  intro v p hp hc
  simpa only [ContinuousLinearMap.adjoint_inner_left] using hw (T.adjoint v) p hp hc

/-- Consequently every bounded spatial cutoff has its own derived AC
squared-norm identity. No finite-rank property is required. -/
theorem cutoff_norm_sq_identity (T : E →L[ℝ] E) (f g : ℝ → E)
    (hf : Continuous f) (hg : LocallyIntegrable g) (hw : WeakDerivative f g)
    (a b : ℝ) (M : NNReal)
    (hb : ∀ᵐ t, t ∈ uIcc a b → ‖T (g t)‖ ≤ M) :
    ‖T (f b)‖ ^ 2 - ‖T (f a)‖ ^ 2 =
      ∫ t in a..b, 2 * ⟪T (f t), T (g t)⟫_ℝ :=
  weak_norm_sq_identity _ _ (T.continuous.comp hf) (locallyIntegrable_map T hg)
    (weak_map T f g hw) a b M hb

end QuantumNLS.Ext005CutoffChainR110
#print axioms QuantumNLS.Ext005CutoffChainR110.weak_to_vector_integral
#print axioms QuantumNLS.Ext005CutoffChainR110.weak_norm_sq_identity
#print axioms QuantumNLS.Ext005CutoffChainR110.cutoff_norm_sq_identity

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005CutoffChainR110." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005CutoffChainR110." then
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
  Lean.logInfo m!"R110 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."

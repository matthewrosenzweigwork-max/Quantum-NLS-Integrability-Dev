import QuantumNLS.Ext005GramConvergenceR112
import QuantumNLS.LinearFundamental
import Mathlib.Analysis.ODE.Gronwall

/-! Constructive bounded regularized dynamics on a Hilbert form embedding.
The evolution is constructed by the frozen Dyson series. The form estimate
here depends on epsilon; it is not the uniform source comparison estimate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005RegularizedR33b
open Ext005GramResolventR112
variable {Q H : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Two-sided regularization of the form force, acting on the form space. -/
def generator (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e) (F : Q →L[ℝ] Q) :
    Q →L[ℝ] Q := (inverse i e he).comp (F.comp (cutoff i e he))

lemma generator_pair (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e)
    (F : Q →L[ℝ] Q) (u v : Q) :
    ⟪i v, i (generator i e he F u)⟫_ℝ =
      ⟪cutoff i e he v, F (cutoff i e he u)⟫_ℝ := by
  rw [← gram_pair]
  change ⟪gram i v, inverse i e he (F (cutoff i e he u))⟫_ℝ = _
  rw [← inverse_symm]
  rfl

lemma generator_norm_le (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e)
    (F : Q →L[ℝ] Q) : ‖generator i e he F‖ ≤ ‖inverse i e he‖ * ‖F‖ := by
  have hc : ‖cutoff i e he‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simpa using cutoff_norm_le i e he)
  calc
    _ ≤ ‖inverse i e he‖ * (‖F‖ * ‖cutoff i e he‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ ‖inverse i e he‖ * (‖F‖ * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc (norm_nonneg F)) (norm_nonneg _)
    _ = ‖inverse i e he‖ * ‖F‖ := by rw [mul_one]

lemma generator_continuous (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e) :
    Continuous (generator i e he : (Q →L[ℝ] Q) → Q →L[ℝ] Q) := by
  unfold generator
  fun_prop

omit [CompleteSpace Q] in
/-- An elementary two-sided Gronwall bound, with the derivative constructed
elsewhere; absolute time displacement is derived by an explicit reflection. -/
theorem norm_bound_two_sided (u g : ℝ → Q) (K : ℝ)
    (hd : ∀ t, HasDerivAt u (g t) t) (hb : ∀ t, ‖g t‖ ≤ K * ‖u t‖)
    (s t : ℝ) : ‖u t‖ ≤ ‖u s‖ * Real.exp (K * |t - s|) := by
  have hc : Continuous u := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  by_cases hst : s ≤ t
  · have h := norm_le_gronwallBound_of_norm_deriv_right_le (K := K) (ε := 0) hc.continuousOn
      (fun z _ => (hd z).hasDerivWithinAt) (le_refl ‖u s‖)
      (fun z _ => by simpa only [add_zero] using hb z) t ⟨hst, le_rfl⟩
    simpa only [gronwallBound_ε0, abs_of_nonneg (sub_nonneg.mpr hst)] using h
  · have hts : t ≤ s := le_of_not_ge hst
    have hdr (z : ℝ) : HasDerivAt (fun r => u (-r)) (-g (-z)) z := by
      simpa only [Function.comp_def, neg_smul, one_smul] using
        (hd (-z)).scomp z (hasDerivAt_neg z)
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (K := K) (ε := 0)
      (hc.comp continuous_neg).continuousOn
      (fun z _ => (hdr z).hasDerivWithinAt) (le_refl ‖u (-(-s))‖)
      (fun z _ => by simpa only [norm_neg, add_zero, Function.comp_apply] using hb (-z))
      (-t) (show -t ∈ Icc (-s) (-t) from ⟨neg_le_neg hts, le_rfl⟩)
    simpa only [gronwallBound_ε0, Function.comp_apply, neg_neg, neg_sub_neg,
      abs_of_nonpos (sub_nonpos.mpr hts), neg_sub] using h

/-- No evolution is supplied as a premise. The Dyson construction gives
the regularized solution for arbitrary initial time and both time directions.
The ambient norm identity is derived from the skew form. -/
theorem exists_regularized (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e)
    (F : ℝ → Q →L[ℝ] Q) (hF : Continuous F)
    (hskew : ∀ t u, ⟪u, F t u⟫_ℝ = 0)
    (M : ℝ) (hM : ∀ t, ‖F t‖ ≤ M) (s : ℝ) (u₀ : Q) :
    ∃ u : ℝ → Q, u s = u₀ ∧
      (∀ t, HasDerivAt u (generator i e he (F t) (u t)) t) ∧
      (∀ t, ‖i (u t)‖ = ‖i u₀‖) ∧
      (∀ t, ‖u t‖ ≤ ‖u₀‖ * Real.exp ((‖inverse i e he‖ * M) * |t - s|)) := by
  have hG : Continuous (fun r => generator i e he (F (r + s))) :=
    (generator_continuous i e he).comp (hF.comp (continuous_id.add continuous_const))
  obtain ⟨U, hU0, hUd⟩ := LinearFundamental.exists_fundamental hG
  let u : ℝ → Q := fun t => U (t - s) u₀
  have hu0 : u s = u₀ := by simp [u, hU0]
  have hud (t : ℝ) : HasDerivAt u (generator i e he (F t) (u t)) t := by
    have h := ((hUd (t - s)).clm_apply (hasDerivAt_const (t - s) u₀)).scomp t
      ((hasDerivAt_id t).sub_const s)
    simpa [u, mul_apply_eq_comp, Function.comp_def] using h
  have hnormd (t : ℝ) : HasDerivAt (fun r => ‖i (u r)‖ ^ 2) 0 t := by
    have h := (i.hasFDerivAt.comp_hasDerivAt t (hud t)).norm_sq
    simpa only [Function.comp_apply, generator_pair, hskew, mul_zero] using h
  have hnorm (t : ℝ) : ‖i (u t)‖ = ‖i u₀‖ := by
    have h := is_const_of_deriv_eq_zero (fun r => (hnormd r).differentiableAt)
      (fun r => (hnormd r).deriv) t s
    rw [hu0] at h
    nlinarith [norm_nonneg (i (u t)), norm_nonneg (i u₀)]
  refine ⟨u, hu0, hud, hnorm, fun t => ?_⟩
  have hb (r : ℝ) : ‖generator i e he (F r) (u r)‖ ≤ (‖inverse i e he‖ * M) * ‖u r‖ := by
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right ((generator_norm_le i e he (F r)).trans
        (mul_le_mul_of_nonneg_left (hM r) (norm_nonneg _))) (norm_nonneg _))
  simpa only [hu0] using norm_bound_two_sided u _ _ hud hb s t

end QuantumNLS.Ext005RegularizedR33b
#print axioms QuantumNLS.Ext005RegularizedR33b.exists_regularized
#print axioms QuantumNLS.Ext005RegularizedR33b.norm_bound_two_sided

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005RegularizedR33b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005RegularizedR33b." then
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
  Lean.logInfo m!"R33b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."

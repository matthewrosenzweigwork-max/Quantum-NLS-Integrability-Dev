import QuantumNLS.WindowActualTrajectoryR45b
import QuantumNLS.WindowSymplecticR45b
import QuantumNLS.RB7Rot

/-! Strong time differentiation of fixed phase paths, and uniqueness on the
actual closed auxiliary-time interval. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
attribute [local instance] InnerProductSpace.complexToReal
open Set MeasureTheory
open scoped ComplexConjugate
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.WindowPhaseR44b QuantumNLS.WindowGradientIdentificationR44b
open QuantumNLS.WindowRadialR45b QuantumNLS.WindowTrajectoryR45b
open QuantumNLS.SymplecticBracket

namespace QuantumNLS.WindowStrongPathR46b
variable {W : PosWeight}

def evalReal (W : PosWeight) (j : ℤ) : WSeq W →L[ℝ] ℂ :=
  (RB7.valCLM W j).restrictScalars ℝ

theorem evalReal_apply (j : ℤ) (z : WSeq W) : evalReal W j z = z.val j := rfl

def phasePath (ν : ℤ → ℝ) (z : WSeq W) (τ : ℝ) : WSeq W :=
  rotate (fun j => -τ * ν j) z

theorem phasePath_continuous (ν : ℤ → ℝ) (z : WSeq W) : Continuous (phasePath ν z) := by
  have hα : Continuous (fun t : ℝ => fun j : ℤ => Circle.exp (-t * ν j)) :=
    continuous_pi fun j => Circle.exp.continuous.comp (continuous_neg.mul continuous_const)
  have h := (WindowTorusR45b.continuous_act W).comp
    (hα.prodMk (continuous_const : Continuous (fun _ : ℝ => z)))
  convert h using 1
  funext t
  apply WSeq.ext
  funext j
  change (phasePath ν z t).val j = (WindowTorusR45b.act W _ z).val j
  rw [WindowTorusR45b.act_val, phasePath, rotate_val]

theorem phasePath_eval_deriv (ν : ℤ → ℝ) (z : WSeq W) (t : ℝ) (j : ℤ) :
    HasDerivAt (fun τ => (phasePath ν z τ).val j)
      (-Complex.I * (ν j : ℂ) * (phasePath ν z t).val j) t := by
  have h₀ : HasDerivAt (fun τ : ℝ => ((-τ * ν j : ℝ) : ℂ) * Complex.I)
      (-(ν j : ℂ) * Complex.I) t := by
    convert (((hasDerivAt_id t).neg.mul_const (ν j)).ofReal_comp).mul_const Complex.I using 1 <;> simp
  have h := h₀.cexp.mul_const (z.val j)
  simp only [phasePath, rotate_val, Circle.coe_exp]
  convert h using 1
  all_goals ring

/-- A square-summable initial generator suffices for strong differentiability.
Integrating its rotated image reduces the fundamental theorem to each coordinate. -/
theorem phasePath_deriv (ν : ℤ → ℝ) (z v : WSeq W)
    (hv : ∀ j, v.val j = -Complex.I * (ν j : ℂ) * z.val j) (t : ℝ) :
    HasDerivAt (phasePath ν z) (phasePath ν v t) t := by
  have hc := phasePath_continuous ν v
  have he (τ : ℝ) : phasePath ν z τ = z + ∫ a in (0 : ℝ)..τ, phasePath ν v a := by
    apply WSeq.ext
    funext j
    have hm := (evalReal W j).intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 τ)
    simp only [evalReal_apply] at hm
    rw [WSeq.val_add, Pi.add_apply, ← hm]
    have hk (a : ℝ) : (phasePath ν v a).val j =
        -Complex.I * (ν j : ℂ) * (phasePath ν z a).val j := by
      simp only [phasePath, rotate_val, hv]
      ring
    have hd (a : ℝ) := hk a ▸ phasePath_eval_deriv ν z a j
    have hf := intervalIntegral.integral_deriv_eq_sub' (a := 0) (b := τ) (fun a => (phasePath ν z a).val j)
      (funext fun a => (hd a).deriv)
      (fun a _ => (hd a).differentiableAt)
      (((evalReal W j).continuous.comp hc).continuousOn)
    have h0 : (phasePath ν z 0).val j = z.val j := by simp [phasePath]
    rw [hf, h0]
    abel
  have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  rw [show phasePath ν z = _ from funext he]
  exact h.const_add z

private theorem const_on_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f 0 (Icc 0 1) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : f t = f 0 := by
  have hs : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) :=
    uniqueDiffOn_Icc (by norm_num)
  refine (convex_Icc (0 : ℝ) 1).is_const_of_fderivWithin_eq_zero
    (fun x hx => (hf x hx).differentiableWithinAt) (fun x hx => ?_) ht (by norm_num)
  simpa using (hf x hx).hasFDerivWithinAt.fderivWithin (hs x hx)

theorem modulus_on_interval (c : ℝ → ℂ) (ν : ℝ → ℝ)
    (hc : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt c (-Complex.I * (ν t : ℂ) * c t) (Icc 0 1) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖c t‖ = ‖c 0‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply const_on_interval (f := fun x => ‖c x‖ ^ 2) _ ht
  intro a ha
  have h := (hasStrictFDerivAt_norm_sq (c a)).hasFDerivAt.comp_hasDerivWithinAt a (hc a ha)
  have hz : (2 • innerSL ℝ (c a)) (-Complex.I * (ν a : ℂ) * c a) = 0 := by
    rw [two_smul]
    simp only [add_apply, innerSL_apply_apply, real_inner_eq_re_inner ℂ,
      RCLike.re_to_complex, RCLike.inner_apply, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  exact hz ▸ h

theorem scalar_unique_on_interval (c : ℝ → ℂ) (ν : ℝ)
    (hc : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt c (-Complex.I * (ν : ℂ) * c t) (Icc 0 1) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    c t = (Circle.exp (-t * ν) : ℂ) * c 0 := by
  let p : ℝ → ℂ := fun a => Complex.exp (((a * ν : ℝ) : ℂ) * Complex.I) * c a
  have hp (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) : HasDerivWithinAt p 0 (Icc 0 1) a := by
    have h₀ : HasDerivAt (fun x : ℝ => ((x * ν : ℝ) : ℂ) * Complex.I)
        ((ν : ℂ) * Complex.I) a := by
      convert (((hasDerivAt_id a).mul_const ν).ofReal_comp).mul_const Complex.I using 1 <;> simp
    have h := h₀.cexp.hasDerivWithinAt.mul (hc a ha)
    convert h using 1
    all_goals ring
  have he := const_on_interval hp ht
  have he' : Complex.exp (((t * ν : ℝ) : ℂ) * Complex.I) * c t = c 0 := by simpa [p] using he
  have hn : (Circle.exp (-t * ν) : ℂ) = (Complex.exp (((t * ν : ℝ) : ℂ) * Complex.I))⁻¹ := by
    rw [Circle.coe_exp, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [hn, ← he']
  field_simp

end QuantumNLS.WindowStrongPathR46b

#print axioms QuantumNLS.WindowStrongPathR46b.phasePath_deriv
#print axioms QuantumNLS.WindowStrongPathR46b.modulus_on_interval
#print axioms QuantumNLS.WindowStrongPathR46b.scalar_unique_on_interval

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowStrongPathR46b." ||
        n.toString.startsWith "_private.QuantumNLS.WindowStrongPathR46b." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
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
  Lean.logInfo m!"R46b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."

import QuantumNLS.WindowInterpolationR44b

open scoped NNReal
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000

/-! R-E59628C9: a real Sobolev differential has a genuine reciprocal-weight
vector representing its full real pairing. No coordinatewise estimate is
summed without summability. The vector here uses the printed full-differential
normalization dF[v] = Re sum conj(w_j) v_j. -/
noncomputable section
set_option autoImplicit false
attribute [local instance] InnerProductSpace.complexToReal
open scoped ComplexConjugate
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.WindowInterpolationR44b
namespace QuantumNLS.WindowDualGradientR44b

/-- Riesz duality with the exact reciprocal weight. -/
theorem dual_vector (W : PosWeight) (ℓ : WSeq W →L[ℝ] ℝ) :
    ∃ g : WSeq (reciprocal W), ‖g‖ = ‖ℓ‖ ∧
      ∀ v : WSeq W, HasSum (fun j => (conj (g.val j)*v.val j).re) (ℓ v) := by
  let x : WSeq W := (InnerProductSpace.toDual ℝ (WSeq W)).symm ℓ
  have hn : ‖x‖ = ‖ℓ‖ := (InnerProductSpace.toDual ℝ (WSeq W)).symm.norm_map ℓ
  let a : ℤ → ℂ := fun j => (W.w j : ℂ)*x.val j
  have he : ∀ j, (reciprocal W).w j * ‖a j‖^2 = W.w j * ‖x.val j‖^2 := by
    intro j
    simp only [a, reciprocal, norm_mul, Complex.norm_real, Real.norm_of_nonneg (W.pos j).le, mul_pow]
    field_simp
  have hs : HasSum (fun j => (reciprocal W).w j * ‖a j‖^2) (‖x‖^2) :=
    (hasSum_norm_sq W x).congr_fun he
  let g := WSeq.mk (reciprocal W) a hs.summable
  have hg : ‖g‖ = ‖x‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    ((hasSum_norm_sq (reciprocal W) g).unique hs)
  refine ⟨g,hg.trans hn,?_⟩
  intro v
  have hv : ℓ v = (inner ℂ x v).re := by
    change ℓ v = inner ℝ x v
    exact (InnerProductSpace.toDual_symm_apply).symm
  rw [hv,inner_def]
  apply (Complex.reCLM.hasSum (lp.hasSum_inner (𝕜 := ℂ) (toL2 W x) (toL2 W v))).congr_fun
  intro j
  symm
  change (inner ℂ ((toL2 W x : lp (fun _ : ℤ => ℂ) 2) j) ((toL2 W v : lp (fun _ : ℤ => ℂ) 2) j)).re = (conj (a j)*v.val j).re
  apply congrArg Complex.re
  simp only [RCLike.inner_apply, toL2_apply, map_mul, Complex.conj_ofReal]
  change (Real.sqrt (W.w j) : ℂ)*v.val j *
      ((Real.sqrt (W.w j) : ℂ)*conj (x.val j)) = conj (a j)*v.val j
  have hsq : (Real.sqrt (W.w j) : ℂ)^2 = (W.w j : ℂ) := by
    exact_mod_cast Real.sq_sqrt (W.pos j).le
  simp only [a, map_mul, Complex.conj_ofReal]
  calc (Real.sqrt (W.w j) : ℂ)*v.val j *
      ((Real.sqrt (W.w j) : ℂ)*conj (x.val j)) =
        (Real.sqrt (W.w j) : ℂ)^2*conj (x.val j)*v.val j := by ring
    _ = _ := by rw [hsq]

/-- Composing the physical gradient error with a bounded inverse derivative
retains a^-1/2 in the genuine negative-order sequence norm. -/
theorem pullback_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : PosWeight) (ℓ : E →L[ℝ] ℝ) (D : WSeq W →L[ℝ] E)
    {a C M : ℝ} (hC : 0 ≤ C) (_hM : 0 ≤ M) (ha : 0 ≤ a)
    (hℓ : ‖ℓ‖ ≤ C*a^(-(1/2 : ℝ))) (hD : ‖D‖ ≤ M) :
    ∃ g : WSeq (reciprocal W), ‖g‖ ≤ (C*M)*a^(-(1/2 : ℝ)) ∧
      ∀ v : WSeq W, HasSum (fun j => (conj (g.val j)*v.val j).re) (ℓ (D v)) := by
  obtain ⟨g,hg,hrep⟩ := dual_vector W (ℓ.comp D)
  refine ⟨g,?_,hrep⟩
  rw [hg]
  calc ‖ℓ.comp D‖ ≤ ‖ℓ‖*‖D‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (C*a^(-(1/2 : ℝ)))*M := mul_le_mul hℓ hD (norm_nonneg _) (by positivity)
    _ = _ := by ring

end QuantumNLS.WindowDualGradientR44b

#print axioms QuantumNLS.WindowDualGradientR44b.dual_vector
#print axioms QuantumNLS.WindowDualGradientR44b.pullback_error

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowDualGradientR44b." ||
        n.toString.startsWith "_private.QuantumNLS.WindowDualGradientR44b." then
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
  Lean.logInfo m!"R44b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."

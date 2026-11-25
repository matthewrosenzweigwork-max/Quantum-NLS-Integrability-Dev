import QuantumNLS.RootGReduced
import QuantumNLS.RootBracketScalars

/-! Real dilations for the full Hilbert Poisson bracket. No quotient or
bracket-vanishing premise is built into the dilation law. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
noncomputable section
open scoped InnerProductSpace ComplexConjugate
attribute [local instance] InnerProductSpace.complexToReal
namespace QuantumNLS.RootBracketDilationR8
open SymplecticBracket
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem gradient_dilate (F : H → ℝ) (r : ℝ) (u : H)
    (hF : DifferentiableAt ℝ F (r • u)) :
    SymplecticBracket.gradient (fun v => F (r • v)) u = r • SymplecticBracket.gradient F (r • u) := by
  have hd := hF.hasFDerivAt.comp u ((hasFDerivAt_id u).const_smul r)
  have he : (fderiv ℝ F (r • u)).comp (r • ContinuousLinearMap.id ℝ H) =
      r • fderiv ℝ F (r • u) := by ext v; simp
  rw [he] at hd
  change HasFDerivAt (fun v => F (r • v)) (r • fderiv ℝ F (r • u)) u at hd
  unfold SymplecticBracket.gradient
  rw [hd.fderiv, map_smul, smul_comm]

theorem pbR_dilate (F G : H → ℝ) (r : ℝ) (u : H)
    (hF : DifferentiableAt ℝ F (r • u)) (hG : DifferentiableAt ℝ G (r • u)) :
    pbR (fun v => F (r • v)) (fun v => G (r • v)) u =
      r ^ 2 * pbR F G (r • u) := by
  rw [pbR_eq_omega, pbR_eq_omega, gradient_dilate F r u hF, gradient_dilate G r u hG]
  unfold omega
  rw [inner_smul_left_eq_smul, inner_smul_right_eq_smul]
  simp only [Complex.smul_im, smul_eq_mul]
  ring

theorem pbC_dilate (F G : H → ℂ) (r : ℝ) (u : H)
    (hF : DifferentiableAt ℝ F (r • u)) (hG : DifferentiableAt ℝ G (r • u)) :
    pbC (fun v => F (r • v)) (fun v => G (r • v)) u =
      ((r ^ 2 : ℝ) : ℂ) * pbC F G (r • u) := by
  have hf := RootGBracket.diff_re_im hF.hasFDerivAt
  have hg := RootGBracket.diff_re_im hG.hasFDerivAt
  unfold pbC
  rw [pbR_dilate _ _ r u hf.1 hg.1, pbR_dilate _ _ r u hf.2 hg.2,
    pbR_dilate _ _ r u hf.2 hg.1, pbR_dilate _ _ r u hf.1 hg.2]
  rw [← Complex.real_smul]
  apply Complex.ext <;>
    simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul] <;> ring

/-- Even differentiable real functions have zero full differential at zero. -/
theorem even_fderiv_zero (F : H → ℝ) (hF : DifferentiableAt ℝ F 0)
    (he : ∀ v, F (-v) = F v) : fderiv ℝ F 0 = 0 := by
  have hF' : HasFDerivAt F (fderiv ℝ F 0) ((fun v : H => -v) 0) := by
    simpa using hF.hasFDerivAt
  have hd := hF'.comp (0 : H) (hasFDerivAt_id (0 : H)).neg
  have hd' : HasFDerivAt F (-(fderiv ℝ F 0)) 0 := by
    convert hd using 1
    · funext v; exact (he v).symm
    · ext v; simp
  have hh := hF.hasFDerivAt.unique hd'
  ext v
  have hv := DFunLike.congr_fun hh v
  simp only [neg_apply] at hv
  change fderiv ℝ F 0 v = 0
  linarith
end QuantumNLS.RootBracketDilationR8
#print axioms QuantumNLS.RootBracketDilationR8.pbR_dilate
#print axioms QuantumNLS.RootBracketDilationR8.pbC_dilate
#print axioms QuantumNLS.RootBracketDilationR8.even_fderiv_zero

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootBracketDilationR8." ||
        n.toString.startsWith "_private.QuantumNLS.RootBracketDilationR8." then
      pending := pending.push n
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
  Lean.logInfo m!"RootBracketDilationR8 audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."

import QuantumNLS.WindowDualGradientR44b

/-! R-E59628C9: identify the reciprocal-weight Riesz error with the actual
DEF-015 coordinate gradient error using single-coordinate real variations.
The conclusion includes summability and the norm estimate; neither is an
input. Zero coordinates require no exceptional case or division. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped ComplexConjugate
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.WindowInterpolationR44b QuantumNLS.WindowDualGradientR44b
namespace QuantumNLS.WindowGradientIdentificationR44b

def coordinate (W : PosWeight) (j : ℤ) (c : ℂ) : WSeq W :=
  WSeq.mk W (Pi.single j c) (summable_of_ne_finset_zero (s := {j}) fun n hn => by
    have hnj : n ≠ j := by simpa using hn
    simp [hnj])

@[simp] theorem coordinate_val (W : PosWeight) (j n : ℤ) (c : ℂ) :
    (coordinate W j c).val n = if n = j then c else 0 := by
  simp [coordinate,Pi.single_apply]

/-- This is the DEF-015 coordinate gradient convention, not an error bound. -/
def IsCoordinateGradient (W : PosWeight) (ℓ : WSeq W →L[ℝ] ℝ) (w : ℤ → ℂ) : Prop :=
  ∀ j c, ℓ (coordinate W j c) = 2*(conj (w j)*c).re

theorem pair_coordinate (W : PosWeight) (ℓ : WSeq W →L[ℝ] ℝ)
    (g : WSeq (reciprocal W))
    (hg : ∀ v : WSeq W, HasSum (fun n => (conj (g.val n)*v.val n).re) (ℓ v))
    (j : ℤ) (c : ℂ) : ℓ (coordinate W j c) = (conj (g.val j)*c).re := by
  rw [← (hg (coordinate W j c)).tsum_eq,tsum_eq_single j]
  · simp
  · intro n hn
    simp [hn]

/-- Riesz representation matches any coordinate gradient satisfying the
actual real differential identity, with the exact factor of two. -/
theorem coordinate_gradient_error (W : PosWeight)
    (ℓ₁ ℓ₂ : WSeq W →L[ℝ] ℝ) (w₁ w₂ : ℤ → ℂ)
    (h₁ : IsCoordinateGradient W ℓ₁ w₁) (h₂ : IsCoordinateGradient W ℓ₂ w₂) :
    ∃ e : WSeq (reciprocal W),
      (∀ j, e.val j = w₁ j-w₂ j) ∧ ‖e‖ ≤ ‖ℓ₁-ℓ₂‖ := by
  obtain ⟨g,hg,hrep⟩ := dual_vector W (ℓ₁-ℓ₂)
  have hdiff : IsCoordinateGradient W (ℓ₁-ℓ₂) (fun j => w₁ j-w₂ j) := by
    intro j c
    rw [sub_apply,h₁ j c,h₂ j c]
    simp only [map_sub,sub_mul,Complex.sub_re]
    ring
  have hcoeff : ∀ j, g.val j = (2 : ℂ)*(w₁ j-w₂ j) := by
    intro j
    have htest : ∀ c : ℂ, (conj (g.val j)*c).re = 2*(conj (w₁ j-w₂ j)*c).re :=
      fun c => (pair_coordinate W (ℓ₁-ℓ₂) g hrep j c).symm.trans (hdiff j c)
    have hre : (g.val j).re = 2*(w₁ j-w₂ j).re := by simpa using htest 1
    have him : (g.val j).im = 2*(w₁ j-w₂ j).im := by
      have hi := htest Complex.I
      simp [Complex.mul_re] at hi
      simp only [Complex.sub_im]
      linarith
    apply Complex.ext
    · simpa using hre
    · simpa using him
  let e : WSeq (reciprocal W) := (1/2 : ℂ) • g
  refine ⟨e,?_,?_⟩
  · intro j
    change (1/2 : ℂ)*g.val j = _
    rw [hcoeff j]
    ring
  · dsimp [e]
    rw [norm_smul,hg]
    norm_num
    nlinarith [norm_nonneg (ℓ₁-ℓ₂)]

/-- The same vector estimate with the already proved scalar cutoff rate. -/
theorem coordinate_gradient_rate (W : PosWeight)
    (ℓ₁ ℓ₂ : WSeq W →L[ℝ] ℝ) (w₁ w₂ : ℤ → ℂ)
    (h₁ : IsCoordinateGradient W ℓ₁ w₁) (h₂ : IsCoordinateGradient W ℓ₂ w₂)
    {a A : ℝ} (h : ‖ℓ₁-ℓ₂‖ ≤ A*a^(-(1/2 : ℝ))) :
    ∃ e : WSeq (reciprocal W),
      (∀ j, e.val j = w₁ j-w₂ j) ∧ ‖e‖ ≤ A*a^(-(1/2 : ℝ)) := by
  obtain ⟨e,he,hn⟩ := coordinate_gradient_error W ℓ₁ ℓ₂ w₁ w₂ h₁ h₂
  exact ⟨e,he,hn.trans h⟩

end QuantumNLS.WindowGradientIdentificationR44b

#print axioms QuantumNLS.WindowGradientIdentificationR44b.coordinate_gradient_error
#print axioms QuantumNLS.WindowGradientIdentificationR44b.coordinate_gradient_rate

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowGradientIdentificationR44b." ||
        n.toString.startsWith "_private.QuantumNLS.WindowGradientIdentificationR44b." then
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

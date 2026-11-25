import QuantumNLS.WindowGradientIdentificationR44b
import QuantumNLS.WindowPhaseR44b

/-! Radial differential of every rotation-invariant C¹ real functional in a
positive weighted sequence Hilbert space. The coordinate gradient uses the
unweighted DEF-015 pairing, hence its coefficients belong to the reciprocal
weight space. No gradient or frequency comparison is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped ComplexConjugate
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.WindowGradientIdentificationR44b QuantumNLS.WindowPhaseR44b
namespace QuantumNLS.WindowRadialR45b
variable (W : PosWeight)

@[simp] theorem real_smul_val (a : ℝ) (z : WSeq W) :
    (a • z).val = fun j => (a : ℂ)*z.val j := rfl

@[simp] theorem coordinate_zero (j : ℤ) : coordinate W j 0 = 0 := by
  apply WSeq.ext
  funext n
  simp

theorem norm_coordinate (j : ℤ) (c : ℂ) :
    ‖coordinate W j c‖ = Real.sqrt (W.w j)*‖c‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_sq_eq_tsum,mul_pow,Real.sq_sqrt (W.pos j).le,tsum_eq_single j]
  · simp
  · intro n hn
    simp [hn]

def coordinateCLM (j : ℤ) : ℂ →L[ℝ] WSeq W :=
  LinearMap.mkContinuous
    { toFun := coordinate W j
      map_add' := fun c d => WSeq.ext (by funext n; simp only [coordinate_val,WSeq.val_add,Pi.add_apply]; split_ifs <;> simp_all)
      map_smul' := fun a c => WSeq.ext (by funext n; simp only [coordinate_val,real_smul_val]; split_ifs <;> simp_all) }
    (Real.sqrt (W.w j)) (fun c => (norm_coordinate W j c).le)

variable {W}
lemma coordinate_add (n : ℤ) (a b : ℂ) : coordinate W n (a + b) = coordinate W n a + coordinate W n b := by
  apply WSeq.ext; funext m
  simp only [coordinate_val, WSeq.val_add, Pi.add_apply]
  split_ifs <;> simp

lemma coordinate_real_smul (n : ℤ) (s : ℝ) (a : ℂ) : coordinate W n ((s : ℂ) * a) = s • coordinate W n a := by
  apply WSeq.ext; funext m
  simp only [coordinate_val, real_smul_val]
  split_ifs <;> simp

lemma coordinate_single_ne (n : ℤ) (w : ℂ) {m : ℤ} (h : m ≠ n) : (coordinate W n w).val m = 0 := by
  rw [coordinate_val, ite_eq_right h]

/-- the line `s ↦ z + s v` -/
lemma hasDerivAt_line (z v : WSeq W) : HasDerivAt (fun s : ℝ => z + s • v) v 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z

section
variable {e : WSeq W → ℝ} {z : WSeq W}

/-- A zero coordinate: the half-turn `z + s w e_n ↦ z - s w e_n` forces a vanishing derivative. -/
theorem D_single_zero (hd : DifferentiableAt ℝ e z) (hinv : ∀ θ y, e (rotate θ y) = e y)
    {n : ℤ} (hzn : z.val n = 0) (w : ℂ) : fderiv ℝ e z (coordinate W n w) = 0 := by
  set v := coordinate W n w with hv
  have h1 : HasDerivAt (fun s : ℝ => e (z + s • v)) (fderiv ℝ e z v) 0 := by
    have hd' : HasFDerivAt e (fderiv ℝ e z) (z + (0 : ℝ) • v) := by
      simpa using hd.hasFDerivAt
    exact hd'.comp_hasDerivAt (0 : ℝ) (hasDerivAt_line z v)
  have hrot : ∀ s : ℝ, rotate (Pi.single n Real.pi) (z + s • v) = z + (-s) • v := by
    intro s
    apply WSeq.ext; funext m
    rw [rotate_val]
    simp only [WSeq.val_add, Pi.add_apply, real_smul_val, hv, coordinate_val]
    by_cases hm : m = n
    · subst hm
      simp [hzn, Circle.coe_exp, Complex.exp_pi_mul_I]
    · simp [hm]
  have hfun : (fun s : ℝ => e (z + s • v)) = fun s : ℝ => e (z + (-s) • v) := by
    funext s
    rw [← hrot s, hinv]
  have h2 : HasDerivAt (fun s : ℝ => e (z + (-s) • v)) (-(fderiv ℝ e z v)) 0 := by
    have h1' : HasDerivAt (fun s : ℝ => e (z + s • v)) (fderiv ℝ e z v) (-(0 : ℝ)) := by
      simpa using h1
    have := h1'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    simpa [Function.comp_def] using this
  rw [hfun] at h1
  have := h1.unique h2
  linarith

/-- An active coordinate: the rotation of coordinate `n` has the radial-orthogonal direction `i z_n e_n`. -/
theorem D_single_rot (hd : DifferentiableAt ℝ e z) (hinv : ∀ θ y, e (rotate θ y) = e y) (n : ℤ) :
    fderiv ℝ e z (coordinate W n (Complex.I * z.val n)) = 0 := by
  have hpath : ∀ s : ℝ, rotate (Pi.single n s) z = z + coordinate W n (((Circle.exp s : ℂ) - 1) * z.val n) := by
    intro s
    apply WSeq.ext; funext m
    rw [rotate_val]
    simp only [WSeq.val_add, Pi.add_apply, coordinate_val]
    by_cases hm : m = n
    · subst hm; simp; ring
    · simp [hm]
  have hc : HasDerivAt (fun s : ℝ => ((Circle.exp s : ℂ) - 1) * z.val n)
      (Complex.I * z.val n) 0 := by
    have h0 : HasDerivAt (fun s : ℝ => ((s : ℂ) * Complex.I)) Complex.I 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I
    have h1 := ((h0.cexp).sub_const 1).mul_const (z.val n)
    simpa [Circle.coe_exp] using h1
  have hι := (coordinateCLM W n).hasFDerivAt
    (x := ((Circle.exp (0 : ℝ) : ℂ) - 1) * z.val n)
  have hs : HasDerivAt (fun s : ℝ => coordinate W n (((Circle.exp s : ℂ) - 1) * z.val n))
      (coordinate W n (Complex.I * z.val n)) 0 := by
    have := hι.comp_hasDerivAt (0 : ℝ) hc
    simpa [Function.comp_def, coordinateCLM] using this
  have hp : HasDerivAt (fun s : ℝ => z + coordinate W n (((Circle.exp s : ℂ) - 1) * z.val n))
      (coordinate W n (Complex.I * z.val n)) 0 := hs.const_add z
  have h1 : HasDerivAt (fun s : ℝ => e (z + coordinate W n (((Circle.exp s : ℂ) - 1) * z.val n)))
      (fderiv ℝ e z (coordinate W n (Complex.I * z.val n))) 0 := by
    have hz0 : z + coordinate W n (((Circle.exp (0 : ℝ) : ℂ) - 1) * z.val n) = z := by simp
    have hd' : HasFDerivAt e (fderiv ℝ e z) (z + coordinate W n (((Circle.exp (0 : ℝ) : ℂ) - 1) * z.val n)) := by
      rw [hz0]; exact hd.hasFDerivAt
    exact hd'.comp_hasDerivAt (0 : ℝ) hp
  have hfun : (fun s : ℝ => e (z + coordinate W n (((Circle.exp s : ℂ) - 1) * z.val n))) =
      fun _ => e z := by
    funext s
    rw [← hpath s, hinv]
  rw [hfun] at h1
  exact h1.unique (hasDerivAt_const _ _) |>.symm ▸ rfl

/-- The coordinate formula. -/
theorem D_single_formula (hd : DifferentiableAt ℝ e z) (hinv : ∀ θ y, e (rotate θ y) = e y)
    (n : ℤ) (w : ℂ) :
    fderiv ℝ e z (coordinate W n w) =
      (fderiv ℝ e z (coordinate W n (z.val n)) / ‖z.val n‖ ^ 2) * (conj (z.val n) * w).re := by
  by_cases hzn : z.val n = 0
  · rw [D_single_zero hd hinv hzn, hzn]; simp
  · have hn2 : (‖z.val n‖ ^ 2 : ℝ) ≠ 0 := by positivity
    set α : ℝ := (conj (z.val n) * w).re / ‖z.val n‖ ^ 2 with hα
    set β : ℝ := (conj (z.val n) * w).im / ‖z.val n‖ ^ 2 with hβ
    have hw : w = (α : ℂ) * z.val n + (β : ℂ) * (Complex.I * z.val n) := by
      set c : ℂ := conj (z.val n) * w with hcdef
      set N' : ℂ := ((‖z.val n‖ ^ 2 : ℝ) : ℂ) with hN'
      have hN'0 : N' ≠ 0 := by rw [hN']; exact_mod_cast hn2
      have hzz : conj (z.val n) * z.val n = N' := by
        rw [hN', Complex.conj_mul']; push_cast; ring
      have hc := Complex.re_add_im c
      have key : (α : ℂ) + (β : ℂ) * Complex.I = c / N' := by
        rw [eq_div_iff hN'0, hα, hβ, Complex.ofReal_div, Complex.ofReal_div, ← hN']
        field_simp
        linear_combination hc
      have : w = (c / N') * z.val n := by
        rw [div_mul_eq_mul_div, eq_div_iff hN'0, hcdef]
        calc w * N' = w * (conj (z.val n) * z.val n) := by rw [hzz]
          _ = _ := by ring
      calc w = (c / N') * z.val n := this
        _ = ((α : ℂ) + (β : ℂ) * Complex.I) * z.val n := by rw [key]
        _ = _ := by ring
    have hs : coordinate W n w = α • coordinate W n (z.val n) + β • coordinate W n (Complex.I * z.val n) := by
      rw [hw, coordinate_add, coordinate_real_smul, coordinate_real_smul]
    rw [hs, map_add, map_smul, map_smul, D_single_rot hd hinv n]
    simp only [smul_eq_mul, mul_zero, add_zero, hα]
    field_simp

end

/-- The real DEF-015 multiplier. Zero actions have multiplier zero. -/
def frequency (e : WSeq W → ℝ) (z : WSeq W) (j : ℤ) : ℝ :=
  fderiv ℝ e z (coordinate W j (z.val j)) / (2*‖z.val j‖^2)

/-- Diagonality is proved from the actual scalar invariance, including zeros. -/
theorem coordinate_gradient {e : WSeq W → ℝ} {z : WSeq W}
    (hd : DifferentiableAt ℝ e z) (hinv : ∀ θ y, e (rotate θ y) = e y) :
    IsCoordinateGradient W (fderiv ℝ e z)
      (fun j => (frequency e z j : ℂ)*z.val j) := by
  intro j c
  rw [D_single_formula hd hinv j c]
  simp only [map_mul,Complex.conj_ofReal,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  unfold frequency
  simp only [mul_inv_rev,div_eq_mul_inv]
  ring

theorem rotate_line (α : ℤ → ℝ) (z : WSeq W) (j : ℤ) (t : ℝ) :
    rotate α (z+t • coordinate W j (z.val j)) =
      rotate α z+t • coordinate W j ((rotate α z).val j) := by
  apply WSeq.ext
  funext n
  change (Circle.exp (α n) : ℂ)*(z.val n+(t : ℂ)*(coordinate W j (z.val j)).val n) =
    (rotate α z).val n+(t : ℂ)*(coordinate W j ((rotate α z).val j)).val n
  simp only [rotate_val,coordinate_val]
  split_ifs <;> simp_all
  all_goals ring

/-- The real multipliers are constant on every full rotation torus. -/
theorem frequency_rotate {e : WSeq W → ℝ} {z : WSeq W}
    (α : ℤ → ℝ) (hd : DifferentiableAt ℝ e z)
    (hd' : DifferentiableAt ℝ e (rotate α z))
    (hinv : ∀ θ y, e (rotate θ y) = e y) (j : ℤ) :
    frequency e (rotate α z) j = frequency e z j := by
  have h₀ : HasDerivAt (fun t : ℝ => e (z+t • coordinate W j (z.val j)))
      (fderiv ℝ e z (coordinate W j (z.val j))) 0 := by
    have h : HasFDerivAt e (fderiv ℝ e z) (z+(0 : ℝ) • coordinate W j (z.val j)) := by
      simpa using hd.hasFDerivAt
    exact h.comp_hasDerivAt 0 (hasDerivAt_line z _)
  have h₁ : HasDerivAt (fun t : ℝ => e (rotate α z+t • coordinate W j ((rotate α z).val j)))
      (fderiv ℝ e (rotate α z) (coordinate W j ((rotate α z).val j))) 0 := by
    have h : HasFDerivAt e (fderiv ℝ e (rotate α z))
        (rotate α z+(0 : ℝ) • coordinate W j ((rotate α z).val j)) := by
      simpa using hd'.hasFDerivAt
    exact h.comp_hasDerivAt 0 (hasDerivAt_line (rotate α z) _)
  have heq : (fun t : ℝ => e (rotate α z+t • coordinate W j ((rotate α z).val j))) =
      (fun t : ℝ => e (z+t • coordinate W j (z.val j))) := by
    funext t
    rw [← rotate_line,hinv]
  rw [heq] at h₁
  have hD := h₁.unique h₀
  unfold frequency
  rw [hD]
  simp

end QuantumNLS.WindowRadialR45b
#print axioms QuantumNLS.WindowRadialR45b.coordinate_gradient
#print axioms QuantumNLS.WindowRadialR45b.frequency_rotate

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowRadialR45b." ||
        n.toString.startsWith "_private.QuantumNLS.WindowRadialR45b." then
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
  Lean.logInfo m!"R45b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."

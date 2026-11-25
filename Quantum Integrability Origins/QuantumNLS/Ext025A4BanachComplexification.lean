import Mathlib

/-! General real Banach complexification. The underlying additive space is
V × V; its Taylor norm is the norm of the real operator (a,b) ↦ a x + b y
on the Euclidean plane. This is exactly sup_θ ‖cos θ x + sin θ y‖.
No coefficient extension or cxExt is defined here. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
namespace QuantumNLS.Ext025A4BanachComplexification

universe u v
/-- A separate type keeps the Taylor norm distinct from the product norm. -/
def Cx (V : Type u) := V × V
namespace Cx
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
instance : AddCommGroup (Cx V) := inferInstanceAs (AddCommGroup (V × V))
def mk (x y : V) : Cx V := (x,y)
def re (z : Cx V) : V := z.1
def im (z : Cx V) : V := z.2
@[ext] theorem ext {z w : Cx V} (hr : re z = re w) (hi : im z = im w) : z = w := Prod.ext hr hi
@[simp] theorem re_mk (x y : V) : re (mk x y) = x := rfl
@[simp] theorem im_mk (x y : V) : im (mk x y) = y := rfl
@[simp] theorem re_add (z w : Cx V) : re (z+w) = re z + re w := rfl
@[simp] theorem im_add (z w : Cx V) : im (z+w) = im z + im w := rfl
@[simp] theorem re_zero : re (0 : Cx V) = 0 := rfl
@[simp] theorem im_zero : im (0 : Cx V) = 0 := rfl
@[simp] theorem re_neg (z : Cx V) : re (-z) = -re z := rfl
@[simp] theorem im_neg (z : Cx V) : im (-z) = -im z := rfl
@[simp] theorem re_sub (z w : Cx V) : re (z-w) = re z - re w := rfl
@[simp] theorem im_sub (z w : Cx V) : im (z-w) = im z - im w := rfl

/-- Evaluate the pair on the real Euclidean plane. -/
def eval (z : Cx V) : ℂ →L[ℝ] V :=
  Complex.reCLM.smulRight (re z) + Complex.imCLM.smulRight (im z)
@[simp] theorem eval_apply (z : Cx V) (c : ℂ) : eval z c = c.re • re z + c.im • im z := rfl

def evalAdd : Cx V →+ (ℂ →L[ℝ] V) where
  toFun := eval
  map_zero' := by ext; simp
  map_add' z w := by ext; simp [smul_add]; abel

theorem eval_injective : Function.Injective (eval : Cx V → (ℂ →L[ℝ] V)) := by
  intro z w h
  apply ext
  · have hh := congrArg (fun A : ℂ →L[ℝ] V => A 1) h
    simpa using hh
  · have hh := congrArg (fun A : ℂ →L[ℝ] V => A Complex.I) h
    simpa using hh

instance : NormedAddCommGroup (Cx V) :=
  NormedAddCommGroup.induced (Cx V) (ℂ →L[ℝ] V) evalAdd eval_injective

theorem norm_eq (z : Cx V) : ‖z‖ = ‖eval z‖ := rfl

instance : SMul ℂ (Cx V) := ⟨fun c z => mk (c.re • re z - c.im • im z) (c.re • im z + c.im • re z)⟩
@[simp] theorem re_smul (c : ℂ) (z : Cx V) : re (c • z) = c.re • re z - c.im • im z := rfl
@[simp] theorem im_smul (c : ℂ) (z : Cx V) : im (c • z) = c.re • im z + c.im • re z := rfl
instance : Module ℂ (Cx V) where
  one_smul z := ext (by simp) (by simp)
  mul_smul c d z := ext (by simp only [re_smul, im_smul, Complex.mul_re, Complex.mul_im]; module)
    (by simp only [re_smul, im_smul, Complex.mul_re, Complex.mul_im]; module)
  smul_zero c := ext (by simp) (by simp)
  smul_add c z w := ext (by simp only [re_smul, re_add, im_add]; module)
    (by simp only [im_smul, re_add, im_add]; module)
  add_smul c d z := ext (by simp only [re_smul, re_add, Complex.add_re, Complex.add_im]; module)
    (by simp only [im_smul, im_add, Complex.add_re, Complex.add_im]; module)
  zero_smul z := ext (by simp) (by simp)

/-- Complex multiplication rotates the argument plane by the conjugate. -/
theorem eval_smul (c w : ℂ) (z : Cx V) : eval (c • z) w = eval z (starRingEnd ℂ c * w) := by
  simp only [eval_apply, re_smul, im_smul, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  module

instance : NormedSpace ℂ (Cx V) where
  norm_smul_le c z := by
    rw [norm_eq, norm_eq]
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    intro w
    rw [eval_smul]
    calc ‖eval z (starRingEnd ℂ c * w)‖ ≤ ‖eval z‖ * ‖starRingEnd ℂ c * w‖ := (eval z).le_opNorm _
      _ = (‖c‖ * ‖eval z‖) * ‖w‖ := by rw [norm_mul, Complex.norm_conj]; ring

/-- The Taylor norm formula requested for arbitrary real Banach spaces. -/
theorem norm_taylor (z : Cx V) :
    ‖z‖ = sSup (Set.range (fun θ : ℝ => ‖Real.cos θ • re z + Real.sin θ • im z‖)) := by
  let b : ℝ → ℝ := fun θ => ‖Real.cos θ • re z + Real.sin θ • im z‖
  have hb (θ : ℝ) : b θ ≤ ‖z‖ := by
    let c : ℂ := ⟨Real.cos θ, Real.sin θ⟩
    have hc : ‖c‖ = 1 := by
      have hh : c = (Real.cos θ : ℂ) + (Real.sin θ : ℂ)*Complex.I := by
        apply Complex.ext <;>
          simp only [c, Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
            mul_zero, sub_zero, add_zero, mul_one, zero_add]
      rw [hh]
      simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using Complex.norm_cos_add_sin_mul_I θ
    have hh := (eval z).le_opNorm c
    simpa only [eval_apply, c, hc, mul_one, ← norm_eq] using hh
  have hbd : BddAbove (Set.range b) := ⟨‖z‖, by rintro _ ⟨θ,rfl⟩; exact hb θ⟩
  apply le_antisymm
  · rw [norm_eq]
    apply ContinuousLinearMap.opNorm_le_of_unit_norm
    · exact (norm_nonneg _).trans (le_csSup hbd (Set.mem_range_self 0))
    · intro c hc
      have hc0 : c ≠ 0 := by intro h; simp [h] at hc
      have hθ : b c.arg = ‖eval z c‖ := by
        simp only [b, Complex.cos_arg hc0, Complex.sin_arg, hc, div_one, eval_apply]
      rw [← hθ]
      exact le_csSup hbd (Set.mem_range_self _)
  · exact csSup_le (Set.range_nonempty b) (by rintro _ ⟨θ,rfl⟩; exact hb θ)

/-- Real evaluation coordinates are contractive. -/
theorem norm_re_le (z : Cx V) : ‖re z‖ ≤ ‖z‖ := by
  rw [norm_eq]
  have hh := (eval z).le_opNorm (1 : ℂ)
  simpa using hh

theorem norm_im_le (z : Cx V) : ‖im z‖ ≤ ‖z‖ := by
  rw [norm_eq]
  have hh := (eval z).le_opNorm Complex.I
  simpa using hh

/-- Isometric real embedding and contractive projection. -/
def ι (x : V) : Cx V := mk x 0
@[simp] theorem re_ι (x : V) : re (ι x) = x := rfl
@[simp] theorem im_ι (x : V) : im (ι x) = 0 := rfl

theorem norm_ι (x : V) : ‖ι x‖ = ‖x‖ := by
  apply le_antisymm
  · rw [norm_eq]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro c
    simp only [eval_apply, re_ι, im_ι, smul_zero, add_zero, norm_smul, Real.norm_eq_abs]
    calc |c.re| * ‖x‖ ≤ ‖c‖ * ‖x‖ := mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm c) (norm_nonneg _)
      _ = ‖x‖ * ‖c‖ := mul_comm _ _
  · exact norm_re_le (ι x)

/-- All real operators on the plane occur, giving completeness without
any inner product on V. -/
def evalEquiv : Cx V ≃ᵢ (ℂ →L[ℝ] V) where
  toFun := eval
  invFun := fun A => mk (A 1) (A Complex.I)
  left_inv z := by apply ext <;> simp
  right_inv A := by
    ext c
    change c.re • A 1 + c.im • A Complex.I = A c
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    apply Complex.ext <;> simp [Complex.real_smul]
  isometry_toFun := AddMonoidHomClass.isometry_of_norm evalAdd (fun _ => rfl)

instance [CompleteSpace V] : CompleteSpace (Cx V) := evalEquiv.completeSpace

theorem ofReal_smul (c : ℝ) (z : Cx V) : (c : ℂ) • z = c • z := by
  exact algebraMap_smul ℂ c z

/-- Norm preservation also gives the inherited real normed space. -/
def ιL : V →L[ℝ] Cx V :=
  LinearMap.mkContinuous
    { toFun := ι
      map_add' := fun _ _ => ext rfl (by simp [ι])
      map_smul' := fun c x => by
        change ι (c • x) = c • ι x
        rw [← ofReal_smul]
        apply ext <;> simp only [re_ι, im_ι, re_smul, im_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, smul_zero, sub_zero, add_zero] }
    1 (fun x => by simp [norm_ι])

def reL : Cx V →L[ℝ] V :=
  LinearMap.mkContinuous
    { toFun := re
      map_add' := re_add
      map_smul' := fun c z => by
        change re (c • z) = c • re z
        rw [← ofReal_smul, re_smul]
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero] }
    1 (fun z => by simpa using norm_re_le z)

@[simp] theorem ιL_apply (x : V) : (ιL : V →L[ℝ] Cx V) x = ι x := rfl
@[simp] theorem reL_apply (z : Cx V) : (reL : Cx V →L[ℝ] V) z = re z := rfl

@[simp] theorem ι_add (x y : V) : ι (x+y) = ι x + ι y := ext rfl (by simp [ι])
@[simp] theorem ι_sub (x y : V) : ι (x-y) = ι x - ι y := ext rfl (by simp [ι])
@[simp] theorem ι_smul (c : ℝ) (x : V) : ι (c • x) = (c : ℂ) • ι x := by
  apply ext <;> simp only [re_ι, im_ι, re_smul, im_smul, Complex.ofReal_re,
    Complex.ofReal_im, zero_smul, smul_zero, sub_zero, add_zero]

theorem mk_eq (x y : V) : mk x y = ι x + Complex.I • ι y := ext (by simp) (by simp)

theorem norm_ιL_le : ‖(ιL : V →L[ℝ] Cx V)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖ι x‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using (norm_ι x).le

theorem norm_reL_le : ‖(reL : Cx V →L[ℝ] V)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖re z‖ ≤ 1 * ‖z‖
  simpa only [one_mul] using norm_re_le z

variable {W : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W]
/-- The complexification of a bounded real operator has no norm loss in
the Taylor norm. This applies also to the source's auxiliary Banach W. -/
def mapL (A : V →L[ℝ] W) : Cx V →L[ℂ] Cx W :=
  LinearMap.mkContinuous
    { toFun := fun z => mk (A (re z)) (A (im z))
      map_add' := fun z w => ext (by simp) (by simp)
      map_smul' := fun c z => by
        apply ext <;> simp only [re_mk, im_mk, re_smul, im_smul, map_sub, map_add, map_smul,
          RingHom.id_apply] }
    ‖A‖ (fun z => by
      rw [norm_eq]
      apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      intro c
      change ‖c.re • A (re z) + c.im • A (im z)‖ ≤ (‖A‖ * ‖z‖) * ‖c‖
      rw [← map_smul, ← map_smul, ← map_add]
      calc ‖A (c.re • re z + c.im • im z)‖ ≤ ‖A‖ * ‖eval z c‖ := A.le_opNorm _
        _ ≤ ‖A‖ * (‖eval z‖ * ‖c‖) := mul_le_mul_of_nonneg_left ((eval z).le_opNorm c) (norm_nonneg _)
        _ = (‖A‖ * ‖z‖) * ‖c‖ := by rw [norm_eq]; ring)

theorem norm_mapL_le (A : V →L[ℝ] W) : ‖mapL A‖ ≤ ‖A‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg A) _

@[simp] theorem mapL_ι (A : V →L[ℝ] W) (x : V) : mapL A (ι x) = ι (A x) :=
  ext rfl (by simp [mapL])

end Cx
end QuantumNLS.Ext025A4BanachComplexification

#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.mk
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.re
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.im
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.ext
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.re_mk
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.im_mk
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.re_add
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.im_add
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.re_zero
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.im_zero
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.re_neg
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.im_neg
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.re_sub
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.im_sub
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.eval
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.eval_apply
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.evalAdd
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.eval_injective
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.norm_eq
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.re_smul
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.im_smul
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.eval_smul
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.norm_taylor
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.norm_re_le
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.norm_im_le
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.ι
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.re_ι
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.im_ι
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.norm_ι
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.evalEquiv
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.ιL
#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.reL

#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.ofReal_smul

#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.ι_add

#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.ι_sub

#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.ι_smul

#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.mk_eq

#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.norm_ιL_le

#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.norm_reL_le

#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.mapL

#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.norm_mapL_le

#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.mapL_ι

#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.ιL_apply

#print axioms QuantumNLS.Ext025A4BanachComplexification.Cx.reL_apply

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025A4BanachComplexification" then
      pending := pending.push n
      roots := roots + 1
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."

import QuantumNLS.WindowRadialR45b
import QuantumNLS.WindowTorusR45b

/-! Construct and uniquely identify the coordinate Hamiltonian trajectories of
rotation-invariant real functionals. The real multipliers are actual derivatives,
not a supplied frequency-error hypothesis. Zeros are retained throughout. -/
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped ComplexConjugate
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.WindowGradientIdentificationR44b QuantumNLS.WindowPhaseR44b
open QuantumNLS.WindowRadialR45b
namespace QuantumNLS.WindowTrajectoryR45b
variable {W : PosWeight}

theorem exists_rotate {z y : WSeq W} (hm : ∀ j, ‖z.val j‖ = ‖y.val j‖) :
    ∃ α : ℤ → ℝ, y = rotate α z := by
  refine ⟨fun j => Complex.arg (y.val j)-Complex.arg (z.val j),?_⟩
  apply WSeq.ext
  funext j
  rw [rotate_val,Circle.coe_exp]
  have e₁ := (Complex.norm_mul_exp_arg_mul_I (z.val j)).symm
  have e₂ : y.val j = (‖z.val j‖ : ℂ)*Complex.exp ((Complex.arg (y.val j) : ℂ)*Complex.I) := by
    rw [hm j]
    exact (Complex.norm_mul_exp_arg_mul_I _).symm
  have key : Complex.exp (((Complex.arg (y.val j)-Complex.arg (z.val j) : ℝ) : ℂ)*Complex.I)*
      ((‖z.val j‖ : ℂ)*Complex.exp ((Complex.arg (z.val j) : ℂ)*Complex.I)) =
      (‖z.val j‖ : ℂ)*Complex.exp ((Complex.arg (y.val j) : ℂ)*Complex.I) := by
    push_cast
    rw [sub_mul,Complex.exp_sub]
    field_simp
  calc y.val j = _ := e₂
    _ = _ := key.symm
    _ = _ := by rw [← e₁]

theorem frequency_of_moduli {e : WSeq W → ℝ} {z y : WSeq W}
    (hd : DifferentiableAt ℝ e z) (hy : DifferentiableAt ℝ e y)
    (hinv : ∀ α x, e (rotate α x) = e x)
    (hm : ∀ j, ‖z.val j‖ = ‖y.val j‖) (j : ℤ) :
    frequency e y j = frequency e z j := by
  obtain ⟨α,rfl⟩ := exists_rotate hm
  exact frequency_rotate α hd hy hinv j

/-- Exact constant-action candidate, with the DEF-015 sign and factor. -/
def trajectory (e : WSeq W → ℝ) (z : WSeq W) (t : ℝ) : WSeq W :=
  rotate (fun j => -t*frequency e z j) z

@[simp] theorem trajectory_zero (e : WSeq W → ℝ) (z : WSeq W) : trajectory e z 0 = z := by
  apply WSeq.ext
  funext j
  simp [trajectory]

@[simp] theorem trajectory_moduli (e : WSeq W → ℝ) (z : WSeq W) (t : ℝ) (j : ℤ) :
    ‖(trajectory e z t).val j‖ = ‖z.val j‖ := by simp only [trajectory,rotate_val,norm_mul,Circle.norm_coe,one_mul]

theorem trajectory_mem_hull (e : WSeq W → ℝ) {K : Set (WSeq W)} {z : WSeq W}
    (hz : z ∈ K) (t : ℝ) : trajectory e z t ∈ WindowTorusR45b.hull W K :=
  WindowTorusR45b.rotate_mem_hull W hz _

theorem coordinate_derivative (e : WSeq W → ℝ) (z : WSeq W) (t : ℝ) (j : ℤ) :
    HasDerivAt (fun τ => (trajectory e z τ).val j)
      (-Complex.I*(frequency e z j : ℂ)*(trajectory e z t).val j) t := by
  have h₀ : HasDerivAt (fun τ : ℝ => ((-τ*frequency e z j : ℝ) : ℂ)*Complex.I)
      (-(frequency e z j : ℂ)*Complex.I) t := by
    convert (((hasDerivAt_id t).neg.mul_const (frequency e z j)).ofReal_comp).mul_const Complex.I using 1 <;> simp
  have h := h₀.cexp.mul_const (z.val j)
  simp only [trajectory,rotate_val,Circle.coe_exp]
  convert h using 1
  all_goals ring

/-- Coordinate Hamilton equation, written with its actual scalar differential. -/
def IsHamiltonianPath (e : WSeq W → ℝ) (γ : ℝ → WSeq W) : Prop :=
  ∀ t j, HasDerivAt (fun τ => (γ τ).val j)
    (-Complex.I*(frequency e (γ t) j : ℂ)*(γ t).val j) t

/-- The constructed rotations solve the actual coordinate Hamilton equation. -/
theorem trajectory_hamiltonian {e : WSeq W → ℝ} (z : WSeq W)
    (hd : ∀ α, DifferentiableAt ℝ e (rotate α z))
    (hinv : ∀ α y, e (rotate α y) = e y) : IsHamiltonianPath e (trajectory e z) := by
  have hz : DifferentiableAt ℝ e z := by
    have he : rotate (fun _ => 0) z = z := by apply WSeq.ext; funext j; simp
    simpa only [he] using hd (fun _ => 0)
  intro t j
  have hf := frequency_rotate (fun j => -t*frequency e z j) hz
    (hd (fun j => -t*frequency e z j)) hinv j
  simpa only [trajectory] using (hf ▸ coordinate_derivative e z t j)

/-- Any coordinate Hamiltonian solution preserves all moduli; this is proved
from its real Hamiltonian multipliers, never assumed as an orbit condition. -/
theorem path_moduli {e : WSeq W → ℝ} {γ : ℝ → WSeq W}
    (hγ : IsHamiltonianPath e γ) (t : ℝ) (j : ℤ) :
    ‖(γ t).val j‖ = ‖(γ 0).val j‖ := by
  have hf : ∀ τ, HasDerivAt (fun x => ‖(γ x).val j‖^2) 0 τ := by
    intro τ
    have h := (hasStrictFDerivAt_norm_sq ((γ τ).val j)).hasFDerivAt.comp_hasDerivAt τ (hγ τ j)
    have hz : (2 • innerSL ℝ ((γ τ).val j))
        (-Complex.I*(frequency e (γ τ) j : ℂ)*(γ τ).val j) = 0 := by
      rw [two_smul]
      simp only [add_apply,innerSL_apply_apply,real_inner_eq_re_inner ℂ,
        RCLike.re_to_complex,RCLike.inner_apply,Complex.mul_re,Complex.mul_im,
        Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im]
      ring
    exact hz ▸ h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (is_const_of_deriv_eq_zero (fun τ => (hf τ).differentiableAt)
      (fun τ => (hf τ).deriv) t 0)

/-- Uniqueness for the scalar equation with a fixed real multiplier. -/
theorem scalar_unique (ω : ℝ) (c : ℝ → ℂ)
    (hc : ∀ t, HasDerivAt c (-Complex.I*(ω : ℂ)*c t) t) (t : ℝ) :
    c t = (Circle.exp (-t*ω) : ℂ)*c 0 := by
  let p : ℝ → ℂ := fun τ => Complex.exp (((τ*ω : ℝ) : ℂ)*Complex.I)*c τ
  have hp : ∀ τ, HasDerivAt p 0 τ := by
    intro τ
    have h₀ : HasDerivAt (fun x : ℝ => ((x*ω : ℝ) : ℂ)*Complex.I)
        ((ω : ℂ)*Complex.I) τ := by
      convert (((hasDerivAt_id τ).mul_const ω).ofReal_comp).mul_const Complex.I using 1 <;> simp
    have h := h₀.cexp.mul (hc τ)
    convert h using 1
    all_goals ring
  have he := is_const_of_deriv_eq_zero (fun τ => (hp τ).differentiableAt)
    (fun τ => (hp τ).deriv) t 0
  have he' : Complex.exp (((t*ω : ℝ) : ℂ)*Complex.I)*c t = c 0 := by simpa [p] using he
  have hn : (Circle.exp (-t*ω) : ℂ) = (Complex.exp (((t*ω : ℝ) : ℂ)*Complex.I))⁻¹ := by
    rw [Circle.coe_exp,← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [hn,← he']
  field_simp

/-- Every coordinate Hamiltonian path is this same rotation trajectory. -/
theorem trajectory_unique {e : WSeq W → ℝ} {γ : ℝ → WSeq W}
    (hd : ∀ x, DifferentiableAt ℝ e x)
    (hinv : ∀ α y, e (rotate α y) = e y)
    (hγ : IsHamiltonianPath e γ) (t : ℝ) : γ t = trajectory e (γ 0) t := by
  apply WSeq.ext
  funext j
  have hf : ∀ τ, frequency e (γ τ) j = frequency e (γ 0) j := fun τ =>
    frequency_of_moduli (hd _) (hd _) hinv (fun n => (path_moduli hγ τ n).symm) j
  have hc : ∀ τ, HasDerivAt (fun x => (γ x).val j)
      (-Complex.I*(frequency e (γ 0) j : ℂ)*(γ τ).val j) τ := by
    intro τ
    simpa only [hf τ] using hγ τ j
  exact scalar_unique _ _ hc t

end QuantumNLS.WindowTrajectoryR45b
#print axioms QuantumNLS.WindowTrajectoryR45b.trajectory_hamiltonian
#print axioms QuantumNLS.WindowTrajectoryR45b.path_moduli
#print axioms QuantumNLS.WindowTrajectoryR45b.trajectory_unique

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowTrajectoryR45b." ||
        n.toString.startsWith "_private.QuantumNLS.WindowTrajectoryR45b." then
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

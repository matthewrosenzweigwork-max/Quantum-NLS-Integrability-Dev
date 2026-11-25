import QuantumNLS.Def021ChartR41b
import QuantumNLS.SymplecticBracket

/-! Exact DEF-015 Hamiltonian-field transfer through the accepted actual
chart. This uses full real strong symplecticity, with no restriction to a
mass surface and no assumed field-identification equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
attribute [local instance] InnerProductSpace.complexToReal
open scoped ComplexConjugate
namespace QuantumNLS.WindowSymplecticR45b
open QuantumNLS.SymplecticBracket
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- DEF-015 gives Ω(X_F,h)=dF[h] with its literal factor of two. -/
theorem omega_hamField (F : H → ℝ) (u h : H) : omega (hamField F u) h = fderiv ℝ F u h := by
  rw [fderiv_eq_two_inner_gradient,real_inner_eq_re_inner ℂ]
  unfold hamField omega
  rw [inner_smul_left]
  simp

theorem omega_ext (a b : H) (h : ∀ k, omega a k = omega b k) : a = b := by
  let d := a-b
  have hz : ∀ k, omega d k = 0 := by
    intro k
    dsimp [d]
    unfold omega
    rw [inner_sub_left,Complex.sub_im]
    have hk := h k
    unfold omega at hk
    linarith
  have hd := omega_mul_I d
  rw [hz] at hd
  have hn : ‖d‖ = 0 := by nlinarith [norm_nonneg d]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The actual inverse derivative sends the actual coordinate Hamiltonian
field to the actual physical Hamiltonian field. All directions are real
Hilbert tangent vectors; no action constraint is imposed. -/
theorem field_transfer (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (F : PhysicalTensor.L2T L → ℝ) (z : D01LocalPrimitive.K)
    (hF : DifferentiableAt ℝ F (C.Ψ z)) :
    fderiv ℝ C.Ψ z (hamField (fun x => F (C.Ψ x)) z) = hamField F (C.Ψ z) := by
  let u := C.Ψ z
  obtain ⟨e,he,hie⟩ := C.differential u
  have hz : C.Φ u = z := C.right_inverse z
  rw [hz] at hie
  have heq : fderiv ℝ C.Φ u = e.toContinuousLinearMap := he.fderiv
  have hieq : fderiv ℝ C.Ψ z = e.symm.toContinuousLinearMap := hie.fderiv
  rw [hieq]
  apply omega_ext
  intro k
  let V := hamField (fun x => F (C.Ψ x)) z
  have hs : omega (e.symm V) k = omega V (e k) := by
    have hp := C.symplectic u (e.symm V) k
    change omega (fderiv ℝ C.Φ u (e.symm V)) (fderiv ℝ C.Φ u k) = omega (e.symm V) k at hp
    rw [heq] at hp
    simpa only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply] using hp.symm
  change omega (e.symm V) k = omega (hamField F u) k
  rw [hs,omega_hamField,omega_hamField]
  have hc : HasFDerivAt (fun x => F (C.Ψ x))
      ((fderiv ℝ F u).comp e.symm.toContinuousLinearMap) z := hF.hasFDerivAt.comp z hie
  change fderiv ℝ (fun x => F (C.Ψ x)) z (e k) = fderiv ℝ F u k
  have hc_apply := congrArg (fun A : D01LocalPrimitive.K →L[ℝ] ℝ => A (e k)) hc.fderiv
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply] using hc_apply

end QuantumNLS.WindowSymplecticR45b
#print axioms QuantumNLS.WindowSymplecticR45b.field_transfer

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowSymplecticR45b." ||
        n.toString.startsWith "_private.QuantumNLS.WindowSymplecticR45b." then
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

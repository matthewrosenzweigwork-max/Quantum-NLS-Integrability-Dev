import QuantumNLS.Prop021CoefficientR128
import QuantumNLS.Ext025B3PhysicalSectors

/-! PROP-021 exact-number extraction, at the actual physical Fock projection.
No normalization of the projected approximate vector is used. The excitation
observable is a sector contraction. Identifying it with (dGamma(q)/N)^(1/2)
and proving its Weyl commutation are separate physical obligations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace
namespace QuantumNLS.Prop021SectorTransferR128
open Ext025B3PhysicalSectors BetheCoefficientTransform Prop021CoefficientR128
variable {L : ℝ} [Fact (0 < L)]

/-- Contractive transfer of the vector error through the actual sector projection. -/
theorem project_error {x y : Fock L} {δ : ℝ} (N : ℕ) (h : ‖x-y‖ ≤ δ) :
    ‖projection L N x-projection L N y‖ ≤ δ := by
  rw [← map_sub]
  exact (projection_norm_le L N (x-y)).trans h

/-- Core unnormalized extraction estimate. The norm of the exact sector vector
is not used, and the approximate projection is allowed to vanish. -/
theorem contraction_transfer (N : ℕ) (K : HN L N →L[ℂ] HN L N)
    (hK : ∀ z, ‖K z‖ ≤ ‖z‖) (ψ : HN L N) (x y : Fock L)
    {c δ : ℝ} (hc : 0 ≤ c) (hx : x N = (c:ℂ) • ψ) (hxy : ‖x-y‖ ≤ δ) :
    c * ‖K ψ‖ ≤ δ+‖K (y N)‖ := by
  have hev : ‖x N-y N‖ ≤ δ := by
    have h := lp.norm_apply_le_norm (by norm_num) (x-y) N
    exact h.trans hxy
  have hd : K ((c:ℂ) • ψ) = K (x N-y N)+K (y N) := by
    rw [← map_add,sub_add_cancel,hx]
  have hn : ‖K ((c:ℂ) • ψ)‖ = c * ‖K ψ‖ := by
    rw [map_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
  calc
    c * ‖K ψ‖ = ‖K ((c:ℂ) • ψ)‖ := hn.symm
    _ ≤ ‖K (x N-y N)‖+‖K (y N)‖ := hd ▸ norm_add_le _ _
    _ ≤ δ+‖K (y N)‖ := by linarith [(hK (x N-y N)).trans hev]

/-- Exact physical projection form of the preceding estimate. -/
theorem projection_contraction_transfer (N : ℕ) (K : HN L N →L[ℂ] HN L N)
    (hK : ∀ z, ‖K z‖ ≤ ‖z‖) (ψ : HN L N) (x y : Fock L)
    {c δ : ℝ} (hc : 0 ≤ c)
    (hx : projection L N x = (c:ℂ) • inclusion L N ψ) (hxy : ‖x-y‖ ≤ δ) :
    c * ‖K ψ‖ ≤ δ+‖K (y N)‖ := by
  apply contraction_transfer N K hK ψ x y hc _ hxy
  have he := congrArg (fun z : Fock L => z N) hx
  rw [projection_same] at he
  have hs : ((c:ℂ) • inclusion L N ψ) N = (c:ℂ) • ψ := by
    change (lp.evalCLM (E := fun n => HN L n) (p := 2) ℂ N)
      ((c:ℂ) • inclusion L N ψ) = _
    rw [map_smul]
    congr 1
    change (lp.single 2 N ψ) N = ψ
    simp [lp.single_apply]
  exact he.trans hs

/-- The N^(1/4) coefficient loss is proved rather than supplied. -/
theorem coherent_contraction_transfer (N : ℕ) (hN : 1 ≤ N)
    (K : HN L N →L[ℂ] HN L N) (hK : ∀ z, ‖K z‖ ≤ ‖z‖)
    (ψ : HN L N) (x y : Fock L) {δ : ℝ}
    (hx : x N = (coherentCoefficient N:ℂ) • ψ) (hxy : ‖x-y‖ ≤ δ) :
    ‖K ψ‖ ≤ Real.sqrt (Real.exp 1) * Real.rpow (N:ℝ) (1/4:ℝ) *
      (δ+‖K (y N)‖) := by
  have hc := coefficient_pos hN
  have h := contraction_transfer N K hK ψ x y hc.le hx hxy
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hxy
  have hsum : 0 ≤ δ+‖K (y N)‖ := add_nonneg hδ (norm_nonneg _)
  have hb := coefficient_inverse_bound hN
  rw [fourthRoot_eq_rpow (N:ℝ) (by positivity)] at hb
  have hm := mul_le_mul_of_nonneg_right hb hsum
  calc
    ‖K ψ‖ ≤ (coherentCoefficient N)⁻¹ * (δ+‖K (y N)‖) := by
      have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hc.le)
      simpa only [← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul] using hh
    _ ≤ _ := hm
end QuantumNLS.Prop021SectorTransferR128
#print axioms QuantumNLS.Prop021SectorTransferR128.projection_contraction_transfer
#print axioms QuantumNLS.Prop021SectorTransferR128.coherent_contraction_transfer

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021SectorTransferR128"].any
        (fun m => n.toString.startsWith ("QuantumNLS." ++ m ++ ".") ||
          n.toString.startsWith ("_private.QuantumNLS." ++ m ++ ".")) then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").contains "HeldGP14Tonelli" ||
          (n.toString.splitOn ".").contains "RegularCut" then
        throwError "Forbidden held dependency: {n}"
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
  Lean.logInfo m!"R128 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."

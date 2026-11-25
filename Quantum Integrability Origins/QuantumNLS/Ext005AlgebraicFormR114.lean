import QuantumNLS.Ext005ComplexRieszR113
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Bounded representability derived for algebraic Hermitian forms. The
input has no topology or continuity field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005AlgebraicFormR114
open Ext005ComplexRieszR113
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]

abbrev RawForm (Q : Type*) [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] :=
  Q →ₗ[ℂ] Q →ₗ⋆[ℂ] ℂ

def Hermitian (f : RawForm Q) : Prop := ∀ u v, starRingEnd ℂ (f u v) = f v u

/-- A nonnegative form built only from the diagonal bound. Its core is used
algebraically for Cauchy--Schwarz, without changing Q's original topology. -/
@[instance_reducible] def positiveCore (f : RawForm Q) (K : ℝ) (hs : Hermitian f)
    (hb : ∀ u, |(f u u).re| ≤ K * ‖u‖ ^ 2) : PreInnerProductSpace.Core ℂ Q where
  inner u v := (K : ℂ) * ⟪u, v⟫_ℂ + f v u
  conj_inner_symm u v := by
    simp only [map_add, map_mul, Complex.conj_ofReal, inner_conj_symm, hs u v]
  re_inner_nonneg u := by
    have h := (abs_le.mp (hb u)).1
    change 0 ≤ ((K : ℂ) * ⟪u, u⟫_ℂ + f u u).re
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    have he := norm_sq_eq_re_inner (𝕜 := ℂ) u
    change ‖u‖ ^ 2 = (⟪u, u⟫_ℂ).re at he
    rw [← he]
    linarith
  add_left u v w := by
    simp only [inner_add_left, map_add, mul_add]
    ring
  smul_left u v c := by
    simp only [inner_smul_left, map_smulₛₗ, smul_eq_mul]
    ring

/-- A two-sided diagonal bound implies a finite bilinear bound. -/
theorem raw_bound (f : RawForm Q) (K : ℝ) (hK : 0 ≤ K) (hs : Hermitian f)
    (hb : ∀ u, |(f u u).re| ≤ K * ‖u‖ ^ 2) (u v : Q) :
    ‖f u v‖ ≤ (3 * K) * ‖u‖ * ‖v‖ := by
  let : PreInnerProductSpace.Core ℂ Q := positiveCore f K hs hb
  let p := fun x y : Q => (K : ℂ) * ⟪x, y⟫_ℂ + f y x
  have hc := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) v u
  change ‖p v u‖ * ‖p u v‖ ≤ (p v v).re * (p u u).re at hc
  have heq : ‖p u v‖ = ‖p v u‖ := by
    have he : starRingEnd ℂ (p u v) = p v u := by
      simp only [p, map_add, map_mul, Complex.conj_ofReal, inner_conj_symm, hs v u]
    rw [← he, RCLike.norm_conj]
  rw [heq] at hc
  have hp (x : Q) : (p x x).re ≤ 2 * K * ‖x‖ ^ 2 := by
    have h := (abs_le.mp (hb x)).2
    change ((K : ℂ) * ⟪x, x⟫_ℂ + f x x).re ≤ _
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    have he := norm_sq_eq_re_inner (𝕜 := ℂ) x
    change ‖x‖ ^ 2 = (⟪x, x⟫_ℂ).re at he
    rw [← he]
    linarith
  have hp0 (x : Q) : 0 ≤ (p x x).re := (positiveCore f K hs hb).re_inner_nonneg x
  have hmul := mul_le_mul (hp v) (hp u) (hp0 u) (by positivity : 0 ≤ 2 * K * ‖v‖ ^ 2)
  have hn : ‖p v u‖ ≤ 2 * K * ‖u‖ * ‖v‖ := by
    have hb' := hc.trans hmul
    have hsquare : ‖p v u‖ ^ 2 ≤ (2 * K * ‖u‖ * ‖v‖) ^ 2 := by
      nlinarith [hb']
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsquare
  have hi : ‖(K : ℂ) * ⟪v, u⟫_ℂ‖ ≤ K * ‖u‖ * ‖v‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK]
    calc
      K * ‖⟪v, u⟫_ℂ‖ ≤ K * (‖v‖ * ‖u‖) := mul_le_mul_of_nonneg_left (norm_inner_le_norm v u) hK
      _ = K * ‖u‖ * ‖v‖ := by ring
  calc
    ‖f u v‖ = ‖p v u - (K : ℂ) * ⟪v, u⟫_ℂ‖ := by congr 1; dsimp [p]; ring
    _ ≤ ‖p v u‖ + ‖(K : ℂ) * ⟪v, u⟫_ℂ‖ := norm_sub_le _ _
    _ ≤ (3 * K) * ‖u‖ * ‖v‖ := by linarith

/-- Construct the continuous form from its algebraic coefficients and a
proved diagonal estimate. -/
def continuousForm (f : RawForm Q) (K : ℝ) (hK : 0 ≤ K) (hs : Hermitian f)
    (hb : ∀ u, |(f u u).re| ≤ K * ‖u‖ ^ 2) : Form Q :=
  f.mkContinuous₂ (3 * K) (raw_bound f K hK hs hb)

@[simp] lemma continuousForm_apply (f : RawForm Q) (K : ℝ) (hK : 0 ≤ K)
    (hs : Hermitian f) (hb : ∀ u, |(f u u).re| ≤ K * ‖u‖ ^ 2) (u v : Q) :
    continuousForm f K hK hs hb u v = f u v := rfl

end QuantumNLS.Ext005AlgebraicFormR114
#print axioms QuantumNLS.Ext005AlgebraicFormR114.raw_bound
#print axioms QuantumNLS.Ext005AlgebraicFormR114.continuousForm_apply

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005AlgebraicFormR114." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005AlgebraicFormR114." then
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
  Lean.logInfo m!"R114 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."

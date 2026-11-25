import QuantumNLS.Ext005SourceRegularizedR33b

/-! Complex compatibility and the actual cutoff Hamiltonian cancellation.
All inverses and cutoffs are the constructed R112 operators. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005ComplexGramR34b
open Ext005GramResolventR112 Ext005ComplexForceR113 Ext005RegularizedR33b
variable {Q H : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ Q := InnerProductSpace.rclikeToReal ℂ Q
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (i : Q →L[ℂ] H) (e : ℝ) (he : 0 < e)

lemma gram_complex (u : Q) :
    gram (i.restrictScalars ℝ) u = i.adjoint (i u) := by
  apply ext_inner_right ℝ
  intro v
  rw [gram_pair]
  exact (congrArg Complex.re (i.adjoint_inner_left v (i u))).symm

lemma gram_smul (c : ℂ) (u : Q) :
    gram (i.restrictScalars ℝ) (c • u) = c • gram (i.restrictScalars ℝ) u := by
  simp only [gram_complex, map_smul]

lemma perturbed_smul (c : ℂ) (u : Q) :
    perturbed (i.restrictScalars ℝ) e (c • u) =
      c • perturbed (i.restrictScalars ℝ) e u := by
  simp only [perturbed, add_apply, id_apply, smul_apply, gram_smul, smul_add,
    smul_comm e c]

lemma inverse_smul (c : ℂ) (u : Q) :
    inverse (i.restrictScalars ℝ) e he (c • u) =
      c • inverse (i.restrictScalars ℝ) e he u := by
  apply_fun perturbed (i.restrictScalars ℝ) e
  · rw [perturbed_inverse, perturbed_smul, perturbed_inverse]
  · intro x y h
    simpa only [inverse_perturbed] using congrArg (inverse (i.restrictScalars ℝ) e he) h

/-- The existing real inverse is complex linear; this is proved, not assumed. -/
def inverseC : Q →L[ℂ] Q :=
  LinearMap.mkContinuous
    { toFun := inverse (i.restrictScalars ℝ) e he
      map_add' := map_add _
      map_smul' := inverse_smul i e he }
    ‖inverse (i.restrictScalars ℝ) e he‖ (ContinuousLinearMap.le_opNorm _)

lemma inverseC_symm (u v : Q) :
    ⟪inverseC i e he u, v⟫_ℂ = ⟪u, inverseC i e he v⟫_ℂ := by
  apply Complex.ext
  · exact inverse_symm (i.restrictScalars ℝ) e he u v
  · have h := inverse_symm (i.restrictScalars ℝ) e he u (Complex.I • v)
    rw [inverse_smul] at h
    change (⟪inverseC i e he u, Complex.I • v⟫_ℂ).re =
      (⟪u, Complex.I • inverseC i e he v⟫_ℂ).re at h
    simpa only [inner_smul_right, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub, neg_inj] using h

lemma gram_complex_pair (u v : Q) :
    ⟪gram (i.restrictScalars ℝ) u, v⟫_ℂ = ⟪i u, i v⟫_ℂ := by
  rw [gram_complex]
  exact i.adjoint_inner_left v (i u)

lemma cutoff_smul (c : ℂ) (u : Q) :
    cutoff (i.restrictScalars ℝ) e he (c • u) =
      c • cutoff (i.restrictScalars ℝ) e he u := by
  change inverse (i.restrictScalars ℝ) e he (gram (i.restrictScalars ℝ) (c • u)) = _
  rw [gram_smul, inverse_smul]
  rfl

lemma cutoff_inverse_pair (z : Q) :
    ⟪z, cutoff (i.restrictScalars ℝ) e he
      (inverse (i.restrictScalars ℝ) e he z)⟫_ℂ =
      ⟪i (inverse (i.restrictScalars ℝ) e he z),
        i (inverse (i.restrictScalars ℝ) e he z)⟫_ℂ := by
  change ⟪z, inverseC i e he (gram (i.restrictScalars ℝ)
    (inverseC i e he z))⟫_ℂ = _
  rw [← inverseC_symm, gram_complex]
  exact i.adjoint_inner_right _ _

/-- Exact cancellation for the R33b generator. The two cutoff factors
are retained. No commutator identity from the source is used. -/
theorem cutoff_hamiltonian_cancel (L : Q →L[ℂ] Q) (u : Q) :
    (⟪L (cutoff (i.restrictScalars ℝ) e he u),
      cutoff (i.restrictScalars ℝ) e he
        (generator (i.restrictScalars ℝ) e he (forceMap L) u)⟫_ℂ).re = 0 := by
  change (⟪L (cutoff (i.restrictScalars ℝ) e he u),
    cutoff (i.restrictScalars ℝ) e he
      (inverse (i.restrictScalars ℝ) e he
        ((-Complex.I) • L (cutoff (i.restrictScalars ℝ) e he u)))⟫_ℂ).re = 0
  rw [inverse_smul, cutoff_smul, inner_smul_right, cutoff_inverse_pair]
  rw [Complex.mul_re]
  have hz := inner_self_im (𝕜 := ℂ)
    (i (inverse (i.restrictScalars ℝ) e he (L (cutoff (i.restrictScalars ℝ) e he u))))
  change (⟪i (inverse (i.restrictScalars ℝ) e he (L (cutoff (i.restrictScalars ℝ) e he u))),
    i (inverse (i.restrictScalars ℝ) e he (L (cutoff (i.restrictScalars ℝ) e he u)))⟫_ℂ).im = 0 at hz
  rw [hz]
  norm_num

end QuantumNLS.Ext005ComplexGramR34b
#print axioms QuantumNLS.Ext005ComplexGramR34b.cutoff_hamiltonian_cancel

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005ComplexGramR34b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005ComplexGramR34b." then
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
  Lean.logInfo m!"R34b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."

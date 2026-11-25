import QuantumNLS.Ext005IntervalChainR111
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-! R112: regularization for an arbitrary Hilbert form-domain embedding.
No sector decomposition, spectral cutoff, chain rule, or uniqueness is a premise.
The inverse is constructed by Lax--Milgram from the embedding Gram operator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped InnerProductSpace Topology
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005GramResolventR112
variable {Q H : Type*}
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Gram operator of the continuous embedding, on the form Hilbert space. -/
def gram (i : Q →L[ℝ] H) : Q →L[ℝ] Q := i.adjoint.comp i

lemma gram_pair (i : Q →L[ℝ] H) (u v : Q) :
    ⟪gram i u, v⟫_ℝ = ⟪i u, i v⟫_ℝ := by
  exact i.adjoint_inner_left v (i u)

lemma gram_symm (i : Q →L[ℝ] H) (u v : Q) :
    ⟪gram i u, v⟫_ℝ = ⟪u, gram i v⟫_ℝ := by
  calc
    _ = ⟪i u, i v⟫_ℝ := gram_pair i u v
    _ = ⟪i v, i u⟫_ℝ := real_inner_comm _ _
    _ = ⟪gram i v, u⟫_ℝ := (gram_pair i v u).symm
    _ = _ := real_inner_comm _ _

/-- The coercive Gram perturbation. -/
def perturbed (i : Q →L[ℝ] H) (e : ℝ) : Q →L[ℝ] Q :=
  gram i + e • ContinuousLinearMap.id ℝ Q

def coerciveForm (i : Q →L[ℝ] H) (e : ℝ) : Q →L[ℝ] Q →L[ℝ] ℝ :=
  (innerSL ℝ).comp (perturbed i e)

lemma perturbed_pair (i : Q →L[ℝ] H) (e : ℝ) (u v : Q) :
    ⟪perturbed i e u, v⟫_ℝ = ⟪i u, i v⟫_ℝ + e * ⟪u, v⟫_ℝ := by
  simp only [perturbed, add_apply, smul_apply, id_apply, inner_add_left,
    real_inner_smul_left, gram_pair]

lemma coercive (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e) :
    IsCoercive (coerciveForm i e) := by
  refine ⟨e, he, fun u => ?_⟩
  change e * ‖u‖ * ‖u‖ ≤ ⟪perturbed i e u, u⟫_ℝ
  rw [perturbed_pair, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg ‖i u‖]

/-- Constructed inverse of the Gram perturbation. -/
def inverse (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e) : Q →L[ℝ] Q :=
  (coercive i e he).continuousLinearEquivOfBilin.symm.toContinuousLinearMap

lemma perturbed_inverse (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e) (u : Q) :
    perturbed i e (inverse i e he u) = u := by
  apply ext_inner_right ℝ
  intro v
  have h := (coercive i e he).continuousLinearEquivOfBilin_apply (inverse i e he u) v
  rw [show (coercive i e he).continuousLinearEquivOfBilin (inverse i e he u) = u from
    (coercive i e he).continuousLinearEquivOfBilin.apply_symm_apply u] at h
  exact h.symm

lemma inverse_perturbed (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e) (u : Q) :
    inverse i e he (perturbed i e u) = u := by
  have h : perturbed i e u = (coercive i e he).continuousLinearEquivOfBilin u := by
    apply ext_inner_right ℝ
    intro v
    exact ((coercive i e he).continuousLinearEquivOfBilin_apply u v).symm
  rw [h]
  exact (coercive i e he).continuousLinearEquivOfBilin.symm_apply_apply u

lemma inverse_symm (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e) (u v : Q) :
    ⟪inverse i e he u, v⟫_ℝ = ⟪u, inverse i e he v⟫_ℝ := by
  conv_lhs => rw [← perturbed_inverse i e he v]
  conv_rhs => rw [← perturbed_inverse i e he u]
  rw [real_inner_comm, perturbed_pair, perturbed_pair,
    real_inner_comm (i (inverse i e he u)), real_inner_comm (inverse i e he u)]

/-- Form-space regularizer; its construction is not an extra hypothesis. -/
def cutoff (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e) : Q →L[ℝ] Q :=
  (inverse i e he).comp (gram i)

lemma cutoff_eq (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e) (u : Q) :
    cutoff i e he u = u - e • inverse i e he u := by
  have h := inverse_perturbed i e he u
  simp only [perturbed, add_apply, smul_apply, id_apply, map_add, map_smul] at h
  change cutoff i e he u + e • inverse i e he u = u at h
  exact eq_sub_of_add_eq h

lemma gram_inverse (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e) (u : Q) :
    gram i (inverse i e he u) = cutoff i e he u := by
  have h := perturbed_inverse i e he u
  simp only [perturbed, add_apply, smul_apply, id_apply] at h
  rw [cutoff_eq]
  exact eq_sub_of_add_eq h

lemma cutoff_symm (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e) (u v : Q) :
    ⟪cutoff i e he u, v⟫_ℝ = ⟪u, cutoff i e he v⟫_ℝ := by
  rw [cutoff_eq, cutoff_eq, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, inverse_symm]

lemma cutoff_norm_le (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e) (u : Q) :
    ‖cutoff i e he u‖ ≤ ‖u‖ := by
  have hx : u = cutoff i e he u + e • inverse i e he u := by
    rw [cutoff_eq]; abel
  have hp : 0 ≤ ⟪cutoff i e he u, inverse i e he u⟫_ℝ := by
    rw [← gram_inverse, gram_pair, real_inner_self_eq_norm_sq]
    positivity
  have hn := norm_add_sq_real (cutoff i e he u) (e • inverse i e he u)
  rw [← hx, real_inner_smul_right] at hn
  nlinarith [sq_nonneg ‖e • inverse i e he u‖, norm_nonneg u,
    norm_nonneg (cutoff i e he u)]

/-- Regularization from the antidual's Riesz coordinates into H. -/
def smooth (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e) : Q →L[ℝ] H :=
  i.comp (inverse i e he)

def physicalCutoff (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e) : H →L[ℝ] H :=
  (smooth i e he).comp i.adjoint

lemma physicalCutoff_embed (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e) (u : Q) :
    physicalCutoff i e he (i u) = i (cutoff i e he u) := rfl

lemma pairing_identity (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e) (u g : Q) :
    ⟪physicalCutoff i e he (i u), smooth i e he g⟫_ℝ =
      ⟪cutoff i e he (cutoff i e he u), g⟫_ℝ := by
  rw [physicalCutoff_embed]
  change ⟪i (cutoff i e he u), i (inverse i e he g)⟫_ℝ = _
  rw [← gram_pair, ← inverse_symm]
  rfl

lemma physicalCutoff_norm_le (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e) (x : H) :
    ‖physicalCutoff i e he x‖ ≤ ‖x‖ := by
  let v := inverse i e he (i.adjoint x)
  have hp := perturbed_pair i e v v
  rw [perturbed_inverse] at hp
  rw [i.adjoint_inner_left, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at hp
  have hb := real_inner_le_norm x (i v)
  have hnon : 0 ≤ e * ‖v‖ ^ 2 := mul_nonneg he.le (sq_nonneg _)
  change ‖i v‖ ≤ ‖x‖
  nlinarith [norm_nonneg (i v), norm_nonneg x]

lemma cutoff_gram_error (i : Q →L[ℝ] H) (e : ℝ) (he : 0 < e) (u : Q) :
    ‖cutoff i e he (gram i u) - gram i u‖ ≤ e * ‖u‖ := by
  rw [cutoff_eq, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos he]
  exact mul_le_mul_of_nonneg_left (cutoff_norm_le i e he u) he.le

end QuantumNLS.Ext005GramResolventR112

#print axioms QuantumNLS.Ext005GramResolventR112.cutoff_norm_le
#print axioms QuantumNLS.Ext005GramResolventR112.pairing_identity

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005GramResolventR112." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005GramResolventR112." then
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
  Lean.logInfo m!"R112 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."

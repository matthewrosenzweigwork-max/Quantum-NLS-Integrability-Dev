import QuantumNLS.Ext006Blocks
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
FIN-CORE-BD-02, kernel construction, author sol_multi, round 2.
The input is an actual bounded real-linear symplectic automorphism for the
original complex structure. No block identities or inverse blocks are supplied
as hypotheses. This module first derives them from the imaginary inner product.
The analytic exponential and its normalization are separate obligations.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006SymplecticKernel
open Ext006Blocks
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local instance] InnerProductSpace.complexToReal

/-- Symplecticity for the report's fixed physical complex structure.
The factor 2 in DEF-015 cancels on both sides. -/
def Symplectic (S : H →L[ℝ] H) : Prop :=
  ∀ x y, (inner ℂ (S x) (S y)).im = (inner ℂ x y).im

lemma J_adjoint : (J (E := H)).adjoint = -J := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp [real_inner_eq_re_inner, J_apply, inner_smul_left, inner_smul_right]

omit [CompleteSpace H] in
lemma J_comp_J : J (E := H) ∘L J = -ContinuousLinearMap.id ℝ H := by
  ext x
  exact J_sq x

omit [CompleteSpace H] in
lemma complexPart_comp (S T : H →L[ℝ] H) :
    complexPart (S ∘L T) = complexPart S ∘L complexPart T +
      antilinearPart S ∘L antilinearPart T := by
  ext x
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    complexPart_apply, antilinearPart_apply, map_smul, map_add, map_sub, J_sq, map_neg]
  module

omit [CompleteSpace H] in
lemma antilinearPart_comp (S T : H →L[ℝ] H) :
    antilinearPart (S ∘L T) = complexPart S ∘L antilinearPart T +
      antilinearPart S ∘L complexPart T := by
  ext x
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    complexPart_apply, antilinearPart_apply, map_smul, map_add, map_sub, J_sq, map_neg]
  module

omit [CompleteSpace H] in
@[simp] lemma complexPart_id : complexPart (ContinuousLinearMap.id ℝ H) =
    ContinuousLinearMap.id ℝ H := by
  ext x
  simp only [complexPart_apply, ContinuousLinearMap.id_apply, J_sq]
  module

omit [CompleteSpace H] in
@[simp] lemma antilinearPart_id : antilinearPart (ContinuousLinearMap.id ℝ H) = 0 := by
  ext x
  simp only [antilinearPart_apply, ContinuousLinearMap.id_apply, J_sq, add_neg_cancel, smul_zero, zero_apply]

lemma inverse_formula (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) :
    S.symm.toContinuousLinearMap = -(J ∘L S.toContinuousLinearMap.adjoint ∘L J) := by
  ext x
  apply ext_inner_right ℝ
  intro y
  have hs := hS (S.symm x) (J y)
  calc
    inner ℝ (S.symm x) y = (inner ℂ x (S (J y))).im := by
      simpa [real_inner_eq_re_inner, J_apply, inner_smul_right] using hs.symm
    _ = inner ℝ (S.toContinuousLinearMap.adjoint (J x)) (J y) := by
      rw [ContinuousLinearMap.adjoint_inner_left]
      simp [real_inner_eq_re_inner, J_apply, inner_smul_left]
    _ = inner ℝ (-(J (S.toContinuousLinearMap.adjoint (J x)))) y := by
      simp [real_inner_eq_re_inner, J_apply, inner_smul_left, inner_smul_right]

lemma complexPart_inverse (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) :
    complexPart S.symm.toContinuousLinearMap = (complexPart S.toContinuousLinearMap).adjoint := by
  simp only [complexPart, map_smulₛₗ, starRingEnd_apply, star_trivial, map_sub]
  simp only [ContinuousLinearMap.adjoint_comp, J_adjoint]
  rw [inverse_formula S hS]
  ext x
  simp only [smul_apply, sub_apply,
    neg_apply, ContinuousLinearMap.comp_apply, map_neg, J_sq]
  module

lemma antilinearPart_inverse (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) :
    antilinearPart S.symm.toContinuousLinearMap = -(antilinearPart S.toContinuousLinearMap).adjoint := by
  simp only [antilinearPart, map_smulₛₗ, starRingEnd_apply, star_trivial, map_add]
  simp only [ContinuousLinearMap.adjoint_comp, J_adjoint]
  rw [inverse_formula S hS]
  ext x
  simp only [smul_apply, add_apply,
    neg_apply, ContinuousLinearMap.comp_apply, map_neg, J_sq]
  module

lemma canonical_left (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) :
    (complexPart S.toContinuousLinearMap).adjoint ∘L complexPart S.toContinuousLinearMap -
      (antilinearPart S.toContinuousLinearMap).adjoint ∘L antilinearPart S.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ H := by
  have h := complexPart_comp S.symm.toContinuousLinearMap S.toContinuousLinearMap
  rw [ContinuousLinearEquiv.coe_symm_comp_coe, complexPart_id,
    complexPart_inverse S hS, antilinearPart_inverse S hS] at h
  simpa only [ContinuousLinearMap.neg_comp, sub_eq_add_neg] using h.symm

lemma canonical_right (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) :
    complexPart S.toContinuousLinearMap ∘L (complexPart S.toContinuousLinearMap).adjoint -
      antilinearPart S.toContinuousLinearMap ∘L (antilinearPart S.toContinuousLinearMap).adjoint =
      ContinuousLinearMap.id ℝ H := by
  have h := complexPart_comp S.toContinuousLinearMap S.symm.toContinuousLinearMap
  rw [ContinuousLinearEquiv.coe_comp_coe_symm, complexPart_id,
    complexPart_inverse S hS, antilinearPart_inverse S hS] at h
  simpa only [ContinuousLinearMap.comp_neg, sub_eq_add_neg] using h.symm

lemma canonical_cross (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) :
    (complexPart S.toContinuousLinearMap).adjoint ∘L antilinearPart S.toContinuousLinearMap =
      (antilinearPart S.toContinuousLinearMap).adjoint ∘L complexPart S.toContinuousLinearMap := by
  have h := antilinearPart_comp S.symm.toContinuousLinearMap S.toContinuousLinearMap
  rw [ContinuousLinearEquiv.coe_symm_comp_coe, antilinearPart_id,
    complexPart_inverse S hS, antilinearPart_inverse S hS] at h
  exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h.symm)

lemma norm_identity (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) (x : H) :
    ‖complexPart S.toContinuousLinearMap x‖^2 - ‖antilinearPart S.toContinuousLinearMap x‖^2 = ‖x‖^2 := by
  have h := congrArg (fun T : H →L[ℝ] H => inner ℝ (T x) x) (canonical_left S hS)
  simpa only [sub_apply, ContinuousLinearMap.comp_apply,
    inner_sub_left, ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq,
    ContinuousLinearMap.id_apply] using h

lemma adjoint_norm_identity (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) (x : H) :
    ‖(complexPart S.toContinuousLinearMap).adjoint x‖^2 -
      ‖(antilinearPart S.toContinuousLinearMap).adjoint x‖^2 = ‖x‖^2 := by
  have h := congrArg (fun T : H →L[ℝ] H => inner ℝ x (T x)) (canonical_right S hS)
  simpa only [sub_apply, ContinuousLinearMap.comp_apply, inner_sub_right,
    ← ContinuousLinearMap.adjoint_inner_left (complexPart S.toContinuousLinearMap),
    ← ContinuousLinearMap.adjoint_inner_left (antilinearPart S.toContinuousLinearMap),
    real_inner_self_eq_norm_sq,
    ContinuousLinearMap.id_apply] using h

lemma complexPart_bijective (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) :
    Function.Bijective (complexPart S.toContinuousLinearMap) := by
  let A := complexPart S.toContinuousLinearMap
  have hnorm (x : H) : ‖x‖ ≤ ‖A x‖ := by
    have := norm_identity S hS x
    nlinarith [sq_nonneg ‖antilinearPart S.toContinuousLinearMap x‖, norm_nonneg x, norm_nonneg (A x)]
  have hanti : AntilipschitzWith 1 A := A.antilipschitz_of_bound (by simpa using hnorm)
  rw [ContinuousLinearMap.bijective_iff_dense_range_and_antilipschitz]
  refine ⟨?_, ⟨1, hanti⟩⟩
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro x hx
  have hz : A.adjoint x = 0 := by
    have hx' : x ∈ A.rangeᗮ := hx
    rw [ContinuousLinearMap.orthogonal_range] at hx'
    exact hx'
  have hi := adjoint_norm_identity S hS x
  change ‖A.adjoint x‖^2 - _ = ‖x‖^2 at hi
  rw [hz, norm_zero, zero_pow (by decide)] at hi
  have : ‖x‖ = 0 := by nlinarith [sq_nonneg ‖(antilinearPart S.toContinuousLinearMap).adjoint x‖, norm_nonneg x]
  exact norm_eq_zero.mp this

/-- Constructed complex block inverse, temporarily carried over the reals. -/
def linearBlock (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) : H ≃L[ℝ] H :=
  ContinuousLinearEquiv.ofBijective (complexPart S.toContinuousLinearMap)
    (LinearMap.ker_eq_bot.mpr (complexPart_bijective S hS).injective)
    (LinearMap.range_eq_top.mpr (complexPart_bijective S hS).surjective)

@[simp] lemma linearBlock_apply (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) (x : H) :
    linearBlock S hS x = complexPart S.toContinuousLinearMap x := rfl

/-- Intrinsic antilinear squeeze operator B A^{-1}. -/
def kernel (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) : H →L[ℝ] H :=
  antilinearPart S.toContinuousLinearMap ∘L (linearBlock S hS).symm.toContinuousLinearMap

lemma kernel_anticommutes_J (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) (x : H) :
    kernel S hS (J x) = -J (kernel S hS x) := by
  have hi : (linearBlock S hS).symm (J x) = J ((linearBlock S hS).symm x) := by
    apply (linearBlock S hS).injective
    simp only [ContinuousLinearEquiv.apply_symm_apply, linearBlock_apply,
      complexPart_commutes_J]
    rw [← linearBlock_apply S hS, ContinuousLinearEquiv.apply_symm_apply]
  change antilinearPart S.toContinuousLinearMap ((linearBlock S hS).symm (J x)) = _
  rw [hi]
  exact
    antilinearPart_anticommutes_J S.toContinuousLinearMap ((linearBlock S hS).symm x)

lemma kernel_symmetric (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) :
    (kernel S hS).adjoint = kernel S hS := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  let u := (linearBlock S hS).symm x
  let v := (linearBlock S hS).symm y
  have hx : x = complexPart S.toContinuousLinearMap u :=
    ((linearBlock S hS).apply_symm_apply x).symm
  have hy : y = complexPart S.toContinuousLinearMap v :=
    ((linearBlock S hS).apply_symm_apply y).symm
  have hc := congrArg (fun T : H →L[ℝ] H => inner ℝ (T u) v) (canonical_cross S hS)
  change inner ℝ (antilinearPart S.toContinuousLinearMap u) y =
    inner ℝ x (antilinearPart S.toContinuousLinearMap v)
  rw [hx, hy]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left] using hc

lemma linearBlock_inverse_J (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) (x : H) :
    (linearBlock S hS).symm (J x) = J ((linearBlock S hS).symm x) := by
  apply (linearBlock S hS).injective
  simp only [ContinuousLinearEquiv.apply_symm_apply, linearBlock_apply,
    complexPart_commutes_J]
  rw [← linearBlock_apply S hS, ContinuousLinearEquiv.apply_symm_apply]

lemma linearBlock_inverse_norm_le (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) :
    ‖(linearBlock S hS).symm.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have h := norm_identity S hS ((linearBlock S hS).symm x)
  rw [← linearBlock_apply S hS, ContinuousLinearEquiv.apply_symm_apply] at h
  change ‖(linearBlock S hS).symm x‖ ≤ 1 * ‖x‖
  nlinarith [norm_nonneg x, norm_nonneg ((linearBlock S hS).symm x),
    sq_nonneg ‖antilinearPart S.toContinuousLinearMap ((linearBlock S hS).symm x)‖]

lemma kernel_complex_symmetric (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) (x y : H) :
    inner ℂ x (kernel S hS y) = inner ℂ y (kernel S hS x) := by
  have hr (u v : H) : inner ℝ u (kernel S hS v) = inner ℝ v (kernel S hS u) := by
    rw [← ContinuousLinearMap.adjoint_inner_left, kernel_symmetric S hS, real_inner_comm]
  apply Complex.ext
  · exact hr x y
  · have hi := hr (J x) y
    rw [kernel_anticommutes_J S hS] at hi
    simpa [real_inner_eq_re_inner, J_apply, inner_smul_left, inner_smul_right] using hi

/-- Uniform strict contraction, derived from the bounded complex block.
The extra 1 in the denominator also covers the zero Hilbert space. -/
lemma kernel_norm_lt_one (S : H ≃L[ℝ] H) (hS : Symplectic S.toContinuousLinearMap) :
    ‖kernel S hS‖ < 1 := by
  let a := ‖complexPart S.toContinuousLinearMap‖ + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : 1 ≤ a := by dsimp [a]; linarith [norm_nonneg (complexPart S.toContinuousLinearMap)]
  have hd : 0 < a⁻¹ := inv_pos.mpr ha
  have hd1 : a⁻¹ ≤ 1 := (inv_le_one₀ ha).mpr ha1
  have hc : 0 ≤ 1 - a⁻¹^2 := by nlinarith
  have hbound (x : H) : ‖kernel S hS x‖ ≤ Real.sqrt (1-a⁻¹^2) * ‖x‖ := by
    let u := (linearBlock S hS).symm x
    have hu : complexPart S.toContinuousLinearMap u = x := (linearBlock S hS).apply_symm_apply x
    have hn := norm_identity S hS u
    rw [hu] at hn
    have hup : ‖x‖ ≤ a * ‖u‖ := by
      have hh := (complexPart S.toContinuousLinearMap).le_opNorm u
      rw [hu] at hh
      dsimp [a]
      nlinarith [norm_nonneg u]
    have hlo : a⁻¹ * ‖x‖ ≤ ‖u‖ := (inv_mul_le_iff₀ ha).mpr hup
    have hs : (a⁻¹*‖x‖)^2 ≤ ‖u‖^2 :=
      pow_le_pow_left₀ (by positivity) hlo 2
    have he : ‖kernel S hS x‖ = ‖antilinearPart S.toContinuousLinearMap u‖ := rfl
    rw [he]
    have hsq := Real.sq_sqrt hc
    have hnon := Real.sqrt_nonneg (1-a⁻¹^2)
    have hxx := norm_nonneg x
    have hbb := norm_nonneg (antilinearPart S.toContinuousLinearMap u)
    nlinarith [mul_nonneg hnon hxx]
  have hop := ContinuousLinearMap.opNorm_le_bound (kernel S hS) (Real.sqrt_nonneg _) hbound
  refine hop.trans_lt ?_
  apply (Real.sqrt_lt' zero_lt_one).mpr
  nlinarith [sq_pos_of_pos hd]

end QuantumNLS.Ext006SymplecticKernel

#print axioms QuantumNLS.Ext006SymplecticKernel.J_adjoint
#print axioms QuantumNLS.Ext006SymplecticKernel.J_comp_J
#print axioms QuantumNLS.Ext006SymplecticKernel.complexPart_comp
#print axioms QuantumNLS.Ext006SymplecticKernel.antilinearPart_comp
#print axioms QuantumNLS.Ext006SymplecticKernel.complexPart_id
#print axioms QuantumNLS.Ext006SymplecticKernel.antilinearPart_id
#print axioms QuantumNLS.Ext006SymplecticKernel.inverse_formula
#print axioms QuantumNLS.Ext006SymplecticKernel.complexPart_inverse
#print axioms QuantumNLS.Ext006SymplecticKernel.antilinearPart_inverse
#print axioms QuantumNLS.Ext006SymplecticKernel.canonical_left
#print axioms QuantumNLS.Ext006SymplecticKernel.canonical_right
#print axioms QuantumNLS.Ext006SymplecticKernel.canonical_cross
#print axioms QuantumNLS.Ext006SymplecticKernel.norm_identity
#print axioms QuantumNLS.Ext006SymplecticKernel.adjoint_norm_identity
#print axioms QuantumNLS.Ext006SymplecticKernel.complexPart_bijective
#print axioms QuantumNLS.Ext006SymplecticKernel.linearBlock_apply
#print axioms QuantumNLS.Ext006SymplecticKernel.kernel_anticommutes_J
#print axioms QuantumNLS.Ext006SymplecticKernel.kernel_symmetric
#print axioms QuantumNLS.Ext006SymplecticKernel.linearBlock_inverse_J
#print axioms QuantumNLS.Ext006SymplecticKernel.linearBlock_inverse_norm_le
#print axioms QuantumNLS.Ext006SymplecticKernel.kernel_complex_symmetric
#print axioms QuantumNLS.Ext006SymplecticKernel.kernel_norm_lt_one

-- COMPLETE NAMESPACE AUDIT
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006SymplecticKernel." then
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
  Lean.logInfo m!"Ext006SymplecticKernel audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."

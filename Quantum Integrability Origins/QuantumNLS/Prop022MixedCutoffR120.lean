import QuantumNLS.Prop022MomentTailR120

/-! The mixed-cutoff error in the actual physical quadratic form. All
cutoffs on the two arguments are retained until the tail estimates apply. -/
set_option Elab.async false
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 160000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap
namespace QuantumNLS.Prop022MixedCutoffR120
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments
open Ext005MomentEnergyR108 Ext005FormCutoffR109 Ext005FormScaleR109
open Ext005PhysicalNumberFormR114 Ext005PhysicalSymmetryR114 Ext005AlgebraicFormR114
open Ext005ComplexRieszR113 Prop022CutoffHamiltonianR115 Prop022MomentTailR120
open Prop022CutoffEvolutionR119 Prop022FactorialCoefficientsR115 Prop022ActualProfileR117
variable {L : ℝ} [Fact (0 < L)]
local instance (priority := 1200) opNormed : NormedAddCommGroup (HN L 1 →L[ℂ] HN L 1) := inferInstance
local instance (priority := 1200) fockOpNormed : NormedAddCommGroup (Fock L →L[ℂ] Fock L) := inferInstance

abbrev first (x : momentDomain (L := L) 3) : momentDomain (L := L) 1 :=
  ⟨x.val, domain_mono (by omega) x.property⟩

lemma first_root_le (x : momentDomain (L := L) 3) :
    ‖momentRoot 1 (first x)‖ ≤ ‖momentRoot 3 x‖ := by
  apply lp.norm_mono (by norm_num)
  intro n
  change ‖(Real.sqrt (momentWeight 1 n) : ℂ) • x.val n‖ ≤
    ‖(Real.sqrt (momentWeight 3 n) : ℂ) • x.val n‖
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (weight_mono (by omega) n)) (norm_nonneg _)

lemma quadratic_bound (a : HN L 1 →L[ℂ] HN L 1) (ha : a.adjoint = a)
    (b : HN L 2) (u v : Fock L) :
    ‖quadraticContinuous a b u v‖ ≤ (3 * (‖a‖+‖b‖)) * ‖u‖ * ‖v‖ := by
  let raw : RawForm (Fock L) :=
    { toFun u := (quadraticContinuous a b u).toLinearMap
      map_add' u v := by ext w; simp
      map_smul' c u := by ext w; simp }
  exact raw_bound raw _ (by positivity) (quadraticContinuous_symmetric a ha b)
    (fun u => (Complex.abs_re_le_norm _).trans (quadraticContinuous_diagonal_bound a b u)) u v

lemma supported_root (j N : ℕ) (x : momentDomain (L := L) j)
    (hx : cutoff N x.val = x.val) : rootCutoff j N x.val = momentRoot j x := by
  rw [rootCutoff_on_domain j N x]
  exact congrArg (momentRoot j) (Subtype.ext hx)

section Algebra
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
lemma form_sub_decomposition (q : H →L[ℂ] H →L⋆[ℂ] ℂ) (X Y Yn Xk : H) :
    q Yn X-q Y Xk = q (Yn-Y) X+q Y (X-Xk) := by
  simp only [map_sub, sub_apply]
  ring

lemma form_error_bound (q : H →L[ℂ] H →L⋆[ℂ] ℂ) (X Y Yn Xk : H) (C R rn rk : ℝ)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hrn : 0 ≤ rn) (_hrk : 0 ≤ rk)
    (hq : ∀ u v, ‖q u v‖ ≤ C*‖u‖*‖v‖)
    (hX : ‖X‖ ≤ R) (hY : ‖Y‖ ≤ R)
    (heY : ‖Yn-Y‖ ≤ rn*R) (heX : ‖X-Xk‖ ≤ rk*R) :
    ‖q Yn X-q Y Xk‖ ≤ C*R^2*(rn+rk) := by
  calc
    _ = ‖q (Yn-Y) X+q Y (X-Xk)‖ := congrArg norm (form_sub_decomposition q X Y Yn Xk)
    _ ≤ ‖q (Yn-Y) X‖+‖q Y (X-Xk)‖ := norm_add_le _ _
    _ ≤ C*‖Yn-Y‖*‖X‖+C*‖Y‖*‖X-Xk‖ := add_le_add (hq _ _) (hq _ _)
    _ ≤ C*(rn*R)*R+C*R*(rk*R) := by gcongr
    _ = _ := by ring
end Algebra

lemma mixed_pair_identity (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2)
    (N K : ℕ) (x y : momentDomain (L := L) 1)
    (hx : cutoff N x.val = x.val) (hy : cutoff K y.val = y.val) :
    ⟪x.val, cutoffHamiltonian a b N y.val-cutoffHamiltonian a b K y.val⟫_ℂ =
      quadraticContinuous a b (rootCutoff 1 N y.val) (momentRoot 1 x) -
        quadraticContinuous a b (momentRoot 1 y) (rootCutoff 1 K x.val) := by
  let X := momentRoot 1 x
  let Y := momentRoot 1 y
  let Xk := rootCutoff 1 K x.val
  let Yn := rootCutoff 1 N y.val
  have hnx : rootCutoff 1 N x.val = X := supported_root 1 N x hx
  have hky : rootCutoff 1 K y.val = Y := supported_root 1 K y hy
  calc
    _ = quadraticContinuous a b Yn (rootCutoff 1 N x.val) -
        quadraticContinuous a b (rootCutoff 1 K y.val) Xk := by
      exact (inner_sub_right x.val _ _).trans
        (congrArg₂ (fun c d : ℂ => c-d) (cutoff_pair a b N x.val y.val) (cutoff_pair a b K x.val y.val))
    _ = quadraticContinuous a b Yn X - quadraticContinuous a b Y Xk :=
      congrArg₂ (fun c d : ℂ => c-d)
        (congrArg (fun z : Fock L => quadraticContinuous a b Yn z) hnx)
        (congrArg (fun z : Fock L => quadraticContinuous a b z Xk) hky)

lemma root_error_bound (N : ℕ) (x : momentDomain (L := L) 3) (R : ℝ)
    (hx : ‖momentRoot 3 x‖ ≤ R) :
    ‖momentRoot 1 (first x)-rootCutoff 1 N x.val‖ ≤ ((N : ℝ)+1)⁻¹*R := by
  exact (root_truncation_error 1 N x).trans (mul_le_mul_of_nonneg_left hx (by positivity))

lemma first_matrix_bound (a : HN L 1 →L[ℂ] HN L 1) (ha : a.adjoint = a)
    (b : HN L 2) (N K : ℕ) (x y : momentDomain (L := L) 1)
    (hx : cutoff N x.val = x.val) (hy : cutoff K y.val = y.val)
    (R : ℝ) (hR : 0 ≤ R) (hX : ‖momentRoot 1 x‖ ≤ R) (hY : ‖momentRoot 1 y‖ ≤ R)
    (heY : ‖momentRoot 1 y-rootCutoff 1 N y.val‖ ≤ ((N : ℝ)+1)⁻¹*R)
    (heX : ‖momentRoot 1 x-rootCutoff 1 K x.val‖ ≤ ((K : ℝ)+1)⁻¹*R) :
    ‖⟪x.val, cutoffHamiltonian a b N y.val-cutoffHamiltonian a b K y.val⟫_ℂ‖ ≤
      (3 * (‖a‖+‖b‖)) * R^2 * (((N : ℝ)+1)⁻¹+((K : ℝ)+1)⁻¹) := by
  have he := mixed_pair_identity a b N K x y hx hy
  have heY' : ‖rootCutoff 1 N y.val-momentRoot 1 y‖ ≤ ((N : ℝ)+1)⁻¹*R :=
    (norm_sub_rev _ _).le.trans heY
  exact (congrArg norm he).le.trans
    (form_error_bound (quadraticContinuous a b) (momentRoot 1 x) (momentRoot 1 y)
      (rootCutoff 1 N y.val) (rootCutoff 1 K x.val) (3*(‖a‖+‖b‖)) R
      ((N : ℝ)+1)⁻¹ ((K : ℝ)+1)⁻¹ (by positivity) hR (by positivity) (by positivity)
      (quadratic_bound a ha b) hX hY heY' heX)

/-- The two different compressions have a small mixed matrix element on
vectors supported in their own cutoff, with an explicit inverse-cutoff rate. -/
theorem mixed_pair_bound (a : HN L 1 →L[ℂ] HN L 1) (ha : a.adjoint = a)
    (b : HN L 2) (N K : ℕ) (x y : momentDomain (L := L) 3)
    (hx : cutoff N x.val = x.val) (hy : cutoff K y.val = y.val)
    (R : ℝ) (hR : 0 ≤ R) (hxr : ‖momentRoot 3 x‖ ≤ R) (hyr : ‖momentRoot 3 y‖ ≤ R) :
    ‖⟪x.val, cutoffHamiltonian a b N y.val-cutoffHamiltonian a b K y.val⟫_ℂ‖ ≤
      (3 * (‖a‖+‖b‖)) * R^2 * (((N : ℝ)+1)⁻¹+((K : ℝ)+1)⁻¹) := by
  rcases x with ⟨x, hxd⟩
  rcases y with ⟨y, hyd⟩
  refine first_matrix_bound a ha b N K
    ⟨x, domain_mono (by decide : 1 ≤ 3) hxd⟩
    ⟨y, domain_mono (by decide : 1 ≤ 3) hyd⟩ hx hy R hR ?_ ?_ ?_ ?_
  · exact (first_root_le ⟨x, hxd⟩).trans hxr
  · exact (first_root_le ⟨y, hyd⟩).trans hyr
  · exact root_error_bound N ⟨y, hyd⟩ R hyr
  · exact root_error_bound K ⟨x, hxd⟩ R hxr

end QuantumNLS.Prop022MixedCutoffR120
#print axioms QuantumNLS.Prop022MixedCutoffR120.mixed_pair_bound
#print axioms QuantumNLS.Prop022MixedCutoffR120.first_root_le

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022MixedCutoffR120." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022MixedCutoffR120." then
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
  Lean.logInfo m!"R120 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."

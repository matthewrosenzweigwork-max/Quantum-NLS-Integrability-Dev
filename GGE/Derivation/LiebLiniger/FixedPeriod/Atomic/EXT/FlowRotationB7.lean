import LiebLiniger.FixedPeriod.Atomic.EXT.FlowRotationB6

/-! # Finite coordinate phase invariance of the literal physical Hamiltonian

Integrate the single-coordinate zero derivative at every rotated base point,
then perform a finite induction over all coordinate phases.
-/

set_option autoImplicit false
noncomputable section
namespace LiebLiniger.FixedPeriod.EXT

set_option maxHeartbeats 400000 in
/-- A single coordinate can be rotated by any real phase without changing the
literal physical finite-plane energy. -/
theorem HLambda_singlePhaseInvariant38 (Λ : Finset ℤ) (w : Λ → ℂ) (i : Λ) (a : ℝ) :
    HΛ Λ (fun j => if j = i then Complex.exp ((a : ℂ) * Complex.I) * w j else w j) =
      HΛ Λ w := by
  classical
  let f := fun b : ℝ => HΛ Λ (fun j => if j = i then
    Complex.exp (-(b : ℂ) * Complex.I) * w j else w j)
  have hd (b : ℝ) : HasDerivAt f 0 b := by
    let v : Λ → ℂ := fun j => if j = i then
      Complex.exp (-(b : ℂ) * Complex.I) * w j else w j
    have hz : HasDerivAt (fun c : ℝ => HΛ Λ (fun j => if j = i then
        Complex.exp (-(c : ℂ) * Complex.I) * v j else v j)) 0 (b - b) := by
      simpa only [sub_self] using HLambda_singlePhase_derivative_zero38 Λ v i
    have hh := hz.comp_sub_const b b
    have he : (fun c : ℝ => HΛ Λ (fun j => if j = i then
        Complex.exp (-((c - b : ℝ) : ℂ) * Complex.I) * v j else v j)) = f := by
      funext c
      dsimp only [f]
      apply congrArg (HΛ Λ)
      funext j
      by_cases hj : j = i
      · simp only [hj, ite_true, v, ← mul_assoc, ← Complex.exp_add]
        apply congrArg (fun z : ℂ => Complex.exp z * w i)
        push_cast
        ring
      · simp only [hj, ite_false, v]
    change HasDerivAt (fun c : ℝ => HΛ Λ (fun j => if j = i then
      Complex.exp (-((c - b : ℝ) : ℂ) * Complex.I) * v j else v j)) 0 b at hh
    rw [he] at hh
    exact hh
  have hc := is_const_of_deriv_eq_zero (fun b => (hd b).differentiableAt)
    (fun b => (hd b).deriv) (-a) 0
  simpa only [f, Complex.ofReal_neg, neg_neg, Complex.ofReal_zero, neg_zero,
    zero_mul, Complex.exp_zero, one_mul, ite_self] using hc

set_option maxHeartbeats 400000 in
/-- All finite coordinate phases preserve the literal physical Hamiltonian HΛ,
for every finite integer set and every vector, including collapsed coordinates. -/
theorem HLambda_phaseInvariant38 :
    ∀ (Λ : Finset ℤ) (w : Λ → ℂ) (θ : Λ → ℝ),
      HΛ Λ (fun i => Complex.exp ((θ i : ℂ) * Complex.I) * w i) = HΛ Λ w := by
  intro Λ w θ
  classical
  have hs (s : Finset Λ) :
      HΛ Λ (fun j => if j ∈ s then Complex.exp ((θ j : ℂ) * Complex.I) * w j else w j) =
        HΛ Λ w := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.notMem_empty, ite_false]
    | @insert i s hi ih =>
      have hh := HLambda_singlePhaseInvariant38 Λ
        (fun j => if j ∈ s then Complex.exp ((θ j : ℂ) * Complex.I) * w j else w j) i (θ i)
      have he : (fun j : Λ => if j = i then Complex.exp ((θ i : ℂ) * Complex.I) *
          (if j ∈ s then Complex.exp ((θ j : ℂ) * Complex.I) * w j else w j)
          else (if j ∈ s then Complex.exp ((θ j : ℂ) * Complex.I) * w j else w j)) =
          fun j => if j ∈ insert i s then Complex.exp ((θ j : ℂ) * Complex.I) * w j else w j := by
        funext j
        by_cases hj : j = i
        · subst j
          simp only [hi, ite_false, ite_true, Finset.mem_insert_self]
        · simp only [Finset.mem_insert, hj, ite_false, false_or]
      rw [he] at hh
      exact hh.trans ih
  simpa only [Finset.mem_univ, ite_true] using hs Finset.univ

end LiebLiniger.FixedPeriod.EXT

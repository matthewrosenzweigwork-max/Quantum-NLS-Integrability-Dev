import NlsGge.ThirdConsultation.G1.G1098Host
import NlsGge.Atomic.G1.G1062
import NlsGge.Sobolev.PeriodicBridge
set_option autoImplicit false

open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38
open scoped BigOperators

                                                                   
                                                                                                    
                                                                                                       
                                                                                                   
                                                                                          
                                                                                                       

namespace NlsGge.Atomic.G1098Basis

open NlsGge.GKDefinitionDesign

noncomputable section

/-- Unit complex sign of the Fourier coefficient of the reference column (`-1` on the plus family,
`I * parity n` on the minus family). -/
def mixedSign (n : ℤ) (minus : Bool) : ℂ :=
  if minus then Complex.I * parity n else -1

/-- Normalized reference family: `mixedBasisVec (n, minus) = ‖mixedReference n minus‖⁻¹ • mixedReference n minus`. -/
def mixedBasisVec (j : ℤ × Bool) : PhysicalL2 :=
  ((‖mixedReference j.1 j.2‖⁻¹ : ℝ) : ℂ) • mixedReference j.1 j.2

theorem parity_eq_one_or_neg_one (n : ℤ) : parity n = 1 ∨ parity n = -1 := by
  rcases Int.even_or_odd n with h | h
  · exact Or.inl (by unfold parity; exact h.neg_one_zpow)
  · exact Or.inr (by unfold parity; exact h.neg_one_zpow)

theorem norm_mixedSign (n : ℤ) (minus : Bool) : ‖mixedSign n minus‖ = 1 := by
  rcases parity_eq_one_or_neg_one n with h | h <;> cases minus <;> simp [mixedSign, h]

theorem reflected_mixedReference (n : ℤ) (minus : Bool) :
    reflectedFourierL2 (mixedReference n minus) =
      lp.single 2 (-n) (if minus then 2 * Complex.I * parity n else -1) := by
  unfold mixedReference
  simp

theorem norm_mixedReference (n : ℤ) (minus : Bool) :
    ‖mixedReference n minus‖ = if minus then 2 else 1 := by
  unfold mixedReference
  rw [reflectedFourierL2.symm.norm_map, lp.norm_single (by norm_num)]
  rcases parity_eq_one_or_neg_one n with h | h <;> cases minus <;> simp [h]

theorem norm_mixedReference_pos (n : ℤ) (minus : Bool) : 0 < ‖mixedReference n minus‖ := by
  rw [norm_mixedReference]
  cases minus <;> norm_num

/-- The reflected image of the normalized basis vector is a unit Fourier mode with sign `mixedSign`. -/
theorem reflected_mixedBasisVec (j : ℤ × Bool) :
    reflectedFourierL2 (mixedBasisVec j) = lp.single 2 (-j.1) (mixedSign j.1 j.2) := by
  obtain ⟨n, minus⟩ := j
  unfold mixedBasisVec
  rw [map_smul, reflected_mixedReference, ← lp.single_smul, norm_mixedReference]
  congr 1
  cases minus
  · simp [mixedSign]
  · simp only [mixedSign, ite_true]
    push_cast
    ring

/-- Complex scalar multiplication by a real number is real scalar multiplication. -/
theorem real_smul_of_complex_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (r : ℝ) (x : E) : (r : ℂ) • x = r • x :=
  (RCLike.real_smul_eq_coe_smul (K := ℂ) r x).symm

/-- The real inner product of PhysicalL2 (an L2 integral of pointwise real inner products) is the
real part of the complex inner product: the real part passes through the integral. -/
theorem real_inner_PhysicalL2_eq_re (x y : PhysicalL2) :
    inner ℝ x y = RCLike.re (inner ℂ x y) := by
  rw [MeasureTheory.L2.inner_def (𝕜 := ℝ), MeasureTheory.L2.inner_def (𝕜 := ℂ),
    ← integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) x y)]
  congr 1

/-- Real inner product through the complex one of the transported vectors. -/
theorem real_inner_reflected (x y : PhysicalL2) :
    inner ℝ x y = RCLike.re (inner ℂ (reflectedFourierL2 x) (reflectedFourierL2 y)) := by
  rw [LinearIsometryEquiv.inner_map_map, real_inner_PhysicalL2_eq_re]

/-- Complex inner products of two Fourier modes: a Kronecker delta times the conjugate product. -/
theorem inner_single_single (k l : ℤ) (s t : ℂ) :
    inner ℂ (lp.single 2 k s : lp (fun _ : ℤ => ℂ) 2) (lp.single 2 l t) =
      if k = l then (starRingEnd ℂ) s * t else 0 := by
  rw [lp.inner_single_left, lp.coeFn_single, Pi.single_apply]
  split_ifs <;> simp [RCLike.inner_apply, mul_comm]

/-- Real orthonormality of the normalized reference family. -/
theorem inner_mixedBasisVec (i j : ℤ × Bool) :
    inner ℝ (mixedBasisVec i) (mixedBasisVec j) = if i = j then (1 : ℝ) else 0 := by
  rw [real_inner_reflected, reflected_mixedBasisVec, reflected_mixedBasisVec, inner_single_single]
  obtain ⟨n, a⟩ := i
  obtain ⟨m, b⟩ := j
  by_cases hnm : n = m
  · subst hnm
    rcases parity_eq_one_or_neg_one n with hp | hp <;> cases a <;> cases b <;>
      simp [mixedSign, hp]
  · simp [hnm]

theorem mixedBasisVec_orthonormal : Orthonormal ℝ mixedBasisVec := by
  rw [orthonormal_iff_ite]
  exact inner_mixedBasisVec

/-- The real span of the normalized family contains the pullback of the mode `lp.single k 1`. -/
theorem mem_span_symm_one (k : ℤ) :
    reflectedFourierL2.symm (lp.single 2 k (1 : ℂ)) ∈
      Submodule.span ℝ (Set.range mixedBasisVec) := by
  have e : reflectedFourierL2.symm (lp.single 2 k (1 : ℂ)) = -mixedBasisVec (-k, false) := by
    apply reflectedFourierL2.injective
    rw [LinearIsometryEquiv.apply_symm_apply, map_neg, reflected_mixedBasisVec]
    simp [mixedSign]
  rw [e]
  exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_range_self _))

/-- The real span of the normalized family contains the pullback of the mode `lp.single k I`. -/
theorem mem_span_symm_I (k : ℤ) :
    reflectedFourierL2.symm (lp.single 2 k Complex.I) ∈
      Submodule.span ℝ (Set.range mixedBasisVec) := by
  rcases parity_eq_one_or_neg_one (-k) with hp | hp
  · have e : reflectedFourierL2.symm (lp.single 2 k Complex.I) = mixedBasisVec (-k, true) := by
      apply reflectedFourierL2.injective
      rw [LinearIsometryEquiv.apply_symm_apply, reflected_mixedBasisVec]
      simp [mixedSign, hp]
    rw [e]
    exact Submodule.subset_span (Set.mem_range_self _)
  · have e : reflectedFourierL2.symm (lp.single 2 k Complex.I) = -mixedBasisVec (-k, true) := by
      apply reflectedFourierL2.injective
      rw [LinearIsometryEquiv.apply_symm_apply, map_neg, reflected_mixedBasisVec]
      simp [mixedSign, hp]
    rw [e]
    exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_range_self _))

theorem mem_span_symm_single (k : ℤ) (c : ℂ) :
    reflectedFourierL2.symm (lp.single 2 k c) ∈
      Submodule.span ℝ (Set.range mixedBasisVec) := by
  have hsplit : (lp.single 2 k c : lp (fun _ : ℤ => ℂ) 2) =
      (c.re : ℂ) • lp.single 2 k 1 + (c.im : ℂ) • lp.single 2 k Complex.I := by
    rw [← lp.single_smul, ← lp.single_smul, ← lp.single_add]
    congr 1
    rw [smul_eq_mul, smul_eq_mul, mul_one]
    exact (Complex.re_add_im c).symm
  have hs := congrArg reflectedFourierL2.symm hsplit
  rw [hs, map_add, map_smul, map_smul, real_smul_of_complex_smul, real_smul_of_complex_smul]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (mem_span_symm_one k))
    (Submodule.smul_mem _ _ (mem_span_symm_I k))

/-- Totality: the real span of the normalized family is dense in PhysicalL2. -/
theorem mixedBasisVec_dense :
    ⊤ ≤ (Submodule.span ℝ (Set.range mixedBasisVec)).topologicalClosure := by
  intro x _
  have hsum : Tendsto (fun s : Finset ℤ => ∑ k ∈ s, lp.single 2 k ((reflectedFourierL2 x) k : ℂ))
      atTop (𝓝 (reflectedFourierL2 x)) :=
    lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := (2 : ENNReal)) (by simp) (reflectedFourierL2 x)
  have ht : Tendsto (fun s : Finset ℤ =>
      reflectedFourierL2.symm (∑ k ∈ s, lp.single 2 k ((reflectedFourierL2 x) k : ℂ)))
      atTop (𝓝 (reflectedFourierL2.symm (reflectedFourierL2 x))) :=
    (reflectedFourierL2.symm.continuous.tendsto _).comp hsum
  have hcl : reflectedFourierL2.symm (reflectedFourierL2 x) ∈
      closure ((Submodule.span ℝ (Set.range mixedBasisVec) : Submodule ℝ PhysicalL2) :
        Set PhysicalL2) := by
    apply mem_closure_of_tendsto ht
    refine Filter.Eventually.of_forall fun s => ?_
    rw [map_sum]
    exact Submodule.sum_mem _ fun k _ => mem_span_symm_single k _
  rw [LinearIsometryEquiv.symm_apply_apply, ← Submodule.topologicalClosure_coe] at hcl
  exact hcl

/-- The normalized reference family as a real Hilbert basis of PhysicalL2. -/
def mixedRealBasis : HilbertBasis (ℤ × Bool) ℝ PhysicalL2 :=
  HilbertBasis.mk mixedBasisVec_orthonormal mixedBasisVec_dense

theorem mixedRealBasis_apply (j : ℤ × Bool) : mixedRealBasis j = mixedBasisVec j :=
  congrFun (HilbertBasis.coe_mk mixedBasisVec_orthonormal mixedBasisVec_dense) j

end

end NlsGge.Atomic.G1098Basis


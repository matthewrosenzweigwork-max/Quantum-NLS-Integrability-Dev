import Mathlib
import NlsGge.Atomic.G5.G5012Host
import NlsGge.Atomic.G5.G5012Sup1
import NlsGge.ThirdConsultation.G5.G5017Support1

/- G5-012 SUPPORT2 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5012Sup2.lean.
   Heads verbatim from Pro round 14 section "G5012/013": physicalFourierBasis_projection, physicalFourierBasis_orthonormal,
   physicalFourierBasis_dense_span, physicalFourierHilbertBasis (body verbatim), physicalFourierHilbertBasis_apply.
   Route: reflectedFourierL2.symm (single n c) = -(c * fourierLp (-n)); real orthonormality from the complex isometry and
   Re (conj c_i c_j); density from lp.hasSum_single transported through the isometry with Re/Im splitting. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GK38
open NlsGge.ThirdConsultation.G5017Support1

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem star_fourierLp_g5012 (n : ℤ) :
    star (fourierLp (T := (1 : ℝ)) 2 n : PhysicalL2) = fourierLp (T := (1 : ℝ)) 2 (-n) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (fourierLp (T := (1 : ℝ)) 2 n : PhysicalL2),
    coeFn_fourierLp (T := (1 : ℝ)) 2 n, coeFn_fourierLp (T := (1 : ℝ)) 2 (-n)] with x h1 h2 h3
  rw [h1]
  change star ((fourierLp (T := (1 : ℝ)) 2 n : PhysicalL2) x) =
    (fourierLp (T := (1 : ℝ)) 2 (-n) : PhysicalL2) x
  rw [h2, h3, fourier_neg]
  rfl

theorem reflected_symm_single_g5012 (n : ℤ) (c : ℂ) :
    reflectedFourierL2.symm (lp.single 2 n c) = -(c • (fourierLp (T := (1 : ℝ)) 2 (-n) : PhysicalL2)) := by
  have hsr : squareReflection (lp.single 2 n c) = lp.single 2 (-n) (-c) := by
    apply lp.ext
    funext m
    by_cases h : m = -n
    · subst h
      simp [squareReflection]
    · have h' : -m ≠ n := fun e => h (by rw [← e]; simp)
      simp [squareReflection, h, h']
  have e1 : reflectedFourierL2.symm (lp.single 2 n c) =
      physicalFourierL2.symm (squareReflection (lp.single 2 n c)) := rfl
  rw [e1, hsr]
  have e2 : physicalFourierL2.symm (lp.single 2 (-n) (-c)) =
      (-c) • (fourierBasis (T := (1 : ℝ)) (-n)) := by
    have h1 : (lp.single 2 (-n) (-c) : lp (fun _ : ℤ => ℂ) 2) =
        (-c) • (lp.single 2 (-n) (1 : ℂ) : lp (fun _ : ℤ => ℂ) 2) := by
      rw [← lp.single_smul]; simp
    show (fourierBasis (T := (1 : ℝ))).repr.symm (lp.single 2 (-n) (-c)) = _
    rw [h1, map_smul, HilbertBasis.repr_symm_single]
  rw [e2, coe_fourierBasis, neg_smul]

theorem physicalFourierBasis_projection (n : ℤ) :
  (1 / Real.sqrt 2 : ℝ) • pairGradientProjection (fourierRealBasisPlus n) =
      physicalFourierBasis (true, n) ∧
  (-1 / Real.sqrt 2 : ℝ) • pairGradientProjection (fourierRealBasisMinus n) =
      physicalFourierBasis (false, n) := by
  have hs : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have hc : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; simp
  have hcne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have key : ∀ (r : ℝ) (c : ℂ) (x : PhysicalL2), r • c • x = ((r : ℂ) * c) • x := by
    intro r c x; rw [mul_smul]; exact (Complex.coe_smul r (c • x)).symm
  set E : PhysicalL2 := (fourierLp (T := (1 : ℝ)) 2 (-n) : PhysicalL2) with hE
  set E' : PhysicalL2 := (fourierLp (T := (1 : ℝ)) 2 n : PhysicalL2) with hE'
  have hsE : star E' = E := star_fourierLp_g5012 n
  have e1 : fourierMode 1 n = ((0 : PhysicalL2), E) := by simp [fourierMode, hE]
  have e2 : fourierMode (-1) n = (E', (0 : PhysicalL2)) := by simp [fourierMode, hE']
  have hstar : ∀ (c : ℂ) (x : PhysicalL2), star (c • x) = (starRingEnd ℂ c) • star x := by
    intro c x; exact star_smul_lp c x
  have p1 : (fourierRealBasisPlus n).1 = (-1 / (Real.sqrt 2 : ℂ)) • E' := by
    simp [fourierRealBasisPlus, e1, e2]
  have p2 : (fourierRealBasisPlus n).2 = (-1 / (Real.sqrt 2 : ℂ)) • E := by
    simp [fourierRealBasisPlus, e1, e2]
  have m1 : (fourierRealBasisMinus n).1 = (-1 / (Complex.I * (Real.sqrt 2 : ℂ))) • (-E') := by
    simp [fourierRealBasisMinus, e1, e2]
  have m2 : (fourierRealBasisMinus n).2 = (-1 / (Complex.I * (Real.sqrt 2 : ℂ))) • E := by
    simp [fourierRealBasisMinus, e1, e2]
  have hP : pairGradientProjection (fourierRealBasisPlus n) =
      ((-1 / (Real.sqrt 2 : ℂ)) + (-1 / (Real.sqrt 2 : ℂ))) • E := by
    unfold pairGradientProjection
    rw [p1, p2, hstar, hsE, add_smul]
    congr 2
    simp
  have hM : pairGradientProjection (fourierRealBasisMinus n) =
      ((-1 / (Complex.I * (Real.sqrt 2 : ℂ))) + (-1 / (Complex.I * (Real.sqrt 2 : ℂ)))) • E := by
    unfold pairGradientProjection
    rw [m1, m2, hstar, show star (-E') = -star E' from starLp.map_neg E', hsE, add_smul]
    congr 1
    rw [smul_neg, ← neg_smul]
    congr 1
    simp only [map_div₀, map_neg, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal]
    field_simp
    try ring
  unfold physicalFourierBasis
  simp only [if_true, if_false, Bool.false_eq_true, reflected_symm_single_g5012]
  refine ⟨?_, ?_⟩
  · rw [hP, key]
    have : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((-1 / (Real.sqrt 2 : ℂ)) + (-1 / (Real.sqrt 2 : ℂ))) = -1 := by
      push_cast
      field_simp
      rw [hc]; ring
    rw [this]; simp only [neg_smul, one_smul] <;> try rfl
  · rw [hM, key]
    have : ((-1 / Real.sqrt 2 : ℝ) : ℂ) *
        ((-1 / (Complex.I * (Real.sqrt 2 : ℂ))) + (-1 / (Complex.I * (Real.sqrt 2 : ℂ)))) =
        -Complex.I := by
      push_cast
      field_simp
      rw [hc]
      have := Complex.I_mul_I
      linear_combination (2 : ℂ) * this
    rw [this]; simp only [neg_smul] <;> try rfl

theorem physicalFourierBasis_orthonormal :
  Orthonormal ℝ physicalFourierBasis := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨b, n⟩ ⟨b', m⟩
  rw [real_inner_eq_re_inner_g5012]
  unfold physicalFourierBasis
  rw [LinearIsometryEquiv.inner_map_map, lp.inner_single_left]
  by_cases h : n = m
  · subst h
    cases b <;> cases b' <;> simp [RCLike.inner_apply]
  · cases b <;> cases b' <;> simp [RCLike.inner_apply, h]

theorem physicalFourierBasis_dense_span :
  (⊤ : Submodule ℝ PhysicalL2) ≤
    (Submodule.span ℝ (Set.range physicalFourierBasis)).topologicalClosure := by
  classical
  intro x _
  set S : Submodule ℝ PhysicalL2 := Submodule.span ℝ (Set.range physicalFourierBasis) with hS
  have hterm : ∀ (n : ℤ) (c : ℂ), reflectedFourierL2.symm (lp.single 2 n c) ∈ S := by
    intro n c
    have hc : c = (c.re : ℂ) • (1 : ℂ) + (c.im : ℂ) • Complex.I := by
      apply Complex.ext <;> simp
    have : reflectedFourierL2.symm (lp.single 2 n c) =
        c.re • physicalFourierBasis (true, n) + c.im • physicalFourierBasis (false, n) := by
      conv_lhs => rw [hc]
      unfold physicalFourierBasis
      rw [lp.single_add, lp.single_smul, lp.single_smul, map_add, map_smul, map_smul]
      simp only [if_true, if_false, Bool.false_eq_true, Complex.coe_smul] <;> try rfl
    rw [this]
    exact S.add_mem (S.smul_mem _ (Submodule.subset_span ⟨(true, n), rfl⟩))
      (S.smul_mem _ (Submodule.subset_span ⟨(false, n), rfl⟩))
  have hsum := (lp.hasSum_single (p := 2) (by norm_num) (reflectedFourierL2 x))
  have hsum' : HasSum (fun n : ℤ => reflectedFourierL2.symm (lp.single 2 n (reflectedFourierL2 x n))) x := by
    have := hsum.mapL (reflectedFourierL2.symm.toContinuousLinearEquiv.toContinuousLinearMap)
    simpa using this
  have hmem : x ∈ closure (S : Set PhysicalL2) := by
    refine mem_closure_of_tendsto hsum' (Eventually.of_forall fun T => ?_)
    exact S.sum_mem fun n _ => hterm n _
  exact hmem

def physicalFourierHilbertBasis : HilbertBasis (Bool × ℤ) ℝ PhysicalL2 :=
  HilbertBasis.mk physicalFourierBasis_orthonormal physicalFourierBasis_dense_span

theorem physicalFourierHilbertBasis_apply (j : Bool × ℤ) :
  physicalFourierHilbertBasis j = physicalFourierBasis j := by
  unfold physicalFourierHilbertBasis
  rw [HilbertBasis.coe_mk]

end
end NlsGge.GKDefinitionDesign

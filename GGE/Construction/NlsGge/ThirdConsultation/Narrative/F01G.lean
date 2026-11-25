import Mathlib
import NlsGge.Birkhoff.F01Determinant38d
import NlsGge.ThirdConsultation.PDE.OneSmoothing

   
                                                                          
                                                                                            
                                                                              
                                                                  

                                                                       
                                                                      
                                                                            
                                                              
  

set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace
open NlsGge.Birkhoff NlsGge.Sobolev38
open NlsGge.Analysis.RegularizedDeterminant

namespace NlsGge.ThirdConsultation.Narrative

section SingularValues

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The sum of all genuine singular values of a real finite-dimensional map. -/
def f01NuclearNorm (A : V →ₗ[ℝ] V) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ V), A.singularValues i

theorem f01NuclearNorm_nonneg (A : V →ₗ[ℝ] V) : 0 ≤ f01NuclearNorm A :=
  Finset.sum_nonneg (fun i _ => A.singularValues_nonneg i)

/-- An orthonormal eigenbasis of A* A, in the same order as the singular values. -/
def f01SingularBasis (A : V →ₗ[ℝ] V) :
    OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V :=
  A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

theorem f01_inner_image_singularBasis (A : V →ₗ[ℝ] V)
    (i j : Fin (Module.finrank ℝ V)) :
    inner ℝ (A (f01SingularBasis A i)) (A (f01SingularBasis A j)) =
      A.singularValues j ^ 2 * (if i = j then 1 else 0) := by
  rw [← LinearMap.adjoint_inner_right]
  change inner ℝ (f01SingularBasis A i)
      ((LinearMap.adjoint A ∘ₗ A) (f01SingularBasis A j)) = _
  dsimp only [f01SingularBasis]
  rw [A.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis]
  rw [real_inner_smul_right, ← A.sq_singularValues_fin rfl j]
  rw [orthonormal_iff_ite.mp
    (A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).orthonormal]
  simp only [RCLike.ofReal_real_eq_id, id_eq]

theorem f01_norm_image_singularBasis (A : V →ₗ[ℝ] V)
    (i : Fin (Module.finrank ℝ V)) :
    ‖A (f01SingularBasis A i)‖ = A.singularValues i := by
  apply (sq_eq_sq₀ (norm_nonneg _) (A.singularValues_nonneg i)).mp
  have h := f01_inner_image_singularBasis A i i
  simpa [real_inner_self_eq_norm_sq] using h

/-- Only the positive singular values are used when normalizing image vectors. -/
def f01PositiveSingularIndex (A : V →ₗ[ℝ] V) :=
  {i : Fin (Module.finrank ℝ V) // A.singularValues i ≠ 0}

instance f01PositiveSingularIndexFintype (A : V →ₗ[ℝ] V) :
    Fintype (f01PositiveSingularIndex A) := by
  classical
  unfold f01PositiveSingularIndex
  infer_instance

/-- No division at a zero singular value: the index carries its nonzero proof. -/
def f01LeftSingularVector (A : V →ₗ[ℝ] V) (i : f01PositiveSingularIndex A) : V :=
  (A.singularValues i.val)⁻¹ • A (f01SingularBasis A i.val)

theorem f01LeftSingularVector_orthonormal (A : V →ₗ[ℝ] V) :
    Orthonormal ℝ (f01LeftSingularVector A) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  simp only [f01LeftSingularVector, real_inner_smul_left, real_inner_smul_right,
    f01_inner_image_singularBasis]
  by_cases hij : i = j
  · subst j
    field_simp [i.property]
  · have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    simp only [ite_eq_right hij, ite_eq_right hval, mul_zero]

theorem f01_inner_leftSingularVector_image (A : V →ₗ[ℝ] V)
    (i : f01PositiveSingularIndex A) :
    inner ℝ (f01LeftSingularVector A i) (A (f01SingularBasis A i.val)) =
      A.singularValues i.val := by
  rw [f01LeftSingularVector, real_inner_smul_left, real_inner_self_eq_norm_sq,
    f01_norm_image_singularBasis]
  field_simp [i.property]

theorem f01NuclearNorm_eq_sum_positive (A : V →ₗ[ℝ] V) :
    f01NuclearNorm A = ∑ i : f01PositiveSingularIndex A, A.singularValues i.val := by
  classical
  let f : Fin (Module.finrank ℝ V) → ℝ := fun i => A.singularValues (i : ℕ)
  let s : Finset (Fin (Module.finrank ℝ V)) :=
    Finset.univ.filter (fun i : Fin (Module.finrank ℝ V) => f i ≠ 0)
  change (∑ i : Fin (Module.finrank ℝ V), f i) =
    ∑ i : f01PositiveSingularIndex A, f i.val
  calc
    ∑ i : Fin (Module.finrank ℝ V), f i = ∑ i ∈ s, f i := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      have hzero : ¬ f i ≠ 0 := by
        simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hi
      exact not_not.mp hzero
    _ = ∑ i : f01PositiveSingularIndex A, f i.val :=
      Finset.sum_subtype
        (p := fun i : Fin (Module.finrank ℝ V) => f i ≠ 0)
        (F := f01PositiveSingularIndexFintype A) s
        (fun i => by simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]) f

end SingularValues

section ComplementaryBlock

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The nuclear bound for the actual complementary-block algebra.
The only abstract compatibility is equality with the genuine discarded block.
The concrete F01 corollary below discharges it using the landed toCLM theorem. -/
theorem f01_complementary_nuclear_bound (D : CplxProj38 H)
    [FiniteDimensional ℝ D.V] (L : H →L[ℝ] H) (c : HilbertSchmidt H H)
    (hc : HilbertSchmidt.toCLM c = D.C L) :
    f01NuclearNorm (D.resRange (D.M L) (D.M_mem L)) ≤ ‖c‖ ^ 2 := by
  classical
  let A : D.V →ₗ[ℝ] D.V := D.resRange (D.M L) (D.M_mem L)
  let b := f01SingularBasis A
  let I := f01PositiveSingularIndex A
  let u : I → D.V := fun i => b i.val
  let v : I → D.V := f01LeftSingularVector A
  have hu : Orthonormal ℝ u :=
    b.orthonormal.comp Subtype.val Subtype.val_injective
  have hv : Orthonormal ℝ v := f01LeftSingularVector_orthonormal A
  have huH : Orthonormal ℝ (fun i => (u i : H)) :=
    hu.comp_linearIsometry D.V.subtypeₗᵢ
  have hvH : Orthonormal ℝ (fun i => (v i : H)) :=
    hv.comp_linearIsometry D.V.subtypeₗᵢ
  have h1 := sum_norm_sq_orthonormal_le c (fun i => D.J (v i : H))
    (hvH.comp_linearIsometry D.Jiso)
  have h2 := sum_norm_sq_orthonormal_le c (fun i => (u i : H)) huH
  rw [hc] at h1 h2
  have hterm (i : I) : A.singularValues i.val ≤
      (‖D.C L (D.J (v i : H))‖ ^ 2 + ‖D.C L (u i : H)‖ ^ 2) / 2 := by
    have hsig : A.singularValues i.val = inner ℝ (v i) (A (u i)) :=
      (f01_inner_leftSingularVector_image A i).symm
    have he : inner ℝ (v i) (A (u i)) =
        -inner ℝ (D.C L (D.J (v i : H))) (D.J (D.C L (u i : H))) := by
      change inner ℝ (v i : H) (D.M L (u i : H)) = _
      simp only [CplxProj38.M, CplxProj38.Qop, mul_apply_eq_comp]
      rw [← neg_neg ⟪(v i : H), D.J _⟫_ℝ, ← D.J_skew,
        ContinuousLinearMap.adjoint_inner_right]
    calc
      A.singularValues i.val = inner ℝ (v i) (A (u i)) := hsig
      _ ≤ |inner ℝ (v i) (A (u i))| := le_abs_self _
      _ = |inner ℝ (D.C L (D.J (v i : H))) (D.J (D.C L (u i : H)))| := by
        rw [he, abs_neg]
      _ ≤ ‖D.C L (D.J (v i : H))‖ * ‖D.J (D.C L (u i : H))‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (‖D.C L (D.J (v i : H))‖ ^ 2 + ‖D.C L (u i : H)‖ ^ 2) / 2 := by
        rw [D.norm_J]
        nlinarith only [sq_nonneg (‖D.C L (D.J (v i : H))‖ - ‖D.C L (u i : H)‖)]
  calc
    f01NuclearNorm A = ∑ i : I, A.singularValues i.val :=
      f01NuclearNorm_eq_sum_positive A
    _ ≤ ∑ i : I,
        (‖D.C L (D.J (v i : H))‖ ^ 2 + ‖D.C L (u i : H)‖ ^ 2) / 2 :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = ((∑ i : I, ‖D.C L (D.J (v i : H))‖ ^ 2) +
        ∑ i : I, ‖D.C L (u i : H)‖ ^ 2) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ ‖c‖ ^ 2 := by linarith only [h1, h2]

/-- G04 at the SAME actual source operators and genuine HS norm. -/
theorem grouped_f01_nuclear_bound (x : H1_38) (N : ℕ) :
    f01NuclearNorm (PDE.actualBirkhoffInput38.MNmap x N) ≤
      ‖PDE.actualBirkhoffInput38.cHS PDE.actualOneSmoothingInput38 x N‖ ^ 2 :=
  f01_complementary_nuclear_bound (cp38 N) (PDE.actualBirkhoffInput38.LxN x N)
    (PDE.actualBirkhoffInput38.cHS PDE.actualOneSmoothingInput38 x N)
    (by rw [BirkhoffInput38.toCLM_cHS, BirkhoffInput38.CNop_eq])

end ComplementaryBlock

section SharpDeterminant

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Hadamard's inequality in a genuine orthonormal basis, including dimension zero. -/
theorem f01_abs_basis_det_le (b : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V)
    (w : Fin (Module.finrank ℝ V) → V) : |b.toBasis.det w| ≤ ∏ i, ‖w i‖ := by
  letI : Fact (Module.finrank ℝ V = Module.finrank ℝ V) := ⟨rfl⟩
  let o := b.toBasis.orientation
  have ho := o.abs_volumeForm_apply_le w
  rw [o.volumeForm_robust b rfl] at ho
  exact ho

/-- The determinant expansion retains the empty-set contribution exactly as 1. -/
theorem f01_abs_det_sub_one_le_prod (A : V →ₗ[ℝ] V)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V) :
    |LinearMap.det (1 + A) - 1| ≤ ∏ i, (1 + ‖A (b i)‖) - 1 := by
  classical
  let d : Finset (Fin (Module.finrank ℝ V)) → ℝ :=
    fun s => b.toBasis.det (s.piecewise (fun i => A (b i)) b)
  let p : Finset (Fin (Module.finrank ℝ V)) → ℝ :=
    fun s => ∏ i ∈ s, ‖A (b i)‖
  have hbself : b.toBasis.det (fun i => b i) = 1 := b.toBasis.det_self
  have hd0 : d ∅ = 1 := by simpa [d] using hbself
  have hp0 : p ∅ = 1 := by simp [p]
  have hexp : LinearMap.det (1 + A) = ∑ s, d s := by
    have hb := b.toBasis.det_comp (1 + A : V →ₗ[ℝ] V)
      (⇑b : Fin (Module.finrank ℝ V) → V)
    rw [hbself, mul_one] at hb
    have hfun :
        (⇑(1 + A : V →ₗ[ℝ] V) ∘ (⇑b : Fin (Module.finrank ℝ V) → V)) =
          (fun i : Fin (Module.finrank ℝ V) => A (b i)) +
            (⇑b : Fin (Module.finrank ℝ V) → V) := by
      funext i
      simp only [Function.comp_apply, LinearMap.add_apply, Module.End.one_apply,
        Pi.add_apply]
      exact add_comm _ _
    rw [hfun] at hb
    dsimp only [d]
    exact hb.symm.trans (b.toBasis.det.map_add_univ
      (fun i : Fin (Module.finrank ℝ V) => A (b i))
      (⇑b : Fin (Module.finrank ℝ V) → V))
  have hprod : (∏ i, (1 + ‖A (b i)‖)) = ∑ s, p s := by
    have h := Finset.prod_one_add
      (f := fun i : Fin (Module.finrank ℝ V) => ‖A (b i)‖)
      (Finset.univ : Finset (Fin (Module.finrank ℝ V)))
    rw [Finset.powerset_univ] at h
    dsimp only [p]
    exact h
  have hdet_erase : LinearMap.det (1 + A) - 1 =
      ∑ s ∈ (Finset.univ : Finset (Finset (Fin (Module.finrank ℝ V)))).erase ∅, d s := by
    have h := Finset.sum_erase_add
      (Finset.univ : Finset (Finset (Fin (Module.finrank ℝ V)))) d (Finset.mem_univ ∅)
    rw [hd0, ← hexp] at h
    linarith only [h]
  have hprod_erase : (∏ i, (1 + ‖A (b i)‖)) - 1 =
      ∑ s ∈ (Finset.univ : Finset (Finset (Fin (Module.finrank ℝ V)))).erase ∅, p s := by
    have h := Finset.sum_erase_add
      (Finset.univ : Finset (Finset (Fin (Module.finrank ℝ V)))) p (Finset.mem_univ ∅)
    rw [hp0, ← hprod] at h
    linarith only [h]
  rw [hdet_erase, hprod_erase]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun s _ => ?_))
  calc
    |d s| ≤ ∏ i, ‖s.piecewise (fun i => A (b i)) b i‖ :=
      f01_abs_basis_det_le b _
    _ = p s := by
      simp only [Finset.piecewise, apply_ite, b.norm_eq_one, p]
      rw [Finset.prod_ite_mem]
      simp only [Finset.univ_inter]

/-- G05: the general sharp real finite-dimensional estimate, with no smallness assumption. -/
theorem grouped_sharp_det_estimate (A : V →ₗ[ℝ] V) :
    |LinearMap.det (1 + A) - 1| ≤ Real.exp (f01NuclearNorm A) - 1 := by
  calc
    |LinearMap.det (1 + A) - 1| ≤
        (∏ i : Fin (Module.finrank ℝ V), (1 + ‖A (f01SingularBasis A i)‖)) - 1 :=
      f01_abs_det_sub_one_le_prod A (f01SingularBasis A)
    _ = (∏ i : Fin (Module.finrank ℝ V), (1 + A.singularValues i)) - 1 := by
      simp only [f01_norm_image_singularBasis]
    _ ≤ Real.exp (f01NuclearNorm A) - 1 :=
      sub_le_sub_right (Real.prod_one_add_le_exp_sum Finset.univ
        (fun i : Fin (Module.finrank ℝ V) => A.singularValues_nonneg i)) 1

/-- The literal source sharp modulus for the SAME real complementary-block determinant. -/
theorem grouped_f01_sharp_det_bound (x : H1_38) (N : ℕ) :
    |PDE.actualBirkhoffInput38.detMN x N - 1| ≤
      Real.exp (‖PDE.actualBirkhoffInput38.cHS PDE.actualOneSmoothingInput38 x N‖ ^ 2) - 1 := by
  exact (grouped_sharp_det_estimate (PDE.actualBirkhoffInput38.MNmap x N)).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr (grouped_f01_nuclear_bound x N)) 1)

end SharpDeterminant

end NlsGge.ThirdConsultation.Narrative

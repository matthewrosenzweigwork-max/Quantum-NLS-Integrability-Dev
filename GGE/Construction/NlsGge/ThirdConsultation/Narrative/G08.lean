import Mathlib
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Atomic.R.R123
import NlsGge.Atomic.R.R124
import NlsGge.Atomic.R.R125
import NlsGge.Analysis.RegularizedDeterminant.FiniteSections

   
                                                         
                                                                        
                                                                                
  
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Birkhoff NlsGge.Sobolev38
open NlsGge.Analysis.RegularizedDeterminant

namespace NlsGge.ThirdConsultation.Narrative

/-- The genuine weighted real Fourier basis of the source E_s carrier. -/
def g08_basis {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ) :
    HilbertBasis (ℤ × Fin 2) ℝ (ECarrier38 c s) :=
  weightedRealHilbertBasis (fullModeWeight c s)

theorem g08_basis_coe {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ)
    (p : ℤ × Fin 2) (n : ℤ) :
    eCoe38 c s (g08_basis c s p) n =
      (if n = p.1 then Complex.orthonormalBasisOneI p.2 else 0) /
        (Real.sqrt (fullModeWeight c s n) : ℂ) := by
  have he : g08_basis c s p = weightedRealBasisVector (fullModeWeight c s) p :=
    weightedRealHilbertBasis_apply _ p
  rw [he]
  exact weightedRealBasisVector_apply _ p n

theorem g08_projection_basis {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ)
    (N : ℕ) (p : ℤ × Fin 2) :
    projE38 c s N (g08_basis c s p) =
      if p.1 ∈ symmetricModes N then g08_basis c s p else 0 := by
  classical
  by_cases hp : p.1 ∈ symmetricModes N
  · rw [if_pos hp]
    apply eExt38 c s
    funext n
    rw [eCoe38_projE38]
    by_cases hn : n ∈ symmetricModes N
    · rw [if_pos hn]
    · rw [if_neg hn, g08_basis_coe]
      have hnp : n ≠ p.1 := fun h => hn (h.symm ▸ hp)
      simp only [if_neg hnp, zero_div]
  · rw [if_neg hp]
    apply eExt38 c s
    funext n
    change (if n ∈ symmetricModes N then eCoe38 c s (g08_basis c s p) n else 0) = 0
    by_cases hn : n ∈ symmetricModes N
    · rw [if_pos hn, g08_basis_coe]
      have hnp : n ≠ p.1 := fun h => hp (h ▸ hn)
      simp only [if_neg hnp, zero_div]
    · rw [if_neg hn]

theorem g08_projection_inner {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ)
    (N : ℕ) (p : ℤ × Fin 2) (x : ECarrier38 c s) :
    inner ℝ (g08_basis c s p) (projE38 c s N x) =
      if p.1 ∈ symmetricModes N then inner ℝ (g08_basis c s p) x else 0 := by
  have he : g08_basis c s p = weightedRealBasisVector (fullModeWeight c s) p :=
    weightedRealHilbertBasis_apply _ p
  have hinner (y : ECarrier38 c s) : inner ℝ (g08_basis c s p) y =
      inner ℝ (Complex.orthonormalBasisOneI p.2)
        ((Real.sqrt (fullModeWeight c s p.1) : ℂ) * eCoe38 c s y p.1) := by
    have h := weightedRealBasisVector_inner (fullModeWeight c s) p y
    rw [he]
    exact h
  rw [hinner, hinner, eCoe38_projE38]
  by_cases hp : p.1 ∈ symmetricModes N
  · simp only [if_pos hp]
  · simp only [if_neg hp, mul_zero, inner_zero_right]

/-- The SAME actual E_s Fourier projections are self-adjoint for its real Hilbert norm. -/
theorem g08_projection_adjoint {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ) (N : ℕ) :
    ContinuousLinearMap.adjoint (projE38 c s N) = projE38 c s N := by
  apply ContinuousLinearMap.ext
  intro x
  apply (g08_basis c s).repr.injective
  apply lp.ext
  funext p
  simp only [HilbertBasis.repr_apply_apply]
  rw [ContinuousLinearMap.adjoint_inner_right, g08_projection_basis, g08_projection_inner]
  by_cases hp : p.1 ∈ symmetricModes N
  · simp only [if_pos hp]
  · simp only [if_neg hp, inner_zero_left]

section HilbertApproximation

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- A bounded strongly convergent family of self-adjoint contractions has a right tail
on every already Hilbert-Schmidt operator. -/
theorem g08_hs_right_tail (P : ℕ → (X →L[ℝ] X))
    (hP : ∀ N, ‖P N‖ ≤ 1)
    (hself : ∀ N, ContinuousLinearMap.adjoint (P N) = P N)
    (hstrong : ∀ x : X, Tendsto (fun N => P N x) atTop (𝓝 x))
    (A : X →L[ℝ] X) (hA : IsHilbertSchmidt A) :
    Tendsto (fun N => ‖A - A.comp (P N)‖) atTop (𝓝 0) := by
  let R : ℕ → (X →L[ℝ] X) := fun N => 1 - P N
  let T : HilbertSchmidt X X := HilbertSchmidt.ofCLM A hA
  have hR (N : ℕ) : ‖R N‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖(1 : X →L[ℝ] X)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    linarith [hP N]
  have hRs (x : X) : Tendsto (fun N => R N x) atTop (𝓝 0) := by
    have hx : Tendsto (fun _ : ℕ => x) atTop (𝓝 x) := tendsto_const_nhds
    simpa only [R, ContinuousLinearMap.sub_apply, one_apply_eq_self, sub_self]
      using hx.sub (hstrong x)
  have hHS := HilbertSchmidt.tendsto_postcompose_zero atTop R
    (HilbertSchmidt.adjoint T) 2 (by norm_num) (Eventually.of_forall hR) hRs
  have hbound (N : ℕ) : ‖(R N).comp (ContinuousLinearMap.adjoint A)‖ ≤
      ‖HilbertSchmidt.postcompose (R N) (HilbertSchmidt.adjoint T)‖ := by
    simpa only [HilbertSchmidt.toCLM_postcompose, HilbertSchmidt.toCLM_adjoint,
      HilbertSchmidt.toCLM_ofCLM, T] using
      HilbertSchmidt.opNorm_le (HilbertSchmidt.postcompose (R N) (HilbertSchmidt.adjoint T))
  have hnorm : Tendsto (fun N =>
      ‖HilbertSchmidt.postcompose (R N) (HilbertSchmidt.adjoint T)‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using hHS.norm
  have hlim : Tendsto (fun N => ‖(R N).comp (ContinuousLinearMap.adjoint A)‖)
      atTop (𝓝 0) :=
    squeeze_zero (fun N => norm_nonneg _) hbound hnorm
  have heq (N : ℕ) : ‖A - A.comp (P N)‖ =
      ‖(R N).comp (ContinuousLinearMap.adjoint A)‖ := by
    rw [← ContinuousLinearMap.adjoint.norm_map (A - A.comp (P N))]
    simp only [map_sub, ContinuousLinearMap.adjoint_comp, hself]
    congr 1
  simpa only [← heq] using hlim

/-- Uniform right-tail perturbation bound; no compactness is assumed in this estimate. -/
theorem g08_right_tail_perturbation (P A B : X →L[ℝ] X) (hP : ‖P‖ ≤ 1) :
    ‖A - A.comp P‖ ≤ 2*‖A-B‖ + ‖B-B.comp P‖ := by
  have he : A - A.comp P = (A-B) + (B-B.comp P) - (A-B).comp P := by
    ext x
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply]
    abel
  have hb : ‖(A-B).comp P‖ ≤ ‖A-B‖ := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left hP (norm_nonneg _)).trans_eq (mul_one _))
  rw [he]
  calc
    ‖(A-B) + (B-B.comp P) - (A-B).comp P‖ ≤
        ‖(A-B) + (B-B.comp P)‖ + ‖(A-B).comp P‖ := norm_sub_le _ _
    _ ≤ (‖A-B‖ + ‖B-B.comp P‖) + ‖A-B‖ := add_le_add (norm_add_le _ _) hb
    _ = 2*‖A-B‖ + ‖B-B.comp P‖ := by ring

/-- Transfer right-tail convergence through operator-norm finite-rank approximations.
Only the approximating heads, rather than A itself, are required to be HS. -/
theorem g08_right_tail_of_heads (P : ℕ → (X →L[ℝ] X))
    (hP : ∀ N, ‖P N‖ ≤ 1)
    (hself : ∀ N, ContinuousLinearMap.adjoint (P N) = P N)
    (hstrong : ∀ x : X, Tendsto (fun N => P N x) atTop (𝓝 x))
    (A : X →L[ℝ] X) (hhead : ∀ M, IsHilbertSchmidt ((P M).comp A))
    (hleft : Tendsto (fun M => ‖A - (P M).comp A‖) atTop (𝓝 0)) :
    Tendsto (fun N => ‖A - A.comp (P N)‖) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := ((tendsto_order.1 hleft).2 (ε/4) (by linarith)).exists
  have hright := g08_hs_right_tail P hP hself hstrong ((P M).comp A) (hhead M)
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 hright (ε/2) (by linarith)
  refine ⟨N0, fun N hN => ?_⟩
  have hn := hN0 N hN
  simp only [Real.dist_eq, sub_zero, abs_norm] at hn ⊢
  have hb := g08_right_tail_perturbation (P N) A ((P M).comp A) (hP N)
  linarith

/-- The two-sided error is controlled by the two one-sided errors of the SAME operator. -/
theorem g08_two_sided_error (P A : X →L[ℝ] X) (hP : ‖P‖ ≤ 1) :
    ‖A - P.comp (A.comp P)‖ ≤ ‖A-P.comp A‖ + ‖A-A.comp P‖ := by
  have he : A - P.comp (A.comp P) = (A-P.comp A) + P.comp (A-A.comp P) := by
    ext x
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [he]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right hP (norm_nonneg _)).trans_eq (one_mul _))

theorem g08_two_sided_limit (P : ℕ → (X →L[ℝ] X)) (hP : ∀ N, ‖P N‖ ≤ 1)
    (A : X →L[ℝ] X)
    (hleft : Tendsto (fun N => ‖A-(P N).comp A‖) atTop (𝓝 0))
    (hright : Tendsto (fun N => ‖A-A.comp (P N)‖) atTop (𝓝 0)) :
    Tendsto (fun N => (P N).comp (A.comp (P N))) atTop (𝓝 A) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun N => ‖A-(P N).comp A‖ + ‖A-A.comp (P N)‖)
      atTop (𝓝 0) := by simpa only [add_zero] using hleft.add hright
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hb
  rw [norm_sub_rev]
  exact g08_two_sided_error (P N) A (hP N)

theorem g08_compression_difference (P A B : X →L[ℝ] X) (hP : ‖P‖ ≤ 1) :
    ‖P.comp (A.comp P) - P.comp (B.comp P)‖ ≤ ‖A-B‖ := by
  have he : P.comp (A.comp P) - P.comp (B.comp P) = P.comp ((A-B).comp P) := by
    ext x
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, map_sub]
  rw [he]
  calc
    ‖P.comp ((A-B).comp P)‖ ≤ ‖P‖ * ‖(A-B).comp P‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖A-B‖ * 1) := mul_le_mul hP
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left hP (norm_nonneg _))) (norm_nonneg _) zero_le_one
    _ = ‖A-B‖ := by ring

theorem g08_varying_compression_limit (P : ℕ → (X →L[ℝ] X)) (hP : ∀ N, ‖P N‖ ≤ 1)
    (A : X →L[ℝ] X) (Aseq : ℕ → (X →L[ℝ] X))
    (hAseq : Tendsto Aseq atTop (𝓝 A))
    (hfixed : Tendsto (fun N => (P N).comp (A.comp (P N))) atTop (𝓝 A)) :
    Tendsto (fun N => (P N).comp ((Aseq N).comp (P N))) atTop (𝓝 A) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hAseq hfixed ⊢
  have hb : Tendsto (fun N => ‖Aseq N-A‖ + ‖(P N).comp (A.comp (P N))-A‖)
      atTop (𝓝 0) := by simpa only [add_zero] using hAseq.add hfixed
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hb
  calc
    ‖(P N).comp ((Aseq N).comp (P N))-A‖ =
        ‖((P N).comp ((Aseq N).comp (P N))-(P N).comp (A.comp (P N))) +
          ((P N).comp (A.comp (P N))-A)‖ := by congr 1; abel
    _ ≤ ‖(P N).comp ((Aseq N).comp (P N))-(P N).comp (A.comp (P N))‖ +
        ‖(P N).comp (A.comp (P N))-A‖ := norm_add_le _ _
    _ ≤ ‖Aseq N-A‖ + ‖(P N).comp (A.comp (P N))-A‖ :=
      add_le_add (g08_compression_difference (P N) (Aseq N) A (hP N)) le_rfl

end HilbertApproximation

/-- Every projected head has finite-dimensional range; the source derivative itself
is not assumed Hilbert-Schmidt by this lemma. -/
theorem g08_head_hilbertSchmidt {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ)
    (M : ℕ) (A : ECarrier38 c s →L[ℝ] ECarrier38 c s) :
    IsHilbertSchmidt ((projE38 c s M).comp A) := by
  let V := LinearMap.range (projE38 c s M).toLinearMap
  letI : FiniteDimensional ℝ V := NlsGge.Atomic.R123.finiteDimensional_range_projE c s M
  let T : ECarrier38 c s →L[ℝ] V := ((projE38 c s M).comp A).codRestrict V
    (fun x => ⟨A x, rfl⟩)
  let S : HilbertSchmidt (ECarrier38 c s) V :=
    HilbertSchmidt.ofCLM T (isHilbertSchmidt_of_finiteCodomain T)
  have he : (HilbertSchmidt.postcompose V.subtypeL S).toCLM = (projE38 c s M).comp A := by
    ext x
    rfl
  rw [← he]
  exact HilbertSchmidt.membership _

/-- Explicit compactness of the actual derivative on the source window. -/
theorem g08_actual_derivative_compact {lo up : ℝ} (c : BoundedCoefficients lo up)
    (s : ℝ) (_hs : (1 : ℝ)/2 < s) (_hs2 : s < 3/4) (x : ECarrier38 c s) :
    IsCompactOperator (fderiv ℝ
      (PDE.actualBirkhoffInput38.KE38 PDE.actualOneSmoothingInput38 c s) x) := by
  rw [PDE.actualBirkhoffInput38.fderiv_KE38 PDE.actualOneSmoothingInput38 c s x]
  have hJ : IsCompactOperator (eInclCLM38 c (by linarith : s-1 ≤ s)) :=
    (NlsGge.Atomic.R123.weightedInclusion_tail_and_compact c s).2.2
  exact hJ.comp_clm _

/-- The missing right-composition tail, for the actual derivative and actual projections. -/
theorem grouped_w09_right_derivative_tail {lo up : ℝ} (c : BoundedCoefficients lo up)
    (s : ℝ) (hs : (1 : ℝ)/2 < s) (hs2 : s < 3/4) (x : ECarrier38 c s) :
    Tendsto (fun N : ℕ => ‖fderiv ℝ
      (PDE.actualBirkhoffInput38.KE38 PDE.actualOneSmoothingInput38 c s) x -
      (fderiv ℝ (PDE.actualBirkhoffInput38.KE38 PDE.actualOneSmoothingInput38 c s) x).comp
        (projE38 c s N)‖) atTop (𝓝 0) := by
  exact g08_right_tail_of_heads (projE38 c s) (norm_projE38_le c s)
    (g08_projection_adjoint c s) (tendsto_projE38 c s) _
    (fun M => g08_head_hilbertSchmidt c s M _)
    (NlsGge.ThirdConsultation.R.r124_main c s x)

/-- Fixed-base two-sided convergence, on precisely the source window. -/
theorem grouped_w09_two_sided {lo up : ℝ} (c : BoundedCoefficients lo up)
    (s : ℝ) (hs : (1 : ℝ)/2 < s) (hs2 : s < 3/4) (x : ECarrier38 c s) :
    Tendsto (fun N => 1 + (projE38 c s N).comp
      ((fderiv ℝ (PDE.actualBirkhoffInput38.KE38 PDE.actualOneSmoothingInput38 c s) x).comp
        (projE38 c s N))) atTop
      (𝓝 (1 + fderiv ℝ (PDE.actualBirkhoffInput38.KE38 PDE.actualOneSmoothingInput38 c s) x)) := by
  have h := g08_two_sided_limit (projE38 c s) (norm_projE38_le c s) _
    (NlsGge.ThirdConsultation.R.r124_main c s x)
    (grouped_w09_right_derivative_tail c s hs hs2 x)
  exact tendsto_const_nhds.add h

/-- Projecting the base point preserves the SAME two-sided limit. -/
theorem grouped_w09_two_sided_varying_base {lo up : ℝ} (c : BoundedCoefficients lo up)
    (s : ℝ) (hs : (1 : ℝ)/2 < s) (hs2 : s < 3/4) (x : ECarrier38 c s) :
    Tendsto (fun N => 1 + (projE38 c s N).comp
      ((fderiv ℝ (PDE.actualBirkhoffInput38.KE38 PDE.actualOneSmoothingInput38 c s)
        (projE38 c s N x)).comp (projE38 c s N))) atTop
      (𝓝 (1 + fderiv ℝ (PDE.actualBirkhoffInput38.KE38 PDE.actualOneSmoothingInput38 c s) x)) := by
  have hA := (PDE.actualBirkhoffInput38.continuousAt_fderiv_KE38
    PDE.actualOneSmoothingInput38 c s x).tendsto.comp (tendsto_projE38 c s x)
  have hfixed := g08_two_sided_limit (projE38 c s) (norm_projE38_le c s) _
    (NlsGge.ThirdConsultation.R.r124_main c s x)
    (grouped_w09_right_derivative_tail c s hs hs2 x)
  have h := g08_varying_compression_limit (projE38 c s) (norm_projE38_le c s) _ _ hA hfixed
  exact tendsto_const_nhds.add h

section InverseStability

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Norm convergence to a genuine equivalence supplies eventual inverses with one common bound.
Invertibility is established before any inverse identity is used. -/
theorem g08_eventual_inverse_bound (A : ℕ → (X →L[ℝ] X)) (e : X ≃L[ℝ] X)
    (hA : Tendsto A atTop (𝓝 (e : X →L[ℝ] X))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∃ eN : X ≃L[ℝ] X, (eN : X →L[ℝ] X) = A N ∧
        ‖(eN.symm : X →L[ℝ] X)‖ ≤ C := by
  have hunit : ∀ᶠ N : ℕ in atTop, IsUnit (A N) := hA.eventually (Units.nhds e.toUnit)
  have heinv : Ring.inverse (e : X →L[ℝ] X) = (e.symm : X →L[ℝ] X) := by
    exact Ring.inverse_unit e.toUnit
  have hI : Tendsto (fun N => Ring.inverse (A N)) atTop
      (𝓝 (Ring.inverse (e : X →L[ℝ] X))) :=
    (NormedRing.inverse_continuousAt e.toUnit).tendsto.comp hA
  have hnorm : Tendsto (fun N => ‖Ring.inverse (A N)‖) atTop (𝓝 ‖(e.symm : X →L[ℝ] X)‖) := by
    simpa only [heinv] using hI.norm
  let C : ℝ := ‖(e.symm : X →L[ℝ] X)‖ + 1
  have hC : 0 < C := by dsimp only [C]; linarith [norm_nonneg (e.symm : X →L[ℝ] X)]
  have hb : ∀ᶠ N : ℕ in atTop, ‖Ring.inverse (A N)‖ < C :=
    (tendsto_order.1 hnorm).2 C (lt_add_one _)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hunit, hb] with N hN hbound
  obtain ⟨u, hu⟩ := hN
  refine ⟨ContinuousLinearEquiv.ofUnit u, ?_, ?_⟩
  · exact hu
  · change ‖(↑u⁻¹ : X →L[ℝ] X)‖ ≤ C
    rw [← Ring.inverse_unit u, hu]
    exact hbound.le

/-- Restrict a block compression equivalence to the SAME projection range.
Both forward and inverse preserve the range, with no larger inverse norm. -/
theorem g08_restrict_block_equiv (P A : X →L[ℝ] X)
    (hP : ∀ x : X, P (P x) = P x) (e : X ≃L[ℝ] X)
    (he : (e : X →L[ℝ] X) = 1 + P.comp (A.comp P)) :
    ∃ f : LinearMap.range P.toLinearMap ≃L[ℝ] LinearMap.range P.toLinearMap,
      (∀ v : LinearMap.range P.toLinearMap, (f v : X) = e v) ∧
      (∀ v : LinearMap.range P.toLinearMap, (f.symm v : X) = e.symm v) ∧
      ‖(f.symm : LinearMap.range P.toLinearMap →L[ℝ] LinearMap.range P.toLinearMap)‖ ≤
        ‖(e.symm : X →L[ℝ] X)‖ := by
  let V := LinearMap.range P.toLinearMap
  have hcomm (x : X) : P (e x) = e (P x) := by
    change P ((e : X →L[ℝ] X) x) = (e : X →L[ℝ] X) (P x)
    simp only [he, ContinuousLinearMap.add_apply, one_apply_eq_self,
      ContinuousLinearMap.comp_apply, map_add, hP]
  have hInv (x : X) : P (e.symm x) = e.symm (P x) := by
    apply e.injective
    rw [← hcomm, e.apply_symm_apply, e.apply_symm_apply]
  have hV (x : X) (hx : x ∈ V) : e x ∈ V := by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨e y, hcomm y⟩
  have hVi (x : X) (hx : x ∈ V) : e.symm x ∈ V := by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨e.symm y, hInv y⟩
  have hmap : V.map e.toLinearMap = V := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hV x hx
    · intro y hy
      exact ⟨e.symm y, hVi y hy, e.apply_symm_apply y⟩
  let f : V ≃L[ℝ] V := e.ofSubmodules V V hmap
  refine ⟨f, ?_, ?_, ?_⟩
  · intro v
    rfl
  · intro v
    rfl
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    change ‖(f.symm v : X)‖ ≤ ‖(e.symm : X →L[ℝ] X)‖ * ‖(v : X)‖
    change ‖e.symm (v : X)‖ ≤ ‖(e.symm : X →L[ℝ] X)‖ * ‖(v : X)‖
    exact (e.symm : X →L[ℝ] X).le_opNorm v

theorem g08_eventual_restricted_bound (P : ℕ → (X →L[ℝ] X))
    (hP : ∀ N x, P N (P N x) = P N x) (A : ℕ → (X →L[ℝ] X)) (C : ℝ)
    (hb : ∀ᶠ N : ℕ in atTop, ∃ e : X ≃L[ℝ] X,
      (e : X →L[ℝ] X) = 1 + (P N).comp ((A N).comp (P N)) ∧
        ‖(e.symm : X →L[ℝ] X)‖ ≤ C) :
    ∀ᶠ N : ℕ in atTop,
      ∃ f : LinearMap.range (P N).toLinearMap ≃L[ℝ] LinearMap.range (P N).toLinearMap,
        (∀ v : LinearMap.range (P N).toLinearMap, (f v : X) =
          (1 + (P N).comp ((A N).comp (P N)) : X →L[ℝ] X) v) ∧
        ‖(f.symm : LinearMap.range (P N).toLinearMap →L[ℝ]
          LinearMap.range (P N).toLinearMap)‖ ≤ C := by
  filter_upwards [hb] with N hN
  obtain ⟨e, he, hnorm⟩ := hN
  obtain ⟨f, hf, _, hfnorm⟩ := g08_restrict_block_equiv (P N) (A N) (hP N) e he
  refine ⟨f, ?_, hfnorm.trans hnorm⟩
  intro v
  rw [hf]
  change (e : X →L[ℝ] X) v = _
  rw [he]

end InverseStability

/-- Eventual full-space inverses at a fixed base, with one N-independent bound. -/
theorem grouped_w09_two_sided_fixed_base_inverses {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ)/2 < s) (hs2 : s < 3/4) (x : ECarrier38 c s) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∃ eN : ECarrier38 c s ≃L[ℝ] ECarrier38 c s,
        (eN : ECarrier38 c s →L[ℝ] ECarrier38 c s) =
          1 + (projE38 c s N).comp
            ((fderiv ℝ (PDE.actualBirkhoffInput38.KE38 PDE.actualOneSmoothingInput38 c s) x).comp
              (projE38 c s N)) ∧
        ‖(eN.symm : ECarrier38 c s →L[ℝ] ECarrier38 c s)‖ ≤ C := by
  obtain ⟨e, he⟩ := NlsGge.ThirdConsultation.R.r125_main c s x
  apply g08_eventual_inverse_bound _ e
  rw [he]
  exact grouped_w09_two_sided c s hs hs2 x

/-- Eventual full-space inverses with the projected base point P_N x. -/
theorem grouped_w09_two_sided_inverses {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ)/2 < s) (hs2 : s < 3/4) (x : ECarrier38 c s) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∃ eN : ECarrier38 c s ≃L[ℝ] ECarrier38 c s,
        (eN : ECarrier38 c s →L[ℝ] ECarrier38 c s) =
          1 + (projE38 c s N).comp
            ((fderiv ℝ (PDE.actualBirkhoffInput38.KE38 PDE.actualOneSmoothingInput38 c s)
              (projE38 c s N x)).comp (projE38 c s N)) ∧
        ‖(eN.symm : ECarrier38 c s →L[ℝ] ECarrier38 c s)‖ ≤ C := by
  obtain ⟨e, he⟩ := NlsGge.ThirdConsultation.R.r125_main c s x
  apply g08_eventual_inverse_bound _ e
  rw [he]
  exact grouped_w09_two_sided_varying_base c s hs hs2 x

/-- The finite plane is the actual range of the same source projection. -/
abbrev g08_plane {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ) (N : ℕ) :=
  LinearMap.range (projE38 c s N).toLinearMap

theorem g08_plane_finite_dimensional {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ) (N : ℕ) :
    FiniteDimensional ℝ (g08_plane c s N) := NlsGge.Atomic.R123.finiteDimensional_range_projE c s N

/-- Fixed-base inverse restrictions to the actual finite planes, with a common bound. -/
theorem grouped_w09_fixed_finite_plane_inverses {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ)/2 < s) (hs2 : s < 3/4) (x : ECarrier38 c s) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∃ fN : g08_plane c s N ≃L[ℝ] g08_plane c s N,
        (∀ v : g08_plane c s N, (fN v : ECarrier38 c s) =
          (1 + (projE38 c s N).comp
            ((fderiv ℝ (PDE.actualBirkhoffInput38.KE38 PDE.actualOneSmoothingInput38 c s) x).comp
              (projE38 c s N)) : ECarrier38 c s →L[ℝ] ECarrier38 c s) v) ∧
        ‖(fN.symm : g08_plane c s N →L[ℝ] g08_plane c s N)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := grouped_w09_two_sided_fixed_base_inverses c s hs hs2 x
  exact ⟨C, hC, g08_eventual_restricted_bound (projE38 c s) (projE38_idem c s) _ C hbound⟩

/-- Projected-base inverse restrictions to the same finite planes, with a common bound. -/
theorem grouped_w09_varying_finite_plane_inverses {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ)/2 < s) (hs2 : s < 3/4) (x : ECarrier38 c s) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∃ fN : g08_plane c s N ≃L[ℝ] g08_plane c s N,
        (∀ v : g08_plane c s N, (fN v : ECarrier38 c s) =
          (1 + (projE38 c s N).comp
            ((fderiv ℝ (PDE.actualBirkhoffInput38.KE38 PDE.actualOneSmoothingInput38 c s)
              (projE38 c s N x)).comp (projE38 c s N)) :
                ECarrier38 c s →L[ℝ] ECarrier38 c s) v) ∧
        ‖(fN.symm : g08_plane c s N →L[ℝ] g08_plane c s N)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := grouped_w09_two_sided_inverses c s hs hs2 x
  exact ⟨C, hC, g08_eventual_restricted_bound (projE38 c s) (projE38_idem c s) _ C hbound⟩

end NlsGge.ThirdConsultation.Narrative

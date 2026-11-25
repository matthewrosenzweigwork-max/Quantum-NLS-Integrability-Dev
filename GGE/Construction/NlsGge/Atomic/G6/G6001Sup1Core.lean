import Mathlib
import NlsGge.Atomic.G5.G5012Host
import NlsGge.Atomic.G5.G5012Sup1
import NlsGge.Atomic.G5.G5012Sup2
import NlsGge.Atomic.G5.G5017Host
import NlsGge.Atomic.G5.G5018Sup1

                                                                                
                                                                                            
                                                                                                                   
                                           
                                                                                                                
                                                                                                                    
                                                                                                                            
                                                                                                         
                                                                                                                      
                                     
                                                                                                                     
                                                                                                                         
                                                                                                               
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GK38
open scoped InnerProductSpace

namespace NlsGge.GKDefinitionDesign
namespace G6001Aux
noncomputable section

/-- Injectivity from a biorthogonal family of continuous functionals (GK Lemma F.7, first half). -/
theorem injective_of_biorth {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) (d : HilbertBasis ι ℝ E) (ψ : ι → E →L[ℝ] ℝ)
    (hψ : ∀ k, ψ k (A (d k)) ≠ 0 ∧ ∀ k', k' ≠ k → ψ k (A (d k')) = 0) :
    Function.Injective A := by
  rw [injective_iff_map_eq_zero]
  intro h hAh
  have hξ := d.hasSum_repr h
  have hsum : HasSum (fun k => d.repr h k • A (d k)) 0 := by
    have := hξ.mapL A
    simpa [hAh] using this
  have hξ0 : ∀ k, d.repr h k = 0 := by
    intro k
    have h2 : HasSum (fun k' => d.repr h k' * ψ k (A (d k'))) 0 := by
      have := hsum.mapL (ψ k)
      simpa using this
    have h3 : HasSum (fun k' => d.repr h k' * ψ k (A (d k'))) (d.repr h k * ψ k (A (d k))) :=
      hasSum_single k (fun k' hk' => by rw [(hψ k).2 k' hk', mul_zero])
    exact (mul_eq_zero.1 (h3.unique h2)).resolve_right (hψ k).1
  have hz : (fun k => d.repr h k • d k) = fun _ => (0 : E) := by
    funext k
    rw [hξ0 k, zero_smul]
  rw [hz] at hξ
  exact hξ.unique hasSum_zero

/-- Real symplectic pairing of projected gradients of two real covectors. -/
theorem omega_eq (L M : PotPair →L[ℂ] ℂ)
    (hL : star (pairGradientCLM L).2 = (pairGradientCLM L).1)
    (hM : star (pairGradientCLM M).2 = (pairGradientCLM M).1) :
    inner ℝ ((-Complex.I) • pairGradientProjection (pairGradientCLM M))
        (pairGradientProjection (pairGradientCLM L)) =
      2 * (pairPoissonCLM L M).re := by
  have hPo : pairPoissonCLM L M =
      inner ℂ (star (pairGradientCLM L).1) (-Complex.I • (pairGradientCLM M).2) +
        inner ℂ (star (pairGradientCLM L).2) (Complex.I • (pairGradientCLM M).1) :=
    clm_eq_bilinPair L _
  have hP : pairGradientProjection (pairGradientCLM L) =
      (pairGradientCLM L).2 + (pairGradientCLM L).2 := by
    unfold pairGradientProjection
    rw [← hL, star_star]
  have hQ : pairGradientProjection (pairGradientCLM M) =
      (pairGradientCLM M).2 + (pairGradientCLM M).2 := by
    unfold pairGradientProjection
    rw [← hM, star_star]
  rw [← hL, ← hM, star_star, inner_smul_right, inner_smul_right, inner_star_star_g5012] at hPo
  rw [hP, hQ, real_inner_eq_re_inner_g5012, hPo, inner_smul_left]
  simp only [inner_add_left, inner_add_right]
  rw [← inner_conj_symm (pairGradientCLM L).2 (pairGradientCLM M).2]
  generalize inner ℂ (pairGradientCLM M).2 (pairGradientCLM L).2 = z
  simp only [map_neg, Complex.conj_I, neg_neg, Complex.mul_re, Complex.add_re, Complex.neg_re,
    Complex.neg_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.add_im,
    Complex.mul_im]
  ring

theorem omega_scaled (r s : ℝ) (L M : PotPair →L[ℂ] ℂ)
    (hL : star (pairGradientCLM L).2 = (pairGradientCLM L).1)
    (hM : star (pairGradientCLM M).2 = (pairGradientCLM M).1) :
    inner ℝ ((-Complex.I) • (s • pairGradientProjection (pairGradientCLM M)))
        (r • pairGradientProjection (pairGradientCLM L)) =
      r * s * (2 * (pairPoissonCLM L M).re) := by
  rw [show (-Complex.I) • (s • pairGradientProjection (pairGradientCLM M)) =
      s • ((-Complex.I) • pairGradientProjection (pairGradientCLM M)) from smul_comm _ _ _,
    real_inner_smul_right, real_inner_smul_left, omega_eq L M hL hM]
  ring

theorem sqrt2_inv_ne : (1 / Real.sqrt 2 : ℝ) ≠ 0 :=
  one_div_ne_zero (Real.sqrt_pos.2 (by norm_num)).ne'

theorem neg_sqrt2_inv_ne : (-1 / Real.sqrt 2 : ℝ) ≠ 0 :=
  div_ne_zero (by norm_num) (Real.sqrt_pos.2 (by norm_num)).ne'

/-- Core of G6-001 from the landed gradient identities, real-covector identities and canonical relations. -/
theorem core6001 (u : PhysicalL2)
    (hgrad : ∀ j : Bool × ℤ,
      jacobianAdjoint u (physicalFourierBasis j) = gradient (physicalCoordinate j) u)
    (hcoord : ∀ j : Bool × ℤ, gradient (physicalCoordinate j) u =
      if j.1 then
        (1 / Real.sqrt 2 : ℝ) •
          pairGradientProjection (pairGradient (cartesianX j.2) (realSlice u))
      else
        (-1 / Real.sqrt 2 : ℝ) •
          pairGradientProjection (pairGradient (cartesianY j.2) (realSlice u)))
    (hX : ∀ n : ℤ, star (pairGradientCLM (fderiv ℂ (cartesianX n) (realSlice u))).2 =
      (pairGradientCLM (fderiv ℂ (cartesianX n) (realSlice u))).1)
    (hY : ∀ n : ℤ, star (pairGradientCLM (fderiv ℂ (cartesianY n) (realSlice u))).2 =
      (pairGradientCLM (fderiv ℂ (cartesianY n) (realSlice u))).1)
    (h40 : ∀ m n : ℤ,
      pairPoisson (cartesianX m) (cartesianX n) (realSlice u) = 0 ∧
      pairPoisson (cartesianX m) (cartesianY n) (realSlice u) =
        -(if m = n then (1 : ℂ) else 0) ∧
      pairPoisson (cartesianY m) (cartesianY n) (realSlice u) = 0) :
    Function.Injective (jacobianAdjoint u) := by
  have gT : ∀ n : ℤ, jacobianAdjoint u (physicalFourierHilbertBasis (true, n)) =
      (1 / Real.sqrt 2 : ℝ) •
        pairGradientProjection (pairGradientCLM (fderiv ℂ (cartesianX n) (realSlice u))) := by
    intro n
    rw [physicalFourierHilbertBasis_apply, hgrad, hcoord]
    rfl
  have gF : ∀ n : ℤ, jacobianAdjoint u (physicalFourierHilbertBasis (false, n)) =
      (-1 / Real.sqrt 2 : ℝ) •
        pairGradientProjection (pairGradientCLM (fderiv ℂ (cartesianY n) (realSlice u))) := by
    intro n
    rw [physicalFourierHilbertBasis_apply, hgrad, hcoord]
    rfl
  have pXY : ∀ m n : ℤ, pairPoissonCLM (fderiv ℂ (cartesianX m) (realSlice u))
      (fderiv ℂ (cartesianY n) (realSlice u)) = -(if m = n then (1 : ℂ) else 0) :=
    fun m n => (h40 m n).2.1
  have pXX : ∀ m n : ℤ, pairPoissonCLM (fderiv ℂ (cartesianX m) (realSlice u))
      (fderiv ℂ (cartesianX n) (realSlice u)) = 0 := fun m n => (h40 m n).1
  have pYY : ∀ m n : ℤ, pairPoissonCLM (fderiv ℂ (cartesianY m) (realSlice u))
      (fderiv ℂ (cartesianY n) (realSlice u)) = 0 := fun m n => (h40 m n).2.2
  have pYX : ∀ m n : ℤ, pairPoissonCLM (fderiv ℂ (cartesianY m) (realSlice u))
      (fderiv ℂ (cartesianX n) (realSlice u)) = (if n = m then (1 : ℂ) else 0) := by
    intro m n
    rw [pairPoissonCLM_antisymm, pXY n m, neg_neg]
  refine injective_of_biorth (jacobianAdjoint u) physicalFourierHilbertBasis
    (fun k => innerSL ℝ ((-Complex.I) •
      jacobianAdjoint u (physicalFourierHilbertBasis (!k.1, k.2)))) ?_
  rintro ⟨b, n⟩
  cases b
  · -- k = (false, n): sigma k = (true, n)
    refine ⟨?_, ?_⟩
    · show inner ℝ ((-Complex.I) • jacobianAdjoint u (physicalFourierHilbertBasis (true, n)))
          (jacobianAdjoint u (physicalFourierHilbertBasis (false, n))) ≠ 0
      rw [gT, gF, omega_scaled _ _ _ _ (hY n) (hX n), pYX, if_pos rfl]
      exact mul_ne_zero (mul_ne_zero neg_sqrt2_inv_ne sqrt2_inv_ne) (by norm_num)
    · rintro ⟨b', n'⟩ hne
      show inner ℝ ((-Complex.I) • jacobianAdjoint u (physicalFourierHilbertBasis (true, n)))
          (jacobianAdjoint u (physicalFourierHilbertBasis (b', n'))) = 0
      cases b'
      · have hn : n ≠ n' := fun h => hne (by rw [h])
        rw [gT, gF, omega_scaled _ _ _ _ (hY n') (hX n), pYX, if_neg hn]
        simp
      · rw [gT, gT, omega_scaled _ _ _ _ (hX n') (hX n), pXX]
        simp
  · -- k = (true, n): sigma k = (false, n)
    refine ⟨?_, ?_⟩
    · show inner ℝ ((-Complex.I) • jacobianAdjoint u (physicalFourierHilbertBasis (false, n)))
          (jacobianAdjoint u (physicalFourierHilbertBasis (true, n))) ≠ 0
      rw [gF, gT, omega_scaled _ _ _ _ (hX n) (hY n), pXY, if_pos rfl]
      exact mul_ne_zero (mul_ne_zero sqrt2_inv_ne neg_sqrt2_inv_ne) (by norm_num)
    · rintro ⟨b', n'⟩ hne
      show inner ℝ ((-Complex.I) • jacobianAdjoint u (physicalFourierHilbertBasis (false, n)))
          (jacobianAdjoint u (physicalFourierHilbertBasis (b', n'))) = 0
      cases b'
      · rw [gF, gF, omega_scaled _ _ _ _ (hY n') (hY n), pYY]
        simp
      · have hn : n' ≠ n := fun h => hne (by rw [h])
        rw [gF, gT, omega_scaled _ _ _ _ (hX n') (hY n), pXY, if_neg hn]
        simp

end
end G6001Aux
end NlsGge.GKDefinitionDesign

import Mathlib
import NlsGge.ThirdConsultation.F.Round5
import NlsGge.ThirdConsultation.F.Wick018A
import NlsGge.Hierarchy.ContractionMonomialBound38
import NlsGge.Hierarchy.ComplexGaussianWick38
import NlsGge.Hierarchy.FiniteOrderGaussianTail38

                                                                                                                        
                                                                                                                  
                                                                                                                            
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.Measure

namespace NlsGge.ThirdConsultation.F
attribute [local instance] Classical.propDecidable

namespace Wick018B

/-- Finite-cutoff tail covariance: the sum of `covarianceTerm` over the block `N < |n| ≤ N'`. -/
def tailCovarianceFin (m : ℕ) (β : ℕ → ℝ) (N N' a b : ℕ) : ℂ :=
  ∑ n ∈ truncFinset38 N N', covarianceTerm m β N a b n

/-- Finite-cutoff matching sum (zero when the unbarred/barred counts differ). -/
def wickMatchingSumFin (m : ℕ) (β : ℕ → ℝ) (N N' : ℕ) (q : Jet →₀ ℕ)
    (R : Finset (OccType38 q)) : ℂ :=
  if (tailUnbar q R).card = (tailBar q R).card then
    ∑ σ : (↥(tailUnbar q R) ≃ ↥(tailBar q R)),
      ∏ i : ↥(tailUnbar q R),
        tailCovarianceFin m β N N' (occOrd38 q i.1) (occOrd38 q (σ i).1)
  else 0

theorem exp_mul_star' (n : ℤ) (x : ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ)) *
      star (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ))) = 1 := by
  have h : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ)) =
      ((2 * Real.pi * n * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h,
    Complex.norm_exp_ofReal_mul_I]
  simp

/-- B1: the `Fin K` covariance of the jets of `Y_{N,N'}` is the finite tail covariance. -/
theorem cov_fin (m : ℕ) (β : ℕ → ℝ) (N N' a b : ℕ) (x : ℝ) :
    ∑ k : Fin (truncFinset38 N N').card,
      tailCoef38 (truncIota38 N N') a k x * star (tailCoef38 (truncIota38 N N') b k x) /
        (finiteHierarchyRate38 m β (truncIota38 N N' k) : ℂ) =
      tailCovarianceFin m β N N' a b := by
  unfold tailCovarianceFin
  rw [← Finset.sum_coe_sort (truncFinset38 N N')]
  refine Fintype.sum_equiv (truncFinset38 N N').equivFin.symm _ _ (fun k => ?_)
  have hk : N < (truncIota38 N N' k).natAbs := by
    have := truncIota_gt38 N N' k
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this
  show _ = covarianceTerm m β N a b (truncIota38 N N' k)
  unfold covarianceTerm tailCoef38
  rw [if_pos hk, star_mul']
  have h := exp_mul_star' (truncIota38 N N' k) x
  calc _ = ((2 * (Real.pi : ℂ) * Complex.I * ((truncIota38 N N' k : ℤ) : ℂ)) ^ a *
        star ((2 * (Real.pi : ℂ) * Complex.I * ((truncIota38 N N' k : ℤ) : ℂ)) ^ b)) *
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((truncIota38 N N' k : ℤ) : ℂ) * (x : ℂ)) *
          star (Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
            ((truncIota38 N N' k : ℤ) : ℂ) * (x : ℂ)))) /
        (finiteHierarchyRate38 m β (truncIota38 N N' k) : ℂ) := by push_cast; ring
    _ = _ := by rw [h, mul_one]

/-- Exact finite Wick formula for Finset-indexed products on `cgPi`. -/
theorem integral_cgPi_wick_finset {K : ℕ} {O : Type*} [DecidableEq O] (a : Fin K → ℝ)
    (ha : ∀ n, 0 < a n) (A B : Finset O) (c e : O → Fin K → ℂ) :
    ∫ g : Fin K → ℂ, (∏ i ∈ A, ∑ n, c i n * g n) * ∏ j ∈ B, star (∑ n, e j n * g n) ∂cgPi a =
      if A.card = B.card then
        ∑ σ : (↥A ≃ ↥B), ∏ i : ↥A, ∑ n, c i.1 n * star (e (σ i).1 n) / (a n : ℂ)
      else 0 := by
  classical
  by_cases h : A.card = B.card
  · rw [if_pos h]
    let eA : A ≃ Fin A.card := A.equivFin
    let eB : B ≃ Fin A.card := Finset.equivFinOfCardEq h.symm
    have hint : (fun g : Fin K → ℂ => (∏ i ∈ A, ∑ n, c i n * g n) *
        ∏ j ∈ B, star (∑ n, e j n * g n)) =
        fun g => (∏ t : Fin A.card, ∑ n, c (eA.symm t : O) n * g n) *
          ∏ t : Fin A.card, star (∑ n, e (eB.symm t : O) n * g n) := by
      funext g
      rw [prod_finset_eq_fin38 A eA (fun i => ∑ n, c i n * g n),
        prod_finset_eq_fin38 B eB (fun j => star (∑ n, e j n * g n))]
    rw [hint, integral_cgPi_wick_eq a ha (fun t => c (eA.symm t : O)) (fun t => e (eB.symm t : O))]
    exact Wick018A.sum_perm_eq_sum_equiv eA.symm eB.symm
      (fun i j => ∑ n, c i.1 n * star (e j.1 n) / (a n : ℂ))
  · rw [if_neg h]
    have hint : (fun g : Fin K → ℂ => (∏ i ∈ A, ∑ n, c i n * g n) *
        ∏ j ∈ B, star (∑ n, e j n * g n)) =
        fun g => (∏ t : Fin A.card, ∑ n, c (A.equivFin.symm t : O) n * g n) *
          ∏ t : Fin B.card, star (∑ n, e (B.equivFin.symm t : O) n * g n) := by
      funext g
      rw [prod_finset_eq_fin38 A A.equivFin (fun i => ∑ n, c i n * g n),
        prod_finset_eq_fin38 B B.equivFin (fun j => star (∑ n, e j n * g n))]
    rw [hint, integral_cgPi_wick_ne h a ha]

theorem filter_unbar (q : Jet →₀ ℕ) (R : Finset (OccType38 q)) :
    (Finset.univ \ R).filter (fun t => ¬ occBar38 q t = true) = tailUnbar q R := by
  unfold tailUnbar
  exact Finset.filter_congr (fun t _ => by simp)

theorem filter_bar (q : Jet →₀ ℕ) (R : Finset (OccType38 q)) :
    (Finset.univ \ R).filter (fun t => occBar38 q t = true) = tailBar q R := by
  unfold tailBar
  exact Finset.filter_congr (fun t _ => by simp)

/-- B2 (W3+W4): for each low-occurrence set `R`, the `x`-integral of the expansion term is
`cgPi`-integrable in `g`, and its `cgPi` expectation is the `x`-integral of the low jets times the
finite-cutoff matching sum (Fubini on `[0,1]`). -/
theorem finite_wick_term (m : ℕ) (β : ℕ → ℝ) (hq : ∀ n : ℤ, 0 < finiteHierarchyRate38 m β n)
    (N N' : ℕ) (z : FourierPlane N) (q : Jet →₀ ℕ) (R : Finset (OccType38 q)) :
    Integrable (fun g : Fin (truncFinset38 N N').card → ℂ => ∫ x in (0 : ℝ)..1,
      termR38 (occBar38 q) (occOrd38 q) N z (truncIota38 N N') R x g)
      (cgPi (fun k => finiteHierarchyRate38 m β (truncIota38 N N' k))) ∧
    ∫ g : Fin (truncFinset38 N N').card → ℂ, (∫ x in (0 : ℝ)..1,
      termR38 (occBar38 q) (occOrd38 q) N z (truncIota38 N N') R x g)
        ∂cgPi (fun k => finiteHierarchyRate38 m β (truncIota38 N N' k)) =
      ∫ x in (0 : ℝ)..1, (∏ i ∈ R, jet38 (occBar38 q) (occOrd38 q) (planeReal N z) i x) *
        wickMatchingSumFin m β N N' q R := by
  classical
  set K := (truncFinset38 N N').card
  set a : Fin K → ℝ := fun k => finiteHierarchyRate38 m β (truncIota38 N N' k) with ha_def
  have ha : ∀ k, 0 < a k := fun k => hq _
  set W : ℝ → ℂ := fun x => ∏ i ∈ R, jet38 (occBar38 q) (occOrd38 q) (planeReal N z) i x with hW_def
  have hW : Continuous W :=
    continuous_finset_prod _ fun t _ => continuous_jet38 (occBar38 q) (occOrd38 q) N z t
  set c : OccType38 q → Fin K → ℝ → ℂ := fun i n x =>
    tailCoef38 (truncIota38 N N') (occOrd38 q i) n x with hc_def
  have hc : ∀ i n, Continuous (c i n) := fun i n => continuous_tailCoef38 _ _ _
  set F : ℝ → (Fin K → ℂ) → ℂ := fun x g => W x *
      ((∏ i ∈ tailUnbar q R, ∑ n, c i n x * g n) *
        ∏ j ∈ tailBar q R, star (∑ n, c j n x * g n)) with hF
  have hterm : ∀ x g, termR38 (occBar38 q) (occOrd38 q) N z (truncIota38 N N') R x g = F x g := by
    intro x g
    unfold termR38
    rw [filter_unbar, filter_bar]
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (cgPi a)) :=
    integrable_term38 a (tailUnbar q R) (tailBar q R) W hW c c hc hc
  simp only [hterm, intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  refine ⟨hint.integral_prod_right, ?_⟩
  rw [← integral_integral_swap hint]
  have hx : ∀ x, ∫ g, F x g ∂cgPi a = W x * wickMatchingSumFin m β N N' q R := by
    intro x
    simp only [hF]
    rw [integral_const_mul, integral_cgPi_wick_finset a ha (tailUnbar q R) (tailBar q R)
      (fun i n => c i n x) (fun j n => c j n x)]
    unfold wickMatchingSumFin
    split_ifs with h
    · congr 1
      refine Finset.sum_congr rfl fun σ _ => Finset.prod_congr rfl fun i _ => ?_
      exact cov_fin m β N N' _ _ x
    · rfl
  simp only [hx]
  rfl

end Wick018B
end NlsGge.ThirdConsultation.F
end

import NlsGge.GK38.AbelianFreeProbe
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! The actual Abelian Fn has sequence derivative 2·id at the free origin.
The all-complex single-coordinate identity is differentiated before the bounded
linear map is identified by the canonical lp density/extensionality theorem. -/
set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.P3FreeDerivative
noncomputable section

/-- Transport an ambient excitation to the genuine omitted coordinate. -/
theorem restrict_single (n : ℤ) (r : P2Index38 n) (t : ℂ) :
    p2Restrict38 n (t • lp.single 2 r.1 (1 : ℂ)) = lp.single 2 r t := by
  apply Subtype.ext
  funext m
  rw [p2Restrict_apply38]
  by_cases h : m = r
  · subst m
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      lp.single_apply_self, mul_one]
  · have hv : m.1 ≠ r.1 := fun hv => h (Subtype.ext hv)
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 r.1 (1 : ℂ) hv, mul_zero,
      lp.single_apply_ne (E := fun _ : P2Index38 n => ℂ) 2 r t h]

/-- Every complex excitation has the book's exact raw-period normalization. -/
theorem actualFn_single (n : ℤ) (r : P2Index38 n) (t : ℂ) :
    p2Fn38 n ((0 : PotPair), lp.single 2 r t) = lp.single 2 r (2 * t) := by
  apply Subtype.ext
  funext m
  rw [← restrict_single n r t, P2FreeProbe.actual_Fn_single n r.1 r.2 t m]
  by_cases h : m = r
  · subst m
    simp only [ite_true, lp.single_apply_self]
  · have hv : m.1 ≠ r.1 := fun hv => h (Subtype.ext hv)
    simp only [hv, ite_false, lp.single_apply_ne (E := fun _ : P2Index38 n => ℂ) 2 r (2 * t) h]

theorem actualFn_zero (n : ℤ) :
    p2Fn38 n ((0 : PotPair), (0 : P2Space38 n)) = 0 := by
  let r : P2Index38 n := ⟨n + 1, by omega⟩
  simpa only [lp.single_zero, mul_zero] using actualFn_single n r 0

theorem free_analytic (n : ℤ) :
    AnalyticAt ℂ (fun s : P2Space38 n => p2Fn38 n ((0 : PotPair), s)) 0 := by
  exact (p2Fn_analytic38 n ((0 : PotPair), (0 : P2Space38 n))
    ⟨free_mem_gkW, mem_univ _⟩).comp (analyticAt_const.prod analyticAt_id)

/-- The Fréchet derivative is identified on all of lp2, using continuity and density. -/
theorem free_fderiv (n : ℤ) :
    fderiv ℂ (fun s : P2Space38 n => p2Fn38 n ((0 : PotPair), s))
      (0 : P2Space38 n) =
      (2 : ℂ) • ContinuousLinearMap.id ℂ (P2Space38 n) := by
  let f : P2Space38 n → P2Space38 n :=
    fun s => p2Fn38 n ((0 : PotPair), s)
  have hf : HasFDerivAt f (fderiv ℂ f 0) 0 :=
    (free_analytic n).differentiableAt.hasFDerivAt
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro r
  let S : ℂ →L[ℂ] P2Space38 n :=
    lp.singleContinuousLinearMap ℂ (fun _ : P2Index38 n => ℂ) 2 r
  have hfS : HasFDerivAt f (fderiv ℂ f 0) (S 0) := by
    simpa only [map_zero] using hf
  have hcomp : HasFDerivAt (f ∘ S) ((fderiv ℂ f 0).comp S) 0 :=
    hfS.comp 0 (S.hasFDerivAt (x := 0))
  have hline : f ∘ S = ((2 : ℂ) • S : ℂ →L[ℂ] P2Space38 n) := by
    funext t
    change p2Fn38 n ((0 : PotPair), lp.single 2 r t) =
      (2 : ℂ) • lp.single 2 r t
    rw [actualFn_single]
    simpa only [smul_eq_mul] using lp.single_smul (E := fun _ : P2Index38 n => ℂ) 2 r (2 : ℂ) t
  rw [hline] at hcomp
  have heq : (fderiv ℂ f 0).comp S = (2 : ℂ) • S :=
    hcomp.unique (((2 : ℂ) • S).hasFDerivAt (x := 0))
  exact heq.trans (by ext t; rfl)

theorem free_hasStrictFDerivAt (n : ℤ) :
    HasStrictFDerivAt
      (fun s : P2Space38 n => p2Fn38 n ((0 : PotPair), s))
      ((2 : ℂ) • ContinuousLinearMap.id ℂ (P2Space38 n))
      (0 : P2Space38 n) := by
  simpa only [free_fderiv n] using (free_analytic n).hasStrictFDerivAt

/-- The same actual derivative is the sequence block of the joint complex derivative. -/
theorem joint_inr_fderiv (n : ℤ) :
    (fderiv ℂ (p2Fn38 n) ((0 : PotPair), (0 : P2Space38 n))).comp
      (ContinuousLinearMap.inr ℂ PotPair (P2Space38 n)) =
      (2 : ℂ) • ContinuousLinearMap.id ℂ (P2Space38 n) := by
  have hj := (p2Fn_analytic38 n ((0 : PotPair), (0 : P2Space38 n))
    ⟨free_mem_gkW, mem_univ _⟩).differentiableAt.hasFDerivAt
  have hcomp := hj.comp 0
    ((ContinuousLinearMap.inr ℂ PotPair (P2Space38 n)).hasFDerivAt
      (x := (0 : P2Space38 n)))
  change HasFDerivAt
    (fun s : P2Space38 n => p2Fn38 n ((0 : PotPair), s))
    ((fderiv ℂ (p2Fn38 n) ((0 : PotPair), (0 : P2Space38 n))).comp
      (ContinuousLinearMap.inr ℂ PotPair (P2Space38 n))) 0 at hcomp
  exact hcomp.unique (free_hasStrictFDerivAt n).hasFDerivAt

end
end NlsGge.GK38.P3FreeDerivative

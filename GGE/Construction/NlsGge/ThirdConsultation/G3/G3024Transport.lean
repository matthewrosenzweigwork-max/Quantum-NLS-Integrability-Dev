import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G2.G2072Host
import NlsGge.ThirdConsultation.G2.G2073Support1
import NlsGge.Atomic.G2.G2021
import NlsGge.ThirdConsultation.G3.G3005C6Core
import Armstrong.Work.ActualScalarCartesianModels

                                                                                                        
                                                                                                                         
                                                                                                     
                                                                                                                          
                                                                                                                             
                                                                                                                              
                                                                                                                                                               
                                                                                                                     
                                                                                                      
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G3024Transport
noncomputable section

/-- The omitted ratio in terms of `psi` and `rootProduct` (no nonvanishing needed). -/
theorem ratio_eq (n : ℤ) (φ : PotPair) (w : ℂ) :
    p2OmittedRatio38 n ((φ, p2Extend38 n (sourceF n φ)), w) =
      -(psi n φ w) / (2 * rootProduct n (φ, w)) := by
  have hpsi : psi n φ w = -2 * Lib.omitProd n (p2Extend38 n (sourceF n φ)) w := rfl
  have hpi : (Lib.piN n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero n)
  rw [hpsi]
  unfold p2OmittedRatio38 rootProduct
  by_cases hA : a5OmittedRootProduct38 n (φ, w) = 0
  · simp [hA]
  · field_simp

theorem pair_sum (n : ℤ) (φ : PotPair) (a b : ℂ)
    (hab : ({a, b} : Set ℂ) = {lamMinus φ n, lamPlus φ n}) :
    a + b = lamMinus φ n + lamPlus φ n ∧
    (∀ z : ℂ, (z - a) * (z - b) = (z - lamMinus φ n) * (z - lamPlus φ n)) := by
  rcases Set.pair_eq_pair_iff.1 hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by rw [h1, h2], fun z => by rw [h1, h2]⟩
  · exact ⟨by rw [h1, h2]; ring, fun z => by rw [h1, h2]; ring⟩

theorem seg_ball (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW) (a b : ℂ)
    (hab : ({a, b} : Set ℂ) = {lamMinus φ n, lamPlus φ n}) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    a + (t : ℂ) * (muSeq φ n - a) ∈ ball (discC φ n) (discR φ n) := by
  obtain ⟨c, N, hg, hspec⟩ := isolating_family38 φ hφ
  have hmem_a : a ∈ ball (discC φ n) (discR φ n) := by
    have h : a ∈ ({lamMinus φ n, lamPlus φ n} : Set ℂ) := by rw [← hab]; simp
    rcases h with h | h
    · rw [h]; exact (hspec.1 n).1 (left_mem_segment ℝ _ _)
    · rw [h]; exact (hspec.1 n).1 (right_mem_segment ℝ _ _)
  have hmu : muSeq φ n ∈ ball (discC φ n) (discR φ n) := (hspec.1 n).2.1
  have := (convex_ball (discC φ n) (discR φ n)) hmem_a hmu (sub_nonneg.2 ht.2) ht.1
    (by ring)
  convert this using 1
  simp only [Complex.real_smul, smul_eq_mul]
  push_cast
  ring

theorem g3024_segment_exponential (n : ℤ) (phi : PotPair) (hphi : phi ∈ sourceW)
    (hgam : lamPlus phi n - lamMinus phi n ≠ 0) (a b rw : ℂ) (rs : ℝ → ℂ)
    (hab : ({a, b} : Set ℂ) = {lamMinus phi n, lamPlus phi n})
    (hw0 : rw ≠ 0) (hwsq : rw ^ 2 = muSeq phi n - a)
    (hc : ContinuousOn rs (Icc (0 : ℝ) 1)) (h0 : ∀ t ∈ Icc (0 : ℝ) 1, rs t ≠ 0)
    (hsq : ∀ t ∈ Icc (0 : ℝ) 1, rs t ^ 2 = a + (t : ℂ) * (muSeq phi n - a) - b)
    (hsign : 2 * Complex.I * rootProduct n (phi, muSeq phi n) * rw * rs 1 =
      antiDiscrim phi (muSeq phi n))
    (hint : IntervalIntegrable (fun t : ℝ =>
      (psi n phi (a + (t : ℂ) * (muSeq phi n - a)) * rw /
        (2 * Complex.I * rootProduct n (phi, a + (t : ℂ) * (muSeq phi n - a)) * rs t)) /
        (Real.sqrt t : ℂ)) volume 0 1) :
    gk16ActualScalarZPlus38 sourceF n phi = (b - a) * Complex.exp (Complex.I *
      ∫ t in (0 : ℝ)..1,
        (psi n phi (a + (t : ℂ) * (muSeq phi n - a)) * rw /
          (2 * Complex.I * rootProduct n (phi, a + (t : ℂ) * (muSeq phi n - a)) * rs t)) /
          (Real.sqrt t : ℂ)) := by
  have hgk : phi ∈ gkW := sourceFamily.W_gk hphi
  have hfam := isolating_family38 phi hgk
  obtain ⟨hsum, hprod⟩ := pair_sum n phi a b hab
  have hperiod : abelianPeriod38 n phi (p2FullNumerator38 n (p2Extend38 n (sourceF n phi))) =
      2 * (Real.pi : ℂ) := by
    have h := sourceFamily.F_period n phi hphi n
    rw [if_pos rfl] at h
    exact h
  have hR := gk16_own_correction_coefficient38 phi hgk (discC phi) (discR phi) hfam n
    (p2Extend38 n (sourceF n phi)) hperiod
  obtain ⟨R, hRdef⟩ : ∃ R : ℂ → ℂ, R = gk16OwnCorrectionCoefficient38 phi n
      (p2Extend38 n (sourceF n phi)) (discC phi n) (discR phi n) := ⟨_, rfl⟩
  have hRan : AnalyticOnNhd ℂ R (ball (discC phi n) (discR phi n)) := by rw [hRdef]; exact hR.1
  have hRode : ∀ z ∈ ball (discC phi n) (discR phi n),
      (z - lamMinus phi n) * (z - lamPlus phi n) * deriv R z +
        (z - (lamMinus phi n + lamPlus phi n) / 2) * R z =
          p2OmittedRatio38 n ((phi, p2Extend38 n (sourceF n phi)), z) - 1 := by
    rw [hRdef]; exact hR.2
  obtain ⟨z, hzdef⟩ : ∃ z : ℝ → ℂ, z = fun t : ℝ => a + (t : ℂ) * (muSeq phi n - a) := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ → ℂ, v = fun t : ℝ => (Real.sqrt t : ℂ) * rw * rs t := ⟨_, rfl⟩
  have hzball : ∀ t ∈ Icc (0 : ℝ) 1, z t ∈ ball (discC phi n) (discR phi n) := by
    intro t ht; rw [hzdef]; exact seg_ball n phi hgk a b hab t ht
  have hzc : Continuous z := by rw [hzdef]; fun_prop
  have hz0 : z 0 = a := by rw [hzdef]; simp
  have hz1 : z 1 = muSeq phi n := by rw [hzdef]; simp
  have hzd : ∀ t : ℝ, HasDerivAt z (muSeq phi n - a) t := by
    intro t
    rw [hzdef]
    simpa using (((hasDerivAt_id t).ofReal_comp).mul_const (muSeq phi n - a)).const_add a
  have hdom : ∀ t ∈ Icc (0 : ℝ) 1, (phi, z t) ∈ a5OmittedRootDomain38 n := fun t ht =>
    ⟨hgk, fun k hk => closedBall_avoids_other_gaps phi hgk n k hk (z t)
      (ball_subset_closedBall (hzball t ht))⟩
  have hrPc : ContinuousOn (fun t : ℝ => rootProduct n (phi, z t)) (Icc (0 : ℝ) 1) := by
    intro t ht
    have h1 : ContinuousAt (rootProduct n) (phi, z t) := ((G2_021 n).2.1 _ (hdom t ht)).continuousAt
    exact (h1.comp (f := fun s : ℝ => (phi, z s))
      (continuousAt_const.prodMk hzc.continuousAt)).continuousWithinAt
  have hrP0 : ∀ t ∈ Icc (0 : ℝ) 1, rootProduct n (phi, z t) ≠ 0 := fun t ht =>
    (G2_021 n).2.2 _ (hdom t ht)
  have hvc : ContinuousOn v (Icc (0 : ℝ) 1) := by
    rw [hvdef]
    exact ((Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousOn.mul
      continuousOn_const).mul hc
  have hvsq : ∀ t ∈ Icc (0 : ℝ) 1, v t ^ 2 =
      (z t - lamMinus phi n) * (z t - lamPlus phi n) := by
    intro t ht
    have hs : ((Real.sqrt t : ℝ) : ℂ) ^ 2 = t := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt ht.1]
    have e : v t ^ 2 = ((Real.sqrt t : ℝ) : ℂ) ^ 2 * rw ^ 2 * rs t ^ 2 := by
      rw [hvdef]; ring
    rw [e, hs, hwsq, hsq t ht, ← hprod (z t)]
    rw [hzdef]
    ring
  have hvne : ∀ t ∈ Ioo (0 : ℝ) 1, v t ≠ 0 := by
    intro t ht
    have hs : (Real.sqrt t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne'
    rw [hvdef]
    exact mul_ne_zero (mul_ne_zero hs hw0) (h0 t ⟨ht.1.le, ht.2.le⟩)
  have hv0 : v 0 = 0 := by rw [hvdef]; simp
  have hv1 : v 1 = rw * rs 1 := by rw [hvdef]; simp
  -- model and density
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℂ, G = fun u => (2 * ((lamMinus phi n + lamPlus phi n) / 2 - z u) -
      2 * (-1 : ℂ) * v u) * Complex.exp ((-1 : ℂ) * v u * R (z u)) := ⟨_, rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ → ℂ, f = fun t : ℝ =>
      (psi n phi (a + (t : ℂ) * (muSeq phi n - a)) * rw /
        (2 * Complex.I * rootProduct n (phi, a + (t : ℂ) * (muSeq phi n - a)) * rs t)) /
        (Real.sqrt t : ℂ) := ⟨_, rfl⟩
  have hint' : IntervalIntegrable f volume 0 1 := by rw [hfdef]; exact hint
  have hfc : ContinuousOn f (Ioo (0 : ℝ) 1) := by
    have hpsi : Continuous (psi n phi) :=
      continuousOn_univ.mp (p6PsiNumerator_entire38 n (sourceF n) phi).continuousOn
    have hz' : ContinuousOn z (Ioo (0 : ℝ) 1) := hzc.continuousOn
    have hnum : ContinuousOn (fun t : ℝ => psi n phi (z t) * rw) (Ioo (0 : ℝ) 1) :=
      (hpsi.comp_continuousOn hz').mul continuousOn_const
    have hden : ContinuousOn (fun t : ℝ => 2 * Complex.I * rootProduct n (phi, z t) * rs t)
        (Ioo (0 : ℝ) 1) :=
      ((continuousOn_const.mul (hrPc.mono Ioo_subset_Icc_self)).mul (hc.mono Ioo_subset_Icc_self))
    have h1 := hnum.div hden (fun t ht => mul_ne_zero (mul_ne_zero
      (mul_ne_zero two_ne_zero Complex.I_ne_zero) (hrP0 t ⟨ht.1.le, ht.2.le⟩))
      (h0 t ⟨ht.1.le, ht.2.le⟩))
    have h2 := h1.div (Complex.continuous_ofReal.comp_continuousOn Real.continuous_sqrt.continuousOn)
      (fun t ht => Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne')
    rw [hfdef]
    refine h2.congr (fun t _ => ?_)
    simp only [Pi.div_apply, Function.comp_apply, hzdef]
  have hGc : ContinuousOn G (Icc (0 : ℝ) 1) := by
    rw [hGdef]
    have hRc : ContinuousOn (fun u => R (z u)) (Icc (0 : ℝ) 1) :=
      hRan.continuousOn.comp hzc.continuousOn (fun t ht => hzball t ht)
    exact ((continuousOn_const.sub hzc.continuousOn).const_mul 2 |>.sub
      (continuousOn_const.mul hvc)).mul (((continuousOn_const.mul hvc).mul hRc).cexp)
  have hGd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt G (Complex.I * f t * G t) t := by
    intro t ht
    have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have htn : Icc (0 : ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hQ : HasDerivAt (fun w : ℂ => (w - lamMinus phi n) * (w - lamPlus phi n))
        (2 * (z t - (lamMinus phi n + lamPlus phi n) / 2)) (z t) := by
      apply (((hasDerivAt_id (z t)).sub_const (lamMinus phi n)).mul
        ((hasDerivAt_id (z t)).sub_const (lamPlus phi n))).congr_deriv
      simp only [id_eq]
      ring
    have he : (fun u => v u ^ 2) =ᶠ[𝓝 t]
        (fun w : ℂ => (w - lamMinus phi n) * (w - lamPlus phi n)) ∘ z := by
      filter_upwards [htn] with u hu
      exact hvsq u hu
    have hvd := G3005C6.root_hasDerivAt (hvc.continuousAt htn) (hvne t ht)
      ((hQ.comp t (hzd t)).congr_of_eventuallyEq he)
    have hvn := hvne t ht
    have hvdd : v t * ((2 * (z t - (lamMinus phi n + lamPlus phi n) / 2) * (muSeq phi n - a)) /
        (2 * v t)) = (z t - (lamMinus phi n + lamPlus phi n) / 2) * (muSeq phi n - a) := by
      field_simp
    have hd := gk16_correction_real_hasDerivAt38 (lamMinus phi n) (lamPlus phi n) (-1)
      (p2OmittedRatio38 n ((phi, p2Extend38 n (sourceF n phi)), z t)) z v R t
      (muSeq phi n - a) _ (deriv R (z t)) (by norm_num) hvn (hzd t) hvd
      ((hRan _ (hzball t htcc)).differentiableAt.hasDerivAt)
      (hvsq t htcc) hvdd (hRode _ (hzball t htcc))
    rw [hGdef]
    refine hd.congr_deriv ?_
    have hs : (Real.sqrt t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne'
    have hr := hrP0 t htcc
    have hρ := h0 t htcc
    have hq := ratio_eq n phi (z t)
    have hfz : f t = psi n phi (z t) * rw / (2 * Complex.I * rootProduct n (phi, z t) * rs t) /
        (Real.sqrt t : ℂ) := by rw [hfdef, hzdef]
    rw [hq, hfz, ← hwsq, hvdef]
    simp only []
    field_simp
  have htr := gk16_compact_exponential_transport38 0 1 zero_le_one Complex.I f G hGc hint' hfc hGd
  have htau : tauN phi n = (lamMinus phi n + lamPlus phi n) / 2 := by
    rw [tauN_value38 phi hgk n]
    ring
  have hG0 : G 0 = b - a := by
    rw [hGdef]
    simp only [hz0, hv0, mul_zero, zero_mul, sub_zero, Complex.exp_zero, mul_one]
    rw [← hsum]
    ring
  have hH : gk16TerminalRoot38 n phi = v 1 := by
    have hp : ((2 * Complex.I) / (Lib.piN n : ℂ)) * a5OmittedRootProduct38 n (phi, muSeq phi n) =
        2 * Complex.I * rootProduct n (phi, muSeq phi n) := by
      have hpi : (Lib.piN n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero n)
      unfold rootProduct
      field_simp
    have hne : 2 * Complex.I * rootProduct n (phi, muSeq phi n) ≠ 0 := by
      have := hrP0 1 ⟨zero_le_one, le_rfl⟩
      rw [hz1] at this
      exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) this
    unfold gk16TerminalRoot38
    rw [hp, ← hsign, hv1, div_eq_iff hne]
    ring
  have hG1 : G 1 = gk16ActualScalarZPlus38 sourceF n phi := by
    unfold gk16ActualScalarZPlus38
    rw [hGdef]
    simp only [hRdef, hz1, ← hH, htau]
    congr 2 <;> ring
  rw [← hG1, htr, hG0, hfdef]

end
end G3024Transport
end NlsGge.GKDefinitionDesign

import Mathlib
import NlsGge.Measure.ComplexGaussian
import NlsGge.Measure.CountableGaussian
import NlsGge.Hierarchy.GaussianTailCovarianceBernstein38
import NlsGge.Hierarchy.FiniteOrderGaussianTail38

                                                                                                                                                                                                                                                                                                                                                                                                                                                         
                                                                                      
                                                                                                   
                                                                                                 
                                         

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace NlsGge.ThirdConsultation.F
namespace F016L1

theorem sq_pair_expand (p : ℝ × ℝ) :
    (p.1 + p.2 * Complex.I) ^ 2 =
      ((p.1 ^ 2 - p.2 ^ 2 : ℝ) : ℂ) + ((2 * p.1 * p.2 : ℝ) : ℂ) * Complex.I := by
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem integral_sq_prod (v : ℝ≥0) :
    ∫ p : ℝ × ℝ, p.1 ^ 2 ∂((gaussianReal 0 v).prod (gaussianReal 0 v)) = (v : ℝ) := by
  have h := integral_prod_mul (μ := gaussianReal 0 v) (ν := gaussianReal 0 v)
    (fun x : ℝ => x ^ 2) (fun _ : ℝ => (1 : ℝ))
  simp only [mul_one, integral_const, probReal_univ, smul_eq_mul, mul_one,
    NlsGge.Measure.integral_realGaussian_sq] at h
  exact h

theorem integral_sq_prod' (v : ℝ≥0) :
    ∫ p : ℝ × ℝ, p.2 ^ 2 ∂((gaussianReal 0 v).prod (gaussianReal 0 v)) = (v : ℝ) := by
  have h := integral_prod_mul (μ := gaussianReal 0 v) (ν := gaussianReal 0 v)
    (fun _ : ℝ => (1 : ℝ)) (fun y : ℝ => y ^ 2)
  simp only [one_mul, integral_const, probReal_univ, smul_eq_mul, mul_one,
    NlsGge.Measure.integral_realGaussian_sq] at h
  exact h

theorem integral_mul_prod_zero (v : ℝ≥0) :
    ∫ p : ℝ × ℝ, p.1 * p.2 ∂((gaussianReal 0 v).prod (gaussianReal 0 v)) = 0 := by
  have h := integral_prod_mul (μ := gaussianReal 0 v) (ν := gaussianReal 0 v)
    (fun x : ℝ => x) (fun y : ℝ => y)
  simp only [integral_id_gaussianReal, mul_zero] at h
  exact h

theorem integral_complexGaussian_sq_zero (a : ℝ) (ha : 0 < a) :
    ∫ z : ℂ, z ^ 2 ∂NlsGge.Measure.complexGaussian a = 0 := by
  unfold NlsGge.Measure.complexGaussian
  rw [integral_map (Complex.measurableEquivRealProd.symm.measurable.aemeasurable)
    (by fun_prop)]
  have hfun : ∀ p : ℝ × ℝ, (Complex.measurableEquivRealProd.symm p) ^ 2 =
      ((p.1 ^ 2 - p.2 ^ 2 : ℝ) : ℂ) + ((2 * p.1 * p.2 : ℝ) : ℂ) * Complex.I := by
    intro p
    apply Complex.ext <;> simp [sq] <;> ring
  simp only [hfun]
  set v := NlsGge.Measure.componentVariance a with hv
  have hi1 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) ((gaussianReal 0 v).prod (gaussianReal 0 v)) := by
    have := Integrable.mul_prod (NlsGge.Measure.integrable_realGaussian_sq v)
      (integrable_const (1 : ℝ) (μ := gaussianReal 0 v))
    simpa using this
  have hi2 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) ((gaussianReal 0 v).prod (gaussianReal 0 v)) := by
    have := Integrable.mul_prod (integrable_const (1 : ℝ) (μ := gaussianReal 0 v))
      (NlsGge.Measure.integrable_realGaussian_sq v)
    simpa using this
  have hid : Integrable (fun x : ℝ => x) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal (μ := 0) (v := v) 1).integrable le_rfl
  have hi3 : Integrable (fun p : ℝ × ℝ => (2 * p.1 * p.2 : ℝ)) ((gaussianReal 0 v).prod (gaussianReal 0 v)) := by
    have := (Integrable.mul_prod hid hid).const_mul 2
    simpa [mul_assoc] using this
  have hre : ∫ p : ℝ × ℝ, (p.1 ^ 2 - p.2 ^ 2 : ℝ) ∂((gaussianReal 0 v).prod (gaussianReal 0 v)) = 0 := by
    rw [integral_sub hi1 hi2, integral_sq_prod, integral_sq_prod']
    ring
  have him : ∫ p : ℝ × ℝ, (2 * p.1 * p.2 : ℝ) ∂((gaussianReal 0 v).prod (gaussianReal 0 v)) = 0 := by
    have : (fun p : ℝ × ℝ => (2 * p.1 * p.2 : ℝ)) = fun p => 2 * (p.1 * p.2) := by
      funext p; ring
    rw [this, integral_const_mul, integral_mul_prod_zero, mul_zero]
  rw [integral_add, integral_mul_const]
  · rw [integral_complex_ofReal, integral_complex_ofReal, hre, him]
    simp
  · exact (hi1.sub hi2).ofReal
  · exact hi3.ofReal.mul_const Complex.I


theorem integral_complexGaussian_id_zero (a : ℝ) (ha : 0 < a) :
    ∫ z : ℂ, z ∂NlsGge.Measure.complexGaussian a = 0 := by
  unfold NlsGge.Measure.complexGaussian
  rw [integral_map (Complex.measurableEquivRealProd.symm.measurable.aemeasurable)
    (by fun_prop)]
  have hfun : ∀ p : ℝ × ℝ, (Complex.measurableEquivRealProd.symm p) =
      ((p.1 : ℝ) : ℂ) + ((p.2 : ℝ) : ℂ) * Complex.I := by
    intro p
    apply Complex.ext <;> simp
  simp only [hfun]
  set v := NlsGge.Measure.componentVariance a with hv
  have hid : Integrable (fun x : ℝ => x) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal (μ := 0) (v := v) 1).integrable le_rfl
  have hi1 : Integrable (fun p : ℝ × ℝ => p.1) ((gaussianReal 0 v).prod (gaussianReal 0 v)) := by
    have := Integrable.mul_prod hid (integrable_const (1 : ℝ) (μ := gaussianReal 0 v))
    simpa using this
  have hi2 : Integrable (fun p : ℝ × ℝ => p.2) ((gaussianReal 0 v).prod (gaussianReal 0 v)) := by
    have := Integrable.mul_prod (integrable_const (1 : ℝ) (μ := gaussianReal 0 v)) hid
    simpa using this
  have hm1 : ∫ p : ℝ × ℝ, p.1 ∂((gaussianReal 0 v).prod (gaussianReal 0 v)) = 0 := by
    have h := integral_prod_mul (μ := gaussianReal 0 v) (ν := gaussianReal 0 v)
      (fun x : ℝ => x) (fun _ : ℝ => (1 : ℝ))
    simp only [mul_one, integral_id_gaussianReal, integral_const, probReal_univ, smul_eq_mul,
      mul_one] at h
    exact h
  have hm2 : ∫ p : ℝ × ℝ, p.2 ∂((gaussianReal 0 v).prod (gaussianReal 0 v)) = 0 := by
    have h := integral_prod_mul (μ := gaussianReal 0 v) (ν := gaussianReal 0 v)
      (fun _ : ℝ => (1 : ℝ)) (fun y : ℝ => y)
    simp only [one_mul, integral_id_gaussianReal, integral_const, probReal_univ, smul_eq_mul,
      mul_one] at h
    exact h
  rw [integral_add, integral_mul_const]
  · rw [integral_complex_ofReal, integral_complex_ofReal, hm1, hm2]
    simp
  · exact hi1.ofReal
  · exact hi2.ofReal.mul_const Complex.I


end F016L1
end NlsGge.ThirdConsultation.F

set_option autoImplicit false

namespace NlsGge.ThirdConsultation.F
namespace F016L2

open NlsGge.Measure F016L1

theorem joint_eq_product (q : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n) {i j : ℤ} (hij : i ≠ j)
    (f g : ℂ → ℂ) (hf : Measurable f) (hg : Measurable g) :
    ∫ ω : ℤ → ℂ, f (ω i) * g (ω j) ∂(countableComplexGaussian q) =
      (∫ z, f z ∂complexGaussian (q i)) * (∫ z, g z ∂complexGaussian (q j)) := by
  have hmap : (countableComplexGaussian q).map (fun ω : ℤ → ℂ => (ω i, ω j)) =
      (complexGaussian (q i)).prod (complexGaussian (q j)) := by
    unfold countableComplexGaussian
    exact Measure.infinitePi_map_eval_prod (P := fun k : ℤ => complexGaussian (q k)) hij
  have hpair : Measurable (fun ω : ℤ → ℂ => (ω i, ω j)) := by fun_prop
  have hF : Measurable (fun p : ℂ × ℂ => f p.1 * g p.2) :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  have key : (fun ω : ℤ → ℂ => f (ω i) * g (ω j)) =
      (fun p : ℂ × ℂ => f p.1 * g p.2) ∘ (fun ω : ℤ → ℂ => (ω i, ω j)) := rfl
  rw [key]
  exact (integral_map hpair.aemeasurable hF.aestronglyMeasurable).symm.trans
    (by rw [hmap, integral_prod_mul])

theorem cross_conj_zero (q : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n) {n m : ℤ} (hnm : n ≠ m) :
    ∫ ω : ℤ → ℂ, ω n * star (ω m) ∂(countableComplexGaussian q) = 0 := by
  have h := joint_eq_product q hq hnm (fun z => z) (fun z => star z)
    measurable_id (by fun_prop)
  rw [h, integral_complexGaussian_id_zero (q n) (hq n), zero_mul]

theorem cross_zero (q : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n) {n m : ℤ} (hnm : n ≠ m) :
    ∫ ω : ℤ → ℂ, ω n * ω m ∂(countableComplexGaussian q) = 0 := by
  have h := joint_eq_product q hq hnm (fun z => z) (fun z => z)
    measurable_id measurable_id
  rw [h, integral_complexGaussian_id_zero (q n) (hq n), zero_mul]

theorem diag_sq_zero (q : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n) (n : ℤ) :
    ∫ ω : ℤ → ℂ, ω n ^ 2 ∂(countableComplexGaussian q) = 0 := by
  have hm : Measurable (fun ω : ℤ → ℂ => ω n) := by fun_prop
  have h2 : ∫ ω : ℤ → ℂ, ω n ^ 2 ∂(countableComplexGaussian q) =
      ∫ ω : ℤ → ℂ, (fun z : ℂ => z ^ 2) (ω n) ∂(countableComplexGaussian q) := rfl
  have h3 : ∫ ω : ℤ → ℂ, (fun z : ℂ => z ^ 2) (ω n) ∂(countableComplexGaussian q) =
      ∫ z : ℂ, z ^ 2 ∂((countableComplexGaussian q).map (fun ω : ℤ → ℂ => ω n)) :=
    (integral_map hm.aemeasurable (continuous_pow 2).aestronglyMeasurable).symm
  rw [h2, h3, countableComplexGaussian_map_eval q n]
  exact integral_complexGaussian_sq_zero (q n) (hq n)

theorem diag_conj (q : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n) (n : ℤ) :
    ∫ ω : ℤ → ℂ, ω n * star (ω n) ∂(countableComplexGaussian q) = 1 / q n := by
  have h : ∀ ω : ℤ → ℂ, ω n * star (ω n) = ((‖ω n‖ ^ 2 : ℝ) : ℂ) := by
    intro ω
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [h]
  rw [integral_complex_ofReal, integral_countableComplexGaussian_sqNorm q hq n]
  simp


end F016L2
end NlsGge.ThirdConsultation.F

namespace NlsGge.ThirdConsultation.F
namespace F016L3

open NlsGge.Measure F016L2

theorem integrable_cross (q : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n) (n m : ℤ) :
    Integrable (fun ω : ℤ → ℂ => ω n * star (ω m)) (countableComplexGaussian q) := by
  have hg : Integrable (fun ω : ℤ → ℂ => (1/2 : ℝ) * (‖ω n‖ ^ 2 + ‖ω m‖ ^ 2))
      (countableComplexGaussian q) :=
    ((integrable_countableComplexGaussian_sqNorm q n).add
      (integrable_countableComplexGaussian_sqNorm q m)).const_mul (1/2)
  refine hg.mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact ((by fun_prop : Measurable (fun ω : ℤ → ℂ => ω n)).mul
      (by fun_prop : Measurable (fun ω : ℤ → ℂ => star (ω m)))).aestronglyMeasurable
  · rw [norm_mul, norm_star]
    nlinarith [sq_nonneg (‖ω n‖ - ‖ω m‖), norm_nonneg (ω n), norm_nonneg (ω m)]

theorem sum_sq_integral (q : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n) (U : Finset ℤ) (c : ℤ → ℂ) :
    ∫ ω : ℤ → ℂ, ‖∑ n ∈ U, c n * ω n‖ ^ 2 ∂countableComplexGaussian q =
      ∑ n ∈ U, ‖c n‖ ^ 2 / q n := by
  have hpt : ∀ ω : ℤ → ℂ, ((‖∑ n ∈ U, c n * ω n‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ U, ∑ m ∈ U, (c n * star (c m)) * (ω n * star (ω m)) := by
    intro ω
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    simp only [map_sum, map_mul, Finset.sum_mul_sum, Complex.star_def]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  have hint : ∀ n ∈ U, ∀ m ∈ U, Integrable
      (fun ω : ℤ → ℂ => (c n * star (c m)) * (ω n * star (ω m))) (countableComplexGaussian q) :=
    fun n _ m _ => (integrable_cross q hq n m).const_mul _
  have hR : ∫ ω : ℤ → ℂ, ‖∑ n ∈ U, c n * ω n‖ ^ 2 ∂countableComplexGaussian q =
      ((∫ ω : ℤ → ℂ, ((‖∑ n ∈ U, c n * ω n‖ ^ 2 : ℝ) : ℂ) ∂countableComplexGaussian q).re) := by
    rw [integral_complex_ofReal]
    simp
  have hC : ∫ ω : ℤ → ℂ, ((‖∑ n ∈ U, c n * ω n‖ ^ 2 : ℝ) : ℂ) ∂countableComplexGaussian q =
      ∑ n ∈ U, ∑ m ∈ U, (c n * star (c m)) * (∫ ω : ℤ → ℂ, ω n * star (ω m) ∂countableComplexGaussian q) := by
    simp only [hpt]
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [integral_finset_sum]
      · refine Finset.sum_congr rfl fun m _ => ?_
        rw [integral_const_mul]
      · exact fun m hm => hint n ‹_› m hm
    · exact fun n hn => integrable_finset_sum _ fun m hm => hint n hn m hm
  have hdiag : ∀ n ∈ U, ∑ m ∈ U, (c n * star (c m)) * (∫ ω : ℤ → ℂ, ω n * star (ω m) ∂countableComplexGaussian q) =
      ((‖c n‖ ^ 2 / q n : ℝ) : ℂ) := by
    intro n hn
    rw [Finset.sum_eq_single n]
    · have hcc : c n * star (c n) = ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [diag_conj q hq n, hcc]
      push_cast
      ring
    · intro m _ hm
      rw [cross_conj_zero q hq (Ne.symm hm), mul_zero]
    · intro h
      exact absurd hn h
  rw [hR, hC, Finset.sum_congr rfl hdiag, ← Complex.ofReal_sum, Complex.ofReal_re]

end F016L3
end NlsGge.ThirdConsultation.F

namespace NlsGge.ThirdConsultation.F
namespace F016L4

open Filter Topology

theorem tail_small (f : ℤ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (hf : Summable f) (ε : ℝ) (hε : 0 < ε) :
    ∃ L0 : ℕ, ∀ t : Finset ℤ, (∀ n ∈ t, L0 < n.natAbs) → ∑ n ∈ t, f n < ε := by
  have hcs : CauchySeq (fun s : Finset ℤ => ∑ n ∈ s, f n) :=
    (summable_iff_cauchySeq_finset).1 hf
  have hv := (cauchySeq_finset_iff_sum_vanishing.1 hcs) (Metric.ball (0 : ℝ) ε)
    (Metric.ball_mem_nhds 0 hε)
  obtain ⟨s, hs⟩ := hv
  refine ⟨s.sup (fun n => n.natAbs), fun t ht => ?_⟩
  have hdisj : Disjoint t s := by
    rw [Finset.disjoint_left]
    intro n hnt hns
    have h1 : n.natAbs ≤ s.sup (fun n => n.natAbs) := Finset.le_sup (f := fun n => n.natAbs) hns
    have h2 := ht n hnt
    omega
  have hmem := hs t hdisj
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun n _ => hf0 n)] at hmem
  exact hmem



open NlsGge.Measure NlsGge.HierarchyRiccati.Core

theorem memLp_coord (q : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n) (n : ℤ) :
    MemLp (fun ω : ℤ → ℂ => ω n) 2 (countableComplexGaussian q) := by
  have hm : Measurable (fun ω : ℤ → ℂ => ω n) := by fun_prop
  rw [memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable]
  exact integrable_countableComplexGaussian_sqNorm q n

theorem memLp_sum (q : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n) (U : Finset ℤ) (c : ℤ → ℂ) :
    MemLp (fun ω : ℤ → ℂ => ∑ n ∈ U, c n * ω n) 2 (countableComplexGaussian q) := by
  exact memLp_finset_sum (p := 2) (μ := countableComplexGaussian q) U
    (f := fun n (ω : ℤ → ℂ) => c n * ω n) (fun n _ => (memLp_coord q hq n).const_mul (c n))

theorem l2norm_sq_sum (q : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n) (U : Finset ℤ) (c : ℤ → ℂ) :
    (eLpNorm (fun ω : ℤ → ℂ => ∑ n ∈ U, c n * ω n) 2 (countableComplexGaussian q)).toReal ^ 2 =
      ∑ n ∈ U, ‖c n‖ ^ 2 / q n := by
  have hmem := memLp_sum q hq U c
  have h := hmem.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num)
  rw [h, ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num
  exact F016L3.sum_sq_integral q hq U c

theorem trunc_mono {N L L' : ℕ} (h : L ≤ L') : truncFinset38 N L ⊆ truncFinset38 N L' := by
  intro n hn
  simp only [truncFinset38, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  refine ⟨⟨?_, ?_⟩, hn.2⟩
  · have : (L : ℤ) ≤ L' := by exact_mod_cast h
    linarith [hn.1.1]
  · have : (L : ℤ) ≤ L' := by exact_mod_cast h
    linarith [hn.1.2]

theorem trunc_sdiff_far {N L L' : ℕ} {n : ℤ} (hn : n ∈ truncFinset38 N L' \ truncFinset38 N L) :
    L < n.natAbs := by
  have h1 := Finset.mem_sdiff.1 hn
  have hN : (N : ℤ) < |n| := (Finset.mem_filter.1 h1.1).2
  by_contra hle
  push_neg at hle
  apply h1.2
  simp only [truncFinset38, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨?_, hN⟩
  have h2 : |n| ≤ (L : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hle
  exact abs_le.1 h2

theorem exists_limit (q : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n) (c : ℤ → ℂ)
    (hs : Summable (fun n : ℤ => ‖c n‖ ^ 2 / q n)) (N : ℕ) :
    ∃ Y : (ℤ → ℂ) → ℂ, MemLp Y 2 (countableComplexGaussian q) ∧
      Tendsto (fun L : ℕ => eLpNorm ((fun ω : ℤ → ℂ => ∑ n ∈ truncFinset38 N L, c n * ω n) - Y) 2
        (countableComplexGaussian q)) atTop (𝓝 0) := by
  set μ := countableComplexGaussian q with hμ
  set S : ℕ → (ℤ → ℂ) → ℂ := fun L ω => ∑ n ∈ truncFinset38 N L, c n * ω n with hS
  have hmem : ∀ L, MemLp (S L) 2 μ := fun L => memLp_sum q hq _ c
  set F : ℕ → Lp ℂ 2 μ := fun L => (hmem L).toLp (S L) with hF
  have hf0 : ∀ n, 0 ≤ ‖c n‖ ^ 2 / q n := fun n => by have := hq n; positivity
  have hdist : ∀ L L' : ℕ, L ≤ L' →
      dist (F L') (F L) ^ 2 = ∑ n ∈ truncFinset38 N L' \ truncFinset38 N L, ‖c n‖ ^ 2 / q n := by
    intro L L' hLL
    rw [dist_eq_norm, hF]
    simp only
    rw [← (hmem L').toLp_sub (hmem L), Lp.norm_toLp]
    have hdiff : (S L' - S L) = fun ω : ℤ → ℂ =>
        ∑ n ∈ truncFinset38 N L' \ truncFinset38 N L, c n * ω n := by
      funext ω
      have := Finset.sum_sdiff (f := fun n => c n * ω n) (trunc_mono (N := N) hLL)
      simp only [hS, Pi.sub_apply]
      linear_combination (-1 : ℂ) * this
    rw [hdiff]
    exact l2norm_sq_sum q hq _ c
  have hcauchy : CauchySeq F := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨L0, hL0⟩ := F016L4.tail_small (fun n => ‖c n‖ ^ 2 / q n) hf0 hs (ε ^ 2) (by positivity)
    refine ⟨L0, fun L' hL' => ?_⟩
    have h1 := hdist L0 L' hL'
    have h2 : ∑ n ∈ truncFinset38 N L' \ truncFinset38 N L0, ‖c n‖ ^ 2 / q n < ε ^ 2 :=
      hL0 _ (fun n hn => trunc_sdiff_far hn)
    rw [← h1] at h2
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h2
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨⇑G, Lp.memLp G, ?_⟩
  have hnorm : ∀ L, eLpNorm (S L - ⇑G) 2 μ = ENNReal.ofReal ‖F L - G‖ := by
    intro L
    have hae : (S L - ⇑G) =ᵐ[μ] ⇑(F L - G) := by
      filter_upwards [Lp.coeFn_sub (F L) G, (hmem L).coeFn_toLp] with ω h1 h2
      rw [h1, Pi.sub_apply, Pi.sub_apply, h2]
    rw [eLpNorm_congr_ae hae, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_lt_top _).ne]
  have hz : Tendsto (fun L => ‖F L - G‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hG)
  have key : Tendsto (fun L => ENNReal.ofReal ‖F L - G‖) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hz
  exact key.congr (fun L => (hnorm L).symm)

theorem cross_integral (q : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n) (U : Finset ℤ) (c d : ℤ → ℂ) :
    ∫ ω : ℤ → ℂ, (∑ n ∈ U, c n * ω n) * star (∑ n ∈ U, d n * ω n) ∂countableComplexGaussian q =
      ∑ n ∈ U, c n * star (d n) / (q n : ℂ) := by
  have hpt : ∀ ω : ℤ → ℂ, (∑ n ∈ U, c n * ω n) * star (∑ n ∈ U, d n * ω n) =
      ∑ n ∈ U, ∑ m ∈ U, (c n * star (d m)) * (ω n * star (ω m)) := by
    intro ω
    simp only [star_sum, star_mul', Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  have hint : ∀ n ∈ U, ∀ m ∈ U, Integrable
      (fun ω : ℤ → ℂ => (c n * star (d m)) * (ω n * star (ω m))) (countableComplexGaussian q) :=
    fun n _ m _ => (F016L3.integrable_cross q hq n m).const_mul _
  simp only [hpt]
  rw [integral_finset_sum]
  · have hdiag : ∀ n ∈ U, ∫ ω : ℤ → ℂ, ∑ m ∈ U, (c n * star (d m)) * (ω n * star (ω m))
        ∂countableComplexGaussian q = c n * star (d n) / (q n : ℂ) := by
      intro n hn
      rw [integral_finset_sum]
      · rw [Finset.sum_eq_single n]
        · rw [integral_const_mul, F016L2.diag_conj q hq n]
          ring
        · intro m _ hm
          rw [integral_const_mul, F016L2.cross_conj_zero q hq (Ne.symm hm), mul_zero]
        · intro h
          exact absurd hn h
      · exact fun m hm => hint n hn m hm
    exact Finset.sum_congr rfl hdiag
  · exact fun n hn => integrable_finset_sum _ fun m hm => hint n hn m hm

theorem prod_integral_zero (q : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n) (U : Finset ℤ) (c d : ℤ → ℂ) :
    ∫ ω : ℤ → ℂ, (∑ n ∈ U, c n * ω n) * (∑ n ∈ U, d n * ω n) ∂countableComplexGaussian q = 0 := by
  have hint : ∀ n m : ℤ, Integrable (fun ω : ℤ → ℂ => ω n * ω m) (countableComplexGaussian q) := by
    intro n m
    have hg : Integrable (fun ω : ℤ → ℂ => (1/2 : ℝ) * (‖ω n‖ ^ 2 + ‖ω m‖ ^ 2))
        (countableComplexGaussian q) :=
      ((integrable_countableComplexGaussian_sqNorm q n).add
        (integrable_countableComplexGaussian_sqNorm q m)).const_mul (1/2)
    refine hg.mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact ((by fun_prop : Measurable (fun ω : ℤ → ℂ => ω n)).mul
        (by fun_prop : Measurable (fun ω : ℤ → ℂ => ω m))).aestronglyMeasurable
    · rw [norm_mul]
      nlinarith [sq_nonneg (‖ω n‖ - ‖ω m‖), norm_nonneg (ω n), norm_nonneg (ω m)]
  have hpt : ∀ ω : ℤ → ℂ, (∑ n ∈ U, c n * ω n) * (∑ n ∈ U, d n * ω n) =
      ∑ n ∈ U, ∑ m ∈ U, (c n * d m) * (ω n * ω m) := by
    intro ω
    simp only [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  simp only [hpt]
  rw [integral_finset_sum]
  · refine Finset.sum_eq_zero fun n hn => ?_
    rw [integral_finset_sum]
    · refine Finset.sum_eq_zero fun m hm => ?_
      rw [integral_const_mul]
      by_cases hnm : n = m
      · subst hnm
        have hsq : ∫ ω : ℤ → ℂ, ω n * ω n ∂countableComplexGaussian q =
            ∫ ω : ℤ → ℂ, ω n ^ 2 ∂countableComplexGaussian q := by simp only [sq]
        rw [hsq, F016L2.diag_sq_zero q hq n, mul_zero]
      · rw [F016L2.cross_zero q hq hnm, mul_zero]
    · exact fun m hm => (hint n m).const_mul _
  · exact fun n hn => integrable_finset_sum _ fun m hm => (hint n m).const_mul _

theorem tendsto_toLp {α : Type*} [MeasurableSpace α] {μ : Measure α} (g' : ℕ → α → ℂ) (g : α → ℂ)
    (hg' : ∀ L, MemLp (g' L) 2 μ) (hg : MemLp g 2 μ)
    (h : Tendsto (fun L => eLpNorm (g' L - g) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun L => (hg' L).toLp (g' L)) atTop (𝓝 (hg.toLp g)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hn : ∀ L, ‖(hg' L).toLp (g' L) - hg.toLp g‖ = (eLpNorm (g' L - g) 2 μ).toReal := by
    intro L
    rw [← (hg' L).toLp_sub hg, Lp.norm_toLp]
  simp only [hn]
  have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [Function.comp_def] using ht

theorem tendsto_integral_mul_star {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f' h' : ℕ → α → ℂ) (f h : α → ℂ)
    (hf' : ∀ L, MemLp (f' L) 2 μ) (hh' : ∀ L, MemLp (h' L) 2 μ)
    (hf : MemLp f 2 μ) (hh : MemLp h 2 μ)
    (hfl : Tendsto (fun L => eLpNorm (f' L - f) 2 μ) atTop (𝓝 0))
    (hhl : Tendsto (fun L => eLpNorm (h' L - h) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun L => ∫ a, f' L a * star (h' L a) ∂μ) atTop (𝓝 (∫ a, f a * star (h a) ∂μ)) := by
  have hF := tendsto_toLp f' f hf' hf hfl
  have hH := tendsto_toLp h' h hh' hh hhl
  have hI := Filter.Tendsto.inner (𝕜 := ℂ) hH hF
  have hid : ∀ (g₁ g₂ : α → ℂ) (h₁ : MemLp g₁ 2 μ) (h₂ : MemLp g₂ 2 μ),
      inner ℂ (h₁.toLp g₁) (h₂.toLp g₂) = ∫ a, g₂ a * star (g₁ a) ∂μ := by
    intro g₁ g₂ h₁ h₂
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [h₁.coeFn_toLp, h₂.coeFn_toLp] with a ha hb
    rw [ha, hb, RCLike.inner_apply', mul_comm]
    rfl
  simpa only [hid] using hI

end F016L4
end NlsGge.ThirdConsultation.F

noncomputable section
open MeasureTheory Filter Topology ENNReal
open NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.F

def highJetPartial (N L a : ℕ) (x : ℝ) (z : ℤ → ℂ) : ℂ :=
  ∑ n ∈ truncFinset38 N L,
    (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ a * z n *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ))

def covarianceTerm (m : ℕ) (β : ℕ → ℝ) (N a b : ℕ) (n : ℤ) : ℂ :=
  if N < n.natAbs then
    (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ a *
      star ((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ b) /
        (finiteHierarchyRate38 m β n : ℂ)
  else 0

def tailCovariance (m : ℕ) (β : ℕ → ℝ) (N a b : ℕ) : ℂ :=
  ∑' n : ℤ, covarianceTerm m β N a b n

end NlsGge.ThirdConsultation.F

namespace NlsGge.ThirdConsultation.F
namespace F016L5

open Filter Topology NlsGge.Measure NlsGge.HierarchyRiccati.Core

/-- The coefficient of mode `n` in the partial sum: `(2π i n)^a e^{2π i n x}`. -/
def cc (a : ℕ) (x : ℝ) (n : ℤ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ a *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ))

theorem norm_exp_phase (n : ℤ) (x : ℝ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ))‖ = 1 := by
  have : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ)) =
      ((2 * Real.pi * n * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this]; exact Complex.norm_exp_ofReal_mul_I _

theorem norm_A (a : ℕ) (n : ℤ) :
    ‖(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ a‖ = (2 * Real.pi * |(n : ℝ)|) ^ a := by
  rw [norm_pow]
  congr 1
  rw [norm_mul, norm_mul, norm_mul]
  simp [abs_of_pos Real.pi_pos]

theorem norm_cc (a : ℕ) (x : ℝ) (n : ℤ) : ‖cc a x n‖ = (2 * Real.pi * |(n : ℝ)|) ^ a := by
  unfold cc
  rw [norm_mul, norm_exp_phase, mul_one, norm_A]

theorem exp_mul_star (n : ℤ) (x : ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ)) *
      star (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ))) = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_exp_phase]
  simp

theorem cc_mul_star (a b : ℕ) (x : ℝ) (n : ℤ) :
    cc a x n * star (cc b x n) =
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ a *
        star ((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ b) := by
  unfold cc
  have h := exp_mul_star n x
  rw [star_mul']
  calc _ = ((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ a *
        star ((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ^ b)) *
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ)) *
          star (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ)))) := by ring
    _ = _ := by rw [h, mul_one]

theorem highJet_eq (N L a : ℕ) (x : ℝ) :
    highJetPartial N L a x = fun ω : ℤ → ℂ => ∑ n ∈ truncFinset38 N L, cc a x n * ω n := by
  funext ω
  unfold highJetPartial cc
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

theorem rate_pos' (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) (n : ℤ) :
    0 < finiteHierarchyRate38 m β n := by
  obtain ⟨c, hc, h⟩ := finiteHierarchyRate38_exists_c m β (fun j hj => (hβ j hj).le) (by omega)
    (hβ 0 (Nat.zero_le _)) (hβ m le_rfl)
  have := h n
  have h2 : 0 < c * (1 + (2 * Real.pi * |(n : ℝ)|) ^ (2 * m)) := by positivity
  linarith

theorem abs_lt_iff_natAbs (N : ℕ) (n : ℤ) : (N : ℤ) < |n| ↔ N < n.natAbs := by
  rw [Int.abs_eq_natAbs]; exact_mod_cast Iff.rfl

theorem norm_covTerm (m : ℕ) (β : ℕ → ℝ) (hq : ∀ n : ℤ, 0 < finiteHierarchyRate38 m β n)
    (N a b : ℕ) (n : ℤ) :
    ‖covarianceTerm m β N a b n‖ =
      if (N : ℤ) < |n| then (2 * Real.pi * |(n : ℝ)|) ^ (a + b) / finiteHierarchyRate38 m β n else 0 := by
  unfold covarianceTerm
  by_cases h : N < n.natAbs
  · rw [if_pos h, if_pos ((abs_lt_iff_natAbs N n).2 h), norm_div, norm_mul, norm_star, norm_A, norm_A,
      Complex.norm_real, Real.norm_of_nonneg (hq n).le, pow_add]
  · rw [if_neg h, if_neg (fun h' => h ((abs_lt_iff_natAbs N n).1 h')), norm_zero]

theorem summable_cov (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) (N a b : ℕ)
    (hN : 1 ≤ N) (ha : a ≤ m - 1) (hb : b ≤ m - 1) :
    Summable (fun n : ℤ => ‖covarianceTerm m β N a b n‖) ∧
    ‖tailCovariance m β N a b‖ ≤
      (2 / min (β 0) (β m)) * (N : ℝ) ^ ((a : ℤ) + b - 2 * m + 1) := by
  obtain ⟨h1, h2⟩ := covariance_tail_finiteHierarchy38 m a b N (by omega) ha hb β
    (fun j hj => (hβ j hj).le) (hβ 0 (Nat.zero_le _)) (hβ m le_rfl) hN
  have hq := rate_pos' m hm β hβ
  have e : (fun n : ℤ => ‖covarianceTerm m β N a b n‖) = fun n : ℤ =>
      (if (N : ℤ) < |n| then
        (2 * Real.pi * |(n : ℝ)|) ^ (a + b) / finiteHierarchyRate38 m β n else 0) :=
    funext fun n => norm_covTerm m β hq N a b n
  rw [e]
  refine ⟨h1, ?_⟩
  unfold tailCovariance
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · rw [e]; exact h1
  · rw [e]; exact h2

end F016L5
end NlsGge.ThirdConsultation.F

end

namespace NlsGge.ThirdConsultation.F
namespace F016L5

open Filter Topology NlsGge.Measure NlsGge.HierarchyRiccati.Core

theorem tendsto_Icc_atTop : Tendsto (fun M : ℕ => Finset.Icc (-(M : ℤ)) M) atTop atTop := by
  refine Filter.tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun n => ?_)
  · exact Finset.Icc_subset_Icc (by omega) (by exact_mod_cast hab)
  · refine ⟨n.natAbs, ?_⟩
    simp only [Finset.mem_Icc]
    omega

theorem partial_cov (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) (N a b L : ℕ) (x : ℝ) :
    ∫ ω : ℤ → ℂ, highJetPartial N L a x ω * star (highJetPartial N L b x ω)
        ∂gammaM38 m β =
      ∑ n ∈ truncFinset38 N L, covarianceTerm m β N a b n := by
  have hq := rate_pos' m hm β hβ
  have h := F016L4.cross_integral (finiteHierarchyRate38 m β) hq (truncFinset38 N L) (cc a x) (cc b x)
  have e1 : (fun ω : ℤ → ℂ => highJetPartial N L a x ω * star (highJetPartial N L b x ω)) =
      fun ω : ℤ → ℂ => (∑ n ∈ truncFinset38 N L, cc a x n * ω n) *
        star (∑ n ∈ truncFinset38 N L, cc b x n * ω n) := by
    funext ω
    rw [highJet_eq, highJet_eq]
  rw [e1]
  show ∫ ω : ℤ → ℂ, (∑ n ∈ truncFinset38 N L, cc a x n * ω n) *
        star (∑ n ∈ truncFinset38 N L, cc b x n * ω n) ∂countableComplexGaussian (finiteHierarchyRate38 m β) = _
  rw [h]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hN : N < n.natAbs := (abs_lt_iff_natAbs N n).1 (Finset.mem_filter.1 hn).2
  rw [cc_mul_star, covarianceTerm, if_pos hN]

theorem tendsto_partial_cov (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) (N a b : ℕ)
    (hN : 1 ≤ N) (ha : a ≤ m - 1) (hb : b ≤ m - 1) :
    Tendsto (fun L : ℕ => ∑ n ∈ truncFinset38 N L, covarianceTerm m β N a b n) atTop
      (𝓝 (tailCovariance m β N a b)) := by
  have hs := (summable_cov m hm β hβ N a b hN ha hb).1.of_norm
  have ht := hs.hasSum.comp tendsto_Icc_atTop
  have e : ∀ L : ℕ, ∑ n ∈ truncFinset38 N L, covarianceTerm m β N a b n =
      ∑ n ∈ Finset.Icc (-(L : ℤ)) L, covarianceTerm m β N a b n := by
    intro L
    unfold truncFinset38
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold covarianceTerm
    by_cases h : (N : ℤ) < |n|
    · rw [if_pos h, if_pos ((abs_lt_iff_natAbs N n).1 h)]
    · rw [if_neg h, if_neg (fun h' => h ((abs_lt_iff_natAbs N n).2 h'))]
  simp only [e]
  exact ht

theorem summable_sq_cc (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) (N a : ℕ)
    (hN : 1 ≤ N) (ha : a ≤ m - 1) (x : ℝ) :
    Summable (fun n : ℤ => ‖cc a x n‖ ^ 2 / finiteHierarchyRate38 m β n) := by
  obtain ⟨h1, _⟩ := covariance_tail_finiteHierarchy38 m a a N (by omega) ha ha β
    (fun j hj => (hβ j hj).le) (hβ 0 (Nat.zero_le _)) (hβ m le_rfl) hN
  have hfin : Summable (fun n : ℤ => if (N : ℤ) < |n| then (0 : ℝ) else
      ‖cc a x n‖ ^ 2 / finiteHierarchyRate38 m β n) := by
    refine summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ)) N) (fun n hn => ?_)
    have : (N : ℤ) < |n| := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hn
      rcases hn with h | h
      · rw [lt_abs]; right; linarith
      · rw [lt_abs]; left; exact h
    simp [this]
  refine (h1.add hfin).congr (fun n => ?_)
  by_cases h : (N : ℤ) < |n|
  · simp only [if_pos h, add_zero, norm_cc, ← pow_mul]
    rw [show a * 2 = a + a by ring]
  · simp only [if_neg h, zero_add]

end F016L5
end NlsGge.ThirdConsultation.F

namespace NlsGge.ThirdConsultation.F

open Filter Topology NlsGge.Measure NlsGge.HierarchyRiccati.Core

theorem f016 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) :
    ∀ N : ℕ, 1 ≤ N →
      (∀ a b : ℕ, a ≤ m - 1 → b ≤ m - 1 →
        Summable (fun n : ℤ => ‖covarianceTerm m β N a b n‖) ∧
        HasSum (covarianceTerm m β N a b) (tailCovariance m β N a b)) ∧
      ∃ Y : ℕ → ℝ → (ℤ → ℂ) → ℂ,
        (∀ a : ℕ, a ≤ m - 1 → ∀ x : ℝ,
          MemLp (Y a x) 2 (gammaM38 m β) ∧
          Tendsto (fun L => eLpNorm (highJetPartial N L a x - Y a x)
            2 (gammaM38 m β)) atTop (nhds 0)) ∧
        ∀ a b : ℕ, a ≤ m - 1 → b ≤ m - 1 → ∀ x : ℝ,
          Integrable (fun z => Y a x z * star (Y b x z)) (gammaM38 m β) ∧
          Integrable (fun z => Y a x z * Y b x z) (gammaM38 m β) ∧
          (∫ z, Y a x z * star (Y b x z) ∂gammaM38 m β) =
            tailCovariance m β N a b ∧
          (∫ z, Y a x z * Y b x z ∂gammaM38 m β) = 0 ∧
          ‖∫ z, Y a x z * star (Y b x z) ∂gammaM38 m β‖ ≤
            (2 / min (β 0) (β m)) *
              (N : ℝ) ^ ((a : ℤ) + (b : ℤ) - 2 * (m : ℤ) + 1) := by
  intro N hN
  have hq := F016L5.rate_pos' m hm β hβ
  have hμ : gammaM38 m β = countableComplexGaussian (finiteHierarchyRate38 m β) := rfl
  refine ⟨fun a b ha hb => ⟨(F016L5.summable_cov m hm β hβ N a b hN ha hb).1, ?_⟩, ?_⟩
  · unfold tailCovariance
    exact (Summable.of_norm (F016L5.summable_cov m hm β hβ N a b hN ha hb).1).hasSum
  have hex : ∀ a : ℕ, a ≤ m - 1 → ∀ x : ℝ, ∃ Y : (ℤ → ℂ) → ℂ, MemLp Y 2 (gammaM38 m β) ∧
      Tendsto (fun L : ℕ => eLpNorm (highJetPartial N L a x - Y) 2 (gammaM38 m β)) atTop (𝓝 0) := by
    intro a ha x
    obtain ⟨Y, hY1, hY2⟩ := F016L4.exists_limit (finiteHierarchyRate38 m β) hq (F016L5.cc a x)
      (F016L5.summable_sq_cc m hm β hβ N a hN ha x) N
    refine ⟨Y, hY1, ?_⟩
    have e : ∀ L : ℕ, highJetPartial N L a x =
        fun ω : ℤ → ℂ => ∑ n ∈ truncFinset38 N L, F016L5.cc a x n * ω n :=
      fun L => F016L5.highJet_eq N L a x
    simp only [e]
    exact hY2
  choose! Y hY using hex
  refine ⟨Y, fun a ha x => hY a ha x, ?_⟩
  intro a b ha hb x
  have hSm : ∀ (c : ℕ) (L : ℕ), MemLp (highJetPartial N L c x) 2 (gammaM38 m β) := by
    intro c L
    rw [F016L5.highJet_eq]
    exact F016L4.memLp_sum _ hq _ _
  have hYa := hY a ha x
  have hYb := hY b hb x
  have hint1 : Integrable (fun z => Y a x z * star (Y b x z)) (gammaM38 m β) :=
    MemLp.integrable_mul (p := 2) (q := 2) hYa.1 hYb.1.star
  have hint2 : Integrable (fun z => Y a x z * Y b x z) (gammaM38 m β) :=
    MemLp.integrable_mul (p := 2) (q := 2) hYa.1 hYb.1
  have hstar : Tendsto (fun L => eLpNorm ((fun ω => star (highJetPartial N L b x ω)) -
      (fun ω => star (Y b x ω))) 2 (gammaM38 m β)) atTop (𝓝 0) := by
    have e : ∀ L, ((fun ω => star (highJetPartial N L b x ω)) - (fun ω => star (Y b x ω))) =
        star (highJetPartial N L b x - Y b x) := by
      intro L; funext ω; simp [star_sub]
    simp only [e, eLpNorm_star]
    exact hYb.2
  -- covariance identity
  have hc : (∫ z, Y a x z * star (Y b x z) ∂gammaM38 m β) = tailCovariance m β N a b := by
    have h1 := F016L4.tendsto_integral_mul_star (fun L => highJetPartial N L a x)
      (fun L => highJetPartial N L b x) (Y a x) (Y b x) (hSm a) (hSm b) hYa.1 hYb.1 hYa.2 hYb.2
    have h2 : Tendsto (fun L : ℕ => ∫ z, highJetPartial N L a x z * star (highJetPartial N L b x z)
        ∂gammaM38 m β) atTop (𝓝 (tailCovariance m β N a b)) := by
      simp only [F016L5.partial_cov m hm β hβ N a b _ x]
      exact F016L5.tendsto_partial_cov m hm β hβ N a b hN ha hb
    exact tendsto_nhds_unique h1 h2
  have hp : (∫ z, Y a x z * Y b x z ∂gammaM38 m β) = 0 := by
    have h1 := F016L4.tendsto_integral_mul_star (fun L => highJetPartial N L a x)
      (fun L ω => star (highJetPartial N L b x ω)) (Y a x) (fun ω => star (Y b x ω))
      (hSm a) (fun L => (hSm b L).star) hYa.1 hYb.1.star hYa.2 hstar
    simp only [star_star] at h1
    have h0 : ∀ L : ℕ, ∫ z, highJetPartial N L a x z * highJetPartial N L b x z ∂gammaM38 m β = 0 := by
      intro L
      have e : (fun z => highJetPartial N L a x z * highJetPartial N L b x z) =
          fun ω : ℤ → ℂ => (∑ n ∈ truncFinset38 N L, F016L5.cc a x n * ω n) *
            (∑ n ∈ truncFinset38 N L, F016L5.cc b x n * ω n) := by
        funext ω; rw [F016L5.highJet_eq, F016L5.highJet_eq]
      rw [e]
      exact F016L4.prod_integral_zero _ hq _ _ _
    simp only [h0] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  refine ⟨hint1, hint2, hc, hp, ?_⟩
  rw [hc]
  exact (F016L5.summable_cov m hm β hβ N a b hN ha hb).2


end NlsGge.ThirdConsultation.F

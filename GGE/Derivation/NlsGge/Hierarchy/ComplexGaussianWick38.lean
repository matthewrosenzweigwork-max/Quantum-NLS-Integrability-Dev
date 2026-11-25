import NlsGge.Measure.ComplexGaussian
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Analysis.Complex.Isometry

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Measure

/-- Planar radial moment `∫ ‖z‖^(2k) = k!/a^k` for the Lebesgue integral against the kernel. -/
lemma integral_kernel_norm_pow (a : ℝ) (ha : 0 < a) (k : ℕ) :
    (∫ z : ℂ, (a / Real.pi) * Real.exp (-a * ‖z‖ ^ 2) * ‖z‖ ^ (2 * k)) =
      (k.factorial : ℝ) / a ^ k := by
  have h := integral_fun_norm_addHaar (volume : Measure ℂ)
    (fun r : ℝ => (a / Real.pi) * Real.exp (-a * r ^ 2) * r ^ (2 * k))
  rw [h]
  have hr : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  rw [hr]
  have hfin : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  rw [hfin]
  have hG := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2 * (k:ℝ) + 1) (b := a)
    (by norm_num) (by have : (0:ℝ) ≤ k := k.cast_nonneg; linarith) ha
  have hexp : (-(2 * (k:ℝ) + 1 + 1) / 2) = -((k:ℝ) + 1) := by ring
  have hexp2 : ((2 * (k:ℝ) + 1 + 1) / 2) = (k:ℝ) + 1 := by ring
  have hpow : a ^ (-((k:ℝ) + 1)) = (a ^ (k + 1))⁻¹ := by
    rw [Real.rpow_neg ha.le, ← Real.rpow_natCast]; push_cast; rfl
  rw [hexp, hexp2, Real.Gamma_nat_eq_factorial, hpow] at hG
  have hI : ∫ y in Set.Ioi (0:ℝ), y ^ (2 - 1) • ((a / Real.pi) * Real.exp (-a * y ^ 2) * y ^ (2 * k))
      = (a / Real.pi) * (((a ^ (k + 1))⁻¹) * (1 / 2) * (k.factorial : ℝ)) := by
    rw [← hG, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    simp only [smul_eq_mul]
    have e1 : y ^ (2 * (k:ℝ) + 1) = y ^ (2 * k + 1) := by
      rw [show (2 * (k:ℝ) + 1) = ((2 * k + 1 : ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]
    have e2 : y ^ (2:ℝ) = y ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [e1, e2]
    ring
  rw [hI]
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- Planar density of `complexGaussian a`. -/
def cgDensity (a : ℝ) (z : ℂ) : ℝ := (a / Real.pi) * Real.exp (-a * ‖z‖ ^ 2)

lemma cgDensity_nonneg (a : ℝ) (ha : 0 < a) (z : ℂ) : 0 ≤ cgDensity a z := by
  unfold cgDensity; positivity

lemma measurable_cgDensity (a : ℝ) : Measurable (cgDensity a) := by
  unfold cgDensity; fun_prop

lemma integral_complexGaussian_eq (a : ℝ) (ha : 0 < a) (F : ℂ → ℂ) :
    ∫ z, F z ∂complexGaussian a = ∫ z : ℂ, ((cgDensity a z : ℝ) : ℂ) * F z := by
  rw [complexGaussian_density a ha,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (by simp)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  have h0 := cgDensity_nonneg a ha z
  unfold cgDensity at h0 ⊢
  beta_reduce
  rw [ENNReal.toReal_ofReal h0, Complex.real_smul]

lemma integral_complexGaussian_rotate (a : ℝ) (t : ℝ) (F : ℂ → ℂ) :
    ∫ z : ℂ, ((cgDensity a z : ℝ) : ℂ) * F (Complex.exp (t * Complex.I) * z) =
      ∫ z : ℂ, ((cgDensity a z : ℝ) : ℂ) * F z := by
  have hmp := (rotation (Circle.exp t)).measurePreserving
  have hme : MeasurableEmbedding (rotation (Circle.exp t)) :=
    (rotation (Circle.exp t)).toHomeomorph.measurableEmbedding
  have := hme.integral_map (μ := (volume : Measure ℂ)) (fun z => ((cgDensity a z : ℝ) : ℂ) * F z)
  rw [hmp.map_eq] at this
  rw [this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [rotation_apply, Circle.coe_exp, cgDensity, Complex.norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]

lemma star_pow_mul_pow_self (z : ℂ) (k : ℕ) :
    z ^ k * star z ^ k = (((‖z‖ ^ (2 * k) : ℝ)) : ℂ) := by
  rw [← mul_pow, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rw [pow_mul]

lemma rotate_monomial (k l : ℕ) (hkl : k ≠ l) :
    ∃ t : ℝ, ∀ z : ℂ, (Complex.exp (t * Complex.I) * z) ^ k * star (Complex.exp (t * Complex.I) * z) ^ l
      = (-1 : ℂ) * (z ^ k * star z ^ l) := by
  have hne : ((k : ℝ) - l) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hkl)
  refine ⟨Real.pi / ((k : ℝ) - l), fun z => ?_⟩
  have hu : star (Complex.exp (((Real.pi / ((k : ℝ) - l) : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (-(((Real.pi / ((k : ℝ) - l) : ℝ) : ℂ) * Complex.I)) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    simp [Complex.conj_ofReal]
  have hm : Complex.exp (((Real.pi / ((k : ℝ) - l) : ℝ) : ℂ) * Complex.I) ^ k *
      Complex.exp (-(((Real.pi / ((k : ℝ) - l) : ℝ) : ℂ) * Complex.I)) ^ l = -1 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    have : (k : ℂ) * (((Real.pi / ((k : ℝ) - l) : ℝ) : ℂ) * Complex.I) +
        (l : ℂ) * -(((Real.pi / ((k : ℝ) - l) : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
      have hne' : ((k : ℂ) - l) ≠ 0 := by exact_mod_cast hne
      push_cast
      field_simp
      ring
    rw [this, Complex.exp_pi_mul_I]
  rw [star_mul, mul_pow, mul_pow, hu]
  calc _ = (Complex.exp (((Real.pi / ((k : ℝ) - l) : ℝ) : ℂ) * Complex.I) ^ k *
      Complex.exp (-(((Real.pi / ((k : ℝ) - l) : ℝ) : ℂ) * Complex.I)) ^ l) * (z ^ k * star z ^ l) := by
        ring
    _ = _ := by rw [hm]

lemma integral_complexGaussian_monomial (a : ℝ) (ha : 0 < a) (k l : ℕ) :
    ∫ z, z ^ k * star z ^ l ∂complexGaussian a =
      if k = l then (((k.factorial : ℝ) / a ^ k : ℝ) : ℂ) else 0 := by
  rw [integral_complexGaussian_eq a ha]
  by_cases hkl : k = l
  · subst hkl
    simp only [ite_true]
    simp_rw [star_pow_mul_pow_self, ← Complex.ofReal_mul]
    rw [integral_complex_ofReal, ← integral_kernel_norm_pow a ha k]
    rfl
  · simp only [hkl, ite_false]
    obtain ⟨t, ht⟩ := rotate_monomial k l hkl
    have h1 := integral_complexGaussian_rotate a t (fun z => z ^ k * star z ^ l)
    simp only [ht] at h1
    have h2 : (∫ z : ℂ, ((cgDensity a z : ℝ) : ℂ) * ((-1 : ℂ) * (z ^ k * star z ^ l))) =
        -∫ z : ℂ, ((cgDensity a z : ℝ) : ℂ) * (z ^ k * star z ^ l) := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only; ring
    rw [h2] at h1
    have : (∫ z : ℂ, ((cgDensity a z : ℝ) : ℂ) * (z ^ k * star z ^ l)) = 0 := by
      linear_combination (-1/2 : ℂ) * h1
    exact this

lemma add_pow_le_two_pow_mul (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (m : ℕ) :
    (u + v) ^ m ≤ 2 ^ m * (u ^ m + v ^ m) := by
  rcases le_total u v with h | h
  · calc (u + v) ^ m ≤ (2 * v) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
      _ = 2 ^ m * v ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (u ^ m + v ^ m) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : 0 ≤ u ^ m := by positivity
        linarith
  · calc (u + v) ^ m ≤ (2 * u) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
      _ = 2 ^ m * u ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (u ^ m + v ^ m) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : 0 ≤ v ^ m := by positivity
        linarith

lemma integrable_complexGaussian_norm_pow (a : ℝ) (m : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ m) (complexGaussian a) := by
  unfold complexGaussian
  rw [Complex.measurableEquivRealProd.symm.measurableEmbedding.integrable_map_iff]
  have hi : Integrable (fun x : ℝ => ‖x‖ ^ m) (gaussianReal 0 (componentVariance a)) := by
    have := (memLp_id_gaussianReal (μ := 0) (v := componentVariance a) m).integrable_norm_pow'
    simpa using this
  have hb := ((hi.comp_fst (gaussianReal 0 (componentVariance a))).add
    (hi.comp_snd (gaussianReal 0 (componentVariance a)))).const_mul (2 ^ m)
  refine hb.mono' (by fun_prop) (Filter.Eventually.of_forall fun p => ?_)
  simp only [Function.comp_apply, Real.norm_eq_abs, norm_pow, abs_norm]
  have h1 : ‖Complex.measurableEquivRealProd.symm p‖ ≤ |p.1| + |p.2| := by
    simpa using Complex.norm_le_abs_re_add_abs_im (Complex.measurableEquivRealProd.symm p)
  calc ‖Complex.measurableEquivRealProd.symm p‖ ^ m ≤ (|p.1| + |p.2|) ^ m :=
        pow_le_pow_left₀ (norm_nonneg _) h1 m
    _ ≤ _ := add_pow_le_two_pow_mul _ _ (abs_nonneg _) (abs_nonneg _) m

lemma integrable_complexGaussian_monomial (a : ℝ) (k l : ℕ) :
    Integrable (fun z : ℂ => z ^ k * star z ^ l) (complexGaussian a) := by
  refine (integrable_complexGaussian_norm_pow a (k + l)).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun z => ?_)
  simp [pow_add]

section Pi

variable {K : ℕ}

/-- The product law of independent complex Gaussians. -/
abbrev cgPi (a : Fin K → ℝ) : Measure (Fin K → ℂ) :=
  Measure.pi (fun n => complexGaussian (a n))

theorem integrable_cgPi_monomial (a : Fin K → ℝ) (k l : Fin K → ℕ) :
    Integrable (fun g : Fin K → ℂ => ∏ n, (g n ^ k n * star (g n) ^ l n)) (cgPi a) :=
  Integrable.fintype_prod (fun n => integrable_complexGaussian_monomial (a n) (k n) (l n))

theorem integral_cgPi_monomial (a : Fin K → ℝ) (ha : ∀ n, 0 < a n) (k l : Fin K → ℕ) :
    ∫ g : Fin K → ℂ, ∏ n, (g n ^ k n * star (g n) ^ l n) ∂cgPi a =
      ∏ n, (if k n = l n then ((((k n).factorial : ℝ) / a n ^ k n : ℝ) : ℂ) else (0 : ℂ)) := by
  rw [integral_fintype_prod_eq_prod (fun n (z : ℂ) => z ^ k n * star z ^ l n)]
  exact Finset.prod_congr rfl fun n _ => integral_complexGaussian_monomial (a n) (ha n) (k n) (l n)

/-- Fibre counts. -/
def cnt {p : ℕ} (f : Fin p → Fin K) (n : Fin K) : ℕ := (Finset.univ.filter fun i => f i = n).card

lemma prod_comp_eq_prod_pow {p : ℕ} (f : Fin p → Fin K) (φ : Fin K → ℂ) :
    ∏ i, φ (f i) = ∏ n, φ n ^ cnt f n := by
  rw [Finset.prod_comp]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro n _ hn
  have : cnt f n = 0 := by
    unfold cnt
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hi
    exact hn (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
  change φ n ^ cnt f n = 1
  rw [this, pow_zero]

lemma card_subtype_eq_cnt {p : ℕ} (f : Fin p → Fin K) (n : Fin K) :
    Fintype.card {a // f a = n} = cnt f n := by
  rw [Fintype.card_subtype]; rfl

lemma exists_perm_comp_eq {p : ℕ} (f h : Fin p → Fin K) (H : ∀ n, cnt f n = cnt h n) :
    ∃ σ : Equiv.Perm (Fin p), f ∘ σ = h := by
  have e : ∀ n, {a // h a = n} ≃ {a // f a = n} := fun n =>
    Fintype.equivOfCardEq (by rw [card_subtype_eq_cnt, card_subtype_eq_cnt, H])
  refine ⟨(Equiv.sigmaFiberEquiv h).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv f)), ?_⟩
  funext x
  simp only [Function.comp_apply, Equiv.trans_apply]
  have h1 := (e (h x) ⟨x, rfl⟩).2
  simpa [Equiv.sigmaFiberEquiv] using h1

lemma cnt_eq_of_comp_eq {p : ℕ} (f h : Fin p → Fin K) (σ : Equiv.Perm (Fin p))
    (hσ : f ∘ σ = h) (n : Fin K) : cnt f n = cnt h n := by
  rw [← card_subtype_eq_cnt, ← card_subtype_eq_cnt]
  refine Fintype.card_congr (Equiv.subtypeEquiv σ.symm ?_)
  intro a
  subst hσ
  simp

lemma card_perm_comp_eq {p : ℕ} (f h : Fin p → Fin K) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin p) => f ∘ σ = h).card =
      if (∀ n, cnt f n = cnt h n) then ∏ n, (cnt f n).factorial else 0 := by
  classical
  by_cases H : ∀ n, cnt f n = cnt h n
  · rw [if_pos H]
    obtain ⟨σ0, hσ0⟩ := exists_perm_comp_eq f h H
    have hst := DomMulAct.stabilizer_card f
    simp only [card_subtype_eq_cnt] at hst
    rw [← hst, Fintype.card_subtype]
    refine Finset.card_bij (fun σ _ => σ * σ0⁻¹) ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      rw [← hσ0] at hσ
      funext x
      have := congrFun hσ (σ0⁻¹ x)
      simpa using this
    · intro σ _ τ _ h
      simpa using h
    · intro τ hτ
      refine ⟨τ * σ0, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      rw [← hσ0]
      funext x
      have := congrFun hτ (σ0 x)
      simpa using this
  · rw [if_neg H, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro σ _ hσ
    exact H (cnt_eq_of_comp_eq f h σ hσ)

lemma integrand_expand {p q : ℕ} (c : Fin p → Fin K → ℂ) (e : Fin q → Fin K → ℂ) (g : Fin K → ℂ) :
    (∏ i, ∑ n, c i n * g n) * ∏ j, star (∑ n, e j n * g n) =
      ∑ f : Fin p → Fin K, ∑ h : Fin q → Fin K,
        ((∏ i, c i (f i)) * ∏ j, star (e j (h j))) *
          ∏ n, (g n ^ cnt f n * star (g n) ^ cnt h n) := by
  have h1 : ∏ i, ∑ n, c i n * g n =
      ∑ f : Fin p → Fin K, (∏ i, c i (f i)) * ∏ n, g n ^ cnt f n := by
    rw [Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.prod_mul_distrib, prod_comp_eq_prod_pow f g]
  have h2 : ∏ j, star (∑ n, e j n * g n) =
      ∑ h : Fin q → Fin K, (∏ j, star (e j (h j))) * ∏ n, star (g n) ^ cnt h n := by
    simp only [star_sum, star_mul']
    rw [Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.prod_mul_distrib, prod_comp_eq_prod_pow h (fun n => star (g n))]
  rw [h1, h2, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

theorem integrable_cgPi_poly {p q : ℕ} (a : Fin K → ℝ)
    (c : Fin p → Fin K → ℂ) (e : Fin q → Fin K → ℂ) :
    Integrable (fun g : Fin K → ℂ =>
      (∏ i, ∑ n, c i n * g n) * ∏ j, star (∑ n, e j n * g n)) (cgPi a) := by
  simp_rw [integrand_expand]
  refine integrable_finset_sum _ fun f _ => integrable_finset_sum _ fun h _ => ?_
  exact (integrable_cgPi_monomial a (cnt f) (cnt h)).const_mul _

lemma monomial_value {p q : ℕ} (a : Fin K → ℝ)
    (f : Fin p → Fin K) (h : Fin q → Fin K) :
    (∏ n, (if cnt f n = cnt h n then ((((cnt f n).factorial : ℝ) / a n ^ cnt f n : ℝ) : ℂ)
        else (0 : ℂ))) =
      if (∀ n, cnt f n = cnt h n) then
        (∏ n, ((cnt f n).factorial : ℂ)) * ∏ n, ((a n : ℂ)⁻¹) ^ cnt f n else 0 := by
  classical
  by_cases H : ∀ n, cnt f n = cnt h n
  · rw [if_pos H, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun n _ => ?_
    rw [if_pos (H n)]
    push_cast
    rw [div_eq_mul_inv, inv_pow]
  · rw [if_neg H]
    push_neg at H
    obtain ⟨n, hn⟩ := H
    exact Finset.prod_eq_zero (Finset.mem_univ n) (if_neg hn)

lemma sum_perm_comp {p : ℕ} (f : Fin p → Fin K) (B : (Fin p → Fin K) → ℂ) :
    ∑ σ : Equiv.Perm (Fin p), B (f ∘ σ) =
      ∑ h : Fin p → Fin K,
        (if (∀ n, cnt f n = cnt h n) then ∏ n, ((cnt f n).factorial : ℂ) else 0) * B h := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun σ : Equiv.Perm (Fin p) => f ∘ σ)]
  refine Finset.sum_congr rfl fun h _ => ?_
  have : ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin p) => f ∘ σ = h), B (f ∘ σ) =
      ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin p) => f ∘ σ = h), B h :=
    Finset.sum_congr rfl fun σ hσ => by rw [(Finset.mem_filter.mp hσ).2]
  rw [this, Finset.sum_const, card_perm_comp_eq, nsmul_eq_mul]
  split_ifs <;> simp

lemma integral_cgPi_poly_expand {p q : ℕ} (a : Fin K → ℝ) (ha : ∀ n, 0 < a n)
    (c : Fin p → Fin K → ℂ) (e : Fin q → Fin K → ℂ) :
    ∫ g : Fin K → ℂ, (∏ i, ∑ n, c i n * g n) * ∏ j, star (∑ n, e j n * g n) ∂cgPi a =
      ∑ f : Fin p → Fin K, ∑ h : Fin q → Fin K,
        ((∏ i, c i (f i)) * ∏ j, star (e j (h j))) *
          (if (∀ n, cnt f n = cnt h n) then
            (∏ n, ((cnt f n).factorial : ℂ)) * ∏ n, ((a n : ℂ)⁻¹) ^ cnt f n else 0) := by
  simp_rw [integrand_expand]
  rw [integral_finset_sum _ (fun f _ => integrable_finsetSum _ fun h _ =>
    (integrable_cgPi_monomial a (cnt f) (cnt h)).const_mul _)]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [integral_finset_sum _ (fun h _ =>
    (integrable_cgPi_monomial a (cnt f) (cnt h)).const_mul _)]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [integral_const_mul, integral_cgPi_monomial a ha, monomial_value a]

theorem integral_cgPi_wick_eq {p : ℕ} (a : Fin K → ℝ) (ha : ∀ n, 0 < a n)
    (c e : Fin p → Fin K → ℂ) :
    ∫ g : Fin K → ℂ, (∏ i, ∑ n, c i n * g n) * ∏ j, star (∑ n, e j n * g n) ∂cgPi a =
      ∑ σ : Equiv.Perm (Fin p), ∏ i, ∑ n, c i n * star (e (σ i) n) / (a n : ℂ) := by
  classical
  rw [integral_cgPi_poly_expand a ha c e]
  · 
    -- right side
    have hR : ∀ σ : Equiv.Perm (Fin p), ∏ i, ∑ n, c i n * star (e (σ i) n) / (a n : ℂ) =
        ∑ f : Fin p → Fin K, (∏ i, c i (f i)) * (∏ j, star (e j (f (σ.symm j)))) *
          ∏ n, ((a n : ℂ)⁻¹) ^ cnt f n := by
      intro σ
      rw [Finset.prod_univ_sum]
      simp only [Fintype.piFinset_univ]
      refine Finset.sum_congr rfl fun f _ => ?_
      have e1 : ∏ i, c i (f i) * star (e (σ i) (f i)) / (a (f i) : ℂ) =
          (∏ i, c i (f i)) * (∏ i, star (e (σ i) (f i))) * ∏ i, ((a (f i) : ℂ)⁻¹) := by
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => by ring
      rw [e1, prod_comp_eq_prod_pow f (fun n => ((a n : ℂ)⁻¹))]
      congr 2
      rw [← Equiv.prod_comp σ (fun j => star (e j (f (σ.symm j))))]
      simp
    simp_rw [hR]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => ?_
    have h3 : ∑ σ : Equiv.Perm (Fin p), (∏ i, c i (f i)) * (∏ j, star (e j (f (σ.symm j)))) *
          ∏ n, ((a n : ℂ)⁻¹) ^ cnt f n =
        (∏ i, c i (f i)) * (∏ n, ((a n : ℂ)⁻¹) ^ cnt f n) *
          ∑ σ : Equiv.Perm (Fin p), ∏ j, star (e j ((f ∘ σ) j)) := by
      rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin p)))
        (fun σ => (∏ i, c i (f i)) * (∏ n, ((a n : ℂ)⁻¹) ^ cnt f n) *
          ∏ j, star (e j ((f ∘ σ) j)))]
      refine Finset.sum_congr rfl fun σ _ => ?_
      simp only [Equiv.inv_apply, Function.comp_apply, Equiv.Perm.inv_def]
      ring
    rw [h3, sum_perm_comp f (fun h => ∏ j, star (e j (h j))), Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs <;> ring
theorem integral_cgPi_wick_ne {p q : ℕ} (hpq : p ≠ q) (a : Fin K → ℝ) (ha : ∀ n, 0 < a n)
    (c : Fin p → Fin K → ℂ) (e : Fin q → Fin K → ℂ) :
    ∫ g : Fin K → ℂ, (∏ i, ∑ n, c i n * g n) * ∏ j, star (∑ n, e j n * g n) ∂cgPi a = 0 := by
  classical
  rw [integral_cgPi_poly_expand a ha c e]
  · 
    refine Finset.sum_eq_zero fun f _ => Finset.sum_eq_zero fun h _ => ?_
    have : ¬ (∀ n, cnt f n = cnt h n) := by
      intro H
      apply hpq
      have c1 : ∑ n, cnt f n = p := by
        unfold cnt
        rw [← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)]
        simp
      have c2 : ∑ n, cnt h n = q := by
        unfold cnt
        rw [← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)]
        simp
      rw [← c1, ← c2]
      exact Finset.sum_congr rfl fun n _ => H n
    rw [if_neg this, mul_zero]

/-- (2) covariance: `E[X_i conj Y_j] = Σ_n c_i,n conj(e_j,n) / a_n`. -/
theorem integral_cgPi_cov (a : Fin K → ℝ) (ha : ∀ n, 0 < a n) (c e : Fin K → ℂ) :
    ∫ g : Fin K → ℂ, (∑ n, c n * g n) * star (∑ n, e n * g n) ∂cgPi a =
      ∑ n, c n * star (e n) / (a n : ℂ) := by
  have := integral_cgPi_wick_eq (p := 1) a ha (fun _ => c) (fun _ => e)
  simpa using this

/-- (2) properness: `E[X_i X_i'] = 0`. -/
theorem integral_cgPi_proper (a : Fin K → ℝ) (ha : ∀ n, 0 < a n) (c c' : Fin K → ℂ) :
    ∫ g : Fin K → ℂ, (∑ n, c n * g n) * (∑ n, c' n * g n) ∂cgPi a = 0 := by
  have := integral_cgPi_wick_ne (p := 2) (q := 0) (by norm_num) a ha ![c, c'] (fun j => j.elim0)
  simpa [Fin.prod_univ_two] using this

/-- (4) Wick formula, with `e` reindexed along `Fin.cast` when `p = q`. -/
theorem integral_cgPi_wick {p q : ℕ} (a : Fin K → ℝ) (ha : ∀ n, 0 < a n)
    (c : Fin p → Fin K → ℂ) (e : Fin q → Fin K → ℂ) :
    ∫ g : Fin K → ℂ, (∏ i, ∑ n, c i n * g n) * ∏ j, star (∑ n, e j n * g n) ∂cgPi a =
      if h : p = q then
        ∑ σ : Equiv.Perm (Fin p), ∏ i,
          ∫ g : Fin K → ℂ, (∑ n, c i n * g n) *
            star (∑ n, e (Fin.cast h (σ i)) n * g n) ∂cgPi a
      else 0 := by
  by_cases h : p = q
  · subst h
    rw [dif_pos rfl, integral_cgPi_wick_eq a ha c e]
    refine Finset.sum_congr rfl fun σ _ => Finset.prod_congr rfl fun i _ => ?_
    rw [integral_cgPi_cov a ha]
    rfl
  · rw [dif_neg h, integral_cgPi_wick_ne h a ha c e]
end Pi

end NlsGge.HierarchyRiccati.Core

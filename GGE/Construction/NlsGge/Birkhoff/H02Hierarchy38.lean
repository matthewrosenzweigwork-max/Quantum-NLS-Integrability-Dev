import NlsGge.Birkhoff.S04Moments38b
import NlsGge.Spectral.F04Lemma38
import NlsGge.Hierarchy.FiniteOrderGaussianTail38

/-! # H02 (v2 `B:prop:hierarchy`), part 1: the coupling layer (Birkhoff-free)

Claim packet `blueprint/claims/H02.md`, sub-claims H02.01 and H02.02 (and the Gaussian
part of H02.03, H02.05); v2 lines 879-913.

* Rates `a_{m,n} = W_m(2πn)` (`hierRate38`) and `a_n = W(2πn)` (`fullWeightRate`), monotone in `m`
  with `a_{m,n} ↑ a_n`.
* The coupling of v2: `z^{(m)}_n = g_n / √a_{m,n}`, `z_n = g_n / √a_n`
  (`scaleSeq38`), with `(g_n)` independent standard complex Gaussians
  (`countableComplexGaussian (fun _ => 1)`), realizing `γ_m` and `γ_W` as push-forwards of the same
  probability measure (`countableComplexGaussian_eq_map_scale38`).
* The probability-one set `Ω₁` of `g` (`Omega1_38`): for every `m ≥ 2`, `z^{(m)} ∈ h^{m-1}`, and
  `∑ |g_n|² ⟨n⟩^{-3/2} < ∞` (`ae_mem_Omega1_38`). It is a countable intersection over `m`.
* Deterministic weighted-square convergence `z^{(m)} → z` in every `h^r` for `g ∈ Ω₁`, by dominated
  convergence from the initial degree `m₀ = r + 2` (`tendsto_scale_sobolev38`), and `z ∈ Ω₀` of S03.

Nothing here uses `B : BirkhoffTop38`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.SpectralFoundations NlsGge.Weights
  NlsGge.Sobolev38 Filter Topology
open ProbabilityTheory
open scoped ENNReal NNReal

/-! ### Rates -/

/-- `a_{m,n} = W_m(2πn)` of v2 `B:eq:finitehierarchy`, with the coefficients of v2 `eq:weight`. -/
def hierRate38 (c : ℕ → ℝ) (m : ℕ) (n : ℤ) : ℝ := partialWeight c m (2 * Real.pi * (n : ℝ))

theorem hierRate38_eq_finiteHierarchyRate38 (c : ℕ → ℝ) (m : ℕ) (n : ℤ) :
    hierRate38 c m n =
      NlsGge.HierarchyRiccati.Core.finiteHierarchyRate38 m (coefficient c) n := rfl

theorem partialWeight_eq_finiteWeightE02_38 (c : ℕ → ℝ) (m : ℕ) :
    partialWeight c m = finiteWeightE02_38 m (coefficient c) := rfl

section Rates

variable (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
  (hupper : ∀ j : ℕ, c j ≤ upper)

include hlower hbound

theorem hierRate38_pos (m : ℕ) (n : ℤ) : 0 < hierRate38 c m n :=
  hlower.trans_le (partialWeight_lower lower c hlower hbound m _)

theorem lower_le_hierRate38 (m : ℕ) (n : ℤ) : lower ≤ hierRate38 c m n :=
  partialWeight_lower lower c hlower hbound m _

theorem hierRate38_mono {m m' : ℕ} (h : m ≤ m') (n : ℤ) :
    hierRate38 c m n ≤ hierRate38 c m' n :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ h))
    (fun j _ _ => weightTerm_nonneg lower c hlower hbound _ j)

include hupper

theorem hierRate38_le_full (m : ℕ) (n : ℤ) : hierRate38 c m n ≤ fullWeightRate c n :=
  partialWeight_le_weight lower upper c hlower hbound hupper m _

theorem tendsto_hierRate38 (n : ℤ) :
    Tendsto (fun m : ℕ => hierRate38 c m n) atTop (𝓝 (fullWeightRate c n)) := by
  have h := (weightTerm_summable lower upper c hlower hbound hupper
    (2 * Real.pi * (n : ℝ))).hasSum.tendsto_sum_nat
  exact h.comp (tendsto_add_atTop_nat 1)

omit hlower hbound hupper

/-- Tail of the weight series: `W(r) - W_m(r) = ∑_{j>m} β_j r^{2j}`. -/
def weightTail38 (c : ℕ → ℝ) (m : ℕ) (r : ℝ) : ℝ := ∑' i : ℕ, weightTerm c r (i + (m + 1))

include hlower hbound hupper

theorem weight_sub_partialWeight38 (m : ℕ) (r : ℝ) :
    weight c r - partialWeight c m r = weightTail38 c m r := by
  have h := (weightTerm_summable lower upper c hlower hbound hupper r).sum_add_tsum_nat_add (m + 1)
  unfold weight partialWeight weightTail38
  linarith

theorem weightTail38_nonneg (m : ℕ) (r : ℝ) : 0 ≤ weightTail38 c m r :=
  tsum_nonneg (fun i => weightTerm_nonneg lower c hlower hbound r _)

theorem weightTail38_mono (m : ℕ) {r R : ℝ} (h : |r| ≤ R) :
    weightTail38 c m r ≤ weightTail38 c m R := by
  have hR : 0 ≤ R := (abs_nonneg r).trans h
  refine Summable.tsum_le_tsum (fun i => ?_) ?_ ?_
  · unfold weightTerm
    refine mul_le_mul_of_nonneg_left ?_ (coefficient_pos lower c hlower hbound _).le
    rw [pow_mul, pow_mul, ← sq_abs r]
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg r) h 2) _
  · exact (summable_nat_add_iff (m + 1)).2
      (weightTerm_summable lower upper c hlower hbound hupper r)
  · exact (summable_nat_add_iff (m + 1)).2
      (weightTerm_summable lower upper c hlower hbound hupper R)

theorem tendsto_weightTail38 (R : ℝ) :
    Tendsto (fun m : ℕ => weightTail38 c m R) atTop (𝓝 0) := by
  have h := _root_.tendsto_sum_nat_add (weightTerm c R)
  have h2 := h.comp (tendsto_add_atTop_nat 1)
  refine h2.congr (fun m => ?_)
  simp only [Function.comp, weightTail38]

end Rates

/-! ### The coupling by scaling -/

/-- `(scaleSeq q g)_n = g_n / √(q n)`. -/
def scaleSeq38 (q : ℤ → ℝ) (g : ℤ → ℂ) : ℤ → ℂ :=
  fun n => (((Real.sqrt (q n))⁻¹ : ℝ) : ℂ) * g n

theorem measurable_scaleSeq38 (q : ℤ → ℝ) : Measurable (scaleSeq38 q) :=
  measurable_pi_iff.2 fun n => measurable_const.mul (measurable_pi_apply n)

theorem norm_sq_scaleSeq38 (q : ℤ → ℝ) (g : ℤ → ℂ) (n : ℤ) (hq : 0 < q n) :
    ‖scaleSeq38 q g n‖ ^ 2 = ‖g n‖ ^ 2 / q n := by
  unfold scaleSeq38
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt hq.le]
  ring

theorem complexGaussian_map_scale38 (a : ℝ) (ha : 0 < a) :
    (complexGaussian 1).map (fun z : ℂ => (((Real.sqrt a)⁻¹ : ℝ) : ℂ) * z) = complexGaussian a := by
  set s : ℝ := (Real.sqrt a)⁻¹ with hs
  have hv : NNReal.mk (s ^ 2) (sq_nonneg s) * componentVariance 1 = componentVariance a := by
    apply NNReal.eq
    rw [NNReal.coe_mul, componentVariance_coe 1 one_pos, componentVariance_coe a ha]
    show s ^ 2 * (1 / (2 * 1)) = 1 / (2 * a)
    rw [hs, inv_pow, Real.sq_sqrt ha.le]
    field_simp
  have hmeas : Measurable (fun z : ℂ => ((s : ℝ) : ℂ) * z) := measurable_const.mul measurable_id
  have hp :
      ((gaussianReal 0 (componentVariance 1)).prod (gaussianReal 0 (componentVariance 1))).map
        (Prod.map (fun x : ℝ => s * x) (fun y : ℝ => s * y)) =
      (gaussianReal 0 (componentVariance a)).prod (gaussianReal 0 (componentVariance a)) := by
    rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
    simp only [gaussianReal_map_const_mul, mul_zero, hv]
  have hf :
      (fun z : ℂ => ((s : ℝ) : ℂ) * z) ∘ Complex.measurableEquivRealProd.symm =
        Complex.measurableEquivRealProd.symm ∘
          (Prod.map (fun x : ℝ => s * x) (fun y : ℝ => s * y)) := by
    funext p
    apply Complex.ext <;> simp [Complex.measurableEquivRealProd]
  unfold complexGaussian
  rw [Measure.map_map hmeas complexGaussian_measurable_transport, hf,
    ← Measure.map_map complexGaussian_measurable_transport (by fun_prop), hp]

/-- **The coupling of v2 (l.884-888).** For positive rates `q`, the product Gaussian with rates `q`
is the image of the standard product Gaussian (`E|g_n|² = 1`) under `g ↦ (g_n/√q_n)_n`. -/
theorem countableComplexGaussian_eq_map_scale38 (q : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n) :
    countableComplexGaussian q =
      (countableComplexGaussian (fun _ => (1 : ℝ))).map (scaleSeq38 q) := by
  unfold countableComplexGaussian
  have h := Measure.infinitePi_map_pi (μ := fun _ : ℤ => complexGaussian (1 : ℝ))
    (f := fun (n : ℤ) (z : ℂ) => (((Real.sqrt (q n))⁻¹ : ℝ) : ℂ) * z)
    (fun n => measurable_const.mul measurable_id)
  have e : scaleSeq38 q = fun (x : ℤ → ℂ) (i : ℤ) => (((Real.sqrt (q i))⁻¹ : ℝ) : ℂ) * x i := rfl
  rw [e, h]
  congr 1
  funext n
  exact (complexGaussian_map_scale38 (q n) (hq n)).symm

theorem integral_eq_integral_scale38 (q : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n)
    (f : (ℤ → ℂ) → ℝ) (hf : Measurable f) :
    ∫ z, f z ∂(countableComplexGaussian q) =
      ∫ g, f (scaleSeq38 q g) ∂(countableComplexGaussian (fun _ => (1 : ℝ))) := by
  rw [countableComplexGaussian_eq_map_scale38 q hq,
    integral_map (measurable_scaleSeq38 q).aemeasurable hf.aestronglyMeasurable]

/-! ### Rates of the hierarchy as a positive sequence -/

section Gauss

variable (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
  (hupper : ∀ j : ℕ, c j ≤ upper)

include hlower hbound hupper

theorem fullWeightRate_pos' (n : ℤ) : 0 < fullWeightRate c n :=
  fullWeightRate_pos lower upper c hlower hbound hupper n

/-- `⟨n⟩^{2(m-1)} / a_{m,n}`. -/
def tailRatio38 (c : ℕ → ℝ) (m : ℕ) (n : ℤ) : ℝ :=
  sobolevModeWeight ((m - 1 : ℕ) : ℝ) n / hierRate38 c m n

theorem summable_tailRatio38' {m : ℕ} (hm : 2 ≤ m) : Summable (tailRatio38 c m) := by
  have hβ : ∀ i ≤ m, 0 ≤ coefficient c i := fun i _ =>
    (coefficient_pos lower c hlower hbound i).le
  exact NlsGge.HierarchyRiccati.Core.summable_tailRatio38 m (coefficient c) hm hβ
    (coefficient_pos lower c hlower hbound 0) (coefficient_pos lower c hlower hbound m)

theorem tailRatio38_nonneg (m : ℕ) (n : ℤ) : 0 ≤ tailRatio38 c m n :=
  div_nonneg (sobolevModeWeight_pos _ n).le (hierRate38_pos lower c hlower hbound m n).le

end Gauss

/-! ### The probability-one set `Ω₁` -/

/-- The probability-one set of the coupling: `z^{(m)} ∈ h^{m-1}` for every `m ≥ 2` (the
countable intersection over the hierarchy order) and the series of v2 `B:eq:coupledbound`
`∑ |g_n|² ⟨n⟩^{-3/2}` is finite. -/
def Omega1_38 (c : ℕ → ℝ) : Set (ℤ → ℂ) :=
  {g | (∀ m : ℕ, 2 ≤ m → Summable (fun n : ℤ => tailRatio38 c m n * ‖g n‖ ^ 2)) ∧
    Summable (fun n : ℤ => japaneseBracket n ^ (-(3 / 2) : ℝ) * ‖g n‖ ^ 2)}

/-- The standard coupling measure: independent standard complex Gaussians, `E|g_n|² = 1`. -/
abbrev stdGauss38 : Measure (ℤ → ℂ) := countableComplexGaussian (fun _ => (1 : ℝ))

theorem ae_mem_Omega1_38 (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) :
    ∀ᵐ g ∂stdGauss38, g ∈ Omega1_38 c := by
  have h1 : ∀ᵐ g ∂stdGauss38, ∀ m : ℕ, 2 ≤ m →
      Summable (fun n : ℤ => tailRatio38 c m n * ‖g n‖ ^ 2) := by
    rw [ae_all_iff]
    intro m
    by_cases hm : 2 ≤ m
    · have := ae_sequenceSummable (fun _ : ℤ => (1 : ℝ)) (tailRatio38 c m) (fun _ => one_pos)
        (tailRatio38_nonneg lower upper c hlower hbound hupper m)
        (by simpa using summable_tailRatio38' lower upper c hlower hbound hupper hm)
      filter_upwards [this] with g hg using fun _ => hg
    · exact Filter.Eventually.of_forall (fun g h => absurd h hm)
  have h2 : ∀ᵐ g ∂stdGauss38,
      Summable (fun n : ℤ => japaneseBracket n ^ (-(3 / 2) : ℝ) * ‖g n‖ ^ 2) :=
    ae_sequenceSummable (fun _ : ℤ => (1 : ℝ)) (fun n => japaneseBracket n ^ (-(3 / 2) : ℝ))
      (fun _ => one_pos) (fun n => Real.rpow_nonneg (japaneseBracket_pos n).le _)
      (by simpa using summable_japaneseBracket_rpow_neg (3 / 2) (by norm_num))
  filter_upwards [h1, h2] with g hg1 hg2 using ⟨hg1, hg2⟩

/-! ### Pathwise statements for `g ∈ Ω₁` -/

section Path

variable (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
  (hupper : ∀ j : ℕ, c j ≤ upper)

/-- `z^{(m)} = (g_n/√a_{m,n})_n`. -/
def zHier38 (c : ℕ → ℝ) (m : ℕ) (g : ℤ → ℂ) : ℤ → ℂ := scaleSeq38 (hierRate38 c m) g

/-- `z = (g_n/√a_n)_n`. -/
def zFull38 (c : ℕ → ℝ) (g : ℤ → ℂ) : ℤ → ℂ := scaleSeq38 (fullWeightRate c) g

include hlower hbound hupper

theorem norm_sq_zHier38 (m : ℕ) (g : ℤ → ℂ) (n : ℤ) :
    ‖zHier38 c m g n‖ ^ 2 = ‖g n‖ ^ 2 / hierRate38 c m n :=
  norm_sq_scaleSeq38 _ g n (hierRate38_pos lower c hlower hbound m n)

theorem norm_sq_zFull38 (g : ℤ → ℂ) (n : ℤ) :
    ‖zFull38 c g n‖ ^ 2 = ‖g n‖ ^ 2 / fullWeightRate c n :=
  norm_sq_scaleSeq38 _ g n (fullWeightRate_pos lower upper c hlower hbound hupper n)

/-- **v2 (l.890-891), a.s. `z^{(m)} ∈ h^{m-1}`.** -/
theorem zHier38_mem_seqSobolev38 {g : ℤ → ℂ} (hg : g ∈ Omega1_38 c) {m : ℕ} (hm : 2 ≤ m) :
    zHier38 c m g ∈ seqSobolev38 ((m - 1 : ℕ) : ℝ) := by
  have := hg.1 m hm
  have h : Summable (fun n : ℤ => sobolevModeWeight ((m - 1 : ℕ) : ℝ) n *
      ‖zHier38 c m g n‖ ^ 2) := by
    refine this.congr (fun n => ?_)
    rw [tailRatio38, norm_sq_zHier38 lower upper c hlower hbound hupper]
    ring
  exact (mem_seqSobolev38_iff _ _).2 h

theorem zHier38_mem_seqSobolev38_nat {g : ℤ → ℂ} (hg : g ∈ Omega1_38 c) {r m : ℕ}
    (hm : r + 2 ≤ m) : zHier38 c m g ∈ seqSobolev38 (r : ℝ) := by
  refine seqSobolev38_mono ?_ (zHier38_mem_seqSobolev38 lower upper c hlower hbound hupper hg
    (m := m) (by omega))
  exact_mod_cast (by omega : r ≤ m - 1)

/-- The weighted domination: for `m ≥ r + 2`,
`⟨n⟩^{2r} ‖z^{(m)}_n‖² ≤ ⟨n⟩^{2(r+1)} ‖g_n‖² / a_{r+2,n}`. -/
theorem sobolev_term_dominated38 (r : ℕ) {m : ℕ} (hm : r + 2 ≤ m) (g : ℤ → ℂ) (n : ℤ) :
    sobolevModeWeight (r : ℝ) n * ‖zHier38 c m g n‖ ^ 2 ≤ tailRatio38 c (r + 2) n * ‖g n‖ ^ 2 := by
  rw [norm_sq_zHier38 lower upper c hlower hbound hupper, tailRatio38]
  have hw : sobolevModeWeight (r : ℝ) n ≤ sobolevModeWeight (((r + 2 - 1 : ℕ)) : ℝ) n :=
    sobolevModeWeight_mono (by exact_mod_cast (by omega : r ≤ r + 2 - 1)) n
  have ha := hierRate38_mono lower c hlower hbound hm n
  have hp := hierRate38_pos lower c hlower hbound (r + 2) n
  have hp' := hierRate38_pos lower c hlower hbound m n
  have hg0 : 0 ≤ ‖g n‖ ^ 2 := sq_nonneg _
  calc sobolevModeWeight (r : ℝ) n * (‖g n‖ ^ 2 / hierRate38 c m n)
      ≤ sobolevModeWeight (((r + 2 - 1 : ℕ)) : ℝ) n * (‖g n‖ ^ 2 / hierRate38 c (r + 2) n) := by
        apply mul_le_mul hw _ (by positivity) (sobolevModeWeight_pos _ n).le
        exact div_le_div_of_nonneg_left hg0 hp ha
    _ = _ := by ring

theorem zFull38_mem_seqSobolev38_nat {g : ℤ → ℂ} (hg : g ∈ Omega1_38 c) (r : ℕ) :
    zFull38 c g ∈ seqSobolev38 (r : ℝ) := by
  have hs := hg.1 (r + 2) (by omega)
  have h : Summable (fun n : ℤ => sobolevModeWeight (r : ℝ) n * ‖zFull38 c g n‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (sobolevModeWeight_pos _ n).le
      (sq_nonneg _)) (fun n => ?_) hs
    rw [norm_sq_zFull38 lower upper c hlower hbound hupper, tailRatio38]
    have hw : sobolevModeWeight (r : ℝ) n ≤ sobolevModeWeight (((r + 2 - 1 : ℕ)) : ℝ) n :=
      sobolevModeWeight_mono (by exact_mod_cast (by omega : r ≤ r + 2 - 1)) n
    have ha := hierRate38_le_full lower upper c hlower hbound hupper (r + 2) n
    have hp := hierRate38_pos lower c hlower hbound (r + 2) n
    have hg0 : 0 ≤ ‖g n‖ ^ 2 := sq_nonneg _
    calc sobolevModeWeight (r : ℝ) n * (‖g n‖ ^ 2 / fullWeightRate c n)
        ≤ sobolevModeWeight (((r + 2 - 1 : ℕ)) : ℝ) n * (‖g n‖ ^ 2 / hierRate38 c (r + 2) n) := by
          apply mul_le_mul hw _ (by
            have := fullWeightRate_pos lower upper c hlower hbound hupper n
            positivity) (sobolevModeWeight_pos _ n).le
          exact div_le_div_of_nonneg_left hg0 hp ha
      _ = _ := by ring
  exact (mem_seqSobolev38_iff _ _).2 h

/-- `z ∈ Ω₀` of S03 (smooth sequence support and finiteness of the tail series). -/
theorem zFull38_mem_Omega038 {g : ℤ → ℂ} (hg : g ∈ Omega1_38 c) : zFull38 c g ∈ Omega038 c := by
  refine ⟨fun m => ?_, ?_⟩
  · exact (mem_seqSobolev38_iff _ _).1 (zFull38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg m)
  · refine hg.2.congr (fun n => ?_)
    rw [tailWeight38, norm_sq_zFull38 lower upper c hlower hbound hupper]
    have := fullWeightRate_pos lower upper c hlower hbound hupper n
    field_simp

theorem norm_sq_zHier_sub_zFull38 (m : ℕ) (g : ℤ → ℂ) (n : ℤ) :
    ‖zHier38 c m g n - zFull38 c g n‖ ^ 2 =
      ((Real.sqrt (hierRate38 c m n))⁻¹ - (Real.sqrt (fullWeightRate c n))⁻¹) ^ 2 * ‖g n‖ ^ 2 := by
  unfold zHier38 zFull38 scaleSeq38
  rw [← sub_mul, norm_mul, mul_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]

theorem tendsto_zHier_sub_zFull_term38 (g : ℤ → ℂ) (n : ℤ) :
    Tendsto (fun m : ℕ => ‖zHier38 c m g n - zFull38 c g n‖ ^ 2) atTop (𝓝 0) := by
  have hpos := fullWeightRate_pos lower upper c hlower hbound hupper n
  have h1 := tendsto_hierRate38 lower upper c hlower hbound hupper n
  have h2 : Tendsto (fun m : ℕ => (Real.sqrt (hierRate38 c m n))⁻¹) atTop
      (𝓝 ((Real.sqrt (fullWeightRate c n))⁻¹)) :=
    ((Real.continuous_sqrt.tendsto _).comp h1).inv₀ (Real.sqrt_pos.2 hpos).ne'
  have h3 := ((h2.sub_const ((Real.sqrt (fullWeightRate c n))⁻¹)).pow 2).mul_const (‖g n‖ ^ 2)
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at h3
  refine h3.congr (fun m => ?_)
  rw [norm_sq_zHier_sub_zFull38 lower upper c hlower hbound hupper]

/-- **v2 (l.891-893): dominated convergence for the weighted square series.** For `g ∈ Ω₁` and every
`r`, `∑_n ⟨n⟩^{2r} |z^{(m)}_n - z_n|² → 0` (the series are the squared `h^r` distances once
`m ≥ r + 2`). -/
theorem tendsto_scale_sobolev38 {g : ℤ → ℂ} (hg : g ∈ Omega1_38 c) (r : ℕ) :
    Tendsto (fun m : ℕ => ∑' n : ℤ, sobolevModeWeight (r : ℝ) n *
      ‖zHier38 c m g n - zFull38 c g n‖ ^ 2) atTop (𝓝 0) := by
  have hbsum : Summable (fun n : ℤ => tailRatio38 c (r + 2) n * ‖g n‖ ^ 2) := hg.1 (r + 2) (by omega)
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℕ))
    (f := fun (m : ℕ) (n : ℤ) => sobolevModeWeight (r : ℝ) n *
      ‖zHier38 c m g n - zFull38 c g n‖ ^ 2) (g := fun _ => (0 : ℝ))
    (bound := fun n : ℤ => tailRatio38 c (r + 2) n * ‖g n‖ ^ 2) hbsum
    (fun n => by
      simpa using (tendsto_zHier_sub_zFull_term38 lower upper c hlower hbound hupper g n).const_mul
        (sobolevModeWeight (r : ℝ) n))
    (by
      refine Filter.eventually_atTop.2 ⟨r + 2, fun m hm n => ?_⟩
      have hw := sobolevModeWeight_pos (r : ℝ) n
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw.le (sq_nonneg _))]
      refine le_trans (mul_le_mul_of_nonneg_left ?_ hw.le)
        (sobolev_term_dominated38 lower upper c hlower hbound hupper r hm g n)
      rw [norm_sq_zHier_sub_zFull38 lower upper c hlower hbound hupper,
        norm_sq_zHier38 lower upper c hlower hbound hupper]
      have hq := hierRate38_pos lower c hlower hbound m n
      have hsq := Real.sqrt_pos.2 hq
      have hle : fullWeightRate c n ≥ hierRate38 c m n :=
        hierRate38_le_full lower upper c hlower hbound hupper m n
      have hs0 : 0 < (Real.sqrt (fullWeightRate c n))⁻¹ :=
        inv_pos.2 (Real.sqrt_pos.2 (hq.trans_le hle))
      have hs1 : (Real.sqrt (fullWeightRate c n))⁻¹ ≤ (Real.sqrt (hierRate38 c m n))⁻¹ :=
        inv_anti₀ hsq (Real.sqrt_le_sqrt hle)
      have h4 : ((Real.sqrt (hierRate38 c m n))⁻¹ - (Real.sqrt (fullWeightRate c n))⁻¹) ^ 2 ≤
          ((Real.sqrt (hierRate38 c m n))⁻¹) ^ 2 := by
        apply pow_le_pow_left₀ (by linarith) (by linarith)
      have h5 : ((Real.sqrt (hierRate38 c m n))⁻¹) ^ 2 = 1 / hierRate38 c m n := by
        rw [inv_pow, Real.sq_sqrt hq.le]; ring
      rw [h5] at h4
      calc ((Real.sqrt (hierRate38 c m n))⁻¹ - (Real.sqrt (fullWeightRate c n))⁻¹) ^ 2 * ‖g n‖ ^ 2
          ≤ 1 / hierRate38 c m n * ‖g n‖ ^ 2 :=
            mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
        _ = ‖g n‖ ^ 2 / hierRate38 c m n := by ring)
  rw [tsum_zero] at h
  exact h

/-- Carrier form: for `g ∈ Ω₁`, `z^{(k + r + 2)} → z` in the real Hilbert carrier of `h^r`. -/
theorem tendsto_carrier_scale38 {g : ℤ → ℂ} (hg : g ∈ Omega1_38 c) (r : ℕ) :
    Tendsto (fun k : ℕ => carrierMk38 (r : ℝ) (zHier38 c (k + (r + 2)) g)
        (zHier38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg (by omega))) atTop
      (𝓝 (carrierMk38 (r : ℝ) (zFull38 c g)
        (zFull38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg r))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hD := (tendsto_scale_sobolev38 lower upper c hlower hbound hupper hg r).comp
    (tendsto_add_atTop_nat (r + 2))
  have h7 : Tendsto (fun k : ℕ => ‖carrierMk38 (r : ℝ) (zHier38 c (k + (r + 2)) g)
        (zHier38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg (by omega)) -
      carrierMk38 (r : ℝ) (zFull38 c g)
        (zFull38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg r)‖ ^ 2) atTop
      (𝓝 0) := by
    refine hD.congr (fun k => ?_)
    have hsub : carrierMk38 (r : ℝ) (zHier38 c (k + (r + 2)) g)
          (zHier38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg (by omega)) -
        carrierMk38 (r : ℝ) (zFull38 c g)
          (zFull38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg r) =
        carrierMk38 (r : ℝ) (zHier38 c (k + (r + 2)) g - zFull38 c g)
          (seqSobolev38_sub (zHier38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg
            (by omega)) (zFull38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg r)) :=
      (carrierMk38_sub _ _ _ _ _).symm
    rw [hsub]
    have h2 := (carrier_hasSum_norm_sq38 (r : ℝ) (carrierMk38 (r : ℝ)
      (zHier38 c (k + (r + 2)) g - zFull38 c g)
      (seqSobolev38_sub (zHier38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg
        (by omega)) (zFull38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg r)))).tsum_eq
    rw [← h2]
    rfl
  have h8 := (Real.continuous_sqrt.tendsto 0).comp h7
  simp only [Real.sqrt_zero, Function.comp_def, Real.sqrt_sq (norm_nonneg _)] at h8
  exact h8

end Path

end NlsGge.Birkhoff
end

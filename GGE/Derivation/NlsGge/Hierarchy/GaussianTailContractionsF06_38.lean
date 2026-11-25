import NlsGge.Hierarchy.ContractionMonomialBound38
import NlsGge.Hierarchy.RiccatiJetEvaluationFiniteIntervalSumRecoverySecond
import Mathlib.Tactic

/-! Batch 38, F06-C1: `C:lem:contractions` (paper/v2.tex l.736-784) with a finite upper Fourier
cutoff. For `v = planeReal N z ∈ F_N` and a finite Gaussian tail `Y = Σ_k g_k e_{ι k}` with
`N < |ι k|` and rates `a_{m,ι k}`, the correction
`E[V_m(v + Y)] − V_m(v)`, with `V_m(u) = Σ_{j≤m} β_j Re ∫₀¹ eval(R_j^norm)(u)` the realized local
remainder on smooth fields, is bounded by `A_m (N^{-2m} + Σ_{l=1}^m (M/N)^l) ≤ (B_m/N)(1 + M^m)`,
uniformly in the tail modes. -/

set_option autoImplicit false
noncomputable section
namespace NlsGge.HierarchyRiccati.Core

open MeasureTheory NlsGge.Pilot NlsGge.Measure
open scoped ContDiff

section Integrability

variable {O : Type*} [Fintype O] [DecidableEq O]

/-- `g`-integrability of the `x`-integral of one occurrence product after the tail substitution. -/
theorem prodJet_integrable38 (m j : ℕ) (β : ℕ → ℝ) (hm : 1 ≤ m) (hβ : ∀ i ≤ m, 0 ≤ β i)
    (h0 : 0 < β 0) (hM : 0 < β m) (bar : O → Bool) (ord : O → ℕ) (hord : ∀ t, ord t ≤ m - 1)
    (hbal : (Finset.univ.filter fun t => bar t = true).card =
      (Finset.univ.filter fun t => ¬ bar t = true).card)
    (h4 : 4 ≤ Fintype.card O) (hdeg : ∑ t, ord t + Fintype.card O = 2 * j + 2) (hj : j ≤ m)
    (N : ℕ) (hN : 1 ≤ N) (z : FourierPlane N) {K : ℕ} (ι : Fin K → ℤ)
    (hinj : Function.Injective ι) (hι : ∀ k, (N : ℤ) < |ι k|) :
    Integrable (fun g : Fin K → ℂ => ∫ x in (0 : ℝ)..1,
        ∏ t, jet38 bar ord (fun y => planeReal N z y + tailField38 ι g y) t x)
      (cgPi (fun k => finiteHierarchyRate38 m β (ι k))) := by
  classical
  set P := (Finset.univ : Finset O).powerset
  have hint : ∀ R ∈ P, Integrable (fun g : Fin K → ℂ => ∫ x in (0 : ℝ)..1,
      termR38 bar ord N z ι R x g) (cgPi (fun k => finiteHierarchyRate38 m β (ι k))) := by
    intro R _
    by_cases hR : R = Finset.univ
    · subst hR
      have : (fun g : Fin K → ℂ => ∫ x in (0 : ℝ)..1, termR38 bar ord N z ι Finset.univ x g) =
          fun _ => ∫ x in (0 : ℝ)..1, ∏ t, jet38 bar ord (planeReal N z) t x := by
        funext g; simp [termR38]
      rw [this]
      exact integrable_const _
    · exact (R_term_bound38 m j β hm hβ h0 hM bar ord hord hbal h4 hdeg hj N hN z ι hinj hι
        R hR).1
  have heq : (fun g : Fin K → ℂ => ∫ x in (0 : ℝ)..1,
        ∏ t, jet38 bar ord (fun y => planeReal N z y + tailField38 ι g y) t x) =
      fun g => ∑ R ∈ P, ∫ x in (0 : ℝ)..1, termR38 bar ord N z ι R x g := by
    funext g
    simp_rw [prod_jet_expand38]
    exact intervalIntegral.integral_finsetSum (fun R _ =>
      (continuous_termR38 bar ord N z ι R g).intervalIntegrable _ _)
  rw [heq]
  exact integrable_finsetSum _ hint

end Integrability

/-- `g`-integrability for every supported monomial of the normalized remainder `R_j`. -/
theorem normalizedRemainder_monomial_integrable38 (m j : ℕ) (β : ℕ → ℝ) (hm : 1 ≤ m)
    (hβ : ∀ i ≤ m, 0 ≤ β i) (h0 : 0 < β 0) (hM : 0 < β m) (hj : j ≤ m)
    (q : Jet →₀ ℕ)
    (hq : q ∈ (formalChargeRemainderNormalizedUniformNativeRecovery29Fourth j).support)
    (N : ℕ) (hN : 1 ≤ N) (z : FourierPlane N) {K : ℕ} (ι : Fin K → ℤ)
    (hinj : Function.Injective ι) (hι : ∀ k, (N : ℤ) < |ι k|) :
    Integrable (fun g : Fin K → ℂ => ∫ x in (0 : ℝ)..1,
        riccatiJetEvaluation (fun y => planeReal N z y + tailField38 ι g y) x
          (MvPolynomial.monomial q
            ((formalChargeRemainderNormalizedUniformNativeRecovery29Fourth j).coeff q)))
      (cgPi (fun k => finiteHierarchyRate38 m β (ι k))) := by
  classical
  have hprop := formalChargeRemainderNormalizedUniform_propertiesNativeRecovery29Fourth j
  have hbi := hprop.2.2.1 q hq
  have hwt : riccatiJetWeightHomAfterComponents q = 2 * j + 2 := by
    simpa [riccatiJetBidegreeAfterComponents] using congrArg Prod.fst hbi
  have hg : riccatiJetGaugeHomAfterComponents q = 0 := by
    simpa [riccatiJetBidegreeAfterComponents] using congrArg Prod.snd hbi
  have hdeg : ∑ t : OccType38 q, occOrd38 q t + Fintype.card (OccType38 q) = 2 * j + 2 := by
    rw [sum_ord_occ38, card_occ38, add_comm,
      ← riccatiJetWeight_eq_degree_add_derivativeOrderSumNativeRecovery]
    exact hwt
  have h := prodJet_integrable38 m j β hm hβ h0 hM (occBar38 q) (occOrd38 q)
    (fun t => (hprop.1 q hq t.1.1 t.1.2).trans (by omega)) (card_bar_occ38 q hg)
    (by rw [card_occ38]; exact hprop.2.1 q hq) hdeg hj N hN z ι hinj hι
  simp_rw [eval_monomial38]
  simp_rw [intervalIntegral.integral_const_mul]
  exact h.const_mul _

/-- The realized local remainder on smooth fields:
`V_m(u) = Σ_{j≤m} β_j Re ∫₀¹ eval(R_j^norm)(u)`. -/
def vLocal38 (m : ℕ) (β : ℕ → ℝ) (u : ℝ → ℂ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), β j *
    (∫ x in (0 : ℝ)..1,
      riccatiJetEvaluation u x (formalChargeRemainderNormalizedUniformNativeRecovery29Fourth j)).re

theorem planeTail_contDiff38 (N : ℕ) (z : FourierPlane N) {K : ℕ} (ι : Fin K → ℤ)
    (g : Fin K → ℂ) : ContDiff ℝ ∞ (fun y => planeReal N z y + tailField38 ι g y) :=
  ((contDiff_planeReal N z).add (contDiff_tailField38 ι g)).of_le le_top

theorem integral_eval_as_sum38 (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (P : Poly) :
    (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x P) =
      ∑ q ∈ P.support, ∫ x in (0 : ℝ)..1,
        riccatiJetEvaluation u x (MvPolynomial.monomial q (P.coeff q)) := by
  conv_lhs => rw [MvPolynomial.as_sum P]
  exact riccatiJetEvaluation_integral_finset_sumNativeRecoverySecond u hu _ _

/-- `Φ = N^{-2m} + Σ_{l=1}^m (M/N)^l ≤ (m+1)(1 + M^m)/N` for `N ≥ 1`, `m ≥ 1`, `M ≥ 0`. -/
theorem Phi38_le38 (m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) (M : ℝ) (hM : 0 ≤ M) :
    Phi38 m N M ≤ (m + 1) * ((1 + M ^ m) / N) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hpow : ∀ l : ℕ, 1 ≤ l → l ≤ m → M ^ l ≤ 1 + M ^ m := by
    intro l hl1 hlm
    by_cases hM1 : M ≤ 1
    · have : M ^ l ≤ 1 := pow_le_one₀ hM hM1
      linarith [pow_nonneg hM m]
    · have : M ^ l ≤ M ^ m := pow_le_pow_right₀ (by linarith) hlm
      linarith
  have hNl : ∀ l : ℕ, 1 ≤ l → (N : ℝ) ≤ (N : ℝ) ^ l := fun l hl => by
    calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (N : ℝ) ^ l := pow_le_pow_right₀ hN1 hl
  unfold Phi38
  have h1 : ((N : ℝ) ^ (2 * m))⁻¹ ≤ (1 + M ^ m) / N := by
    rw [inv_eq_one_div]
    apply div_le_div₀ (by positivity) (by linarith [pow_nonneg hM m]) hN0 (hNl _ (by omega))
  have h2 : ∑ l ∈ Finset.Icc 1 m, (M / N) ^ l ≤ ∑ _l ∈ Finset.Icc 1 m, (1 + M ^ m) / N := by
    apply Finset.sum_le_sum
    intro l hl
    obtain ⟨hl1, hlm⟩ := Finset.mem_Icc.mp hl
    rw [div_pow]
    apply div_le_div₀ (by positivity) (hpow l hl1 hlm) hN0 (hNl l hl1)
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at h2
  have : ((m + 1 - 1 : ℕ) : ℝ) = m := by push_cast; simp
  rw [this] at h2
  nlinarith

/-- F06-C1 (`C:lem:contractions` with an upper Fourier cutoff): the Gaussian-tail correction of the
realized local remainder is bounded by `A (N^{-2m} + Σ_{l=1}^m (M/N)^l)`, with `A` independent of
`N`, `z`, and of the (finitely many, injective, high) tail modes; the `g`-integrability of
`V_m(v + Y)` is part of the conclusion. -/
theorem contraction_finiteCutoff38 (m : ℕ) (β : ℕ → ℝ) (hm : 1 ≤ m) (hβ : ∀ i ≤ m, 0 ≤ β i)
    (h0 : 0 < β 0) (hM : 0 < β m) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (z : FourierPlane N) (K : ℕ) (ι : Fin K → ℤ),
      Function.Injective ι → (∀ k, (N : ℤ) < |ι k|) →
      Integrable (fun g : Fin K → ℂ => vLocal38 m β (fun y => planeReal N z y + tailField38 ι g y))
        (cgPi (fun k => finiteHierarchyRate38 m β (ι k))) ∧
      |(∫ g : Fin K → ℂ, vLocal38 m β (fun y => planeReal N z y + tailField38 ι g y)
          ∂cgPi (fun k => finiteHierarchyRate38 m β (ι k))) -
        vLocal38 m β (planeReal N z)| ≤ A * Phi38 m N (∑ i, ‖z i‖ ^ 2) := by
  classical
  set R : ℕ → Poly := formalChargeRemainderNormalizedUniformNativeRecovery29Fourth with hRdef
  have hb : ∀ j : ℕ, ∀ q : Jet →₀ ℕ, ∃ A : ℝ, 0 ≤ A ∧ (j ≤ m → q ∈ (R j).support →
      ∀ (N : ℕ), 1 ≤ N → ∀ (z : FourierPlane N) (K : ℕ) (ι : Fin K → ℤ),
      Function.Injective ι → (∀ k, (N : ℤ) < |ι k|) →
      ‖(∫ g : Fin K → ℂ, (∫ x in (0 : ℝ)..1,
            riccatiJetEvaluation (fun y => planeReal N z y + tailField38 ι g y) x
              (MvPolynomial.monomial q ((R j).coeff q)))
          ∂cgPi (fun k => finiteHierarchyRate38 m β (ι k))) -
        ∫ x in (0 : ℝ)..1, riccatiJetEvaluation (planeReal N z) x
          (MvPolynomial.monomial q ((R j).coeff q))‖ ≤
      A * Phi38 m N (∑ i, ‖z i‖ ^ 2)) := by
    intro j q
    by_cases h : j ≤ m ∧ q ∈ (R j).support
    · obtain ⟨A, hA0, hA⟩ := normalizedRemainder_monomial_tail_bound38 m j β hm hβ h0 hM h.1 q h.2
      exact ⟨A, hA0, fun _ _ N hN z K ι hinj hι => (hA N hN z K ι hinj hι).trans_eq (by
        unfold Phi38; ring)⟩
    · exact ⟨0, le_rfl, fun hj hq => absurd ⟨hj, hq⟩ h⟩
  choose A hA0 hA using hb
  refine ⟨∑ j ∈ Finset.range (m + 1), |β j| * ∑ q ∈ (R j).support, A j q, ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _)
      (Finset.sum_nonneg fun q _ => hA0 j q)
  intro N hN z K ι hinj hι
  set μ := cgPi (fun k => finiteHierarchyRate38 m β (ι k)) with hμ
  set u : (Fin K → ℂ) → ℝ → ℂ := fun g y => planeReal N z y + tailField38 ι g y with hu
  set I : ℕ → (Jet →₀ ℕ) → (Fin K → ℂ) → ℂ := fun j q g => ∫ x in (0 : ℝ)..1,
    riccatiJetEvaluation (u g) x (MvPolynomial.monomial q ((R j).coeff q)) with hI
  set I0 : ℕ → (Jet →₀ ℕ) → ℂ := fun j q => ∫ x in (0 : ℝ)..1,
    riccatiJetEvaluation (planeReal N z) x (MvPolynomial.monomial q ((R j).coeff q)) with hI0
  have hIint : ∀ j ∈ Finset.range (m + 1), ∀ q ∈ (R j).support, Integrable (I j q) μ :=
    fun j hj q hq => normalizedRemainder_monomial_integrable38 m j β hm hβ h0 hM
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) q hq N hN z ι hinj hι
  have hF : ∀ j g, (∫ x in (0 : ℝ)..1, riccatiJetEvaluation (u g) x (R j)) =
      ∑ q ∈ (R j).support, I j q g := fun j g =>
    integral_eval_as_sum38 (u g) (planeTail_contDiff38 N z ι g) (R j)
  have hF0 : ∀ j, (∫ x in (0 : ℝ)..1, riccatiJetEvaluation (planeReal N z) x (R j)) =
      ∑ q ∈ (R j).support, I0 j q := fun j =>
    integral_eval_as_sum38 (planeReal N z) ((contDiff_planeReal N z).of_le le_top) (R j)
  have hFint : ∀ j ∈ Finset.range (m + 1),
      Integrable (fun g => ∑ q ∈ (R j).support, I j q g) μ :=
    fun j hj => integrable_finsetSum _ (hIint j hj)
  have hre : ∀ j ∈ Finset.range (m + 1),
      Integrable (fun g => β j * (∑ q ∈ (R j).support, I j q g).re) μ := by
    intro j hj
    have h := (hFint j hj).re
    simp only [RCLike.re_to_complex] at h
    exact h.const_mul _
  have hV : (fun g => vLocal38 m β (u g)) =
      fun g => ∑ j ∈ Finset.range (m + 1), β j * (∑ q ∈ (R j).support, I j q g).re := by
    funext g
    unfold vLocal38
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hF j g]
  have hVint : Integrable (fun g => vLocal38 m β (u g)) μ := by
    rw [hV]
    exact integrable_finsetSum _ hre
  refine ⟨hVint, ?_⟩
  have hint_eq : (∫ g, vLocal38 m β (u g) ∂μ) =
      ∑ j ∈ Finset.range (m + 1), β j * (∑ q ∈ (R j).support, ∫ g, I j q g ∂μ).re := by
    rw [hV, integral_finsetSum _ hre]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hr := integral_re (hFint j hj)
    simp only [RCLike.re_to_complex] at hr
    rw [integral_const_mul, hr, integral_finsetSum _ (hIint j hj)]
  have hv_eq : vLocal38 m β (planeReal N z) =
      ∑ j ∈ Finset.range (m + 1), β j * (∑ q ∈ (R j).support, I0 j q).re := by
    unfold vLocal38
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hF0 j]
  rw [hint_eq, hv_eq, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← mul_sub, abs_mul, ← Complex.sub_re, ← Finset.sum_sub_distrib, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun q hq => hA j q hjm hq N hN z K ι hinj hι

/-- Second form of `C:eq:massbound`: `≤ (B/N)(1 + M^m)`. -/
theorem contraction_finiteCutoff_simple38 (m : ℕ) (β : ℕ → ℝ) (hm : 1 ≤ m)
    (hβ : ∀ i ≤ m, 0 ≤ β i) (h0 : 0 < β 0) (hM : 0 < β m) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (z : FourierPlane N) (K : ℕ) (ι : Fin K → ℤ),
      Function.Injective ι → (∀ k, (N : ℤ) < |ι k|) →
      |(∫ g : Fin K → ℂ, vLocal38 m β (fun y => planeReal N z y + tailField38 ι g y)
          ∂cgPi (fun k => finiteHierarchyRate38 m β (ι k))) -
        vLocal38 m β (planeReal N z)| ≤ B / N * (1 + (∑ i, ‖z i‖ ^ 2) ^ m) := by
  obtain ⟨A, hA0, h⟩ := contraction_finiteCutoff38 m β hm hβ h0 hM
  refine ⟨A * (m + 1), by positivity, fun N hN z K ι hinj hι => ?_⟩
  have hMnn : 0 ≤ ∑ i, ‖z i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  refine (h N hN z K ι hinj hι).2.trans ?_
  have := Phi38_le38 m N hm hN _ hMnn
  calc A * Phi38 m N (∑ i, ‖z i‖ ^ 2) ≤ A * ((m + 1) * ((1 + (∑ i, ‖z i‖ ^ 2) ^ m) / N)) :=
        mul_le_mul_of_nonneg_left this hA0
    _ = A * (m + 1) / N * (1 + (∑ i, ‖z i‖ ^ 2) ^ m) := by ring

end NlsGge.HierarchyRiccati.Core

end

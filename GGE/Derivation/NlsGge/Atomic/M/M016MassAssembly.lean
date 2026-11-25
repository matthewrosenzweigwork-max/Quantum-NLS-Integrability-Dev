import Mathlib
import NlsGge.Atomic.M.M016MassCore
import NlsGge.Atomic.M.M016DysonCore

/- M016 MASS ASSEMBLY PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/M/M016MassAssembly.lean. Support declaration `NlsGge.ThirdConsultation.M.discriminant_imaginary_bilinear_mass`
   for the COMPLEX M-016 head (Pro R16 §1.3, PRO_DEFINITION_RESPONSE_FP80_16.md L156-164, head VERBATIM; proof §4).
   Leaves (in NlsGge.ThirdConsultation.M016AssemblyAux):
   * N1_10, N1_01, N2_00, N2_11: explicit first/second Dyson terms at z = iτ.
   * trOne_two (leaf (b)): tr N₂(1) = e^τ · P_τ with P_τ exactly M016MassCore's ∫∫ pairW·φ₁(s)φ₂(r); the wrap part by a
     triangular Fubini swap (kernel split kLow + kWrap on the product measure, integral_prod / integral_prod_symm).
   * schur_pot, majA_le_schur, majW_le_schur: A' ≤ S and W(1) ≤ S ≤ (1-e^{-2τ})/(2τ)·‖φ₁‖₂‖φ₂‖₂ (schur_bound).
   * remainder_tendsto: 2τ·e^{-τ}(Δ(iτ) − Σ_{k<4} tr N_k(1)) → 0, bound 2M²/τ (DysonCore.dyson_remainder_le).
   Assembly (leaf (e)): 2τ(e^{-τ}Δ − 1) = 2τe^{-2τ} + 2τP_τ + [remainder]; 2τP_τ → ∫₀¹φ₁φ₂ by
   M016MassCore.mass_limit_cover. No reality restriction, conjugation, or regularity hypothesis; no new hypothesis.
   Helper definitions (supporting only): kLow, kWrap. Route record: M016MASS_ROUTE.md.
   Own imports suffice (all names come through M016MassCore / M016DysonCore and their GK38 imports).
   Lane: the full text (MassCore + DysonCore + this body) is lane-checked as M016Asm_AS2_RUN05 (64e504d9, exit 0,
   axioms [propext, Classical.choice, Quot.sound]); this split file needs a ROOT MAIN PROBE after the two cores land. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M016AssemblyAux

open NlsGge.ThirdConsultation.M016MassAux NlsGge.ThirdConsultation.M016DysonAux

theorem cexp_mul (a b : ℝ) : (Real.exp a : ℂ) * (Real.exp b : ℂ) = (Real.exp (a + b) : ℂ) := by
  rw [← Complex.ofReal_mul, ← Real.exp_add]

theorem mem01 {s x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hs : s ∈ uIcc (0 : ℝ) x) : s ∈ Icc (0 : ℝ) 1 := by
  have := sub01 hx hs
  rwa [uIcc_of_le zero_le_one] at this

theorem dysonTerm_zero_eq (φ : PotPair) (τ : ℝ) :
    dysonTerm φ τ 0 = freeFundP (Complex.I * τ) := by simp [dysonTerm]

theorem N1_10 (φ : PotPair) (τ : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    dysonTerm φ τ 1 ⟨s, hs⟩ 1 0 = -Complex.I * (Real.exp (τ * s) : ℂ) *
      ∫ r in (0 : ℝ)..s, (Real.exp (-(2 * τ * (s - r))) : ℂ) * potRepSnd38 φ r := by
  rw [dysonTerm_succ φ τ 0, volterraP_entry_one, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun r hr => ?_
  have hr' := mem01 hs hr
  rw [ext38_of_mem _ hr', dysonTerm_zero_eq, (freeFundP_entries τ hr').1]
  have hx : (Real.exp (-(τ * (s - r))) : ℂ) * (Real.exp (τ * r) : ℂ) =
      (Real.exp (τ * s) : ℂ) * (Real.exp (-(2 * τ * (s - r))) : ℂ) := by
    rw [cexp_mul, cexp_mul]; congr 2; ring
  linear_combination (-(Complex.I * potRepSnd38 φ r)) * hx

theorem N1_01 (φ : PotPair) (τ : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    dysonTerm φ τ 1 ⟨s, hs⟩ 0 1 = Complex.I * (Real.exp (τ * s) : ℂ) *
      ∫ r in (0 : ℝ)..s, (Real.exp (-(2 * τ * r)) : ℂ) * potRepFst38 φ r := by
  rw [dysonTerm_succ φ τ 0, volterraP_entry_zero, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun r hr => ?_
  have hr' := mem01 hs hr
  rw [ext38_of_mem _ hr', dysonTerm_zero_eq, (freeFundP_entries τ hr').2.2.2]
  have hx : (Real.exp (τ * (s - r)) : ℂ) * (Real.exp (-(τ * r)) : ℂ) =
      (Real.exp (τ * s) : ℂ) * (Real.exp (-(2 * τ * r)) : ℂ) := by
    rw [cexp_mul, cexp_mul]; congr 2; ring
  linear_combination (Complex.I * potRepFst38 φ r) * hx

theorem N2_00 (φ : PotPair) (τ : ℝ) :
    dysonTerm φ τ 2 one01 0 0 = (Real.exp τ : ℂ) *
      ∫ s in (0 : ℝ)..1, potRepFst38 φ s *
        ∫ r in (0 : ℝ)..s, (Real.exp (-(2 * τ * (s - r))) : ℂ) * potRepSnd38 φ r := by
  have h2 : dysonTerm φ τ 2 = volterraP φ (Complex.I * τ) (dysonTerm φ τ 1) := dysonTerm_succ φ τ 1
  rw [h2]
  rw [show one01 = (⟨1, one01.2⟩ : Icc (0 : ℝ) 1) from rfl, volterraP_entry_zero,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s hs => ?_
  have hs' := mem01 one01.2 hs
  rw [ext38_of_mem _ hs', N1_10 φ τ hs']
  have hx : (Real.exp (τ * (1 - s)) : ℂ) * (Real.exp (τ * s) : ℂ) = (Real.exp τ : ℂ) := by
    rw [cexp_mul]; congr 2; ring
  set G := ∫ r in (0 : ℝ)..s, (Real.exp (-(2 * τ * (s - r))) : ℂ) * potRepSnd38 φ r
  linear_combination (potRepFst38 φ s * G) * hx +
    (-((Real.exp (τ * (1 - s)) : ℂ) * (Real.exp (τ * s) : ℂ) * potRepFst38 φ s * G)) * Complex.I_sq

theorem N2_11 (φ : PotPair) (τ : ℝ) :
    dysonTerm φ τ 2 one01 1 1 = (Real.exp τ : ℂ) *
      ∫ s in (0 : ℝ)..1, (Real.exp (-(2 * τ * (1 - s))) : ℂ) * potRepSnd38 φ s *
        ∫ r in (0 : ℝ)..s, (Real.exp (-(2 * τ * r)) : ℂ) * potRepFst38 φ r := by
  have h2 : dysonTerm φ τ 2 = volterraP φ (Complex.I * τ) (dysonTerm φ τ 1) := dysonTerm_succ φ τ 1
  rw [h2]
  rw [show one01 = (⟨1, one01.2⟩ : Icc (0 : ℝ) 1) from rfl, volterraP_entry_one,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s hs => ?_
  have hs' := mem01 one01.2 hs
  rw [ext38_of_mem _ hs', N1_01 φ τ hs']
  have hx : (Real.exp (-(τ * (1 - s))) : ℂ) * (Real.exp (τ * s) : ℂ) =
      (Real.exp τ : ℂ) * (Real.exp (-(2 * τ * (1 - s))) : ℂ) := by
    rw [cexp_mul, cexp_mul]; congr 2; ring
  set H := ∫ r in (0 : ℝ)..s, (Real.exp (-(2 * τ * r)) : ℂ) * potRepFst38 φ r
  linear_combination (potRepSnd38 φ s * H) * hx +
    (-((Real.exp (-(τ * (1 - s))) : ℂ) * (Real.exp (τ * s) : ℂ) * potRepSnd38 φ s * H)) *
      Complex.I_sq

/-! ### Second order: the kernel split on the product measure (triangular Fubini) -/

/-- Lower-triangle part of the kernel. -/
def kLow (τ : ℝ) (p : ℝ × ℝ) : ℂ :=
  if p.2 ≤ p.1 then (Real.exp (-(2 * τ * (p.1 - p.2))) : ℂ) else 0

/-- Wrap-around part of the kernel. -/
def kWrap (τ : ℝ) (p : ℝ × ℝ) : ℂ :=
  if p.2 ≤ p.1 then 0 else (Real.exp (-(2 * τ * (1 + p.1 - p.2))) : ℂ)

theorem pairW_split (τ : ℝ) (p : ℝ × ℝ) : (pairW τ p.1 p.2 : ℂ) = kLow τ p + kWrap τ p := by
  unfold pairW kLow kWrap
  split_ifs <;> simp

theorem norm_kLow_le (τ : ℝ) (p : ℝ × ℝ) : ‖kLow τ p‖ ≤ pairW τ p.1 p.2 := by
  unfold kLow pairW
  split_ifs
  · rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  · simpa using (Real.exp_pos _).le

theorem norm_kWrap_le (τ : ℝ) (p : ℝ × ℝ) : ‖kWrap τ p‖ ≤ pairW τ p.1 p.2 := by
  unfold kWrap pairW
  split_ifs
  · simpa using (Real.exp_pos _).le
  · rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

theorem measurable_kLow (τ : ℝ) : Measurable (kLow τ) := by
  unfold kLow
  exact Measurable.ite (measurableSet_le measurable_snd measurable_fst) (by fun_prop) measurable_const

theorem measurable_kWrap (τ : ℝ) : Measurable (kWrap τ) := by
  unfold kWrap
  exact Measurable.ite (measurableSet_le measurable_snd measurable_fst) measurable_const (by fun_prop)

/-- **Leaf (b).** `tr N₂(1) = e^τ · P_τ`, with `P_τ` exactly the mass-core double integral. -/
theorem trOne_two (φ : PotPair) (τ : ℝ) (hτ : 0 ≤ τ) :
    trOne (dysonTerm φ τ 2) = (Real.exp τ : ℂ) *
      ∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1,
        (pairW τ s r : ℂ) * NlsGge.GK38.coverRep38 φ.1 s * NlsGge.GK38.coverRep38 φ.2 r := by
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hμ
  obtain ⟨hI, hQ⟩ := Q_eq_prod τ hτ (memLp_coverRep38 φ.1) (memLp_coverRep38 φ.2)
  have hprod : μ.prod μ = (volume.prod volume).restrict (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) :=
    Measure.prod_restrict _ _
  have hW_ae : ∀ᵐ p ∂(μ.prod μ), pairW τ p.1 p.2 ≤ 1 := by
    rw [hprod]
    exact ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioc) fun p hp =>
      pairW_le_one hτ (Ioc_subset_Icc_self hp.1) (Ioc_subset_Icc_self hp.2)
  have hF : Integrable (fun p : ℝ × ℝ => NlsGge.GK38.coverRep38 φ.1 p.1 * NlsGge.GK38.coverRep38 φ.2 p.2) (μ.prod μ) :=
    ((memLp_coverRep38 φ.1).integrable one_le_two).mul_prod ((memLp_coverRep38 φ.2).integrable one_le_two)
  have hI1 : Integrable (fun p : ℝ × ℝ => kLow τ p * (NlsGge.GK38.coverRep38 φ.1 p.1 * NlsGge.GK38.coverRep38 φ.2 p.2)) (μ.prod μ) :=
    hF.bdd_mul (measurable_kLow τ).aestronglyMeasurable
      (hW_ae.mono fun p hp => (norm_kLow_le τ p).trans hp)
  have hI2 : Integrable (fun p : ℝ × ℝ => kWrap τ p * (NlsGge.GK38.coverRep38 φ.1 p.1 * NlsGge.GK38.coverRep38 φ.2 p.2)) (μ.prod μ) :=
    hF.bdd_mul (measurable_kWrap τ).aestronglyMeasurable
      (hW_ae.mono fun p hp => (norm_kWrap_le τ p).trans hp)
  -- the lower-triangle part, inner integral in `r`
  have hlow : ∫ p, kLow τ p * (NlsGge.GK38.coverRep38 φ.1 p.1 * NlsGge.GK38.coverRep38 φ.2 p.2) ∂(μ.prod μ) =
      ∫ s in (0 : ℝ)..1, NlsGge.GK38.coverRep38 φ.1 s *
        ∫ r in (0 : ℝ)..s, (Real.exp (-(2 * τ * (s - r))) : ℂ) * NlsGge.GK38.coverRep38 φ.2 r := by
    rw [integral_prod _ hI1, intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have e1 : (fun r => kLow τ (s, r) * (NlsGge.GK38.coverRep38 φ.1 s * NlsGge.GK38.coverRep38 φ.2 r)) =
        (Iic s).indicator (fun r => (Real.exp (-(2 * τ * (s - r))) : ℂ) * (NlsGge.GK38.coverRep38 φ.1 s * NlsGge.GK38.coverRep38 φ.2 r)) := by
      funext r
      by_cases h : r ≤ s <;> simp [kLow, Set.indicator, h]
    rw [e1, setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right hs.2,
      ← intervalIntegral.integral_of_le hs.1.le, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun r _ => by ring
  -- the wrap part, inner integral in `s`
  have hwrap : ∫ p, kWrap τ p * (NlsGge.GK38.coverRep38 φ.1 p.1 * NlsGge.GK38.coverRep38 φ.2 p.2) ∂(μ.prod μ) =
      ∫ r in (0 : ℝ)..1, (Real.exp (-(2 * τ * (1 - r))) : ℂ) * NlsGge.GK38.coverRep38 φ.2 r *
        ∫ s in (0 : ℝ)..r, (Real.exp (-(2 * τ * s)) : ℂ) * NlsGge.GK38.coverRep38 φ.1 s := by
    rw [integral_prod_symm _ hI2, intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    have e1 : (fun s => kWrap τ (s, r) * (NlsGge.GK38.coverRep38 φ.1 s * NlsGge.GK38.coverRep38 φ.2 r)) =
        (Iio r).indicator (fun s => (Real.exp (-(2 * τ * (1 + s - r))) : ℂ) * (NlsGge.GK38.coverRep38 φ.1 s * NlsGge.GK38.coverRep38 φ.2 r)) := by
      funext s
      by_cases h : r ≤ s
      · simp [kWrap, Set.indicator, h, not_lt.2 h]
      · simp [kWrap, Set.indicator, h, not_le.1 h]
    have e2 : Ioc (0 : ℝ) 1 ∩ Iio r = Ioo 0 r := by
      ext x
      simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
      constructor
      · intro h; exact ⟨h.1.1, h.2⟩
      · intro h; exact ⟨⟨h.1, by linarith [h.2, hr.2]⟩, h.2⟩
    rw [e1, setIntegral_indicator measurableSet_Iio, e2, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hr.1.le, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    have hx : (Real.exp (-(2 * τ * (1 + s - r))) : ℂ) =
        (Real.exp (-(2 * τ * (1 - r))) : ℂ) * (Real.exp (-(2 * τ * s)) : ℂ) := by
      rw [cexp_mul]; congr 2; ring
    rw [hx]; ring
  have hsplit : ∫ p, (pairW τ p.1 p.2 : ℂ) * (NlsGge.GK38.coverRep38 φ.1 p.1 * NlsGge.GK38.coverRep38 φ.2 p.2) ∂(μ.prod μ) =
      ∫ p, kLow τ p * (NlsGge.GK38.coverRep38 φ.1 p.1 * NlsGge.GK38.coverRep38 φ.2 p.2) ∂(μ.prod μ) +
        ∫ p, kWrap τ p * (NlsGge.GK38.coverRep38 φ.1 p.1 * NlsGge.GK38.coverRep38 φ.2 p.2) ∂(μ.prod μ) := by
    rw [← integral_add hI1 hI2]
    exact integral_congr_ae (Eventually.of_forall fun p => by
      first
        | (rw [pairW_split]; ring)
        | (simp only [Pi.add_apply]; rw [pairW_split]; ring))
  unfold trOne
  rw [N2_00, N2_11, hQ, hsplit, hlow, hwrap]
  simp only [potRepFst38, potRepSnd38]
  ring

end NlsGge.ThirdConsultation.M016AssemblyAux

namespace NlsGge.ThirdConsultation.M016AssemblyAux

open NlsGge.ThirdConsultation.M016MassAux NlsGge.ThirdConsultation.M016DysonAux

theorem ii_pW_snd (φ : PotPair) (τ : ℝ) (hτ : 0 ≤ τ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun r => pairW τ s r * ‖potRepSnd38 φ r‖) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine ((ii_snd φ).1).bdd_mul (c := 1)
    ((measurable_pairW τ).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => ?_)
  rw [Real.norm_of_nonneg (pairW_pos τ s r).le]
  exact pairW_le_one hτ hs (Ioc_subset_Icc_self hr)

theorem ii_pW_fst (φ : PotPair) (τ : ℝ) (hτ : 0 ≤ τ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun r => pairW τ r s * ‖potRepFst38 φ r‖) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine ((ii_fst φ).1).bdd_mul (c := 1)
    ((measurable_pairW τ).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => ?_)
  rw [Real.norm_of_nonneg (pairW_pos τ r s).le]
  exact pairW_le_one hτ (Ioc_subset_Icc_self hr) hs

/-- The Schur double integral of the absolute potentials, and its bound. -/
theorem schur_pot (φ : PotPair) (τ : ℝ) (hτ : 0 < τ) :
    Integrable (fun p : ℝ × ℝ => pairW τ p.1 p.2 * (‖potRepFst38 φ p.1‖ * ‖potRepSnd38 φ p.2‖))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) ∧
    ∫ p, pairW τ p.1 p.2 * (‖potRepFst38 φ p.1‖ * ‖potRepSnd38 φ p.2‖)
      ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) ≤
      (1 - Real.exp (-(2 * τ))) / (2 * τ) *
        (Real.sqrt (∫ s in Ioc (0 : ℝ) 1, ‖NlsGge.GK38.coverRep38 φ.1 s‖ ^ 2) *
          Real.sqrt (∫ r in Ioc (0 : ℝ) 1, ‖NlsGge.GK38.coverRep38 φ.2 r‖ ^ 2)) := by
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have hprod : μ.prod μ = (volume.prod volume).restrict (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) :=
    Measure.prod_restrict _ _
  have hW_ae : ∀ᵐ p ∂(μ.prod μ), ‖pairW τ p.1 p.2‖ ≤ 1 := by
    rw [hprod]
    refine ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioc) fun p hp => ?_
    rw [Real.norm_of_nonneg (pairW_pos _ _ _).le]
    exact pairW_le_one hτ.le (Ioc_subset_Icc_self hp.1) (Ioc_subset_Icc_self hp.2)
  have hI : Integrable (fun p : ℝ × ℝ => pairW τ p.1 p.2 * (‖potRepFst38 φ p.1‖ * ‖potRepSnd38 φ p.2‖))
      (μ.prod μ) :=
    ((((memLp_coverRep38 φ.1).norm).integrable one_le_two).mul_prod
      (((memLp_coverRep38 φ.2).norm).integrable one_le_two)).bdd_mul
      (measurable_pairW τ).aestronglyMeasurable hW_ae
  refine ⟨hI, ?_⟩
  have hs := schur_bound τ hτ (memLp_coverRep38 φ.1).norm (memLp_coverRep38 φ.2).norm
  refine le_of_eq_of_le ?_ hs
  rw [integral_prod _ hI]
  exact integral_congr_ae (Eventually.of_forall fun s => integral_congr_ae
    (Eventually.of_forall fun r => by simp only [potRepFst38, potRepSnd38]; ring))

/-- `A' ≤` the Schur double integral. -/
theorem majA_le_schur (φ : PotPair) (τ : ℝ) (hτ : 0 < τ) :
    majA φ τ ≤ ∫ p, pairW τ p.1 p.2 * (‖potRepFst38 φ p.1‖ * ‖potRepSnd38 φ p.2‖)
      ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hμ
  have hI := (schur_pot φ τ hτ).1
  rw [integral_prod _ hI]
  unfold majA
  rw [intervalIntegral.integral_of_le zero_le_one]
  refine integral_mono_of_nonneg (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs =>
    mul_nonneg (norm_nonneg _) (majK_nonneg φ τ hs.1.le)) hI.integral_prod_left
    (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_)
  have hsI : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hs
  have hK : majK φ τ s = ∫ r in (0 : ℝ)..s, pairW τ s r * ‖potRepSnd38 φ r‖ := by
    unfold majK
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hsI.1] at hr
    simp only [pairW, hr.2, ↓reduceIte]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2; ring
  have hle : majK φ τ s ≤ ∫ r in (0 : ℝ)..1, pairW τ s r * ‖potRepSnd38 φ r‖ := by
    rw [hK]
    exact intervalIntegral.integral_mono_interval le_rfl hsI.1 hsI.2
      (ae_restrict_of_forall_mem measurableSet_Ioc fun r _ =>
        mul_nonneg (pairW_pos τ s r).le (norm_nonneg _)) (ii_pW_snd φ τ hτ.le hsI)
  have hR : ∫ r, pairW τ s r * (‖potRepFst38 φ s‖ * ‖potRepSnd38 φ r‖) ∂μ =
      ‖potRepFst38 φ s‖ * ∫ r in (0 : ℝ)..1, pairW τ s r * ‖potRepSnd38 φ r‖ := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun r => by ring)
  dsimp only
  rw [hR]
  exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)

/-- `W(1) ≤` the Schur double integral (the cyclic pair, by `integral_prod_symm`). -/
theorem majW_le_schur (φ : PotPair) (τ : ℝ) (hτ : 0 < τ) :
    majW φ τ 1 ≤ ∫ p, pairW τ p.1 p.2 * (‖potRepFst38 φ p.1‖ * ‖potRepSnd38 φ p.2‖)
      ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hμ
  have hI := (schur_pot φ τ hτ).1
  rw [integral_prod_symm _ hI]
  have hW : majW φ τ 1 = ∫ s in (0 : ℝ)..1, ‖potRepSnd38 φ s‖ *
      ∫ r in (0 : ℝ)..s, pairW τ r s * ‖potRepFst38 φ r‖ := by
    unfold majW
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    have hin : ∫ r in (0 : ℝ)..s, pairW τ r s * ‖potRepFst38 φ r‖ =
        Real.exp (-(2 * τ * 1)) * Real.exp (2 * τ * s) * majJ φ τ s := by
      unfold majJ
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr_ae ((ae_ne_point s).mono fun r hne hr => ?_)
      rw [uIoc_of_le hs.1] at hr
      simp only [pairW, not_le.2 (lt_of_le_of_ne hr.2 hne), ↓reduceIte]
      rw [← mul_assoc, ← Real.exp_add, ← Real.exp_add]
      congr 2; ring
    rw [hin]; ring
  rw [hW, intervalIntegral.integral_of_le zero_le_one]
  refine integral_mono_of_nonneg (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs =>
    mul_nonneg (norm_nonneg _) (intervalIntegral.integral_nonneg hs.1.le fun r _ =>
      mul_nonneg (pairW_pos τ r s).le (norm_nonneg _))) hI.integral_prod_right
    (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_)
  have hsI : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hs
  have hle : ∫ r in (0 : ℝ)..s, pairW τ r s * ‖potRepFst38 φ r‖ ≤
      ∫ r in (0 : ℝ)..1, pairW τ r s * ‖potRepFst38 φ r‖ :=
    intervalIntegral.integral_mono_interval le_rfl hsI.1 hsI.2
      (ae_restrict_of_forall_mem measurableSet_Ioc fun r _ =>
        mul_nonneg (pairW_pos τ r s).le (norm_nonneg _)) (ii_pW_fst φ τ hτ.le hsI)
  have hR : ∫ r, pairW τ r s * (‖potRepFst38 φ r‖ * ‖potRepSnd38 φ s‖) ∂μ =
      ‖potRepSnd38 φ s‖ * ∫ r in (0 : ℝ)..1, pairW τ r s * ‖potRepFst38 φ r‖ := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun r => by ring)
  dsimp only
  rw [hR]
  exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)

/-- The `O(t^{-2})` remainder, multiplied by `2t`, tends to zero. -/
theorem remainder_tendsto (φ : PotPair) :
    Tendsto (fun t : ℝ => ((2 * t : ℝ) : ℂ) * ((Real.exp (-t) : ℂ) *
      (NlsGge.GK38.discrim φ (Complex.I * t) - ∑ k ∈ Finset.range 4, trOne (dysonTerm φ t k))))
      atTop (𝓝 0) := by
  set M : ℝ := Real.sqrt (∫ s in Ioc (0 : ℝ) 1, ‖NlsGge.GK38.coverRep38 φ.1 s‖ ^ 2) *
    Real.sqrt (∫ r in Ioc (0 : ℝ) 1, ‖NlsGge.GK38.coverRep38 φ.2 r‖ ^ 2) with hMdef
  have hM0 : 0 ≤ M := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hlim : Tendsto (fun t : ℝ => 2 * M ^ 2 / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (M + 1)] with t ht
  have ht0 : 0 < t := by linarith
  have hS := (schur_pot φ t ht0).2
  have hc : (1 - Real.exp (-(2 * t))) / (2 * t) * M ≤ M / (2 * t) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by nlinarith [Real.exp_pos (-(2 * t))]) (by positivity)
  have hA : majA φ t ≤ M / (2 * t) := (majA_le_schur φ t ht0).trans (hS.trans (by rw [← hMdef] at *; linarith))
  have hW : majW φ t 1 ≤ M / (2 * t) := (majW_le_schur φ t ht0).trans (hS.trans (by rw [← hMdef] at *; linarith))
  have hA0 := majA_nonneg φ t
  have hhalf : M / (2 * t) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) two_pos]; nlinarith
  have hA1 : majA φ t < 1 := by linarith
  have hrem := dyson_remainder_le φ t hA1
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le]
  have hfrac : majA φ t / (1 - majA φ t) ≤ M / t := by
    rw [div_le_div_iff₀ (by linarith) ht0]
    have : M / (2 * t) * t = M / 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right hA ht0.le]
  have hsum : majA φ t + majW φ t 1 ≤ M / t := by
    have : M / (2 * t) + M / (2 * t) = M / t := by field_simp; ring
    linarith
  have hexp : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  calc 2 * t * (Real.exp (-t) *
        ‖NlsGge.GK38.discrim φ (Complex.I * ↑t) - ∑ k ∈ Finset.range 4, trOne (dysonTerm φ t k)‖)
      ≤ 2 * t * (Real.exp (-t) * (Real.exp t * (majA φ t + majW φ t 1) *
          (majA φ t / (1 - majA φ t)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrem (Real.exp_pos _).le) (by positivity)
    _ = 2 * t * ((majA φ t + majW φ t 1) * (majA φ t / (1 - majA φ t))) := by
        rw [← mul_assoc (Real.exp (-t)), ← mul_assoc (Real.exp (-t)), hexp, one_mul]
    _ ≤ 2 * t * (M / t * (M / t)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hsum hfrac
          (div_nonneg hA0 (by linarith)) (by positivity)) (by positivity)
    _ = 2 * M ^ 2 / t := by
        field_simp
        try ring

end NlsGge.ThirdConsultation.M016AssemblyAux

namespace NlsGge.ThirdConsultation.M

open NlsGge.ThirdConsultation.M016MassAux NlsGge.ThirdConsultation.M016DysonAux
  NlsGge.ThirdConsultation.M016AssemblyAux

theorem discriminant_imaginary_bilinear_mass (φ : PotPair) :
    Filter.Tendsto
      (fun t : ℝ => ((2 * t : ℝ) : ℂ) *
        (Complex.exp (-(t : ℂ)) *
          NlsGge.GK38.discrim φ (Complex.I * (t : ℂ)) - 1))
      Filter.atTop
      (nhds (∫ x in (0 : ℝ)..1,
        NlsGge.GK38.coverRep38 φ.1 x *
          NlsGge.GK38.coverRep38 φ.2 x)) := by
  have hP := mass_limit_cover φ.1 φ.2
  have hE : Tendsto (fun t : ℝ => ((2 * t : ℝ) : ℂ) * (Real.exp (-(2 * t)) : ℂ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.const_mul_atTop (two_pos : (0 : ℝ) < 2))
    have h2 := (Complex.continuous_ofReal.tendsto 0).comp h
    rw [Complex.ofReal_zero] at h2
    refine h2.congr fun t => ?_
    simp only [Function.comp_apply, id, pow_one]
    push_cast
    try ring_nf
  have hR := remainder_tendsto φ
  have hsum := (hE.add hP).add hR
  rw [zero_add, add_zero] at hsum
  refine hsum.congr' ((eventually_gt_atTop 0).mono fun t ht => ?_)
  have h1 : trOne (dysonTerm φ t 1) = 0 := trOne_odd φ t 0
  have h3 : trOne (dysonTerm φ t 3) = 0 := trOne_odd φ t 1
  have hsig : ∑ k ∈ Finset.range 4, trOne (dysonTerm φ t k) =
      ((Real.exp t : ℂ) + (Real.exp (-t) : ℂ)) + (Real.exp t : ℂ) *
        ∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1,
          (pairW t s r : ℂ) * NlsGge.GK38.coverRep38 φ.1 s * NlsGge.GK38.coverRep38 φ.2 r := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
    rw [trOne_zero, trOne_two φ t ht.le, h1, h3]
    ring
  have hce : Complex.exp (-(t : ℂ)) = (Real.exp (-t) : ℂ) := by
    rw [Complex.ofReal_exp, Complex.ofReal_neg]
  have e1 : (Real.exp (-t) : ℂ) * (Real.exp t : ℂ) = 1 := by
    rw [cexp_mul]; simp
  have e2 : (Real.exp (-t) : ℂ) * (Real.exp (-t) : ℂ) = (Real.exp (-(2 * t)) : ℂ) := by
    rw [cexp_mul]; congr 2; ring
  set Pt := ∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1,
    (pairW t s r : ℂ) * NlsGge.GK38.coverRep38 φ.1 s * NlsGge.GK38.coverRep38 φ.2 r
  dsimp only
  rw [hsig, hce]
  linear_combination (-((2 * t : ℝ) : ℂ)) * (1 + Pt) * e1 + (-((2 * t : ℝ) : ℂ)) * e2

end NlsGge.ThirdConsultation.M

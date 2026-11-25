import Mathlib
import NlsGge.ThirdConsultation.G3.G3M12Support
import NlsGge.ThirdConsultation.G2.G2072Host
import NlsGge.Atomic.G2.G2021
import NlsGge.Atomic.G2.G2046
import NlsGge.GK38.IsolatingTopology
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G3.G3005Host

/- G3-005 SUPPORT S1 (proof development, AUTHOR; not self-reviewed; supporting module, NOT the G3-005 head).
   Integrability of the literal bank density `betaGapDensity` (Pro round 9, sec. 9, "Integrability of the
   literal density"). Body of betaGapDensity verbatim from root/gpt6pro_followup7 DEFINITIONS/G3.lean.md
   lines 68-72 (no other design name is declared here). Reuses landed: isolating_family38 (IsolatingTopology),
   g3m2_dom (G3M12Support, own-cut omitted domain), a5OmittedRoot_ne_zero38 / a5OmittedRoot_analytic38
   (XiSqOmittedRoot), p6PsiNumerator_joint_analytic38 (AbelianPsiNumerator), rootProduct (G2021), psi (G2072Host),
   gap (G2046), sourceFamily / sourceW / sourceF (SourceFamilyBasic).
   Route: on the closed gap segment the omitted-index product is nonzero (own cut omitted, other cuts avoided by
   the isolating discs), so psi/rootProduct is continuous and bounded there; the density equals
   (psi/rootProduct) * (2 sqrt(t(1-t)))^{-1} on (0,1), and (sqrt(t(1-t)))^{-1} is integrable on (0,1) because
   it is bounded by 2(t^{-1/2} + (1-t)^{-1/2}). Integrability is proved before any integral identity.
   This does NOT use the endpoint limit of G3-001. Hypotheses: only sourceW membership and gap ≠ 0. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g3005_rpow_neg_half_eq {t : ℝ} (ht : 0 < t) :
    t ^ (-(1 / 2 : ℝ)) = (Real.sqrt t)⁻¹ := by
  rw [Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]

/-- Pointwise majorant: (sqrt(t(1-t)))⁻¹ ≤ 2 (t^{-1/2} + (1-t)^{-1/2}) on (0,1). -/
theorem g3005_inv_sqrt_bound {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (Real.sqrt (t*(1-t)))⁻¹ ≤ 2 * (t ^ (-(1 / 2 : ℝ)) + (1 - t) ^ (-(1 / 2 : ℝ))) := by
  have hu : 0 < 1 - t := by linarith
  rw [g3005_rpow_neg_half_eq ht0, g3005_rpow_neg_half_eq hu]
  have ha : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hb : 0 < Real.sqrt (1-t) := Real.sqrt_pos.2 hu
  have ha2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have hb2 : Real.sqrt (1-t) ^ 2 = 1 - t := Real.sq_sqrt hu.le
  have hmul : Real.sqrt (t*(1-t)) = Real.sqrt t * Real.sqrt (1-t) := Real.sqrt_mul ht0.le _
  rw [hmul, mul_inv]
  have hsum : Real.sqrt t ^ 2 + Real.sqrt (1-t) ^ 2 = 1 := by rw [ha2, hb2]; ring
  rcases le_total (Real.sqrt (1-t)) (Real.sqrt t) with hba | hab
  · have h2a : 1 ≤ 2 * Real.sqrt t := by
      nlinarith [mul_nonneg (sub_nonneg.2 hba) (add_nonneg ha.le hb.le)]
    have hinv : (Real.sqrt t)⁻¹ ≤ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ ha]; linarith
    have h1 : (Real.sqrt t)⁻¹ * (Real.sqrt (1-t))⁻¹ ≤ 2 * (Real.sqrt (1-t))⁻¹ :=
      mul_le_mul_of_nonneg_right hinv (inv_nonneg.2 hb.le)
    nlinarith [inv_nonneg.2 ha.le]
  · have h2b : 1 ≤ 2 * Real.sqrt (1-t) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hab) (add_nonneg ha.le hb.le)]
    have hinv : (Real.sqrt (1-t))⁻¹ ≤ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ hb]; linarith
    have h1 : (Real.sqrt t)⁻¹ * (Real.sqrt (1-t))⁻¹ ≤ (Real.sqrt t)⁻¹ * 2 :=
      mul_le_mul_of_nonneg_left hinv (inv_nonneg.2 ha.le)
    nlinarith [inv_nonneg.2 hb.le, inv_nonneg.2 ha.le]

/-- (sqrt(t(1-t)))⁻¹ is integrable on (0,1). -/
theorem g3005_integrable_inv_sqrt :
    IntegrableOn (fun t : ℝ => (Real.sqrt (t*(1-t)))⁻¹) (Ioo (0:ℝ) 1) := by
  have h1 : IntervalIntegrable (fun t : ℝ => t ^ (-(1/2:ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h2 : IntervalIntegrable (fun t : ℝ => (1 - t) ^ (-(1/2:ℝ))) volume 0 1 := by
    have h := h1.comp_sub_left 1
    norm_num at h
    exact h.symm
  have hA : IntegrableOn (fun t : ℝ => t ^ (-(1/2:ℝ))) (Ioo (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 h1
  have hB : IntegrableOn (fun t : ℝ => (1 - t) ^ (-(1/2:ℝ))) (Ioo (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 h2
  have hcont : ContinuousOn (fun t : ℝ => (Real.sqrt (t*(1-t)))⁻¹) (Ioo (0:ℝ) 1) := by
    apply ContinuousOn.inv₀
    · exact (Real.continuous_sqrt.comp (continuous_id.mul (continuous_const.sub continuous_id))).continuousOn
    · intro t ht
      exact (Real.sqrt_pos.2 (mul_pos ht.1 (by linarith [ht.2]))).ne'
  refine Integrable.mono' ((hA.add hB).const_mul 2) (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => ?_)
  rw [Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  exact g3005_inv_sqrt_bound ht.1 ht.2

/-- The closed gap segment lies in the open disc of its own index. -/
theorem g3005_gap_mem (m : ℤ) (ψ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hspec : IsolatingSpectral38 ψ C R) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    lamMinus ψ m + (t:ℂ) * gap ψ m ∈ ball (C m) (R m) := by
  have hL : lamMinus ψ m ∈ ball (C m) (R m) := (hspec.1 m).1 (left_mem_segment ℝ _ _)
  have hR : lamPlus ψ m ∈ ball (C m) (R m) := (hspec.1 m).1 (right_mem_segment ℝ _ _)
  have h := (convex_ball (C m) (R m)).add_smul_sub_mem hL hR ht
  rw [Complex.real_smul] at h
  unfold gap
  exact h

/-- Continuity of the omitted root product along the gap segment of its own index. -/
theorem g3005_root_cont (m : ℤ) (φ : PotPair)
    (hdom : ∀ t ∈ Icc (0:ℝ) 1, (φ, lamMinus φ m + (t:ℂ) * gap φ m) ∈ a5OmittedRootDomain38 m) :
    ContinuousOn (fun t : ℝ => rootProduct m (φ, lamMinus φ m + (t:ℂ) * gap φ m)) (Icc 0 1) := by
  intro t ht
  have hz : Continuous (fun t : ℝ => lamMinus φ m + (t:ℂ) * gap φ m) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hp : Continuous (fun t : ℝ => ((φ, lamMinus φ m + (t:ℂ) * gap φ m) : PotPair × ℂ)) :=
    continuous_const.prodMk hz
  have hA := a5OmittedRoot_analytic38 m _ (hdom t ht)
  have hc : ContinuousAt (fun t : ℝ => a5OmittedRootProduct38 m (φ, lamMinus φ m + (t:ℂ) * gap φ m)) t :=
    ContinuousAt.comp (g := a5OmittedRootProduct38 m)
      (f := fun t : ℝ => ((φ, lamMinus φ m + (t:ℂ) * gap φ m) : PotPair × ℂ))
      hA.continuousAt hp.continuousAt
  unfold rootProduct
  exact (continuousAt_const.mul hc).continuousWithinAt

/-- Continuity of psi along the gap segment, from the joint analyticity on sourceW. -/
theorem g3005_psi_cont (n m : ℤ) (φ : PotPair) (hφ : φ ∈ sourceW) :
    ContinuousOn (fun t : ℝ => psi n φ (lamMinus φ m + (t:ℂ) * gap φ m)) (Icc 0 1) := by
  intro t _
  have hjoint := p6PsiNumerator_joint_analytic38 n sourceW (sourceF n) (sourceFamily.F_analytic n)
  have hz : Continuous (fun t : ℝ => lamMinus φ m + (t:ℂ) * gap φ m) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hp : Continuous (fun t : ℝ => ((φ, lamMinus φ m + (t:ℂ) * gap φ m) : PotPair × ℂ)) :=
    continuous_const.prodMk hz
  have hA := hjoint (φ, lamMinus φ m + (t:ℂ) * gap φ m) ⟨hφ, Set.mem_univ _⟩
  have hc : ContinuousAt (fun t : ℝ => p6PsiNumerator38 n (sourceF n) φ (lamMinus φ m + (t:ℂ) * gap φ m)) t :=
    ContinuousAt.comp (g := fun p : PotPair × ℂ => p6PsiNumerator38 n (sourceF n) p.1 p.2)
      (f := fun t : ℝ => ((φ, lamMinus φ m + (t:ℂ) * gap φ m) : PotPair × ℂ))
      hA.continuousAt hp.continuousAt
  exact hc.continuousWithinAt

/-- Density identity, after the convergent algebra 2i(-i g s) = 2 g s. -/
theorem g3005_density_eq (n m : ℤ) (φ : PotPair) (t : ℝ) (hg : gap φ m ≠ 0)
    (hs : 0 < t*(1-t))
    (hR : rootProduct m (φ, lamMinus φ m + (t:ℂ) * gap φ m) ≠ 0) :
    betaGapDensity n m φ t =
      (psi n φ (lamMinus φ m + (t:ℂ) * gap φ m) /
        rootProduct m (φ, lamMinus φ m + (t:ℂ) * gap φ m)) *
        ((2:ℂ) * (Real.sqrt (t*(1-t)) : ℂ))⁻¹ := by
  unfold betaGapDensity
  dsimp only
  have hsq : (Real.sqrt (t*(1-t)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hs).ne'
  have hden : (2 * Complex.I * (-Complex.I * gap φ m * (Real.sqrt (t*(1-t)) : ℂ))) =
      2 * gap φ m * (Real.sqrt (t*(1-t)) : ℂ) := by
    linear_combination (-2 * gap φ m * (Real.sqrt (t*(1-t)) : ℂ)) * Complex.I_sq
  rw [hden]
  field_simp

/-- **G3-005 support S1: integrability of the literal bank density.** No endpoint limit is used. -/
theorem g3005_bank_integrable (n m : ℤ) (φ : PotPair) (hφ : φ ∈ sourceW) (hgap : gap φ m ≠ 0) :
    IntervalIntegrable (betaGapDensity n m φ) volume 0 1 := by
  have hgk : φ ∈ gkW := sourceFamily.W_gk hφ
  obtain ⟨c, N, hg, hspec⟩ := isolating_family38 φ hgk
  have hdom : ∀ t ∈ Icc (0:ℝ) 1,
      (φ, lamMinus φ m + (t:ℂ) * gap φ m) ∈ a5OmittedRootDomain38 m := fun t ht =>
    g3m2_dom (m+1) m (by omega) (discC φ) (discR φ) c N hg φ hgk hspec _
      (g3005_gap_mem m φ (discC φ) (discR φ) hspec t ht)
  have hRne : ∀ t ∈ Icc (0:ℝ) 1, rootProduct m (φ, lamMinus φ m + (t:ℂ) * gap φ m) ≠ 0 := by
    intro t ht
    unfold rootProduct
    exact mul_ne_zero (inv_ne_zero (by exact_mod_cast Lib.piN_ne_zero m))
      (a5OmittedRoot_ne_zero38 m _ (hdom t ht))
  have hratioC : ContinuousOn
      (fun t : ℝ => psi n φ (lamMinus φ m + (t:ℂ) * gap φ m) /
        rootProduct m (φ, lamMinus φ m + (t:ℂ) * gap φ m)) (Icc 0 1) :=
    (g3005_psi_cont n m φ hφ).div (g3005_root_cont m φ hdom) hRne
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hratioC
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_refl _, zero_le_one⟩)
  -- continuity of the factorised density on (0,1)
  have hFc : ContinuousOn
      (fun t : ℝ => psi n φ (lamMinus φ m + (t:ℂ) * gap φ m) /
        rootProduct m (φ, lamMinus φ m + (t:ℂ) * gap φ m)) (Ioo 0 1) :=
    hratioC.mono Ioo_subset_Icc_self
  have hGc : ContinuousOn (fun t : ℝ => ((2:ℂ) * (Real.sqrt (t*(1-t)) : ℂ))⁻¹) (Ioo (0:ℝ) 1) := by
    apply ContinuousOn.inv₀
    · exact continuousOn_const.mul
        (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
          (continuous_id.mul (continuous_const.sub continuous_id)))).continuousOn
    · intro t ht
      have hs : 0 < t*(1-t) := mul_pos ht.1 (by linarith [ht.2])
      have hsq : (Real.sqrt (t*(1-t)) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.2 hs).ne'
      exact mul_ne_zero two_ne_zero hsq
  have hHint : IntegrableOn
      (fun t : ℝ => (psi n φ (lamMinus φ m + (t:ℂ) * gap φ m) /
        rootProduct m (φ, lamMinus φ m + (t:ℂ) * gap φ m)) *
        ((2:ℂ) * (Real.sqrt (t*(1-t)) : ℂ))⁻¹) (Ioo (0:ℝ) 1) := by
    refine Integrable.mono' (g := fun t : ℝ => M * (Real.sqrt (t*(1-t)))⁻¹)
      (g3005_integrable_inv_sqrt.const_mul M)
      ((hFc.mul hGc).aestronglyMeasurable measurableSet_Ioo) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => ?_)
    have hs : 0 < Real.sqrt (t*(1-t)) := Real.sqrt_pos.2 (mul_pos ht.1 (by linarith [ht.2]))
    have hG : ‖((2:ℂ) * (Real.sqrt (t*(1-t)) : ℂ))⁻¹‖ = (2 * Real.sqrt (t*(1-t)))⁻¹ := by
      rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
      norm_num
    have hGle : (2 * Real.sqrt (t*(1-t)))⁻¹ ≤ (Real.sqrt (t*(1-t)))⁻¹ :=
      inv_anti₀ hs (by linarith)
    have hF := hM t ⟨ht.1.le, ht.2.le⟩
    rw [norm_mul, hG]
    exact mul_le_mul hF hGle (by positivity) hM0
  have hEq : IntegrableOn (betaGapDensity n m φ) (Ioo (0:ℝ) 1) := by
    refine hHint.congr_fun (fun t ht => ?_) measurableSet_Ioo
    have hs : 0 < t*(1-t) := mul_pos ht.1 (by linarith [ht.2])
    have hIcc : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    exact (g3005_density_eq n m φ t hgap hs (hRne t hIcc)).symm
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hEq

end
end NlsGge.GKDefinitionDesign

import Mathlib
import NlsGge.GK38.PoissonSpectralModel
import NlsGge.GK38.DirichletRealReality
import NlsGge.GK38.DirichletRealAnalytic
import NlsGge.GK38.ActionGradientQuotient
import NlsGge.GK38.GradEigenKernels
import NlsGge.Atomic.G1.G1100Support
import NlsGge.Atomic.G1.G1081Host

                                                                                           
                                                                                                                             
                                                                                                                           
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.PoissonSpectral38
open NlsGge.GKDefinitionDesign
namespace NlsGge.Atomic.G1081Sup1
noncomputable section

theorem real_inner_eq_re_complex (x y : PhysicalL2) :
    @inner ℝ PhysicalL2 _ x y = (inner ℂ x y).re := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have hi := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) x y
  have := integral_re (𝕜 := ℂ) hi
  rw [RCLike.re_to_complex] at this
  simp only [RCLike.re_to_complex] at this
  rw [← this]
  apply integral_congr_ae
  filter_upwards with a
  exact real_inner_eq_re_inner (𝕜 := ℂ) _ _

theorem inner_eq_integral (x y : PhysicalL2) :
    inner ℂ x y = ∫ s in (0 : ℝ)..1, starRingEnd ℂ (coverRep38 x s) * coverRep38 y s := by
  have hint := NlsGge.Atomic.G1100Support.integrable_conj_mul x y
  have hre : (∫ s in (0 : ℝ)..1, starRingEnd ℂ (coverRep38 x s) * coverRep38 y s).re =
      ∫ s in (0 : ℝ)..1, (starRingEnd ℂ (coverRep38 x s) * coverRep38 y s).re :=
    (Complex.reCLM.intervalIntegral_comp_comm hint).symm
  have him : (∫ s in (0 : ℝ)..1, starRingEnd ℂ (coverRep38 x s) * coverRep38 y s).im =
      ∫ s in (0 : ℝ)..1, (starRingEnd ℂ (coverRep38 x s) * coverRep38 y s).im :=
    (Complex.imCLM.intervalIntegral_comp_comm hint).symm
  apply Complex.ext
  · rw [hre, ← NlsGge.Atomic.G1100Support.real_inner_eq_integral x y]
    exact (real_inner_eq_re_complex x y).symm
  · have h1 := NlsGge.Atomic.G1100Support.Bform_integral x y
    rw [NlsGge.Atomic.G1100Support.Bform_apply] at h1
    have h2 := real_inner_eq_re_complex (Complex.I • x) y
    rw [inner_smul_left] at h2
    rw [him, ← h1]
    refine Eq.trans ?_ h2.symm
    simp

theorem coverRep38_zero_ae' : ∀ᵐ t : ℝ, coverRep38 (0 : PhysicalL2) t = 0 := by
  filter_upwards [coverRep38_smul_ae (0 : ℂ) (0 : PhysicalL2)] with t ht
  simpa using ht

/-- Real-linear conjugate Riesz map: `ℓ ↦ star (toDual⁻¹ ℓ)`. -/
def rieszStarCL : (PhysicalL2 →L[ℂ] ℂ) →L[ℝ] PhysicalL2 :=
  LinearMap.mkContinuous
    { toFun := fun ℓ => starLp ((InnerProductSpace.toDual ℂ PhysicalL2).symm ℓ)
      map_add' := fun a b => by simp
      map_smul' := fun c ℓ => by
        have : (c • ℓ : PhysicalL2 →L[ℂ] ℂ) = (c : ℂ) • ℓ := by
          ext h; simp
        simp only [RingHom.id_apply]
        rw [this, LinearIsometryEquiv.map_smulₛₗ]
        simp
        exact starLp.map_smul c _ }
    1 (fun ℓ => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearIsometry.norm_map,
        LinearIsometryEquiv.norm_map, one_mul]
      exact le_rfl)

theorem rieszStarCL_apply_of_pairing (g : PhysicalL2) (ℓ : PhysicalL2 →L[ℂ] ℂ)
    (hℓ : ∀ h : PhysicalL2, ℓ h = ∫ s in (0 : ℝ)..1, coverRep38 g s * coverRep38 h s) :
    rieszStarCL ℓ = g := by
  have hw : (InnerProductSpace.toDual ℂ PhysicalL2).symm ℓ = star g := by
    apply ext_inner_right ℂ
    intro h
    rw [InnerProductSpace.toDual_symm_apply, hℓ h, inner_eq_integral]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [coverRep38_star_ae g] with s hs _
    rw [hs]; simp
  change starLp ((InnerProductSpace.toDual ℂ PhysicalL2).symm ℓ) = g
  rw [hw]
  exact star_star g

theorem ae_Ioc_of_Icc {p : ℝ → Prop}
    (h : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) 1)), p s) :
    ∀ᵐ s : ℝ, s ∈ Ioc (0 : ℝ) 1 → p s := by
  rw [← restrict_Ioc_eq_restrict_Icc] at h
  exact (ae_restrict_iff' measurableSet_Ioc).1 h

def rieszPair : (PotPair →L[ℂ] ℂ) →L[ℝ] PotPair :=
  (rieszStarCL.comp (((ContinuousLinearMap.compL ℂ PhysicalL2 PotPair ℂ).flip
      (ContinuousLinearMap.inl ℂ PhysicalL2 PhysicalL2)).restrictScalars ℝ)).prod
    (rieszStarCL.comp (((ContinuousLinearMap.compL ℂ PhysicalL2 PotPair ℂ).flip
      (ContinuousLinearMap.inr ℂ PhysicalL2 PhysicalL2)).restrictScalars ℝ))

theorem gradDiscrimL2_eq_rieszPair (φ : PotPair) (z : ℂ) :
    gradDiscrimL2 φ z = rieszPair (gradDiscrimCLM φ z) := by
  apply Prod.ext
  · refine (rieszStarCL_apply_of_pairing _ _ ?_).symm
    intro h
    change gradDiscrimCLM φ z (h, 0) = _
    rw [gradDiscrimCLM_apply]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_Ioc_of_Icc (gradDiscrimL2_rep φ z), coverRep38_zero_ae'] with s hs hz hm
    have hm' : s ∈ Ioc (0 : ℝ) 1 := by rwa [Set.uIoc_of_le zero_le_one] at hm
    have h1 : coverRep38 (gradDiscrimL2 φ z).1 s = gradDiscrim38 φ z s 0 := (hs hm').1
    simp only [potRepFst38, potRepSnd38]
    rw [h1, hz]; ring
  · refine (rieszStarCL_apply_of_pairing _ _ ?_).symm
    intro h
    change gradDiscrimCLM φ z (0, h) = _
    rw [gradDiscrimCLM_apply]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_Ioc_of_Icc (gradDiscrimL2_rep φ z), coverRep38_zero_ae'] with s hs hz hm
    have hm' : s ∈ Ioc (0 : ℝ) 1 := by rwa [Set.uIoc_of_le zero_le_one] at hm
    have h1 : coverRep38 (gradDiscrimL2 φ z).2 s = gradDiscrim38 φ z s 1 := (hs hm').2
    simp only [potRepFst38, potRepSnd38]
    rw [h1, hz]; ring

theorem analyticOnNhd_gradDiscrimL2 :
    AnalyticOnNhd ℝ (fun p : PotPair × ℂ => gradDiscrimL2 p.1 p.2) univ := by
  have he : (fun p : PotPair × ℂ => gradDiscrimL2 p.1 p.2) =
      fun p : PotPair × ℂ => rieszPair (gradDiscrimCLM p.1 p.2) := by
    funext p; exact gradDiscrimL2_eq_rieszPair p.1 p.2
  rw [he]
  intro p hp
  exact (rieszPair.analyticAt _).comp
    ((NlsGge.GK38.ActionGradient.gradDiscrim_joint_analytic p hp).restrictScalars)

/-- Multiplication by `-I` as a real-linear map. -/
def negIMul : PhysicalL2 →L[ℝ] PhysicalL2 :=
  ((-Complex.I) • ContinuousLinearMap.id ℂ PhysicalL2).restrictScalars ℝ

theorem singleGapField_eq (n : ℤ) (u : PhysicalL2) :
    singleGapField n u =
      negIMul (gradDiscrimL2 (realSlice u) ((gkMu u n : ℝ) : ℂ)).2 := rfl

theorem analyticOnNhd_singleGapField (n : ℤ) :
    AnalyticOnNhd ℝ (singleGapField n) univ := by
  intro u _
  have e : singleGapField n = fun v : PhysicalL2 =>
      negIMul ((fun p : PotPair × ℂ => gradDiscrimL2 p.1 p.2)
        (realSlice v, ((gkMu v n : ℝ) : ℂ))).2 := by
    funext v; exact singleGapField_eq n v
  rw [e]
  have h1 : AnalyticAt ℝ (fun v : PhysicalL2 => (realSlice v, ((gkMu v n : ℝ) : ℂ))) u :=
    (realSlice.analyticAt u).prod
      (Complex.ofRealCLM.analyticAt _ |>.comp (NlsGge.GK38.analyticAt_gkMu38 u n))
  have hg : AnalyticAt ℝ (fun p : PotPair × ℂ => gradDiscrimL2 p.1 p.2)
      (realSlice u, ((gkMu u n : ℝ) : ℂ)) :=
    analyticOnNhd_gradDiscrimL2 _ (mem_univ _)
  have h2 : AnalyticAt ℝ (fun v : PhysicalL2 => gradDiscrimL2 (realSlice v) ((gkMu v n : ℝ) : ℂ)) u :=
    AnalyticAt.comp (g := fun p : PotPair × ℂ => gradDiscrimL2 p.1 p.2)
      (f := fun v : PhysicalL2 => (realSlice v, ((gkMu v n : ℝ) : ℂ))) hg h1
  have h3 : AnalyticAt ℝ (fun v : PhysicalL2 => (gradDiscrimL2 (realSlice v) ((gkMu v n : ℝ) : ℂ)).2) u :=
    AnalyticAt.comp (g := ⇑(ContinuousLinearMap.snd ℝ PhysicalL2 PhysicalL2))
      (f := fun v : PhysicalL2 => gradDiscrimL2 (realSlice v) ((gkMu v n : ℝ) : ℂ))
      ((ContinuousLinearMap.snd ℝ PhysicalL2 PhysicalL2).analyticAt _) h2
  exact AnalyticAt.comp (g := ⇑negIMul)
    (f := fun v : PhysicalL2 => (gradDiscrimL2 (realSlice v) ((gkMu v n : ℝ) : ℂ)).2)
    (negIMul.analyticAt _) h3

theorem locallyLipschitz_singleGapField (n : ℤ) :
    ∀ u : PhysicalL2, ∃ K : NNReal, ∃ s ∈ 𝓝 u, LipschitzOnWith K (singleGapField n) s := by
  intro u
  have hc : ContDiffAt ℝ 1 (singleGapField n) u :=
    (analyticOnNhd_singleGapField n u (mem_univ _)).contDiffAt
  obtain ⟨K, s, hs, hK⟩ := hc.exists_lipschitzOnWith
  exact ⟨K, s, hs, hK⟩

theorem locallyLipschitzOn_singleGapField (n : ℤ) :
    LocallyLipschitzOn (univ : Set PhysicalL2) (singleGapField n) := by
  intro u _
  obtain ⟨K, s, hs, hK⟩ := locallyLipschitz_singleGapField n u
  exact ⟨K, s, by rwa [nhdsWithin_univ], hK⟩

end
end NlsGge.Atomic.G1081Sup1

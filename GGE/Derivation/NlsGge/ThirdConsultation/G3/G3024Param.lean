import Mathlib
import NlsGge.ThirdConsultation.G3.G3024Transport
import NlsGge.ThirdConsultation.G3.G3015Support
import NlsGge.ThirdConsultation.G3.G3006Host
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G2.G2072Host
import NlsGge.ThirdConsultation.G2.G2073Support1
import NlsGge.Atomic.G2.G2021
import NlsGge.Atomic.G2.G2075
import NlsGge.Atomic.G3.G3005
import NlsGge.Atomic.G3.G3014
import NlsGge.Atomic.G4.G4012

/- G3-024 SUPPORT M2 (diagonal analytic parameter integral) (proof development, AUTHOR; not semantically reviewed by its author).
   Target NlsGge/ThirdConsultation/G3/G3024Param.lean (proposed), namespace NlsGge.GKDefinitionDesign.G3024Param.
   Diagonal analogue of landed G3015Aux.local_data / analytic_of_local (NlsGge/Atomic/G3/G3015.lean) with m = n and integrand
   G = psi*rw/(2 I rootProduct n (phi,z) rs) (no betaZeta factor):  labels from landed G3015Aux.labels (G3013), roots from landed G3_014,
   joint continuity + tube lemma for a uniform bound C, analyticity in phi from joint analyticity of psi and rootProduct,
   G4-012 analyticOn_integral_of_rpow_half_locally_dominated with majorant C t^(-1/2).  M1 (G3024Transport) gives
   Z+ = (b-a) exp(I int ...) pointwise on V.  Final corollary g3024_nonE_lift is the non-endpoint case of the hlift of G3024Red:
   exp(I e) = +-etaExponential for an analytic e on a neighbourhood inside sourceBetaW \ collapsedSet n (phi0 not in endpointSet n).
   No analytic anchor (gk16_same_family_scalar_models_analytic38, gkSourceBeta_analytic38, XY_analytic) is used. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G3024Param
noncomputable section

theorem diag_local_data (n : ℤ) :
  ∀ φ0 ∈ sourceW \ (collapsedSet n ∪ endpointSet n),
    ∃ V : Set PotPair, ∃ a b rω : PotPair → ℂ,
    ∃ rseg : PotPair → ℝ → ℂ, ∃ C : ℝ,
      φ0 ∈ V ∧ LocalEndpointSegmentSeparation n V a b ∧
      AnalyticSegmentRoots n V a b rω rseg ∧ 0 < C ∧
      let G : PotPair → ℝ → ℂ := fun φ t =>
        let z := a φ+(t : ℂ)*(muSeq φ n-a φ)
        psi n φ z * rω φ / (2 * Complex.I * rootProduct n (φ, z) * rseg φ t)
      (∀ t ∈ Ioo (0 : ℝ) 1, AnalyticOnNhd ℂ (fun φ => G φ t) V) ∧
      (∀ φ ∈ V, ContinuousOn (G φ) (Icc (0 : ℝ) 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ‖G φ t‖ ≤ C) ∧
        IntervalIntegrable (fun t => G φ t/(Real.sqrt t : ℂ)) volume 0 1 ∧
        gk16ActualScalarZPlus38 sourceF n φ = (b φ - a φ) *
          Complex.exp (Complex.I * ∫ t in (0 : ℝ)..1, G φ t/(Real.sqrt t : ℂ))) := by
  intro φ0 hφ0
  obtain ⟨V1, a, b, hφV1, hsep⟩ := G3015Aux.labels n φ0 hφ0
  obtain ⟨U, rω, rseg, hUo, hφU, hUV1, hroots⟩ := G3_014 n V1 a b hsep φ0 hφV1
  have hsepU : LocalEndpointSegmentSeparation n U a b := G3015Aux.sep_mono n hsep hUo hUV1
  obtain ⟨-, hUsub, haA, hbA, hUp⟩ := hsepU
  obtain ⟨hrωA, hrsegA, hrsegC, hall⟩ := hroots
  have hUW : ∀ φ ∈ U, φ ∈ sourceW := fun φ hφ => (hUsub hφ).1
  have hUgk : ∀ φ ∈ U, φ ∈ gkW := fun φ hφ => sourceFamily.W_gk (hUW φ hφ)
  have hγ : ∀ φ ∈ U, lamPlus φ n - lamMinus φ n ≠ 0 := fun φ hφ =>
    G3015Aux.gap_ne_of_mem n φ (hUsub hφ)
  have hμA : ∀ φ ∈ U, AnalyticAt ℂ (fun ψ : PotPair => muSeq ψ n) φ := fun φ hφ =>
    analyticOnNhd_muSeq_complex38 n φ (hUgk φ hφ)
  have hpsiJ : AnalyticOnNhd ℂ (fun p : PotPair × ℂ => psi n p.1 p.2) (sourceW ×ˢ (univ : Set ℂ)) :=
    G2_075.2.2.2.1 n
  have hrPJ : AnalyticOnNhd ℂ (rootProduct n) (a5OmittedRootDomain38 n) := (G2_021 n).2.1
  have hrPN : ∀ p ∈ a5OmittedRootDomain38 n, rootProduct n p ≠ 0 := (G2_021 n).2.2
  obtain ⟨G, hG⟩ : ∃ G : PotPair → ℝ → ℂ, ∀ φ t, G φ t =
      psi n φ (a φ + (t : ℂ) * (muSeq φ n - a φ)) * rω φ /
        (2 * Complex.I * rootProduct n (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) * rseg φ t) :=
    ⟨fun φ t => psi n φ (a φ + (t : ℂ) * (muSeq φ n - a φ)) * rω φ /
        (2 * Complex.I * rootProduct n (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) * rseg φ t),
      fun _ _ => rfl⟩
  have hzball : ∀ φ ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
      a φ + (t : ℂ) * (muSeq φ n - a φ) ∈ ball (discC φ n) (discR φ n) :=
    fun φ hφ t ht => G3015Aux.seg_mem_ball n φ (hUgk φ hφ) (a φ) (b φ) (hUp φ hφ).1 t ht
  have hdom : ∀ φ ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
      (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) ∈ a5OmittedRootDomain38 n := fun φ hφ t ht =>
    ⟨hUgk φ hφ, fun k hk => closedBall_avoids_other_gaps φ (hUgk φ hφ) n k hk _
      (ball_subset_closedBall (hzball φ hφ t ht))⟩
  have hrP0 : ∀ φ ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
      rootProduct n (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) ≠ 0 := fun φ hφ t ht =>
    hrPN _ (hdom φ hφ t ht)
  have hden : ∀ φ ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
      2 * Complex.I * rootProduct n (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) * rseg φ t ≠ 0 :=
    fun φ hφ t ht => mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
      (hrP0 φ hφ t ht)) (((hall φ hφ).2.2.1 t ht).1)
  -- joint continuity of G on U × [0,1]
  have hμC : ContinuousOn (fun ψ : PotPair => muSeq ψ n) U :=
    fun φ hφ => (hμA φ hφ).continuousAt.continuousWithinAt
  have hSt : ∀ p ∈ U ×ˢ Icc (0 : ℝ) 1, p.1 ∈ U := fun p hp => hp.1
  have hzzC : ContinuousOn (fun p : PotPair × ℝ => a p.1 + (p.2 : ℂ) * (muSeq p.1 n - a p.1))
      (U ×ˢ Icc (0 : ℝ) 1) := by
    have ha_c : ContinuousOn (fun p : PotPair × ℝ => a p.1) (U ×ˢ Icc (0 : ℝ) 1) :=
      haA.continuousOn.comp continuousOn_fst hSt
    have hm_c : ContinuousOn (fun p : PotPair × ℝ => muSeq p.1 n) (U ×ˢ Icc (0 : ℝ) 1) :=
      hμC.comp continuousOn_fst hSt
    exact ha_c.add ((Complex.continuous_ofReal.comp_continuousOn continuousOn_snd).mul
      (hm_c.sub ha_c))
  have hmaps : MapsTo (fun p : PotPair × ℝ => (p.1, a p.1 + (p.2 : ℂ) * (muSeq p.1 n - a p.1)))
      (U ×ˢ Icc (0 : ℝ) 1) (a5OmittedRootDomain38 n) := fun p hp => hdom p.1 hp.1 p.2 hp.2
  have hGc : ContinuousOn (fun p : PotPair × ℝ => G p.1 p.2) (U ×ˢ Icc (0 : ℝ) 1) := by
    have hpsi : ContinuousOn (fun p : PotPair × ℝ =>
        psi n p.1 (a p.1 + (p.2 : ℂ) * (muSeq p.1 n - a p.1))) (U ×ˢ Icc (0 : ℝ) 1) :=
      ContinuousOn.comp (g := fun q : PotPair × ℂ => psi n q.1 q.2)
        (f := fun p : PotPair × ℝ => (p.1, a p.1 + (p.2 : ℂ) * (muSeq p.1 n - a p.1)))
        hpsiJ.continuousOn (continuousOn_fst.prodMk hzzC)
        (fun p hp => ⟨hUW p.1 hp.1, mem_univ _⟩)
    have hrP : ContinuousOn (fun p : PotPair × ℝ =>
        rootProduct n (p.1, a p.1 + (p.2 : ℂ) * (muSeq p.1 n - a p.1)))
        (U ×ˢ Icc (0 : ℝ) 1) :=
      ContinuousOn.comp (g := rootProduct n)
        (f := fun p : PotPair × ℝ => (p.1, a p.1 + (p.2 : ℂ) * (muSeq p.1 n - a p.1)))
        hrPJ.continuousOn (continuousOn_fst.prodMk hzzC) hmaps
    have hω : ContinuousOn (fun p : PotPair × ℝ => rω p.1) (U ×ˢ Icc (0 : ℝ) 1) :=
      hrωA.continuousOn.comp continuousOn_fst hSt
    have hnum := (hpsi.mul hω)
    have hc2 : ContinuousOn (fun _ : PotPair × ℝ => (2 * Complex.I)) (U ×ˢ Icc (0 : ℝ) 1) :=
      continuousOn_const
    have hdenC := ((hc2.mul hrP).mul hrsegC)
    have := hnum.div hdenC (fun p hp => hden p.1 hp.1 p.2 hp.2)
    refine this.congr (fun p _ => ?_)
    exact hG p.1 p.2
  -- uniform bound by the tube lemma
  obtain ⟨K, hK⟩ := (isCompact_singleton (x := φ0)).prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    |>.exists_bound_of_continuousOn (hGc.mono (by
      rintro ⟨φ, t⟩ ⟨hφ, ht⟩
      rw [mem_singleton_iff] at hφ
      subst hφ
      exact ⟨hφU, ht⟩))
  obtain ⟨cl, hcl⟩ : ∃ cl : ℝ → ℝ, cl = fun t => max 0 (min t 1) := ⟨_, rfl⟩
  have hclc : Continuous cl := by rw [hcl]; fun_prop
  have hcl_mem : ∀ t, cl t ∈ Icc (0 : ℝ) 1 := fun t => by
    rw [hcl]; exact ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hcl_id : ∀ t ∈ Icc (0 : ℝ) 1, cl t = t := fun t ht => by
    rw [hcl]; simp only [min_eq_left ht.2, max_eq_right ht.1]
  have hG'c : ContinuousOn (fun p : PotPair × ℝ => G p.1 (cl p.2)) (U ×ˢ (univ : Set ℝ)) :=
    hGc.comp (continuousOn_fst.prodMk (hclc.comp continuous_snd).continuousOn)
      (fun p hp => ⟨hp.1, hcl_mem _⟩)
  have hopen : IsOpen ((U ×ˢ (univ : Set ℝ)) ∩
      (fun p : PotPair × ℝ => ‖G p.1 (cl p.2)‖) ⁻¹' Iio (K + 1)) :=
    ContinuousOn.isOpen_inter_preimage hG'c.norm (hUo.prod isOpen_univ) isOpen_Iio
  have hsub : ({φ0} : Set PotPair) ×ˢ Icc (0 : ℝ) 1 ⊆ ((U ×ˢ (univ : Set ℝ)) ∩
      (fun p : PotPair × ℝ => ‖G p.1 (cl p.2)‖) ⁻¹' Iio (K + 1)) := by
    rintro ⟨φ, t⟩ ⟨hφ, ht⟩
    rw [mem_singleton_iff] at hφ
    subst hφ
    refine ⟨⟨hφU, mem_univ _⟩, ?_⟩
    simp only [mem_preimage, mem_Iio]
    rw [hcl_id t ht]
    linarith [hK (φ, t) ⟨rfl, ht⟩]
  obtain ⟨u, v, huo, hvo, hφu, hIv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hopen hsub
  have hφ0u : φ0 ∈ u := singleton_subset_iff.1 hφu
  have huU : u ⊆ U := fun φ hφ =>
    (huv (show (φ, (0 : ℝ)) ∈ u ×ˢ v from ⟨hφ, hIv ⟨le_refl _, zero_le_one⟩⟩)).1.1
  have hbd : ∀ φ ∈ u, ∀ t ∈ Icc (0 : ℝ) 1, ‖G φ t‖ < K + 1 := by
    intro φ hφ t ht
    have h := (huv (show (φ, t) ∈ u ×ˢ v from ⟨hφ, hIv ht⟩)).2
    simp only [mem_preimage, mem_Iio] at h
    rwa [hcl_id t ht] at h
  have hC : 0 < max K 0 + 1 := by positivity
  refine ⟨u, a, b, rω, rseg, max K 0 + 1, hφ0u, G3015Aux.sep_mono n hsep huo (huU.trans hUV1),
    G3015Aux.roots_mono n ⟨hrωA, hrsegA, hrsegC, hall⟩ huU, hC, ?_⟩
  intro H
  have hHH : H = G := by
    funext φ t
    exact (hG φ t).symm
  rw [hHH]
  have hbound : ∀ φ ∈ u, ∀ t ∈ Icc (0 : ℝ) 1, ‖G φ t‖ ≤ max K 0 + 1 := by
    intro φ hφ t ht
    have := hbd φ hφ t ht
    have h2 : K + 1 ≤ max K 0 + 1 := by linarith [le_max_left K 0]
    linarith
  have hcont : ∀ φ ∈ u, ContinuousOn (G φ) (Icc (0 : ℝ) 1) := by
    intro φ hφ
    exact hGc.comp (continuousOn_const.prodMk continuousOn_id)
        (fun t ht => ⟨huU hφ, ht⟩)
  refine ⟨?_, fun φ hφ => ?_⟩
  · intro t ht
    have htc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    intro φ hφ
    have hφU' : φ ∈ U := huU hφ
    have hzA : AnalyticAt ℂ (fun ψ : PotPair => a ψ + (t : ℂ) * (muSeq ψ n - a ψ)) φ :=
      (haA φ hφU').add (analyticAt_const.mul ((hμA φ hφU').sub (haA φ hφU')))
    have hpair : AnalyticAt ℂ (fun ψ : PotPair => (ψ, a ψ + (t : ℂ) * (muSeq ψ n - a ψ))) φ :=
      analyticAt_id.prod hzA
    have hpsi : AnalyticAt ℂ (fun ψ : PotPair =>
        psi n ψ (a ψ + (t : ℂ) * (muSeq ψ n - a ψ))) φ :=
      AnalyticAt.comp (g := fun p : PotPair × ℂ => psi n p.1 p.2)
        (f := fun ψ : PotPair => (ψ, a ψ + (t : ℂ) * (muSeq ψ n - a ψ)))
        (hpsiJ (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) ⟨hUW φ hφU', mem_univ _⟩) hpair
    have hrP : AnalyticAt ℂ (fun ψ : PotPair =>
        rootProduct n (ψ, a ψ + (t : ℂ) * (muSeq ψ n - a ψ))) φ :=
      AnalyticAt.comp (g := rootProduct n)
        (f := fun ψ : PotPair => (ψ, a ψ + (t : ℂ) * (muSeq ψ n - a ψ)))
        (hrPJ _ (hdom φ hφU' t htc)) hpair
    have := (hpsi.mul (hrωA φ hφU')).div
      ((analyticAt_const.mul hrP).mul (hrsegA t htc φ hφU')) (hden φ hφU' t htc)
    exact this.congr (Filter.Eventually.of_forall fun ψ => (hG ψ t).symm)
  · have hφU' : φ ∈ U := huU hφ
    have hint : IntervalIntegrable (fun t : ℝ => G φ t / (Real.sqrt t : ℂ)) volume 0 1 :=
      G3015Aux.integrable_of_bound (G φ) _ (hcont φ hφ) (hbound φ hφ)
    refine ⟨hcont φ hφ, hbound φ hφ, hint, ?_⟩
    obtain ⟨hω0, hωsq, hseg, hsign⟩ := hall φ hφU'
    have hρc : ContinuousOn (rseg φ) (Icc (0 : ℝ) 1) :=
      hrsegC.comp (continuousOn_const.prodMk continuousOn_id) (fun t ht => ⟨hφU', ht⟩)
    simp only [hG] at hint ⊢
    exact G3024Transport.g3024_segment_exponential n φ (hUW φ hφU') (hγ φ hφU') (a φ) (b φ)
      (rω φ) (rseg φ) (hUp φ hφU').1 hω0 hωsq hρc (fun t ht => (hseg t ht).1)
      (fun t ht => (hseg t ht).2) hsign hint

theorem g3024_diag_package (n : ℤ) (φ0 : PotPair)
    (hφ0 : φ0 ∈ sourceW \ (collapsedSet n ∪ endpointSet n)) :
    ∃ V : Set PotPair, ∃ a b rω : PotPair → ℂ, ∃ rseg : PotPair → ℝ → ℂ,
      φ0 ∈ V ∧ LocalEndpointSegmentSeparation n V a b ∧
      AnalyticSegmentRoots n V a b rω rseg ∧
      AnalyticOnNhd ℂ (fun φ : PotPair => ∫ t in (0 : ℝ)..1,
        (psi n φ (a φ + (t : ℂ) * (muSeq φ n - a φ)) * rω φ /
          (2 * Complex.I * rootProduct n (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) * rseg φ t)) /
          (Real.sqrt t : ℂ)) V ∧
      ∀ φ ∈ V, gk16ActualScalarZPlus38 sourceF n φ = (b φ - a φ) * Complex.exp (Complex.I *
        ∫ t in (0 : ℝ)..1,
          (psi n φ (a φ + (t : ℂ) * (muSeq φ n - a φ)) * rω φ /
            (2 * Complex.I * rootProduct n (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) * rseg φ t)) /
            (Real.sqrt t : ℂ)) := by
  obtain ⟨V, a, b, rω, rseg, C, hφV, hsep, hroots, hC, hH⟩ := diag_local_data n φ0 hφ0
  obtain ⟨hHan, hHφ⟩ := hH
  have hVo : IsOpen V := hsep.1
  obtain ⟨Gf, hGf⟩ : ∃ Gf : PotPair → ℝ → ℂ, Gf = fun (φ : PotPair) (t : ℝ) =>
      psi n φ (a φ + (t : ℂ) * (muSeq φ n - a φ)) * rω φ /
        (2 * Complex.I * rootProduct n (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) * rseg φ t) :=
    ⟨_, rfl⟩
  have hHan' : ∀ t ∈ Ioo (0 : ℝ) 1, AnalyticOnNhd ℂ (fun φ => Gf φ t) V := by
    subst hGf; exact hHan
  have hHφ' : ∀ φ ∈ V, ContinuousOn (Gf φ) (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ‖Gf φ t‖ ≤ C) ∧
      IntervalIntegrable (fun t => Gf φ t / (Real.sqrt t : ℂ)) volume 0 1 ∧
      gk16ActualScalarZPlus38 sourceF n φ = (b φ - a φ) *
        Complex.exp (Complex.I * ∫ t in (0 : ℝ)..1, Gf φ t / (Real.sqrt t : ℂ)) := by
    subst hGf; exact hHφ
  have hmain := NlsGge.Atomic.G4.analyticOn_integral_of_rpow_half_locally_dominated
    (E := PotPair) (F := ℂ) (U := V)
    (a := fun (t : ℝ) (φ : PotPair) => Gf φ t / (Real.sqrt t : ℂ)) C hC.le hVo
    ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t ht φ hφ =>
      (hHan' t ht φ hφ).div analyticAt_const
        (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne')))
    (fun φ hφ => by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
      refine ((hHφ' φ hφ).1.mono Ioo_subset_Icc_self).div
        (Complex.continuous_ofReal.comp_continuousOn Real.continuous_sqrt.continuousOn) ?_
      intro t ht
      exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne')
    (fun φ hφ => by
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hVo φ hφ
      refine ⟨r, hr, hball, fun v hv => ?_⟩
      refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t ht => ?_)
      have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
      have hb := (hHφ' v (hball hv)).2.1 t ⟨ht.1.le, ht.2.le⟩
      have hr' : Real.rpow t (-1 / 2) = (Real.sqrt t)⁻¹ := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]
        exact g3005_rpow_neg_half_eq ht.1
      rw [hr', norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right hb hs.le)
  refine ⟨V, a, b, rω, rseg, hφV, hsep, hroots, ?_, ?_⟩
  · intro φ hφ
    have h1 := (hmain φ hφ).congr (g := fun φ : PotPair => ∫ t in (0 : ℝ)..1,
      Gf φ t / (Real.sqrt t : ℂ)) (by
        filter_upwards [hVo.mem_nhds hφ] with ψ hψ
        rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo])
    rw [hGf] at h1
    exact h1
  · intro φ hφ
    have h := (hHφ' φ hφ).2.2.2
    rw [hGf] at h
    exact h

/-- Non-endpoint case of the analytic lift: `exp(I e) = ±etaExponential` for an analytic `e` on a neighbourhood
inside `sourceBetaW \ collapsedSet n`. -/
theorem g3024_nonE_lift (n : ℤ) (φ0 : PotPair)
    (hφ0 : φ0 ∈ sourceBetaW \ (collapsedSet n ∪ endpointSet n)) :
    ∃ V : Set PotPair, ∃ e : PotPair → ℂ,
      IsOpen V ∧ φ0 ∈ V ∧ V ⊆ sourceBetaW \ collapsedSet n ∧
      AnalyticOnNhd ℂ e V ∧
      ∀ φ ∈ V, ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
        Complex.exp (Complex.I * e φ) = s * etaExponential n φ := by
  have hW : φ0 ∈ sourceW := sourceFamily.V_W hφ0.1
  obtain ⟨V, a, b, rω, rseg, hφV, hsep, -, hAn, hZ⟩ :=
    g3024_diag_package n φ0 ⟨hW, hφ0.2⟩
  obtain ⟨hVo, hVsub, -, -, hVp⟩ := hsep
  refine ⟨V ∩ sourceBetaW, fun φ : PotPair => ∫ t in (0 : ℝ)..1,
    (psi n φ (a φ + (t : ℂ) * (muSeq φ n - a φ)) * rω φ /
      (2 * Complex.I * rootProduct n (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) * rseg φ t)) /
      (Real.sqrt t : ℂ), hVo.inter sourceFamily.V_open, ⟨hφV, hφ0.1⟩, ?_, hAn.mono inter_subset_left, ?_⟩
  · intro φ hφ
    exact ⟨hφ.2, fun hc => (hVsub hφ.1).2 (Or.inl hc)⟩
  · intro φ hφ
    have hgam : lamPlus φ n - lamMinus φ n ≠ 0 := G3015Aux.gap_ne_of_mem n φ (hVsub hφ.1)
    have hZφ := hZ φ hφ.1
    obtain ⟨hpair, -⟩ := hVp φ hφ.1
    set X : ℂ := ∫ t in (0 : ℝ)..1,
      (psi n φ (a φ + (t : ℂ) * (muSeq φ n - a φ)) * rω φ /
        (2 * Complex.I * rootProduct n (φ, a φ + (t : ℂ) * (muSeq φ n - a φ)) * rseg φ t)) /
        (Real.sqrt t : ℂ) with hX
    have hE : etaExponential n φ = gk16ActualScalarZPlus38 sourceF n φ / (lamPlus φ n - lamMinus φ n) :=
      rfl
    rcases Set.pair_eq_pair_iff.1 hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨1, Or.inl rfl, ?_⟩
      show Complex.exp (Complex.I * X) = 1 * etaExponential n φ
      rw [h1, h2] at hZφ
      rw [hE, one_mul, hZφ]
      field_simp
    · refine ⟨-1, Or.inr rfl, ?_⟩
      show Complex.exp (Complex.I * X) = -1 * etaExponential n φ
      rw [h1, h2] at hZφ
      rw [hE, hZφ]
      field_simp
      ring

end
end G3024Param
end NlsGge.GKDefinitionDesign

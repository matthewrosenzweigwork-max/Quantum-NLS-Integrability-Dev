import Mathlib
import NlsGge.ThirdConsultation.G3.G3015Support
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G2.G2073Support1
import NlsGge.Atomic.G2.G2021
import NlsGge.Atomic.G2.G2075
import NlsGge.Atomic.G3.G3003
import NlsGge.Atomic.G3.G3014
import NlsGge.Atomic.G3.G3ZetaHost
import NlsGge.Atomic.G4.G4012
import NlsGge.ThirdConsultation.G3.G3005Support1

/- G3_015 PRODUCTION01 (proof development, AUTHOR; not semantically reviewed by its author).
   Target NlsGge/Atomic/G3/G3015.lean, namespace NlsGge.GKDefinitionDesign.
   Head VERBATIM from root/gpt6pro_followup7 STATEMENTS/G3.md:238-259 (Pro round 9; no later round changes G3-015).
   Proof: local_data uses G3015Support.labels (Pro G3_013 shape), landed G3_014 (analytic roots), then the explicit integrand
   H = G (psi form via G3015Support.factor), joint continuity on U x [0,1], a tube-lemma uniform bound C, analyticity in the potential
   from the joint analyticity of psi and rootProduct, integrability from C/sqrt(t), and the identity beta = int H/sqrt(t)
   (G3015Support.segment_integral).  analytic_of_local applies the landed G4-012 analytic-parameter-integral theorem
   (analyticOn_integral_of_rpow_half_locally_dominated) with majorant C t^(-1/2).  No hypothesis beyond the head. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G3015Aux
noncomputable section

theorem local_data (n m : ℤ) (hmn : m ≠ n) :
  ∀ φ0 ∈ sourceW \ (collapsedSet m ∪ endpointSet m),
    ∃ V : Set PotPair, ∃ a b rω : PotPair → ℂ,
    ∃ rseg : PotPair → ℝ → ℂ, ∃ C : ℝ,
      φ0 ∈ V ∧ LocalEndpointSegmentSeparation m V a b ∧
      AnalyticSegmentRoots m V a b rω rseg ∧ 0 < C ∧
      let H : PotPair → ℝ → ℂ := fun φ t =>
        let z := a φ+(t : ℂ)*(muSeq φ m-a φ)
        (normalizedRoot n m φ-z)*betaZeta n m φ z*rω φ/rseg φ t
      (∀ t ∈ Ioo (0 : ℝ) 1, AnalyticOnNhd ℂ (fun φ => H φ t) V) ∧
      (∀ φ ∈ V, ContinuousOn (H φ) (Icc (0 : ℝ) 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ‖H φ t‖ ≤ C) ∧
        IntervalIntegrable (fun t => H φ t/(Real.sqrt t : ℂ)) volume 0 1 ∧
        offDiagonalBeta n m φ = ∫ t in (0 : ℝ)..1, H φ t/(Real.sqrt t : ℂ)) := by
  intro φ0 hφ0
  obtain ⟨V1, a, b, hφV1, hsep⟩ := labels m φ0 hφ0
  obtain ⟨U, rω, rseg, hUo, hφU, hUV1, hroots⟩ := G3_014 m V1 a b hsep φ0 hφV1
  have hsepU : LocalEndpointSegmentSeparation m U a b := sep_mono m hsep hUo hUV1
  obtain ⟨-, hUsub, haA, hbA, hUp⟩ := hsepU
  obtain ⟨hrωA, hrsegA, hrsegC, hall⟩ := hroots
  have hUW : ∀ φ ∈ U, φ ∈ sourceW := fun φ hφ => (hUsub hφ).1
  have hUgk : ∀ φ ∈ U, φ ∈ gkW := fun φ hφ => sourceFamily.W_gk (hUW φ hφ)
  have hγ : ∀ φ ∈ U, lamPlus φ m - lamMinus φ m ≠ 0 := fun φ hφ => gap_ne_of_mem m φ (hUsub hφ)
  have hμA : ∀ φ ∈ U, AnalyticAt ℂ (fun ψ : PotPair => muSeq ψ m) φ := fun φ hφ =>
    analyticOnNhd_muSeq_complex38 m φ (hUgk φ hφ)
  have hpsiJ : AnalyticOnNhd ℂ (fun p : PotPair × ℂ => psi n p.1 p.2) (sourceW ×ˢ (univ : Set ℂ)) :=
    G2_075.2.2.2.1 n
  have hrPJ : AnalyticOnNhd ℂ (rootProduct m) (a5OmittedRootDomain38 m) := (G2_021 m).2.1
  have hrPN : ∀ p ∈ a5OmittedRootDomain38 m, rootProduct m p ≠ 0 := (G2_021 m).2.2
  -- explicit integrand
  obtain ⟨Hx, hHx⟩ : ∃ Hx : PotPair → ℝ → ℂ, ∀ φ t, Hx φ t =
      (normalizedRoot n m φ - (a φ + (t : ℂ) * (muSeq φ m - a φ))) *
        betaZeta n m φ (a φ + (t : ℂ) * (muSeq φ m - a φ)) * rω φ / rseg φ t :=
    ⟨fun φ t => (normalizedRoot n m φ - (a φ + (t : ℂ) * (muSeq φ m - a φ))) *
        betaZeta n m φ (a φ + (t : ℂ) * (muSeq φ m - a φ)) * rω φ / rseg φ t, fun _ _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : PotPair → ℝ → ℂ, ∀ φ t, G φ t =
      psi n φ (a φ + (t : ℂ) * (muSeq φ m - a φ)) * rω φ /
        (2 * Complex.I * rootProduct m (φ, a φ + (t : ℂ) * (muSeq φ m - a φ)) * rseg φ t) :=
    ⟨fun φ t => psi n φ (a φ + (t : ℂ) * (muSeq φ m - a φ)) * rω φ /
        (2 * Complex.I * rootProduct m (φ, a φ + (t : ℂ) * (muSeq φ m - a φ)) * rseg φ t),
      fun _ _ => rfl⟩
  have hzball : ∀ φ ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
      a φ + (t : ℂ) * (muSeq φ m - a φ) ∈ ball (discC φ m) (discR φ m) :=
    fun φ hφ t ht => seg_mem_ball m φ (hUgk φ hφ) (a φ) (b φ) (hUp φ hφ).1 t ht
  have hdom : ∀ φ ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
      (φ, a φ + (t : ℂ) * (muSeq φ m - a φ)) ∈ a5OmittedRootDomain38 m := fun φ hφ t ht =>
    ⟨hUgk φ hφ, fun k hk => closedBall_avoids_other_gaps φ (hUgk φ hφ) m k hk _
      (ball_subset_closedBall (hzball φ hφ t ht))⟩
  have hrP0 : ∀ φ ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
      rootProduct m (φ, a φ + (t : ℂ) * (muSeq φ m - a φ)) ≠ 0 := fun φ hφ t ht =>
    hrPN _ (hdom φ hφ t ht)
  have hden : ∀ φ ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
      2 * Complex.I * rootProduct m (φ, a φ + (t : ℂ) * (muSeq φ m - a φ)) * rseg φ t ≠ 0 :=
    fun φ hφ t ht => mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
      (hrP0 φ hφ t ht)) (((hall φ hφ).2.2.1 t ht).1)
  have hGeq : ∀ φ ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, Hx φ t = G φ t := by
    intro φ hφ t ht
    have hf := factor n m hmn φ (hUW φ hφ) (hγ φ hφ) _ (hzball φ hφ t ht)
    have hr := hrP0 φ hφ t ht
    have hρ := ((hall φ hφ).2.2.1 t ht).1
    rw [hHx, hG, hf]
    field_simp
  -- joint continuity of G on U × [0,1]
  have hμC : ContinuousOn (fun ψ : PotPair => muSeq ψ m) U :=
    fun φ hφ => (hμA φ hφ).continuousAt.continuousWithinAt
  have hSt : ∀ p ∈ U ×ˢ Icc (0 : ℝ) 1, p.1 ∈ U := fun p hp => hp.1
  have hzzC : ContinuousOn (fun p : PotPair × ℝ => a p.1 + (p.2 : ℂ) * (muSeq p.1 m - a p.1))
      (U ×ˢ Icc (0 : ℝ) 1) := by
    have ha_c : ContinuousOn (fun p : PotPair × ℝ => a p.1) (U ×ˢ Icc (0 : ℝ) 1) :=
      haA.continuousOn.comp continuousOn_fst hSt
    have hm_c : ContinuousOn (fun p : PotPair × ℝ => muSeq p.1 m) (U ×ˢ Icc (0 : ℝ) 1) :=
      hμC.comp continuousOn_fst hSt
    exact ha_c.add ((Complex.continuous_ofReal.comp_continuousOn continuousOn_snd).mul
      (hm_c.sub ha_c))
  have hmaps : MapsTo (fun p : PotPair × ℝ => (p.1, a p.1 + (p.2 : ℂ) * (muSeq p.1 m - a p.1)))
      (U ×ˢ Icc (0 : ℝ) 1) (a5OmittedRootDomain38 m) := fun p hp => hdom p.1 hp.1 p.2 hp.2
  have hGc : ContinuousOn (fun p : PotPair × ℝ => G p.1 p.2) (U ×ˢ Icc (0 : ℝ) 1) := by
    have hpsi : ContinuousOn (fun p : PotPair × ℝ =>
        psi n p.1 (a p.1 + (p.2 : ℂ) * (muSeq p.1 m - a p.1))) (U ×ˢ Icc (0 : ℝ) 1) :=
      ContinuousOn.comp (g := fun q : PotPair × ℂ => psi n q.1 q.2)
        (f := fun p : PotPair × ℝ => (p.1, a p.1 + (p.2 : ℂ) * (muSeq p.1 m - a p.1)))
        hpsiJ.continuousOn (continuousOn_fst.prodMk hzzC)
        (fun p hp => ⟨hUW p.1 hp.1, mem_univ _⟩)
    have hrP : ContinuousOn (fun p : PotPair × ℝ =>
        rootProduct m (p.1, a p.1 + (p.2 : ℂ) * (muSeq p.1 m - a p.1)))
        (U ×ˢ Icc (0 : ℝ) 1) :=
      ContinuousOn.comp (g := rootProduct m)
        (f := fun p : PotPair × ℝ => (p.1, a p.1 + (p.2 : ℂ) * (muSeq p.1 m - a p.1)))
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
  refine ⟨u, a, b, rω, rseg, max K 0 + 1, hφ0u, sep_mono m hsep huo (huU.trans hUV1),
    roots_mono m ⟨hrωA, hrsegA, hrsegC, hall⟩ huU, hC, ?_⟩
  intro H
  have hHH : H = Hx := by
    funext φ t
    exact (hHx φ t).symm
  rw [hHH]
  have hbound : ∀ φ ∈ u, ∀ t ∈ Icc (0 : ℝ) 1, ‖Hx φ t‖ ≤ max K 0 + 1 := by
    intro φ hφ t ht
    rw [hGeq φ (huU hφ) t ht]
    have := hbd φ hφ t ht
    have h2 : K + 1 ≤ max K 0 + 1 := by linarith [le_max_left K 0]
    linarith
  have hcont : ∀ φ ∈ u, ContinuousOn (Hx φ) (Icc (0 : ℝ) 1) := by
    intro φ hφ
    have h1 : ContinuousOn (fun t : ℝ => G φ t) (Icc (0 : ℝ) 1) :=
      hGc.comp (continuousOn_const.prodMk continuousOn_id)
        (fun t ht => ⟨huU hφ, ht⟩)
    exact h1.congr (fun t ht => hGeq φ (huU hφ) t ht)
  refine ⟨?_, fun φ hφ => ?_⟩
  · intro t ht
    have htc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    intro φ hφ
    have hφU' : φ ∈ U := huU hφ
    have hzA : AnalyticAt ℂ (fun ψ : PotPair => a ψ + (t : ℂ) * (muSeq ψ m - a ψ)) φ :=
      (haA φ hφU').add (analyticAt_const.mul ((hμA φ hφU').sub (haA φ hφU')))
    have hpair : AnalyticAt ℂ (fun ψ : PotPair => (ψ, a ψ + (t : ℂ) * (muSeq ψ m - a ψ))) φ :=
      analyticAt_id.prod hzA
    have hpsi : AnalyticAt ℂ (fun ψ : PotPair =>
        psi n ψ (a ψ + (t : ℂ) * (muSeq ψ m - a ψ))) φ :=
      AnalyticAt.comp (g := fun p : PotPair × ℂ => psi n p.1 p.2)
        (f := fun ψ : PotPair => (ψ, a ψ + (t : ℂ) * (muSeq ψ m - a ψ)))
        (hpsiJ (φ, a φ + (t : ℂ) * (muSeq φ m - a φ)) ⟨hUW φ hφU', mem_univ _⟩) hpair
    have hrP : AnalyticAt ℂ (fun ψ : PotPair =>
        rootProduct m (ψ, a ψ + (t : ℂ) * (muSeq ψ m - a ψ))) φ :=
      AnalyticAt.comp (g := rootProduct m)
        (f := fun ψ : PotPair => (ψ, a ψ + (t : ℂ) * (muSeq ψ m - a ψ)))
        (hrPJ _ (hdom φ hφU' t htc)) hpair
    have hGA : AnalyticAt ℂ (fun ψ : PotPair => G ψ t) φ := by
      have := (hpsi.mul (hrωA φ hφU')).div
        ((analyticAt_const.mul hrP).mul (hrsegA t htc φ hφU')) (hden φ hφU' t htc)
      refine this.congr (Filter.Eventually.of_forall fun ψ => ?_)
      exact (hG ψ t).symm
    refine hGA.congr ?_
    filter_upwards [huo.mem_nhds hφ] with ψ hψ
    exact (hGeq ψ (huU hψ) t htc).symm
  · refine ⟨hcont φ hφ, hbound φ hφ, integrable_of_bound (Hx φ) _ (hcont φ hφ) (hbound φ hφ), ?_⟩
    have hφU' : φ ∈ U := huU hφ
    obtain ⟨hω0, hωsq, hseg, hsign⟩ := hall φ hφU'
    have hρc : ContinuousOn (rseg φ) (Icc (0 : ℝ) 1) :=
      hrsegC.comp (continuousOn_const.prodMk continuousOn_id) (fun t ht => ⟨hφU', ht⟩)
    have hint : IntervalIntegrable (fun t : ℝ => Hx φ t / (Real.sqrt t : ℂ)) volume 0 1 :=
      integrable_of_bound (Hx φ) _ (hcont φ hφ) (hbound φ hφ)
    simp only [hHx] at hint ⊢
    exact segment_integral n m hmn φ (hUW φ hφU') (hγ φ hφU') (a φ) (b φ) (rω φ) (rseg φ)
      (hUp φ hφU').1 hω0 hωsq hρc (fun t ht => (hseg t ht).1) (fun t ht => (hseg t ht).2) hsign hint

def Hfun (n m : ℤ) (a rω : PotPair → ℂ) (rseg : PotPair → ℝ → ℂ) (φ : PotPair) (t : ℝ) : ℂ :=
  let z := a φ+(t : ℂ)*(muSeq φ m-a φ)
  (normalizedRoot n m φ-z)*betaZeta n m φ z*rω φ/rseg φ t

theorem analytic_of_local (n m : ℤ) (hmn : m ≠ n) :
    AnalyticOnNhd ℂ (offDiagonalBeta n m) (sourceW \ (collapsedSet m ∪ endpointSet m)) := by
  intro φ0 hφ0
  obtain ⟨V, a, b, rω, rseg, C, hφV, hsep, hroots, hC, hH⟩ := local_data n m hmn φ0 hφ0
  obtain ⟨hHan, hHφ⟩ := hH
  have hVo : IsOpen V := hsep.1
  have hHan' : ∀ t ∈ Ioo (0 : ℝ) 1, AnalyticOnNhd ℂ (fun φ => Hfun n m a rω rseg φ t) V := hHan
  have hHφ' : ∀ φ ∈ V, ContinuousOn (Hfun n m a rω rseg φ) (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ‖Hfun n m a rω rseg φ t‖ ≤ C) ∧
      IntervalIntegrable (fun t => Hfun n m a rω rseg φ t / (Real.sqrt t : ℂ)) volume 0 1 ∧
      offDiagonalBeta n m φ = ∫ t in (0 : ℝ)..1, Hfun n m a rω rseg φ t / (Real.sqrt t : ℂ) :=
    hHφ
  have hmain := NlsGge.Atomic.G4.analyticOn_integral_of_rpow_half_locally_dominated
    (E := PotPair) (F := ℂ) (U := V)
    (a := fun (t : ℝ) (φ : PotPair) => Hfun n m a rω rseg φ t / (Real.sqrt t : ℂ)) C hC.le hVo
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
  refine (hmain φ0 hφV).congr ?_
  filter_upwards [hVo.mem_nhds hφV] with φ hφ
  rw [(hHφ' φ hφ).2.2.2, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]

end
end G3015Aux

noncomputable section

theorem G3_015 (n m : ℤ) (hmn : m ≠ n) :
  AnalyticOnNhd ℂ (offDiagonalBeta n m)
    (sourceW \ (collapsedSet m ∪ endpointSet m)) ∧
  ∀ φ0 ∈ sourceW \ (collapsedSet m ∪ endpointSet m),
    ∃ V : Set PotPair, ∃ a b rω : PotPair → ℂ,
    ∃ rseg : PotPair → ℝ → ℂ, ∃ C : ℝ,
      φ0 ∈ V ∧ LocalEndpointSegmentSeparation m V a b ∧
      AnalyticSegmentRoots m V a b rω rseg ∧ 0 < C ∧
      let H : PotPair → ℝ → ℂ := fun φ t =>
        let z := a φ+(t : ℂ)*(muSeq φ m-a φ)
        (normalizedRoot n m φ-z)*betaZeta n m φ z*rω φ/rseg φ t
      (∀ t ∈ Ioo (0 : ℝ) 1, AnalyticOnNhd ℂ (fun φ => H φ t) V) ∧
      (∀ φ ∈ V, ContinuousOn (H φ) (Icc (0 : ℝ) 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ‖H φ t‖ ≤ C) ∧
        IntervalIntegrable (fun t => H φ t/(Real.sqrt t : ℂ)) volume 0 1 ∧
        offDiagonalBeta n m φ = ∫ t in (0 : ℝ)..1, H φ t/(Real.sqrt t : ℂ)) :=
  ⟨G3015Aux.analytic_of_local n m hmn, G3015Aux.local_data n m hmn⟩

end
end NlsGge.GKDefinitionDesign

import Mathlib
import NlsGge.ThirdConsultation.G3.G3SourcePathHost
import NlsGge.ThirdConsultation.G3.G3005UpperHost
import NlsGge.ThirdConsultation.G3.G3005C4Support
import NlsGge.ThirdConsultation.G3.G3001Support

/- G3-005 C5 (proof development, AUTHOR; not self-reviewed). Target NlsGge/ThirdConsultation/G3/G3005C5.lean (proposed).
   Conjunct 5 of Pro round 9 sec. 9 G3_005: every upper-start path has a joint improper integral. Route = the G3-001 route with
   the first endpoint changed from lamMinus to lamPlus:
     * g3005_first_arc_limit_at: byte-for-byte the proof of g3001_first_arc_endpoint_limit_native with the base point a0 a
       parameter (a0 in the cut instead of lamMinus); same hypotheses otherwise.
     * compact integrability of arcs (copy of the private Armstrong rawBetaArcCompactIntegrable38 with the nonvanishing of
       perChar on the slit proved natively from canonRoot38).
     * last arc: g3001_last_arc_full (G3-001), local primitive: g3001_L3_branch_prim at lamPlus (Or.inr rfl).
   Dependencies on G3-001: g3001_L3_branch_prim, g3001_last_arc_full, g3001_arc_props261, g3001_L2n_perChar_eventually_ne,
   g3001_sheet_primitive_hasDerivAt. No hypothesis beyond gap <> 0. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory intervalIntegral
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g3005_first_arc_limit_at
    (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (a : GKRootedC1Arc38 φ m)
    (a0 : ℂ) (ha0 : GKArcCurve38 a 0 = a0)
    (ha0seg : a0 ∈ segment ℝ (lamMinus φ.1 m) (lamPlus φ.1 m))
    (hint : ∀ ε : ℝ, 0 < ε → ε < 1 →
      IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume ε 1)
    (hprim : ∃ r : ℝ, 0 < r ∧ ∃ R : ℂ → ℂ, AnalyticOnNhd ℂ R (ball a0 r) ∧
      ∀ z ∈ ball a0 r,
        perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z =
          p6PsiNumerator38 n (F n) φ.1 z) :
    ∃ L : ℂ, Tendsto (fun ε : ℝ => ∫ t in ε..(1:ℝ), GKRootedArcIntegrand38 n m F φ a t)
      (𝓝[>] (0:ℝ)) (𝓝 L) := by
  obtain ⟨hγc, hγd, hsc, hsq, hslit⟩ := g3001_arc_props261 a
  obtain ⟨r, hr, R, hRan, hODE⟩ := hprim
  -- perChar has no zero in a punctured neighbourhood of a0
  have hnv : ∀ᶠ z in 𝓝[≠] a0, perChar φ.1 z ≠ 0 := g3001_L2n_perChar_eventually_ne φ.1 a0
  obtain ⟨ρ, hρ, hρball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hnv)
  have hδ : 0 < min ρ r := lt_min hρ hr
  have hc : Tendsto (GKArcCurve38 a) (𝓝[Icc (0:ℝ) 1] 0) (𝓝 a0) := by
    rw [← ha0]
    exact (hγc 0 ⟨le_rfl, zero_le_one⟩).tendsto
  have hev : ∀ᶠ t in 𝓝[Icc (0:ℝ) 1] (0:ℝ), GKArcCurve38 a t ∈ ball a0 (min ρ r) :=
    hc.eventually (ball_mem_nhds a0 hδ)
  obtain ⟨θ, hθ, hθev⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  obtain ⟨t0, ht0, ht0θ, ht01⟩ : ∃ t0 : ℝ, 0 < t0 ∧ t0 < θ ∧ t0 < 1 :=
    ⟨min (θ / 2) (1 / 2), lt_min (by linarith) (by norm_num),
      by linarith [min_le_left (θ / 2) (1 / 2)], by linarith [min_le_right (θ / 2) (1 / 2)]⟩
  have hball : ∀ t ∈ Icc (0:ℝ) t0, GKArcCurve38 a t ∈ ball a0 (min ρ r) := by
    intro t ht
    have hd : dist t 0 < θ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      linarith [ht.2]
    exact hθev hd ⟨ht.1, ht.2.trans ht01.le⟩
  -- the sheet does not vanish on (0,t0]
  have hsn : ∀ t ∈ Ioo (0:ℝ) t0, GKArcSheet38 a t ≠ 0 := by
    intro t ht
    have ht1 : t ∈ Ioo (0:ℝ) 1 := ⟨ht.1, lt_trans ht.2 ht01⟩
    have hmem := hball t ⟨ht.1.le, ht.2.le⟩
    have hne : GKArcCurve38 a t ≠ a0 := by
      intro h
      apply hslit t ht1
      rw [h]
      exact ha0seg
    have hdist : dist (GKArcCurve38 a t) a0 < ρ :=
      lt_of_lt_of_le (mem_ball.mp hmem) (min_le_left _ _)
    have hpc : perChar φ.1 (GKArcCurve38 a t) ≠ 0 :=
      hρball hdist (Set.mem_compl_singleton_iff.mpr hne)
    intro h0
    have hs2 := hsq t ⟨ht1.1.le, ht1.2.le⟩
    rw [h0] at hs2
    exact hpc (by simpa using hs2.symm)
  -- derivative of G(t) = sheet(t) * R(arc t) is the integrand on (0,t0)
  have hderiv : ∀ t ∈ Ioo (0:ℝ) t0,
      HasDerivAt (fun u => GKArcSheet38 a u * R (GKArcCurve38 a u))
        (GKRootedArcIntegrand38 n m F φ a t) t := by
    intro t ht
    have ht1 : t ∈ Ioo (0:ℝ) 1 := ⟨ht.1, lt_trans ht.2 ht01⟩
    have hIcc : Icc (0:ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht1.1 ht1.2
    have hγ : HasDerivAt (GKArcCurve38 a) (deriv (GKArcCurve38 a) t) t :=
      ((hγd.differentiableOn (by norm_num)).differentiableAt hIcc).hasDerivAt
    have hmem := hball t ⟨ht.1.le, ht.2.le⟩
    have hRball : GKArcCurve38 a t ∈ ball a0 r := ball_subset_ball (min_le_right _ _) hmem
    have hP : HasDerivAt (perChar φ.1) (deriv (perChar φ.1) (GKArcCurve38 a t))
        (GKArcCurve38 a t) :=
      ((analyticOnNhd_perChar_z φ.1 (GKArcCurve38 a t) (mem_univ _)).differentiableAt).hasDerivAt
    have hR : HasDerivAt R (deriv R (GKArcCurve38 a t)) (GKArcCurve38 a t) :=
      ((hRan _ hRball).differentiableAt).hasDerivAt
    have hsc' : ContinuousAt (GKArcSheet38 a) t := hsc.continuousAt hIcc
    have he : (fun u => GKArcSheet38 a u ^ 2) =ᶠ[𝓝 t] (perChar φ.1 ∘ GKArcCurve38 a) := by
      filter_upwards [hIcc] with u hu
      exact hsq u hu
    have hODE' := hODE (GKArcCurve38 a t) hRball
    have key := g3001_sheet_primitive_hasDerivAt (P := perChar φ.1)
      (Ψ := fun z => p6PsiNumerator38 n (F n) φ.1 z) (R := R) hγ hP hR hsc'
      (hsn t ht) he hODE'
    unfold GKRootedArcIntegrand38
    exact key
  -- G is continuous on [0,t0]
  have hGc : ContinuousOn (fun u => GKArcSheet38 a u * R (GKArcCurve38 a u)) (Icc 0 t0) := by
    have hRc : ContinuousOn R (ball a0 r) := fun x hx =>
      ((hRan x hx).continuousAt).continuousWithinAt
    have hγ' : ContinuousOn (GKArcCurve38 a) (Icc 0 t0) :=
      hγc.mono (Icc_subset_Icc le_rfl ht01.le)
    have hmaps : MapsTo (GKArcCurve38 a) (Icc 0 t0) (ball a0 r) := fun u hu =>
      ball_subset_ball (min_le_right _ _) (hball u hu)
    exact (hsc.mono (Icc_subset_Icc le_rfl ht01.le)).mul (hRc.comp hγ' hmaps)
  set G : ℝ → ℂ := fun u => GKArcSheet38 a u * R (GKArcCurve38 a u) with hGdef
  -- FTC on [eps,t0] and splitting at t0
  have hftc : ∀ ε ∈ Ioo (0:ℝ) t0,
      ∫ t in ε..(1:ℝ), GKRootedArcIntegrand38 n m F φ a t =
        (G t0 - G ε) + ∫ t in t0..(1:ℝ), GKRootedArcIntegrand38 n m F φ a t := by
    intro ε hε
    have hint_ε : IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume ε t0 :=
      (hint ε hε.1 (lt_trans hε.2 ht01)).mono_set
        (Set.uIcc_subset_uIcc Set.left_mem_uIcc
          (Set.mem_uIcc.2 (Or.inl ⟨hε.2.le, ht01.le⟩)))
    have hC : IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume t0 1 :=
      hint t0 ht0 ht01
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hint_ε hC
    have hcont : ContinuousOn G (Icc ε t0) := hGc.mono (Icc_subset_Icc hε.1.le le_rfl)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hε.2.le hcont
      (f' := GKRootedArcIntegrand38 n m F φ a)
      (fun x hx => hderiv x ⟨lt_trans hε.1 hx.1, hx.2⟩) hint_ε
    rw [← hsplit, hFTC]
  -- limit of G at 0 from the right
  have hGlim : Tendsto G (𝓝[>] (0:ℝ)) (𝓝 (G 0)) := by
    have h0 : ContinuousWithinAt G (Icc 0 t0) 0 := hGc 0 ⟨le_rfl, ht0.le⟩
    have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0:ℝ)) (𝓝[Icc (0:ℝ) t0] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, ?_⟩
      · exact (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT ht0] with ε hε
        exact ⟨hε.1.le, hε.2.le⟩
    exact h0.tendsto.comp hid
  refine ⟨G t0 - G 0 + ∫ t in t0..(1:ℝ), GKRootedArcIntegrand38 n m F φ a t, ?_⟩
  refine Tendsto.congr' ?_ ((tendsto_const_nhds.sub hGlim).add tendsto_const_nhds)
  filter_upwards [Ioo_mem_nhdsGT ht0] with ε hε
  exact (hftc ε hε).symm

theorem g3005_perChar_ne_slit (φ : GKPotential38) (m : ℤ) (z : ℂ) (hz : z ∈ GKOriginalSlit38 φ m) :
    perChar φ.1 z ≠ 0 := by
  have hng : z ∉ gapSegments38 φ.1 := G3005C4.not_gap φ.1 φ.2 m z hz.1 hz.2
  rw [← canonRoot_sq38 φ.1 φ.2 z hng]
  exact pow_ne_zero 2 (canonRoot_ne_zero38 φ.1 φ.2 z hng)

theorem g3005_arc_integrable (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (φ : GKPotential38) (a : GKRootedC1Arc38 φ m)
    (u v : ℝ) (hu : 0 ≤ u) (hv : v ≤ 1) (huv : u ≤ v)
    (hslit : ∀ t ∈ Icc u v, GKArcCurve38 a t ∈ GKOriginalSlit38 φ m) :
    IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume u v := by
  have hsub : Icc u v ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hu hv
  have hcurve : ContinuousOn (GKArcCurve38 a) (Icc (0 : ℝ) 1) := a.2.1
  have hC1 : ContDiffOn ℝ 1 (GKArcCurve38 a) (Icc (0 : ℝ) 1) := a.2.2.1
  have hsheet : ContinuousOn (GKArcSheet38 a) (Icc (0 : ℝ) 1) := a.2.2.2.1
  have hsquare : ∀ t ∈ Icc (0 : ℝ) 1,
      GKArcSheet38 a t ^ 2 = perChar φ.1 (GKArcCurve38 a t) := a.2.2.2.2.1
  have hnonzero : ∀ t ∈ Icc u v, GKArcSheet38 a t ≠ 0 := by
    intro t ht hzero
    apply g3005_perChar_ne_slit φ m (GKArcCurve38 a t) (hslit t ht)
    rw [← hsquare t (hsub ht), hzero]
    norm_num
  have hnumerator : Continuous (p6PsiNumerator38 n (F n) φ.1) :=
    continuousOn_univ.mp (p6PsiNumerator_entire38 n (F n) φ.1).continuousOn
  have hquotient : ContinuousOn
      (fun t => p6PsiNumerator38 n (F n) φ.1 (GKArcCurve38 a t) /
        GKArcSheet38 a t) (Icc u v) :=
    ((hnumerator.comp_continuousOn hcurve).mono hsub).div₀
      (hsheet.mono hsub) hnonzero
  have hderivative : ContinuousOn
      (derivWithin (GKArcCurve38 a) (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) :=
    hC1.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hcontinuous : ContinuousOn
      (fun t => (p6PsiNumerator38 n (F n) φ.1 (GKArcCurve38 a t) /
        GKArcSheet38 a t) *
        derivWithin (GKArcCurve38 a) (Icc (0 : ℝ) 1) t) (Icc u v) :=
    hquotient.mul (hderivative.mono hsub)
  have hintegrable : IntervalIntegrable
      (fun t => (p6PsiNumerator38 n (F n) φ.1 (GKArcCurve38 a t) /
        GKArcSheet38 a t) *
        derivWithin (GKArcCurve38 a) (Icc (0 : ℝ) 1) t) volume u v :=
    hcontinuous.intervalIntegrable_of_Icc huv
  apply hintegrable.congr_uIoo
  intro t ht
  have hti : t ∈ Ioo u v := by simpa only [uIoo_of_le huv] using ht
  have ht0 : 0 < t := lt_of_le_of_lt hu hti.1
  have ht1 : t < 1 := lt_of_lt_of_le hti.2 hv
  change (p6PsiNumerator38 n (F n) φ.1 (GKArcCurve38 a t) /
      GKArcSheet38 a t) * derivWithin (GKArcCurve38 a) (Icc (0 : ℝ) 1) t =
    (p6PsiNumerator38 n (F n) φ.1 (GKArcCurve38 a t) /
      GKArcSheet38 a t) * deriv (GKArcCurve38 a) t
  exact congrArg (fun d : ℂ =>
    (p6PsiNumerator38 n (F n) φ.1 (GKArcCurve38 a t) / GKArcSheet38 a t) * d)
    (derivWithin_of_mem_nhds (f := GKArcCurve38 a) (Icc_mem_nhds ht0 ht1))

theorem g3005_chain_slit_endpoints
    (φ : GKPotential38) (m : ℤ)
    (first last : GKRootedC1Arc38 φ m)
    (middle : List (GKRootedC1Arc38 φ m))
    (hchain : GKRootedArcChain38 φ m (first :: (middle ++ [last]))) :
    GKArcCurve38 first 1 ∈ GKOriginalSlit38 φ m ∧
    (∀ a ∈ middle,
      GKArcCurve38 a 0 ∈ GKOriginalSlit38 φ m ∧
      GKArcCurve38 a 1 ∈ GKOriginalSlit38 φ m) ∧
    GKArcCurve38 last 0 ∈ GKOriginalSlit38 φ m := by
  induction middle generalizing first with
  | nil =>
      change GKRootedArcJoin38 φ m first last ∧
        GKRootedArcChain38 φ m [last] at hchain
      have hjoin := hchain.1
      refine ⟨hjoin.2.2, ?_, ?_⟩
      · intro a ha
        simp at ha
      · simpa only [hjoin.1] using hjoin.2.2
  | cons a tail ih =>
      change GKRootedArcJoin38 φ m first a ∧
        GKRootedArcChain38 φ m (a :: (tail ++ [last])) at hchain
      have hjoin := hchain.1
      obtain ⟨ha1, htail, hlast0⟩ := ih a hchain.2
      refine ⟨hjoin.2.2, ?_, hlast0⟩
      intro b hb
      rcases List.mem_cons.mp hb with hba | hb
      · subst b
        refine ⟨?_, ha1⟩
        simpa only [hjoin.1] using hjoin.2.2
      · exact htail b hb

theorem g3005_upper_compact (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (φ : GKPotential38) (q : GKRootedPathData38 φ m)
    (hchain : GKRootedArcChain38 φ m (q.1 :: (q.2.1 ++ [q.2.2]))) :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ε + η < 1 →
      IntervalIntegrable (GKRootedArcIntegrand38 n m F φ q.1) volume ε 1 ∧
      (∀ a ∈ q.2.1, IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume 0 1) ∧
      IntervalIntegrable (GKRootedArcIntegrand38 n m F φ q.2.2) volume 0 (1 - η) := by
  obtain ⟨hfirstEnd, hmiddleEnds, hlastStart⟩ :=
    g3005_chain_slit_endpoints φ m q.1 q.2.2 q.2.1 hchain
  intro ε η hε hη hsum
  have hε1 : ε < 1 := by linarith
  have hη1 : η < 1 := by linarith
  have hlastpos : 0 < 1 - η := by linarith
  have hlastlt : 1 - η < 1 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · apply g3005_arc_integrable n m F φ q.1 ε 1 hε.le le_rfl hε1.le
    intro t ht
    by_cases ht1 : t = 1
    · subst t
      exact hfirstEnd
    have hti : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_lt_of_le hε ht.1, lt_of_le_of_ne ht.2 ht1⟩
    exact q.1.2.2.2.2.2.2 t hti
  · intro a ha
    apply g3005_arc_integrable n m F φ a 0 1 le_rfl le_rfl zero_le_one
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      exact (hmiddleEnds a ha).1
    by_cases ht1 : t = 1
    · subst t
      exact (hmiddleEnds a ha).2
    have hti : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    exact a.2.2.2.2.2.2 t hti
  · apply g3005_arc_integrable n m F φ q.2.2 0 (1 - η) le_rfl hlastlt.le hlastpos.le
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      exact hlastStart
    have hti : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_lt ht.2 hlastlt⟩
    exact q.2.2.2.2.2.2.2.2 t hti

theorem g3005_c5 (n m : ℤ) (φ : SourcePotential) (hgap : gap φ.1 m ≠ 0)
    (p : UpperStartPath m φ) : ∃ b : ℂ, HasUpperStartIntegral n m φ p b := by
  have hgap' : lamPlus φ.1 m ≠ lamMinus φ.1 m := fun h => hgap (sub_eq_zero.mpr h)
  have hcompact := g3005_upper_compact n m sourceF (sourceGK φ) p.1 p.2.2.1
  have hint1 : ∀ ε : ℝ, 0 < ε → ε < 1 →
      IntervalIntegrable (GKRootedArcIntegrand38 n m sourceF (sourceGK φ) p.1.1) volume ε 1 := by
    intro ε hε hε1
    exact (hcompact ε ((1 - ε) / 2) hε (by linarith) (by linarith)).1
  have hint3 : ∀ η : ℝ, 0 < η → η < 1 →
      IntervalIntegrable (GKRootedArcIntegrand38 n m sourceF (sourceGK φ) p.1.2.2) volume 0 (1 - η) := by
    intro η hη hη1
    exact (hcompact ((1 - η) / 2) η (by linarith) hη (by linarith)).2.2
  have hz0 : perChar φ.1 (lamPlus φ.1 m) = 0 :=
    ((lamSeq_enumeration38 φ.1).2.1 _).mpr ⟨2 * m + 1, rfl⟩
  have hprim := g3001_L3_branch_prim n m sourceF (sourceGK φ) hgap' (lamPlus φ.1 m) hz0 (Or.inr rfl)
  obtain ⟨L1, hL1⟩ := g3005_first_arc_limit_at n m sourceF (sourceGK φ) p.1.1 (lamPlus φ.1 m)
    p.2.2.2.1 (right_mem_segment ℝ _ _) hint1 hprim
  obtain ⟨L2, hL2⟩ := g3001_last_arc_full n m sourceF (sourceGK φ) hgap' p.1.2.2 p.2.2.2.2.1 hint3
  refine ⟨L1 + GKPathMiddleIntegral38 n m sourceF (sourceGK φ) p.1.2.1 + L2, ?_, ?_⟩
  · exact hcompact
  let S : Set (ℝ × ℝ) := {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}
  have hS : S ∈ 𝓝[S] ((0:ℝ), (0:ℝ)) := self_mem_nhdsWithin
  have hfst : Tendsto (fun q : ℝ × ℝ => q.1) (𝓝[S] ((0:ℝ), (0:ℝ))) (𝓝[>] (0:ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (continuous_fst.tendsto ((0:ℝ), (0:ℝ))).mono_left nhdsWithin_le_nhds
    · filter_upwards [hS] with q hq
      exact hq.1
  have hsnd : Tendsto (fun q : ℝ × ℝ => q.2) (𝓝[S] ((0:ℝ), (0:ℝ))) (𝓝[>] (0:ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (continuous_snd.tendsto ((0:ℝ), (0:ℝ))).mono_left nhdsWithin_le_nhds
    · filter_upwards [hS] with q hq
      exact hq.2.1
  have hA := hL1.comp hfst
  have hB := hL2.comp hsnd
  exact (hA.add_const (GKPathMiddleIntegral38 n m sourceF (sourceGK φ) p.1.2.1)).add hB

end
end NlsGge.GKDefinitionDesign

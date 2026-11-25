import NlsGge.Ramer.LinearSmallStep8
import NlsGge.Ramer.RamerLemma54
import NlsGge.Ramer.RamerStep1Locality

/-!
# D2, part 2: the Jacobi formula for the linear small `S` near `0`

Ramer (1974) Step 10, two-sided argument, on a small ball `V = B_ρ(0)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- From (**)'s null-set clause to null-set preservation of `TM L` on a small set `U`. -/
theorem nullPres_of_concl (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c)
    {ε : ℝ} (hc : Step8Concl c s hs L ε) (U : Set (FullWeightedHilbert c s))
    (hUb : U ⊆ closedBall (0 : FullWeightedHilbert c s) ε)
    (hUZ : ∀ x ∈ U, x + inclE c s hs (L x) ∈ ball (0 : FullWeightedHilbert c s) (ε / 2)) :
    ∀ N : Set (FullWeightedHilbert c s),
      NlsGge.Measure.fullWeightedSequenceGaussian c s N = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (U ∩ TM c s hs L ⁻¹' N) = 0 := by
  intro N hN
  have hN' : NlsGge.Measure.fullWeightedSequenceGaussian c s
      (toMeasurable (NlsGge.Measure.fullWeightedSequenceGaussian c s) N) = 0 := by
    rwa [measure_toMeasurable]
  have := hc.2.2 (toMeasurable (NlsGge.Measure.fullWeightedSequenceGaussian c s) N ∩
      ball (0 : FullWeightedHilbert c s) (ε / 2))
    ((measurableSet_toMeasurable _ _).inter measurableSet_ball) inter_subset_right
    (measure_mono_null inter_subset_left hN')
  refine measure_mono_null ?_ this
  rintro x ⟨hxU, hxN⟩
  exact ⟨hUb hxU, subset_toMeasurable _ _ hxN, hUZ x hxU⟩

theorem ramerJac_nonneg (hs : (1 : ℝ) / 2 < s) (M : FullWeightedHilbert c s → ActualCM c)
    (x : FullWeightedHilbert c s) : 0 ≤ ramerJac c s hs M x := by
  rw [ramerJac_eq]; positivity

theorem aemeasurable_ofReal_ramerJac (hs : (1 : ℝ) / 2 < s)
    (M : FullWeightedHilbert c s → ActualCM c) (hM : ContDiff ℝ 2 M) :
    AEMeasurable (fun x => ENNReal.ofReal (ramerJac c s hs M x))
      (NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
  have h := aestronglyMeasurable_ramerJE c s hs M (hM.of_le (by norm_num)) (ramerDiv c s hs M)
    (ramerDiv_spec c s hs M hM).1
  exact h.aemeasurable.ennreal_ofReal

/-- Transfer of a.e. statements along `S.symm`, from null-set preservation. -/
theorem ae_transfer {X : Type*} [MeasurableSpace X] (μ : Measure X) (e : X ≃ᵐ X) (V : Set X)
    (hQ : ∀ N : Set X, μ N = 0 → μ (e '' (V ∩ N)) = 0) (P : X → Prop)
    (hP : ∀ᵐ x ∂μ, P x) : ∀ᵐ y ∂μ, y ∈ e '' V → P (e.symm y) := by
  have h1 : μ {x | ¬ P x} = 0 := ae_iff.1 hP
  have h2 := hQ _ h1
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h2] with y hy hyV
  obtain ⟨x, hxV, rfl⟩ := hyV
  rw [e.symm_apply_apply]
  by_contra hP'
  exact hy ⟨x, ⟨hxV, hP'⟩, rfl⟩


variable {c s}

/-- **Ramer Step 10, two-sided argument, on a ball.**  See the module docstring. -/
theorem jacobi_local_of_step8 (hs : (1 : ℝ) / 2 < s)
    (S : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (A M : FullWeightedHilbert c s → ActualCM c)
    (hAs : ContDiff ℝ 2 A) (hMs : ContDiff ℝ 2 M)
    (hS : ∀ x, S x = x + inclE c s hs (A x))
    (hSs : ∀ x, S.symm x = x + inclE c s hs (M x))
    (hGT : ∀ x, M (S x) = -A x)
    {ε : ℝ} (hcA : Step8Concl c s hs A ε)
    (hcAk : ∀ k : ℕ, Step8Concl c s hs (projField k A) ε)
    (hcM : Step8Concl c s hs M ε)
    (ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ ≤ ε / 2)
    (hρS : ∀ x ∈ ball (0 : FullWeightedHilbert c s) ρ,
      S x ∈ ball (0 : FullWeightedHilbert c s) (ε / 2))
    (hρk : ∀ k : ℕ, ∀ x ∈ ball (0 : FullWeightedHilbert c s) ρ,
      TM c s hs (projField k A) x ∈ ball (0 : FullWeightedHilbert c s) (ε / 2)) :
    ∃ J : FullWeightedHilbert c s → ℝ≥0∞, Measurable J ∧
      (J =ᵐ[NlsGge.Measure.fullWeightedSequenceGaussian c s]
        fun x => ENNReal.ofReal (ramerJac c s hs A x)) ∧
      ∀ F : FullWeightedHilbert c s → ℝ, UniformContinuous F → (∃ C, ∀ y, |F y| ≤ C) →
        (∀ y, 0 ≤ F y) →
        tsupport F ⊆ S '' ball (0 : FullWeightedHilbert c s) ρ →
        ∫⁻ y in S '' ball (0 : FullWeightedHilbert c s) ρ, ENNReal.ofReal (F y)
            ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) =
          ∫⁻ x in ball (0 : FullWeightedHilbert c s) ρ, ENNReal.ofReal (F (S x)) * J x
            ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
  set γ := NlsGge.Measure.fullWeightedSequenceGaussian c s with hγ
  set V : Set (FullWeightedHilbert c s) := ball 0 ρ with hV
  have hVo : IsOpen V := isOpen_ball
  have hVZ : V ⊆ ball (0 : FullWeightedHilbert c s) (ε / 2) :=
    ball_subset_ball hρε
  have hVB : V ⊆ closedBall (0 : FullWeightedHilbert c s) ε := fun x hx =>
    ball_subset_closedBall (hVZ.trans (ball_subset_ball (by linarith)) hx)
  have hSZ : S '' V ⊆ ball (0 : FullWeightedHilbert c s) (ε / 2) := by
    rintro _ ⟨x, hx, rfl⟩; exact hρS x hx
  -- measurable representatives
  have hmA := aemeasurable_ofReal_ramerJac c s hs A hAs
  have hmM := aemeasurable_ofReal_ramerJac c s hs M hMs
  set JA := hmA.mk with hJAdef
  set JM := hmM.mk with hJMdef
  have hJA : Measurable JA := hmA.measurable_mk
  have hJM : Measurable JM := hmM.measurable_mk
  have hJAae : JA =ᵐ[γ] fun x => ENNReal.ofReal (ramerJac c s hs A x) := hmA.ae_eq_mk.symm
  have hJMae : JM =ᵐ[γ] fun x => ENNReal.ofReal (ramerJac c s hs M x) := hmM.ae_eq_mk.symm
  -- the measurable equivalence
  let e : FullWeightedHilbert c s ≃ᵐ FullWeightedHilbert c s := S.toHomeomorph.toMeasurableEquiv
  have he : ∀ x, e x = S x := fun x => rfl
  have hes : ∀ x, e.symm x = S.symm x := fun x => rfl
  have hSV : MeasurableSet (S '' V) := (S.toHomeomorph.isOpenMap V hVo).measurableSet
  have hSinj : Function.Injective S := S.injective
  -- preimage / image under the two maps
  have hpreS : ∀ B : Set (FullWeightedHilbert c s),
      (fun y => y + inclE c s hs (A y)) ⁻¹' B = S ⁻¹' B := by
    intro B; ext x; simp only [mem_preimage, hS x]
  have hpreSs : ∀ B : Set (FullWeightedHilbert c s),
      (fun y => y + inclE c s hs (M y)) ⁻¹' B = S.symm ⁻¹' B := by
    intro B; ext x; simp only [mem_preimage, hSs x]
  have himg : ∀ B : Set (FullWeightedHilbert c s), S.symm ⁻¹' B = S '' B := by
    intro B; ext x; constructor
    · intro h; exact ⟨S.symm x, h, S.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  -- (1)
  have h1 : ∀ B : Set (FullWeightedHilbert c s), B ⊆ S '' V →
      ∫⁻ x in S ⁻¹' B, JA x ∂γ ≤ γ B := by
    intro B hB
    have hsub : S ⁻¹' B ⊆ V := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hB hx
      rwa [← hSinj hyx]
    have := hcA.2.1 B (hB.trans hSZ)
    rw [hpreS, inter_eq_right.2 (hsub.trans hVB)] at this
    refine le_trans (le_of_eq ?_) this
    exact lintegral_congr_ae (ae_restrict_of_ae hJAae)
  -- (2)
  have h2 : ∀ A' : Set (FullWeightedHilbert c s), A' ⊆ V →
      ∫⁻ y in S '' A', JM y ∂γ ≤ γ A' := by
    intro A' hA'
    have := hcM.2.1 A' (hA'.trans hVZ)
    rw [hpreSs, himg, inter_eq_right.2 ((image_mono hA').trans (hSZ.trans
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))))] at this
    refine le_trans (le_of_eq ?_) this
    exact lintegral_congr_ae (ae_restrict_of_ae hJMae)
  -- null-set preservation of `S` on `V` (from `M`)
  have hQ : ∀ N : Set (FullWeightedHilbert c s), γ N = 0 → γ (e '' (V ∩ N)) = 0 := by
    intro N hN
    have hN' : γ (toMeasurable γ N) = 0 := by rwa [measure_toMeasurable]
    have := hcM.2.2 (toMeasurable γ N ∩ V) ((measurableSet_toMeasurable _ _).inter
      hVo.measurableSet) (inter_subset_right.trans hVZ)
      (measure_mono_null inter_subset_left hN')
    refine measure_mono_null ?_ this
    rintro _ ⟨x, ⟨hxV, hxN⟩, rfl⟩
    refine ⟨closedBall_subset_closedBall (by linarith : ε / 2 ≤ ε)
      (ball_subset_closedBall (hSZ ⟨x, hxV, rfl⟩)), ?_⟩
    have hx : S x + inclE c s hs (M (S x)) = x := by rw [← hSs, S.symm_apply_apply]
    show S x + inclE c s hs (M (S x)) ∈ toMeasurable γ N ∩ V
    rw [hx]
    exact ⟨subset_toMeasurable _ _ hxN, hxV⟩
  -- a.e. identity
  have hd := ramerJac_comp_mul_eq_one hs V hVo A M hAs hMs
    (nullPres_of_concl c s hs A hcA V hVB (fun x hx => by rw [← hS x]; exact hρS x hx))
    (fun k => nullPres_of_concl c s hs _ (hcAk k) V hVB (hρk k)) 
    (fun x _ => by
      have : TM c s hs A x = S x := (hS x).symm
      rw [this, hGT])
  have hTMS : TM c s hs A = S := funext fun x => (hS x).symm
  rw [hTMS] at hd
  have hT1 := ae_transfer γ e V hQ _ hd
  have hT2 := ae_transfer γ e V hQ _ hJAae
  have hT3 : ∀ᵐ y ∂γ, JM y = ENNReal.ofReal (ramerJac c s hs M y) := hJMae
  have hprod : ∀ᵐ y ∂γ, y ∈ S '' V → JA (S.symm y) * JM y = 1 := by
    filter_upwards [hT1, hT2, hT3] with y a b c' hy
    have hyV : y ∈ e '' V := hy
    have a' := a hyV
    have b' := b hyV
    rw [hes] at a' b'
    obtain ⟨x, hxV, rfl⟩ := hy
    rw [S.symm_apply_apply] at a' b' ⊢
    rw [b', c', ← ENNReal.ofReal_mul (ramerJac_nonneg c s hs A x), mul_comm, a' hxV]
    simp
  -- the weighted measure and its pull-back
  set ρ1 : Measure (FullWeightedHilbert c s) := (γ.restrict (S '' V)).withDensity JM with hρ1
  have hle : Measure.map S.symm ρ1 ≤ γ.restrict V := by
    rw [Measure.le_iff]
    intro A' hA'
    have hpre : MeasurableSet (S.symm ⁻¹' A') := S.symm.continuous.measurable hA'
    rw [Measure.map_apply S.symm.continuous.measurable hA', hρ1, withDensity_apply _ hpre,
      Measure.restrict_restrict hpre, Measure.restrict_apply hA', himg, ← image_inter hSinj]
    exact h2 (A' ∩ V) inter_subset_right
  -- the reverse inequality
  have h4 : ∀ B : Set (FullWeightedHilbert c s), MeasurableSet B → B ⊆ S '' V →
      γ B ≤ ∫⁻ x in S ⁻¹' B, JA x ∂γ := by
    intro B hB hBV
    have hC : MeasurableSet (S ⁻¹' B) := S.continuous.measurable hB
    have hCV : S ⁻¹' B ⊆ V := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hBV hx
      rwa [← hSinj hyx]
    have hmeasg : Measurable fun y => (S ⁻¹' B).indicator JA (S.symm y) :=
      (hJA.indicator hC).comp S.symm.continuous.measurable
    calc γ B = ∫⁻ y in S '' V, B.indicator (fun _ => (1 : ℝ≥0∞)) y ∂γ := by
          rw [lintegral_indicator hB, setLIntegral_const, one_mul, Measure.restrict_apply hB, inter_eq_left.2 hBV]
      _ = ∫⁻ y in S '' V, (S ⁻¹' B).indicator JA (S.symm y) * JM y ∂γ := by
          refine lintegral_congr_ae ((ae_restrict_iff' hSV).2 ?_)
          filter_upwards [hprod] with y hy hyV
          by_cases hyB : y ∈ B
          · have : S.symm y ∈ S ⁻¹' B := by simpa using hyB
            rw [indicator_of_mem hyB, indicator_of_mem this, hy hyV]
          · have : S.symm y ∉ S ⁻¹' B := by simpa using hyB
            rw [indicator_of_notMem hyB, indicator_of_notMem this, zero_mul]
      _ = ∫⁻ y, (S ⁻¹' B).indicator JA (S.symm y) ∂ρ1 := by
          rw [hρ1, lintegral_withDensity_eq_lintegral_mul _ hJM hmeasg]
          exact lintegral_congr fun y => mul_comm _ _
      _ = ∫⁻ x, (S ⁻¹' B).indicator JA x ∂(Measure.map S.symm ρ1) :=
          (lintegral_map (hJA.indicator hC) S.symm.continuous.measurable).symm
      _ ≤ ∫⁻ x, (S ⁻¹' B).indicator JA x ∂(γ.restrict V) := lintegral_mono' hle le_rfl
      _ = ∫⁻ x in S ⁻¹' B, JA x ∂γ := by
          rw [lintegral_indicator hC, Measure.restrict_restrict hC, inter_eq_left.2 hCV]
  have hEq : ∀ B : Set (FullWeightedHilbert c s), MeasurableSet B → B ⊆ S '' V →
      γ B = ∫⁻ x in S ⁻¹' B, JA x ∂γ := fun B hB hBV =>
    le_antisymm (h4 B hB hBV) (h1 B hBV)
  -- the F-identity
  have hmeq : γ.restrict (S '' V) = Measure.map S ((γ.restrict V).withDensity JA) := by
    ext B hB
    rw [Measure.restrict_apply hB, Measure.map_apply S.continuous.measurable hB,
      withDensity_apply _ (S.continuous.measurable hB), Measure.restrict_restrict
      (S.continuous.measurable hB)]
    have : S ⁻¹' B ∩ V = S ⁻¹' (B ∩ S '' V) := by
      ext x; constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, ⟨x, h2, rfl⟩⟩
      · rintro ⟨h1, y, hy, hyx⟩; exact ⟨h1, by rwa [← hSinj hyx]⟩
    rw [this, ← hEq _ (hB.inter hSV) inter_subset_right]
  refine ⟨JA, hJA, hJAae, fun F hF _ _ _ => ?_⟩
  have hFm : Measurable fun y => ENNReal.ofReal (F y) :=
    ENNReal.measurable_ofReal.comp hF.continuous.measurable
  have hFS : Measurable fun x => ENNReal.ofReal (F (S x)) := hFm.comp S.continuous.measurable
  rw [hmeq, lintegral_map hFm S.continuous.measurable,
    lintegral_withDensity_eq_lintegral_mul _ hJA hFS]
  exact lintegral_congr fun x => mul_comm _ _

/-- `P_n P_k (I - P_n) = 0`. -/
theorem headProj_headProj_tailProj (n k : ℕ) (w : ActualCM c) :
    headProj c n (headProj c k (tailProj c n w)) = 0 := by
  apply cmCoord_ext
  intro m
  rw [headProj_apply, cmCoord_cmTrunc, cmCoord_headProj_tailProj]
  split_ifs <;> rfl

/-- **Step 8 for the truncations `P_k A`**, `A = (I - P_n) K̃`. -/
theorem linearSmall_step8_proj (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s →L[ℝ] ActualCM c)
    (κ : ℝ) (hκ : 0 ≤ κ) (hK : ∀ y, ‖K y‖ ≤ κ * ‖y‖) (n : ℕ)
    (hAi : ∀ h : ActualCM c, ‖tailProj c n (K (inclE c s hs h))‖ ≤ (1 / 8) * ‖h‖)
    (ε : ℝ) (hε : 0 < ε)
    (hn : ∀ m ≥ n, ∀ h : ActualCM c, ‖h‖ < 3 * κ * ε + 1 →
      ‖cmToFullWeightedHilbert c s (zero_le_of_half_lt hs) h -
        cmToFullWeightedHilbert c s (zero_le_of_half_lt hs)
          ((cmTrunc c m h : actualCMHead c m) : ActualCM c)‖ < (ε / 2) / 2) (k : ℕ) :
    Step8Concl c s hs (projField k (fun y => tailProj c n (K y))) ε := by
  have hyp : Step8Hyp c s hs (fun y => ((headProj c k).comp ((tailProj c n).comp K)) y) ε := by
    refine step8Hyp_of_tail c s hs ((headProj c k).comp ((tailProj c n).comp K)) n
      (fun y => headProj_headProj_tailProj n k _) (1 / 8) (by norm_num)
      (fun h => (norm_headProj_le c k _).trans (hAi h)) ε (3 * κ * ε + 1) hε
      (fun y hy => ?_) hn
    have h0 : ‖headProj c k (tailProj c n (K y))‖ ≤ ‖tailProj c n (K y)‖ := norm_headProj_le c k _
    have h1 : ‖tailProj c n (K y)‖ ≤ 2 * ‖K y‖ := norm_tailProj_le c n _
    have h2 : ‖K y‖ ≤ κ * ‖y‖ := hK y
    have h3 : κ * ‖y‖ ≤ κ * ε := mul_le_mul_of_nonneg_left hy hκ
    show ‖headProj c k (tailProj c n (K y))‖ < _
    nlinarith
  exact step8Concl_of_hyp c s hs _ hyp

variable (c s)

/-- **D2 step 2: the Jacobi formula for the linear small `S` near `0`**, in the local form
consumed by `map_symm_eq_withDensity_of_local` (Ramer Step 1 (*)), with `T := S`, `V := B_ρ(0)`. -/
theorem linearSmall_jacobi_local (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s →L[ℝ] ActualCM c)
    (T : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (hT : ∀ x, T x = x + inclE c s hs (K x)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (S Pi : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
      (M : FullWeightedHilbert c s →L[ℝ] ActualCM c),
      (∀ h : ActualCM c, ‖tailProj c n (K (inclE c s hs h))‖ ≤ (1 / 8) * ‖h‖) ∧
      (∀ x, S x = x + inclE c s hs (tailProj c n (K x))) ∧
      (∀ x, S.symm x = x + inclE c s hs (M x)) ∧
      (∀ x, M x = -(tailProj c n (K (S.symm x)))) ∧
      (∀ x, Pi x = T (S.symm x)) ∧
      (∀ x, Pi x - x = inclE c s hs (headProj c n (K (S.symm x)))) ∧
      (∀ x, SameTail c s n (Pi x) x) ∧
      ∃ ρ : ℝ, 0 < ρ ∧
        ∃ J : FullWeightedHilbert c s → ℝ≥0∞, Measurable J ∧
          (J =ᵐ[NlsGge.Measure.fullWeightedSequenceGaussian c s]
            fun x => ENNReal.ofReal
              (ramerJac c s hs (fun y => tailProj c n (K y)) x)) ∧
          ∀ F : FullWeightedHilbert c s → ℝ, UniformContinuous F → (∃ C, ∀ y, |F y| ≤ C) →
            (∀ y, 0 ≤ F y) →
            tsupport F ⊆ (S.toHomeomorph : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s) ''
              ball (0 : FullWeightedHilbert c s) ρ →
            ∫⁻ y in (S.toHomeomorph : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s) ''
                ball (0 : FullWeightedHilbert c s) ρ, ENNReal.ofReal (F y)
                ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) =
              ∫⁻ x in ball (0 : FullWeightedHilbert c s) ρ,
                ENNReal.ofReal (F ((S.toHomeomorph : FullWeightedHilbert c s ≃ₜ
                  FullWeightedHilbert c s) x)) * J x
                ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
  have hs0 : 0 ≤ s := zero_le_of_half_lt hs
  obtain ⟨κ0, hκ0, hK0⟩ := K.bound
  set κ := max κ0 0 with hκdef
  have hκ : 0 ≤ κ := le_max_right _ _
  have hK : ∀ y, ‖K y‖ ≤ κ * ‖y‖ := fun y =>
    (hK0 y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ (ActualCM c)
  have hi := cmToFullWeightedHilbert_hs c s hs b
  obtain ⟨n₀, hn₀⟩ := exists_tail_small c s (by linarith : 0 < s) (3 * κ * ε + 1) (ε / 2)
    (by linarith)
  obtain ⟨n, S, Pi, M, hnn, hAi, hS, hSs, hM, hMi, hPi, hPi2⟩ :=
    linear_decomposition_ge (inclE c s hs) b hi K T hT (headProj c)
      (fun n x => norm_cmTrunc_le c n x) (headProj_tendsto c)
      (tailProj c) (tailProj_apply c) n₀
  have hn' : ∀ m ≥ n, ∀ h : ActualCM c, ‖h‖ < 3 * κ * ε + 1 →
      ‖cmToFullWeightedHilbert c s hs0 h - cmToFullWeightedHilbert c s hs0
        ((cmTrunc c m h : actualCMHead c m) : ActualCM c)‖ < (ε / 2) / 2 :=
    fun m hm h hh => hn₀ m (le_trans hnn hm) h hh
  have hfix : ∀ x, SameTail c s n (Pi x) x := by
    intro x m hm
    have e : coordE c s (Pi x - x) m = 0 := by
      rw [hPi2 x]; exact coordE_incl_headProj c s hs0 n (K (S.symm x)) m hm
    rw [coordE_sub] at e
    exact sub_eq_zero.1 e
  obtain ⟨-, hcA⟩ := linearSmall_step8_S c s hs K κ hκ hK n hAi ε hε hn'
  obtain ⟨-, hcM⟩ := linearSmall_step8_Sinv c s hs K S M κ hκ hK n hAi hSs hM hMi ε hε hn'
  have hcAk := fun k => linearSmall_step8_proj hs K κ hκ hK n hAi ε hε hn' k
  refine ⟨n, S, Pi, M, hAi, hS, hSs, hM, hPi, hPi2, hfix, ?_⟩
  -- the radius
  obtain ⟨a0, -, ha0⟩ := (inclE c s hs).bound
  set a : ℝ := max a0 0 with ha
  have ha1 : 0 ≤ a := le_max_right _ _
  have ha2 : ∀ w, ‖inclE c s hs w‖ ≤ a * ‖w‖ := fun w =>
    (ha0 w).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  set C : ℝ := 1 + a * (2 * κ) with hC
  have hC1 : 1 ≤ C := by
    have : 0 ≤ a * (2 * κ) := by positivity
    linarith
  set ρ : ℝ := ε / (2 * (C + 1)) with hρ
  have hρpos : 0 < ρ := by positivity
  have hρε : ρ ≤ ε / 2 := by
    rw [hρ]
    apply div_le_div_of_nonneg_left hε.le (by norm_num) (by linarith)
  have hbound : ∀ x : FullWeightedHilbert c s, ‖x‖ < ρ → ∀ w : ActualCM c,
      ‖w‖ ≤ ‖tailProj c n (K x)‖ → ‖x + inclE c s hs w‖ < ε / 2 := by
    intro x hx w hw
    have h1 : ‖tailProj c n (K x)‖ ≤ 2 * (κ * ‖x‖) :=
      (norm_tailProj_le c n _).trans (by linarith [hK x])
    have h2 : ‖inclE c s hs w‖ ≤ a * ‖w‖ := ha2 w
    have h4 : a * ‖w‖ ≤ a * (2 * (κ * ‖x‖)) :=
      mul_le_mul_of_nonneg_left (hw.trans h1) ha1
    have h5 : ‖x + inclE c s hs w‖ ≤ C * ‖x‖ := by
      calc _ ≤ ‖x‖ + ‖inclE c s hs w‖ := norm_add_le _ _
        _ ≤ ‖x‖ + a * (2 * (κ * ‖x‖)) := by linarith
        _ = C * ‖x‖ := by rw [hC]; ring
    have h6 : C * ‖x‖ < C * ρ := mul_lt_mul_of_pos_left hx (by linarith)
    have h7 : C * ρ < ε / 2 := by
      rw [hρ, mul_div_assoc', div_lt_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    linarith
  have hS' : ∀ x, S x = x + inclE c s hs (tailProj c n (K x)) := hS
  obtain ⟨J, hJm, hJae, hJ⟩ := jacobi_local_of_step8 hs S (fun y => tailProj c n (K y))
    (fun y => M y) ((tailProj c n).comp K).contDiff M.contDiff hS' hSs
    (fun x => by have := hM (S x); rw [S.symm_apply_apply] at this; exact this) hcA hcAk hcM ρ hρpos hρε
    (fun x hx => by
      rw [mem_ball_zero_iff] at hx ⊢
      have h := hbound x hx _ le_rfl
      rw [← hS' x] at h
      exact h)
    (fun k x hx => by
      rw [mem_ball_zero_iff] at hx ⊢
      exact hbound x hx _ ((norm_headProj_le c k _)))
  exact ⟨ρ, hρpos, J, hJm, hJae, hJ⟩

end NlsGge.Ramer

import Mathlib
import NlsGge.Ramer.General.LinearSmallStep8G
import NlsGge.Ramer.General.RamerLemma54G
import NlsGge.Ramer.General.RamerLemma54EventuallyG
import NlsGge.Ramer.RamerStep1Locality

/-!
# D2, part 2: the Jacobi formula for the linear small `S` near `0`, generalized (GE2)

Adapted from `NlsGge/Ramer/LinearSmallJacobiLocal.lean`.  Dictionary: `c, s, hs ↦ S`,
`FullWeightedHilbert c s ↦ S.E`, `ActualCM c ↦ S.H`, `inclE ↦ S.incl`,
`fullWeightedSequenceGaussian c s ↦ S.γE`, `TM c s hs ↦ S.TM`, `ramerJac c s hs ↦ S.ramerJac`,
`headProj c / tailProj c ↦ S.headProj / S.tailProj`, `SameTail c s ↦ S.SameTail`.

The linear equivalence called `S` in the old file is called `Q` here (`S` is the setting).
No isotropy is used: the only norm facts are `‖incl h‖ ≤ a ‖h‖` (any bound `a`, from `incl.bound`)
and `‖P_k h‖ ≤ ‖h‖`, `‖(I-P_n) h‖ ≤ 2‖h‖`.

Ramer (1974) Step 10, two-sided argument, on a small ball `V = B_ρ(0)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer.Gen

/-- Transfer of a.e. statements along `e.symm`, from null-set preservation.
(Old: `NlsGge.Ramer.ae_transfer`.) -/
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

end NlsGge.Ramer.Gen

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer NlsGge.Ramer.Gen

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- From (**)'s null-set clause to null-set preservation of `TM L` on a small set `U`.
(Old: `nullPres_of_concl`.) -/
theorem nullPres_of_concl (L : S.E → S.H)
    {ε : ℝ} (hc : S.Step8Concl L ε) (U : Set S.E)
    (hUb : U ⊆ closedBall (0 : S.E) ε)
    (hUZ : ∀ x ∈ U, x + S.incl (L x) ∈ ball (0 : S.E) (ε / 2)) :
    ∀ N : Set S.E, S.γE N = 0 → S.γE (U ∩ S.TM L ⁻¹' N) = 0 := by
  intro N hN
  have hN' : S.γE (toMeasurable S.γE N) = 0 := by
    rwa [measure_toMeasurable]
  have := hc.2.2 (toMeasurable S.γE N ∩ ball (0 : S.E) (ε / 2))
    ((measurableSet_toMeasurable _ _).inter measurableSet_ball) inter_subset_right
    (measure_mono_null inter_subset_left hN')
  refine measure_mono_null ?_ this
  rintro x ⟨hxU, hxN⟩
  exact ⟨hUb hxU, subset_toMeasurable _ _ hxN, hUZ x hxU⟩

/-- (Old: `ramerJac_nonneg`.) -/
theorem ramerJac_nonneg (M : S.E → S.H) (x : S.E) : 0 ≤ S.ramerJac M x := by
  rw [S.ramerJac_eq]; positivity

/-- (Old: `aemeasurable_ofReal_ramerJac`.) -/
theorem aemeasurable_ofReal_ramerJac (M : S.E → S.H) (hM : ContDiff ℝ 2 M) :
    AEMeasurable (fun x => ENNReal.ofReal (S.ramerJac M x)) S.γE := by
  have h := S.aestronglyMeasurable_ramerJE M (hM.of_le (by norm_num)) (S.ramerDiv M)
    (S.ramerDiv_spec M hM).1
  exact h.aemeasurable.ennreal_ofReal

/-- **Ramer Step 10, two-sided argument, on a ball.**  See the module docstring.
(Old: `jacobi_local_of_step8`.) -/
theorem jacobi_local_of_step8
    (Q : S.E ≃L[ℝ] S.E)
    (A M : S.E → S.H)
    (hAs : ContDiff ℝ 2 A) (hMs : ContDiff ℝ 2 M)
    (hS : ∀ x, Q x = x + S.incl (A x))
    (hSs : ∀ x, Q.symm x = x + S.incl (M x))
    (hGT : ∀ x, M (Q x) = -A x)
    {ε : ℝ} (hcA : S.Step8Concl A ε)
    (hcAk : ∀ k : ℕ, S.Step8Concl (S.projField k A) ε)
    (hcM : S.Step8Concl M ε)
    (ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ ≤ ε / 2)
    (hρS : ∀ x ∈ ball (0 : S.E) ρ, Q x ∈ ball (0 : S.E) (ε / 2))
    (hρk : ∀ k : ℕ, ∀ x ∈ ball (0 : S.E) ρ,
      S.TM (S.projField k A) x ∈ ball (0 : S.E) (ε / 2)) :
    ∃ J : S.E → ℝ≥0∞, Measurable J ∧
      (J =ᵐ[S.γE] fun x => ENNReal.ofReal (S.ramerJac A x)) ∧
      ∀ F : S.E → ℝ, UniformContinuous F → (∃ C, ∀ y, |F y| ≤ C) →
        (∀ y, 0 ≤ F y) →
        tsupport F ⊆ Q '' ball (0 : S.E) ρ →
        ∫⁻ y in Q '' ball (0 : S.E) ρ, ENNReal.ofReal (F y) ∂S.γE =
          ∫⁻ x in ball (0 : S.E) ρ, ENNReal.ofReal (F (Q x)) * J x ∂S.γE := by
  set γ := S.γE with hγ
  set V : Set S.E := ball 0 ρ with hV
  have hVo : IsOpen V := isOpen_ball
  have hVZ : V ⊆ ball (0 : S.E) (ε / 2) :=
    ball_subset_ball hρε
  have hVB : V ⊆ closedBall (0 : S.E) ε := fun x hx =>
    ball_subset_closedBall (hVZ.trans (ball_subset_ball (by linarith)) hx)
  have hSZ : Q '' V ⊆ ball (0 : S.E) (ε / 2) := by
    rintro _ ⟨x, hx, rfl⟩; exact hρS x hx
  -- measurable representatives
  have hmA := S.aemeasurable_ofReal_ramerJac A hAs
  have hmM := S.aemeasurable_ofReal_ramerJac M hMs
  set JA := hmA.mk with hJAdef
  set JM := hmM.mk with hJMdef
  have hJA : Measurable JA := hmA.measurable_mk
  have hJM : Measurable JM := hmM.measurable_mk
  have hJAae : JA =ᵐ[γ] fun x => ENNReal.ofReal (S.ramerJac A x) := hmA.ae_eq_mk.symm
  have hJMae : JM =ᵐ[γ] fun x => ENNReal.ofReal (S.ramerJac M x) := hmM.ae_eq_mk.symm
  -- the measurable equivalence
  let e : S.E ≃ᵐ S.E := Q.toHomeomorph.toMeasurableEquiv
  have he : ∀ x, e x = Q x := fun x => rfl
  have hes : ∀ x, e.symm x = Q.symm x := fun x => rfl
  have hSV : MeasurableSet (Q '' V) := (Q.toHomeomorph.isOpenMap V hVo).measurableSet
  have hSinj : Function.Injective Q := Q.injective
  -- preimage / image under the two maps
  have hpreS : ∀ B : Set S.E,
      (fun y => y + S.incl (A y)) ⁻¹' B = Q ⁻¹' B := by
    intro B; ext x; simp only [mem_preimage, hS x]
  have hpreSs : ∀ B : Set S.E,
      (fun y => y + S.incl (M y)) ⁻¹' B = Q.symm ⁻¹' B := by
    intro B; ext x; simp only [mem_preimage, hSs x]
  have himg : ∀ B : Set S.E, Q.symm ⁻¹' B = Q '' B := by
    intro B; ext x; constructor
    · intro h; exact ⟨Q.symm x, h, Q.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  -- (1)
  have h1 : ∀ B : Set S.E, B ⊆ Q '' V →
      ∫⁻ x in Q ⁻¹' B, JA x ∂γ ≤ γ B := by
    intro B hB
    have hsub : Q ⁻¹' B ⊆ V := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hB hx
      rwa [← hSinj hyx]
    have := hcA.2.1 B (hB.trans hSZ)
    rw [hpreS, inter_eq_right.2 (hsub.trans hVB)] at this
    refine le_trans (le_of_eq ?_) this
    exact lintegral_congr_ae (ae_restrict_of_ae hJAae)
  -- (2)
  have h2 : ∀ A' : Set S.E, A' ⊆ V →
      ∫⁻ y in Q '' A', JM y ∂γ ≤ γ A' := by
    intro A' hA'
    have := hcM.2.1 A' (hA'.trans hVZ)
    rw [hpreSs, himg, inter_eq_right.2 ((image_mono hA').trans (hSZ.trans
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))))] at this
    refine le_trans (le_of_eq ?_) this
    exact lintegral_congr_ae (ae_restrict_of_ae hJMae)
  -- null-set preservation of `Q` on `V` (from `M`)
  have hQ : ∀ N : Set S.E, γ N = 0 → γ (e '' (V ∩ N)) = 0 := by
    intro N hN
    have hN' : γ (toMeasurable γ N) = 0 := by rwa [measure_toMeasurable]
    have := hcM.2.2 (toMeasurable γ N ∩ V) ((measurableSet_toMeasurable _ _).inter
      hVo.measurableSet) (inter_subset_right.trans hVZ)
      (measure_mono_null inter_subset_left hN')
    refine measure_mono_null ?_ this
    rintro _ ⟨x, ⟨hxV, hxN⟩, rfl⟩
    refine ⟨closedBall_subset_closedBall (by linarith : ε / 2 ≤ ε)
      (ball_subset_closedBall (hSZ ⟨x, hxV, rfl⟩)), ?_⟩
    have hx : Q x + S.incl (M (Q x)) = x := by rw [← hSs, Q.symm_apply_apply]
    show Q x + S.incl (M (Q x)) ∈ toMeasurable γ N ∩ V
    rw [hx]
    exact ⟨subset_toMeasurable _ _ hxN, hxV⟩
  -- a.e. identity
  have hd := S.ramerJac_comp_mul_eq_one V hVo A M hAs hMs
    (S.nullPres_of_concl A hcA V hVB (fun x hx => by rw [← hS x]; exact hρS x hx))
    (fun k => S.nullPres_of_concl _ (hcAk k) V hVB (hρk k))
    (fun x _ => by
      have : S.TM A x = Q x := (hS x).symm
      rw [this, hGT])
  have hTMS : S.TM A = Q := funext fun x => (hS x).symm
  rw [hTMS] at hd
  have hT1 := ae_transfer γ e V hQ _ hd
  have hT2 := ae_transfer γ e V hQ _ hJAae
  have hT3 : ∀ᵐ y ∂γ, JM y = ENNReal.ofReal (S.ramerJac M y) := hJMae
  have hprod : ∀ᵐ y ∂γ, y ∈ Q '' V → JA (Q.symm y) * JM y = 1 := by
    filter_upwards [hT1, hT2, hT3] with y a b c' hy
    have hyV : y ∈ e '' V := hy
    have a' := a hyV
    have b' := b hyV
    rw [hes] at a' b'
    obtain ⟨x, hxV, rfl⟩ := hy
    rw [Q.symm_apply_apply] at a' b' ⊢
    rw [b', c', ← ENNReal.ofReal_mul (S.ramerJac_nonneg A x), mul_comm, a' hxV]
    simp
  -- the weighted measure and its pull-back
  set ρ1 : Measure S.E := (γ.restrict (Q '' V)).withDensity JM with hρ1
  have hle : Measure.map Q.symm ρ1 ≤ γ.restrict V := by
    rw [Measure.le_iff]
    intro A' hA'
    have hpre : MeasurableSet (Q.symm ⁻¹' A') := Q.symm.continuous.measurable hA'
    rw [Measure.map_apply Q.symm.continuous.measurable hA', hρ1, withDensity_apply _ hpre,
      Measure.restrict_restrict hpre, Measure.restrict_apply hA', himg, ← image_inter hSinj]
    exact h2 (A' ∩ V) inter_subset_right
  -- the reverse inequality
  have h4 : ∀ B : Set S.E, MeasurableSet B → B ⊆ Q '' V →
      γ B ≤ ∫⁻ x in Q ⁻¹' B, JA x ∂γ := by
    intro B hB hBV
    have hC : MeasurableSet (Q ⁻¹' B) := Q.continuous.measurable hB
    have hCV : Q ⁻¹' B ⊆ V := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hBV hx
      rwa [← hSinj hyx]
    have hmeasg : Measurable fun y => (Q ⁻¹' B).indicator JA (Q.symm y) :=
      (hJA.indicator hC).comp Q.symm.continuous.measurable
    calc γ B = ∫⁻ y in Q '' V, B.indicator (fun _ => (1 : ℝ≥0∞)) y ∂γ := by
          rw [lintegral_indicator hB, setLIntegral_const, one_mul, Measure.restrict_apply hB, inter_eq_left.2 hBV]
      _ = ∫⁻ y in Q '' V, (Q ⁻¹' B).indicator JA (Q.symm y) * JM y ∂γ := by
          refine lintegral_congr_ae ((ae_restrict_iff' hSV).2 ?_)
          filter_upwards [hprod] with y hy hyV
          by_cases hyB : y ∈ B
          · have : Q.symm y ∈ Q ⁻¹' B := by simpa using hyB
            rw [indicator_of_mem hyB, indicator_of_mem this, hy hyV]
          · have : Q.symm y ∉ Q ⁻¹' B := by simpa using hyB
            rw [indicator_of_notMem hyB, indicator_of_notMem this, zero_mul]
      _ = ∫⁻ y, (Q ⁻¹' B).indicator JA (Q.symm y) ∂ρ1 := by
          rw [hρ1, lintegral_withDensity_eq_lintegral_mul _ hJM hmeasg]
          exact lintegral_congr fun y => mul_comm _ _
      _ = ∫⁻ x, (Q ⁻¹' B).indicator JA x ∂(Measure.map Q.symm ρ1) :=
          (lintegral_map (hJA.indicator hC) Q.symm.continuous.measurable).symm
      _ ≤ ∫⁻ x, (Q ⁻¹' B).indicator JA x ∂(γ.restrict V) := lintegral_mono' hle le_rfl
      _ = ∫⁻ x in Q ⁻¹' B, JA x ∂γ := by
          rw [lintegral_indicator hC, Measure.restrict_restrict hC, inter_eq_left.2 hCV]
  have hEq : ∀ B : Set S.E, MeasurableSet B → B ⊆ Q '' V →
      γ B = ∫⁻ x in Q ⁻¹' B, JA x ∂γ := fun B hB hBV =>
    le_antisymm (h4 B hB hBV) (h1 B hBV)
  -- the F-identity
  have hmeq : γ.restrict (Q '' V) = Measure.map Q ((γ.restrict V).withDensity JA) := by
    ext B hB
    rw [Measure.restrict_apply hB, Measure.map_apply Q.continuous.measurable hB,
      withDensity_apply _ (Q.continuous.measurable hB), Measure.restrict_restrict
      (Q.continuous.measurable hB)]
    have : Q ⁻¹' B ∩ V = Q ⁻¹' (B ∩ Q '' V) := by
      ext x; constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, ⟨x, h2, rfl⟩⟩
      · rintro ⟨h1, y, hy, hyx⟩; exact ⟨h1, by rwa [← hSinj hyx]⟩
    rw [this, ← hEq _ (hB.inter hSV) inter_subset_right]
  refine ⟨JA, hJA, hJAae, fun F hF _ _ _ => ?_⟩
  have hFm : Measurable fun y => ENNReal.ofReal (F y) :=
    ENNReal.measurable_ofReal.comp hF.continuous.measurable
  have hFS : Measurable fun x => ENNReal.ofReal (F (Q x)) := hFm.comp Q.continuous.measurable
  rw [hmeq, lintegral_map hFm Q.continuous.measurable,
    lintegral_withDensity_eq_lintegral_mul _ hJA hFS]
  exact lintegral_congr fun x => mul_comm _ _

/-- `P_n P_k (I - P_n) = 0`. (Old: `headProj_headProj_tailProj`.) -/
theorem headProj_headProj_tailProj (n k : ℕ) (w : S.H) :
    S.headProj n (S.headProj k (S.tailProj n w)) = 0 := by
  apply S.hcoord_ext
  intro m
  rw [S.hcoord_headProj, S.hcoord_headProj_tailProj]
  split_ifs <;> rfl

/-- **Step 8 for the truncations `P_k A`**, `A = (I - P_n) K̃`. (Old: `linearSmall_step8_proj`.) -/
theorem linearSmall_step8_proj
    (K : S.E →L[ℝ] S.H)
    (κ : ℝ) (hκ : 0 ≤ κ) (hK : ∀ y, ‖K y‖ ≤ κ * ‖y‖) (n : ℕ)
    (hAi : ∀ h : S.H, ‖S.tailProj n (K (S.incl h))‖ ≤ (1 / 8) * ‖h‖)
    (ε : ℝ) (hε : 0 < ε)
    (hn : ∀ m ≥ n, ∀ h : S.H, ‖h‖ < 3 * κ * ε + 1 →
      ‖S.incl h - S.incl (S.headProj m h)‖ < (ε / 2) / 2) (k : ℕ) :
    S.Step8Concl (S.projField k (fun y => S.tailProj n (K y))) ε := by
  have hyp : S.Step8Hyp (fun y => ((S.headProj k).comp ((S.tailProj n).comp K)) y) ε := by
    refine S.step8Hyp_of_tail ((S.headProj k).comp ((S.tailProj n).comp K)) n
      (fun y => S.headProj_headProj_tailProj n k _) (1 / 8) (by norm_num)
      (fun h => (S.norm_headProj_le k _).trans (hAi h)) ε (3 * κ * ε + 1) hε
      (fun y hy => ?_) hn
    have h0 : ‖S.headProj k (S.tailProj n (K y))‖ ≤ ‖S.tailProj n (K y)‖ :=
      S.norm_headProj_le k _
    have h1 : ‖S.tailProj n (K y)‖ ≤ 2 * ‖K y‖ := S.norm_tailProj_le n _
    have h2 : ‖K y‖ ≤ κ * ‖y‖ := hK y
    have h3 : κ * ‖y‖ ≤ κ * ε := mul_le_mul_of_nonneg_left hy hκ
    show ‖S.headProj k (S.tailProj n (K y))‖ < _
    nlinarith
  exact S.step8Concl_of_hyp _ hyp

/-- **D2 step 2: the Jacobi formula for the linear small `S` near `0`**, in the local form
consumed by `map_symm_eq_withDensity_of_local` (Ramer Step 1 (*)), with `T := Q`, `V := B_ρ(0)`.
(Old: `linearSmall_jacobi_local`.) -/
theorem linearSmall_jacobi_local
    (K : S.E →L[ℝ] S.H)
    (T : S.E ≃L[ℝ] S.E)
    (hT : ∀ x, T x = x + S.incl (K x)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (Q Pi : S.E ≃L[ℝ] S.E)
      (M : S.E →L[ℝ] S.H),
      (∀ h : S.H, ‖S.tailProj n (K (S.incl h))‖ ≤ (1 / 8) * ‖h‖) ∧
      (∀ x, Q x = x + S.incl (S.tailProj n (K x))) ∧
      (∀ x, Q.symm x = x + S.incl (M x)) ∧
      (∀ x, M x = -(S.tailProj n (K (Q.symm x)))) ∧
      (∀ x, Pi x = T (Q.symm x)) ∧
      (∀ x, Pi x - x = S.incl (S.headProj n (K (Q.symm x)))) ∧
      (∀ x, S.SameTail n (Pi x) x) ∧
      ∃ ρ : ℝ, 0 < ρ ∧
        ∃ J : S.E → ℝ≥0∞, Measurable J ∧
          (J =ᵐ[S.γE]
            fun x => ENNReal.ofReal (S.ramerJac (fun y => S.tailProj n (K y)) x)) ∧
          ∀ F : S.E → ℝ, UniformContinuous F → (∃ C, ∀ y, |F y| ≤ C) →
            (∀ y, 0 ≤ F y) →
            tsupport F ⊆ (Q.toHomeomorph : S.E ≃ₜ S.E) '' ball (0 : S.E) ρ →
            ∫⁻ y in (Q.toHomeomorph : S.E ≃ₜ S.E) '' ball (0 : S.E) ρ, ENNReal.ofReal (F y)
                ∂S.γE =
              ∫⁻ x in ball (0 : S.E) ρ,
                ENNReal.ofReal (F ((Q.toHomeomorph : S.E ≃ₜ S.E) x)) * J x
                ∂S.γE := by
  obtain ⟨κ0, hκ0, hK0⟩ := K.bound
  set κ := max κ0 0 with hκdef
  have hκ : 0 ≤ κ := le_max_right _ _
  have hK : ∀ y, ‖K y‖ ≤ κ * ‖y‖ := fun y =>
    (hK0 y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ S.H
  have hi := S.incl_hs b
  obtain ⟨n₀, hn₀⟩ := Gen.exists_tail_small S (3 * κ * ε + 1) (ε / 2) (by linarith)
  obtain ⟨n, Q, Pi, M, hnn, hAi, hS, hSs, hM, hMi, hPi, hPi2⟩ :=
    linear_decomposition_ge S.incl b hi K T hT (S.headProj)
      (fun n x => S.norm_headProj_le n x) S.headProj_tendsto
      (S.tailProj) (S.tailProj_apply) n₀
  have hn' : ∀ m ≥ n, ∀ h : S.H, ‖h‖ < 3 * κ * ε + 1 →
      ‖S.incl h - S.incl (S.headProj m h)‖ < (ε / 2) / 2 :=
    fun m hm h hh => hn₀ m (le_trans hnn hm) h hh
  have hAi' : ∀ h : S.H, ‖S.tailProj n (K (S.incl h))‖ ≤ (1 / 8) * ‖h‖ := hAi
  have hMi' : ∀ h : S.H, ‖M (S.incl h)‖ ≤ ((1 / 8) / (1 - 1 / 8)) * ‖h‖ := hMi
  have hS0 : ∀ x, Q x = x + S.incl (S.tailProj n (K x)) := hS
  have hM0 : ∀ x, M x = -(S.tailProj n (K (Q.symm x))) := hM
  have hPi3 : ∀ x, Pi x - x = S.incl (S.headProj n (K (Q.symm x))) := hPi2
  have hfix : ∀ x, S.SameTail n (Pi x) x := by
    intro x m hm
    have e : S.coord m (Pi x - x) = 0 := by
      rw [hPi3 x]; exact S.coord_incl_headProj n (K (Q.symm x)) m hm
    rw [S.coord_sub] at e
    exact sub_eq_zero.1 e
  obtain ⟨-, hcA⟩ := S.linearSmall_step8_S K κ hκ hK n hAi' ε hε hn'
  obtain ⟨-, hcM⟩ := S.linearSmall_step8_Sinv K Q M κ hκ hK n hAi' hSs hM0 hMi' ε hε hn'
  have hcAk := fun k => S.linearSmall_step8_proj K κ hκ hK n hAi' ε hε hn' k
  refine ⟨n, Q, Pi, M, hAi', hS0, hSs, hM0, hPi, hPi3, hfix, ?_⟩
  -- the radius
  obtain ⟨a0, -, ha0⟩ := S.incl.bound
  set a : ℝ := max a0 0 with ha
  have ha1 : 0 ≤ a := le_max_right _ _
  have ha2 : ∀ w, ‖S.incl w‖ ≤ a * ‖w‖ := fun w =>
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
  have hbound : ∀ x : S.E, ‖x‖ < ρ → ∀ w : S.H,
      ‖w‖ ≤ ‖S.tailProj n (K x)‖ → ‖x + S.incl w‖ < ε / 2 := by
    intro x hx w hw
    have h1 : ‖S.tailProj n (K x)‖ ≤ 2 * (κ * ‖x‖) :=
      (S.norm_tailProj_le n _).trans (by linarith [hK x])
    have h2 : ‖S.incl w‖ ≤ a * ‖w‖ := ha2 w
    have h4 : a * ‖w‖ ≤ a * (2 * (κ * ‖x‖)) :=
      mul_le_mul_of_nonneg_left (hw.trans h1) ha1
    have h5 : ‖x + S.incl w‖ ≤ C * ‖x‖ := by
      calc _ ≤ ‖x‖ + ‖S.incl w‖ := norm_add_le _ _
        _ ≤ ‖x‖ + a * (2 * (κ * ‖x‖)) := by linarith
        _ = C * ‖x‖ := by rw [hC]; ring
    have h6 : C * ‖x‖ < C * ρ := mul_lt_mul_of_pos_left hx (by linarith)
    have h7 : C * ρ < ε / 2 := by
      rw [hρ, mul_div_assoc', div_lt_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    linarith
  obtain ⟨J, hJm, hJae, hJ⟩ := S.jacobi_local_of_step8 Q (fun y => S.tailProj n (K y))
    (fun y => M y) ((S.tailProj n).comp K).contDiff M.contDiff hS0 hSs
    (fun x => by have := hM0 (Q x); rw [Q.symm_apply_apply] at this; exact this) hcA hcAk hcM
    ρ hρpos hρε
    (fun x hx => by
      rw [mem_ball_zero_iff] at hx ⊢
      have h := hbound x hx _ le_rfl
      rw [← hS0 x] at h
      exact h)
    (fun k x hx => by
      rw [mem_ball_zero_iff] at hx ⊢
      exact hbound x hx _ ((S.norm_headProj_le k _)))
  exact ⟨ρ, hρpos, J, hJm, hJae, hJ⟩

end NlsGge.Ramer.General.RamerSetting

import NlsGge.Ramer.General.RamerGeneral
import NlsGge.Ramer.RamerTheorem

/-!
# G5 (i): the `E_s` regression

The old theorems `NlsGge.Ramer.ramer_eq_Ramercommon`, `ramer_eq_Ramercommon_C2` and
`v2_divergence_unique` (about `FullWeightedHilbert c s`, `ActualCM c`,
`fullWeightedSequenceRealization c s`, ...) are re-derived from `RamerSetting.ramer_general`,
`ramer_general_analytic` and `v2_divergence_unique` at `S = RamerSetting.ofCoefficients c s hs`.

`H`, `γ`, `head`, `headPt`, `cmTrunc`, `cylField`, `cylDiv` and `IsClosedDiv` of
`ofCoefficients c s hs` coincide *definitionally* with the project's.  `E` does not: it is the
anisotropic carrier `lp (ℝ²)`.  The transport uses the coordinate preserving linear isometry
`e := fullWeightedEquiv c s hs : FullWeightedHilbert c s ≃ₗᵢ[ℝ] S.E` (propositional
identifications, all proved from `coord_fullWeightedEquiv`):
`e ∘ R_old = S.R`, `γE = γ_old.map e`, `e ∘ inclE = S.incl`, `e ∘ headToE = S.headToE`,
`S.coordE ∘ e = coordE`.  A field `K` on `E_s` becomes `K ∘ e.symm` on `S.E`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer.General

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant NlsGge.Ramer
open NlsGge.Ramer.General.RamerSetting

section Transport

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)
  (hs : (1 : ℝ) / 2 < s)

/-- The field `K ∘ e.symm` on `S.E`. -/
def transportField (K : FullWeightedHilbert c s → ActualCM c) :
    (ofCoefficients c s hs).E → ActualCM c :=
  fun y => K ((fullWeightedEquiv c s hs).symm y)

/-- The Ramer density on `S.E` built from `K ∘ e.symm` and a divergence `δK`. -/
def transportJ (K : FullWeightedHilbert c s → ActualCM c) (δK : (ℤ → ℂ) → ℝ) :
    (ofCoefficients c s hs).E → ℝ := fun x =>
  |det2 ((ofCoefficients c s hs).hsDerivH (transportField c s hs K) x)| *
    Real.exp (-(δK ((ofCoefficients c s hs).coordE x)) - ‖transportField c s hs K x‖ ^ 2 / 2)

theorem transportField_apply (K : FullWeightedHilbert c s → ActualCM c)
    (x : FullWeightedHilbert c s) :
    transportField c s hs K (fullWeightedEquiv c s hs x) = K x := by
  show K ((fullWeightedEquiv c s hs).symm (fullWeightedEquiv c s hs x)) = K x
  rw [LinearIsometryEquiv.symm_apply_apply]

/-- The homeomorphism `e ∘ T ∘ e.symm` of `S.E`. -/
def transportHomeo (T : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s) :
    (ofCoefficients c s hs).E ≃ₜ (ofCoefficients c s hs).E :=
  (fullWeightedEquiv c s hs).toHomeomorph.symm.trans
    (T.trans (fullWeightedEquiv c s hs).toHomeomorph)

theorem transportHomeo_apply (T : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s)
    (y : (ofCoefficients c s hs).E) :
    transportHomeo c s hs T y =
      fullWeightedEquiv c s hs (T ((fullWeightedEquiv c s hs).symm y)) := rfl

theorem transportHomeo_symm_apply (T : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s)
    (y : (ofCoefficients c s hs).E) :
    (transportHomeo c s hs T).symm y =
      fullWeightedEquiv c s hs (T.symm ((fullWeightedEquiv c s hs).symm y)) := rfl

theorem e_inclE (h : ActualCM c) :
    fullWeightedEquiv c s hs (inclE c s hs h) = (ofCoefficients c s hs).incl h :=
  fullWeightedEquiv_cmToFull c s hs h

theorem symm_incl (h : ActualCM c) :
    (fullWeightedEquiv c s hs).symm ((ofCoefficients c s hs).incl h) = inclE c s hs h := by
  rw [← e_inclE c s hs h, LinearIsometryEquiv.symm_apply_apply]

theorem e_realization (z : ℤ → ℂ) :
    fullWeightedEquiv c s hs (NlsGge.Measure.fullWeightedSequenceRealization c s z) =
      (ofCoefficients c s hs).R z :=
  fullWeightedEquiv_realization c s hs z

theorem symm_R (z : ℤ → ℂ) :
    (fullWeightedEquiv c s hs).symm ((ofCoefficients c s hs).R z) =
      NlsGge.Measure.fullWeightedSequenceRealization c s z := by
  rw [← e_realization c s hs z, LinearIsometryEquiv.symm_apply_apply]

theorem e_headToE (N : ℕ) (v : actualCMHead c N) :
    fullWeightedEquiv c s hs (headToE c s N v) = (ofCoefficients c s hs).headToE N v := by
  apply (ofCoefficients c s hs).E_ext; intro n
  rw [coord_fullWeightedEquiv]
  exact ((ofCoefficients c s hs).headToE_coord N v n).symm

theorem truncField_transport (K : FullWeightedHilbert c s → ActualCM c) (N : ℕ) :
    (ofCoefficients c s hs).truncField (transportField c s hs K) N = truncField c s K N := by
  funext v
  show cmTrunc c N (K ((fullWeightedEquiv c s hs).symm
    ((ofCoefficients c s hs).headToE N v))) = cmTrunc c N (K (headToE c s N v))
  rw [← e_headToE c s hs N v, LinearIsometryEquiv.symm_apply_apply]

theorem hsDerivH_transport (K : FullWeightedHilbert c s → ActualCM c)
    (x : FullWeightedHilbert c s) (hK : DifferentiableAt ℝ K x) :
    (ofCoefficients c s hs).hsDerivH (transportField c s hs K) (fullWeightedEquiv c s hs x) =
      hsDerivH c s hs K x := by
  apply HilbertSchmidt.ext; intro v
  have h1 : HasFDerivAt K (fderiv ℝ K x) ((fullWeightedEquiv c s hs).symm
      (fullWeightedEquiv c s hs x)) := by
    rw [LinearIsometryEquiv.symm_apply_apply]; exact hK.hasFDerivAt
  have h2 := h1.comp (fullWeightedEquiv c s hs x)
    ((fullWeightedEquiv c s hs).symm.toContinuousLinearEquiv.hasFDerivAt)
  have h3 : HasFDerivAt (transportField c s hs K)
      ((fderiv ℝ K x).comp (fullWeightedEquiv c s hs).symm.toContinuousLinearEquiv.toContinuousLinearMap)
      (fullWeightedEquiv c s hs x) := h2
  have key : (fderiv ℝ (transportField c s hs K) (fullWeightedEquiv c s hs x))
      ((ofCoefficients c s hs).incl v) = fderiv ℝ K x (inclE c s hs v) := by
    refine (congrArg (fun f : (ofCoefficients c s hs).E →L[ℝ] ActualCM c =>
      f ((ofCoefficients c s hs).incl v)) h3.fderiv).trans ?_
    exact congrArg (fderiv ℝ K x) (symm_incl c s hs v)
  exact (congrArg (fun f => f v) ((ofCoefficients c s hs).hsDerivH_toCLM _ _)).trans
    (key.trans (congrArg (fun f => f v) (hsDerivH_toCLM c s hs K x)).symm)

theorem mem_ball_e (x₀ x : FullWeightedHilbert c s) (r : ℝ) :
    fullWeightedEquiv c s hs x ∈ ball (fullWeightedEquiv c s hs x₀) r ↔ x ∈ ball x₀ r := by
  simp [Metric.mem_ball, LinearIsometryEquiv.dist_map]

theorem closedDiv_transport_fwd (G : FullWeightedHilbert c s → ActualCM c) (η : (ℤ → ℂ) → ℝ)
    (h : IsClosedDiv c
      (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η) :
    (ofCoefficients c s hs).IsClosedDiv
      (fun z => (G ∘ (fullWeightedEquiv c s hs).symm) ((ofCoefficients c s hs).R z)) η := by
  have : (fun z => (G ∘ (fullWeightedEquiv c s hs).symm) ((ofCoefficients c s hs).R z)) =
      fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z) := by
    funext z; simp only [Function.comp, symm_R]
  rw [this]; exact h

theorem closedDiv_transport_bwd (G : (ofCoefficients c s hs).E → ActualCM c) (η : (ℤ → ℂ) → ℝ)
    (h : (ofCoefficients c s hs).IsClosedDiv (fun z => G ((ofCoefficients c s hs).R z)) η) :
    IsClosedDiv c
      (fun z => (G ∘ fullWeightedEquiv c s hs) (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η := by
  have : (fun z => (G ∘ fullWeightedEquiv c s hs)
      (NlsGge.Measure.fullWeightedSequenceRealization c s z)) =
      fun z => G ((ofCoefficients c s hs).R z) := by
    funext z; simp only [Function.comp, e_realization]
  rw [this]; exact h

end Transport

section Regression

variable {lower upper : ℝ}

/-- Any two divergences satisfying clauses 2 and 3 (clause 2 is only needed for `δ₁`) agree
`γ`-a.e.  Re-derived from `RamerSetting.v2_divergence_unique` at `ofCoefficients c s hs`.
(Old: `NlsGge.Ramer.v2_divergence_unique`.) -/
theorem v2_divergence_unique_G (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (K : FullWeightedHilbert c s → ActualCM c)
    (δ₁ δ₂ : (ℤ → ℂ) → ℝ)
    (h2 : ∀ x₀, ∃ r > 0, ∃ (G : FullWeightedHilbert c s → ActualCM c) (η : (ℤ → ℂ) → ℝ),
      Set.EqOn G K (ball x₀ r) ∧
      IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η)
    (h3₁ : ∀ (x₀ : FullWeightedHilbert c s) (r : ℝ) (G : FullWeightedHilbert c s → ActualCM c)
        (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (ball x₀ r) →
        IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η →
        ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
          NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ ball x₀ r → δ₁ z = η z)
    (h3₂ : ∀ (x₀ : FullWeightedHilbert c s) (r : ℝ) (G : FullWeightedHilbert c s → ActualCM c)
        (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (ball x₀ r) →
        IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η →
        ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
          NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ ball x₀ r → δ₂ z = η z) :
    δ₁ =ᵐ[NlsGge.Measure.fullWeightSequenceGaussian c.val] δ₂ := by
  -- fields transported to `S.E`
  have hball : ∀ (y₀ y : (ofCoefficients c s hs).E) (r : ℝ),
      y ∈ ball y₀ r ↔ (fullWeightedEquiv c s hs).symm y ∈ ball ((fullWeightedEquiv c s hs).symm y₀) r := by
    intro y₀ y r
    simp [Metric.mem_ball, LinearIsometryEquiv.dist_map]
  refine (ofCoefficients c s hs).v2_divergence_unique (transportField c s hs K) δ₁ δ₂ ?_ ?_ ?_
  · intro y₀
    obtain ⟨r, hr, G, η, hG, hCD⟩ := h2 ((fullWeightedEquiv c s hs).symm y₀)
    refine ⟨r, hr, G ∘ (fullWeightedEquiv c s hs).symm, η, ?_, closedDiv_transport_fwd c s hs G η hCD⟩
    intro y hy
    exact hG ((hball y₀ y r).1 hy)
  · intro y₀ r G η hG hCD
    have hG' : Set.EqOn (G ∘ (fullWeightedEquiv c s hs)) K (ball ((fullWeightedEquiv c s hs).symm y₀) r) := by
      intro x hx
      have hx' : (fullWeightedEquiv c s hs) x ∈ ball y₀ r := by
        rw [hball]; simpa using hx
      have := hG hx'
      rwa [transportField_apply] at this
    filter_upwards [h3₁ ((fullWeightedEquiv c s hs).symm y₀) r (G ∘ (fullWeightedEquiv c s hs)) η hG' (closedDiv_transport_bwd c s hs G η hCD)]
      with z hz hzm
    refine hz ?_
    rw [← mem_ball_e c s hs ((fullWeightedEquiv c s hs).symm y₀)]
    simpa [e_realization] using hzm
  · intro y₀ r G η hG hCD
    have hG' : Set.EqOn (G ∘ (fullWeightedEquiv c s hs)) K (ball ((fullWeightedEquiv c s hs).symm y₀) r) := by
      intro x hx
      have hx' : (fullWeightedEquiv c s hs) x ∈ ball y₀ r := by
        rw [hball]; simpa using hx
      have := hG hx'
      rwa [transportField_apply] at this
    filter_upwards [h3₂ ((fullWeightedEquiv c s hs).symm y₀) r (G ∘ (fullWeightedEquiv c s hs)) η hG' (closedDiv_transport_bwd c s hs G η hCD)]
      with z hz hzm
    refine hz ?_
    rw [← mem_ball_e c s hs ((fullWeightedEquiv c s hs).symm y₀)]
    simpa [e_realization] using hzm


/-- **Ramer's theorem (v2 `eq:Ramercommon`, `eq:cylindricalcommon`), `C²` form**, re-derived from
`RamerSetting.ramer_general` at `ofCoefficients c s hs`, transported along
`fullWeightedEquiv`.  (Old: `NlsGge.Ramer.ramer_eq_Ramercommon_C2`.) -/
theorem ramer_eq_Ramercommon_C2_G (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s)
    (T : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s)
    (K K' : FullWeightedHilbert c s → ActualCM c)
    (hT : ∀ x, T x = x + inclE c s hs (K x))
    (hTs : ∀ y, T.symm y = y + inclE c s hs (K' y))
    (hK : ContDiff ℝ 2 K) (hK' : ContDiff ℝ 2 K') :
    ∃ δK : (ℤ → ℂ) → ℝ,
      (∀ x₀ : FullWeightedHilbert c s, ∃ r > 0,
        ∃ (G : FullWeightedHilbert c s → ActualCM c) (η : (ℤ → ℂ) → ℝ),
          Set.EqOn G K (ball x₀ r) ∧
          IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η) ∧
      (∀ (x₀ : FullWeightedHilbert c s) (r : ℝ) (G : FullWeightedHilbert c s → ActualCM c)
          (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (ball x₀ r) →
          IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η →
          ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
            NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ ball x₀ r →
              δK z = η z) ∧
      let J : FullWeightedHilbert c s → ℝ := fun x =>
        |det2 (hsDerivH c s hs K x)| *
          Real.exp (-(δK (coordE c s x)) - ‖K x‖ ^ 2 / 2)
      (NlsGge.Measure.fullWeightedSequenceGaussian c s).map T.symm =
          (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
            (fun x => ENNReal.ofReal (J x)) ∧
      (∀ x, 0 < J x) ∧
      Integrable J (NlsGge.Measure.fullWeightedSequenceGaussian c s) ∧
      ∫ x, J x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) = 1 ∧
      TendstoInMeasure (NlsGge.Measure.fullWeightSequenceGaussian c.val)
        (fun N z => finiteRamerDensity (fun v => v + truncField c s K N v) (headPt c N z))
        atTop (fun z => J (NlsGge.Measure.fullWeightedSequenceRealization c s z)) := by
  -- transported data on `S.E`
  have hT' : ∀ y, transportHomeo c s hs T y =
      y + (ofCoefficients c s hs).incl (transportField c s hs K y) := by
    intro y
    rw [transportHomeo_apply, hT, map_add, e_inclE]
    simp [transportField]
  have hTs' : ∀ y, (transportHomeo c s hs T).symm y =
      y + (ofCoefficients c s hs).incl (transportField c s hs K' y) := by
    intro y
    rw [transportHomeo_symm_apply, hTs, map_add, e_inclE]
    simp [transportField]
  have hKc : ContDiff ℝ 2 (transportField c s hs K) :=
    hK.comp (fullWeightedEquiv c s hs).symm.contDiff
  have hKc' : ContDiff ℝ 2 (transportField c s hs K') :=
    hK'.comp (fullWeightedEquiv c s hs).symm.contDiff
  obtain ⟨δK, h2, h3, hrest⟩ :=
    (ofCoefficients c s hs).ramer_general (transportHomeo c s hs T) (transportField c s hs K)
      (transportField c s hs K') hT' hTs' hKc hKc'
  refine ⟨δK, ?_, ?_, ?_⟩
  · intro x₀
    obtain ⟨r, hr, G, η, hG, hCD⟩ := h2 (fullWeightedEquiv c s hs x₀)
    refine ⟨r, hr, G ∘ fullWeightedEquiv c s hs, η, ?_, closedDiv_transport_bwd c s hs G η hCD⟩
    intro x hx
    have := hG ((mem_ball_e c s hs x₀ x r).2 hx)
    rwa [transportField_apply] at this
  · intro x₀ r G η hG hCD
    have hG' : Set.EqOn (G ∘ (fullWeightedEquiv c s hs).symm) (transportField c s hs K)
        (ball (fullWeightedEquiv c s hs x₀) r) := by
      intro y hy
      have hy' : (fullWeightedEquiv c s hs).symm y ∈ ball x₀ r := by
        refine (mem_ball_e c s hs x₀ _ r).1 ?_
        simpa using hy
      exact hG hy'
    filter_upwards [h3 (fullWeightedEquiv c s hs x₀) r (G ∘ (fullWeightedEquiv c s hs).symm) η hG'
      (closedDiv_transport_fwd c s hs G η hCD)] with z hz hzm
    refine hz ?_
    rw [← e_realization]
    exact (mem_ball_e c s hs x₀ _ r).2 hzm
  · intro J
    have hJ : ∀ x, J x = |det2 ((ofCoefficients c s hs).hsDerivH (transportField c s hs K)
        (fullWeightedEquiv c s hs x))| *
        Real.exp (-(δK ((ofCoefficients c s hs).coordE (fullWeightedEquiv c s hs x))) -
          ‖transportField c s hs K (fullWeightedEquiv c s hs x)‖ ^ 2 / 2) := by
      intro x
      simp only [J]
      rw [hsDerivH_transport c s hs K x (hK.differentiable (by norm_num) x),
        coordE_fullWeightedEquiv, transportField_apply]
      rfl
    have hrest' : ((ofCoefficients c s hs).γE.map (transportHomeo c s hs T).symm =
        (ofCoefficients c s hs).γE.withDensity
          (fun x => ENNReal.ofReal (transportJ c s hs K δK x))) ∧
        (∀ x, 0 < transportJ c s hs K δK x) ∧
        Integrable (transportJ c s hs K δK) (ofCoefficients c s hs).γE ∧
        ∫ x, transportJ c s hs K δK x ∂(ofCoefficients c s hs).γE = 1 ∧
        TendstoInMeasure (ofCoefficients c s hs).γ
          (fun N z => finiteRamerDensity
            (fun v => v + (ofCoefficients c s hs).truncField (transportField c s hs K) N v)
            ((ofCoefficients c s hs).headPt N z))
          atTop (fun z => transportJ c s hs K δK ((ofCoefficients c s hs).R z)) := hrest
    obtain ⟨hmap, hpos, hint, hone, hconv⟩ := hrest'
    have hmp : MeasurePreserving (fullWeightedEquiv c s hs)
        (NlsGge.Measure.fullWeightedSequenceGaussian c s) (ofCoefficients c s hs).γE :=
      ⟨(fullWeightedEquiv c s hs).continuous.measurable, (ofCoefficients_γE c s hs).symm⟩
    have hemb : MeasurableEmbedding (fullWeightedEquiv c s hs) :=
      (fullWeightedEquiv c s hs).toHomeomorph.measurableEmbedding
    have hJ' : ∀ x, transportJ c s hs K δK (fullWeightedEquiv c s hs x) = J x :=
      fun x => (hJ x).symm
    have hJc : transportJ c s hs K δK ∘ fullWeightedEquiv c s hs = J := funext hJ'
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · refine Measure.ext fun A hA => ?_
      have hB : MeasurableSet ((fullWeightedEquiv c s hs).symm ⁻¹' A) :=
        (fullWeightedEquiv c s hs).symm.continuous.measurable hA
      have hAB : A = fullWeightedEquiv c s hs ⁻¹' ((fullWeightedEquiv c s hs).symm ⁻¹' A) := by
        ext x; simp
      generalize (fullWeightedEquiv c s hs).symm ⁻¹' A = B at hB hAB
      subst hAB
      have hpre : fullWeightedEquiv c s hs ⁻¹' ((transportHomeo c s hs T).symm ⁻¹' B) =
          T.symm ⁻¹' (fullWeightedEquiv c s hs ⁻¹' B) := by
        ext x
        simp only [Set.mem_preimage, transportHomeo_symm_apply, LinearIsometryEquiv.symm_apply_apply]
      have hL : (Measure.map T.symm (NlsGge.Measure.fullWeightedSequenceGaussian c s))
          (fullWeightedEquiv c s hs ⁻¹' B) =
          (Measure.map (transportHomeo c s hs T).symm (ofCoefficients c s hs).γE) B := by
        rw [Measure.map_apply T.symm.continuous.measurable hA,
          Measure.map_apply (transportHomeo c s hs T).symm.continuous.measurable hB,
          ← hpre, hmp.measure_preimage_emb hemb]
      rw [hL, hmap, withDensity_apply _ hA, withDensity_apply _ hB]
      have := hmp.setLIntegral_comp_preimage_emb hemb (fun y => ENNReal.ofReal (transportJ c s hs K δK y)) B
      rw [← this]
      refine setLIntegral_congr_fun hA (fun x _ => ?_)
      simp only [hJ']
    · intro x; rw [← hJ']; exact hpos _
    · have := (hmp.integrable_comp_emb hemb (g := transportJ c s hs K δK)).2 hint
      rwa [hJc] at this
    · have := (hmp.integral_comp hemb (transportJ c s hs K δK)).trans hone
      simpa only [hJ'] using this
    · have h1 : (fun z => transportJ c s hs K δK ((ofCoefficients c s hs).R z)) =
          fun z => J (NlsGge.Measure.fullWeightedSequenceRealization c s z) := by
        funext z; rw [← e_realization, hJ']
      simp only [truncField_transport] at hconv
      rw [h1] at hconv
      exact hconv


/-- **Ramer's theorem, analytic form** (v2 `prop:gaussiancommon` hypotheses), re-derived from
`ramer_eq_Ramercommon_C2_G` (hence from `RamerSetting.ramer_general`).
(Old: `NlsGge.Ramer.ramer_eq_Ramercommon`.) -/
theorem ramer_eq_Ramercommon_G (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s)
    (T : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s)
    (K K' : FullWeightedHilbert c s → ActualCM c)
    (hT : ∀ x, T x = x + inclE c s hs (K x))
    (hTs : ∀ y, T.symm y = y + inclE c s hs (K' y))
    (hK : AnalyticOnNhd ℝ K Set.univ) (hK' : AnalyticOnNhd ℝ K' Set.univ) :
    ∃ δK : (ℤ → ℂ) → ℝ,
      (∀ x₀ : FullWeightedHilbert c s, ∃ r > 0,
        ∃ (G : FullWeightedHilbert c s → ActualCM c) (η : (ℤ → ℂ) → ℝ),
          Set.EqOn G K (ball x₀ r) ∧
          IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η) ∧
      (∀ (x₀ : FullWeightedHilbert c s) (r : ℝ) (G : FullWeightedHilbert c s → ActualCM c)
          (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (ball x₀ r) →
          IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η →
          ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
            NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ ball x₀ r →
              δK z = η z) ∧
      let J : FullWeightedHilbert c s → ℝ := fun x =>
        |det2 (hsDerivH c s hs K x)| *
          Real.exp (-(δK (coordE c s x)) - ‖K x‖ ^ 2 / 2)
      (NlsGge.Measure.fullWeightedSequenceGaussian c s).map T.symm =
          (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
            (fun x => ENNReal.ofReal (J x)) ∧
      (∀ x, 0 < J x) ∧
      Integrable J (NlsGge.Measure.fullWeightedSequenceGaussian c s) ∧
      ∫ x, J x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) = 1 ∧
      TendstoInMeasure (NlsGge.Measure.fullWeightSequenceGaussian c.val)
        (fun N z => finiteRamerDensity (fun v => v + truncField c s K N v) (headPt c N z))
        atTop (fun z => J (NlsGge.Measure.fullWeightedSequenceRealization c s z)) :=
  ramer_eq_Ramercommon_C2_G c s hs T K K' hT hTs hK.contDiff hK'.contDiff

/-! ### Regression check: the `_G` theorems have *exactly* the old types -/

open Lean Meta Elab Command in
run_cmd do
  let pairs : List (Name × Name) :=
    [(``NlsGge.Ramer.v2_divergence_unique, ``v2_divergence_unique_G),
     (``NlsGge.Ramer.ramer_eq_Ramercommon_C2, ``ramer_eq_Ramercommon_C2_G),
     (``NlsGge.Ramer.ramer_eq_Ramercommon, ``ramer_eq_Ramercommon_G)]
  for (o, n) in pairs do
    let env ← getEnv
    let some oi := env.find? o | throwError "missing {o}"
    let some ni := env.find? n | throwError "missing {n}"
    unless oi.type == ni.type do throwError "TYPE MISMATCH {o} vs {n}"
  logInfo "regression: all three types are syntactically identical"

example : type_of% @NlsGge.Ramer.v2_divergence_unique = type_of% @v2_divergence_unique_G := rfl
example : type_of% @NlsGge.Ramer.ramer_eq_Ramercommon_C2 =
    type_of% @ramer_eq_Ramercommon_C2_G := rfl
example : type_of% @NlsGge.Ramer.ramer_eq_Ramercommon = type_of% @ramer_eq_Ramercommon_G := rfl

end Regression

end NlsGge.Ramer.General

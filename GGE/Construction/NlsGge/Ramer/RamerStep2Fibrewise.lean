import NlsGge.Ramer.CylindricalChangeOfVariables

/-!
# Ramer Step 2 (R2): fibrewise change of variables for tail-parametrized head maps

See `RamerStep2Fibrewise.md`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot

section Finite

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Density ratio of the standard Gaussian. -/
theorem ofReal_gaussianDensity_mul_ramer (T : V → V) (v : V) :
    ENNReal.ofReal |(fderiv ℝ T v).det| * ENNReal.ofReal (finiteGaussianDensity V (T v)) =
      ENNReal.ofReal (finiteRamerDensity T v) * ENNReal.ofReal (finiteGaussianDensity V v) := by
  rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (finiteRamerDensity_nonneg T v)]
  congr 1
  unfold finiteRamerDensity finiteGaussianDensity
  have hexp : Real.exp (-(‖T v‖ ^ 2) / 2) =
      Real.exp (-(‖v‖ ^ 2) / 2) * Real.exp (-(‖T v‖ ^ 2 - ‖v‖ ^ 2) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]; ring

/-- Fibrewise change of variables for the standard Gaussian of `V`. -/
theorem lintegral_image_finiteStdGaussian (T : V → V) (B : Set V) (hB : MeasurableSet B)
    (hd : ∀ v ∈ B, DifferentiableAt ℝ T v) (hinj : Set.InjOn T B)
    (F : V → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ w in T '' B, F w ∂finiteStdGaussian V =
      ∫⁻ v in B, F (T v) * ENNReal.ofReal (finiteRamerDensity T v) ∂finiteStdGaussian V := by
  have hρ : Measurable (fun x : V => ENNReal.ofReal (finiteGaussianDensity V x)) :=
    (continuous_finiteGaussianDensity.measurable).ennreal_ofReal
  have hder : ∀ v ∈ B, HasFDerivWithinAt T (fderiv ℝ T v) B v :=
    fun v hv => (hd v hv).hasFDerivAt.hasFDerivWithinAt
  have hs : MeasurableSet (T '' B) := measurable_image_of_fderivWithin hB hder hinj
  unfold finiteStdGaussian
  rw [restrict_withDensity hs, restrict_withDensity hB,
    lintegral_withDensity_eq_lintegral_mul _ hρ hF,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ hρ
      (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)),
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hB hder hinj]
  refine lintegral_congr (fun v => ?_)
  simp only [Pi.mul_apply]
  rw [← mul_assoc, ofReal_gaussianDensity_mul_ramer T v]
  ring

end Finite


section HeadTail

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (N : ℕ)

theorem tailPt_headRec (v : actualCMHead c N) (t : TailSpace N) :
    tailPt N (headRec c N v t) = t := by
  funext i
  have hi : i.1 ∉ symmetricModes N := fun h => i.2 (by simpa using h)
  simp [tailPt, headRec, hi]

theorem headPt_headRec (v : actualCMHead c N) (t : TailSpace N) :
    headPt c N (headRec c N v t) = v := by
  apply Subtype.ext
  apply cmCoord_ext
  intro n
  rw [cmCoord_headPt]
  by_cases hn : n ∈ symmetricModes N
  · simp [headRec, hn]
  · simp [hn, cmCoord_head_eq_zero c N _ hn]

/-- The fibrewise head action: head `S t (headPt z)`, tail `t = tailPt z` unchanged. -/
def fibreAct (S : TailSpace N → actualCMHead c N → actualCMHead c N) (z : ℤ → ℂ) : ℤ → ℂ :=
  headRec c N (S (tailPt N z) (headPt c N z)) (tailPt N z)

/-- The fibre Ramer density `|det D(S t)(v)| exp(-(‖S t v‖² - ‖v‖²)/2)` at `v = headPt z`,
`t = tailPt z`. -/
def fibreJ (S : TailSpace N → actualCMHead c N → actualCMHead c N) (z : ℤ → ℂ) : ℝ :=
  finiteRamerDensity (S (tailPt N z)) (headPt c N z)

theorem fibreAct_headRec (S : TailSpace N → actualCMHead c N → actualCMHead c N)
    (v : actualCMHead c N) (t : TailSpace N) :
    fibreAct c N S (headRec c N v t) = headRec c N (S t v) t := by
  simp [fibreAct, headPt_headRec, tailPt_headRec]

theorem fibreJ_headRec (S : TailSpace N → actualCMHead c N → actualCMHead c N)
    (v : actualCMHead c N) (t : TailSpace N) :
    fibreJ c N S (headRec c N v t) = finiteRamerDensity (S t) v := by
  simp [fibreJ, headPt_headRec, tailPt_headRec]

theorem measurable_fibreAct (S : TailSpace N → actualCMHead c N → actualCMHead c N)
    (hS : Measurable (Function.uncurry S)) : Measurable (fibreAct c N S) := by
  have h1 : Measurable (fun z : ℤ → ℂ => (S (tailPt N z) (headPt c N z), tailPt N z)) :=
    (hS.comp ((measurable_tailPt N).prodMk (measurable_headPt c N))).prodMk (measurable_tailPt N)
  exact (measurable_headRec c N).comp h1

/-- Fibre Jacobian measurability from joint continuity of `S`. -/
theorem measurable_fibreJ_of_continuous (S : TailSpace N → actualCMHead c N → actualCMHead c N)
    (hS : Continuous (Function.uncurry S)) : Measurable (fibreJ c N S) := by
  have h1 : Measurable (fun p : TailSpace N × actualCMHead c N =>
      finiteRamerDensity (S p.1) p.2) := by
    unfold finiteRamerDensity
    have hd : Measurable (fun p : TailSpace N × actualCMHead c N => (fderiv ℝ (S p.1) p.2).det) :=
      ContinuousLinearMap.continuous_det.measurable.comp
        (measurable_fderiv_with_param ℝ hS)
    have he : Continuous (fun p : TailSpace N × actualCMHead c N =>
        Real.exp (-(‖S p.1 p.2‖ ^ 2 - ‖p.2‖ ^ 2) / 2)) := by
      have : Continuous (fun p : TailSpace N × actualCMHead c N => S p.1 p.2) := hS
      fun_prop
    exact (continuous_abs.measurable.comp hd).mul he.measurable
  exact h1.comp ((measurable_tailPt N).prodMk (measurable_headPt c N))

/-- Tonelli over the head/tail splitting of the full law. -/
theorem lintegral_eq_lintegral_headRec (g : (ℤ → ℂ) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ z, g z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) =
      ∫⁻ t, ∫⁻ v, g (headRec c N v t) ∂(finiteStdGaussian (actualCMHead c N))
        ∂((NlsGge.Measure.fullWeightSequenceGaussian c.val).map (tailPt N)) := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val
  have hP : Measurable (fun z : ℤ → ℂ => (headPt c N z, tailPt N z)) :=
    (measurable_headPt c N).prodMk (measurable_tailPt N)
  have hgR : Measurable (fun p : actualCMHead c N × TailSpace N => g (headRec c N p.1 p.2)) :=
    hg.comp (measurable_headRec c N)
  have h1 : ∫⁻ z, g z ∂γ =
      ∫⁻ p, g (headRec c N p.1 p.2) ∂(γ.map (fun z => (headPt c N z, tailPt N z))) := by
    rw [lintegral_map hgR hP]
    refine lintegral_congr (fun z => ?_)
    simp [headRec_headPt_tailPt]
  rw [h1, map_headPt_tailPt, lintegral_prod_symm _ hgR.aemeasurable]

/-- The image of a fibre. -/
theorem headRec_mem_image_fibreAct_iff (S : TailSpace N → actualCMHead c N → actualCMHead c N)
    (A : Set (ℤ → ℂ)) (v : actualCMHead c N) (t : TailSpace N) :
    headRec c N v t ∈ fibreAct c N S '' A ↔
      v ∈ S t '' {w | headRec c N w t ∈ A} := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    have ht : tailPt N z = t := by
      have := congrArg (tailPt N) hzy
      rwa [tailPt_headRec, fibreAct, tailPt_headRec] at this
    have hv : S t (headPt c N z) = v := by
      have := congrArg (headPt c N) hzy
      rw [headPt_headRec, fibreAct, headPt_headRec, ht] at this
      exact this
    refine ⟨headPt c N z, ?_, hv⟩
    show headRec c N (headPt c N z) t ∈ A
    rw [← ht, headRec_headPt_tailPt]; exact hz
  · rintro ⟨w, hw, rfl⟩
    exact ⟨headRec c N w t, hw, fibreAct_headRec c N S w t⟩

theorem measurableSet_fibre (A : Set (ℤ → ℂ)) (hA : MeasurableSet A) (t : TailSpace N) :
    MeasurableSet {w : actualCMHead c N | headRec c N w t ∈ A} :=
  (measurable_headRec c N).comp (measurable_id.prodMk measurable_const) hA

theorem injOn_fibreAct (S : TailSpace N → actualCMHead c N → actualCMHead c N)
    (A : Set (ℤ → ℂ)) (hinj : ∀ t, Set.InjOn (S t) {w | headRec c N w t ∈ A}) :
    Set.InjOn (fibreAct c N S) A := by
  intro z hz z' hz' h
  have ht : tailPt N z = tailPt N z' := by
    have := congrArg (tailPt N) h
    simpa [fibreAct, tailPt_headRec] using this
  have hv : S (tailPt N z) (headPt c N z) = S (tailPt N z) (headPt c N z') := by
    have := congrArg (headPt c N) h
    rw [fibreAct, fibreAct, headPt_headRec, headPt_headRec, ← ht] at this
    exact this
  have hm : ∀ y ∈ A, headPt c N y ∈ {w | headRec c N w (tailPt N y) ∈ A} := by
    intro y hy; show headRec c N _ _ ∈ A
    rw [headRec_headPt_tailPt]; exact hy
  have hz'' : headPt c N z' ∈ {w | headRec c N w (tailPt N z) ∈ A} := by
    rw [ht]; exact hm z' hz'
  have := hinj (tailPt N z) (hm z hz) hz'' hv
  rw [← headRec_headPt_tailPt c N z, ← headRec_headPt_tailPt c N z', this, ht]

/-- Measurability of the image `fibreAct '' A` (Lusin-Souslin). -/
theorem measurableSet_image_fibreAct (S : TailSpace N → actualCMHead c N → actualCMHead c N)
    (hSm : Measurable (Function.uncurry S)) (A : Set (ℤ → ℂ)) (hA : MeasurableSet A)
    (hinj : ∀ t, Set.InjOn (S t) {w | headRec c N w t ∈ A}) :
    MeasurableSet (fibreAct c N S '' A) :=
  hA.image_of_measurable_injOn (measurable_fibreAct c N S hSm) (injOn_fibreAct c N S A hinj)

/-- **R2: local fibrewise change of variables** for the tail-parametrized head map
`fibreAct S`.  Hypotheses: `S` jointly measurable, fibre Jacobian measurable (automatic when `S`
is jointly continuous, `measurable_fibreJ_of_continuous`), `S t`
differentiable at each point of the fibre `A_t` and injective on `A_t`. -/
theorem lintegral_image_fibreAct (S : TailSpace N → actualCMHead c N → actualCMHead c N)
    (hSm : Measurable (Function.uncurry S)) (hJm : Measurable (fibreJ c N S))
    (A : Set (ℤ → ℂ)) (hA : MeasurableSet A)
    (hdiff : ∀ t (v : actualCMHead c N), headRec c N v t ∈ A → DifferentiableAt ℝ (S t) v)
    (hinj : ∀ t, Set.InjOn (S t) {w | headRec c N w t ∈ A})
    (f : (ℤ → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y in fibreAct c N S '' A, f y ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) =
      ∫⁻ z in A, f (fibreAct c N S z) * ENNReal.ofReal (fibreJ c N S z)
        ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  have hB : MeasurableSet (fibreAct c N S '' A) :=
    measurableSet_image_fibreAct c N S hSm A hA hinj
  rw [← lintegral_indicator hB, ← lintegral_indicator hA,
    lintegral_eq_lintegral_headRec c N _ (hf.indicator hB),
    lintegral_eq_lintegral_headRec c N
      (A.indicator (fun z => f (fibreAct c N S z) * ENNReal.ofReal (fibreJ c N S z)))
      (((hf.comp (measurable_fibreAct c N S hSm)).mul hJm.ennreal_ofReal).indicator hA)]
  refine lintegral_congr (fun t => ?_)
  set At : Set (actualCMHead c N) := {w | headRec c N w t ∈ A} with hAt
  have hAtm : MeasurableSet At := measurableSet_fibre c N A hA t
  have hmeas : Measurable (fun w : actualCMHead c N => f (headRec c N w t)) :=
    hf.comp ((measurable_headRec c N).comp (measurable_id.prodMk measurable_const))
  have hd : ∀ v ∈ At, DifferentiableAt ℝ (S t) v := fun v hv => hdiff t v hv
  have himg : MeasurableSet (S t '' At) :=
    measurable_image_of_fderivWithin hAtm
      (fun x hx => (hd x hx).hasFDerivAt.hasFDerivWithinAt) (hinj t)
  have e1 : ∀ v, (fibreAct c N S '' A).indicator f (headRec c N v t) =
      (S t '' At).indicator (fun w => f (headRec c N w t)) v := by
    intro v
    by_cases hv : v ∈ S t '' At
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem]
      exact (headRec_mem_image_fibreAct_iff c N S A v t).2 hv
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem]
      exact fun h => hv ((headRec_mem_image_fibreAct_iff c N S A v t).1 h)
  have e2 : ∀ v, A.indicator (fun z => f (fibreAct c N S z) * ENNReal.ofReal (fibreJ c N S z))
      (headRec c N v t) =
      At.indicator (fun w => f (headRec c N (S t w) t) *
        ENNReal.ofReal (finiteRamerDensity (S t) w)) v := by
    intro v
    by_cases hv : v ∈ At
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (show headRec c N v t ∈ A from hv),
        fibreAct_headRec, fibreJ_headRec]
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem (show headRec c N v t ∉ A from hv)]
  simp only [e1, e2]
  rw [lintegral_indicator himg, lintegral_indicator hAtm]
  exact lintegral_image_finiteStdGaussian (S t) At hAtm hd (hinj t) _ hmeas

/-- **Ramer `(*)` shape**: for measurable `F ≥ 0` vanishing off `Π(A) = fibreAct '' A`,
`∫_{Π(A)} F dγ = ∫_A F(Π z) J(z) dγ`. -/
theorem lintegral_eq_of_support_subset_image_fibreAct
    (S : TailSpace N → actualCMHead c N → actualCMHead c N)
    (hSm : Measurable (Function.uncurry S)) (hJm : Measurable (fibreJ c N S))
    (A : Set (ℤ → ℂ)) (hA : MeasurableSet A)
    (hdiff : ∀ t (v : actualCMHead c N), headRec c N v t ∈ A → DifferentiableAt ℝ (S t) v)
    (hinj : ∀ t, Set.InjOn (S t) {w | headRec c N w t ∈ A})
    (F : (ℤ → ℂ) → ℝ≥0∞) (hF : Measurable F) (hsupp : Function.support F ⊆ fibreAct c N S '' A) :
    ∫⁻ y, F y ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) =
      ∫⁻ z in A, F (fibreAct c N S z) * ENNReal.ofReal (fibreJ c N S z)
        ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  rw [← lintegral_image_fibreAct c N S hSm hJm A hA hdiff hinj F hF,
    setLIntegral_eq_of_support_subset hsupp]

/-- Inverse of the fibre action when each `S t` is a homeomorphism. -/
def fibreActInv (S : TailSpace N → actualCMHead c N ≃ₜ actualCMHead c N) (z : ℤ → ℂ) : ℤ → ℂ :=
  headRec c N ((S (tailPt N z)).symm (headPt c N z)) (tailPt N z)

theorem fibreAct_fibreActInv (S : TailSpace N → actualCMHead c N ≃ₜ actualCMHead c N)
    (y : ℤ → ℂ) :
    fibreAct c N (fun t => (S t : actualCMHead c N → actualCMHead c N)) (fibreActInv c N S y) = y := by
  have := fibreAct_headRec c N (fun t => (S t : actualCMHead c N → actualCMHead c N))
    ((S (tailPt N y)).symm (headPt c N y)) (tailPt N y)
  simp only [fibreActInv]
  rw [this]
  simp [headRec_headPt_tailPt]

theorem fibreActInv_fibreAct (S : TailSpace N → actualCMHead c N ≃ₜ actualCMHead c N)
    (z : ℤ → ℂ) :
    fibreActInv c N S (fibreAct c N (fun t => (S t : actualCMHead c N → actualCMHead c N)) z) = z := by
  simp only [fibreActInv, fibreAct, headPt_headRec, tailPt_headRec, Homeomorph.symm_apply_apply]
  exact headRec_headPt_tailPt c N z

/-- **Global form** (inverse-pushforward orientation): if every `S t` is a differentiable
homeomorphism of the head, then `(Π⁻¹)_# γ = J γ` with `J = fibreJ`. -/
theorem map_fibreActInv (S : TailSpace N → actualCMHead c N ≃ₜ actualCMHead c N)
    (hSm : Measurable (Function.uncurry
      (fun t => (S t : actualCMHead c N → actualCMHead c N))))
    (hJm : Measurable (fibreJ c N (fun t => (S t : actualCMHead c N → actualCMHead c N))))
    (hd : ∀ t, Differentiable ℝ (S t)) :
    (NlsGge.Measure.fullWeightSequenceGaussian c.val).map (fibreActInv c N S) =
      (NlsGge.Measure.fullWeightSequenceGaussian c.val).withDensity
        (fun z => ENNReal.ofReal
          (fibreJ c N (fun t => (S t : actualCMHead c N → actualCMHead c N)) z)) := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val
  set Φ := fibreAct c N (fun t => (S t : actualCMHead c N → actualCMHead c N)) with hΦ
  have hΦm : Measurable Φ := measurable_fibreAct c N _ hSm
  have hinj : Function.Injective Φ := by
    have := injOn_fibreAct c N (fun t => (S t : actualCMHead c N → actualCMHead c N)) Set.univ
      (fun t => (S t).injective.injOn)
    exact Set.injOn_univ.1 this
  have hΦe : MeasurableEmbedding Φ := hΦm.measurableEmbedding hinj
  have hpre : ∀ B : Set (ℤ → ℂ), fibreActInv c N S ⁻¹' B = Φ '' B := by
    intro B; ext y
    constructor
    · intro hy
      exact ⟨_, hy, fibreAct_fibreActInv c N S y⟩
    · rintro ⟨w, hw, rfl⟩
      show fibreActInv c N S (Φ w) ∈ B
      rw [fibreActInv_fibreAct]; exact hw
  have hΨm : Measurable (fibreActInv c N S) := fun B hB => by
    rw [hpre]; exact hΦe.measurableSet_image.2 hB
  ext B hB
  rw [Measure.map_apply hΨm hB, withDensity_apply _ hB]
  have himg : Φ '' Set.univ = Set.univ := by
    apply Set.eq_univ_of_forall; intro y
    exact ⟨_, trivial, fibreAct_fibreActInv c N S y⟩
  have key := lintegral_image_fibreAct c N (fun t => (S t : actualCMHead c N → actualCMHead c N))
    hSm hJm Set.univ MeasurableSet.univ (fun t v _ => (hd t).differentiableAt)
    (fun t => (S t).injective.injOn)
    ((fibreActInv c N S ⁻¹' B).indicator (fun _ => 1))
    (measurable_const.indicator (hΨm hB))
  rw [← hΦ, himg, Measure.restrict_univ] at key
  rw [lintegral_indicator_const (hΨm hB), one_mul] at key
  rw [key, ← lintegral_indicator hB]
  refine lintegral_congr (fun z => ?_)
  by_cases hz : z ∈ B
  · have : Φ z ∈ fibreActInv c N S ⁻¹' B := by
      show fibreActInv c N S (Φ z) ∈ B
      rw [hΦ, fibreActInv_fibreAct]; exact hz
    simp [Set.indicator_of_mem this, Set.indicator_of_mem hz]
  · have : Φ z ∉ fibreActInv c N S ⁻¹' B := by
      show ¬ fibreActInv c N S (Φ z) ∈ B
      rw [hΦ, fibreActInv_fibreAct]; exact hz
    simp [Set.indicator_of_notMem this, Set.indicator_of_notMem hz]

/-- Regression: for a tail-independent `S`, the inverse fibre action is J2's `headAct S.symm`. -/
theorem fibreActInv_const (S : actualCMHead c N ≃ₜ actualCMHead c N) :
    fibreActInv c N (fun _ => S) = headAct c N (S.symm : actualCMHead c N → actualCMHead c N) := by
  funext z
  rw [headAct_eq_headRec]; rfl

/-- Regression: J2's `map_headActEquiv_symm` recovered from the fibrewise global form. -/
theorem map_headActEquiv_symm_of_fibre (S : actualCMHead c N ≃ₜ actualCMHead c N)
    (hS : Differentiable ℝ S) :
    (NlsGge.Measure.fullWeightSequenceGaussian c.val).map (headActEquiv c N S).symm =
      (NlsGge.Measure.fullWeightSequenceGaussian c.val).withDensity
        (fun z => ENNReal.ofReal
          (finiteRamerDensity (S : actualCMHead c N → actualCMHead c N) (headPt c N z))) := by
  have h := map_fibreActInv c N (fun _ => S)
    (by
      show Measurable (fun p : TailSpace N × actualCMHead c N => S p.2)
      exact S.continuous.measurable.comp measurable_snd)
    (by
      show Measurable (fun z : ℤ → ℂ => finiteRamerDensity (S : actualCMHead c N → actualCMHead c N)
        (headPt c N z))
      exact (measurable_finiteRamerDensity S).comp (measurable_headPt c N))
    (fun _ => hS)
  rw [fibreActInv_const] at h
  exact h

/-- det₂/divergence form of the fibre Jacobian (`finiteRamerDensity_eq_det2_form` fibrewise):
`J(z) = |det₂(I + DK_t(v))| exp(-δK_t(v) - ‖K_t v‖²/2)`, `K_t = S t - id`, `t = tailPt z`,
`v = headPt z`. -/
theorem fibreJ_eq_det2_form (S : TailSpace N → actualCMHead c N → actualCMHead c N)
    (hd : ∀ t, Differentiable ℝ (S t)) (z : ℤ → ℂ) :
    fibreJ c N S z =
      |finiteDet2 (fderiv ℝ (fun y => S (tailPt N z) y - y) (headPt c N z))| *
        Real.exp (-finiteGaussianDivergence (fun y => S (tailPt N z) y - y) (headPt c N z) -
          ‖S (tailPt N z) (headPt c N z) - headPt c N z‖ ^ 2 / 2) :=
  finiteRamerDensity_eq_det2_form _ (hd _) _

end HeadTail

end NlsGge.Ramer

import NlsGge.Ramer.General.CylindricalChangeOfVariablesG
import NlsGge.Ramer.RamerStep2Fibrewise

/-!
# Ramer Step 2 (R2), generalized (GD2): fibrewise change of variables for tail-parametrized
head maps over a `RamerSetting S`

Copy of `NlsGge/Ramer/RamerStep2Fibrewise.lean` with the dictionary of GA5.  The self-map family
of the head is called `T` (the old file calls it `S`).  The `S`-independent finite-dimensional
lemma `lintegral_image_finiteStdGaussian` is reused from the old file.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer NlsGge.Measure

section HeadTail

variable (S : NlsGge.Ramer.General.RamerSetting) (N : ℕ)

theorem tailPt_headRec (v : S.head N) (t : TailSpace N) :
    tailPt N (S.headRec N v t) = t := by
  funext i
  have hi : i.1 ∉ symmetricModes N := fun h => i.2 (by simpa using h)
  simp [tailPt, headRec, hi]

theorem headPt_headRec (v : S.head N) (t : TailSpace N) :
    S.headPt N (S.headRec N v t) = v := by
  apply Subtype.ext
  apply S.hcoord_ext
  intro n
  rw [hcoord_headPt]
  by_cases hn : n ∈ symmetricModes N
  · simp [headRec, hn]
  · simp [hn, S.hcoord_head_eq_zero N _ hn]

/-- The fibrewise head action: head `T t (headPt z)`, tail `t = tailPt z` unchanged. -/
def fibreAct (T : TailSpace N → S.head N → S.head N) (z : ℤ → ℂ) : ℤ → ℂ :=
  S.headRec N (T (tailPt N z) (S.headPt N z)) (tailPt N z)

/-- The fibre Ramer density `|det D(T t)(v)| exp(-(‖T t v‖² - ‖v‖²)/2)` at `v = headPt z`,
`t = tailPt z`. -/
def fibreJ (T : TailSpace N → S.head N → S.head N) (z : ℤ → ℂ) : ℝ :=
  finiteRamerDensity (T (tailPt N z)) (S.headPt N z)

theorem fibreAct_headRec (T : TailSpace N → S.head N → S.head N)
    (v : S.head N) (t : TailSpace N) :
    S.fibreAct N T (S.headRec N v t) = S.headRec N (T t v) t := by
  simp [fibreAct, headPt_headRec, tailPt_headRec]

theorem fibreJ_headRec (T : TailSpace N → S.head N → S.head N)
    (v : S.head N) (t : TailSpace N) :
    S.fibreJ N T (S.headRec N v t) = finiteRamerDensity (T t) v := by
  simp [fibreJ, headPt_headRec, tailPt_headRec]

theorem measurable_fibreAct (T : TailSpace N → S.head N → S.head N)
    (hS : Measurable (Function.uncurry T)) : Measurable (S.fibreAct N T) := by
  have h1 : Measurable (fun z : ℤ → ℂ => (T (tailPt N z) (S.headPt N z), tailPt N z)) :=
    (hS.comp ((measurable_tailPt N).prodMk (S.measurable_headPt N))).prodMk (measurable_tailPt N)
  exact (S.measurable_headRec N).comp h1

/-- Fibre Jacobian measurability from joint continuity of `T`. -/
theorem measurable_fibreJ_of_continuous (T : TailSpace N → S.head N → S.head N)
    (hS : Continuous (Function.uncurry T)) : Measurable (S.fibreJ N T) := by
  have h1 : Measurable (fun p : TailSpace N × S.head N =>
      finiteRamerDensity (T p.1) p.2) := by
    unfold finiteRamerDensity
    have hd : Measurable (fun p : TailSpace N × S.head N => (fderiv ℝ (T p.1) p.2).det) :=
      ContinuousLinearMap.continuous_det.measurable.comp
        (measurable_fderiv_with_param ℝ hS)
    have he : Continuous (fun p : TailSpace N × S.head N =>
        Real.exp (-(‖T p.1 p.2‖ ^ 2 - ‖p.2‖ ^ 2) / 2)) := by
      have : Continuous (fun p : TailSpace N × S.head N => T p.1 p.2) := hS
      fun_prop
    exact (continuous_abs.measurable.comp hd).mul he.measurable
  exact h1.comp ((measurable_tailPt N).prodMk (S.measurable_headPt N))

/-- Tonelli over the head/tail splitting of the full law. -/
theorem lintegral_eq_lintegral_headRec (g : (ℤ → ℂ) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ z, g z ∂(S.γ) =
      ∫⁻ t, ∫⁻ v, g (S.headRec N v t) ∂(finiteStdGaussian (S.head N))
        ∂((S.γ).map (tailPt N)) := by
  set γ := S.γ
  have hP : Measurable (fun z : ℤ → ℂ => (S.headPt N z, tailPt N z)) :=
    (S.measurable_headPt N).prodMk (measurable_tailPt N)
  have hgR : Measurable (fun p : S.head N × TailSpace N => g (S.headRec N p.1 p.2)) :=
    hg.comp (S.measurable_headRec N)
  have h1 : ∫⁻ z, g z ∂γ =
      ∫⁻ p, g (S.headRec N p.1 p.2) ∂(γ.map (fun z => (S.headPt N z, tailPt N z))) := by
    rw [lintegral_map hgR hP]
    refine lintegral_congr (fun z => ?_)
    simp [headRec_headPt_tailPt]
  rw [h1, map_headPt_tailPt, lintegral_prod_symm _ hgR.aemeasurable]

/-- The image of a fibre. -/
theorem headRec_mem_image_fibreAct_iff (T : TailSpace N → S.head N → S.head N)
    (A : Set (ℤ → ℂ)) (v : S.head N) (t : TailSpace N) :
    S.headRec N v t ∈ S.fibreAct N T '' A ↔
      v ∈ T t '' {w | S.headRec N w t ∈ A} := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    have ht : tailPt N z = t := by
      have := congrArg (tailPt N) hzy
      rwa [tailPt_headRec, fibreAct, tailPt_headRec] at this
    have hv : T t (S.headPt N z) = v := by
      have := congrArg (S.headPt N) hzy
      rw [headPt_headRec, fibreAct, headPt_headRec, ht] at this
      exact this
    refine ⟨S.headPt N z, ?_, hv⟩
    show S.headRec N (S.headPt N z) t ∈ A
    rw [← ht, headRec_headPt_tailPt]; exact hz
  · rintro ⟨w, hw, rfl⟩
    exact ⟨S.headRec N w t, hw, S.fibreAct_headRec N T w t⟩

theorem measurableSet_fibre (A : Set (ℤ → ℂ)) (hA : MeasurableSet A) (t : TailSpace N) :
    MeasurableSet {w : S.head N | S.headRec N w t ∈ A} :=
  (S.measurable_headRec N).comp (measurable_id.prodMk measurable_const) hA

theorem injOn_fibreAct (T : TailSpace N → S.head N → S.head N)
    (A : Set (ℤ → ℂ)) (hinj : ∀ t, Set.InjOn (T t) {w | S.headRec N w t ∈ A}) :
    Set.InjOn (S.fibreAct N T) A := by
  intro z hz z' hz' h
  have ht : tailPt N z = tailPt N z' := by
    have := congrArg (tailPt N) h
    simpa [fibreAct, tailPt_headRec] using this
  have hv : T (tailPt N z) (S.headPt N z) = T (tailPt N z) (S.headPt N z') := by
    have := congrArg (S.headPt N) h
    rw [fibreAct, fibreAct, headPt_headRec, headPt_headRec, ← ht] at this
    exact this
  have hm : ∀ y ∈ A, S.headPt N y ∈ {w | S.headRec N w (tailPt N y) ∈ A} := by
    intro y hy; show S.headRec N _ _ ∈ A
    rw [headRec_headPt_tailPt]; exact hy
  have hz'' : S.headPt N z' ∈ {w | S.headRec N w (tailPt N z) ∈ A} := by
    rw [ht]; exact hm z' hz'
  have := hinj (tailPt N z) (hm z hz) hz'' hv
  rw [← S.headRec_headPt_tailPt N z, ← S.headRec_headPt_tailPt N z', this, ht]

/-- Measurability of the image `fibreAct '' A` (Lusin-Souslin). -/
theorem measurableSet_image_fibreAct (T : TailSpace N → S.head N → S.head N)
    (hSm : Measurable (Function.uncurry T)) (A : Set (ℤ → ℂ)) (hA : MeasurableSet A)
    (hinj : ∀ t, Set.InjOn (T t) {w | S.headRec N w t ∈ A}) :
    MeasurableSet (S.fibreAct N T '' A) :=
  hA.image_of_measurable_injOn (S.measurable_fibreAct N T hSm) (S.injOn_fibreAct N T A hinj)

/-- **R2: local fibrewise change of variables** for the tail-parametrized head map
`fibreAct T`.  Hypotheses: `T` jointly measurable, fibre Jacobian measurable (automatic when `T`
is jointly continuous, `measurable_fibreJ_of_continuous`), `T t`
differentiable at each point of the fibre `A_t` and injective on `A_t`. -/
theorem lintegral_image_fibreAct (T : TailSpace N → S.head N → S.head N)
    (hSm : Measurable (Function.uncurry T)) (hJm : Measurable (S.fibreJ N T))
    (A : Set (ℤ → ℂ)) (hA : MeasurableSet A)
    (hdiff : ∀ t (v : S.head N), S.headRec N v t ∈ A → DifferentiableAt ℝ (T t) v)
    (hinj : ∀ t, Set.InjOn (T t) {w | S.headRec N w t ∈ A})
    (f : (ℤ → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y in S.fibreAct N T '' A, f y ∂(S.γ) =
      ∫⁻ z in A, f (S.fibreAct N T z) * ENNReal.ofReal (S.fibreJ N T z)
        ∂(S.γ) := by
  have hB : MeasurableSet (S.fibreAct N T '' A) :=
    S.measurableSet_image_fibreAct N T hSm A hA hinj
  rw [← lintegral_indicator hB, ← lintegral_indicator hA,
    S.lintegral_eq_lintegral_headRec N _ (hf.indicator hB),
    S.lintegral_eq_lintegral_headRec N
      (A.indicator (fun z => f (S.fibreAct N T z) * ENNReal.ofReal (S.fibreJ N T z)))
      (((hf.comp (S.measurable_fibreAct N T hSm)).mul hJm.ennreal_ofReal).indicator hA)]
  refine lintegral_congr (fun t => ?_)
  set At : Set (S.head N) := {w | S.headRec N w t ∈ A} with hAt
  have hAtm : MeasurableSet At := S.measurableSet_fibre N A hA t
  have hmeas : Measurable (fun w : S.head N => f (S.headRec N w t)) :=
    hf.comp ((S.measurable_headRec N).comp (measurable_id.prodMk measurable_const))
  have hd : ∀ v ∈ At, DifferentiableAt ℝ (T t) v := fun v hv => hdiff t v hv
  have himg : MeasurableSet (T t '' At) :=
    measurable_image_of_fderivWithin hAtm
      (fun x hx => (hd x hx).hasFDerivAt.hasFDerivWithinAt) (hinj t)
  have e1 : ∀ v, (S.fibreAct N T '' A).indicator f (S.headRec N v t) =
      (T t '' At).indicator (fun w => f (S.headRec N w t)) v := by
    intro v
    by_cases hv : v ∈ T t '' At
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem]
      exact (S.headRec_mem_image_fibreAct_iff N T A v t).2 hv
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem]
      exact fun h => hv ((S.headRec_mem_image_fibreAct_iff N T A v t).1 h)
  have e2 : ∀ v, A.indicator (fun z => f (S.fibreAct N T z) * ENNReal.ofReal (S.fibreJ N T z))
      (S.headRec N v t) =
      At.indicator (fun w => f (S.headRec N (T t w) t) *
        ENNReal.ofReal (finiteRamerDensity (T t) w)) v := by
    intro v
    by_cases hv : v ∈ At
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (show S.headRec N v t ∈ A from hv),
        fibreAct_headRec, fibreJ_headRec]
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem (show S.headRec N v t ∉ A from hv)]
  simp only [e1, e2]
  rw [lintegral_indicator himg, lintegral_indicator hAtm]
  exact lintegral_image_finiteStdGaussian (T t) At hAtm hd (hinj t) _ hmeas

/-- **Ramer `(*)` shape**: for measurable `F ≥ 0` vanishing off `Π(A) = fibreAct '' A`,
`∫_{Π(A)} F dγ = ∫_A F(Π z) J(z) dγ`. -/
theorem lintegral_eq_of_support_subset_image_fibreAct
    (T : TailSpace N → S.head N → S.head N)
    (hSm : Measurable (Function.uncurry T)) (hJm : Measurable (S.fibreJ N T))
    (A : Set (ℤ → ℂ)) (hA : MeasurableSet A)
    (hdiff : ∀ t (v : S.head N), S.headRec N v t ∈ A → DifferentiableAt ℝ (T t) v)
    (hinj : ∀ t, Set.InjOn (T t) {w | S.headRec N w t ∈ A})
    (F : (ℤ → ℂ) → ℝ≥0∞) (hF : Measurable F) (hsupp : Function.support F ⊆ S.fibreAct N T '' A) :
    ∫⁻ y, F y ∂(S.γ) =
      ∫⁻ z in A, F (S.fibreAct N T z) * ENNReal.ofReal (S.fibreJ N T z)
        ∂(S.γ) := by
  rw [← S.lintegral_image_fibreAct N T hSm hJm A hA hdiff hinj F hF,
    setLIntegral_eq_of_support_subset hsupp]

/-- Inverse of the fibre action when each `T t` is a homeomorphism. -/
def fibreActInv (T : TailSpace N → S.head N ≃ₜ S.head N) (z : ℤ → ℂ) : ℤ → ℂ :=
  S.headRec N ((T (tailPt N z)).symm (S.headPt N z)) (tailPt N z)

theorem fibreAct_fibreActInv (T : TailSpace N → S.head N ≃ₜ S.head N)
    (y : ℤ → ℂ) :
    S.fibreAct N (fun t => (T t : S.head N → S.head N)) (S.fibreActInv N T y) = y := by
  have := S.fibreAct_headRec N (fun t => (T t : S.head N → S.head N))
    ((T (tailPt N y)).symm (S.headPt N y)) (tailPt N y)
  simp only [fibreActInv]
  rw [this]
  simp [headRec_headPt_tailPt]

theorem fibreActInv_fibreAct (T : TailSpace N → S.head N ≃ₜ S.head N)
    (z : ℤ → ℂ) :
    S.fibreActInv N T (S.fibreAct N (fun t => (T t : S.head N → S.head N)) z) = z := by
  simp only [fibreActInv, fibreAct, headPt_headRec, tailPt_headRec, Homeomorph.symm_apply_apply]
  exact S.headRec_headPt_tailPt N z

/-- **Global form** (inverse-pushforward orientation): if every `T t` is a differentiable
homeomorphism of the head, then `(Π⁻¹)_# γ = J γ` with `J = fibreJ`. -/
theorem map_fibreActInv (T : TailSpace N → S.head N ≃ₜ S.head N)
    (hSm : Measurable (Function.uncurry
      (fun t => (T t : S.head N → S.head N))))
    (hJm : Measurable (S.fibreJ N (fun t => (T t : S.head N → S.head N))))
    (hd : ∀ t, Differentiable ℝ (T t)) :
    (S.γ).map (S.fibreActInv N T) =
      (S.γ).withDensity
        (fun z => ENNReal.ofReal
          (S.fibreJ N (fun t => (T t : S.head N → S.head N)) z)) := by
  set γ := S.γ
  set Φ := S.fibreAct N (fun t => (T t : S.head N → S.head N)) with hΦ
  have hΦm : Measurable Φ := S.measurable_fibreAct N _ hSm
  have hinj : Function.Injective Φ := by
    have := S.injOn_fibreAct N (fun t => (T t : S.head N → S.head N)) Set.univ
      (fun t => (T t).injective.injOn)
    exact Set.injOn_univ.1 this
  have hΦe : MeasurableEmbedding Φ := hΦm.measurableEmbedding hinj
  have hpre : ∀ B : Set (ℤ → ℂ), S.fibreActInv N T ⁻¹' B = Φ '' B := by
    intro B; ext y
    constructor
    · intro hy
      exact ⟨_, hy, S.fibreAct_fibreActInv N T y⟩
    · rintro ⟨w, hw, rfl⟩
      show S.fibreActInv N T (Φ w) ∈ B
      rw [fibreActInv_fibreAct]; exact hw
  have hΨm : Measurable (S.fibreActInv N T) := fun B hB => by
    rw [hpre]; exact hΦe.measurableSet_image.2 hB
  ext B hB
  rw [Measure.map_apply hΨm hB, withDensity_apply _ hB]
  have himg : Φ '' Set.univ = Set.univ := by
    apply Set.eq_univ_of_forall; intro y
    exact ⟨_, trivial, S.fibreAct_fibreActInv N T y⟩
  have key := S.lintegral_image_fibreAct N (fun t => (T t : S.head N → S.head N))
    hSm hJm Set.univ MeasurableSet.univ (fun t v _ => (hd t).differentiableAt)
    (fun t => (T t).injective.injOn)
    ((S.fibreActInv N T ⁻¹' B).indicator (fun _ => 1))
    (measurable_const.indicator (hΨm hB))
  rw [← hΦ, himg, Measure.restrict_univ] at key
  rw [lintegral_indicator_const (hΨm hB), one_mul] at key
  rw [key, ← lintegral_indicator hB]
  refine lintegral_congr (fun z => ?_)
  by_cases hz : z ∈ B
  · have : Φ z ∈ S.fibreActInv N T ⁻¹' B := by
      show S.fibreActInv N T (Φ z) ∈ B
      rw [hΦ, fibreActInv_fibreAct]; exact hz
    simp [Set.indicator_of_mem this, Set.indicator_of_mem hz]
  · have : Φ z ∉ S.fibreActInv N T ⁻¹' B := by
      show ¬ S.fibreActInv N T (Φ z) ∈ B
      rw [hΦ, fibreActInv_fibreAct]; exact hz
    simp [Set.indicator_of_notMem this, Set.indicator_of_notMem hz]

/-- Regression: for a tail-independent `T`, the inverse fibre action is J2's `headAct T.symm`. -/
theorem fibreActInv_const (T : S.head N ≃ₜ S.head N) :
    S.fibreActInv N (fun _ => T) = S.headAct N (T.symm : S.head N → S.head N) := by
  funext z
  rw [headAct_eq_headRec]; rfl

/-- Regression: J2's `map_headActEquiv_symm` recovered from the fibrewise global form. -/
theorem map_headActEquiv_symm_of_fibre (T : S.head N ≃ₜ S.head N)
    (hS : Differentiable ℝ T) :
    (S.γ).map (S.headActEquiv N T).symm =
      (S.γ).withDensity
        (fun z => ENNReal.ofReal
          (finiteRamerDensity (T : S.head N → S.head N) (S.headPt N z))) := by
  have h := S.map_fibreActInv N (fun _ => T)
    (by
      show Measurable (fun p : TailSpace N × S.head N => T p.2)
      exact T.continuous.measurable.comp measurable_snd)
    (by
      show Measurable (fun z : ℤ → ℂ => finiteRamerDensity (T : S.head N → S.head N)
        (S.headPt N z))
      exact (measurable_finiteRamerDensity T).comp (S.measurable_headPt N))
    (fun _ => hS)
  rw [fibreActInv_const] at h
  exact h

/-- det₂/divergence form of the fibre Jacobian (`finiteRamerDensity_eq_det2_form` fibrewise):
`J(z) = |det₂(I + DK_t(v))| exp(-δK_t(v) - ‖K_t v‖²/2)`, `K_t = T t - id`, `t = tailPt z`,
`v = headPt z`. -/
theorem fibreJ_eq_det2_form (T : TailSpace N → S.head N → S.head N)
    (hd : ∀ t, Differentiable ℝ (T t)) (z : ℤ → ℂ) :
    S.fibreJ N T z =
      |finiteDet2 (fderiv ℝ (fun y => T (tailPt N z) y - y) (S.headPt N z))| *
        Real.exp (-finiteGaussianDivergence (fun y => T (tailPt N z) y - y) (S.headPt N z) -
          ‖T (tailPt N z) (S.headPt N z) - S.headPt N z‖ ^ 2 / 2) :=
  finiteRamerDensity_eq_det2_form _ (hd _) _

end HeadTail

end NlsGge.Ramer.General.RamerSetting

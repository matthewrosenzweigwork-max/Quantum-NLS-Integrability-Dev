import NlsGge.Ramer.RamerStep2Fibrewise
import NlsGge.Ramer.SpaceTransfer
import NlsGge.Ramer.LinearDecomposition

/-!
# FB: bridge from `E`-maps that fix the tail to the fibre coordinates of R2

See `FibreBridge.md`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot

/-- The realization map `R : (ℤ → ℂ) → E_s` (`realE c s`). -/
local notation "realE" => NlsGge.Measure.fullWeightedSequenceRealization

section Bridge

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (n : ℕ)


open Classical in
/-- The fibre maps of `Φ : E → E`: for a summable tail the head of `Φ (R (headRec v t))`,
otherwise the identity. -/
def fibreMapOf (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s) (t : TailSpace n)
    (v : actualCMHead c n) : actualCMHead c n :=
  if WeightedSquareSummable (sourceRate c) s (headRec c n v t) then
    headPt c n (coordE c s (Φ (realE c s (headRec c n v t))))
  else v

/-- The tail `t` is summable (equivalently `headRec v t` is summable for every head `v`). -/
def TailSummable (t : TailSpace n) : Prop :=
  WeightedSquareSummable (sourceRate c) s (headRec c n 0 t)

theorem coordE_realE (z : ℤ → ℂ) (hz : WeightedSquareSummable (sourceRate c) s z) :
    coordE c s (realE c s z) = z := by
  funext m
  exact NlsGge.Measure.fullWeightedSequenceRealization_apply c s z hz m

theorem realE_coordE (x : FullWeightedHilbert c s) : realE c s (coordE c s x) = x :=
  realization_coordE c s x

theorem coordE_injective : Function.Injective (coordE c s) := fun x y h => by
  rw [← realization_coordE c s x, ← realization_coordE c s y, h]

theorem coordE_smul (r : ℝ) (x : FullWeightedHilbert c s) (m : ℤ) :
    coordE c s (r • x) m = (r : ℂ) * coordE c s x m := rfl

theorem coordE_zero (m : ℤ) : coordE c s (0 : FullWeightedHilbert c s) m = 0 := rfl

/-- `headToE` has the head coordinates and zero tail. -/
theorem coordE_headToE (v : actualCMHead c n) (m : ℤ) :
    coordE c s (headToE c s n v) m = cmCoord (v : ActualCM c) m := rfl

theorem headRec_apply_mem (v : actualCMHead c n) (t : TailSpace n) {m : ℤ}
    (hm : m ∈ symmetricModes n) : headRec c n v t m = cmCoord (v : ActualCM c) m := by
  simp [headRec, hm]

theorem headRec_apply_not_mem (v : actualCMHead c n) (t : TailSpace n) {m : ℤ}
    (hm : m ∉ symmetricModes n) :
    headRec c n v t m = t ⟨m, by simpa using hm⟩ := by
  simp [headRec, hm]

theorem headRec_eq_add (v : actualCMHead c n) (t : TailSpace n) (m : ℤ) :
    headRec c n v t m = headRec c n 0 t m + coordE c s (headToE c s n v) m := by
  by_cases hm : m ∈ symmetricModes n
  · rw [headRec_apply_mem c n _ _ hm, headRec_apply_mem c n _ _ hm, coordE_headToE]
    have : cmCoord (((0 : actualCMHead c n)) : ActualCM c) m = 0 := rfl
    rw [this, zero_add]
  · rw [headRec_apply_not_mem c n _ _ hm, headRec_apply_not_mem c n _ _ hm,
      coordE_headToE, cmCoord_head_eq_zero c n v hm, add_zero]

theorem coordE_neg (x : FullWeightedHilbert c s) (m : ℤ) :
    coordE c s (-x) m = -coordE c s x m := rfl

/-- Summability of `headRec v t` does not depend on `v`. -/
theorem summable_headRec_iff (v : actualCMHead c n) (t : TailSpace n) :
    WeightedSquareSummable (sourceRate c) s (headRec c n v t) ↔ TailSummable c s n t := by
  have key : ∀ (v : actualCMHead c n) (t : TailSpace n),
      TailSummable c s n t → WeightedSquareSummable (sourceRate c) s (headRec c n v t) := by
    intro v t ht
    have h : headRec c n v t = coordE c s (realE c s (headRec c n 0 t) + headToE c s n v) := by
      funext m
      rw [headRec_eq_add c s n v t m, coordE_add, coordE_realE c s _ ht]
    rw [h]
    exact weightedSquareSummable_coordE c s _
  refine ⟨fun h => ?_, key v t⟩
  have h0 : headRec c n 0 t = coordE c s (realE c s (headRec c n v t) + headToE c s n (-v)) := by
    funext m
    rw [coordE_add, coordE_realE c s _ h]
    have := headRec_eq_add c s n v t m
    rw [map_neg, coordE_neg, this]; ring
  rw [TailSummable, h0]
  exact weightedSquareSummable_coordE c s _

/-- The base point `R (headRec 0 t)` of the affine slice over the tail `t`. -/
def tailBase (t : TailSpace n) : FullWeightedHilbert c s := realE c s (headRec c n 0 t)

theorem realE_headRec (v : actualCMHead c n) (t : TailSpace n) (ht : TailSummable c s n t) :
    realE c s (headRec c n v t) = tailBase c s n t + headToE c s n v := by
  apply coordE_injective c s
  funext m
  rw [coordE_add, coordE_realE c s _ ((summable_headRec_iff c s n v t).2 ht), tailBase,
    coordE_realE c s _ ht, headRec_eq_add c s n v t m]

theorem headRec_injective_left {v v' : actualCMHead c n} {t : TailSpace n}
    (h : headRec c n v t = headRec c n v' t) : v = v' := by
  rw [← headPt_headRec c n v t, h, headPt_headRec]

theorem fibreMapOf_of_summable (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (t : TailSpace n) (v : actualCMHead c n) (h : TailSummable c s n t) :
    fibreMapOf c s n Φ t v =
      headPt c n (coordE c s (Φ (tailBase c s n t + headToE c s n v))) := by
  unfold fibreMapOf
  simp only [(summable_headRec_iff c s n v t).2 h, ↓reduceIte, realE_headRec c s n v t h]

theorem fibreMapOf_of_not_summable (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (t : TailSpace n) (v : actualCMHead c n) (h : ¬ TailSummable c s n t) :
    fibreMapOf c s n Φ t v = v := by
  unfold fibreMapOf
  have hn : ¬ WeightedSquareSummable (sourceRate c) s (headRec c n v t) :=
    fun h' => h ((summable_headRec_iff c s n v t).1 h')
  simp only [hn, ↓reduceIte]

/-- If `w` agrees with `headRec v t` off the head, then `headRec (headPt w) t = w`. -/
theorem headRec_headPt_of_tail (w : ℤ → ℂ) (t : TailSpace n)
    (hw : ∀ m (hm : m ∉ symmetricModes n), w m = t ⟨m, by simpa using hm⟩) :
    headRec c n (headPt c n w) t = w := by
  have : tailPt n w = t := by
    funext i
    exact hw i.1 (fun h => i.2 (by simpa using h))
  rw [← this]
  exact headRec_headPt_tailPt c n w

/-- Core fibre identity: the fibre map is conjugate to `Φ` through `R ∘ headRec`. -/
theorem headRec_fibreMapOf (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (t : TailSpace n) (v : actualCMHead c n) (ht : TailSummable c s n t)
    (hfix : SameTail c s n (Φ (realE c s (headRec c n v t))) (realE c s (headRec c n v t))) :
    headRec c n (fibreMapOf c s n Φ t v) t =
      coordE c s (Φ (realE c s (headRec c n v t))) := by
  have hs := (summable_headRec_iff c s n v t).2 ht
  unfold fibreMapOf
  simp only [hs, ↓reduceIte]
  refine headRec_headPt_of_tail c n _ t (fun m hm => ?_)
  rw [hfix m hm, coordE_realE c s _ hs, headRec_apply_not_mem c n _ _ hm]

theorem realE_headRec_fibreMapOf (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (t : TailSpace n) (v : actualCMHead c n) (ht : TailSummable c s n t)
    (hfix : SameTail c s n (Φ (realE c s (headRec c n v t))) (realE c s (headRec c n v t))) :
    realE c s (headRec c n (fibreMapOf c s n Φ t v) t) =
      Φ (realE c s (headRec c n v t)) := by
  rw [headRec_fibreMapOf c s n Φ t v ht hfix]
  exact realE_coordE c s _

/-! ### Goal 1 -/

/-- **FB 1.** If `Φ` fixes tails, then `coordE ∘ Φ ∘ R` is the fibre action of `fibreMapOf Φ` on
every summable sample. -/
theorem coordE_comp_realE_eq_fibreAct
    (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x) (z : ℤ → ℂ)
    (hz : WeightedSquareSummable (sourceRate c) s z) :
    coordE c s (Φ (realE c s z)) = fibreAct c n (fibreMapOf c s n Φ) z := by
  have hz' : TailSummable c s n (tailPt n z) := by
    have := (summable_headRec_iff c s n (headPt c n z) (tailPt n z)).1
    rw [headRec_headPt_tailPt] at this
    exact this hz
  have h := headRec_fibreMapOf c s n Φ (tailPt n z) (headPt c n z) hz'
    (by rw [headRec_headPt_tailPt]; exact hfix _)
  rw [headRec_headPt_tailPt] at h
  exact h.symm

/-- **FB 1 (a.e. form).** `Φ̂ = coordE ∘ Φ ∘ R` equals `fibreAct (fibreMapOf Φ)` `γ`-a.e. -/
theorem ae_coordE_comp_realE_eq_fibreAct (hs : (1 : ℝ) / 2 < s)
    (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x) :
    ∀ᵐ z ∂NlsGge.Measure.fullWeightSequenceGaussian c.val,
      coordE c s (Φ (realE c s z)) = fibreAct c n (fibreMapOf c s n Φ) z := by
  filter_upwards [coordE_realization_ae c s hs] with z hz
  refine coordE_comp_realE_eq_fibreAct c s n Φ hfix z ?_
  rw [← hz]
  exact weightedSquareSummable_coordE c s _

/-! ### Goal 2 -/

theorem measurableSet_tailSummable : MeasurableSet {t : TailSpace n | TailSummable c s n t} := by
  have h : Measurable (fun t : TailSpace n => headRec c n 0 t) :=
    (measurable_headRec c n).comp (measurable_const.prodMk measurable_id)
  exact (NlsGge.Measure.measurableSet_fullWeightedSequenceSupport c s).preimage h

/-- **FB 2.** -/
theorem measurable_fibreMapOf (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (hΦ : Measurable Φ) : Measurable (Function.uncurry (fibreMapOf c s n Φ)) := by
  have hR : Measurable (fun p : TailSpace n × actualCMHead c n => headRec c n p.2 p.1) :=
    (measurable_headRec c n).comp measurable_swap
  have hset : MeasurableSet {p : TailSpace n × actualCMHead c n |
      WeightedSquareSummable (sourceRate c) s (headRec c n p.2 p.1)} :=
    (NlsGge.Measure.measurableSet_fullWeightedSequenceSupport c s).preimage hR
  unfold fibreMapOf Function.uncurry
  refine Measurable.ite hset ?_ measurable_snd
  exact (measurable_headPt c n).comp ((measurable_coordE c s).comp
    (hΦ.comp ((NlsGge.Measure.measurable_fullWeightedSequenceRealization c s).comp hR)))

theorem measurable_fibreMapOf_of_continuous
    (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s) (hΦ : Continuous Φ) :
    Measurable (Function.uncurry (fibreMapOf c s n Φ)) :=
  measurable_fibreMapOf c s n Φ hΦ.measurable

/-! ### Goal 3 -/

/-- The slice `{v | R (headRec v t) ∈ A}` of `A ⊆ E` over the tail `t`. -/
def fibreSlice (A : Set (FullWeightedHilbert c s)) (t : TailSpace n) : Set (actualCMHead c n) :=
  {v | realE c s (headRec c n v t) ∈ A}

theorem mem_coordE_image_iff (A : Set (FullWeightedHilbert c s)) (z : ℤ → ℂ) :
    z ∈ coordE c s '' A ↔ WeightedSquareSummable (sourceRate c) s z ∧ realE c s z ∈ A := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨weightedSquareSummable_coordE c s x, by rw [realE_coordE]; exact hx⟩
  · rintro ⟨hz, hA⟩
    exact ⟨_, hA, coordE_realE c s z hz⟩

theorem fibreSlice_coordE_subset (A : Set (FullWeightedHilbert c s)) (t : TailSpace n) :
    {v : actualCMHead c n | headRec c n v t ∈ coordE c s '' A} ⊆ fibreSlice c s n A t :=
  fun _ hv => ((mem_coordE_image_iff c s A _).1 hv).2

theorem hfix_symm (Φ : FullWeightedHilbert c s ≃ FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x) (y : FullWeightedHilbert c s) :
    SameTail c s n (Φ.symm y) y := by
  intro m hm
  have := hfix (Φ.symm y) m hm
  rw [Φ.apply_symm_apply] at this
  exact this.symm

theorem fibreMapOf_comp_fibreMapOf (Φ Ψ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (hΦ : ∀ x, SameTail c s n (Φ x) x) (hΨ : ∀ x, SameTail c s n (Ψ x) x)
    (hinv : ∀ x, Ψ (Φ x) = x) (t : TailSpace n) (v : actualCMHead c n) :
    fibreMapOf c s n Ψ t (fibreMapOf c s n Φ t v) = v := by
  by_cases ht : TailSummable c s n t
  · have h1 := realE_headRec_fibreMapOf c s n Φ t v ht (hΦ _)
    have hw : realE c s (headRec c n (fibreMapOf c s n Φ t v) t) =
        Φ (realE c s (headRec c n v t)) := h1
    have h2 := realE_headRec_fibreMapOf c s n Ψ t (fibreMapOf c s n Φ t v) ht
      (by rw [hw]; exact hΨ _)
    rw [hw, hinv] at h2
    apply headRec_injective_left c n (t := t)
    have hs := (summable_headRec_iff c s n v t).2 ht
    have hs' := (summable_headRec_iff c s n (fibreMapOf c s n Ψ t (fibreMapOf c s n Φ t v)) t).2 ht
    rw [← coordE_realE c s _ hs, ← coordE_realE c s _ hs', h2]
  · rw [fibreMapOf_of_not_summable c s n _ t _ ht, fibreMapOf_of_not_summable c s n _ t _ ht]

/-- **FB 3 (injectivity).** Injectivity of `Φ` on `A ⊆ E` transfers to the fibre slices. -/
theorem injOn_fibreMapOf (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x) (A : Set (FullWeightedHilbert c s))
    (hinj : Set.InjOn Φ A) (t : TailSpace n) :
    Set.InjOn (fibreMapOf c s n Φ t) (fibreSlice c s n A t) := by
  by_cases ht : TailSummable c s n t
  · intro v hv v' hv' h
    have e1 := realE_headRec_fibreMapOf c s n Φ t v ht (hfix _)
    have e2 := realE_headRec_fibreMapOf c s n Φ t v' ht (hfix _)
    rw [h] at e1
    have := hinj hv hv' (e1.symm.trans e2)
    apply headRec_injective_left c n (t := t)
    rw [← coordE_realE c s _ ((summable_headRec_iff c s n v t).2 ht),
      ← coordE_realE c s _ ((summable_headRec_iff c s n v' t).2 ht), this]
  · intro v _ v' _ h
    rwa [fibreMapOf_of_not_summable c s n Φ t v ht,
      fibreMapOf_of_not_summable c s n Φ t v' ht] at h

theorem injective_of_bijOn_fibre (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x)
    (hbij : ∀ x₀, Set.BijOn Φ {x | SameTail c s n x x₀} {x | SameTail c s n x x₀}) :
    Function.Injective Φ := by
  intro x x' h
  refine (hbij x).injOn (fun m _ => rfl) (fun m hm => ?_) h
  rw [← hfix x' m hm, ← h, hfix x m hm]

/-- **FB 3 (surjectivity).** -/
theorem surjective_fibreMapOf (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x)
    (hbij : ∀ x₀, Set.BijOn Φ {x | SameTail c s n x x₀} {x | SameTail c s n x x₀})
    (t : TailSpace n) : Function.Surjective (fibreMapOf c s n Φ t) := by
  by_cases ht : TailSummable c s n t
  · intro w
    set y := realE c s (headRec c n w t) with hy
    obtain ⟨x, hx, hxy⟩ := (hbij y).surjOn (show y ∈ {x | SameTail c s n x y} from fun m _ => rfl)
    have hws := (summable_headRec_iff c s n w t).2 ht
    have hxt : ∀ m (hm : m ∉ symmetricModes n),
        coordE c s x m = t ⟨m, by simpa using hm⟩ := by
      intro m hm
      rw [hx m hm, hy, coordE_realE c s _ hws, headRec_apply_not_mem c n _ _ hm]
    refine ⟨headPt c n (coordE c s x), ?_⟩
    have hrec : headRec c n (headPt c n (coordE c s x)) t = coordE c s x :=
      headRec_headPt_of_tail c n _ t hxt
    have hR : realE c s (headRec c n (headPt c n (coordE c s x)) t) = x := by
      rw [hrec, realE_coordE]
    have h1 := headRec_fibreMapOf c s n Φ t (headPt c n (coordE c s x)) ht
      (by rw [hR]; exact hfix x)
    rw [hR, hxy, hy, coordE_realE c s _ hws] at h1
    exact headRec_injective_left c n h1
  · intro w
    exact ⟨w, fibreMapOf_of_not_summable c s n Φ t w ht⟩

theorem bijective_fibreMapOf (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x)
    (hbij : ∀ x₀, Set.BijOn Φ {x | SameTail c s n x x₀} {x | SameTail c s n x x₀})
    (t : TailSpace n) : Function.Bijective (fibreMapOf c s n Φ t) :=
  ⟨fun _ _ h => injOn_fibreMapOf c s n Φ hfix Set.univ
      (Set.injOn_univ.2 (injective_of_bijOn_fibre c s n Φ hfix hbij)) t
        (Set.mem_univ _) (Set.mem_univ _) h, surjective_fibreMapOf c s n Φ hfix hbij t⟩

theorem continuous_headPt' : Continuous (headPt c n) :=
  (actualCMHeadCoord c n).symm.toContinuousLinearEquiv.continuous.comp
    (continuous_pi fun _ => continuous_apply _)

theorem continuous_coordE : Continuous (coordE c s) :=
  continuous_pi (continuous_coordE_apply c s)

/-- `x ↦ headPt (coordE x)` as a real-linear map `E → V`. -/
def headCoordLin : FullWeightedHilbert c s →ₗ[ℝ] actualCMHead c n where
  toFun x := headPt c n (coordE c s x)
  map_add' x y := by
    unfold headPt
    rw [← map_add]
    rfl
  map_smul' r x := by
    unfold headPt
    simp only [RingHom.id_apply]
    rw [← map_smul]
    congr 1

/-- `x ↦ headPt (coordE x)` as a continuous real-linear map `E → V`. -/
def headCoord : FullWeightedHilbert c s →L[ℝ] actualCMHead c n :=
  { headCoordLin c s n with
    cont := (continuous_headPt' c n).comp (continuous_coordE c s) }

theorem headCoord_apply (x : FullWeightedHilbert c s) :
    headCoord c s n x = headPt c n (coordE c s x) := rfl

theorem fibreMapOf_of_summable' (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (t : TailSpace n) (h : TailSummable c s n t) :
    fibreMapOf c s n Φ t =
      fun v => headCoord c s n (Φ (tailBase c s n t + headToE c s n v)) :=
  funext fun v => fibreMapOf_of_summable c s n Φ t v h

theorem fibreMapOf_of_not_summable' (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (t : TailSpace n) (h : ¬ TailSummable c s n t) :
    fibreMapOf c s n Φ t = id :=
  funext fun v => fibreMapOf_of_not_summable c s n Φ t v h

/-- Continuity of the fibre maps of a continuous `Φ`. -/
theorem continuous_fibreMapOf (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (hΦ : Continuous Φ) (t : TailSpace n) : Continuous (fibreMapOf c s n Φ t) := by
  by_cases ht : TailSummable c s n t
  · rw [fibreMapOf_of_summable' c s n Φ t ht]
    exact (headCoord c s n).continuous.comp
      (hΦ.comp (continuous_const.add (headToE c s n).continuous))
  · rw [fibreMapOf_of_not_summable' c s n Φ t ht]
    exact continuous_id

/-- **FB 3 (equivalence).** For a bijection `Φ` of `E` fixing tails, the fibre maps form a family
of bijections `V ≃ V`, with inverse the fibre maps of `Φ⁻¹`. -/
def fibreEquivOf (Φ : FullWeightedHilbert c s ≃ FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x) (t : TailSpace n) :
    actualCMHead c n ≃ actualCMHead c n where
  toFun := fibreMapOf c s n Φ t
  invFun := fibreMapOf c s n Φ.symm t
  left_inv v := fibreMapOf_comp_fibreMapOf c s n Φ Φ.symm hfix (hfix_symm c s n Φ hfix)
    (fun x => Φ.symm_apply_apply x) t v
  right_inv w := fibreMapOf_comp_fibreMapOf c s n Φ.symm Φ (hfix_symm c s n Φ hfix) hfix
    (fun x => Φ.apply_symm_apply x) t w

theorem fibreEquivOf_apply (Φ : FullWeightedHilbert c s ≃ FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x) (t : TailSpace n) (v : actualCMHead c n) :
    fibreEquivOf c s n Φ hfix t v = fibreMapOf c s n Φ t v := rfl

/-- **FB 3 (homeomorphism).** For a homeomorphism `Φ` of `E` fixing tails, the fibre maps form a
family `V ≃ₜ V`. -/
def fibreHomeoOf (Φ : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x) (t : TailSpace n) :
    actualCMHead c n ≃ₜ actualCMHead c n where
  toEquiv := fibreEquivOf c s n Φ.toEquiv hfix t
  continuous_toFun := continuous_fibreMapOf c s n Φ Φ.continuous t
  continuous_invFun := continuous_fibreMapOf c s n Φ.symm Φ.symm.continuous t

theorem fibreHomeoOf_apply (Φ : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x) (t : TailSpace n) (v : actualCMHead c n) :
    fibreHomeoOf c s n Φ hfix t v = fibreMapOf c s n Φ t v := rfl

theorem fibreHomeoOf_symm_apply (Φ : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x) (t : TailSpace n) (v : actualCMHead c n) :
    (fibreHomeoOf c s n Φ hfix t).symm v = fibreMapOf c s n Φ.symm t v := rfl

/-! ### Goal 4 -/

/-- **FB 4.** Differentiability along head directions transfers to the fibre maps.  The slice
parametrization `v ↦ R (headRec v t) = tailBase t + headToE v` is affine. -/
theorem differentiableAt_fibreMapOf (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (t : TailSpace n) (v₀ : actualCMHead c n)
    (hd : TailSummable c s n t →
      DifferentiableAt ℝ (fun v : actualCMHead c n =>
        Φ (tailBase c s n t + headToE c s n v)) v₀) :
    DifferentiableAt ℝ (fibreMapOf c s n Φ t) v₀ := by
  by_cases ht : TailSummable c s n t
  · rw [fibreMapOf_of_summable' c s n Φ t ht]
    exact (headCoord c s n).differentiableAt.comp v₀ (hd ht)
  · rw [fibreMapOf_of_not_summable' c s n Φ t ht]
    exact differentiableAt_id

/-- **FB 4 (pointwise head-direction form).** If `h ↦ Φ (x + headToE h)` is differentiable at `0`
for `x = R (headRec v₀ t)`, then `fibreMapOf Φ t` is differentiable at `v₀`. -/
theorem differentiableAt_fibreMapOf_of_head
    (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s)
    (t : TailSpace n) (v₀ : actualCMHead c n)
    (hd : DifferentiableAt ℝ (fun h : actualCMHead c n =>
        Φ (realE c s (headRec c n v₀ t) + headToE c s n h)) 0) :
    DifferentiableAt ℝ (fibreMapOf c s n Φ t) v₀ := by
  refine differentiableAt_fibreMapOf c s n Φ t v₀ (fun ht => ?_)
  have e : (fun v : actualCMHead c n => Φ (tailBase c s n t + headToE c s n v)) =
      (fun h : actualCMHead c n => Φ (realE c s (headRec c n v₀ t) + headToE c s n h)) ∘
        (fun v => v - v₀) := by
    funext v
    simp only [Function.comp, realE_headRec c s n v₀ t ht, map_sub]
    congr 1
    abel
  rw [e]
  have hd' : DifferentiableAt ℝ (fun h : actualCMHead c n =>
      Φ (realE c s (headRec c n v₀ t) + headToE c s n h)) (v₀ - v₀) := by
    rw [sub_self]; exact hd
  exact DifferentiableAt.comp v₀ hd' (differentiableAt_id.sub_const v₀)

/-! ### Goal 5: linear `Φ` -/

theorem headCoord_headToE (v : actualCMHead c n) : headCoord c s n (headToE c s n v) = v := by
  apply Subtype.ext
  apply cmCoord_ext
  intro m
  rw [headCoord_apply, cmCoord_headPt]
  by_cases hm : m ∈ symmetricModes n
  · rw [if_pos hm]; rfl
  · rw [if_neg hm, cmCoord_head_eq_zero c n v hm]

theorem eq_headToE_headCoord (x : FullWeightedHilbert c s)
    (hx : ∀ m ∉ symmetricModes n, coordE c s x m = 0) :
    x = headToE c s n (headCoord c s n x) := by
  apply coordE_injective c s
  funext m
  rw [coordE_headToE, headCoord_apply, cmCoord_headPt]
  by_cases hm : m ∈ symmetricModes n
  · rw [if_pos hm]
  · rw [if_neg hm, hx m hm]

/-- The tail-independent linear part of the fibre maps of a linear `Φ`. -/
def fibreLin (Φ : FullWeightedHilbert c s →L[ℝ] FullWeightedHilbert c s) :
    actualCMHead c n →L[ℝ] actualCMHead c n :=
  (headCoord c s n).comp (Φ.comp (headToE c s n))

theorem fibreLin_apply (Φ : FullWeightedHilbert c s →L[ℝ] FullWeightedHilbert c s)
    (v : actualCMHead c n) :
    fibreLin c s n Φ v = headCoord c s n (Φ (headToE c s n v)) := rfl

theorem map_headToE_eq (Φ : FullWeightedHilbert c s →L[ℝ] FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x) (v : actualCMHead c n) :
    Φ (headToE c s n v) = headToE c s n (fibreLin c s n Φ v) := by
  apply eq_headToE_headCoord
  intro m hm
  rw [hfix _ m hm, coordE_headToE, cmCoord_head_eq_zero c n v hm]

theorem hfix_symm_clm (Φ : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x) (y : FullWeightedHilbert c s) :
    SameTail c s n (Φ.symm y) y := by
  intro m hm
  have := hfix (Φ.symm y) m hm
  rw [Φ.apply_symm_apply] at this
  exact this.symm

/-- The fibre linear part is a continuous linear equivalence of `V`. -/
def fibreLinEquiv (Φ : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x) : actualCMHead c n ≃L[ℝ] actualCMHead c n :=
  ContinuousLinearEquiv.equivOfInverse
    (fibreLin c s n (Φ : FullWeightedHilbert c s →L[ℝ] FullWeightedHilbert c s))
    (fibreLin c s n (Φ.symm : FullWeightedHilbert c s →L[ℝ] FullWeightedHilbert c s))
    (fun v => by
      have h1 := map_headToE_eq c s n (Φ : FullWeightedHilbert c s →L[ℝ] FullWeightedHilbert c s)
        hfix v
      have h2 : Φ.symm (headToE c s n (fibreLin c s n
          (Φ : FullWeightedHilbert c s →L[ℝ] FullWeightedHilbert c s) v)) = headToE c s n v := by
        have : Φ (headToE c s n v) = headToE c s n (fibreLin c s n
          (Φ : FullWeightedHilbert c s →L[ℝ] FullWeightedHilbert c s) v) := h1
        rw [← this, Φ.symm_apply_apply]
      rw [fibreLin_apply]
      show headCoord c s n (Φ.symm _) = v
      rw [h2, headCoord_headToE])
    (fun v => by
      have h1 := map_headToE_eq c s n (Φ.symm : FullWeightedHilbert c s →L[ℝ] FullWeightedHilbert c s)
        (hfix_symm_clm c s n Φ hfix) v
      have h2 : Φ (headToE c s n (fibreLin c s n
          (Φ.symm : FullWeightedHilbert c s →L[ℝ] FullWeightedHilbert c s) v)) = headToE c s n v := by
        have : Φ.symm (headToE c s n v) = headToE c s n (fibreLin c s n
          (Φ.symm : FullWeightedHilbert c s →L[ℝ] FullWeightedHilbert c s) v) := h1
        rw [← this, Φ.apply_symm_apply]
      rw [fibreLin_apply]
      show headCoord c s n (Φ _) = v
      rw [h2, headCoord_headToE])

/-- **FB 5.** For a continuous linear automorphism `Φ` of `E` fixing tails, each fibre map is an
affine homeomorphism of `V`: `fibreMapOf Φ t = A + b_t`, with `A` a continuous linear
equivalence (independent of `t`) and `b_t = headCoord (Φ (tailBase t))` (or `id` for a non-summable
tail). -/
theorem fibreMapOf_affine (Φ : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x) (t : TailSpace n) :
    ∃ (A : actualCMHead c n ≃L[ℝ] actualCMHead c n) (b : actualCMHead c n),
      ∀ v, fibreMapOf c s n Φ t v = A v + b := by
  by_cases ht : TailSummable c s n t
  · refine ⟨fibreLinEquiv c s n Φ hfix, headCoord c s n (Φ (tailBase c s n t)), fun v => ?_⟩
    rw [fibreMapOf_of_summable c s n Φ t v ht]
    change headCoord c s n (Φ (tailBase c s n t + headToE c s n v)) = _
    rw [map_add, map_add, add_comm]
    rfl
  · exact ⟨ContinuousLinearEquiv.refl ℝ _, 0, fun v => by
      rw [fibreMapOf_of_not_summable c s n Φ t v ht]; simp⟩

/-- **FB 5 (S_Π).** The family of fibre homeomorphisms `TailSpace n → V ≃ₜ V` attached to a
continuous linear automorphism of `E` fixing tails. -/
def fibreHomeoOfCLE (Φ : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x) (t : TailSpace n) :
    actualCMHead c n ≃ₜ actualCMHead c n :=
  fibreHomeoOf c s n Φ.toHomeomorph hfix t

theorem fibreHomeoOfCLE_apply (Φ : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x) (t : TailSpace n) (v : actualCMHead c n) :
    fibreHomeoOfCLE c s n Φ hfix t v = fibreMapOf c s n Φ t v := rfl

theorem differentiable_fibreMapOf (Φ : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x) (t : TailSpace n) :
    Differentiable ℝ (fibreMapOf c s n Φ t) := by
  obtain ⟨A, b, h⟩ := fibreMapOf_affine c s n Φ hfix t
  have : fibreMapOf c s n Φ t = fun v => A v + b := funext h
  rw [this]
  exact A.differentiable.add_const b

open Classical in
theorem fderiv_fibreMapOf (Φ : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (t : TailSpace n) (v : actualCMHead c n) :
    fderiv ℝ (fibreMapOf c s n Φ t) v =
      (if TailSummable c s n t then
        (fibreLin c s n (Φ : FullWeightedHilbert c s →L[ℝ] FullWeightedHilbert c s))
      else ContinuousLinearMap.id ℝ _) := by
  by_cases ht : TailSummable c s n t
  · rw [if_pos ht]
    have e : fibreMapOf c s n Φ t = fun v => fibreLin c s n
        (Φ : FullWeightedHilbert c s →L[ℝ] FullWeightedHilbert c s) v +
        headCoord c s n (Φ (tailBase c s n t)) := by
      funext v
      rw [fibreMapOf_of_summable c s n Φ t v ht]
      change headCoord c s n (Φ (tailBase c s n t + headToE c s n v)) = _
      rw [map_add, map_add, add_comm]
      rfl
    rw [e]
    exact ((fibreLin c s n
      (Φ : FullWeightedHilbert c s →L[ℝ] FullWeightedHilbert c s)).hasFDerivAt.add_const _).fderiv
  · rw [if_neg ht, fibreMapOf_of_not_summable' c s n Φ t ht]
    exact (hasFDerivAt_id v).fderiv

/-- Measurability of the fibre Jacobian from measurability of `S` and of the fibre determinant. -/
theorem measurable_fibreJ_of_det (S : TailSpace n → actualCMHead c n → actualCMHead c n)
    (hS : Measurable (Function.uncurry S))
    (hdet : Measurable (fun z : ℤ → ℂ =>
      (fderiv ℝ (S (tailPt n z)) (headPt c n z)).det)) :
    Measurable (fibreJ c n S) := by
  have hz : Measurable (fun z : ℤ → ℂ => (tailPt n z, headPt c n z)) :=
    (measurable_tailPt n).prodMk (measurable_headPt c n)
  have h1 : Measurable (fun z : ℤ → ℂ => S (tailPt n z) (headPt c n z)) := hS.comp hz
  have hnorm : Measurable (fun z : ℤ → ℂ => ‖S (tailPt n z) (headPt c n z)‖) := h1.norm
  have hnorm2 : Measurable (fun z : ℤ → ℂ => ‖headPt c n z‖) := (measurable_headPt c n).norm
  have hexp : Measurable (fun z : ℤ → ℂ => Real.exp (-(‖S (tailPt n z) (headPt c n z)‖ ^ 2 -
      ‖headPt c n z‖ ^ 2) / 2)) :=
    Real.measurable_exp.comp (((hnorm.pow_const 2).sub (hnorm2.pow_const 2)).neg.div_const 2)
  have hab := hdet.abs
  unfold fibreJ finiteRamerDensity
  exact hab.mul hexp

/-- Measurability of the fibre Jacobian for a linear `Φ` fixing tails. -/
theorem measurable_fibreJ_of_clm (Φ : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s) :
    Measurable (fibreJ c n (fibreMapOf c s n Φ)) := by
  classical
  have hS := measurable_fibreMapOf c s n Φ Φ.continuous.measurable
  have hset : MeasurableSet {z : ℤ → ℂ | TailSummable c s n (tailPt n z)} :=
    (measurableSet_tailSummable c s n).preimage (measurable_tailPt n)
  refine measurable_fibreJ_of_det c n _ hS ?_
  have : (fun z : ℤ → ℂ =>
      (fderiv ℝ (fibreMapOf c s n Φ (tailPt n z)) (headPt c n z)).det) =
      fun z => if TailSummable c s n (tailPt n z) then
        (fibreLin c s n (Φ : FullWeightedHilbert c s →L[ℝ] FullWeightedHilbert c s)).det
        else 1 := by
    funext z
    rw [fderiv_fibreMapOf c s n Φ]
    split_ifs
    · rfl
    · simp [ContinuousLinearMap.det]
  rw [this]
  exact Measurable.ite hset measurable_const measurable_const

/-! ### Goal 6 -/

theorem ae_weightedSquareSummable_coordE_realE (hs : (1 : ℝ) / 2 < s) :
    ∀ᵐ z ∂NlsGge.Measure.fullWeightSequenceGaussian c.val,
      WeightedSquareSummable (sourceRate c) s z ∧ coordE c s (realE c s z) = z := by
  filter_upwards [coordE_realization_ae c s hs] with z hz
  exact ⟨by rw [← hz]; exact weightedSquareSummable_coordE c s _, hz⟩

/-- **FB 6 (homeomorphism form).**  `(Φ⁻¹)_# γ_E = J γ_E` with `J = fibreJ ∘ coordE`, for a
homeomorphism `Φ` of `E` fixing tails whose fibre maps are differentiable with measurable fibre
Jacobian. -/
theorem map_symm_eq_withDensity_of_homeo (hs : (1 : ℝ) / 2 < s)
    (Φ : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x)
    (hJm : Measurable (fibreJ c n (fibreMapOf c s n Φ)))
    (hd : ∀ t, Differentiable ℝ (fibreMapOf c s n Φ t)) :
    (NlsGge.Measure.fullWeightedSequenceGaussian c s).map Φ.symm =
      (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
        (fun x => ENNReal.ofReal (fibreJ c n (fibreMapOf c s n Φ) (coordE c s x))) := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  have hRm := NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have hγE : NlsGge.Measure.fullWeightedSequenceGaussian c s = γ.map (realE c s) := rfl
  have hfixS : ∀ x, SameTail c s n (Φ.symm x) x := fun x =>
    hfix_symm c s n Φ.toEquiv hfix x
  have hSm : Measurable (Function.uncurry (fun t => (fibreHomeoOf c s n Φ hfix t :
      actualCMHead c n → actualCMHead c n))) :=
    measurable_fibreMapOf c s n Φ Φ.continuous.measurable
  have key := map_fibreActInv c n (fibreHomeoOf c s n Φ hfix) hSm hJm hd
  have hΨ : fibreActInv c n (fibreHomeoOf c s n Φ hfix) = fibreAct c n (fibreMapOf c s n Φ.symm) :=
    rfl
  have hΨm : Measurable (fibreActInv c n (fibreHomeoOf c s n Φ hfix)) := by
    rw [hΨ]
    exact measurable_fibreAct c n _ (measurable_fibreMapOf c s n Φ.symm
      Φ.symm.continuous.measurable)
  ext B hB
  have hmeas : Measurable (fun x : FullWeightedHilbert c s =>
      ENNReal.ofReal (fibreJ c n (fibreMapOf c s n Φ) (coordE c s x))) :=
    (hJm.comp (measurable_coordE c s)).ennreal_ofReal
  have hset : (fun z => z ∈ realE c s ⁻¹' (Φ.symm ⁻¹' B)) =ᵐ[γ]
      (fun z => z ∈ fibreActInv c n (fibreHomeoOf c s n Φ hfix) ⁻¹' (realE c s ⁻¹' B)) := by
    filter_upwards [ae_weightedSquareSummable_coordE_realE c s hs] with z hz
    have h1 := coordE_comp_realE_eq_fibreAct c s n Φ.symm hfixS z hz.1
    have h2 : realE c s (fibreActInv c n (fibreHomeoOf c s n Φ hfix) z) = Φ.symm (realE c s z) := by
      rw [hΨ, ← h1, realE_coordE]
    simp only [Set.mem_preimage, h2]
  calc (NlsGge.Measure.fullWeightedSequenceGaussian c s).map Φ.symm B
      = γ (realE c s ⁻¹' (Φ.symm ⁻¹' B)) := by
        rw [Measure.map_apply Φ.symm.continuous.measurable hB, hγE,
          Measure.map_apply hRm (Φ.symm.continuous.measurable hB)]
    _ = γ (fibreActInv c n (fibreHomeoOf c s n Φ hfix) ⁻¹' (realE c s ⁻¹' B)) :=
        measure_congr (Filter.eventuallyEq_set.2 (by
          filter_upwards [hset] with z hz using by simpa using hz))
    _ = (γ.map (fibreActInv c n (fibreHomeoOf c s n Φ hfix))) (realE c s ⁻¹' B) :=
        (Measure.map_apply hΨm (hRm hB)).symm
    _ = (γ.withDensity (fun z => ENNReal.ofReal
          (fibreJ c n (fibreMapOf c s n Φ) z))) (realE c s ⁻¹' B) := by
        rw [key]; rfl
    _ = ∫⁻ z in realE c s ⁻¹' B, ENNReal.ofReal (fibreJ c n (fibreMapOf c s n Φ) z) ∂γ :=
        withDensity_apply _ (hRm hB)
    _ = ∫⁻ z in realE c s ⁻¹' B, ENNReal.ofReal
          (fibreJ c n (fibreMapOf c s n Φ) (coordE c s (realE c s z))) ∂γ := by
        refine setLIntegral_congr_fun_ae (hRm hB) ?_
        filter_upwards [ae_weightedSquareSummable_coordE_realE c s hs] with z hz _
        rw [hz.2]
    _ = ∫⁻ x in B, ENNReal.ofReal (fibreJ c n (fibreMapOf c s n Φ) (coordE c s x))
          ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
        rw [hγE, setLIntegral_map hB hmeas hRm]
    _ = _ := (withDensity_apply _ hB).symm

/-- **FB 6.**  For a continuous linear automorphism `Φ` of `E` fixing tails,
`(Φ⁻¹)_# γ_E = γ_E.withDensity (ofReal ∘ fibreJ (fibreMapOf Φ) ∘ coordE)`. -/
theorem map_symm_eq_withDensity (hs : (1 : ℝ) / 2 < s)
    (Φ : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Φ x) x) :
    (NlsGge.Measure.fullWeightedSequenceGaussian c s).map Φ.symm =
      (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
        (fun x => ENNReal.ofReal (fibreJ c n (fibreMapOf c s n Φ) (coordE c s x))) :=
  map_symm_eq_withDensity_of_homeo c s n hs Φ.toHomeomorph hfix
    (measurable_fibreJ_of_clm c s n Φ) (differentiable_fibreMapOf c s n Φ hfix)

/-! ### Goal 6' -/

/-- **FB 6' (local version).**  For `A ⊆ E` measurable with `Φ` injective on `A`, fibre maps
differentiable on the fibres over `A`, and `Φ '' A` measurable (automatic in the application,
where `Φ '' A` is a ball),
`∫_{Φ(A)} f dγ_E = ∫_A f(Φ x) J(coordE x) dγ_E` with `J = fibreJ (fibreMapOf Φ)`.  Proof: apply
R2 (`lintegral_image_fibreAct`) to `coordE '' A = {z | summable z ∧ R z ∈ A}`. -/
theorem lintegral_image_eq_fibre (hs : (1 : ℝ) / 2 < s)
    (Φ : FullWeightedHilbert c s → FullWeightedHilbert c s) (hΦm : Measurable Φ)
    (hfix : ∀ x, SameTail c s n (Φ x) x)
    (hJm : Measurable (fibreJ c n (fibreMapOf c s n Φ)))
    (A : Set (FullWeightedHilbert c s)) (hA : MeasurableSet A)
    (hΦA : MeasurableSet (Φ '' A)) (hinj : Set.InjOn Φ A)
    (hdiff : ∀ (t : TailSpace n) (v : actualCMHead c n),
      WeightedSquareSummable (sourceRate c) s (headRec c n v t) →
      realE c s (headRec c n v t) ∈ A → DifferentiableAt ℝ (fibreMapOf c s n Φ t) v)
    (f : FullWeightedHilbert c s → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y in Φ '' A, f y ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) =
      ∫⁻ x in A, f (Φ x) * ENNReal.ofReal (fibreJ c n (fibreMapOf c s n Φ) (coordE c s x))
        ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  have hRm := NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have hγE : NlsGge.Measure.fullWeightedSequenceGaussian c s = γ.map (realE c s) := rfl
  set A' : Set (ℤ → ℂ) := coordE c s '' A with hA'def
  have hA'eq : A' = {z | WeightedSquareSummable (sourceRate c) s z} ∩ realE c s ⁻¹' A := by
    ext z
    rw [hA'def, mem_coordE_image_iff]
    rfl
  have hA' : MeasurableSet A' := by
    rw [hA'eq]
    exact (NlsGge.Measure.measurableSet_fullWeightedSequenceSupport c s).inter (hRm hA)
  have hSm := measurable_fibreMapOf c s n Φ hΦm
  have hR2 := lintegral_image_fibreAct c n (fibreMapOf c s n Φ) hSm hJm A' hA'
    (fun t v hv => hdiff t v ((mem_coordE_image_iff c s A _).1 hv).1
      ((mem_coordE_image_iff c s A _).1 hv).2)
    (fun t => (injOn_fibreMapOf c s n Φ hfix A hinj t).mono
      (fibreSlice_coordE_subset c s n A t))
    (fun z => f (realE c s z)) (hf.comp hRm)
  have hfa := ae_weightedSquareSummable_coordE_realE c s hs
  -- left side
  have hL : ∫⁻ y in Φ '' A, f y ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) =
      ∫⁻ z in fibreAct c n (fibreMapOf c s n Φ) '' A',
        f (realE c s z) ∂γ := by
    rw [hγE, setLIntegral_map hΦA hf hRm]
    refine setLIntegral_congr (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [hfa] with z hz
    simp only [Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, hxz⟩
      refine ⟨coordE c s x, ⟨x, hx, rfl⟩, ?_⟩
      rw [← coordE_comp_realE_eq_fibreAct c s n Φ hfix _ (weightedSquareSummable_coordE c s x),
        realE_coordE, hxz, hz.2]
    · rintro ⟨z', hz', hzz⟩
      obtain ⟨hs', hA''⟩ := (mem_coordE_image_iff c s A _).1 hz'
      refine ⟨realE c s z', hA'', ?_⟩
      rw [← coordE_comp_realE_eq_fibreAct c s n Φ hfix z' hs'] at hzz
      rw [← hzz, realE_coordE]
  -- right side
  have hmeas : Measurable (fun x : FullWeightedHilbert c s =>
      f (Φ x) * ENNReal.ofReal (fibreJ c n (fibreMapOf c s n Φ) (coordE c s x))) :=
    (hf.comp hΦm).mul (hJm.comp (measurable_coordE c s)).ennreal_ofReal
  have hR : ∫⁻ x in A, f (Φ x) * ENNReal.ofReal (fibreJ c n (fibreMapOf c s n Φ) (coordE c s x))
        ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) =
      ∫⁻ z in A', f (realE c s (fibreAct c n (fibreMapOf c s n Φ) z)) *
        ENNReal.ofReal (fibreJ c n (fibreMapOf c s n Φ) z) ∂γ := by
    rw [hγE, setLIntegral_map hA hmeas hRm]
    have hseteq : (realE c s ⁻¹' A : Set (ℤ → ℂ)) =ᵐ[γ] A' := by
      refine Filter.eventuallyEq_set.2 ?_
      filter_upwards [hfa] with z hz
      rw [hA'eq]
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨hz.1, h⟩, fun h => h.2⟩
    rw [setLIntegral_congr hseteq]
    refine setLIntegral_congr_fun_ae hA' ?_
    filter_upwards [hfa] with z hz hzA
    have hzA' : WeightedSquareSummable (sourceRate c) s z := ((mem_coordE_image_iff c s A _).1 hzA).1
    rw [← coordE_comp_realE_eq_fibreAct c s n Φ hfix z hzA', realE_coordE, hz.2]
  rw [hL, hR]
  exact hR2

end Bridge

end NlsGge.Ramer

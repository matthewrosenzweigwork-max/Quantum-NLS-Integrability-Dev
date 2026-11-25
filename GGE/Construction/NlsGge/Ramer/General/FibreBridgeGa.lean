import NlsGge.Ramer.General.RamerStep2FibrewiseG
import NlsGge.Ramer.General.SpaceTransferG
import NlsGge.Ramer.General.LinearDecompositionG

/-!
# FB (part a), generalized (GD4a): bridge from `E`-maps that fix the tail to the fibre
coordinates of R2, over a `RamerSetting S`

Adapted from the first half of `NlsGge/Ramer/FibreBridge.lean` (goals 1-3).  Dictionary:
`realE ↦ S.R`, `coordE ↦ S.coordE`, `WeightedSquareSummable (sourceRate c) s z ↦ S.memE z`,
`cmCoord ↦ S.hcoord`, `SameTail ↦ S.SameTail` (GD3, stated in coordinates `S.coord`), `headToE ↦
S.headToE` (GB1).  No norm of `E` is used in this part.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer NlsGge.Measure

section Bridge

variable (S : NlsGge.Ramer.General.RamerSetting) (N : ℕ)

open Classical in
/-- The fibre maps of `Φ : E → E`: for a summable tail the head of `Φ (R (headRec v t))`,
otherwise the identity. -/
def fibreMapOf (Φ : S.E → S.E) (t : TailSpace N) (v : S.head N) : S.head N :=
  if S.memE (S.headRec N v t) then
    S.headPt N (S.coordE (Φ (S.R (S.headRec N v t))))
  else v

/-- The tail `t` is summable (equivalently `headRec v t` is summable for every head `v`). -/
def TailSummable (t : TailSpace N) : Prop :=
  S.memE (S.headRec N 0 t)

theorem coordE_realE (z : ℤ → ℂ) (hz : S.memE z) : S.coordE (S.R z) = z := by
  funext m
  exact S.coord_R hz m

theorem realE_coordE (x : S.E) : S.R (S.coordE x) = x := S.R_coordE x

theorem coordE_injective : Function.Injective S.coordE := fun x y h => by
  rw [← S.R_coordE x, ← S.R_coordE y, h]

theorem coordE_add (x y : S.E) (m : ℤ) :
    S.coordE (x + y) m = S.coordE x m + S.coordE y m := S.coord_add x y m

theorem coordE_smul (r : ℝ) (x : S.E) (m : ℤ) :
    S.coordE (r • x) m = (r : ℂ) * S.coordE x m := S.coord_smul r x m

theorem coordE_zero (m : ℤ) : S.coordE (0 : S.E) m = 0 := S.coord_zero m

theorem coordE_neg (x : S.E) (m : ℤ) : S.coordE (-x) m = -S.coordE x m :=
  map_neg (S.coord m) x

/-- `headToE` has the head coordinates and zero tail. -/
theorem coordE_headToE (v : S.head N) (m : ℤ) :
    S.coordE (S.headToE N v) m = S.hcoord (v : S.H) m := S.headToE_coord N v m

theorem headRec_apply_mem (v : S.head N) (t : TailSpace N) {m : ℤ}
    (hm : m ∈ symmetricModes N) : S.headRec N v t m = S.hcoord (v : S.H) m := by
  simp [headRec, hm]

theorem headRec_apply_not_mem (v : S.head N) (t : TailSpace N) {m : ℤ}
    (hm : m ∉ symmetricModes N) :
    S.headRec N v t m = t ⟨m, by simpa using hm⟩ := by
  simp [headRec, hm]

theorem hcoord_zero_head (m : ℤ) : S.hcoord (((0 : S.head N)) : S.H) m = 0 := rfl

theorem headRec_eq_add (v : S.head N) (t : TailSpace N) (m : ℤ) :
    S.headRec N v t m = S.headRec N 0 t m + S.coordE (S.headToE N v) m := by
  by_cases hm : m ∈ symmetricModes N
  · rw [S.headRec_apply_mem N _ _ hm, S.headRec_apply_mem N _ _ hm, S.coordE_headToE,
      S.hcoord_zero_head, zero_add]
  · rw [S.headRec_apply_not_mem N _ _ hm, S.headRec_apply_not_mem N _ _ hm,
      S.coordE_headToE, S.hcoord_head_eq_zero N v hm, add_zero]

/-- Summability of `headRec v t` does not depend on `v`. -/
theorem summable_headRec_iff (v : S.head N) (t : TailSpace N) :
    S.memE (S.headRec N v t) ↔ S.TailSummable N t := by
  have key : ∀ (v : S.head N) (t : TailSpace N),
      S.TailSummable N t → S.memE (S.headRec N v t) := by
    intro v t ht
    have h : S.headRec N v t = S.coordE (S.R (S.headRec N 0 t) + S.headToE N v) := by
      funext m
      rw [S.headRec_eq_add N v t m, S.coordE_add, S.coordE_realE _ ht]
    rw [h]
    exact S.memE_coordE _
  refine ⟨fun h => ?_, key v t⟩
  have h0 : S.headRec N 0 t = S.coordE (S.R (S.headRec N v t) + S.headToE N (-v)) := by
    funext m
    rw [S.coordE_add, S.coordE_realE _ h]
    have := S.headRec_eq_add N v t m
    rw [map_neg, S.coordE_neg, this]; ring
  rw [TailSummable, h0]
  exact S.memE_coordE _

/-- The base point `R (headRec 0 t)` of the affine slice over the tail `t`. -/
def tailBase (t : TailSpace N) : S.E := S.R (S.headRec N 0 t)

theorem realE_headRec (v : S.head N) (t : TailSpace N) (ht : S.TailSummable N t) :
    S.R (S.headRec N v t) = S.tailBase N t + S.headToE N v := by
  apply S.coordE_injective
  funext m
  rw [S.coordE_add, S.coordE_realE _ ((S.summable_headRec_iff N v t).2 ht), tailBase,
    S.coordE_realE _ ht, S.headRec_eq_add N v t m]

theorem headRec_injective_left {v v' : S.head N} {t : TailSpace N}
    (h : S.headRec N v t = S.headRec N v' t) : v = v' := by
  rw [← S.headPt_headRec N v t, h, S.headPt_headRec]

theorem fibreMapOf_of_summable (Φ : S.E → S.E)
    (t : TailSpace N) (v : S.head N) (h : S.TailSummable N t) :
    S.fibreMapOf N Φ t v =
      S.headPt N (S.coordE (Φ (S.tailBase N t + S.headToE N v))) := by
  unfold fibreMapOf
  simp only [(S.summable_headRec_iff N v t).2 h, ↓reduceIte, S.realE_headRec N v t h]

theorem fibreMapOf_of_not_summable (Φ : S.E → S.E)
    (t : TailSpace N) (v : S.head N) (h : ¬ S.TailSummable N t) :
    S.fibreMapOf N Φ t v = v := by
  unfold fibreMapOf
  have hn : ¬ S.memE (S.headRec N v t) :=
    fun h' => h ((S.summable_headRec_iff N v t).1 h')
  simp only [hn, ↓reduceIte]

/-- If `w` agrees with `headRec v t` off the head, then `headRec (headPt w) t = w`. -/
theorem headRec_headPt_of_tail (w : ℤ → ℂ) (t : TailSpace N)
    (hw : ∀ m (hm : m ∉ symmetricModes N), w m = t ⟨m, by simpa using hm⟩) :
    S.headRec N (S.headPt N w) t = w := by
  have : tailPt N w = t := by
    funext i
    exact hw i.1 (fun h => i.2 (by simpa using h))
  rw [← this]
  exact S.headRec_headPt_tailPt N w

/-- Core fibre identity: the fibre map is conjugate to `Φ` through `R ∘ headRec`. -/
theorem headRec_fibreMapOf (Φ : S.E → S.E)
    (t : TailSpace N) (v : S.head N) (ht : S.TailSummable N t)
    (hfix : S.SameTail N (Φ (S.R (S.headRec N v t))) (S.R (S.headRec N v t))) :
    S.headRec N (S.fibreMapOf N Φ t v) t =
      S.coordE (Φ (S.R (S.headRec N v t))) := by
  have hs := (S.summable_headRec_iff N v t).2 ht
  unfold fibreMapOf
  simp only [hs, ↓reduceIte]
  refine S.headRec_headPt_of_tail N _ t (fun m hm => ?_)
  have h1 := hfix m hm
  rw [S.coord_R hs] at h1
  exact h1.trans (S.headRec_apply_not_mem N _ _ hm)

theorem realE_headRec_fibreMapOf (Φ : S.E → S.E)
    (t : TailSpace N) (v : S.head N) (ht : S.TailSummable N t)
    (hfix : S.SameTail N (Φ (S.R (S.headRec N v t))) (S.R (S.headRec N v t))) :
    S.R (S.headRec N (S.fibreMapOf N Φ t v) t) =
      Φ (S.R (S.headRec N v t)) := by
  rw [S.headRec_fibreMapOf N Φ t v ht hfix]
  exact S.realE_coordE _

/-! ### Goal 1 -/

/-- **FB 1.** If `Φ` fixes tails, then `coordE ∘ Φ ∘ R` is the fibre action of `fibreMapOf Φ` on
every summable sample. -/
theorem coordE_comp_realE_eq_fibreAct
    (Φ : S.E → S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x) (z : ℤ → ℂ)
    (hz : S.memE z) :
    S.coordE (Φ (S.R z)) = S.fibreAct N (S.fibreMapOf N Φ) z := by
  have hz' : S.TailSummable N (tailPt N z) := by
    have := (S.summable_headRec_iff N (S.headPt N z) (tailPt N z)).1
    rw [S.headRec_headPt_tailPt] at this
    exact this hz
  have h := S.headRec_fibreMapOf N Φ (tailPt N z) (S.headPt N z) hz'
    (by rw [S.headRec_headPt_tailPt]; exact hfix _)
  rw [S.headRec_headPt_tailPt] at h
  exact h.symm

/-- **FB 1 (a.e. form).** `Φ̂ = coordE ∘ Φ ∘ R` equals `fibreAct (fibreMapOf Φ)` `γ`-a.e. -/
theorem ae_coordE_comp_realE_eq_fibreAct
    (Φ : S.E → S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x) :
    ∀ᵐ z ∂S.γ,
      S.coordE (Φ (S.R z)) = S.fibreAct N (S.fibreMapOf N Φ) z := by
  filter_upwards [S.ae_memE] with z hz
  exact S.coordE_comp_realE_eq_fibreAct N Φ hfix z hz

/-! ### Goal 2 -/

theorem measurableSet_tailSummable : MeasurableSet {t : TailSpace N | S.TailSummable N t} := by
  have h : Measurable (fun t : TailSpace N => S.headRec N 0 t) :=
    (S.measurable_headRec N).comp (measurable_const.prodMk measurable_id)
  exact S.measurableSet_memE.preimage h

/-- **FB 2.** -/
theorem measurable_fibreMapOf (Φ : S.E → S.E)
    (hΦ : Measurable Φ) : Measurable (Function.uncurry (S.fibreMapOf N Φ)) := by
  have hR : Measurable (fun p : TailSpace N × S.head N => S.headRec N p.2 p.1) :=
    (S.measurable_headRec N).comp measurable_swap
  have hset : MeasurableSet {p : TailSpace N × S.head N |
      S.memE (S.headRec N p.2 p.1)} :=
    S.measurableSet_memE.preimage hR
  unfold fibreMapOf Function.uncurry
  refine Measurable.ite hset ?_ measurable_snd
  exact (S.measurable_headPt N).comp (S.measurable_coordE.comp
    (hΦ.comp (S.measurable_R.comp hR)))

theorem measurable_fibreMapOf_of_continuous
    (Φ : S.E → S.E) (hΦ : Continuous Φ) :
    Measurable (Function.uncurry (S.fibreMapOf N Φ)) :=
  S.measurable_fibreMapOf N Φ hΦ.measurable

/-! ### Goal 3 -/

/-- The slice `{v | R (headRec v t) ∈ A}` of `A ⊆ E` over the tail `t`. -/
def fibreSlice (A : Set S.E) (t : TailSpace N) : Set (S.head N) :=
  {v | S.R (S.headRec N v t) ∈ A}

theorem mem_coordE_image_iff (A : Set S.E) (z : ℤ → ℂ) :
    z ∈ S.coordE '' A ↔ S.memE z ∧ S.R z ∈ A := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨S.memE_coordE x, by rw [S.realE_coordE]; exact hx⟩
  · rintro ⟨hz, hA⟩
    exact ⟨_, hA, S.coordE_realE z hz⟩

theorem fibreSlice_coordE_subset (A : Set S.E) (t : TailSpace N) :
    {v : S.head N | S.headRec N v t ∈ S.coordE '' A} ⊆ S.fibreSlice N A t :=
  fun _ hv => ((S.mem_coordE_image_iff A _).1 hv).2

theorem hfix_symm (Φ : S.E ≃ S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x) (y : S.E) :
    S.SameTail N (Φ.symm y) y := by
  intro m hm
  have := hfix (Φ.symm y) m hm
  rw [Φ.apply_symm_apply] at this
  exact this.symm

theorem fibreMapOf_comp_fibreMapOf (Φ Ψ : S.E → S.E)
    (hΦ : ∀ x, S.SameTail N (Φ x) x) (hΨ : ∀ x, S.SameTail N (Ψ x) x)
    (hinv : ∀ x, Ψ (Φ x) = x) (t : TailSpace N) (v : S.head N) :
    S.fibreMapOf N Ψ t (S.fibreMapOf N Φ t v) = v := by
  by_cases ht : S.TailSummable N t
  · have h1 := S.realE_headRec_fibreMapOf N Φ t v ht (hΦ _)
    have hw : S.R (S.headRec N (S.fibreMapOf N Φ t v) t) =
        Φ (S.R (S.headRec N v t)) := h1
    have h2 := S.realE_headRec_fibreMapOf N Ψ t (S.fibreMapOf N Φ t v) ht
      (by rw [hw]; exact hΨ _)
    rw [hw, hinv] at h2
    apply S.headRec_injective_left N (t := t)
    have hs := (S.summable_headRec_iff N v t).2 ht
    have hs' := (S.summable_headRec_iff N (S.fibreMapOf N Ψ t (S.fibreMapOf N Φ t v)) t).2 ht
    rw [← S.coordE_realE _ hs, ← S.coordE_realE _ hs', h2]
  · rw [S.fibreMapOf_of_not_summable N _ t _ ht, S.fibreMapOf_of_not_summable N _ t _ ht]

/-- **FB 3 (injectivity).** Injectivity of `Φ` on `A ⊆ E` transfers to the fibre slices. -/
theorem injOn_fibreMapOf (Φ : S.E → S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x) (A : Set S.E)
    (hinj : Set.InjOn Φ A) (t : TailSpace N) :
    Set.InjOn (S.fibreMapOf N Φ t) (S.fibreSlice N A t) := by
  by_cases ht : S.TailSummable N t
  · intro v hv v' hv' h
    have e1 := S.realE_headRec_fibreMapOf N Φ t v ht (hfix _)
    have e2 := S.realE_headRec_fibreMapOf N Φ t v' ht (hfix _)
    rw [h] at e1
    have := hinj hv hv' (e1.symm.trans e2)
    apply S.headRec_injective_left N (t := t)
    rw [← S.coordE_realE _ ((S.summable_headRec_iff N v t).2 ht),
      ← S.coordE_realE _ ((S.summable_headRec_iff N v' t).2 ht), this]
  · intro v _ v' _ h
    rwa [S.fibreMapOf_of_not_summable N Φ t v ht,
      S.fibreMapOf_of_not_summable N Φ t v' ht] at h

theorem injective_of_bijOn_fibre (Φ : S.E → S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x)
    (hbij : ∀ x₀, Set.BijOn Φ {x | S.SameTail N x x₀} {x | S.SameTail N x x₀}) :
    Function.Injective Φ := by
  intro x x' h
  refine (hbij x).injOn (fun m _ => rfl) (fun m hm => ?_) h
  rw [← hfix x' m hm, ← h, hfix x m hm]

/-- **FB 3 (surjectivity).** -/
theorem surjective_fibreMapOf (Φ : S.E → S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x)
    (hbij : ∀ x₀, Set.BijOn Φ {x | S.SameTail N x x₀} {x | S.SameTail N x x₀})
    (t : TailSpace N) : Function.Surjective (S.fibreMapOf N Φ t) := by
  by_cases ht : S.TailSummable N t
  · intro w
    set y := S.R (S.headRec N w t) with hy
    obtain ⟨x, hx, hxy⟩ := (hbij y).surjOn (show y ∈ {x | S.SameTail N x y} from fun m _ => rfl)
    have hws := (S.summable_headRec_iff N w t).2 ht
    have hxt : ∀ m (hm : m ∉ symmetricModes N),
        S.coordE x m = t ⟨m, by simpa using hm⟩ := by
      intro m hm
      have h1 : S.coord m x = S.coord m y := hx m hm
      rw [hy, S.coord_R hws] at h1
      exact h1.trans (S.headRec_apply_not_mem N _ _ hm)
    refine ⟨S.headPt N (S.coordE x), ?_⟩
    have hrec : S.headRec N (S.headPt N (S.coordE x)) t = S.coordE x :=
      S.headRec_headPt_of_tail N _ t hxt
    have hR : S.R (S.headRec N (S.headPt N (S.coordE x)) t) = x := by
      rw [hrec, S.realE_coordE]
    have h1 := S.headRec_fibreMapOf N Φ t (S.headPt N (S.coordE x)) ht
      (by rw [hR]; exact hfix x)
    rw [hR, hxy, hy, S.coordE_realE _ hws] at h1
    exact S.headRec_injective_left N h1
  · intro w
    exact ⟨w, S.fibreMapOf_of_not_summable N Φ t w ht⟩

theorem bijective_fibreMapOf (Φ : S.E → S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x)
    (hbij : ∀ x₀, Set.BijOn Φ {x | S.SameTail N x x₀} {x | S.SameTail N x x₀})
    (t : TailSpace N) : Function.Bijective (S.fibreMapOf N Φ t) :=
  ⟨fun _ _ h => S.injOn_fibreMapOf N Φ hfix Set.univ
      (Set.injOn_univ.2 (S.injective_of_bijOn_fibre N Φ hfix hbij)) t
        (Set.mem_univ _) (Set.mem_univ _) h, S.surjective_fibreMapOf N Φ hfix hbij t⟩

theorem continuous_headPt' : Continuous (S.headPt N) :=
  (S.headCoord N).symm.toContinuousLinearEquiv.continuous.comp
    (continuous_pi fun _ => continuous_apply _)

theorem continuous_coordE : Continuous S.coordE :=
  continuous_pi fun n => (S.coord n).continuous

/-- `x ↦ headPt (coordE x)` as a real-linear map `E → V`. -/
def headCoordLinE : S.E →ₗ[ℝ] S.head N where
  toFun x := S.headPt N (S.coordE x)
  map_add' x y := by
    unfold headPt
    rw [← map_add]
    congr 1
    funext i
    exact S.coord_add x y _
  map_smul' r x := by
    unfold headPt
    simp only [RingHom.id_apply]
    rw [← map_smul]
    congr 1
    funext i
    exact S.coord_smul r x _

/-- `x ↦ headPt (coordE x)` as a continuous real-linear map `E → V`.  (Old: `headCoord`; renamed
because `S.headCoord N` is the head coordinate equivalence of GA1.) -/
def headCoordE : S.E →L[ℝ] S.head N :=
  { S.headCoordLinE N with
    cont := (S.continuous_headPt' N).comp S.continuous_coordE }

theorem headCoordE_apply (x : S.E) : S.headCoordE N x = S.headPt N (S.coordE x) := rfl

theorem fibreMapOf_of_summable' (Φ : S.E → S.E)
    (t : TailSpace N) (h : S.TailSummable N t) :
    S.fibreMapOf N Φ t =
      fun v => S.headCoordE N (Φ (S.tailBase N t + S.headToE N v)) :=
  funext fun v => S.fibreMapOf_of_summable N Φ t v h

theorem fibreMapOf_of_not_summable' (Φ : S.E → S.E)
    (t : TailSpace N) (h : ¬ S.TailSummable N t) :
    S.fibreMapOf N Φ t = id :=
  funext fun v => S.fibreMapOf_of_not_summable N Φ t v h

/-- Continuity of the fibre maps of a continuous `Φ`. -/
theorem continuous_fibreMapOf (Φ : S.E → S.E)
    (hΦ : Continuous Φ) (t : TailSpace N) : Continuous (S.fibreMapOf N Φ t) := by
  by_cases ht : S.TailSummable N t
  · rw [S.fibreMapOf_of_summable' N Φ t ht]
    exact (S.headCoordE N).continuous.comp
      (hΦ.comp (continuous_const.add (S.headToE N).continuous))
  · rw [S.fibreMapOf_of_not_summable' N Φ t ht]
    exact continuous_id

/-- **FB 3 (equivalence).** For a bijection `Φ` of `E` fixing tails, the fibre maps form a family
of bijections `V ≃ V`, with inverse the fibre maps of `Φ⁻¹`. -/
def fibreEquivOf (Φ : S.E ≃ S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x) (t : TailSpace N) :
    S.head N ≃ S.head N where
  toFun := S.fibreMapOf N Φ t
  invFun := S.fibreMapOf N Φ.symm t
  left_inv v := S.fibreMapOf_comp_fibreMapOf N Φ Φ.symm hfix (S.hfix_symm N Φ hfix)
    (fun x => Φ.symm_apply_apply x) t v
  right_inv w := S.fibreMapOf_comp_fibreMapOf N Φ.symm Φ (S.hfix_symm N Φ hfix) hfix
    (fun x => Φ.apply_symm_apply x) t w

theorem fibreEquivOf_apply (Φ : S.E ≃ S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x) (t : TailSpace N) (v : S.head N) :
    S.fibreEquivOf N Φ hfix t v = S.fibreMapOf N Φ t v := rfl

/-- **FB 3 (homeomorphism).** For a homeomorphism `Φ` of `E` fixing tails, the fibre maps form a
family `V ≃ₜ V`. -/
def fibreHomeoOf (Φ : S.E ≃ₜ S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x) (t : TailSpace N) :
    S.head N ≃ₜ S.head N where
  toEquiv := S.fibreEquivOf N Φ.toEquiv hfix t
  continuous_toFun := S.continuous_fibreMapOf N Φ Φ.continuous t
  continuous_invFun := S.continuous_fibreMapOf N Φ.symm Φ.symm.continuous t

theorem fibreHomeoOf_apply (Φ : S.E ≃ₜ S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x) (t : TailSpace N) (v : S.head N) :
    S.fibreHomeoOf N Φ hfix t v = S.fibreMapOf N Φ t v := rfl

theorem fibreHomeoOf_symm_apply (Φ : S.E ≃ₜ S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x) (t : TailSpace N) (v : S.head N) :
    (S.fibreHomeoOf N Φ hfix t).symm v = S.fibreMapOf N Φ.symm t v := rfl

end Bridge

end NlsGge.Ramer.General.RamerSetting

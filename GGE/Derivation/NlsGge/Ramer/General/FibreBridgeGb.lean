import NlsGge.Ramer.General.FibreBridgeGa

/-!
# FB (part b), generalized (GD4b): differentiability, linear `Φ`, pushforward of `γ_E`,
local change of variables on `E`, over a `RamerSetting S`

Adapted from the second half of `NlsGge/Ramer/FibreBridge.lean` (goals 4-6').  See
`FibreBridgeGa`.  The slices `v ↦ S.R (headRec v t) = tailBase t + headToE v` are affine with the
linear part `S.headToE N = S.incl ∘ subtype` (GB1); only continuity of `headToE` and of the
coordinate maps `S.coord n` is used, so anisotropy does not enter.  The measure layer is G1
(`S.γ`, `S.γE`, `S.R`, `S.coordE`).
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

/-! ### Goal 4 -/

/-- **FB 4.** Differentiability along head directions transfers to the fibre maps.  The slice
parametrization `v ↦ R (headRec v t) = tailBase t + headToE v` is affine. -/
theorem differentiableAt_fibreMapOf (Φ : S.E → S.E)
    (t : TailSpace N) (v₀ : S.head N)
    (hd : S.TailSummable N t →
      DifferentiableAt ℝ (fun v : S.head N =>
        Φ (S.tailBase N t + S.headToE N v)) v₀) :
    DifferentiableAt ℝ (S.fibreMapOf N Φ t) v₀ := by
  by_cases ht : S.TailSummable N t
  · rw [S.fibreMapOf_of_summable' N Φ t ht]
    exact (S.headCoordE N).differentiableAt.comp v₀ (hd ht)
  · rw [S.fibreMapOf_of_not_summable' N Φ t ht]
    exact differentiableAt_id

/-- **FB 4 (pointwise head-direction form).** If `h ↦ Φ (x + headToE h)` is differentiable at `0`
for `x = R (headRec v₀ t)`, then `fibreMapOf Φ t` is differentiable at `v₀`. -/
theorem differentiableAt_fibreMapOf_of_head
    (Φ : S.E → S.E)
    (t : TailSpace N) (v₀ : S.head N)
    (hd : DifferentiableAt ℝ (fun h : S.head N =>
        Φ (S.R (S.headRec N v₀ t) + S.headToE N h)) 0) :
    DifferentiableAt ℝ (S.fibreMapOf N Φ t) v₀ := by
  refine S.differentiableAt_fibreMapOf N Φ t v₀ (fun ht => ?_)
  have e : (fun v : S.head N => Φ (S.tailBase N t + S.headToE N v)) =
      (fun h : S.head N => Φ (S.R (S.headRec N v₀ t) + S.headToE N h)) ∘
        (fun v => v - v₀) := by
    funext v
    simp only [Function.comp, S.realE_headRec N v₀ t ht, map_sub]
    congr 1
    abel
  rw [e]
  have hd' : DifferentiableAt ℝ (fun h : S.head N =>
      Φ (S.R (S.headRec N v₀ t) + S.headToE N h)) (v₀ - v₀) := by
    rw [sub_self]; exact hd
  exact DifferentiableAt.comp v₀ hd' (differentiableAt_id.sub_const v₀)

/-! ### Goal 5: linear `Φ` -/

theorem headCoordE_headToE (v : S.head N) : S.headCoordE N (S.headToE N v) = v := by
  apply Subtype.ext
  apply S.hcoord_ext
  intro m
  rw [S.headCoordE_apply, S.hcoord_headPt]
  by_cases hm : m ∈ symmetricModes N
  · rw [if_pos hm]; exact S.coordE_headToE N v m
  · rw [if_neg hm, S.hcoord_head_eq_zero N v hm]

theorem eq_headToE_headCoordE (x : S.E)
    (hx : ∀ m ∉ symmetricModes N, S.coord m x = 0) :
    x = S.headToE N (S.headCoordE N x) := by
  apply S.coordE_injective
  funext m
  rw [S.coordE_headToE, S.headCoordE_apply, S.hcoord_headPt]
  by_cases hm : m ∈ symmetricModes N
  · rw [if_pos hm]
  · rw [if_neg hm]; exact hx m hm

/-- The tail-independent linear part of the fibre maps of a linear `Φ`. -/
def fibreLin (Φ : S.E →L[ℝ] S.E) : S.head N →L[ℝ] S.head N :=
  (S.headCoordE N).comp (Φ.comp (S.headToE N))

theorem fibreLin_apply (Φ : S.E →L[ℝ] S.E) (v : S.head N) :
    S.fibreLin N Φ v = S.headCoordE N (Φ (S.headToE N v)) := rfl

theorem map_headToE_eq (Φ : S.E →L[ℝ] S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x) (v : S.head N) :
    Φ (S.headToE N v) = S.headToE N (S.fibreLin N Φ v) := by
  apply S.eq_headToE_headCoordE
  intro m hm
  rw [hfix _ m hm, S.headToE_coord, S.hcoord_head_eq_zero N v hm]

theorem hfix_symm_clm (Φ : S.E ≃L[ℝ] S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x) (y : S.E) :
    S.SameTail N (Φ.symm y) y := by
  intro m hm
  have := hfix (Φ.symm y) m hm
  rw [Φ.apply_symm_apply] at this
  exact this.symm

/-- The fibre linear part is a continuous linear equivalence of `V`. -/
def fibreLinEquiv (Φ : S.E ≃L[ℝ] S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x) : S.head N ≃L[ℝ] S.head N :=
  ContinuousLinearEquiv.equivOfInverse
    (S.fibreLin N (Φ : S.E →L[ℝ] S.E))
    (S.fibreLin N (Φ.symm : S.E →L[ℝ] S.E))
    (fun v => by
      have h1 := S.map_headToE_eq N (Φ : S.E →L[ℝ] S.E) hfix v
      have h2 : Φ.symm (S.headToE N (S.fibreLin N
          (Φ : S.E →L[ℝ] S.E) v)) = S.headToE N v := by
        have : Φ (S.headToE N v) = S.headToE N (S.fibreLin N
          (Φ : S.E →L[ℝ] S.E) v) := h1
        rw [← this, Φ.symm_apply_apply]
      rw [S.fibreLin_apply]
      show S.headCoordE N (Φ.symm _) = v
      rw [h2, S.headCoordE_headToE])
    (fun v => by
      have h1 := S.map_headToE_eq N (Φ.symm : S.E →L[ℝ] S.E)
        (S.hfix_symm_clm N Φ hfix) v
      have h2 : Φ (S.headToE N (S.fibreLin N
          (Φ.symm : S.E →L[ℝ] S.E) v)) = S.headToE N v := by
        have : Φ.symm (S.headToE N v) = S.headToE N (S.fibreLin N
          (Φ.symm : S.E →L[ℝ] S.E) v) := h1
        rw [← this, Φ.apply_symm_apply]
      rw [S.fibreLin_apply]
      show S.headCoordE N (Φ _) = v
      rw [h2, S.headCoordE_headToE])

/-- **FB 5.** For a continuous linear automorphism `Φ` of `E` fixing tails, each fibre map is an
affine homeomorphism of `V`: `fibreMapOf Φ t = A + b_t`, with `A` a continuous linear
equivalence (independent of `t`) and `b_t = headCoordE (Φ (tailBase t))` (or `id` for a
non-summable tail). -/
theorem fibreMapOf_affine (Φ : S.E ≃L[ℝ] S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x) (t : TailSpace N) :
    ∃ (A : S.head N ≃L[ℝ] S.head N) (b : S.head N),
      ∀ v, S.fibreMapOf N Φ t v = A v + b := by
  by_cases ht : S.TailSummable N t
  · refine ⟨S.fibreLinEquiv N Φ hfix, S.headCoordE N (Φ (S.tailBase N t)), fun v => ?_⟩
    rw [S.fibreMapOf_of_summable N Φ t v ht]
    change S.headCoordE N (Φ (S.tailBase N t + S.headToE N v)) = _
    rw [map_add, map_add, add_comm]
    rfl
  · exact ⟨ContinuousLinearEquiv.refl ℝ _, 0, fun v => by
      rw [S.fibreMapOf_of_not_summable N Φ t v ht]; simp⟩

/-- **FB 5 (S_Π).** The family of fibre homeomorphisms `TailSpace N → V ≃ₜ V` attached to a
continuous linear automorphism of `E` fixing tails. -/
def fibreHomeoOfCLE (Φ : S.E ≃L[ℝ] S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x) (t : TailSpace N) :
    S.head N ≃ₜ S.head N :=
  S.fibreHomeoOf N Φ.toHomeomorph hfix t

theorem fibreHomeoOfCLE_apply (Φ : S.E ≃L[ℝ] S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x) (t : TailSpace N) (v : S.head N) :
    S.fibreHomeoOfCLE N Φ hfix t v = S.fibreMapOf N Φ t v := rfl

theorem differentiable_fibreMapOf (Φ : S.E ≃L[ℝ] S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x) (t : TailSpace N) :
    Differentiable ℝ (S.fibreMapOf N Φ t) := by
  obtain ⟨A, b, h⟩ := S.fibreMapOf_affine N Φ hfix t
  have : S.fibreMapOf N Φ t = fun v => A v + b := funext h
  rw [this]
  exact A.differentiable.add_const b

open Classical in
theorem fderiv_fibreMapOf (Φ : S.E ≃L[ℝ] S.E)
    (t : TailSpace N) (v : S.head N) :
    fderiv ℝ (S.fibreMapOf N Φ t) v =
      (if S.TailSummable N t then
        (S.fibreLin N (Φ : S.E →L[ℝ] S.E))
      else ContinuousLinearMap.id ℝ _) := by
  by_cases ht : S.TailSummable N t
  · rw [if_pos ht]
    have e : S.fibreMapOf N Φ t = fun v => S.fibreLin N
        (Φ : S.E →L[ℝ] S.E) v +
        S.headCoordE N (Φ (S.tailBase N t)) := by
      funext v
      rw [S.fibreMapOf_of_summable N Φ t v ht]
      change S.headCoordE N (Φ (S.tailBase N t + S.headToE N v)) = _
      rw [map_add, map_add, add_comm]
      rfl
    rw [e]
    exact ((S.fibreLin N
      (Φ : S.E →L[ℝ] S.E)).hasFDerivAt.add_const _).fderiv
  · rw [if_neg ht, S.fibreMapOf_of_not_summable' N Φ t ht]
    exact (hasFDerivAt_id v).fderiv

/-- Measurability of the fibre Jacobian from measurability of `T` and of the fibre determinant. -/
theorem measurable_fibreJ_of_det (T : TailSpace N → S.head N → S.head N)
    (hS : Measurable (Function.uncurry T))
    (hdet : Measurable (fun z : ℤ → ℂ =>
      (fderiv ℝ (T (tailPt N z)) (S.headPt N z)).det)) :
    Measurable (S.fibreJ N T) := by
  have hz : Measurable (fun z : ℤ → ℂ => (tailPt N z, S.headPt N z)) :=
    (measurable_tailPt N).prodMk (S.measurable_headPt N)
  have h1 : Measurable (fun z : ℤ → ℂ => T (tailPt N z) (S.headPt N z)) := hS.comp hz
  have hnorm : Measurable (fun z : ℤ → ℂ => ‖T (tailPt N z) (S.headPt N z)‖) := h1.norm
  have hnorm2 : Measurable (fun z : ℤ → ℂ => ‖S.headPt N z‖) := (S.measurable_headPt N).norm
  have hexp : Measurable (fun z : ℤ → ℂ => Real.exp (-(‖T (tailPt N z) (S.headPt N z)‖ ^ 2 -
      ‖S.headPt N z‖ ^ 2) / 2)) :=
    Real.measurable_exp.comp (((hnorm.pow_const 2).sub (hnorm2.pow_const 2)).neg.div_const 2)
  have hab := hdet.abs
  unfold fibreJ finiteRamerDensity
  exact hab.mul hexp

/-- Measurability of the fibre Jacobian for a linear `Φ` fixing tails. -/
theorem measurable_fibreJ_of_clm (Φ : S.E ≃L[ℝ] S.E) :
    Measurable (S.fibreJ N (S.fibreMapOf N Φ)) := by
  classical
  have hS := S.measurable_fibreMapOf N Φ Φ.continuous.measurable
  have hset : MeasurableSet {z : ℤ → ℂ | S.TailSummable N (tailPt N z)} :=
    (S.measurableSet_tailSummable N).preimage (measurable_tailPt N)
  refine S.measurable_fibreJ_of_det N _ hS ?_
  have : (fun z : ℤ → ℂ =>
      (fderiv ℝ (S.fibreMapOf N Φ (tailPt N z)) (S.headPt N z)).det) =
      fun z => if S.TailSummable N (tailPt N z) then
        (S.fibreLin N (Φ : S.E →L[ℝ] S.E)).det
        else 1 := by
    funext z
    rw [S.fderiv_fibreMapOf N Φ]
    split_ifs
    · rfl
    · simp [ContinuousLinearMap.det]
  rw [this]
  exact Measurable.ite hset measurable_const measurable_const

/-! ### Goal 6 -/

/-- (Old: `ae_weightedSquareSummable_coordE_realE`.) -/
theorem ae_memE_coordE_realE :
    ∀ᵐ z ∂S.γ, S.memE z ∧ S.coordE (S.R z) = z := by
  filter_upwards [S.ae_memE, S.coordE_R_ae] with z h1 h2 using ⟨h1, h2⟩

/-- **FB 6 (homeomorphism form).**  `(Φ⁻¹)_# γ_E = J γ_E` with `J = fibreJ ∘ coordE`, for a
homeomorphism `Φ` of `E` fixing tails whose fibre maps are differentiable with measurable fibre
Jacobian. -/
theorem map_symm_eq_withDensity_of_homeo
    (Φ : S.E ≃ₜ S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x)
    (hJm : Measurable (S.fibreJ N (S.fibreMapOf N Φ)))
    (hd : ∀ t, Differentiable ℝ (S.fibreMapOf N Φ t)) :
    S.γE.map Φ.symm =
      S.γE.withDensity
        (fun x => ENNReal.ofReal (S.fibreJ N (S.fibreMapOf N Φ) (S.coordE x))) := by
  set γ := S.γ with hγ
  have hRm := S.measurable_R
  have hγE : S.γE = γ.map S.R := rfl
  have hfixS : ∀ x, S.SameTail N (Φ.symm x) x := fun x =>
    S.hfix_symm N Φ.toEquiv hfix x
  have hSm : Measurable (Function.uncurry (fun t => (S.fibreHomeoOf N Φ hfix t :
      S.head N → S.head N))) :=
    S.measurable_fibreMapOf N Φ Φ.continuous.measurable
  have key := S.map_fibreActInv N (S.fibreHomeoOf N Φ hfix) hSm hJm hd
  have hΨ : S.fibreActInv N (S.fibreHomeoOf N Φ hfix) = S.fibreAct N (S.fibreMapOf N Φ.symm) :=
    rfl
  have hΨm : Measurable (S.fibreActInv N (S.fibreHomeoOf N Φ hfix)) := by
    rw [hΨ]
    exact S.measurable_fibreAct N _ (S.measurable_fibreMapOf N Φ.symm
      Φ.symm.continuous.measurable)
  ext B hB
  have hmeas : Measurable (fun x : S.E =>
      ENNReal.ofReal (S.fibreJ N (S.fibreMapOf N Φ) (S.coordE x))) :=
    (hJm.comp S.measurable_coordE).ennreal_ofReal
  have hset : (fun z => z ∈ S.R ⁻¹' (Φ.symm ⁻¹' B)) =ᵐ[γ]
      (fun z => z ∈ S.fibreActInv N (S.fibreHomeoOf N Φ hfix) ⁻¹' (S.R ⁻¹' B)) := by
    filter_upwards [S.ae_memE_coordE_realE] with z hz
    have h1 := S.coordE_comp_realE_eq_fibreAct N Φ.symm hfixS z hz.1
    have h2 : S.R (S.fibreActInv N (S.fibreHomeoOf N Φ hfix) z) = Φ.symm (S.R z) := by
      rw [hΨ, ← h1, S.realE_coordE]
    simp only [Set.mem_preimage, h2]
  calc S.γE.map Φ.symm B
      = γ (S.R ⁻¹' (Φ.symm ⁻¹' B)) := by
        rw [Measure.map_apply Φ.symm.continuous.measurable hB, hγE,
          Measure.map_apply hRm (Φ.symm.continuous.measurable hB)]
    _ = γ (S.fibreActInv N (S.fibreHomeoOf N Φ hfix) ⁻¹' (S.R ⁻¹' B)) :=
        measure_congr (Filter.eventuallyEq_set.2 (by
          filter_upwards [hset] with z hz using by simpa using hz))
    _ = (γ.map (S.fibreActInv N (S.fibreHomeoOf N Φ hfix))) (S.R ⁻¹' B) :=
        (Measure.map_apply hΨm (hRm hB)).symm
    _ = (γ.withDensity (fun z => ENNReal.ofReal
          (S.fibreJ N (S.fibreMapOf N Φ) z))) (S.R ⁻¹' B) := by
        rw [key]; rfl
    _ = ∫⁻ z in S.R ⁻¹' B, ENNReal.ofReal (S.fibreJ N (S.fibreMapOf N Φ) z) ∂γ :=
        withDensity_apply _ (hRm hB)
    _ = ∫⁻ z in S.R ⁻¹' B, ENNReal.ofReal
          (S.fibreJ N (S.fibreMapOf N Φ) (S.coordE (S.R z))) ∂γ := by
        refine setLIntegral_congr_fun_ae (hRm hB) ?_
        filter_upwards [S.ae_memE_coordE_realE] with z hz _
        rw [hz.2]
    _ = ∫⁻ x in B, ENNReal.ofReal (S.fibreJ N (S.fibreMapOf N Φ) (S.coordE x))
          ∂S.γE := by
        rw [hγE, setLIntegral_map hB hmeas hRm]
    _ = _ := (withDensity_apply _ hB).symm

/-- **FB 6.**  For a continuous linear automorphism `Φ` of `E` fixing tails,
`(Φ⁻¹)_# γ_E = γ_E.withDensity (ofReal ∘ fibreJ (fibreMapOf Φ) ∘ coordE)`. -/
theorem map_symm_eq_withDensity
    (Φ : S.E ≃L[ℝ] S.E)
    (hfix : ∀ x, S.SameTail N (Φ x) x) :
    S.γE.map Φ.symm =
      S.γE.withDensity
        (fun x => ENNReal.ofReal (S.fibreJ N (S.fibreMapOf N Φ) (S.coordE x))) :=
  S.map_symm_eq_withDensity_of_homeo N Φ.toHomeomorph hfix
    (S.measurable_fibreJ_of_clm N Φ) (S.differentiable_fibreMapOf N Φ hfix)

/-! ### Goal 6' -/

/-- **FB 6' (local version).**  For `A ⊆ E` measurable with `Φ` injective on `A`, fibre maps
differentiable on the fibres over `A`, and `Φ '' A` measurable (automatic in the application,
where `Φ '' A` is a ball),
`∫_{Φ(A)} f dγ_E = ∫_A f(Φ x) J(coordE x) dγ_E` with `J = fibreJ (fibreMapOf Φ)`.  Proof: apply
R2 (`lintegral_image_fibreAct`) to `coordE '' A = {z | summable z ∧ R z ∈ A}`. -/
theorem lintegral_image_eq_fibre
    (Φ : S.E → S.E) (hΦm : Measurable Φ)
    (hfix : ∀ x, S.SameTail N (Φ x) x)
    (hJm : Measurable (S.fibreJ N (S.fibreMapOf N Φ)))
    (A : Set S.E) (hA : MeasurableSet A)
    (hΦA : MeasurableSet (Φ '' A)) (hinj : Set.InjOn Φ A)
    (hdiff : ∀ (t : TailSpace N) (v : S.head N),
      S.memE (S.headRec N v t) →
      S.R (S.headRec N v t) ∈ A → DifferentiableAt ℝ (S.fibreMapOf N Φ t) v)
    (f : S.E → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y in Φ '' A, f y ∂S.γE =
      ∫⁻ x in A, f (Φ x) * ENNReal.ofReal (S.fibreJ N (S.fibreMapOf N Φ) (S.coordE x))
        ∂S.γE := by
  set γ := S.γ with hγ
  have hRm := S.measurable_R
  have hγE : S.γE = γ.map S.R := rfl
  set A' : Set (ℤ → ℂ) := S.coordE '' A with hA'def
  have hA'eq : A' = {z | S.memE z} ∩ S.R ⁻¹' A := by
    ext z
    rw [hA'def, S.mem_coordE_image_iff]
    rfl
  have hA' : MeasurableSet A' := by
    rw [hA'eq]
    exact S.measurableSet_memE.inter (hRm hA)
  have hSm := S.measurable_fibreMapOf N Φ hΦm
  have hR2 := S.lintegral_image_fibreAct N (S.fibreMapOf N Φ) hSm hJm A' hA'
    (fun t v hv => hdiff t v ((S.mem_coordE_image_iff A _).1 hv).1
      ((S.mem_coordE_image_iff A _).1 hv).2)
    (fun t => (S.injOn_fibreMapOf N Φ hfix A hinj t).mono
      (S.fibreSlice_coordE_subset N A t))
    (fun z => f (S.R z)) (hf.comp hRm)
  have hfa := S.ae_memE_coordE_realE
  -- left side
  have hL : ∫⁻ y in Φ '' A, f y ∂S.γE =
      ∫⁻ z in S.fibreAct N (S.fibreMapOf N Φ) '' A',
        f (S.R z) ∂γ := by
    rw [hγE, setLIntegral_map hΦA hf hRm]
    refine setLIntegral_congr (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [hfa] with z hz
    simp only [Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, hxz⟩
      refine ⟨S.coordE x, ⟨x, hx, rfl⟩, ?_⟩
      rw [← S.coordE_comp_realE_eq_fibreAct N Φ hfix _ (S.memE_coordE x),
        S.realE_coordE, hxz, hz.2]
    · rintro ⟨z', hz', hzz⟩
      obtain ⟨hs', hA''⟩ := (S.mem_coordE_image_iff A _).1 hz'
      refine ⟨S.R z', hA'', ?_⟩
      rw [← S.coordE_comp_realE_eq_fibreAct N Φ hfix z' hs'] at hzz
      rw [← hzz, S.realE_coordE]
  -- right side
  have hmeas : Measurable (fun x : S.E =>
      f (Φ x) * ENNReal.ofReal (S.fibreJ N (S.fibreMapOf N Φ) (S.coordE x))) :=
    (hf.comp hΦm).mul (hJm.comp S.measurable_coordE).ennreal_ofReal
  have hR : ∫⁻ x in A, f (Φ x) * ENNReal.ofReal (S.fibreJ N (S.fibreMapOf N Φ) (S.coordE x))
        ∂S.γE =
      ∫⁻ z in A', f (S.R (S.fibreAct N (S.fibreMapOf N Φ) z)) *
        ENNReal.ofReal (S.fibreJ N (S.fibreMapOf N Φ) z) ∂γ := by
    rw [hγE, setLIntegral_map hA hmeas hRm]
    have hseteq : (S.R ⁻¹' A : Set (ℤ → ℂ)) =ᵐ[γ] A' := by
      refine Filter.eventuallyEq_set.2 ?_
      filter_upwards [hfa] with z hz
      rw [hA'eq]
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨hz.1, h⟩, fun h => h.2⟩
    rw [setLIntegral_congr hseteq]
    refine setLIntegral_congr_fun_ae hA' ?_
    filter_upwards [hfa] with z hz hzA
    have hzA' : S.memE z := ((S.mem_coordE_image_iff A _).1 hzA).1
    rw [← S.coordE_comp_realE_eq_fibreAct N Φ hfix z hzA', S.realE_coordE, hz.2]
  rw [hL, hR]
  exact hR2

end Bridge

end NlsGge.Ramer.General.RamerSetting

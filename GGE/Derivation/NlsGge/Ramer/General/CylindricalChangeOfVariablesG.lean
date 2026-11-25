import NlsGge.Ramer.General.CylindricalDivergenceG
import NlsGge.Ramer.CylindricalChangeOfVariables

/-!
# Head-acting nonlinear change of variables on `S.γ` (GA5)

Generalization of `NlsGge/Ramer/CylindricalChangeOfVariables.lean` to a `RamerSetting S`.
For `T : V_N ≃ₜ V_N` (`V_N = S.head N`) differentiable, `S.headAct N T : (ℤ → ℂ) → (ℤ → ℂ)`
replaces the head coordinates of `z` by those of `T (S.headPt N z)` and keeps the tail.
It is a measurable equivalence and `(T̂⁻¹)_# S.γ = J_T(x_N) S.γ`.

The `S`-independent tail declarations `TailSpace`, `tailPt`, `measurable_tailPt` are reused from
the old file.  Head/tail independence is proved here directly for the law
`countableComplexGaussian q` with arbitrary rates `q` (`indepFun_restrict`).
The self-map of the head is called `T` (the old file calls it `S`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer NlsGge.Measure

/-! ### Independence of coordinate restrictions, for arbitrary rates -/

theorem comap_restrict_eq (A : Set ℤ) :
    MeasurableSpace.comap (fun z : ℤ → ℂ => fun a : A => z a.1) MeasurableSpace.pi =
      ⨆ i ∈ A, MeasurableSpace.comap (fun z : ℤ → ℂ => z i) inferInstance := by
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, iSup_subtype']
  refine iSup_congr (fun a => ?_)
  rw [MeasurableSpace.comap_comp]; rfl

theorem indepFun_restrict (q : ℤ → ℝ) (A : Set ℤ) :
    ProbabilityTheory.IndepFun (fun z : ℤ → ℂ => fun a : A => z a.1)
      (fun z : ℤ → ℂ => fun i : (Aᶜ : Set ℤ) => z i.1) (countableComplexGaussian q) := by
  have h := ProbabilityTheory.iIndepFun_infinitePi (P := fun n : ℤ => complexGaussian (q n))
    (X := fun _ x => x) (fun _ => measurable_id)
  have h2 := (ProbabilityTheory.iIndepFun_iff_iIndep _ _ _).1 h
  have h3 := ProbabilityTheory.indep_iSup_of_disjoint
    (fun i => ((measurable_pi_apply i).comap_le)) h2 (disjoint_compl_right (a := A))
  rw [ProbabilityTheory.IndepFun_iff_Indep, comap_restrict_eq, comap_restrict_eq]
  exact h3

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- Head-acting map, for an arbitrary self-map `T` of the head. -/
def headAct (N : ℕ) (T : S.head N → S.head N) (z : ℤ → ℂ) : ℤ → ℂ :=
  fun n => if n ∈ symmetricModes N then S.hcoord (T (S.headPt N z) : S.H) n else z n

theorem hcoord_head_eq_zero (N : ℕ) (v : S.head N) {n : ℤ} (hn : n ∉ symmetricModes N) :
    S.hcoord (v : S.H) n = 0 := v.2 n hn

theorem headPt_headAct (N : ℕ) (T : S.head N → S.head N) (z : ℤ → ℂ) :
    S.headPt N (S.headAct N T z) = T (S.headPt N z) := by
  apply Subtype.ext
  apply S.hcoord_ext
  intro n
  rw [hcoord_headPt]
  by_cases hn : n ∈ symmetricModes N
  · simp [headAct, hn]
  · simp [hn, S.hcoord_head_eq_zero N _ hn]

theorem headAct_headAct (N : ℕ) (T T' : S.head N → S.head N) (z : ℤ → ℂ)
    (h : T' (T (S.headPt N z)) = S.headPt N z) :
    S.headAct N T' (S.headAct N T z) = z := by
  funext n
  by_cases hn : n ∈ symmetricModes N
  · simp only [headAct, hn, if_true]
    rw [headPt_headAct, h, hcoord_headPt]; simp [hn]
  · simp [headAct, hn]

theorem measurable_hcoord_head (N : ℕ) {n : ℤ} (hn : n ∈ symmetricModes N) :
    Measurable (fun v : S.head N => S.hcoord (v : S.H) n) := by
  rw [symmetricModes_eq_image] at hn
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hn
  have : Continuous (fun v : S.head N => (S.headCoord N v) j) :=
    (continuous_apply j).comp (S.headCoord N).toContinuousLinearEquiv.continuous
  exact this.measurable

theorem measurable_headAct (N : ℕ) (T : S.head N → S.head N) (hT : Measurable T) :
    Measurable (S.headAct N T) := by
  refine measurable_pi_iff.2 (fun n => ?_)
  by_cases hn : n ∈ symmetricModes N
  · simp only [headAct, hn, if_true]
    exact (S.measurable_hcoord_head N hn).comp (hT.comp (S.measurable_headPt N))
  · simp only [headAct, hn, if_false]; exact measurable_pi_apply n

/-- The head-acting measurable equivalence. -/
def headActEquiv (N : ℕ) (T : S.head N ≃ₜ S.head N) : (ℤ → ℂ) ≃ᵐ (ℤ → ℂ) where
  toFun := S.headAct N T
  invFun := S.headAct N T.symm
  left_inv z := S.headAct_headAct N T T.symm z (T.symm_apply_apply _)
  right_inv z := S.headAct_headAct N T.symm T z (T.apply_symm_apply _)
  measurable_toFun := S.measurable_headAct N T T.continuous.measurable
  measurable_invFun := S.measurable_headAct N T.symm T.symm.continuous.measurable

/-! ### Head/tail splitting of the sample -/

/-- Reassemble a sample from a head point and a tail. -/
def headRec (N : ℕ) (v : S.head N) (t : TailSpace N) : ℤ → ℂ :=
  fun n => if h : n ∈ symmetricModes N then S.hcoord (v : S.H) n
    else t ⟨n, by simpa using h⟩

theorem measurable_headRec (N : ℕ) :
    Measurable (fun p : S.head N × TailSpace N => S.headRec N p.1 p.2) := by
  refine measurable_pi_iff.2 (fun n => ?_)
  by_cases hn : n ∈ symmetricModes N
  · simp only [headRec, hn, dif_pos]
    exact (S.measurable_hcoord_head N hn).comp measurable_fst
  · simp only [headRec, hn, dif_neg, not_false_eq_true]
    exact (measurable_pi_apply _).comp measurable_snd

theorem headRec_headPt_tailPt (N : ℕ) (z : ℤ → ℂ) :
    S.headRec N (S.headPt N z) (tailPt N z) = z := by
  funext n
  by_cases hn : n ∈ symmetricModes N
  · simp [headRec, hn, hcoord_headPt]
  · simp [headRec, hn, tailPt]

theorem headAct_eq_headRec (N : ℕ) (T : S.head N → S.head N) (z : ℤ → ℂ) :
    S.headAct N T z = S.headRec N (T (S.headPt N z)) (tailPt N z) := by
  funext n
  by_cases hn : n ∈ symmetricModes N
  · simp [headAct, headRec, hn]
  · simp [headAct, headRec, hn, tailPt]

/-- Under `S.γ`, the head point and the tail are independent. -/
theorem indepFun_headPt_tailPt (N : ℕ) :
    ProbabilityTheory.IndepFun (S.headPt N) (tailPt N) S.γ := by
  classical
  have h := indepFun_restrict S.q (symmetricModes N : Set ℤ)
  let g : (((symmetricModes N : Set ℤ)) → ℂ) → S.head N :=
    fun w => (S.headCoord N).symm
      (fun i => w ⟨modeIndex N i, by simpa using modeIndex_mem_symmetricModes N i⟩)
  have hg : Measurable g := by
    refine (S.headCoord N).symm.toContinuousLinearEquiv.continuous.measurable.comp ?_
    exact measurable_pi_iff.2 (fun i => measurable_pi_apply _)
  have := h.comp hg measurable_id
  exact this

/-- Joint law of (head point, tail) under `S.γ`. -/
theorem map_headPt_tailPt (N : ℕ) :
    S.γ.map (fun z => (S.headPt N z, tailPt N z)) =
      (finiteStdGaussian (S.head N)).prod (S.γ.map (tailPt N)) := by
  rw [← S.headPt_map N]
  exact ((ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    (S.measurable_headPt N).aemeasurable (measurable_tailPt N).aemeasurable).1
    (S.indepFun_headPt_tailPt N))

/-! ### The change-of-variables formula -/

/-- **Head-acting change of variables on `S.γ`** (inverse-pushforward orientation).
`(T̂⁻¹)_# S.γ = J_T(x_N) S.γ`, with `J_T = finiteRamerDensity T`, for a differentiable
homeomorphism `T` of the head `V_N`. -/
theorem map_headActEquiv_symm (N : ℕ)
    (T : S.head N ≃ₜ S.head N) (hT : Differentiable ℝ T) :
    S.γ.map (S.headActEquiv N T).symm =
      S.γ.withDensity
        (fun z => ENNReal.ofReal
          (finiteRamerDensity (T : S.head N → S.head N) (S.headPt N z))) := by
  set γ := S.γ with hγ
  have : IsProbabilityMeasure γ := by rw [hγ]; infer_instance
  set μτ := γ.map (tailPt N) with hμτ
  have : IsProbabilityMeasure μτ :=
    (Measure.isProbabilityMeasure_map_iff (measurable_tailPt N).aemeasurable).2 inferInstance
  set ρ : S.head N → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (finiteRamerDensity (T : S.head N → S.head N) x) with hρ
  have hρm : Measurable ρ := (measurable_finiteRamerDensity T).ennreal_ofReal
  have hP : Measurable (fun z : ℤ → ℂ => (S.headPt N z, tailPt N z)) :=
    (S.measurable_headPt N).prodMk (measurable_tailPt N)
  have hR := S.measurable_headRec N
  have hSs : Measurable (fun p : S.head N × TailSpace N => (T.symm p.1, p.2)) :=
    (T.symm.continuous.measurable.comp measurable_fst).prodMk measurable_snd
  ext B hB
  have hcomp : ∀ z, (S.headActEquiv N T).symm z =
      S.headRec N (T.symm (S.headPt N z)) (tailPt N z) := fun z =>
    S.headAct_eq_headRec N T.symm z
  have hpre : (S.headActEquiv N T).symm ⁻¹' B =
      (fun z => (S.headPt N z, tailPt N z)) ⁻¹'
        ((fun p : S.head N × TailSpace N => (T.symm p.1, p.2)) ⁻¹'
          ((fun p : S.head N × TailSpace N => S.headRec N p.1 p.2) ⁻¹' B)) := by
    ext z; simp [hcomp]
  have hW : MeasurableSet ((fun p : S.head N × TailSpace N => (T.symm p.1, p.2)) ⁻¹'
          ((fun p : S.head N × TailSpace N => S.headRec N p.1 p.2) ⁻¹' B)) :=
    hSs (hR hB)
  have hRB : MeasurableSet
      ((fun p : S.head N × TailSpace N => S.headRec N p.1 p.2) ⁻¹' B) := hR hB
  rw [Measure.map_apply (S.headActEquiv N T).symm.measurable hB, hpre,
    ← Measure.map_apply hP hW, S.map_headPt_tailPt, ← hμτ]
  have hprod : ((finiteStdGaussian (S.head N)).prod μτ).map
      (fun p : S.head N × TailSpace N => (T.symm p.1, p.2)) =
      ((finiteStdGaussian (S.head N)).withDensity ρ).prod μτ := by
    have := Measure.map_prod_map (finiteStdGaussian (S.head N)) μτ
      (f := (T.symm : S.head N → S.head N)) (g := id)
      T.symm.continuous.measurable measurable_id
    rw [Measure.map_id] at this
    rw [← finiteStdGaussian_map_symm T hT]
    exact this.symm
  rw [← Measure.map_apply hSs hRB, hprod, prod_withDensity_left hρm,
    withDensity_apply _ hRB, withDensity_apply _ hB, ← S.map_headPt_tailPt]
  rw [setLIntegral_map hRB (f := fun p : S.head N × TailSpace N => ρ p.1)
    (hρm.comp measurable_fst) hP]
  have : (fun z : ℤ → ℂ => (S.headPt N z, tailPt N z)) ⁻¹'
      ((fun p : S.head N × TailSpace N => S.headRec N p.1 p.2) ⁻¹' B) = B := by
    ext z; simp [headRec_headPt_tailPt]
  rw [this]

/-- Mass one of the head Ramer density on `S.γ`. -/
theorem lintegral_finiteRamerDensity_headPt (N : ℕ)
    (T : S.head N ≃ₜ S.head N) (hT : Differentiable ℝ T) :
    ∫⁻ z, ENNReal.ofReal
        (finiteRamerDensity (T : S.head N → S.head N) (S.headPt N z)) ∂S.γ = 1 := by
  rw [← lintegral_map (f := fun x => ENNReal.ofReal
      (finiteRamerDensity (T : S.head N → S.head N) x))
    (measurable_finiteRamerDensity T).ennreal_ofReal (S.measurable_headPt N), S.headPt_map]
  exact lintegral_finiteRamerDensity T hT

end NlsGge.Ramer.General.RamerSetting

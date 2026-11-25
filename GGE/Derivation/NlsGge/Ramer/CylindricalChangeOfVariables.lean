import NlsGge.Ramer.CylindricalDivergence
import NlsGge.Measure.RawHeadTailIndepFunPublicRestrictionsV1

/-!
# Head-acting nonlinear change of variables on the full law

See `CylindricalChangeOfVariables.md`.  For `S : V_N ≃ₜ V_N` (`V_N = actualCMHead c N`)
differentiable, `headAct S : (ℤ → ℂ) → (ℤ → ℂ)` replaces the head coordinates of `z` by those of
`S (headPt z)` and keeps the tail.  It is a measurable equivalence and
`(Ŝ⁻¹)_# γ = J_S(x_N) γ` with `J_S = finiteRamerDensity S`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot

variable {lower upper : ℝ}

/-- Head-acting map, for an arbitrary self-map `S` of the head. -/
def headAct (c : BoundedCoefficients lower upper) (N : ℕ) (S : actualCMHead c N → actualCMHead c N)
    (z : ℤ → ℂ) : ℤ → ℂ :=
  fun n => if n ∈ symmetricModes N then cmCoord (S (headPt c N z) : ActualCM c) n else z n

theorem cmCoord_head_eq_zero (c : BoundedCoefficients lower upper) (N : ℕ)
    (v : actualCMHead c N) {n : ℤ} (hn : n ∉ symmetricModes N) :
    cmCoord (v : ActualCM c) n = 0 := v.2 n hn

theorem headPt_headAct (c : BoundedCoefficients lower upper) (N : ℕ)
    (S : actualCMHead c N → actualCMHead c N) (z : ℤ → ℂ) :
    headPt c N (headAct c N S z) = S (headPt c N z) := by
  apply Subtype.ext
  apply cmCoord_ext
  intro n
  rw [cmCoord_headPt]
  by_cases hn : n ∈ symmetricModes N
  · simp [headAct, hn]
  · simp [hn, cmCoord_head_eq_zero c N _ hn]

theorem headAct_headAct (c : BoundedCoefficients lower upper) (N : ℕ)
    (S S' : actualCMHead c N → actualCMHead c N) (z : ℤ → ℂ)
    (h : S' (S (headPt c N z)) = headPt c N z) :
    headAct c N S' (headAct c N S z) = z := by
  funext n
  by_cases hn : n ∈ symmetricModes N
  · simp only [headAct, hn, if_true]
    rw [headPt_headAct, h, cmCoord_headPt]; simp [hn]
  · simp [headAct, hn]

theorem measurable_cmCoord_head (c : BoundedCoefficients lower upper) (N : ℕ) {n : ℤ}
    (hn : n ∈ symmetricModes N) :
    Measurable (fun v : actualCMHead c N => cmCoord (v : ActualCM c) n) := by
  rw [symmetricModes_eq_image] at hn
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hn
  have : Continuous (fun v : actualCMHead c N => (actualCMHeadCoord c N v) j) :=
    (continuous_apply j).comp (actualCMHeadCoord c N).toContinuousLinearEquiv.continuous
  exact this.measurable

theorem measurable_headAct (c : BoundedCoefficients lower upper) (N : ℕ)
    (S : actualCMHead c N → actualCMHead c N) (hS : Measurable S) :
    Measurable (headAct c N S) := by
  refine measurable_pi_iff.2 (fun n => ?_)
  by_cases hn : n ∈ symmetricModes N
  · simp only [headAct, hn, if_true]
    exact (measurable_cmCoord_head c N hn).comp (hS.comp (measurable_headPt c N))
  · simp only [headAct, hn, if_false]; exact measurable_pi_apply n

/-- The head-acting measurable equivalence. -/
def headActEquiv (c : BoundedCoefficients lower upper) (N : ℕ) (S : actualCMHead c N ≃ₜ actualCMHead c N) :
    (ℤ → ℂ) ≃ᵐ (ℤ → ℂ) where
  toFun := headAct c N S
  invFun := headAct c N S.symm
  left_inv z := headAct_headAct c N S S.symm z (S.symm_apply_apply _)
  right_inv z := headAct_headAct c N S.symm S z (S.apply_symm_apply _)
  measurable_toFun := measurable_headAct c N S S.continuous.measurable
  measurable_invFun := measurable_headAct c N S.symm S.symm.continuous.measurable


/-! ### Head/tail splitting of the sample -/

/-- The tail coordinate space `ℂ^{ℤ \ [-N,N]}`. -/
abbrev TailSpace (N : ℕ) : Type := ((symmetricModes N : Set ℤ)ᶜ : Set ℤ) → ℂ

/-- The tail of a sample. -/
def tailPt (N : ℕ) (z : ℤ → ℂ) : TailSpace N := fun i => z i.1

/-- Reassemble a sample from a head point and a tail. -/
def headRec (c : BoundedCoefficients lower upper) (N : ℕ) (v : actualCMHead c N)
    (t : TailSpace N) : ℤ → ℂ :=
  fun n => if h : n ∈ symmetricModes N then cmCoord (v : ActualCM c) n
    else t ⟨n, by simpa using h⟩

theorem measurable_tailPt (N : ℕ) : Measurable (tailPt N) :=
  measurable_pi_iff.2 (fun i => measurable_pi_apply i.1)

theorem measurable_headRec (c : BoundedCoefficients lower upper) (N : ℕ) :
    Measurable (fun p : actualCMHead c N × TailSpace N => headRec c N p.1 p.2) := by
  refine measurable_pi_iff.2 (fun n => ?_)
  by_cases hn : n ∈ symmetricModes N
  · simp only [headRec, hn, dif_pos]
    exact (measurable_cmCoord_head c N hn).comp measurable_fst
  · simp only [headRec, hn, dif_neg, not_false_eq_true]
    exact (measurable_pi_apply _).comp measurable_snd

theorem headRec_headPt_tailPt (c : BoundedCoefficients lower upper) (N : ℕ) (z : ℤ → ℂ) :
    headRec c N (headPt c N z) (tailPt N z) = z := by
  funext n
  by_cases hn : n ∈ symmetricModes N
  · simp [headRec, hn, cmCoord_headPt]
  · simp [headRec, hn, tailPt]

theorem headAct_eq_headRec (c : BoundedCoefficients lower upper) (N : ℕ)
    (S : actualCMHead c N → actualCMHead c N) (z : ℤ → ℂ) :
    headAct c N S z = headRec c N (S (headPt c N z)) (tailPt N z) := by
  funext n
  by_cases hn : n ∈ symmetricModes N
  · simp [headAct, headRec, hn]
  · simp [headAct, headRec, hn, tailPt]

/-- Under the full law, the head point and the tail are independent. -/
theorem indepFun_headPt_tailPt (c : BoundedCoefficients lower upper) (N : ℕ) :
    ProbabilityTheory.IndepFun (headPt c N) (tailPt N)
      (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  classical
  have h := NlsGge.Measure.RawHeadTailIndepFunPublicRestrictionsV1.fullWeightSequenceGaussian_indepFun_coordinateRestrictions_v1
    c.val (symmetricModes N : Set ℤ)
  let g : (((symmetricModes N : Set ℤ)) → ℂ) → actualCMHead c N :=
    fun w => (actualCMHeadCoord c N).symm
      (fun i => w ⟨modeIndex N i, by simpa using modeIndex_mem_symmetricModes N i⟩)
  have hg : Measurable g := by
    refine (actualCMHeadCoord c N).symm.toContinuousLinearEquiv.continuous.measurable.comp ?_
    exact measurable_pi_iff.2 (fun i => measurable_pi_apply _)
  have := h.comp hg measurable_id
  exact this

/-- Joint law of (head point, tail) under the full law. -/
theorem map_headPt_tailPt (c : BoundedCoefficients lower upper) (N : ℕ) :
    (NlsGge.Measure.fullWeightSequenceGaussian c.val).map
        (fun z => (headPt c N z, tailPt N z)) =
      (finiteStdGaussian (actualCMHead c N)).prod
        ((NlsGge.Measure.fullWeightSequenceGaussian c.val).map (tailPt N)) := by
  rw [← headPt_map c N]
  exact ((ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    (measurable_headPt c N).aemeasurable (measurable_tailPt N).aemeasurable).1
    (indepFun_headPt_tailPt c N))


/-! ### The change-of-variables formula -/

/-- **Head-acting change of variables on the full law** (inverse-pushforward orientation).
`(Ŝ⁻¹)_# γ = J_S(x_N) γ`, with `J_S = finiteRamerDensity S`, for a differentiable
homeomorphism `S` of the head `V_N`. -/
theorem map_headActEquiv_symm (c : BoundedCoefficients lower upper) (N : ℕ)
    (S : actualCMHead c N ≃ₜ actualCMHead c N) (hS : Differentiable ℝ S) :
    (NlsGge.Measure.fullWeightSequenceGaussian c.val).map (headActEquiv c N S).symm =
      (NlsGge.Measure.fullWeightSequenceGaussian c.val).withDensity
        (fun z => ENNReal.ofReal
          (finiteRamerDensity (S : actualCMHead c N → actualCMHead c N) (headPt c N z))) := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  have : IsProbabilityMeasure γ := by rw [hγ]; infer_instance
  set μτ := γ.map (tailPt N) with hμτ
  have : IsProbabilityMeasure μτ := (Measure.isProbabilityMeasure_map_iff (measurable_tailPt N).aemeasurable).2 inferInstance
  set ρ : actualCMHead c N → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (finiteRamerDensity (S : actualCMHead c N → actualCMHead c N) x) with hρ
  have hρm : Measurable ρ := (measurable_finiteRamerDensity S).ennreal_ofReal
  have hP : Measurable (fun z : ℤ → ℂ => (headPt c N z, tailPt N z)) :=
    (measurable_headPt c N).prodMk (measurable_tailPt N)
  have hR := measurable_headRec c N
  have hSs : Measurable (fun p : actualCMHead c N × TailSpace N => (S.symm p.1, p.2)) :=
    (S.symm.continuous.measurable.comp measurable_fst).prodMk measurable_snd
  ext B hB
  have hcomp : ∀ z, (headActEquiv c N S).symm z =
      headRec c N (S.symm (headPt c N z)) (tailPt N z) := fun z =>
    headAct_eq_headRec c N S.symm z
  have hpre : (headActEquiv c N S).symm ⁻¹' B =
      (fun z => (headPt c N z, tailPt N z)) ⁻¹'
        ((fun p : actualCMHead c N × TailSpace N => (S.symm p.1, p.2)) ⁻¹'
          ((fun p : actualCMHead c N × TailSpace N => headRec c N p.1 p.2) ⁻¹' B)) := by
    ext z; simp [hcomp]
  have hW : MeasurableSet ((fun p : actualCMHead c N × TailSpace N => (S.symm p.1, p.2)) ⁻¹'
          ((fun p : actualCMHead c N × TailSpace N => headRec c N p.1 p.2) ⁻¹' B)) :=
    hSs (hR hB)
  have hRB : MeasurableSet ((fun p : actualCMHead c N × TailSpace N => headRec c N p.1 p.2) ⁻¹' B) :=
    hR hB
  rw [Measure.map_apply (headActEquiv c N S).symm.measurable hB, hpre,
    ← Measure.map_apply hP hW, map_headPt_tailPt, ← hμτ]
  have hprod : ((finiteStdGaussian (actualCMHead c N)).prod μτ).map
      (fun p : actualCMHead c N × TailSpace N => (S.symm p.1, p.2)) =
      ((finiteStdGaussian (actualCMHead c N)).withDensity ρ).prod μτ := by
    have := Measure.map_prod_map (finiteStdGaussian (actualCMHead c N)) μτ
      (f := (S.symm : actualCMHead c N → actualCMHead c N)) (g := id)
      S.symm.continuous.measurable measurable_id
    rw [Measure.map_id] at this
    rw [← finiteStdGaussian_map_symm S hS]
    exact this.symm
  rw [← Measure.map_apply hSs hRB, hprod, prod_withDensity_left hρm,
    withDensity_apply _ hRB, withDensity_apply _ hB, ← map_headPt_tailPt]
  rw [setLIntegral_map hRB (f := fun p : actualCMHead c N × TailSpace N => ρ p.1)
    (hρm.comp measurable_fst) hP]
  have : (fun z : ℤ → ℂ => (headPt c N z, tailPt N z)) ⁻¹'
      ((fun p : actualCMHead c N × TailSpace N => headRec c N p.1 p.2) ⁻¹' B) = B := by
    ext z; simp [headRec_headPt_tailPt]
  rw [this]

/-- Mass one of the head Ramer density on the full law. -/
theorem lintegral_finiteRamerDensity_headPt (c : BoundedCoefficients lower upper) (N : ℕ)
    (S : actualCMHead c N ≃ₜ actualCMHead c N) (hS : Differentiable ℝ S) :
    ∫⁻ z, ENNReal.ofReal
        (finiteRamerDensity (S : actualCMHead c N → actualCMHead c N) (headPt c N z))
      ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) = 1 := by
  rw [← lintegral_map (f := fun x => ENNReal.ofReal
      (finiteRamerDensity (S : actualCMHead c N → actualCMHead c N) x))
    (measurable_finiteRamerDensity S).ennreal_ofReal (measurable_headPt c N), headPt_map]
  exact lintegral_finiteRamerDensity S hS

end NlsGge.Ramer

import NlsGge.ThirdConsultation.Narrative.G07C
import NlsGge.Composition.Main

   
                                                                  
                                                                             
                                                                         
                                                                  
  

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.Narrative.G07

open MeasureTheory AddCircle Set
open NlsGge.Composition
open NlsGge.ThirdConsultation.Narrative.G07C

abbrev RealComplexCoeff (X : Type*) := G07C.Complexification X

section Coefficients

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The Taylor complexification norm, exactly the real rotation supremum. -/
def realComplexificationCoeffNorm (z : RealComplexCoeff X) : ℝ := ‖z‖

theorem realComplexificationCoeffNorm_eq_display (z : RealComplexCoeff X) :
    realComplexificationCoeffNorm z =
      sSup (Set.range (fun u : {v : ℝ × ℝ // v.1 ^ 2 + v.2 ^ 2 = 1} =>
        ‖u.val.1 • z.re - u.val.2 • z.im‖)) := by
  change sSup (Set.range (fun w : Circle => ‖((w : ℂ) • z).re‖)) = _
  congr 1
  ext r
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨⟨((w : ℂ).re, (w : ℂ).im), ?_⟩, rfl⟩
    simpa only [Complex.normSq_apply, ← sq, Circle.norm_coe, one_pow] using
      (Complex.sq_norm (w : ℂ)).symm
  · rintro ⟨u, rfl⟩
    let w : Circle := ⟨⟨u.val.1, u.val.2⟩, by
      change (⟨u.val.1, u.val.2⟩ : ℂ) ∈ Metric.sphere (0 : ℂ) 1
      rw [mem_sphere_zero_iff_norm, Complex.norm_def]
      have h : Complex.normSq (⟨u.val.1, u.val.2⟩ : ℂ) = 1 := by
        simpa only [Complex.normSq_mk, ← sq] using u.property
      rw [h, Real.sqrt_one]⟩
    exact ⟨w, rfl⟩

variable [CompleteSpace X]

/-- Ordinary mode n Fourier coefficient of the real function in X + i X;
Mathlib's Fourier coefficient uses the negative phase. -/
def realFourierCoeff (f : AddCircle (1 : ℝ) → X) (n : ℤ) : RealComplexCoeff X :=
  fourierCoeff (fun t => Complexification.ofReal (f t)) n

theorem realFourierCoeff_eq_integrals {f : AddCircle (1 : ℝ) → X}
    (hf : Continuous f) (n : ℤ) :
    realFourierCoeff f n =
      ⟨∫ t, (fourier (-n) t).re • f t ∂haarAddCircle,
       ∫ t, (fourier (-n) t).im • f t ∂haarAddCircle⟩ := by
  have hi : Integrable (fun t : AddCircle (1 : ℝ) =>
      fourier (-n) t • Complexification.ofReal (f t)) haarAddCircle :=
    integrable_of_continuous ((map_continuous (fourier (-n))).smul
      ((Complexification.ofRealLI X).continuous.comp hf))
  apply Complexification.ext
  · change (Complexification.reCLM X)
      (∫ t, fourier (-n) t • Complexification.ofReal (f t) ∂haarAddCircle) = _
    rw [← (Complexification.reCLM X).integral_comp_comm hi]
    simp only [Complexification.reCLM_apply, Complexification.smul_re,
      Complexification.ofReal_re, Complexification.ofReal_im, smul_zero, sub_zero]
  · change (Complexification.imCLM X)
      (∫ t, fourier (-n) t • Complexification.ofReal (f t) ∂haarAddCircle) = _
    rw [← (Complexification.imCLM X).integral_comp_comm hi]
    simp only [Complexification.imCLM_apply, Complexification.smul_im,
      Complexification.ofReal_re, Complexification.ofReal_im, smul_zero, add_zero]

/-- The literal continuous real-valued function carrier with the source
weighted squared Fourier-coefficient summability condition. -/
structure RealAw (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (a b : ℝ) where
  toFun : AddCircle (1 : ℝ) → X
  continuous_toFun : Continuous toFun
  summable_weighted_coefficients : Summable (fun n : ℤ =>
    (srcWeight a b n * realComplexificationCoeffNorm (realFourierCoeff toFun n)) ^ 2)

instance {a b : ℝ} : CoeFun (RealAw X a b) (fun _ => AddCircle (1 : ℝ) → X) :=
  ⟨RealAw.toFun⟩

@[ext] theorem RealAw.ext {a b : ℝ} {f g : RealAw X a b}
    (h : ∀ t, f t = g t) : f = g := by
  cases f
  cases g
  congr 1
  exact funext h

/-- Exactly the displayed source norm, with unchanged a and b. -/
def realAwNorm {a b : ℝ} (f : RealAw X a b) : ℝ :=
  Real.sqrt (∑' n : ℤ,
    (srcWeight a b n * realComplexificationCoeffNorm (realFourierCoeff f.toFun n)) ^ 2)

theorem realAw_memAw {a b : ℝ} (f : RealAw X a b) :
    MemAw (srcWeight a b) (fun t => Complexification.ofReal (f t)) :=
  ⟨(Complexification.ofRealLI X).continuous.comp f.continuous_toFun,
    f.summable_weighted_coefficients⟩

end Coefficients

section ClosedRealModel

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {a b : ℝ}

/-- The actual weighted model elements whose synthesized functions are real. -/
def realModel (ha : 0 < a) : Submodule ℝ (Model (RealComplexCoeff X)) where
  carrier := {g | ∀ t, (synth (srcWeight a b) g t).im = 0}
  zero_mem' := by
    intro t
    change (((evalCLM (srcWeight_admissible ha b) t) 0 : RealComplexCoeff X)).im = 0
    rw [map_zero]
    rfl
  add_mem' := by
    intro g h hg hh t
    rw [synth_add (srcWeight_admissible ha b), Complexification.add_im, hg t, hh t,
      add_zero]
  smul_mem' := by
    intro r g hg t
    rw [synth_smul, Complexification.real_smul_im, hg t, smul_zero]

theorem isClosed_realModel (ha : 0 < a) :
    IsClosed (realModel (X := X) (b := b) ha : Set (Model (RealComplexCoeff X))) := by
  change IsClosed {g : Model (RealComplexCoeff X) |
    ∀ t, (synth (srcWeight a b) g t).im = 0}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun t =>
    isClosed_eq ((Complexification.imCLM X).continuous.comp
      (evalCLM (srcWeight_admissible ha b) t).continuous) continuous_const

instance realModelCompleteSpace (ha : 0 < a) :
    CompleteSpace (realModel (X := X) (b := b) ha) :=
  (isClosed_realModel ha).completeSpace_coe

def realAwToRealModel (ha : 0 < a) (f : RealAw X a b) :
    realModel (X := X) (b := b) ha :=
  ⟨toModel (srcWeight_admissible ha b) (realAw_memAw f), by
    intro t
    rw [synth_toModel]
    rfl⟩

theorem synth_realAwToRealModel (ha : 0 < a) (f : RealAw X a b)
    (t : AddCircle (1 : ℝ)) :
    synth (srcWeight a b) (realAwToRealModel ha f).val t =
      Complexification.ofReal (f t) :=
  congrFun (synth_toModel (srcWeight_admissible ha b) (realAw_memAw f)) t

def realAwOfRealModel (ha : 0 < a) (g : realModel (X := X) (b := b) ha) :
    RealAw X a b where
  toFun t := (synth (srcWeight a b) g.val t).re
  continuous_toFun := (Complexification.reCLM X).continuous.comp
    (continuous_synth (srcWeight_admissible ha b) g.val)
  summable_weighted_coefficients := by
    have heq : (fun t => Complexification.ofReal (synth (srcWeight a b) g.val t).re) =
        synth (srcWeight a b) g.val := by
      funext t
      apply Complexification.ext
      · rfl
      · exact (g.property t).symm
    change Summable (fun n : ℤ => (srcWeight a b n *
      ‖fourierCoeff (fun t => Complexification.ofReal
        (synth (srcWeight a b) g.val t).re) n‖) ^ 2)
    rw [heq]
    exact (memAw_synth (srcWeight_admissible ha b) g.val).2

theorem ofReal_realAwOfRealModel (ha : 0 < a)
    (g : realModel (X := X) (b := b) ha) (t : AddCircle (1 : ℝ)) :
    Complexification.ofReal (realAwOfRealModel ha g t) =
      synth (srcWeight a b) g.val t := by
  apply Complexification.ext
  · rfl
  · exact (g.property t).symm

/-- The isometric identification is earned from Fourier synthesis; it does
not replace the literal function carrier by an assumed sequence interface. -/
def realAwEquiv (ha : 0 < a) : RealAw X a b ≃ realModel (X := X) (b := b) ha where
  toFun := realAwToRealModel ha
  invFun := realAwOfRealModel ha
  left_inv f := by
    apply RealAw.ext
    intro t
    change (synth (srcWeight a b) (realAwToRealModel ha f).val t).re = f t
    rw [synth_realAwToRealModel]
    rfl
  right_inv g := by
    apply Subtype.ext
    apply synth_injective (srcWeight_admissible ha b)
    funext t
    rw [synth_realAwToRealModel, ofReal_realAwOfRealModel]

end ClosedRealModel

section CanonicalBanachStructure

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {a b : ℝ} [Fact (0 < a)]

instance realAwAddCommGroup : AddCommGroup (RealAw X a b) :=
  (realAwEquiv (X := X) (b := b) (Fact.out : 0 < a)).addCommGroup

def realAwAddEquiv : RealAw X a b ≃+ realModel (X := X) (b := b) (Fact.out : 0 < a) :=
  (realAwEquiv (X := X) (b := b) (Fact.out : 0 < a)).addEquiv

instance realAwModule : Module ℝ (RealAw X a b) :=
  (realAwAddEquiv (X := X) (a := a) (b := b)).module ℝ

def realAwLinearEquiv :
    RealAw X a b ≃ₗ[ℝ] realModel (X := X) (b := b) (Fact.out : 0 < a) :=
  (realAwAddEquiv (X := X) (a := a) (b := b)).linearEquiv ℝ

instance realAwNormedAddCommGroup : NormedAddCommGroup (RealAw X a b) :=
  NormedAddCommGroup.induced _ _
    (realAwLinearEquiv (X := X) (a := a) (b := b)).toLinearMap.toAddMonoidHom
    (realAwLinearEquiv (X := X) (a := a) (b := b)).injective

instance realAwNormedSpace : NormedSpace ℝ (RealAw X a b) where
  norm_smul_le r f := by
    change ‖realAwLinearEquiv (r • f)‖ ≤ ‖r‖ * ‖realAwLinearEquiv f‖
    rw [map_smul]
    exact norm_smul_le r _

def realAwLinearIsometryEquiv :
    RealAw X a b ≃ₗᵢ[ℝ] realModel (X := X) (b := b) (Fact.out : 0 < a) where
  toLinearEquiv := realAwLinearEquiv
  norm_map' _ := rfl

instance realAwCompleteSpace : CompleteSpace (RealAw X a b) := by
  let e : RealAw X a b ≃L[ℝ] realModel (X := X) (b := b) (Fact.out : 0 < a) :=
    (realAwLinearIsometryEquiv (X := X) (a := a) (b := b)).toContinuousLinearEquiv
  exact ((e.isUniformEmbedding.isUniformInducing).completeSpace_congr e.surjective).2
    inferInstance

theorem realAw_norm_eq (f : RealAw X a b) : ‖f‖ = realAwNorm f := by
  change ‖toModel (srcWeight_admissible (Fact.out : 0 < a) b) (realAw_memAw f)‖ = _
  exact norm_toModel (srcWeight_admissible (Fact.out : 0 < a) b) (realAw_memAw f)

theorem realAw_zero_apply (t : AddCircle (1 : ℝ)) : (0 : RealAw X a b) t = 0 := by
  change (synth (srcWeight a b) (0 : Model (RealComplexCoeff X)) t).re = 0
  change (((evalCLM (srcWeight_admissible (Fact.out : 0 < a) b) t) 0 :
    RealComplexCoeff X)).re = 0
  rw [map_zero]
  rfl

theorem realAw_add_apply (f g : RealAw X a b) (t : AddCircle (1 : ℝ)) :
    (f + g) t = f t + g t := by
  change (synth (srcWeight a b)
    ((realAwToRealModel (Fact.out : 0 < a) f).val +
      (realAwToRealModel (Fact.out : 0 < a) g).val) t).re = _
  rw [synth_add (srcWeight_admissible (Fact.out : 0 < a) b),
    synth_realAwToRealModel, synth_realAwToRealModel]
  rfl

theorem realAw_smul_apply (r : ℝ) (f : RealAw X a b) (t : AddCircle (1 : ℝ)) :
    (r • f) t = r • f t := by
  change (synth (srcWeight a b)
    (r • (realAwToRealModel (Fact.out : 0 < a) f).val) t).re = _
  rw [synth_smul, synth_realAwToRealModel, Complexification.real_smul_re]
  rfl

theorem realAw_neg_apply (f : RealAw X a b) (t : AddCircle (1 : ℝ)) :
    (-f) t = -f t := by
  rw [← neg_one_smul ℝ f, realAw_smul_apply, neg_one_smul]

def realAwToModelCLM : RealAw X a b →L[ℝ] Model (RealComplexCoeff X) :=
  (realModel (X := X) (b := b) (Fact.out : 0 < a)).subtypeL.comp
    ((realAwLinearIsometryEquiv (X := X) (a := a) (b := b)).toContinuousLinearEquiv.toContinuousLinearMap)

theorem realAwToModelCLM_apply (f : RealAw X a b) :
    realAwToModelCLM f = (realAwToRealModel (Fact.out : 0 < a) f).val := rfl

theorem synth_realAwToModelCLM (f : RealAw X a b) (t : AddCircle (1 : ℝ)) :
    synth (srcWeight a b) (realAwToModelCLM f) t = Complexification.ofReal (f t) := by
  rw [realAwToModelCLM_apply]
  exact synth_realAwToRealModel (Fact.out : 0 < a) f t

/-- Absolute convergence and exact synthesis in the genuine complexification. -/
theorem realAw_fourier_synthesis (f : RealAw X a b) :
    Summable (fun n : ℤ => ‖realFourierCoeff f.toFun n‖) ∧
      ∀ t, Complexification.ofReal (f t) =
        ∑' n : ℤ, fourier n t • realFourierCoeff f.toFun n := by
  have hw := srcWeight_admissible (Fact.out : 0 < a) b
  have hc : Summable (fun n : ℤ => ‖realFourierCoeff f.toFun n‖) := by
    simpa only [coeff_toModel, realFourierCoeff] using
      (summable_norm_coeff hw (toModel hw (realAw_memAw f))).1
  refine ⟨hc, ?_⟩
  intro t
  exact (congrFun (expSum_fourierCoeff (realAw_memAw f).1 hc) t).symm

end CanonicalBanachStructure

section RealProjection

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {a b : ℝ} [Fact (0 < a)]

def realPartMap : RealComplexCoeff X →L[ℝ] RealComplexCoeff X :=
  (Complexification.ofRealLI X).toContinuousLinearMap.comp (Complexification.reCLM X)

theorem synth_comp_realPartMap (g : Model (RealComplexCoeff X))
    (t : AddCircle (1 : ℝ)) :
    synth (srcWeight a b)
      (compMap (srcWeight_admissible (Fact.out : 0 < a) b) (realPartMap (X := X)) g) t =
        Complexification.ofReal (synth (srcWeight a b) g t).re := by
  have h := (composition_analytic (srcWeight_admissible (Fact.out : 0 < a) b)
    isOpen_univ ((realPartMap (X := X)).analyticOnNhd Set.univ)).2.2 g (by intro t; trivial)
  exact congrFun h.2 t

/-- A continuous real-linear retraction onto the real synthesized subspace.
It is constructed from the already landed complex-space composition theorem
applied to the fixed real-linear projection, not assumed as a real-space input. -/
def realModelProjection : Model (RealComplexCoeff X) →L[ℝ]
    realModel (X := X) (b := b) (Fact.out : 0 < a) where
  toFun g := ⟨compMap (srcWeight_admissible (Fact.out : 0 < a) b)
    (realPartMap (X := X)) g, by
      intro t
      simpa only [Complexification.ofReal_im] using
        congrArg Complexification.im (synth_comp_realPartMap (a := a) (b := b) g t)⟩
  map_add' g h := by
    apply Subtype.ext
    simp only [Submodule.coe_add]
    change compMap (srcWeight_admissible (Fact.out : 0 < a) b)
        (realPartMap (X := X)) (g + h) =
      compMap (srcWeight_admissible (Fact.out : 0 < a) b) (realPartMap (X := X)) g +
        compMap (srcWeight_admissible (Fact.out : 0 < a) b) (realPartMap (X := X)) h
    apply synth_injective (srcWeight_admissible (Fact.out : 0 < a) b)
    funext t
    rw [synth_add (srcWeight_admissible (Fact.out : 0 < a) b),
      synth_comp_realPartMap, synth_comp_realPartMap, synth_comp_realPartMap,
      synth_add (srcWeight_admissible (Fact.out : 0 < a) b)]
    apply Complexification.ext <;> simp
  map_smul' r g := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply]
    change compMap (srcWeight_admissible (Fact.out : 0 < a) b)
        (realPartMap (X := X)) (r • g) =
      r • compMap (srcWeight_admissible (Fact.out : 0 < a) b) (realPartMap (X := X)) g
    apply synth_injective (srcWeight_admissible (Fact.out : 0 < a) b)
    funext t
    rw [synth_smul, synth_comp_realPartMap, synth_comp_realPartMap, synth_smul]
    apply Complexification.ext <;> simp [Complexification.real_smul_re]
  cont := by
    apply Continuous.subtype_mk
    have hana : AnalyticOnNhd ℝ
        (compMap (srcWeight_admissible (Fact.out : 0 < a) b) (realPartMap (X := X)))
        Set.univ := by
      intro g _
      exact (composition_analytic (srcWeight_admissible (Fact.out : 0 < a) b)
        isOpen_univ ((realPartMap (X := X)).analyticOnNhd Set.univ)).2.1 g
          (by intro t; trivial)
    exact hana.continuous

def realAwProjectCLM : Model (RealComplexCoeff X) →L[ℝ] RealAw X a b :=
  ((realAwLinearIsometryEquiv (X := X) (a := a) (b := b)).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (realModelProjection (X := X) (a := a) (b := b))

theorem realAwProjectCLM_apply (g : Model (RealComplexCoeff X))
    (t : AddCircle (1 : ℝ)) :
    realAwProjectCLM (a := a) (b := b) g t = (synth (srcWeight a b) g t).re := by
  change (synth (srcWeight a b)
    (compMap (srcWeight_admissible (Fact.out : 0 < a) b) (realPartMap (X := X)) g) t).re = _
  rw [synth_comp_realPartMap]
  rfl

end RealProjection

section Bilinear

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
variable {a b : ℝ} [Fact (0 < a)]

/-- A fixed continuous real-bilinear extension sufficient for restricting
the already proved complex-carrier product theorem to real-valued functions. -/
def realBilinearLift (B : X →L[ℝ] Y →L[ℝ] Z) :
    RealComplexCoeff X →L[ℝ] RealComplexCoeff Y →L[ℝ] RealComplexCoeff Z :=
  (ContinuousLinearMap.compL ℝ (RealComplexCoeff Y) Z (RealComplexCoeff Z)
    (Complexification.ofRealLI Z).toContinuousLinearMap).comp
      (B.bilinearComp (Complexification.reCLM X) (Complexification.reCLM Y))

def realAwBilinear (B : X →L[ℝ] Y →L[ℝ] Z) :
    RealAw X a b →L[ℝ] RealAw Y a b →L[ℝ] RealAw Z a b :=
  (ContinuousLinearMap.compL ℝ (RealAw Y a b) (Model (RealComplexCoeff Z)) (RealAw Z a b)
    (realAwProjectCLM (a := a) (b := b))).comp
      ((prodCLM (srcWeight_admissible (Fact.out : 0 < a) b) (realBilinearLift B)).bilinearComp
        (realAwToModelCLM (a := a) (b := b)) (realAwToModelCLM (a := a) (b := b)))

theorem realAwBilinear_apply (B : X →L[ℝ] Y →L[ℝ] Z)
    (f : RealAw X a b) (g : RealAw Y a b) (t : AddCircle (1 : ℝ)) :
    realAwBilinear B f g t = B (f t) (g t) := by
  change realAwProjectCLM
    (prodCLM (srcWeight_admissible (Fact.out : 0 < a) b) (realBilinearLift B)
      (realAwToModelCLM f) (realAwToModelCLM g)) t = _
  rw [realAwProjectCLM_apply, synth_prodCLM,
    synth_realAwToModelCLM, synth_realAwToModelCLM]
  rfl

end Bilinear

/-- The source bilinear assertion over arbitrary real Banach spaces and the
same source a,b, with the canonical normed structures just constructed. -/
theorem grouped_real_banach_bilinear
    (X Y Z : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (a b : ℝ) (ha : 0 < a) (B : X →L[ℝ] Y →L[ℝ] Z) :
    letI : Fact (0 < a) := ⟨ha⟩
    ∃ L : RealAw X a b →L[ℝ] RealAw Y a b →L[ℝ] RealAw Z a b,
      ∀ f g t, L f g t = B (f t) (g t) := by
  letI : Fact (0 < a) := ⟨ha⟩
  exact ⟨realAwBilinear B, realAwBilinear_apply B⟩

/-- The source composition assertion, including the range-preserving open
neighborhood and the produced local analytic map. No input composition map. -/
theorem grouped_real_banach_composition
    (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (a b : ℝ) (ha : 0 < a) (O : Set X) (hO : IsOpen O)
    (F : X → Y) (hF : AnalyticOnNhd ℝ F O) :
    letI : Fact (0 < a) := ⟨ha⟩
    ∀ f : RealAw X a b, (∀ t, f t ∈ O) →
      ∃ U : Set (RealAw X a b), IsOpen U ∧ f ∈ U ∧
        (∀ g ∈ U, ∀ t, g t ∈ O) ∧
        ∃ C : RealAw X a b → RealAw Y a b,
          AnalyticOnNhd ℝ C U ∧ (∀ g ∈ U, ∀ t, C g t = F (g t)) := by
  letI : Fact (0 < a) := ⟨ha⟩
  intro f hf
  obtain ⟨V, hV, hOV, FC, hFC, hagree⟩ :=
    G07C.exists_complexification_on_open hO F hF
  let W : Set (RealComplexCoeff X) := V ∩ (Complexification.reCLM X) ⁻¹' O
  have hW : IsOpen W := hV.inter (hO.preimage (Complexification.reCLM X).continuous)
  have hFCW : AnalyticOnNhd ℝ FC W :=
    (hFC.restrictScalars (𝕜 := ℝ)).mono Set.inter_subset_left
  let hw := srcWeight_admissible ha b
  let E : RealAw X a b →L[ℝ] Model (RealComplexCoeff X) := realAwToModelCLM
  let P : Model (RealComplexCoeff Y) →L[ℝ] RealAw Y a b := realAwProjectCLM
  obtain ⟨hopen, hana, hcomp⟩ := composition_analytic hw hW hFCW
  let U : Set (RealAw X a b) := E ⁻¹' rangeSet (srcWeight a b) W
  have hU : IsOpen U := hopen.preimage E.continuous
  have hUf : f ∈ U := by
    intro t
    change synth (srcWeight a b) (realAwToModelCLM f) t ∈ W
    rw [synth_realAwToModelCLM]
    exact ⟨hOV _ (hf t), hf t⟩
  have hUO : ∀ g ∈ U, ∀ t, g t ∈ O := by
    intro g hg t
    have ht := (hg t).2
    change (synth (srcWeight a b) (realAwToModelCLM g) t).re ∈ O at ht
    rw [synth_realAwToModelCLM] at ht
    exact ht
  refine ⟨U, hU, hUf, hUO, (fun g => P (compMap hw FC (E g))), ?_, ?_⟩
  · intro g hg
    exact (P.analyticAt _).comp ((hana (E g) hg).comp (E.analyticAt g))
  · intro g hg t
    change realAwProjectCLM (compMap hw FC (realAwToModelCLM g)) t = F (g t)
    rw [realAwProjectCLM_apply, congrFun (hcomp (E g) hg).2 t]
    change (FC (synth (srcWeight a b) (realAwToModelCLM g) t)).re = F (g t)
    rw [synth_realAwToModelCLM, hagree _ (hUO g hg t)]
    rfl

end NlsGge.ThirdConsultation.Narrative.G07

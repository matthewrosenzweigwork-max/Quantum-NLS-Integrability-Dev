import NlsGge.Atomic.LIB.LIB033
import NlsGge.Atomic.LIB.LIB002
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Genuine p=2 weak H1 graphs on the interval and unnormalized doubled circle. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology Classical

namespace NlsGge.Atomic.LIB034
open NlsGge.Schur NlsGge.Atomic.Interval NlsGge.Atomic.LIB026

local instance : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩

abbrev IntervalJet := WithLp 2 (SourceIntervalL2 × SourceIntervalL2)

/-- The exact interval weak graph, with genuine p=2 ambient norm. -/
def intervalH1Graph : Submodule ℂ IntervalJet where
  carrier := {j | HasWeakDerivative j.fst j.snd}
  zero_mem' := by
    change HasWeakDerivative (↑↑(0 : SourceIntervalL2)) (↑↑(0 : SourceIntervalL2))
    simpa only [zero_smul] using NlsGge.Atomic.LIB033.weakDerivative_smul
      (0 : ℂ) NlsGge.Atomic.LIB033.h1Zero.weak
  add_mem' := by
    intro f g hf hg
    change HasWeakDerivative (↑↑(f.fst + g.fst)) (↑↑(f.snd + g.snd))
    exact NlsGge.Atomic.LIB033.weakDerivative_add hf hg
  smul_mem' := by
    intro c f hf
    change HasWeakDerivative (↑↑(c • f.fst)) (↑↑(c • f.snd))
    exact NlsGge.Atomic.LIB033.weakDerivative_smul c hf

abbrev IntervalH1 := intervalH1Graph

def intervalH1OfLiteral (f : H1) : IntervalH1 :=
  ⟨WithLp.toLp 2 (f.value, f.derivative), f.weak⟩

def intervalH1ToLiteral (f : IntervalH1) : H1 :=
  ⟨f.val.fst, f.val.snd, f.property⟩

/-- No endpoint or regularity premise is added by the normed carrier. -/
def intervalH1Equiv : H1 ≃ IntervalH1 where
  toFun := intervalH1OfLiteral
  invFun := intervalH1ToLiteral
  left_inv f := by cases f; rfl
  right_inv f := by apply Subtype.ext; rfl

lemma intervalH1_norm_sq (f : IntervalH1) :
    ‖f‖ ^ 2 = ‖f.val.fst‖ ^ 2 + ‖f.val.snd‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

lemma intervalH1OfLiteral_norm_sq (f : H1) :
    ‖intervalH1OfLiteral f‖ ^ 2 = ‖f.value‖ ^ 2 + ‖f.derivative‖ ^ 2 :=
  intervalH1_norm_sq _

@[simp] lemma intervalH1OfLiteral_add (f g : H1) :
    intervalH1OfLiteral (NlsGge.Atomic.LIB033.h1Add f g) =
      intervalH1OfLiteral f + intervalH1OfLiteral g := rfl

@[simp] lemma intervalH1OfLiteral_smul (c : ℂ) (f : H1) :
    intervalH1OfLiteral (NlsGge.Atomic.LIB033.h1Smul c f) =
      c • intervalH1OfLiteral f := rfl

abbrev PeriodTwoL2 := Lp ℂ 2 (volume : Measure SpectralCircle)
abbrev PeriodTwoJet := WithLp 2 (PeriodTwoL2 × PeriodTwoL2)

/-- A genuine smooth periodic test in ordinary-volume circle L2. -/
def periodicTestL2 (ψ : NlsGge.Atomic.LIB002.SmoothPeriodicTest (2 : ℝ)) : PeriodTwoL2 :=
  ContinuousMap.toLp 2 volume ℂ ψ.toContinuousMap

/-- All smooth complex periodic tests, with the conjugate-first L2 pairing. -/
def HasPeriodicWeakDerivative (u v : PeriodTwoL2) : Prop :=
  ∀ ψ : NlsGge.Atomic.LIB002.SmoothPeriodicTest (2 : ℝ),
    inner ℂ (periodicTestL2 (NlsGge.Atomic.LIB002.SmoothPeriodicTest.iterated ψ 1)) u =
      -inner ℂ (periodicTestL2 ψ) v

/-- The actual distributional weak graph on AddCircle2, with unnormalized volume. -/
def periodicH1Graph : Submodule ℂ PeriodTwoJet where
  carrier := {j | HasPeriodicWeakDerivative j.fst j.snd}
  zero_mem' := by intro ψ; simp
  add_mem' := by
    intro f g hf hg ψ
    change inner ℂ _ (f.fst + g.fst) = -inner ℂ _ (f.snd + g.snd)
    rw [inner_add_right, inner_add_right, hf ψ, hg ψ]
    ring
  smul_mem' := by
    intro c f hf ψ
    change inner ℂ _ (c • f.fst) = -inner ℂ _ (c • f.snd)
    rw [inner_smul_right, inner_smul_right, hf ψ]
    ring

abbrev PeriodicH1Two := periodicH1Graph

lemma periodicH1Two_norm_sq (f : PeriodicH1Two) :
    ‖f‖ ^ 2 = ‖f.val.fst‖ ^ 2 + ‖f.val.snd‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 _


/-- Reflection sends the second Ioc half to Ico(0,1). -/
lemma secondHalfReflect_preserving : MeasurePreserving
    (fun x : ℝ => 2 - x) (volume.restrict (Ioc (1 : ℝ) 2))
      (volume.restrict (Ico (0 : ℝ) 1)) := by
  have hp := (volume.measurePreserving_sub_left (2 : ℝ)).restrict_preimage
    (measurableSet_Ico (a := (0 : ℝ)) (b := 1))
  have hs : (fun x : ℝ => 2 - x) ⁻¹' Ico (0 : ℝ) 1 = Ioc (1 : ℝ) 2 := by
    ext x
    simp only [mem_preimage, mem_Ico, mem_Ioc]
    constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]
  simpa only [hs] using hp

/-- Endpoint-null transfer precedes reflection of an L2 class. -/
lemma interval_memLp_Ico (u : SourceIntervalL2) :
    MemLp u 2 (volume.restrict (Ico (0 : ℝ) 1)) := by
  rw [Measure.restrict_congr_set Ico_ae_eq_Ioc]
  exact Lp.memLp u

/-- Explicit positive or negative reflection on the doubled real interval. -/
def reflectedHalf (negative : Bool) (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  if x ≤ 1 then u x else (if negative then -1 else 1) * u (2 - x)

lemma reflectedHalf_memLp (negative : Bool) (u : SourceIntervalL2) :
    MemLp (reflectedHalf negative u) 2 (volume.restrict (Ioc (0 : ℝ) 2)) := by
  have hfirst : Iic (1 : ℝ) ∩ Ioc (0 : ℝ) 2 = Ioc (0 : ℝ) 1 := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨h1, h0, h2⟩; exact ⟨h0, h1⟩
    · rintro ⟨h0, h1⟩; exact ⟨h1, h0, h1.trans (by norm_num)⟩
  have hsecond : (Iic (1 : ℝ))ᶜ ∩ Ioc (0 : ℝ) 2 = Ioc (1 : ℝ) 2 := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨h1, h0, h2⟩; exact ⟨lt_of_not_ge h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨not_le.mpr h1, (by norm_num : (0 : ℝ) < 1).trans h1, h2⟩
  have hf : MemLp u 2 ((volume.restrict (Ioc (0 : ℝ) 2)).restrict (Iic (1 : ℝ))) := by
    rw [Measure.restrict_restrict measurableSet_Iic, hfirst]
    exact Lp.memLp u
  have hg : MemLp (fun x : ℝ => (if negative then (-1 : ℂ) else 1) * u (2 - x)) 2
      ((volume.restrict (Ioc (0 : ℝ) 2)).restrict (Iic (1 : ℝ))ᶜ) := by
    rw [Measure.restrict_restrict measurableSet_Iic.compl, hsecond]
    exact ((interval_memLp_Ico u).comp_measurePreserving secondHalfReflect_preserving).const_mul _
  exact MemLp.piecewise measurableSet_Iic hf hg

def reflectedCircle (negative : Bool) (u : ℝ → ℂ) : SpectralCircle → ℂ :=
  AddCircle.liftIoc (2 : ℝ) 0 (reflectedHalf negative u)

lemma reflectedCircle_memLp (negative : Bool) (u : SourceIntervalL2) :
    MemLp (reflectedCircle negative u) 2 (volume : Measure SpectralCircle) := by
  apply MemLp.memLp_liftIoc
  simpa only [zero_add] using reflectedHalf_memLp negative u

/-- Genuine L2 classes, constructed only after actual MemLp proofs. -/
def reflectedL2 (negative : Bool) (u : SourceIntervalL2) : PeriodTwoL2 :=
  (reflectedCircle_memLp negative u).toLp (reflectedCircle negative u)

lemma reflectedL2_ae (negative : Bool) (u : SourceIntervalL2) :
    reflectedL2 negative u =ᵐ[(volume : Measure SpectralCircle)] reflectedCircle negative u :=
  (reflectedCircle_memLp negative u).coeFn_toLp

lemma periodTwoL2_norm_sq (f : PeriodTwoL2) :
    ‖f‖ ^ 2 = ∫ x : SpectralCircle, ‖f x‖ ^ 2 := by
  calc
    ‖f‖ ^ 2 = RCLike.re (inner ℂ f f) := norm_sq_eq_re_inner (𝕜 := ℂ) f
    _ = ∫ x : SpectralCircle, RCLike.re (inner ℂ (f x) (f x)) := by
      rw [L2.inner_def, ← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)]
    _ = ∫ x : SpectralCircle, ‖f x‖ ^ 2 := by
      simp only [← norm_sq_eq_re_inner (𝕜 := ℂ)]

lemma reflectedHalf_sq_integral (negative : Bool) (u : SourceIntervalL2) :
    (∫ x in (0 : ℝ)..2, ‖reflectedHalf negative u x‖ ^ 2) = 2 * ‖u‖ ^ 2 := by
  have hmem := reflectedHalf_memLp negative u
  have hi : IntervalIntegrable (fun x => ‖reflectedHalf negative u x‖ ^ 2) volume 0 2 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 2)).mpr
      ((memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem)
  have h1 : (∫ x in (0 : ℝ)..1, ‖reflectedHalf negative u x‖ ^ 2) =
      ∫ x in (0 : ℝ)..1, ‖u x‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    simp [reflectedHalf, hx.2]
  have h2 : (∫ x in (1 : ℝ)..2, ‖reflectedHalf negative u x‖ ^ 2) =
      ∫ x in (1 : ℝ)..2, ‖u (2 - x)‖ ^ 2 := by
    apply intervalIntegral.integral_congr_ae_restrict
    simp only [uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    cases negative <;> simp [reflectedHalf, not_le.mpr hx.1]
  have hi1 : IntervalIntegrable (fun x => ‖reflectedHalf negative u x‖ ^ 2) volume 0 1 := by
    apply hi.mono_set
    rw [uIcc_of_le zero_le_one, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hi2 : IntervalIntegrable (fun x => ‖reflectedHalf negative u x‖ ^ 2) volume 1 2 := by
    apply hi.mono_set
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2), uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, h1, h2,
    intervalIntegral.integral_comp_sub_left (fun t => ‖u t‖ ^ 2) (a := 1) (b := 2) 2]
  norm_num only
  rw [intervalIntegral.integral_of_le zero_le_one, ← sourceInterval_norm_sq]
  ring

lemma reflectedL2_norm_sq (negative : Bool) (u : SourceIntervalL2) :
    ‖reflectedL2 negative u‖ ^ 2 = 2 * ‖u‖ ^ 2 := by
  rw [periodTwoL2_norm_sq]
  calc
    _ = ∫ x : SpectralCircle, ‖reflectedCircle negative u x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [reflectedL2_ae negative u] with x hx
      rw [hx]
    _ = ∫ x in (0 : ℝ)..2, ‖reflectedHalf negative u x‖ ^ 2 := by
      change (∫ x : SpectralCircle, AddCircle.liftIoc (2 : ℝ) 0
        (fun t => ‖reflectedHalf negative u t‖ ^ 2) x) = _
      simpa only [zero_add] using AddCircle.integral_liftIoc_eq_intervalIntegral
        (T := (2 : ℝ)) (t := 0) (f := fun t => ‖reflectedHalf negative u t‖ ^ 2)
    _ = _ := reflectedHalf_sq_integral negative u


lemma reflectedHalf_congr {u v : ℝ → ℂ}
    (h : u =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] v) (negative : Bool) :
    reflectedHalf negative u =ᵐ[volume.restrict (Ioc (0 : ℝ) 2)] reflectedHalf negative v := by
  have hc : u =ᵐ[volume.restrict (Ico (0 : ℝ) 1)] v := by
    rw [Measure.restrict_congr_set Ico_ae_eq_Ioc]
    exact h
  have hr := secondHalfReflect_preserving.quasiMeasurePreserving.ae_eq_comp hc
  apply (ae_restrict_iff' measurableSet_Ioc).mpr
  have hfirst := (ae_restrict_iff' measurableSet_Ioc).mp h
  have hsecond := (ae_restrict_iff' measurableSet_Ioc).mp hr
  filter_upwards [hfirst, hsecond] with x hf hs hx
  by_cases hx1 : x ≤ 1
  · simp only [reflectedHalf, ite_eq_left hx1]
    exact hf ⟨hx.1, hx1⟩
  · simp only [reflectedHalf, ite_eq_right hx1]
    exact congrArg (fun z : ℂ => (if negative then -1 else 1) * z)
      (hs ⟨lt_of_not_ge hx1, hx.2⟩)

lemma liftIoc_congr {u v : ℝ → ℂ}
    (h : u =ᵐ[volume.restrict (Ioc (0 : ℝ) 2)] v) :
    AddCircle.liftIoc (2 : ℝ) 0 u =ᵐ[(volume : Measure SpectralCircle)]
      AddCircle.liftIoc (2 : ℝ) 0 v := by
  have h' : u =ᵐ[volume.restrict (Ioc (0 : ℝ) (0 + 2))] v := by simpa only [zero_add] using h
  have hp := (measurePreserving_subtype_coe
    (μa := (volume : Measure ℝ)) (measurableSet_Ioc (a := (0 : ℝ)) (b := 0 + 2))).comp
      (AddCircle.measurePreserving_equivIoc (T := (2 : ℝ)) (a := 0))
  exact hp.quasiMeasurePreserving.ae_eq_comp h'

lemma reflectedCircle_congr {u v : ℝ → ℂ}
    (h : u =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] v) (negative : Bool) :
    reflectedCircle negative u =ᵐ[(volume : Measure SpectralCircle)] reflectedCircle negative v :=
  liftIoc_congr (reflectedHalf_congr h negative)

lemma reflectedCircle_add (negative : Bool) (u v : ℝ → ℂ) (x : SpectralCircle) :
    reflectedCircle negative (u + v) x = reflectedCircle negative u x + reflectedCircle negative v x := by
  dsimp [reflectedCircle, AddCircle.liftIoc, domRestrict, reflectedHalf]
  split_ifs <;> ring

lemma reflectedCircle_smul (negative : Bool) (c : ℂ) (u : ℝ → ℂ) (x : SpectralCircle) :
    reflectedCircle negative (c • u) x = c • reflectedCircle negative u x := by
  dsimp [reflectedCircle, AddCircle.liftIoc, domRestrict, reflectedHalf]
  split_ifs <;> ring

lemma reflectedL2_add (negative : Bool) (u v : SourceIntervalL2) :
    reflectedL2 negative (u + v) = reflectedL2 negative u + reflectedL2 negative v := by
  apply Lp.ext
  filter_upwards [reflectedL2_ae negative (u + v), reflectedL2_ae negative u,
    reflectedL2_ae negative v, Lp.coeFn_add (reflectedL2 negative u) (reflectedL2 negative v),
    reflectedCircle_congr (Lp.coeFn_add u v) negative] with x hsum hu hv ha heq
  rw [hsum, ha]
  simp only [Pi.add_apply]
  rw [hu, hv, heq, reflectedCircle_add]

lemma reflectedL2_smul (negative : Bool) (c : ℂ) (u : SourceIntervalL2) :
    reflectedL2 negative (c • u) = c • reflectedL2 negative u := by
  apply Lp.ext
  filter_upwards [reflectedL2_ae negative (c • u), reflectedL2_ae negative u,
    Lp.coeFn_smul c (reflectedL2 negative u),
    reflectedCircle_congr (Lp.coeFn_smul c u) negative] with x hsum hu ha heq
  rw [hsum, ha]
  simp only [Pi.smul_apply]
  rw [hu, heq, reflectedCircle_smul]

lemma reflectedL2_norm (negative : Bool) (u : SourceIntervalL2) :
    ‖reflectedL2 negative u‖ = Real.sqrt 2 * ‖u‖ := by
  calc
    _ = Real.sqrt (‖reflectedL2 negative u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (2 * ‖u‖ ^ 2) := congrArg Real.sqrt (reflectedL2_norm_sq negative u)
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq (norm_nonneg _)]

/-- Actual bounded positive/negative L2 reflection, before any H1 claim. -/
def reflectL2 (negative : Bool) : SourceIntervalL2 →L[ℂ] PeriodTwoL2 :=
  LinearMap.mkContinuous
    { toFun := reflectedL2 negative
      map_add' := reflectedL2_add negative
      map_smul' := by intro c u; exact reflectedL2_smul negative c u }
    (Real.sqrt 2) (fun u => (reflectedL2_norm negative u).le)

lemma circle_ae_pullback_first_half {u v : SpectralCircle → ℂ}
    (h : u =ᵐ[(volume : Measure SpectralCircle)] v) :
    (fun x : ℝ => u (x : SpectralCircle)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun x : ℝ => v (x : SpectralCircle)) := by
  have hr : (fun x : ℝ => u (x : SpectralCircle)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 2)]
      (fun x : ℝ => v (x : SpectralCircle)) := by
    simpa only [Function.comp_def, zero_add] using
      (AddCircle.measurePreserving_mk (2 : ℝ) 0).quasiMeasurePreserving.ae_eq_comp h
  exact ae_restrict_of_ae_restrict_of_subset
    (by intro x hx; exact ⟨hx.1, hx.2.trans (by norm_num)⟩) hr

lemma restrict_memLp (u : PeriodTwoL2) :
    MemLp (fun x : ℝ => u (x : SpectralCircle)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hfull : MemLp (fun x : ℝ => u (x : SpectralCircle)) 2
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    simpa only [Function.comp_def, zero_add] using
      (Lp.memLp u).comp_measurePreserving (AddCircle.measurePreserving_mk (2 : ℝ) 0)
  exact hfull.mono_measure (Measure.restrict_mono_set volume
    (by intro x hx; exact ⟨hx.1, hx.2.trans (by norm_num)⟩))

def restrictL2Value (u : PeriodTwoL2) : SourceIntervalL2 :=
  (restrict_memLp u).toLp (fun x : ℝ => u (x : SpectralCircle))

lemma restrictL2Value_ae (u : PeriodTwoL2) :
    restrictL2Value u =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun x : ℝ => u (x : SpectralCircle)) := (restrict_memLp u).coeFn_toLp

lemma restrictL2Value_add (u v : PeriodTwoL2) :
    restrictL2Value (u + v) = restrictL2Value u + restrictL2Value v := by
  apply Lp.ext
  filter_upwards [restrictL2Value_ae (u + v), restrictL2Value_ae u, restrictL2Value_ae v,
    Lp.coeFn_add (restrictL2Value u) (restrictL2Value v),
    circle_ae_pullback_first_half (Lp.coeFn_add u v)] with x hsum hu hv ha hin
  rw [hsum, ha]
  simp only [Pi.add_apply]
  rw [hin, hu, hv]
  rfl

lemma restrictL2Value_smul (c : ℂ) (u : PeriodTwoL2) :
    restrictL2Value (c • u) = c • restrictL2Value u := by
  apply Lp.ext
  filter_upwards [restrictL2Value_ae (c • u), restrictL2Value_ae u,
    Lp.coeFn_smul c (restrictL2Value u),
    circle_ae_pullback_first_half (Lp.coeFn_smul c u)] with x hsum hu ha hin
  rw [hsum, ha]
  simp only [Pi.smul_apply]
  rw [hin, hu]
  rfl

lemma restrictL2Value_norm_le (u : PeriodTwoL2) : ‖restrictL2Value u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [sourceInterval_norm_sq, periodTwoL2_norm_sq]
  calc
    _ = ∫ x in Ioc (0 : ℝ) 1, ‖u (x : SpectralCircle)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [restrictL2Value_ae u] with x hx
      rw [hx]
    _ ≤ ∫ x in Ioc (0 : ℝ) 2, ‖u (x : SpectralCircle)‖ ^ 2 := by
      apply integral_mono_measure
        (Measure.restrict_mono_set volume (by intro x hx; exact ⟨hx.1, hx.2.trans (by norm_num)⟩))
      · exact .of_forall (fun x => sq_nonneg _)
      · have hfull := (Lp.memLp u).comp_measurePreserving (AddCircle.measurePreserving_mk (2 : ℝ) 0)
        simpa only [Function.comp_def, zero_add] using
          (memLp_two_iff_integrable_sq_norm hfull.aestronglyMeasurable).mp hfull
    _ = _ := by simpa only [zero_add] using AddCircle.integral_preimage (2 : ℝ) 0 (fun x => ‖u x‖ ^ 2)

/-- Actual bounded restriction of circle L2 classes to the first source half. -/
def restrictL2 : PeriodTwoL2 →L[ℂ] SourceIntervalL2 :=
  LinearMap.mkContinuous
    { toFun := restrictL2Value
      map_add' := restrictL2Value_add
      map_smul' := by intro c u; exact restrictL2Value_smul c u }
    1 (fun u => by
      change ‖restrictL2Value u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using restrictL2Value_norm_le u)

lemma restrict_reflectL2 (negative : Bool) (u : SourceIntervalL2) :
    restrictL2 (reflectL2 negative u) = u := by
  apply Lp.ext
  filter_upwards [restrictL2Value_ae (reflectedL2 negative u),
    circle_ae_pullback_first_half (reflectedL2_ae negative u),
    ae_restrict_mem measurableSet_Ioc] with x hr hf hx
  change restrictL2Value (reflectedL2 negative u) x = u x
  rw [hr, hf]
  rw [reflectedCircle, AddCircle.liftIoc_coe_apply
    (show x ∈ Ioc (0 : ℝ) (0 + 2) from ⟨hx.1, hx.2.trans (by norm_num)⟩)]
  simp [reflectedHalf, hx.2]


lemma reflectedHalf_intervalIntegrable (negative : Bool) (u : SourceIntervalL2) :
    IntervalIntegrable (reflectedHalf negative u) volume 0 2 :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 2)).mpr
    ((reflectedHalf_memLp negative u).integrable (by norm_num))

/-- Actual H1 integration by parts against arbitrary smooth complex tests. -/
lemma smooth_h1_pairing (f : H1) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) :
    (∫ x in (0 : ℝ)..1, star (deriv ψ x) * f.value x + star (ψ x) * f.derivative x) =
      star (ψ 1) * traceRight f - star (ψ 0) * traceLeft f := by
  have hAC : AbsolutelyContinuousOnInterval ψ 0 1 :=
    (hψ.of_le (by simp) : ContDiff ℝ 1 ψ).contDiffOn.absolutelyContinuousOnInterval
  have hd : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ uIcc (0 : ℝ) 1 → HasDerivAt ψ (deriv ψ x) x :=
    .of_forall (fun x _ => ((hψ.differentiable (by simp)).differentiableAt).hasDerivAt)
  have hp := ac_conjugate_integrationByParts hAC (representative_spec f).1
    ((hψ.continuous_deriv (by simp)).intervalIntegrable 0 1)
    (intervalIntegrable_L2 f.derivative) hd (representative_spec f).2
  calc
    _ = ∫ x in (0 : ℝ)..1,
        star (deriv ψ x) * IccExtend zero_le_one (representative f) x +
          star (ψ x) * f.derivative x := by
      apply intervalIntegral.integral_congr_ae_restrict
      simp only [uIoc_of_le zero_le_one]
      filter_upwards [representative_ae f] with x hx
      rw [hx]
    _ = _ := by simpa only [IccExtend_right, IccExtend_left, traceRight, traceLeft] using hp

lemma deriv_comp_reflection (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (x : ℝ) :
    deriv (fun t : ℝ => ψ (2 - t)) x = -deriv ψ (2 - x) := by
  have hout : HasDerivAt ψ (deriv ψ (2 - x)) (2 - x) :=
    ((hψ.differentiable (by simp)).differentiableAt).hasDerivAt
  exact (hout.comp_const_sub 2 x).deriv

/-- The two explicit seams cancel in the literal unnormalized weak identity. -/
lemma reflected_pairing_integral (f : H1) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (hper : Function.Periodic ψ 2) :
    (∫ x in (0 : ℝ)..2,
      star (deriv ψ x) * reflectedHalf false f.value x +
        star (ψ x) * reflectedHalf true f.derivative x) = 0 := by
  let J : ℝ → ℂ := fun x => star (deriv ψ x) * reflectedHalf false f.value x +
    star (ψ x) * reflectedHalf true f.derivative x
  let K : ℝ → ℂ := fun t => star (deriv ψ (2 - t)) * f.value t - star (ψ (2 - t)) * f.derivative t
  have hi : IntervalIntegrable J volume 0 2 :=
    ((reflectedHalf_intervalIntegrable false f.value).continuousOn_mul
      (hψ.continuous_deriv (by simp)).star.continuousOn).add
      ((reflectedHalf_intervalIntegrable true f.derivative).continuousOn_mul hψ.continuous.star.continuousOn)
  have hi1 : IntervalIntegrable J volume 0 1 := by
    apply hi.mono_set
    rw [uIcc_of_le zero_le_one, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hi2 : IntervalIntegrable J volume 1 2 := by
    apply hi.mono_set
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2), uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hfirst : (∫ x in (0 : ℝ)..1, J x) =
      star (ψ 1) * traceRight f - star (ψ 0) * traceLeft f := by
    calc
      _ = ∫ x in (0 : ℝ)..1, star (deriv ψ x) * f.value x + star (ψ x) * f.derivative x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le zero_le_one] at hx
        simp [J, reflectedHalf, hx.2]
      _ = _ := smooth_h1_pairing f ψ hψ
  have hsecond : (∫ x in (1 : ℝ)..2, J x) = ∫ t in (0 : ℝ)..1, K t := by
    calc
      _ = ∫ x in (1 : ℝ)..2, K (2 - x) := by
        apply intervalIntegral.integral_congr_ae_restrict
        simp only [uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        dsimp [J, K]
        simp [reflectedHalf, not_le.mpr hx.1, sub_eq_add_neg]
      _ = _ := by
        simpa only [sub_self, show (2 : ℝ) - 1 = 1 by norm_num] using
          intervalIntegral.integral_comp_sub_left K (a := 1) (b := 2) 2
  have hψr : ContDiff ℝ ∞ (fun x : ℝ => ψ (2 - x)) :=
    hψ.comp (contDiff_const.sub contDiff_id)
  have hparts := smooth_h1_pairing f (fun x : ℝ => ψ (2 - x)) hψr
  have hK : (∫ t in (0 : ℝ)..1, K t) =
      -(star (ψ 1) * traceRight f - star (ψ 2) * traceLeft f) := by
    calc
      _ = -(∫ t in (0 : ℝ)..1,
          star (deriv (fun x : ℝ => ψ (2 - x)) t) * f.value t +
            star (ψ (2 - t)) * f.derivative t) := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only [K]
        rw [deriv_comp_reflection ψ hψ]
        simp only [star_neg]
        ring
      _ = _ := by rw [hparts]; norm_num
  change (∫ x in (0 : ℝ)..2, J x) = 0
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, hfirst, hsecond, hK]
  have hend : ψ 2 = ψ 0 := by simpa only [zero_add] using hper 0
  rw [hend]
  ring


lemma circle_ae_pullback_full {u v : SpectralCircle → ℂ}
    (h : u =ᵐ[(volume : Measure SpectralCircle)] v) :
    (fun x : ℝ => u (x : SpectralCircle)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 2)]
      (fun x : ℝ => v (x : SpectralCircle)) := by
  simpa only [Function.comp_def, zero_add] using
    (AddCircle.measurePreserving_mk (2 : ℝ) 0).quasiMeasurePreserving.ae_eq_comp h

lemma reflectedL2_pullback_ae (negative : Bool) (u : SourceIntervalL2) :
    (fun x : ℝ => reflectedL2 negative u (x : SpectralCircle)) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) 2)] reflectedHalf negative u := by
  filter_upwards [circle_ae_pullback_full (reflectedL2_ae negative u),
    ae_restrict_mem measurableSet_Ioc] with x hx hm
  rw [hx, reflectedCircle, AddCircle.liftIoc_coe_apply (by simpa only [zero_add] using hm)]

lemma periodicTestL2_pullback_ae (ψ : NlsGge.Atomic.LIB002.SmoothPeriodicTest (2 : ℝ)) :
    (fun x : ℝ => periodicTestL2 ψ (x : SpectralCircle)) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) 2)] ψ.toFun := by
  have ha := ContinuousMap.coeFn_toLp (μ := (volume : Measure SpectralCircle))
    (p := 2) (𝕜 := ℂ) ψ.toContinuousMap
  filter_upwards [circle_ae_pullback_full ha, ae_restrict_mem measurableSet_Ioc] with x hx hm
  change (ContinuousMap.toLp 2 volume ℂ ψ.toContinuousMap) (x : SpectralCircle) = ψ.toFun x
  rw [hx, NlsGge.Atomic.LIB002.SmoothPeriodicTest.toContinuousMap_apply,
    AddCircle.liftIoc_coe_apply (by simpa only [zero_add] using hm)]

lemma periodTwo_inner_eq_interval (u v : PeriodTwoL2) :
    inner ℂ u v = ∫ x in (0 : ℝ)..2,
      star (u (x : SpectralCircle)) * v (x : SpectralCircle) := by
  rw [L2.inner_def]
  rw [← AddCircle.intervalIntegral_preimage (2 : ℝ) 0]
  simp only [zero_add]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [RCLike.inner_apply, starRingEnd_apply]
  ring

lemma periodicTest_pairing_reflected (negative : Bool) (u : SourceIntervalL2)
    (ψ : NlsGge.Atomic.LIB002.SmoothPeriodicTest (2 : ℝ)) :
    inner ℂ (periodicTestL2 ψ) (reflectedL2 negative u) =
      ∫ x in (0 : ℝ)..2, star (ψ.toFun x) * reflectedHalf negative u x := by
  rw [periodTwo_inner_eq_interval]
  apply intervalIntegral.integral_congr_ae_restrict
  simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
  filter_upwards [periodicTestL2_pullback_ae ψ, reflectedL2_pullback_ae negative u] with x ht hu
  rw [ht, hu]

/-- All periodic tests satisfy the weak identity, proved by the actual seam calculation. -/
lemma reflected_hasPeriodicWeakDerivative (f : H1) :
    HasPeriodicWeakDerivative (reflectedL2 false f.value) (reflectedL2 true f.derivative) := by
  intro ψ
  rw [periodicTest_pairing_reflected, periodicTest_pairing_reflected]
  change (∫ x in (0 : ℝ)..2, star (iteratedDeriv 1 ψ.toFun x) * reflectedHalf false f.value x) = _
  simp only [iteratedDeriv_one]
  apply eq_neg_iff_add_eq_zero.mpr
  rw [← intervalIntegral.integral_add
    ((reflectedHalf_intervalIntegrable false f.value).continuousOn_mul
      (ψ.smooth.continuous_deriv (by simp)).star.continuousOn)
    ((reflectedHalf_intervalIntegrable true f.derivative).continuousOn_mul ψ.smooth.continuous.star.continuousOn)]
  exact reflected_pairing_integral f ψ.toFun ψ.smooth ψ.periodic

/-- Actual reflection of the normed weak graph, with no assumed periodicity or energy. -/
def intervalH1ReflectLinear : IntervalH1 →ₗ[ℂ] PeriodicH1Two where
  toFun f := ⟨WithLp.toLp 2 (reflectL2 false f.val.fst, reflectL2 true f.val.snd),
    reflected_hasPeriodicWeakDerivative (intervalH1ToLiteral f)⟩
  map_add' f g := by
    apply Subtype.ext
    change WithLp.toLp 2 (reflectL2 false (f.val.fst + g.val.fst),
      reflectL2 true (f.val.snd + g.val.snd)) =
      WithLp.toLp 2 (reflectL2 false f.val.fst, reflectL2 true f.val.snd) +
        WithLp.toLp 2 (reflectL2 false g.val.fst, reflectL2 true g.val.snd)
    rw [map_add, map_add]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    change WithLp.toLp 2 (reflectL2 false (c • f.val.fst), reflectL2 true (c • f.val.snd)) =
      c • WithLp.toLp 2 (reflectL2 false f.val.fst, reflectL2 true f.val.snd)
    rw [map_smul, map_smul]
    rfl

lemma intervalH1ReflectLinear_energy (f : IntervalH1) :
    ‖intervalH1ReflectLinear f‖ ^ 2 = 2 * ‖f‖ ^ 2 := by
  rw [periodicH1Two_norm_sq, intervalH1_norm_sq]
  change ‖reflectedL2 false f.val.fst‖ ^ 2 + ‖reflectedL2 true f.val.snd‖ ^ 2 = _
  rw [reflectedL2_norm_sq, reflectedL2_norm_sq]
  ring

lemma intervalH1ReflectLinear_norm (f : IntervalH1) :
    ‖intervalH1ReflectLinear f‖ = Real.sqrt 2 * ‖f‖ := by
  calc
    _ = Real.sqrt (‖intervalH1ReflectLinear f‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (2 * ‖f‖ ^ 2) := congrArg Real.sqrt (intervalH1ReflectLinear_energy f)
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq (norm_nonneg _)]

/-- Bounded complex-linear even reflection into the actual periodic weak H1 graph. -/
def intervalH1Reflect : IntervalH1 →L[ℂ] PeriodicH1Two :=
  intervalH1ReflectLinear.mkContinuous (Real.sqrt 2)
    (fun f => (intervalH1ReflectLinear_norm f).le)

/-- Exact doubled unnormalized H1 energy, for both actual L2 coordinates. -/
theorem intervalH1Reflect_energy (f : IntervalH1) :
    ‖intervalH1Reflect f‖ ^ 2 = 2 * ‖f‖ ^ 2 := intervalH1ReflectLinear_energy f

theorem intervalH1Reflect_norm (f : IntervalH1) :
    ‖intervalH1Reflect f‖ = Real.sqrt 2 * ‖f‖ := intervalH1ReflectLinear_norm f

/-- The actual value coordinate restricts to the original value class. -/
theorem intervalH1Reflect_restrict_value (f : IntervalH1) :
    restrictL2 (intervalH1Reflect f).val.fst = f.val.fst :=
  restrict_reflectL2 false f.val.fst

/-- The actual derivative coordinate restricts to the original derivative class. -/
theorem intervalH1Reflect_restrict_derivative (f : IntervalH1) :
    restrictL2 (intervalH1Reflect f).val.snd = f.val.snd :=
  restrict_reflectL2 true f.val.snd


/-- The quotient-circle norm is the fold distance on the doubled interval. -/
lemma reflectedCircle_even_eq_norm (u : ℝ → ℂ) (z : SpectralCircle) :
    reflectedCircle false u z = u ‖z‖ := by
  let r : ℝ := (AddCircle.equivIoc (2 : ℝ) 0 z).val
  have hr : 0 < r ∧ r ≤ 2 := by
    simpa only [r, zero_add, mem_Ioc] using (AddCircle.equivIoc (2 : ℝ) 0 z).property
  have hz : (r : SpectralCircle) = z := AddCircle.coe_equivIoc
  change reflectedHalf false u r = u ‖z‖
  by_cases hsmall : r ≤ 1
  · have hn : ‖(r : SpectralCircle)‖ = r := by
      rw [(AddCircle.norm_coe_eq_abs_iff (2 : ℝ) (by norm_num)).mpr]
      · exact abs_of_nonneg hr.1.le
      · simpa [abs_of_nonneg hr.1.le] using hsmall
    rw [hz] at hn
    simp [reflectedHalf, hsmall, hn]
  · have h0 : 0 ≤ 2 - r := sub_nonneg.mpr hr.2
    have h1 : 2 - r ≤ 1 := by linarith
    have hn : ‖((2 - r : ℝ) : SpectralCircle)‖ = 2 - r := by
      rw [(AddCircle.norm_coe_eq_abs_iff (2 : ℝ) (by norm_num)).mpr]
      · exact abs_of_nonneg h0
      · simpa [abs_of_nonneg h0] using h1
    have hc : ((2 - r : ℝ) : SpectralCircle) = -z := by
      rw [AddCircle.coe_sub, AddCircle.coe_period, hz, zero_sub]
    rw [hc, norm_neg] at hn
    simp [reflectedHalf, hsmall, hn]

/-- The actual continuous even reflected representative; its seams are literal equalities. -/
def evenRepresentative (f : H1) : C(SpectralCircle, ℂ) where
  toFun z := IccExtend zero_le_one (representative f) ‖z‖
  continuous_toFun := (representative f).continuous.Icc_extend'.comp continuous_norm

lemma evenRepresentative_even (f : H1) (z : SpectralCircle) :
    evenRepresentative f (-z) = evenRepresentative f z := by
  change IccExtend zero_le_one (representative f) ‖-z‖ = _
  rw [norm_neg]
  rfl

lemma evenRepresentative_periodic (f : H1) :
    Function.Periodic (fun x : ℝ => evenRepresentative f (x : SpectralCircle)) 2 := by
  intro x
  change evenRepresentative f ((x + 2 : ℝ) : SpectralCircle) = evenRepresentative f (x : SpectralCircle)
  rw [AddCircle.coe_add_period]

lemma reflectedL2_evenRepresentative_ae (f : H1) :
    reflectedL2 false f.value =ᵐ[(volume : Measure SpectralCircle)] evenRepresentative f := by
  have hr := reflectedCircle_congr (representative_ae f).symm false
  filter_upwards [reflectedL2_ae false f.value, hr] with z hz hrz
  rw [hz, hrz, reflectedCircle_even_eq_norm]
  rfl

/-- Actual value and derivative energies each double, independently. -/
theorem intervalH1Reflect_value_energy (f : IntervalH1) :
    ‖(intervalH1Reflect f).val.fst‖ ^ 2 = 2 * ‖f.val.fst‖ ^ 2 :=
  reflectedL2_norm_sq false f.val.fst

theorem intervalH1Reflect_derivative_energy (f : IntervalH1) :
    ‖(intervalH1Reflect f).val.snd‖ ^ 2 = 2 * ‖f.val.snd‖ ^ 2 :=
  reflectedL2_norm_sq true f.val.snd

/-- Full doubled-interval value formula using the canonical continuous H1 representative. -/
theorem intervalH1Reflect_value_ae (f : IntervalH1) :
    (fun x : ℝ => (intervalH1Reflect f).val.fst (x : SpectralCircle)) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) 2)]
      reflectedHalf false (IccExtend zero_le_one (representative (intervalH1ToLiteral f))) :=
  (reflectedL2_pullback_ae false f.val.fst).trans
    (reflectedHalf_congr (representative_ae (intervalH1ToLiteral f)).symm false)

/-- The weak derivative has the required negative sign on the reflected half. -/
theorem intervalH1Reflect_derivative_ae (f : IntervalH1) :
    (fun x : ℝ => (intervalH1Reflect f).val.snd (x : SpectralCircle)) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) 2)]
      (fun x => if x ≤ 1 then f.val.snd x else -f.val.snd (2 - x)) := by
  filter_upwards [reflectedL2_pullback_ae true f.val.snd] with x hx
  change reflectedL2 true f.val.snd (x : SpectralCircle) = _
  rw [hx]
  simp [reflectedHalf]

/-- The circle output has a genuine continuous, even, 2-periodic pullback representative. -/
theorem intervalH1Reflect_continuous_even (f : IntervalH1) :
    ∃ F : C(SpectralCircle, ℂ),
      (fun z => (intervalH1Reflect f).val.fst z) =ᵐ[(volume : Measure SpectralCircle)] F ∧
      (∀ z, F (-z) = F z) ∧ Function.Periodic (fun x : ℝ => F (x : SpectralCircle)) 2 :=
  ⟨evenRepresentative (intervalH1ToLiteral f),
    reflectedL2_evenRepresentative_ae (intervalH1ToLiteral f),
    evenRepresentative_even (intervalH1ToLiteral f),
    evenRepresentative_periodic (intervalH1ToLiteral f)⟩

/-- Literal restriction of both graph coordinates is the original normed H1 jet. -/
theorem intervalH1Reflect_restrict_jet (f : IntervalH1) :
    WithLp.toLp 2 (restrictL2 (intervalH1Reflect f).val.fst,
      restrictL2 (intervalH1Reflect f).val.snd) = (f : IntervalJet) := by
  rw [intervalH1Reflect_restrict_value, intervalH1Reflect_restrict_derivative]
  rfl

/-- The literally restricted coordinates satisfy the weak graph and return the same H1 element. -/
theorem intervalH1Reflect_restrict_graph (f : IntervalH1) :
    ∃ hw : HasWeakDerivative (restrictL2 (intervalH1Reflect f).val.fst)
        (restrictL2 (intervalH1Reflect f).val.snd),
      (⟨WithLp.toLp 2 (restrictL2 (intervalH1Reflect f).val.fst,
        restrictL2 (intervalH1Reflect f).val.snd), hw⟩ : IntervalH1) = f := by
  have hw : HasWeakDerivative (restrictL2 (intervalH1Reflect f).val.fst)
      (restrictL2 (intervalH1Reflect f).val.snd) := by
    rw [intervalH1Reflect_restrict_value, intervalH1Reflect_restrict_derivative]
    exact f.property
  exact ⟨hw, Subtype.ext (intervalH1Reflect_restrict_jet f)⟩


/-- Periodicity holds for the actual quotient-class pullback as well. -/
theorem intervalH1Reflect_pullback_periodic (f : IntervalH1) :
    Function.Periodic (fun x : ℝ => (intervalH1Reflect f).val.fst (x : SpectralCircle)) 2 := by
  intro x
  change (intervalH1Reflect f).val.fst ((x + 2 : ℝ) : SpectralCircle) =
    (intervalH1Reflect f).val.fst (x : SpectralCircle)
  rw [AddCircle.coe_add_period]

/-- Evenness is an AE equality of actual circle L2 classes, not only a chosen representative. -/
theorem intervalH1Reflect_value_even_ae (f : IntervalH1) :
    (fun z : SpectralCircle => (intervalH1Reflect f).val.fst (-z)) =ᵐ[
      (volume : Measure SpectralCircle)] (fun z => (intervalH1Reflect f).val.fst z) := by
  have hr := reflectedL2_evenRepresentative_ae (intervalH1ToLiteral f)
  have hs := (Measure.measurePreserving_neg (volume : Measure SpectralCircle)).quasiMeasurePreserving.ae_eq_comp hr
  filter_upwards [hr, hs] with z hz hn
  change reflectedL2 false f.val.fst (-z) = reflectedL2 false f.val.fst z
  change reflectedL2 false f.val.fst (-z) = evenRepresentative (intervalH1ToLiteral f) (-z) at hn
  change reflectedL2 false f.val.fst z = evenRepresentative (intervalH1ToLiteral f) z at hz
  rw [hn, evenRepresentative_even]
  exact hz.symm

/-- The actual real-line pullback is even a.e. on a complete period. -/
theorem intervalH1Reflect_pullback_even_ae (f : IntervalH1) :
    (fun x : ℝ => (intervalH1Reflect f).val.fst ((-x : ℝ) : SpectralCircle)) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) 2)]
      (fun x => (intervalH1Reflect f).val.fst (x : SpectralCircle)) := by
  simpa only [AddCircle.coe_neg] using circle_ae_pullback_full (intervalH1Reflect_value_even_ae f)

lemma evenRepresentative_left (f : H1) : evenRepresentative f (0 : SpectralCircle) = traceLeft f := by
  change IccExtend zero_le_one (representative f) ‖(0 : SpectralCircle)‖ = traceLeft f
  rw [norm_zero, IccExtend_left]
  rfl

lemma evenRepresentative_right (f : H1) :
    evenRepresentative f ((1 : ℝ) : SpectralCircle) = traceRight f := by
  have hn : ‖((1 : ℝ) : SpectralCircle)‖ = 1 := by
    simpa using AddCircle.norm_half_period_eq (2 : ℝ)
  change IccExtend zero_le_one (representative f) ‖((1 : ℝ) : SpectralCircle)‖ = traceRight f
  rw [hn, IccExtend_right]
  rfl

end NlsGge.Atomic.LIB034

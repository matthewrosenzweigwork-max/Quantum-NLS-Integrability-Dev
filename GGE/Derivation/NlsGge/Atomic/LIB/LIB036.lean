import NlsGge.Atomic.LIB.LIB033
import NlsGge.Atomic.LIB.LIB031


/-!
# LIB-036: complete normalized free Zakharov--Shabat eigenbases

The separated bases are transferred from the genuine period-two Haar Fourier
basis through a constructed scalar-to-pair unitary. Its reflected extension is
proved inverse in both directions, with the exact square-norm measure identity.
The periodic and antiperiodic bases use the already constructed actual parity
restriction equivalence, with the frequency sign changed for the native action.

Every basis vector is identified with an actual distributional interval H1 pair.
The canonical representatives give the exponential formulas and endpoint
conditions; the genuine L2 action gives the realization eigenvector equality.
All four bases are orthonormal and complete, and their canonical Euclidean
representatives have sup norm at most one.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff
namespace NlsGge.Atomic.LIB036
open NlsGge.Schur NlsGge.Atomic.Interval NlsGge.Atomic.LIB026

abbrev unitMeasure : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)

def separatedSign (neu : Bool) : ℂ := if neu then -1 else 1
@[simp] lemma separatedSign_norm (neu : Bool) : ‖separatedSign neu‖ = 1 := by cases neu <;> simp [separatedSign]
@[simp] lemma separatedSign_sq (neu : Bool) : separatedSign neu * separatedSign neu = 1 := by cases neu <;> simp [separatedSign]

def halfFactor : ℝ := (Real.sqrt 2)⁻¹
lemma halfFactor_nonneg : 0 ≤ halfFactor := by unfold halfFactor; positivity
lemma halfFactor_sq : halfFactor ^ 2 = (1 / 2 : ℝ) := by
  rw [halfFactor, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
lemma halfFactor_mul_sqrt : halfFactor * Real.sqrt 2 = 1 :=
  inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))

lemma fullCircle_restrict_memLp (f : SpectralScalarL2) :
    MemLp (fun x : ℝ => f (x : SpectralCircle)) 2 unitMeasure := by
  have hf : MemLp f 2 (volume : Measure SpectralCircle) := (Lp.memLp f).of_haarAddCircle
  have hd : MemLp (fun x : ℝ => f (x : SpectralCircle)) 2
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    simpa only [Function.comp_def, zero_add] using
      hf.comp_measurePreserving (AddCircle.measurePreserving_mk (2 : ℝ) 0)
  exact hd.mono_measure (Measure.restrict_mono_set volume (by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩))

def halfRestrict (f : SpectralScalarL2) : SourceIntervalL2 :=
  (fullCircle_restrict_memLp f).toLp (fun x : ℝ => f (x : SpectralCircle))
lemma halfRestrict_ae (f : SpectralScalarL2) :
    (fun x => halfRestrict f x) =ᵐ[unitMeasure] fun x : ℝ => f (x : SpectralCircle) :=
  (fullCircle_restrict_memLp f).coeFn_toLp

lemma halfRestrict_add (f g : SpectralScalarL2) : halfRestrict (f + g) = halfRestrict f + halfRestrict g := by
  apply Lp.ext
  filter_upwards [halfRestrict_ae (f + g), halfRestrict_ae f, halfRestrict_ae g,
    spectral_ae_pullback_first_half (Lp.coeFn_add f g),
    Lp.coeFn_add (halfRestrict f) (halfRestrict g)] with x h0 hf hg hc hh
  calc
    halfRestrict (f + g) x = (f + g) (x : SpectralCircle) := h0
    _ = f (x : SpectralCircle) + g (x : SpectralCircle) := hc
    _ = halfRestrict f x + halfRestrict g x := by rw [hf, hg]
    _ = (halfRestrict f + halfRestrict g) x := hh.symm

lemma halfRestrict_smul (c : ℂ) (f : SpectralScalarL2) : halfRestrict (c • f) = c • halfRestrict f := by
  apply Lp.ext
  filter_upwards [halfRestrict_ae (c • f), halfRestrict_ae f,
    spectral_ae_pullback_first_half (Lp.coeFn_smul c f), Lp.coeFn_smul c (halfRestrict f)]
    with x h0 hf hc hh
  calc
    halfRestrict (c • f) x = (c • f) (x : SpectralCircle) := h0
    _ = c * f (x : SpectralCircle) := hc
    _ = c * halfRestrict f x := by rw [hf]
    _ = (c • halfRestrict f) x := hh.symm

def halfRestrictLinear : SpectralScalarL2 →ₗ[ℂ] SourceIntervalL2 where
  toFun := halfRestrict
  map_add' := halfRestrict_add
  map_smul' := halfRestrict_smul

lemma spectralNeg_preserving : MeasurePreserving (fun x : SpectralCircle => -x) spectralHaar spectralHaar := by
  change MeasurePreserving (fun x : SpectralCircle => -x) AddCircle.haarAddCircle AddCircle.haarAddCircle
  exact Measure.measurePreserving_neg AddCircle.haarAddCircle

def spectralNeg : SpectralScalarL2 →ₗᵢ[ℂ] SpectralScalarL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : SpectralCircle => -x) spectralNeg_preserving
lemma spectralNeg_ae (f : SpectralScalarL2) :
    (fun x => spectralNeg f x) =ᵐ[spectralHaar] fun x => f (-x) :=
  Lp.coeFn_compMeasurePreserving f spectralNeg_preserving

/-- The actual normalized scalar-to-pair pullback, before proving its norm identity. -/
def unfoldLinear (neu : Bool) : SpectralScalarL2 →ₗ[ℂ] SourcePairL2 where
  toFun f := WithLp.toLp 2 (fun b => if b then
    (halfFactor : ℂ) • halfRestrictLinear (spectralNeg f) else
    ((halfFactor : ℂ) * separatedSign neu) • halfRestrictLinear f)
  map_add' := by
    intro f g
    apply PiLp.ext
    intro b
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, map_add, smul_add] <;> rfl
  map_smul' := by
    intro c f
    apply PiLp.ext
    intro b
    cases b
    · change ((halfFactor : ℂ) * separatedSign neu) • halfRestrictLinear (c • f) =
        c • (((halfFactor : ℂ) * separatedSign neu) • halfRestrictLinear f)
      simp only [map_smul, smul_smul]
      congr 1
      ring
    · change (halfFactor : ℂ) • halfRestrictLinear (spectralNeg (c • f)) =
        c • ((halfFactor : ℂ) • halfRestrictLinear (spectralNeg f))
      simp only [map_smul, smul_smul]
      congr 1
      ring

lemma secondReflect_preserving : MeasurePreserving (fun x : ℝ => 2 - x)
    (volume.restrict (Ioc (1 : ℝ) 2)) unitMeasure := by
  have hp := (volume.measurePreserving_sub_left (2 : ℝ)).restrict_preimage
    (measurableSet_Ioc (a := (0 : ℝ)) (b := 1))
  have hs : (fun x : ℝ => 2 - x) ⁻¹' Ioc (0 : ℝ) 1 = Ico (1 : ℝ) 2 := by
    ext x
    simp only [mem_preimage, mem_Ioc, mem_Ico]
    constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]
  rw [hs, Measure.restrict_congr_set (Ico_ae_eq_Ioc (a := (1 : ℝ)) (b := 2))] at hp
  exact hp

def foldRealValue (neu : Bool) (f : SourcePairL2) (x : ℝ) : ℂ :=
  if x ≤ 1 then (Real.sqrt 2 : ℂ) * separatedSign neu * f false x
  else (Real.sqrt 2 : ℂ) * f true (2 - x)

lemma foldRealValue_memLp (neu : Bool) (f : SourcePairL2) :
    MemLp (foldRealValue neu f) 2 (volume.restrict (Ioc (0 : ℝ) 2)) := by
  classical
  have hfirst : Iic (1 : ℝ) ∩ Ioc (0 : ℝ) 2 = Ioc (0 : ℝ) 1 := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨h1,h0,h2⟩; exact ⟨h0,h1⟩
    · rintro ⟨h0,h1⟩; exact ⟨h1,h0,h1.trans (by norm_num)⟩
  have hsecond : (Iic (1 : ℝ))ᶜ ∩ Ioc (0 : ℝ) 2 = Ioc (1 : ℝ) 2 := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨h1,h0,h2⟩; exact ⟨lt_of_not_ge h1,h2⟩
    · rintro ⟨h1,h2⟩; exact ⟨not_le.mpr h1, (by norm_num : (0 : ℝ) < 1).trans h1,h2⟩
  have hf : MemLp (fun x => (Real.sqrt 2 : ℂ) * separatedSign neu * f false x) 2
      ((volume.restrict (Ioc (0 : ℝ) 2)).restrict (Iic (1 : ℝ))) := by
    rw [Measure.restrict_restrict measurableSet_Iic, hfirst]
    exact (Lp.memLp (f false)).const_mul _
  have hg : MemLp (fun x => (Real.sqrt 2 : ℂ) * f true (2 - x)) 2
      ((volume.restrict (Ioc (0 : ℝ) 2)).restrict (Iic (1 : ℝ))ᶜ) := by
    rw [Measure.restrict_restrict measurableSet_Iic.compl, hsecond]
    exact ((Lp.memLp (f true)).comp_measurePreserving secondReflect_preserving).const_mul _
  exact MemLp.piecewise measurableSet_Iic hf hg

def foldCircleValue (neu : Bool) (f : SourcePairL2) : SpectralCircle → ℂ :=
  AddCircle.liftIoc (2 : ℝ) 0 (foldRealValue neu f)
lemma foldCircle_memLp (neu : Bool) (f : SourcePairL2) :
    MemLp (foldCircleValue neu f) 2 spectralHaar := by
  have hf : MemLp (foldRealValue neu f) 2 (volume.restrict (Ioc (0 : ℝ) (0 + 2))) := by
    simpa only [zero_add] using foldRealValue_memLp neu f
  exact hf.memLp_liftIoc.haarAddCircle

def fold (neu : Bool) (f : SourcePairL2) : SpectralScalarL2 :=
  (foldCircle_memLp neu f).toLp (foldCircleValue neu f)
lemma fold_ae (neu : Bool) (f : SourcePairL2) :
    (fun x => fold neu f x) =ᵐ[spectralHaar] foldCircleValue neu f :=
  (foldCircle_memLp neu f).coeFn_toLp

lemma circle_neg_eq (x : ℝ) : -(x : SpectralCircle) = ((2 - x : ℝ) : SpectralCircle) := by
  calc
    -(x : SpectralCircle) = ((-x : ℝ) : SpectralCircle) := by simp
    _ = ((-x + 2 : ℝ) : SpectralCircle) := (AddCircle.coe_add_period (2 : ℝ) (-x)).symm
    _ = ((2 - x : ℝ) : SpectralCircle) := by congr 1; ring

lemma unfoldLinear_component_ae (neu : Bool) (f : SpectralScalarL2) (b : Bool) :
    (fun x => unfoldLinear neu f b x) =ᵐ[unitMeasure]
      fun x : ℝ => if b then (halfFactor : ℂ) * f (-(x : SpectralCircle))
        else (halfFactor : ℂ) * separatedSign neu * f (x : SpectralCircle) := by
  cases b
  · change (fun x => (((halfFactor : ℂ) * separatedSign neu) • halfRestrict f) x) =ᵐ[_] _
    filter_upwards [Lp.coeFn_smul ((halfFactor : ℂ) * separatedSign neu) (halfRestrict f),
      halfRestrict_ae f] with x hs hr
    simpa only [Bool.false_eq_true, ↓reduceIte, hs, Pi.smul_apply, hr, smul_eq_mul]
  · change (fun x => ((halfFactor : ℂ) • halfRestrict (spectralNeg f)) x) =ᵐ[_] _
    filter_upwards [Lp.coeFn_smul (halfFactor : ℂ) (halfRestrict (spectralNeg f)),
      halfRestrict_ae (spectralNeg f), spectral_ae_pullback_first_half (spectralNeg_ae f)]
      with x hs hr hn
    simpa only [↓reduceIte, hs, Pi.smul_apply, hr, hn, smul_eq_mul]

lemma halfRestrict_norm_sq (f : SpectralScalarL2) :
    ‖halfRestrict f‖ ^ 2 = ∫ x in Ioc (0 : ℝ) 1, ‖f (x : SpectralCircle)‖ ^ 2 := by
  rw [sourceInterval_norm_sq]
  exact integral_congr_ae ((halfRestrict_ae f).fun_comp (fun z : ℂ => ‖z‖ ^ 2))

lemma negative_half_norm_sq (f : SpectralScalarL2) :
    ‖halfRestrict (spectralNeg f)‖ ^ 2 =
      ∫ x in Ioc (1 : ℝ) 2, ‖f (x : SpectralCircle)‖ ^ 2 := by
  rw [halfRestrict_norm_sq]
  calc
    (∫ x in Ioc (0 : ℝ) 1, ‖spectralNeg f (x : SpectralCircle)‖ ^ 2) =
        ∫ x in Ioc (0 : ℝ) 1, ‖f ((2 - x : ℝ) : SpectralCircle)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [spectral_ae_pullback_first_half (spectralNeg_ae f)] with x hx
      rw [hx, circle_neg_eq]
    _ = ∫ x in Ioc (1 : ℝ) 2, ‖f (x : SpectralCircle)‖ ^ 2 := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]
      simpa only [sub_self, sub_zero, show (2 : ℝ) - 1 = 1 by norm_num] using
        intervalIntegral.integral_comp_sub_left
          (fun x : ℝ => ‖f (x : SpectralCircle)‖ ^ 2) (a := 0) (b := 1) 2

lemma unfoldLinear_norm_sq (neu : Bool) (f : SpectralScalarL2) :
    ‖unfoldLinear neu f‖ ^ 2 = ‖f‖ ^ 2 := by
  have hpair : ‖unfoldLinear neu f‖ ^ 2 = halfFactor ^ 2 *
      (‖halfRestrict (spectralNeg f)‖ ^ 2 + ‖halfRestrict f‖ ^ 2) := by
    rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_bool]
    change ‖(halfFactor : ℂ) • halfRestrict (spectralNeg f)‖ ^ 2 +
      ‖((halfFactor : ℂ) * separatedSign neu) • halfRestrict f‖ ^ 2 = _
    simp only [norm_smul, norm_mul, separatedSign_norm, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg halfFactor_nonneg]
    ring
  rw [hpair, halfFactor_sq, negative_half_norm_sq, halfRestrict_norm_sq,
    spectral_norm_sq_doubled_interval]
  let g : ℝ → ℝ := fun x => ‖f (x : SpectralCircle)‖ ^ 2
  have hf := spectral_integrableOn_norm_sq_doubled_interval f
  have h01 : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      (hf.mono_set (fun x hx => ⟨hx.1, hx.2.trans (by norm_num)⟩))
  have h12 : IntervalIntegrable g volume 1 2 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      (hf.mono_set (fun x hx => ⟨(by norm_num : (0 : ℝ) < 1).trans hx.1, hx.2⟩))
  have hadd := intervalIntegral.integral_add_adjacent_intervals h01 h12
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hadd
  change (1 / 2 : ℝ) * ((∫ x in Ioc (1 : ℝ) 2, g x) + ∫ x in Ioc (0 : ℝ) 1, g x) =
    (1 / 2 : ℝ) * ∫ x in Ioc (0 : ℝ) 2, g x
  rw [add_comm, hadd]

def unfoldIsometry (neu : Bool) : SpectralScalarL2 →ₗᵢ[ℂ] SourcePairL2 where
  toLinearMap := unfoldLinear neu
  norm_map' f := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (unfoldLinear_norm_sq neu f)

lemma foldCircle_first (neu : Bool) (f : SourcePairL2) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    foldCircleValue neu f (x : SpectralCircle) =
      (Real.sqrt 2 : ℂ) * separatedSign neu * f false x := by
  rw [foldCircleValue, AddCircle.liftIoc_coe_apply (by
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩)]
  simp only [foldRealValue, ite_eq_left hx.2]

lemma foldCircle_negative (neu : Bool) (f : SourcePairL2) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    foldCircleValue neu f (-(x : SpectralCircle)) = (Real.sqrt 2 : ℂ) * f true x := by
  rw [circle_neg_eq, foldCircleValue, AddCircle.liftIoc_coe_apply (by
    simp only [mem_Ioc, zero_add]; constructor <;> linarith [hx.1, hx.2])]
  simp only [foldRealValue, ite_eq_right (show ¬ 2 - x ≤ 1 by linarith [hx.2])]
  congr 2
  ring

lemma unfold_fold (neu : Bool) (f : SourcePairL2) : unfoldLinear neu (fold neu f) = f := by
  apply PiLp.ext
  intro b
  apply Lp.ext
  have hfirst := spectral_ae_pullback_first_half (fold_ae neu f)
  have hneg := spectral_ae_pullback_first_half
    (spectralNeg_preserving.quasiMeasurePreserving.ae_eq_comp (fold_ae neu f))
  have hio : ∀ᵐ x : ℝ ∂unitMeasure, x ∈ Ioo (0 : ℝ) 1 := by
    rw [unitMeasure, ← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1))]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [unfoldLinear_component_ae neu (fold neu f) b, hfirst, hneg, hio]
    with x hu hf hn hx
  rw [hu]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hf, foldCircle_first neu f ⟨hx.1, hx.2.le⟩]
    have hr : (halfFactor : ℂ) * (Real.sqrt 2 : ℂ) = 1 := by
      exact_mod_cast halfFactor_mul_sqrt
    calc
      (halfFactor : ℂ) * separatedSign neu *
          ((Real.sqrt 2 : ℂ) * separatedSign neu * f false x) =
        ((halfFactor : ℂ) * (Real.sqrt 2 : ℂ)) *
          (separatedSign neu * separatedSign neu) * f false x := by ring
      _ = f false x := by rw [hr, separatedSign_sq]; ring
  · simp only [↓reduceIte]
    dsimp only [Function.comp_def] at hn
    rw [hn, foldCircle_negative neu f hx]
    have hr : (halfFactor : ℂ) * (Real.sqrt 2 : ℂ) = 1 := by
      exact_mod_cast halfFactor_mul_sqrt
    rw [← mul_assoc, hr, one_mul]

def unfoldEquiv (neu : Bool) : SpectralScalarL2 ≃ₗᵢ[ℂ] SourcePairL2 :=
  LinearIsometryEquiv.ofSurjective (unfoldIsometry neu) (fun f => ⟨fold neu f, unfold_fold neu f⟩)

lemma fold_unfold (neu : Bool) (f : SpectralScalarL2) : fold neu (unfoldLinear neu f) = f := by
  apply (unfoldIsometry neu).injective
  exact unfold_fold neu (unfoldLinear neu f)

def transportBasis {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (b : HilbertBasis ι ℂ E) (e : E ≃ₗᵢ[ℂ] F) : HilbertBasis ι ℂ F :=
  HilbertBasis.ofRepr (e.symm.trans b.repr)
lemma transportBasis_apply {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (b : HilbertBasis ι ℂ E) (e : E ≃ₗᵢ[ℂ] F) (i : ι) :
    transportBasis b e i = e (b i) := by
  classical
  change e (b.repr.symm (lp.single 2 i (1 : ℂ))) = e (b i)
  rw [b.repr_symm_single]

def reindexBasis {ι κ E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (b : HilbertBasis ι ℂ E) (e : κ ≃ ι) : HilbertBasis κ ℂ E :=
  HilbertBasis.mk (b.orthonormal.comp e e.injective) (by
    have hr : Set.range (b ∘ e) = Set.range b := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨e i, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨e.symm i, by simp⟩
    rw [hr, b.dense_span])
lemma reindexBasis_apply {ι κ E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (b : HilbertBasis ι ℂ E) (e : κ ≃ ι) (i : κ) :
    reindexBasis b e i = b (e i) := by
  simp only [reindexBasis, HilbertBasis.coe_mk, Function.comp_apply]

def separatedBasis (neu : Bool) : HilbertBasis ℤ ℂ SourcePairL2 :=
  transportBasis (fourierBasis (T := (2 : ℝ))) (unfoldEquiv neu)

def parityBasis (n : ℤ) : HilbertBasis (Bool × Sector n) ℂ SourcePairL2 :=
  reindexBasis (transportBasis (parityPairFourierBasis n) (parityPairIntervalEquiv n))
    (Equiv.prodCongr (Equiv.refl Bool) (negateEquiv n))

set_option backward.isDefEq.respectTransparency false in
lemma separatedBasis_eq (neu : Bool) (m : ℤ) :
    separatedBasis neu m = unfoldLinear neu (spectralBasis m) := by
  change transportBasis (fourierBasis (T := (2 : ℝ))) (unfoldEquiv neu) m = _
  rw [transportBasis_apply]
  simp only [coe_fourierBasis]
  rfl
lemma parityBasis_eq (n : ℤ) (i : Bool × Sector n) :
    parityBasis n i = sourcePairVector n (i.1, negateIndex n i.2) := by
  rw [parityBasis, reindexBasis_apply, transportBasis_apply]
  simp only [parityPairFourierBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]
  rfl

def characterValue (m : ℤ) (x : ℝ) : ℂ := fourier m (x : SpectralCircle)
lemma characterValue_contDiff (m : ℤ) : ContDiff ℝ ∞ (characterValue m) := by
  unfold characterValue
  simp only [fourier_coe_apply]
  exact Complex.contDiff_exp.comp
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).div_const _)
lemma characterValue_hasDerivAt (m : ℤ) (x : ℝ) :
    HasDerivAt (characterValue m)
      (Complex.I * ((m : ℂ) * Real.pi) * characterValue m x) x := by
  unfold characterValue
  convert hasDerivAt_fourier (2 : ℝ) m x using 1
  norm_num
  ring

lemma characterValue_deriv (m : ℤ) :
    deriv (characterValue m) = fun x => Complex.I * ((m : ℂ) * Real.pi) * characterValue m x := by
  funext x
  exact (characterValue_hasDerivAt m x).deriv
lemma characterValue_norm (m : ℤ) (x : ℝ) : ‖characterValue m x‖ = 1 :=
  spectralFourier_norm m (x : SpectralCircle)
lemma characterValue_memLp (m : ℤ) : MemLp (characterValue m) 2 unitMeasure := by
  apply MemLp.of_bound (characterValue_contDiff m).continuous.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun x => le_of_eq (characterValue_norm m x))
lemma characterDeriv_memLp (m : ℤ) : MemLp (deriv (characterValue m)) 2 unitMeasure := by
  rw [characterValue_deriv]
  exact (characterValue_memLp m).const_mul _

def smoothIntervalH1 (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hv : MemLp u 2 unitMeasure) (hd : MemLp (deriv u) 2 unitMeasure) : H1 where
  value := hv.toLp u
  derivative := hd.toLp (deriv u)
  weak := by
    intro ψ hψs hψc hψU
    have h := NlsGge.Atomic.LIB028.smooth_hasWeakDerivative u hu ψ hψs hψc hψU
    have hev : (∫ x in (0 : ℝ)..1, hv.toLp u x * ((deriv ψ x : ℝ) : ℂ)) =
        ∫ x in (0 : ℝ)..1, u x * ((deriv ψ x : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr_ae_restrict
      simp only [uIoc_of_le zero_le_one]
      filter_upwards [hv.coeFn_toLp] with x hx
      rw [hx]
    have hed : (∫ x in (0 : ℝ)..1, hd.toLp (deriv u) x * (ψ x : ℂ)) =
        ∫ x in (0 : ℝ)..1, deriv u x * (ψ x : ℂ) := by
      apply intervalIntegral.integral_congr_ae_restrict
      simp only [uIoc_of_le zero_le_one]
      filter_upwards [hd.coeFn_toLp] with x hx
      rw [hx]
    rw [hev, hed]
    exact h

lemma smoothIntervalH1_representative (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hv : MemLp u 2 unitMeasure) (hd : MemLp (deriv u) 2 unitMeasure)
    (x : Icc (0 : ℝ) 1) : representative (smoothIntervalH1 u hu hv hd) x = u x := by
  let F : C(Icc (0 : ℝ) 1, ℂ) := ⟨fun x => u x, hu.continuous.comp continuous_subtype_val⟩
  have he : F = representative (smoothIntervalH1 u hu hv hd) := by
    apply representative_eq_of_ae
    filter_upwards [hv.coeFn_toLp, ae_restrict_mem measurableSet_Ioc] with y hy hmem
    rw [IccExtend_of_mem zero_le_one F ⟨hmem.1.le, hmem.2⟩]
    exact hy.symm
  exact congrArg (fun f : C(Icc (0 : ℝ) 1, ℂ) => f x) he.symm

def characterH1 (m : ℤ) : H1 :=
  smoothIntervalH1 (characterValue m) (characterValue_contDiff m)
    (characterValue_memLp m) (characterDeriv_memLp m)
lemma characterH1_value_ae (m : ℤ) :
    (characterH1 m).value =ᵐ[unitMeasure] characterValue m := (characterValue_memLp m).coeFn_toLp
lemma characterH1_derivative_ae (m : ℤ) :
    (characterH1 m).derivative =ᵐ[unitMeasure]
      fun x => Complex.I * ((m : ℂ) * Real.pi) * characterValue m x := by
  change ((characterDeriv_memLp m).toLp (deriv (characterValue m))) =ᵐ[_] _
  convert (characterDeriv_memLp m).coeFn_toLp using 1
  exact (characterValue_deriv m).symm
lemma characterH1_representative (m : ℤ) (x : Icc (0 : ℝ) 1) :
    representative (characterH1 m) x = characterValue m x :=
  smoothIntervalH1_representative _ _ _ _ x
@[simp] lemma characterH1_traceLeft (m : ℤ) : traceLeft (characterH1 m) = 1 := by
  rw [traceLeft, characterH1_representative]
  simp [characterValue]
@[simp] lemma characterH1_traceRight (m : ℤ) : traceRight (characterH1 m) = spectralSign m := by
  rw [traceRight, characterH1_representative]
  exact spectralFourier_one m

def modeFrequency (m : ℤ) (b : Bool) : ℤ := if b then -m else m
def modeH1 (a : Bool → ℂ) (m : ℤ) : H1Pair :=
  fun b => NlsGge.Atomic.LIB033.h1Smul (a b) (characterH1 (modeFrequency m b))
lemma modeH1_representative (a : Bool → ℂ) (m : ℤ) (b : Bool) (x : Icc (0 : ℝ) 1) :
    representative (modeH1 a m b) x = a b * characterValue (modeFrequency m b) x := by
  rw [modeH1, NlsGge.Atomic.LIB033.representative_h1Smul]
  change a b * representative (characterH1 (modeFrequency m b)) x = _
  rw [characterH1_representative]
lemma modeH1_value_ae (a : Bool → ℂ) (m : ℤ) (b : Bool) :
    (modeH1 a m b).value =ᵐ[unitMeasure]
      fun x => a b * characterValue (modeFrequency m b) x := by
  filter_upwards [Lp.coeFn_smul (a b) (characterH1 (modeFrequency m b)).value,
    characterH1_value_ae (modeFrequency m b)] with x hs hv
  change ((a b) • (characterH1 (modeFrequency m b)).value) x = _
  rw [hs]
  change a b * (characterH1 (modeFrequency m b)).value x = _
  rw [hv]
lemma modeH1_derivative_ae (a : Bool → ℂ) (m : ℤ) (b : Bool) :
    (modeH1 a m b).derivative =ᵐ[unitMeasure]
      fun x => a b * (Complex.I * ((modeFrequency m b : ℂ) * Real.pi) *
        characterValue (modeFrequency m b) x) := by
  filter_upwards [Lp.coeFn_smul (a b) (characterH1 (modeFrequency m b)).derivative,
    characterH1_derivative_ae (modeFrequency m b)] with x hs hd
  change ((a b) • (characterH1 (modeFrequency m b)).derivative) x = _
  rw [hs]
  change a b * (characterH1 (modeFrequency m b)).derivative x = _
  rw [hd]

lemma modeH1_action (a : Bool → ℂ) (m : ℤ) :
    zsApply 0 (modeH1 a m) = ((m : ℂ) * Real.pi) • h1PairValue (modeH1 a m) := by
  apply PiLp.ext
  intro b
  apply Lp.ext
  have hz : (fun x => (0 : SourcePairL2) b x) =ᵐ[unitMeasure] fun _ => 0 := by
    exact Lp.coeFn_zero ℂ 2 unitMeasure
  have hs := Lp.coeFn_smul ((m : ℂ) * Real.pi) (modeH1 a m b).value
  filter_upwards [zsApply_ae 0 (modeH1 a m) b, modeH1_derivative_ae a m b,
    modeH1_value_ae a m b, hz, hs] with x ha hd hv hz hs
  change zsApply 0 (modeH1 a m) b x =
    (((m : ℂ) * Real.pi) • (modeH1 a m b).value) x
  rw [ha, hs]
  change (if b then Complex.I else -Complex.I) * (modeH1 a m b).derivative x +
    (0 : SourcePairL2) b x * (modeH1 a m (!b)).value x =
    ((m : ℂ) * Real.pi) * (modeH1 a m b).value x
  rw [hd, hv, hz, zero_mul, add_zero]
  cases b <;> simp only [modeFrequency, Bool.false_eq_true, ↓reduceIte, Int.cast_neg] <;>
    ring_nf <;> simp [Complex.I_sq]

lemma spectralSign_neg (m : ℤ) : spectralSign (-m) = spectralSign m := by
  apply spectralSign_eq_of_parity
  omega
@[simp] lemma modeH1_traceLeft (a : Bool → ℂ) (m : ℤ) (b : Bool) :
    traceLeft (modeH1 a m b) = a b := by
  rw [traceLeft, modeH1_representative]
  simp [characterValue]
@[simp] lemma modeH1_traceRight (a : Bool → ℂ) (m : ℤ) (b : Bool) :
    traceRight (modeH1 a m b) = a b * spectralSign m := by
  rw [traceRight, modeH1_representative]
  change a b * fourier (modeFrequency m b) ((1 : ℝ) : SpectralCircle) = _
  rw [spectralFourier_one]
  cases b <;> simp [modeFrequency, spectralSign_neg]

def separatedAmplitude (neu : Bool) (b : Bool) : ℂ :=
  if b then (halfFactor : ℂ) else (halfFactor : ℂ) * separatedSign neu
def separatedH1 (neu : Bool) (m : ℤ) : H1Pair := modeH1 (separatedAmplitude neu) m

def unitAmplitude (c b : Bool) : ℂ := if b = c then 1 else 0
def parityH1 (n : ℤ) (i : Bool × Sector n) : H1Pair := modeH1 (unitAmplitude i.1) i.2.val

lemma fourier_negative_argument (m : ℤ) (x : SpectralCircle) : fourier m (-x) = fourier (-m) x := by
  simp only [fourier_apply, zsmul_neg, neg_zsmul]

set_option backward.isDefEq.respectTransparency false in
lemma separatedH1_value (neu : Bool) (m : ℤ) :
    h1PairValue (separatedH1 neu m) = separatedBasis neu m := by
  rw [separatedBasis_eq]
  apply PiLp.ext
  intro b
  apply Lp.ext
  have hf := spectral_ae_pullback_first_half (coeFn_fourierLp (T := (2 : ℝ)) 2 m)
  have hn := spectral_ae_pullback_first_half
    (spectralNeg_preserving.quasiMeasurePreserving.ae_eq_comp
      (coeFn_fourierLp (T := (2 : ℝ)) 2 m))
  filter_upwards [modeH1_value_ae (separatedAmplitude neu) m b,
    unfoldLinear_component_ae neu (spectralBasis m) b, hf, hn] with x hv hu hf hn
  change (modeH1 (separatedAmplitude neu) m b).value x = _
  rw [hv, hu]
  dsimp only [Function.comp_def] at hn
  change fourierLp 2 m (x : SpectralCircle) = _ at hf
  change fourierLp 2 m (-(x : SpectralCircle)) = _ at hn
  cases b <;> simp only [separatedAmplitude, modeFrequency, characterValue,
    Bool.false_eq_true, ↓reduceIte, spectralBasis]
  · rw [hf]
  · rw [hn, fourier_negative_argument]

lemma scalarParityVector_value (n : ℤ) (m : Sector n) :
    scalarParityIntervalEquiv n (scalarParityVector n m) = (characterH1 m.val).value := by
  apply Lp.ext
  filter_upwards [scalarParityRestrictValue_ae n (scalarParityVector n m),
    spectral_ae_pullback_first_half (coeFn_fourierLp (T := (2 : ℝ)) 2 m.val),
    characterH1_value_ae m.val] with x hr hf hc
  change scalarParityRestrictValue n (scalarParityVector n m) x = _
  rw [hr]
  change fourierLp 2 m.val (x : SpectralCircle) = _
  rw [hf, hc]
  rfl

lemma parityH1_value (n : ℤ) (i : Bool × Sector n) :
    h1PairValue (parityH1 n i) = parityBasis n i := by
  rw [parityBasis_eq]
  apply PiLp.ext
  intro b
  rcases i with ⟨c,m⟩
  change (modeH1 (unitAmplitude c) m.val b).value =
    scalarParityIntervalEquiv n (parityPairVector n (c, negateIndex n m) b)
  cases c <;> cases b <;>
    simp [modeH1, modeFrequency, unitAmplitude, NlsGge.Atomic.LIB033.h1Smul,
      parityPairVector, mixedIndex, scalarParityVector_value]

lemma separatedH1_hasBC (neu : Bool) (m : ℤ) :
    HasZSBoundaryCondition (if neu then .neumann else .dirichlet) (separatedH1 neu m) := by
  cases neu <;>
    simp [HasZSBoundaryCondition, separatedH1, modeH1_traceLeft, modeH1_traceRight,
      separatedAmplitude, separatedSign]

lemma parityH1_hasFloquet (n : ℤ) (i : Bool × Sector n) (b : Bool) :
    traceRight (parityH1 n i b) = spectralSign n * traceLeft (parityH1 n i b) := by
  rw [parityH1, modeH1_traceRight, modeH1_traceLeft,
    spectralSign_eq_of_parity i.2.val n i.2.property, mul_comm]

lemma parityH1_hasBC_periodic (i : Bool × Sector 0) :
    HasZSBoundaryCondition .periodic (parityH1 0 i) := by
  intro b
  simpa only [spectralSign, Int.zero_emod, ite_true, one_mul] using parityH1_hasFloquet 0 i b
lemma parityH1_hasBC_antiperiodic (i : Bool × Sector 1) :
    HasZSBoundaryCondition .antiperiodic (parityH1 1 i) := by
  intro b
  simpa only [spectralSign, show (1 : ℤ) % 2 ≠ 0 by decide, ite_false, neg_one_mul]
    using parityH1_hasFloquet 1 i b

lemma modeH1_representative_norm_sq (a : Bool → ℂ) (m : ℤ) (x : Icc (0 : ℝ) 1) :
    ‖NlsGge.Atomic.LIB031.pairRepresentative (modeH1 a m) x‖ ^ 2 =
      ‖a true‖ ^ 2 + ‖a false‖ ^ 2 := by
  rw [NlsGge.Atomic.LIB031.pairRepresentative_norm_sq,
    modeH1_representative, modeH1_representative]
  simp only [norm_mul, characterValue_norm, mul_one]

lemma separatedH1_sup_le (neu : Bool) (m : ℤ) :
    ‖NlsGge.Atomic.LIB031.pairRepresentative (separatedH1 neu m)‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).2
  intro x
  have he := modeH1_representative_norm_sq (separatedAmplitude neu) m x
  have hr : ‖(halfFactor : ℂ)‖ = halfFactor := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg halfFactor_nonneg]
  simp only [separatedAmplitude, ↓reduceIte, Bool.false_eq_true, norm_mul,
    separatedSign_norm, mul_one, hr, halfFactor_sq] at he
  have hn := norm_nonneg (NlsGge.Atomic.LIB031.pairRepresentative (separatedH1 neu m) x)
  change ‖NlsGge.Atomic.LIB031.pairRepresentative (modeH1 (separatedAmplitude neu) m) x‖ ≤ 1
  nlinarith only [he, hn]

lemma parityH1_sup_le (n : ℤ) (i : Bool × Sector n) :
    ‖NlsGge.Atomic.LIB031.pairRepresentative (parityH1 n i)‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).2
  intro x
  have he := modeH1_representative_norm_sq (unitAmplitude i.1) i.2.val x
  have ha : ‖unitAmplitude i.1 true‖ ^ 2 + ‖unitAmplitude i.1 false‖ ^ 2 = 1 := by
    rcases i with ⟨b,m⟩
    cases b <;> norm_num [unitAmplitude]
  rw [ha] at he
  change ‖NlsGge.Atomic.LIB031.pairRepresentative (modeH1 (unitAmplitude i.1) i.2.val) x‖ ≤ 1
  nlinarith only [he]

def FreeIndex : ZSBoundaryCondition → Type
  | .dirichlet => ℤ
  | .neumann => ℤ
  | .periodic => Bool × Sector 0
  | .antiperiodic => Bool × Sector 1

def freeZSBasis (bc : ZSBoundaryCondition) : HilbertBasis (FreeIndex bc) ℂ SourcePairL2 :=
  match bc with
  | .dirichlet => separatedBasis false
  | .neumann => separatedBasis true
  | .periodic => parityBasis 0
  | .antiperiodic => parityBasis 1

def freeZSH1 (bc : ZSBoundaryCondition) : FreeIndex bc → H1Pair :=
  match bc with
  | .dirichlet => separatedH1 false
  | .neumann => separatedH1 true
  | .periodic => parityH1 0
  | .antiperiodic => parityH1 1

def freeFrequency (bc : ZSBoundaryCondition) : FreeIndex bc → ℤ :=
  match bc with
  | .dirichlet => id
  | .neumann => id
  | .periodic => fun i => i.2.val
  | .antiperiodic => fun i => i.2.val

def freeEigenvalue (bc : ZSBoundaryCondition) (i : FreeIndex bc) : ℂ :=
  (freeFrequency bc i : ℂ) * Real.pi

theorem freeZSH1_value (bc : ZSBoundaryCondition) (i : FreeIndex bc) :
    h1PairValue (freeZSH1 bc i) = freeZSBasis bc i := by
  cases bc
  · exact separatedH1_value false i
  · exact separatedH1_value true i
  · exact parityH1_value 0 i
  · exact parityH1_value 1 i

theorem freeZSH1_boundary (bc : ZSBoundaryCondition) (i : FreeIndex bc) :
    HasZSBoundaryCondition bc (freeZSH1 bc i) := by
  cases bc
  · exact separatedH1_hasBC false i
  · exact separatedH1_hasBC true i
  · exact parityH1_hasBC_periodic i
  · exact parityH1_hasBC_antiperiodic i

theorem freeZSH1_action (bc : ZSBoundaryCondition) (i : FreeIndex bc) :
    zsApply 0 (freeZSH1 bc i) = freeEigenvalue bc i • freeZSBasis bc i := by
  rw [← freeZSH1_value]
  cases bc <;> exact modeH1_action _ _

theorem freeZSBasis_mem_domain (bc : ZSBoundaryCondition) (i : FreeIndex bc) :
    freeZSBasis bc i ∈ (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain :=
  ⟨freeZSH1 bc i, freeZSH1_boundary bc i, freeZSH1_value bc i⟩

/-- Eigenvector equality for the actual densely defined interval realization. -/
theorem free_zs_eigenvector (bc : ZSBoundaryCondition) (i : FreeIndex bc) :
    NlsGge.Atomic.LIB033.zsRealization 0 bc
      ⟨freeZSBasis bc i, freeZSBasis_mem_domain bc i⟩ =
        freeEigenvalue bc i • freeZSBasis bc i := by
  have he : (⟨freeZSBasis bc i, freeZSBasis_mem_domain bc i⟩ :
      (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain) =
      ⟨h1PairValue (freeZSH1 bc i), ⟨freeZSH1 bc i, freeZSH1_boundary bc i, rfl⟩⟩ := by
    apply Subtype.ext
    exact (freeZSH1_value bc i).symm
  rw [he, NlsGge.Atomic.LIB033.zsRealization_apply 0 bc (freeZSH1 bc i)
    (freeZSH1_boundary bc i)]
  exact freeZSH1_action bc i

theorem free_zs_orthonormal (bc : ZSBoundaryCondition) : Orthonormal ℂ (freeZSBasis bc) :=
  (freeZSBasis bc).orthonormal

theorem free_zs_complete (bc : ZSBoundaryCondition) :
    (Submodule.span ℂ (Set.range (freeZSBasis bc))).topologicalClosure = ⊤ :=
  (freeZSBasis bc).dense_span

theorem free_zs_normalized (bc : ZSBoundaryCondition) (i : FreeIndex bc) :
    ‖freeZSBasis bc i‖ = 1 := (freeZSBasis bc).orthonormal.norm_eq_one i

/-- One constant controls every canonical representative in all four bases. -/
theorem free_zs_sup_le_one (bc : ZSBoundaryCondition) (i : FreeIndex bc) :
    ‖NlsGge.Atomic.LIB031.pairRepresentative (freeZSH1 bc i)‖ ≤ 1 := by
  cases bc
  · exact separatedH1_sup_le false i
  · exact separatedH1_sup_le true i
  · exact parityH1_sup_le 0 i
  · exact parityH1_sup_le 1 i

lemma characterValue_exp (m : ℤ) (x : ℝ) :
    characterValue m x = Complex.exp (Complex.I * (m : ℂ) * Real.pi * (x : ℂ)) := by
  rw [characterValue, fourier_coe_apply]
  congr 1
  norm_num
  ring

/-- The separated basis has exactly the source's normalized exponential formulas.
The boolean chooses the Neumann minus sign in the lower component. -/
theorem separated_representative_formula (neu : Bool) (m : ℤ) (x : Icc (0 : ℝ) 1) :
    representative (separatedH1 neu m true) x = (halfFactor : ℂ) *
      Complex.exp (-Complex.I * (m : ℂ) * Real.pi * (x : ℂ)) ∧
    representative (separatedH1 neu m false) x = (halfFactor : ℂ) * separatedSign neu *
      Complex.exp (Complex.I * (m : ℂ) * Real.pi * (x : ℂ)) := by
  simp only [separatedH1, modeH1_representative, separatedAmplitude,
    modeFrequency, ↓reduceIte, Bool.false_eq_true, characterValue_exp, Int.cast_neg]
  constructor
  · congr 2
    ring
  · trivial

/-- Native periodic/antiperiodic modes use the selected component and the even/odd
integer frequency respectively. This is an equality of canonical representatives. -/
theorem parity_representative_formula (n : ℤ) (i : Bool × Sector n)
    (b : Bool) (x : Icc (0 : ℝ) 1) :
    representative (parityH1 n i b) x = unitAmplitude i.1 b *
      Complex.exp (Complex.I * (modeFrequency i.2.val b : ℂ) * Real.pi * (x : ℂ)) := by
  rw [parityH1, modeH1_representative, characterValue_exp]

end NlsGge.Atomic.LIB036

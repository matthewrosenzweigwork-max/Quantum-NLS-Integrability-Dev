import NlsGge.Ramer.General.RamerSetting
import NlsGge.Measure.CountableGaussian
import NlsGge.Measure.CountableReconstruction
import NlsGge.Ramer.SpaceTransfer

/-!
# The measure layer over a `RamerSetting` (G1)

See `NlsGge/Ramer/RAMER_GENERALIZATION_PLAN.md` ("G1 FINAL SPEC").

`S.γ = countableComplexGaussian S.q` on `ℤ → ℂ`, a.s. supported in `{memE}`, the realization
`S.R : (ℤ → ℂ) → S.E`, the law `S.γE = S.γ.map S.R`, coordinates back (`S.coordE`),
measure-preserving transfer both ways, window truncations `S.headE N`, translations in
coordinates, and the regression to the project's `E_s` setting.

Only the coordinate API of G0 is used.  Since `S.E` is a type synonym, this file also provides
its Borel `MeasurableSpace`/`BorelSpace` instances.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology
open NlsGge.Pilot NlsGge.Measure

namespace NlsGge.Ramer.General

namespace RamerSetting

variable (S : RamerSetting)

instance instMeasurableSpaceE : MeasurableSpace S.E := borel S.E

instance instBorelSpaceE : BorelSpace S.E := ⟨rfl⟩

/-! ## 1. The law -/

/-- The Gaussian law of the sequence of Fourier coordinates. -/
def γ : Measure (ℤ → ℂ) := countableComplexGaussian S.q

instance instIsProbabilityMeasureγ : IsProbabilityMeasure S.γ := by
  unfold γ; infer_instance

theorem γ_map_eval (n : ℤ) : S.γ.map (fun z : ℤ → ℂ => z n) = complexGaussian (S.q n) :=
  countableComplexGaussian_map_eval S.q n

/-! ## 2. Almost-sure support -/

theorem measurable_form_coord (n : ℤ) :
    Measurable (fun z : ℤ → ℂ => (S.M n).form (z n) (z n)) := by
  unfold ModeForm.form
  have h1 : Measurable (fun z : ℤ → ℂ => (z n).re) :=
    Complex.measurable_re.comp (measurable_pi_apply n)
  have h2 : Measurable (fun z : ℤ → ℂ => (z n).im) :=
    Complex.measurable_im.comp (measurable_pi_apply n)
  fun_prop

theorem measurableSet_memE : MeasurableSet {z : ℤ → ℂ | S.memE z} := by
  have hm : Measurable (fun z : ℤ → ℂ => ∑' n : ℤ, ENNReal.ofReal ((S.M n).form (z n) (z n))) :=
    Measurable.tsum (fun n => (S.measurable_form_coord n).ennreal_ofReal)
  have : {z : ℤ → ℂ | S.memE z} =
      (fun z : ℤ → ℂ => ∑' n : ℤ, ENNReal.ofReal ((S.M n).form (z n) (z n))) ⁻¹' {⊤}ᶜ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · intro hz
      exact hz.tsum_ofReal_ne_top
    · intro hz
      have hs := ENNReal.tsum_coe_ne_top_iff_summable_coe.mp
        (show (∑' n : ℤ, (((S.M n).form (z n) (z n)).toNNReal : ℝ≥0∞)) ≠ ⊤ from hz)
      exact hs.congr (fun n => Real.coe_toNNReal _ ((S.M n).form_nonneg _))
  rw [this]
  exact hm (measurableSet_singleton _).compl

theorem summable_tr_div : Summable (fun n : ℤ => (S.M n).tr / S.q n) := by
  refine (S.hs.mul_left 2).congr (fun n => ?_)
  have := (S.q_pos n).ne'
  field_simp

theorem ae_memE : ∀ᵐ z ∂S.γ, S.memE z := by
  have h := ae_sequenceSummable S.q (fun n => (S.M n).tr) S.q_pos
    (fun n => (S.M n).tr_pos.le) S.summable_tr_div
  filter_upwards [h] with z hz
  exact Summable.of_nonneg_of_le (fun n => (S.M n).form_nonneg _)
    (fun n => (S.M n).form_le_tr _) hz

/-! ## 3. The realization -/

/-- The realization `ℤ → ℂ → E` (arbitrary off `{memE}`). -/
def R (z : ℤ → ℂ) : S.E := by
  classical
  exact if h : S.memE z then S.ofSeq z h else 0

theorem coord_R {z : ℤ → ℂ} (hz : S.memE z) (n : ℤ) : S.coord n (S.R z) = z n := by
  simp [R, hz]

theorem R_of_not_memE {z : ℤ → ℂ} (hz : ¬ S.memE z) : S.R z = 0 := by
  simp [R, hz]

theorem coord_R_ae : ∀ᵐ z ∂S.γ, ∀ n, S.coord n (S.R z) = z n := by
  filter_upwards [S.ae_memE] with z hz n using S.coord_R hz n

/-- Window truncation of a sequence, as an element of `E`. -/
def headE (N : ℕ) (z : ℤ → ℂ) : S.E :=
  S.ofSeq (fun n => if n ∈ symmetricModes N then z n else 0)
    (S.memE_of_finite_support ((symmetricModes N).finite_toSet.subset (fun n hn => by
      by_contra h
      apply hn
      simp only [Finset.mem_coe] at h
      simp [h])))

theorem coord_headE (N : ℕ) (z : ℤ → ℂ) (n : ℤ) :
    S.coord n (S.headE N z) = if n ∈ symmetricModes N then z n else 0 := by
  simp [headE]

theorem headE_eq_sum (N : ℕ) (z : ℤ → ℂ) :
    S.headE N z = S.ofLp (∑ n ∈ symmetricModes N,
      lp.single (E := fun _ : ℤ => EuclideanSpace ℝ (Fin 2)) 2 n ((S.M n).chol (z n))) := by
  classical
  apply S.E_ext; intro n
  apply (S.M n).chol.injective
  rw [S.chol_coord, S.chol_coord, raw_ofLp, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply, Finset.sum_pi_single]
  rw [← S.chol_coord (S.headE N z) n, coord_headE]
  split_ifs with hn
  · rfl
  · exact map_zero _

theorem continuous_headE (N : ℕ) : Continuous (S.headE N) := by
  have hterm (n : ℤ) : Continuous (fun z : ℤ → ℂ =>
      lp.single (E := fun _ : ℤ => EuclideanSpace ℝ (Fin 2)) 2 n ((S.M n).chol (z n))) :=
    (lp.isometry_single (p := (2 : ℝ≥0∞))
      (E := fun _ : ℤ => EuclideanSpace ℝ (Fin 2)) n).continuous.comp
      ((S.M n).chol.continuous.comp (continuous_apply n))
  have hsum : Continuous (fun z : ℤ → ℂ =>
      (∑ n ∈ symmetricModes N, lp.single (E := fun _ : ℤ => EuclideanSpace ℝ (Fin 2)) 2 n
        ((S.M n).chol (z n)) : lp (fun _ : ℤ => EuclideanSpace ℝ (Fin 2)) 2)) :=
    continuous_finsetSum _ (fun n _ => hterm n)
  have e : S.headE N = fun z => S.ofLp (∑ n ∈ symmetricModes N,
      lp.single (E := fun _ : ℤ => EuclideanSpace ℝ (Fin 2)) 2 n ((S.M n).chol (z n))) :=
    funext (S.headE_eq_sum N)
  rw [e]
  exact hsum

theorem headE_eq_projE_R {z : ℤ → ℂ} (hz : S.memE z) (N : ℕ) :
    S.headE N z = S.projE N (S.R z) := by
  apply S.E_ext; intro n
  rw [coord_headE, coord_projE]
  split_ifs
  · exact (S.coord_R hz n).symm
  · rfl

/-- Window truncation, set to `0` off `{memE}`. -/
def headEApprox (N : ℕ) (z : ℤ → ℂ) : S.E := by
  classical
  exact if S.memE z then S.headE N z else 0

theorem measurable_headEApprox (N : ℕ) : Measurable (S.headEApprox N) := by
  classical
  exact Measurable.ite S.measurableSet_memE (S.continuous_headE N).measurable measurable_const

theorem tendsto_headEApprox (z : ℤ → ℂ) :
    Tendsto (fun N => S.headEApprox N z) atTop (𝓝 (S.R z)) := by
  classical
  by_cases hz : S.memE z
  · simp only [headEApprox, if_pos hz]
    simp_rw [S.headE_eq_projE_R hz]
    exact S.projE_tendsto _
  · simp only [headEApprox, if_neg hz, S.R_of_not_memE hz]
    exact tendsto_const_nhds

theorem measurable_R : Measurable S.R :=
  measurable_of_tendsto_metrizable S.measurable_headEApprox
    (tendsto_pi_nhds.mpr S.tendsto_headEApprox)

theorem tendsto_headE_ae :
    ∀ᵐ z ∂S.γ, Tendsto (fun N => S.headE N z) atTop (𝓝 (S.R z)) := by
  filter_upwards [S.ae_memE] with z hz
  simp_rw [S.headE_eq_projE_R hz]
  exact S.projE_tendsto _

/-! ## 4. The law on `E` -/

/-- The Gaussian law on `E`. -/
def γE : Measure S.E := S.γ.map S.R

instance instIsProbabilityMeasureγE : IsProbabilityMeasure S.γE := by
  unfold γE
  exact ⟨by rw [Measure.map_apply S.measurable_R MeasurableSet.univ]; simp⟩

/-! ## 5. Coordinates back -/

/-- The coordinate sequence of a vector of `E`. -/
def coordE (x : S.E) : ℤ → ℂ := fun n => S.coord n x

theorem measurable_coordE : Measurable S.coordE :=
  measurable_pi_iff.mpr fun n => (S.coord n).continuous.measurable

theorem memE_coordE (x : S.E) : S.memE (S.coordE x) := S.memE_coord x

theorem R_coordE (x : S.E) : S.R (S.coordE x) = x := by
  apply S.E_ext; intro n
  rw [S.coord_R (S.memE_coordE x)]
  rfl

theorem coordE_R_ae : ∀ᵐ z ∂S.γ, S.coordE (S.R z) = z := by
  filter_upwards [S.coord_R_ae] with z hz
  funext n
  exact hz n

theorem measurePreserving_R : MeasurePreserving S.R S.γ S.γE :=
  ⟨S.measurable_R, rfl⟩

theorem measurePreserving_coordE : MeasurePreserving S.coordE S.γE S.γ := by
  refine ⟨S.measurable_coordE, ?_⟩
  unfold γE
  rw [Measure.map_map S.measurable_coordE S.measurable_R]
  have : Measure.map (S.coordE ∘ S.R) S.γ = Measure.map id S.γ :=
    Measure.map_congr S.coordE_R_ae
  rw [this, Measure.map_id]

theorem ae_of_ae_coordE {P : (ℤ → ℂ) → Prop} (h : ∀ᵐ z ∂S.γ, P z) :
    ∀ᵐ x ∂S.γE, P (S.coordE x) :=
  S.measurePreserving_coordE.quasiMeasurePreserving.ae h

theorem integral_comp_coordE {f : (ℤ → ℂ) → ℝ} (hf : AEStronglyMeasurable f S.γ) :
    ∫ x, f (S.coordE x) ∂S.γE = ∫ z, f z ∂S.γ := by
  have := S.measurePreserving_coordE.map_eq
  rw [← this] at hf ⊢
  rw [integral_map S.measurable_coordE.aemeasurable hf]

theorem lintegral_comp_coordE {f : (ℤ → ℂ) → ℝ≥0∞} (hf : AEMeasurable f S.γ) :
    ∫⁻ x, f (S.coordE x) ∂S.γE = ∫⁻ z, f z ∂S.γ := by
  have := S.measurePreserving_coordE.map_eq
  rw [← this] at hf ⊢
  rw [lintegral_map' hf S.measurable_coordE.aemeasurable]

theorem tendstoInMeasure_comp_coordE {ι : Type*} {l : Filter ι} {F : Type*}
    [PseudoEMetricSpace F] {f : ι → (ℤ → ℂ) → F} {g : (ℤ → ℂ) → F}
    (h : TendstoInMeasure S.γ f l g) :
    TendstoInMeasure S.γE (fun i x => f i (S.coordE x)) l (fun x => g (S.coordE x)) := by
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun _ => zero_le) (fun i => ?_)
  have := Measure.le_map_apply S.measurable_coordE.aemeasurable
    (μ := S.γE) {z | ε ≤ edist (f i z) (g z)}
  rw [S.measurePreserving_coordE.map_eq] at this
  exact this

/-! ## 7. Translations in coordinates -/

theorem coordE_add_incl (x : S.E) (h : S.H) :
    S.coordE (x + S.incl h) = S.coordE x + S.hcoord h := by
  funext n
  simp [coordE, S.coord_add]

theorem coordE_sub_incl (x : S.E) (h : S.H) :
    S.coordE (x - S.incl h) = S.coordE x - S.hcoord h := by
  funext n
  simp [coordE, map_sub]

theorem memE_add {z w : ℤ → ℂ} (hz : S.memE z) (hw : S.memE w) : S.memE (z + w) := by
  have h := ((hz.mul_left 2).add (hw.mul_left 2))
  refine Summable.of_nonneg_of_le (fun n => (S.M n).form_nonneg _) (fun n => ?_) h
  have := (S.M n).form_nonneg (z n - w n)
  simp only [Pi.add_apply]
  simp only [ModeForm.form, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im] at this ⊢
  nlinarith [this]

theorem R_add {z : ℤ → ℂ} (hz : S.memE z) (h : S.H) :
    S.R (z + S.hcoord h) = S.R z + S.incl h := by
  have hzh : S.memE (z + S.hcoord h) := S.memE_add hz (S.memE_hcoord h)
  apply S.E_ext; intro n
  rw [S.coord_R hzh, S.coord_add, S.coord_R hz, S.coord_incl]
  rfl

/-! ## 8. Regression to the `E_s` instance -/

section Regression

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s)

theorem ofCoefficients_γ : (ofCoefficients c s hs).γ = fullWeightSequenceGaussian c.val := rfl

theorem memE_iff_weightedSquareSummable (z : ℤ → ℂ) :
    (ofCoefficients c s hs).memE z ↔ WeightedSquareSummable (sourceRate c) s z := by
  unfold ofCoefficients
  rw [memE_ofWeights_iff]
  rfl

theorem fullWeightedEquiv_realization (z : ℤ → ℂ) :
    fullWeightedEquiv c s hs (fullWeightedSequenceRealization c s z) =
      (ofCoefficients c s hs).R z := by
  by_cases hz : (ofCoefficients c s hs).memE z
  · have hz' := (memE_iff_weightedSquareSummable c s hs z).1 hz
    apply (ofCoefficients c s hs).E_ext; intro n
    rw [coord_fullWeightedEquiv, (ofCoefficients c s hs).coord_R hz]
    exact fullWeightedSequenceRealization_apply c s z hz' n
  · have hz' : ¬ WeightedSquareSummable (sourceRate c) s z :=
      fun h => hz ((memE_iff_weightedSquareSummable c s hs z).2 h)
    rw [(ofCoefficients c s hs).R_of_not_memE hz]
    have : fullWeightedSequenceRealization c s z = 0 := by
      simp [fullWeightedSequenceRealization, hz']
    rw [this]; exact (fullWeightedEquiv c s hs).map_zero

theorem ofCoefficients_γE :
    (ofCoefficients c s hs).γE = (fullWeightedSequenceGaussian c s).map (fullWeightedEquiv c s hs) := by
  unfold fullWeightedSequenceGaussian γE
  rw [Measure.map_map (fullWeightedEquiv c s hs).continuous.measurable
    (measurable_fullWeightedSequenceRealization c s)]
  congr 1
  funext z
  exact (fullWeightedEquiv_realization c s hs z).symm

theorem coordE_fullWeightedEquiv (x : FullWeightedHilbert c s) :
    (ofCoefficients c s hs).coordE (fullWeightedEquiv c s hs x) = NlsGge.Ramer.coordE c s x := by
  funext n
  exact coord_fullWeightedEquiv c s hs x n

end Regression

end RamerSetting

end NlsGge.Ramer.General

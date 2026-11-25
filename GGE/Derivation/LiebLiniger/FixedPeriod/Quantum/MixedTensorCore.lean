import LiebLiniger.FixedPeriod.Quantum.SymmetricTensorBridges
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
Actual mixed product kernels and their continuous multilinear map.
Candidate only: root alone runs the compiler. No density or totality premise.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace LiebLiniger.FixedPeriod.Quantum

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product has one independently chosen L² factor in each coordinate. -/
theorem mixedTensorFunction_memLp (u : ι → Lp ℂ 2 μ) :
    MemLp (fun x : ι → X => ∏ i, u i (x i)) 2 (Measure.pi fun _ : ι => μ) := by
  have hm : AEStronglyMeasurable (fun x : ι → X => ∏ i, u i (x i))
      (Measure.pi fun _ : ι => μ) := by
    apply Finset.aestronglyMeasurable_fun_prod
    intro i _
    exact (Lp.aestronglyMeasurable (u i)).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : ι => μ) i)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  simpa only [norm_prod, Finset.prod_pow] using
    (Integrable.fintype_prod (fun i : ι => (Lp.memLp (u i)).norm.integrable_sq))

def mixedTensorL2 (u : ι → Lp ℂ 2 μ) : ProductL2 μ ι :=
  (mixedTensorFunction_memLp μ u).toLp (fun x => ∏ i, u i (x i))

theorem coeFn_mixedTensorL2 (u : ι → Lp ℂ 2 μ) :
    (mixedTensorL2 μ u : (ι → X) → ℂ) =ᵐ[Measure.pi fun _ : ι => μ]
      fun x => ∏ i, u i (x i) :=
  (mixedTensorFunction_memLp μ u).coeFn_toLp

@[simp] theorem mixedTensorL2_diagonal (u : Lp ℂ 2 μ) :
    mixedTensorL2 (ι := ι) μ (fun _ => u) = pureTensorL2 μ u := by
  apply Lp.ext
  exact (coeFn_mixedTensorL2 μ _).trans ((pureTensorFunction_memLp (ι := ι) μ u).coeFn_toLp).symm

theorem inner_mixedTensorL2 (u v : ι → Lp ℂ 2 μ) :
    inner ℂ (mixedTensorL2 μ u) (mixedTensorL2 μ v) = ∏ i, inner ℂ (u i) (v i) := by
  classical
  have hpair (i : ι) : Integrable (fun x => inner ℂ (u i x) (v i x)) μ :=
    L2.integrable_inner (u i) (v i)
  have hprod := Integrable.fintype_prod hpair
  rw [L2.inner_def]
  calc
    _ = ∫ x : ι → X, ∏ i, inner ℂ (u i (x i)) (v i (x i))
        ∂Measure.pi (fun _ : ι => μ) := by
      apply integral_congr_ae
      filter_upwards [coeFn_mixedTensorL2 μ u, coeFn_mixedTensorL2 μ v] with x hu hv
      rw [hu, hv]
      simp only [RCLike.inner_apply, map_prod, Finset.prod_mul_distrib]
    _ = ∏ i, ∫ x, inner ℂ (u i x) (v i x) ∂μ :=
      integral_fintype_prod_eq_prod (𝕜 := ℂ)
        (fun i : ι => fun x : X => inner ℂ (u i x) (v i x))
    _ = _ := Finset.prod_congr rfl (fun i _ => (L2.inner_def (u i) (v i)).symm)

theorem norm_mixedTensorL2 (u : ι → Lp ℂ 2 μ) :
    ‖mixedTensorL2 μ u‖ = ∏ i, ‖u i‖ := by
  classical
  have hs : ‖mixedTensorL2 μ u‖^2 = (∏ i, ‖u i‖)^2 := by
    have hi : (∏ i, inner ℂ (u i) (u i)) = (((∏ i, ‖u i‖)^2 : ℝ) : ℂ) := by
      calc
        _ = ∏ i, (‖u i‖ : ℂ)^2 := by
          apply Finset.prod_congr rfl
          intro i _
          simpa only [RCLike.ofReal_eq_complex_ofReal] using
            (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (u i))
        _ = _ := by rw [← Finset.prod_pow]; push_cast; rfl
    calc
      _ = (inner ℂ (mixedTensorL2 μ u) (mixedTensorL2 μ u)).re :=
        norm_sq_eq_re_inner (𝕜 := ℂ) _
      _ = (∏ i, inner ℂ (u i) (u i)).re :=
        congrArg Complex.re (inner_mixedTensorL2 μ u u)
      _ = _ := by rw [hi, Complex.ofReal_re]
  have hp : 0 ≤ ∏ i, ‖u i‖ := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  nlinarith only [hs, norm_nonneg (mixedTensorL2 μ u), hp]

/-- Pulling out one factor from an actual product kernel. -/
theorem mixedTensorFunction_update (u : ι → Lp ℂ 2 μ)
    (i : ι) (v : Lp ℂ 2 μ) (x : ι → X) :
    (∏ j, (Function.update u i v j) (x j)) =
      v (x i) * ∏ j ∈ Finset.univ \ {i}, u j (x j) := by
  have hf : (fun j => (Function.update u i v j) (x j)) =
      Function.update (fun j => u j (x j)) i (v (x i)) := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [hf, Finset.prod_update_of_mem (Finset.mem_univ _)]

theorem mixedTensorL2_update_add (u : ι → Lp ℂ 2 μ) (i : ι) (v w : Lp ℂ 2 μ) :
    mixedTensorL2 μ (Function.update u i (v + w)) =
      mixedTensorL2 μ (Function.update u i v) + mixedTensorL2 μ (Function.update u i w) := by
  classical
  have hvw : ∀ᵐ x : ι → X ∂Measure.pi (fun _ : ι => μ),
      (v + w) (x i) = v (x i) + w (x i) := by
    filter_upwards [(Lp.coeFn_add v w).comp_tendsto
      (Measure.quasiMeasurePreserving_eval (fun _ : ι => μ) i).tendsto_ae] with x hx
    simpa only [Pi.add_apply, Function.comp_apply] using hx
  apply Lp.ext
  filter_upwards [coeFn_mixedTensorL2 μ (Function.update u i (v + w)),
    coeFn_mixedTensorL2 μ (Function.update u i v),
    coeFn_mixedTensorL2 μ (Function.update u i w),
    Lp.coeFn_add (mixedTensorL2 μ (Function.update u i v))
      (mixedTensorL2 μ (Function.update u i w)), hvw] with x hl hv hw hr ha
  rw [hl, hr]
  simp only [Pi.add_apply]
  rw [hv, hw]
  simp only [mixedTensorFunction_update, ha]
  ring

theorem mixedTensorL2_update_smul (u : ι → Lp ℂ 2 μ) (i : ι) (z : ℂ) (v : Lp ℂ 2 μ) :
    mixedTensorL2 μ (Function.update u i (z • v)) =
      z • mixedTensorL2 μ (Function.update u i v) := by
  classical
  have hzv : ∀ᵐ x : ι → X ∂Measure.pi (fun _ : ι => μ),
      (z • v) (x i) = z * v (x i) := by
    filter_upwards [(Lp.coeFn_smul z v).comp_tendsto
      (Measure.quasiMeasurePreserving_eval (fun _ : ι => μ) i).tendsto_ae] with x hx
    simpa only [Pi.smul_apply, smul_eq_mul, Function.comp_apply] using hx
  apply Lp.ext
  filter_upwards [coeFn_mixedTensorL2 μ (Function.update u i (z • v)),
    coeFn_mixedTensorL2 μ (Function.update u i v),
    Lp.coeFn_smul z (mixedTensorL2 μ (Function.update u i v)), hzv] with x hl hv hr ha
  rw [hl, hr]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hv]
  simp only [mixedTensorFunction_update, ha, Pi.smul_apply, smul_eq_mul]
  ring

/-- Literal coordinate-product multilinearity, proved in the L² quotient. -/
def mixedTensorMultilinear : MultilinearMap ℂ (fun _ : ι => Lp ℂ 2 μ) (ProductL2 μ ι) := by
  classical
  exact MultilinearMap.mk' (mixedTensorL2 μ)
    (mixedTensorL2_update_add μ) (mixedTensorL2_update_smul μ)

/-- The continuous multilinear product-kernel map, with exact product norm. -/
def mixedTensorContinuousMultilinear :
    ContinuousMultilinearMap ℂ (fun _ : ι => Lp ℂ 2 μ) (ProductL2 μ ι) :=
  (mixedTensorMultilinear μ).mkContinuous 1 (fun u => by
    change ‖mixedTensorL2 μ u‖ ≤ 1 * ∏ i, ‖u i‖
    rw [norm_mixedTensorL2, one_mul])

@[simp] theorem mixedTensorContinuousMultilinear_apply (u : ι → Lp ℂ 2 μ) :
    mixedTensorContinuousMultilinear μ u = mixedTensorL2 μ u := rfl

/-- Pullback of a mixed product permutes its one-particle factors in the
opposite order. The inverse is forced by the coordinate pullback convention. -/
theorem permutationL2_mixedTensorL2 (σ : Equiv.Perm ι) (u : ι → Lp ℂ 2 μ) :
    permutationL2 μ σ (mixedTensorL2 μ u) = mixedTensorL2 μ (fun i => u (σ.symm i)) := by
  change Lp.compMeasurePreserving _ _ ((mixedTensorFunction_memLp μ u).toLp _) =
    (mixedTensorFunction_memLp μ _).toLp _
  rw [Lp.toLp_compMeasurePreserving]
  apply MemLp.toLp_congr
  apply Filter.Eventually.of_forall
  intro x
  simpa only [Function.comp_apply, coordinatePermutation_apply,
    Equiv.symm_apply_apply] using Equiv.prod_comp σ (fun j => u (σ.symm j) (x j))

/-- Genuine symmetric n-linear kernel map used for pure-power polarization. -/
def symmetricTensorContinuousMultilinear (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => Lp ℂ 2 μ) (SymmetricSector μ n) :=
  (symmetricSectorProjection μ n).compContinuousMultilinearMap
    (mixedTensorContinuousMultilinear μ)

/-- Symmetrization makes the actual mixed-kernel map invariant under
permuting its factors. -/
theorem symmetricTensorContinuousMultilinear_permutation (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (u : Fin n → Lp ℂ 2 μ) :
    symmetricTensorContinuousMultilinear μ n (fun i => u (σ i)) =
      symmetricTensorContinuousMultilinear μ n u := by
  apply Subtype.ext
  change symmetrizeL2 μ (mixedTensorL2 μ (fun i => u (σ i))) =
    symmetrizeL2 μ (mixedTensorL2 μ u)
  have hp : mixedTensorL2 μ (fun i => u (σ i)) =
      permutationL2 μ σ.symm (mixedTensorL2 μ u) := by
    simpa only [Equiv.symm_symm] using
      (permutationL2_mixedTensorL2 μ σ.symm u).symm
  rw [hp, symmetrizeL2_permutationL2]

section FiniteMeasureTotality
variable [IsFiniteMeasure μ]

/-- Coordinate indicator products are exactly rectangle indicators in L². -/
theorem mixedTensorL2_indicator (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i)) :
    mixedTensorL2 μ (fun i => indicatorConstLp 2 (hs i) (measure_ne_top μ (s i)) (1 : ℂ)) =
      indicatorConstLp 2 (MeasurableSet.univ_pi hs) (measure_ne_top _ _) (1 : ℂ) := by
  classical
  have hi : ∀ᵐ x : ι → X ∂Measure.pi (fun _ : ι => μ), ∀ i : ι,
      indicatorConstLp 2 (hs i) (measure_ne_top μ (s i)) (1 : ℂ) (x i) =
        (s i).indicator (fun _ => (1 : ℂ)) (x i) := by
    apply ae_all_iff.mpr
    intro i
    exact (indicatorConstLp_coeFn (p := 2) (hs := hs i)
      (hμs := measure_ne_top μ (s i)) (c := (1 : ℂ))).comp_tendsto
        (Measure.quasiMeasurePreserving_eval (fun _ : ι => μ) i).tendsto_ae
  apply Lp.ext
  filter_upwards [coeFn_mixedTensorL2 μ
      (fun i => indicatorConstLp 2 (hs i) (measure_ne_top μ (s i)) (1 : ℂ)),
    indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ_pi hs)
      (hμs := measure_ne_top _ _) (c := (1 : ℂ)), hi] with x hm hb hx
  rw [hm, hb]
  simp_rw [hx]
  by_cases hxs : x ∈ Set.pi Set.univ s
  · have hxi (i : ι) : x i ∈ s i := hxs i (Set.mem_univ _)
    simp [hxs, hxi]
  · rw [Set.indicator_of_notMem hxs]
    obtain ⟨i, hi⟩ : ∃ i : ι, x i ∉ s i := by
      simpa only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] using hxs
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Box integrals determine an integrable function on the actual finite product
space. This includes the empty-coordinate space. -/
theorem ae_eq_zero_of_pi_box_integrals (f : (ι → X) → ℂ)
    (hf : Integrable f (Measure.pi fun _ : ι => μ))
    (hbox : ∀ (s : ι → Set X), (∀ i, MeasurableSet (s i)) →
      ∫ x in Set.pi Set.univ s, f x ∂Measure.pi (fun _ : ι => μ) = 0) :
    f =ᵐ[Measure.pi fun _ : ι => μ] 0 := by
  have hu : ∫ x, f x ∂Measure.pi (fun _ : ι => μ) = 0 := by
    simpa only [Set.pi_univ, setIntegral_univ] using
      hbox (fun _ => Set.univ) (fun _ => MeasurableSet.univ)
  have hall : ∀ s : Set (ι → X), MeasurableSet s →
      ∫ x in s, f x ∂Measure.pi (fun _ : ι => μ) = 0 := by
    refine MeasurableSpace.induction_on_inter
      (C := fun s _ => ∫ x in s, f x ∂Measure.pi (fun _ : ι => μ) = 0)
      generateFrom_pi.symm isPiSystem_pi ?_ ?_ ?_ ?_
    · simp only [setIntegral_empty]
    · rintro _ ⟨s, hs, rfl⟩
      exact hbox s (fun i => hs i (Set.mem_univ _))
    · intro s hs hzero
      have h := integral_add_compl hs hf
      rw [hzero, zero_add, hu] at h
      exact h
    · intro s hdisj hs hzero
      rw [integral_iUnion hs hdisj hf.integrableOn]
      simp only [hzero, tsum_zero]
  exact ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite
    (fun _ _ _ => hf.integrableOn) (fun s hs _ => hall s hs)

/-- Actual elementary product kernels are total in product L². Density is
proved by box indicators and the generating π-system, rather than assumed. -/
theorem mixedTensorL2_eq_zero_of_inner (f : ProductL2 μ ι)
    (h : ∀ u : ι → Lp ℂ 2 μ, inner ℂ f (mixedTensorL2 μ u) = 0) : f = 0 := by
  have hint : Integrable f (Measure.pi fun _ : ι => μ) := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim
        (measure_ne_top (Measure.pi fun _ : ι => μ) Set.univ)
  have hbox : ∀ (s : ι → Set X), (∀ i, MeasurableSet (s i)) →
      ∫ x in Set.pi Set.univ s, f x ∂Measure.pi (fun _ : ι => μ) = 0 := by
    intro s hs
    have hi := h (fun i => indicatorConstLp 2 (hs i) (measure_ne_top μ (s i)) (1 : ℂ))
    rw [mixedTensorL2_indicator] at hi
    rw [← L2.inner_indicatorConstLp_one (MeasurableSet.univ_pi hs) (measure_ne_top _ _) f]
    rw [← inner_conj_symm, hi]
    simp
  apply Lp.ext
  exact (ae_eq_zero_of_pi_box_integrals μ f hint hbox).trans (Lp.coeFn_zero ℂ 2 (Measure.pi fun _ : ι => μ)).symm

end FiniteMeasureTotality

end LiebLiniger.FixedPeriod.Quantum

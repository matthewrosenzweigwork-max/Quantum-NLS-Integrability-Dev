import QuantumNLS.BetheExtension
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
First weak derivatives of the literal symmetric Bethe extension.
Source: periodic_basis.tex:24--41 and 245--259, frozen PR11
3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f. The chamber expression and
its continuity/periodic face matching come from BetheExtension c92af850.
Coordinate slices cross only finitely many collision values. No gluing
hypothesis is supplied. WeakDerivatives.lean belongs to the separate
Fourier characterization chain and is not edited here.
-/

noncomputable section
open scoped BigOperators Topology Interval
open Filter MeasureTheory Set

namespace QuantumNLS.BetheWeakGradient
open BetheWavefunctions BetheExtension

/-- The actual classical coordinate derivative of the finite chamber sum. -/
def ansatzPartial {N : ℕ} (c : ℝ) (q : Fin N → ℝ) (i : Fin N)
    (x : Fin N → ℝ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin N), coefficient c (q ∘ σ) *
    (Complex.I * (q (σ i) : ℂ) * planeWave (q ∘ σ) x)

/-- A uniform finite bound; there is no normalization factor. -/
def gradientBound {N : ℕ} (c : ℝ) (q : Fin N → ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin N), ‖coefficient c (q ∘ σ)‖ * ∑ j, |q j|

theorem gradientBound_nonneg {N : ℕ} (c : ℝ) (q : Fin N → ℝ) :
    0 ≤ gradientBound c q := by
  unfold gradientBound
  positivity

theorem norm_ansatzPartial_le {N : ℕ} (c : ℝ) (q : Fin N → ℝ)
    (i : Fin N) (x : Fin N → ℝ) :
    ‖ansatzPartial c q i x‖ ≤ gradientBound c q := by
  classical
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro σ _
  simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    planeWave_norm, one_mul, mul_one]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun j _ => abs_nonneg (q j)) (Finset.mem_univ (σ i)))
    (norm_nonneg _)

theorem planeWave_update_hasDerivAt {N : ℕ} (q x : Fin N → ℝ) (i : Fin N) (t : ℝ) :
    HasDerivAt (fun s => planeWave q (Function.update x i s))
      (Complex.I * (q i : ℂ) * planeWave q (Function.update x i t)) t := by
  classical
  have hdj (j : Fin N) : HasDerivAt
      (fun s => q j * Function.update x i s j) (if j = i then q i else 0) t := by
    by_cases h : j = i
    · subst j
      simpa using (hasDerivAt_id t).const_mul (q i)
    · simpa [h, Function.update_of_ne h] using hasDerivAt_const t (q j * x j)
  have hd : HasDerivAt (fun s => ∑ j, q j * Function.update x i s j) (q i) t := by
    simpa only [Finset.sum_fn, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
      HasDerivAt.sum (u := Finset.univ) (fun j _ => hdj j)
  have hdc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hd
  convert (hdc.const_mul Complex.I).cexp using 1 <;>
    simp [planeWave, mul_assoc, mul_comm]

theorem coordinateAnsatz_update_hasDerivAt {N : ℕ} (c : ℝ)
    (q x : Fin N → ℝ) (i : Fin N) (t : ℝ) :
    HasDerivAt (fun s => coordinateAnsatz c q (Function.update x i s))
      (ansatzPartial c q i (Function.update x i t)) t := by
  simpa only [coordinateAnsatz, ansatzPartial, Finset.sum_fn, Function.comp_apply] using
    HasDerivAt.sum (u := Finset.univ) (fun (σ : Equiv.Perm (Fin N)) _ =>
      (planeWave_update_hasDerivAt (q ∘ σ) x i t).const_mul (coefficient c (q ∘ σ)))

/-- Only collisions involving the differentiated coordinate are exceptional.
Ties among the spectators are allowed throughout the slicing argument. -/
def regular {N : ℕ} (i : Fin N) (x : Fin N → ℝ) : Prop :=
  ∀ j, j ≠ i → x i ≠ x j

/-- Values on collision slices are set to zero. Off them this is the actual
classical coordinate derivative, rather than an assumed gradient field. -/
def gradient {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (i : Fin N)
    (x : Fin N → ℝ) : ℂ := by
  classical
  exact if regular i x then
    deriv (fun t => symmetricExtension L c n (Function.update x i t)) (x i)
  else 0

/-- Local ordering is stable when only one coordinate moves and avoids all
spectator values. Spectator coincidences do not need to be removed. -/
theorem eventually_antitone_update {N : ℕ} {x : Fin N → ℝ}
    (hx : Antitone x) (i : Fin N) (hi : regular i x) :
    ∀ᶠ t in 𝓝 (x i), Antitone (Function.update x i t) := by
  classical
  have hp : ∀ a b : Fin N, a < b →
      ∀ᶠ t in 𝓝 (x i), Function.update x i t b ≤ Function.update x i t a := by
    intro a b hab
    by_cases hai : a = i
    · subst a
      have hlt : x b < x i := lt_of_le_of_ne (hx hab.le) (hi b hab.ne').symm
      filter_upwards [eventually_gt_nhds hlt] with t ht
      simpa [Function.update_of_ne hab.ne'] using ht.le
    · by_cases hbi : b = i
      · subst b
        have hlt : x i < x a := lt_of_le_of_ne (hx hab.le) (hi a hab.ne)
        filter_upwards [eventually_lt_nhds hlt] with t ht
        simpa [Function.update_of_ne hai] using ht.le
      · exact Filter.Eventually.of_forall (fun t => by
          simpa [Function.update_of_ne hai, Function.update_of_ne hbi] using hx hab.le)
  have hall : ∀ᶠ t in 𝓝 (x i), ∀ a b : Fin N, a < b →
      Function.update x i t b ≤ Function.update x i t a := by
    apply Filter.eventually_all.mpr
    intro a
    apply Filter.eventually_all.mpr
    intro b
    by_cases hab : a < b
    · exact (hp a b hab).mono fun _ ht _ => ht
    · exact Filter.Eventually.of_forall fun _ h => (hab h).elim
  exact hall.mono fun _ ht => antitone_iff_forall_lt.mpr ht

theorem regular_permute {N : ℕ} {x : Fin N → ℝ} {i : Fin N}
    (hi : regular i x) (σ : Equiv.Perm (Fin N)) : regular (σ.symm i) (x ∘ σ) := by
  intro j hj
  simpa [Function.comp_def] using hi (σ j) (by
    intro h
    exact hj (σ.injective (h.trans (σ.apply_symm_apply i).symm)))

/-- The genuine derivative off a finite collection of collision values.
Its value is a permuted classical chamber gradient with the original roots. -/
theorem symmetricExtension_update_hasDerivAt {N : ℕ} (L c : ℝ)
    (n : Fin N → ℤ) (i : Fin N) (x : Fin N → ℝ) (hi : regular i x) :
    HasDerivAt (fun t => symmetricExtension L c n (Function.update x i t))
      (ansatzPartial c (BetheSmooth.sourceRoots L n c)
        ((Tuple.sort (α := ℝᵒᵈ) x).symm i) (decreasing x)) (x i) := by
  classical
  let σ := Tuple.sort (α := ℝᵒᵈ) x
  have he (t : ℝ) : Function.update x i t ∘ σ =
      Function.update (x ∘ σ) (σ.symm i) t := by
    simpa using Function.update_comp_eq_of_injective x σ.injective (σ.symm i) t
  have hord : ∀ᶠ t in 𝓝 (x i), Antitone (Function.update (x ∘ σ) (σ.symm i) t) := by
    simpa [decreasing, σ, Function.comp_def] using
      eventually_antitone_update (decreasing_antitone x) (σ.symm i) (regular_permute hi σ)
  have hg : (fun t => symmetricExtension L c n (Function.update x i t)) =ᶠ[𝓝 (x i)]
      (fun t => wavefunction L c n (Function.update (x ∘ σ) (σ.symm i) t)) := by
    filter_upwards [hord] with t ht
    rw [← symmetricExtension_permute L c n _ σ, he]
    exact symmetricExtension_eq L c n ht
  have hd := coordinateAnsatz_update_hasDerivAt c (BetheSmooth.sourceRoots L n c)
    (x ∘ σ) (σ.symm i) (x i)
  have hx : Function.update (x ∘ σ) (σ.symm i) (x i) = decreasing x := by
    simp [σ, decreasing, Function.comp_def]
  rw [hx] at hd
  exact hd.congr_of_eventuallyEq hg

theorem measurableSet_regular {N : ℕ} (i : Fin N) :
    MeasurableSet {x : Fin N → ℝ | regular i x} := by
  simp only [regular, Set.ofPred_forall]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun (_ : j ≠ i) =>
    (isClosed_eq (continuous_apply i) (continuous_apply j)).measurableSet.compl

theorem measurable_gradient {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (i : Fin N) :
    Measurable (gradient L c n i) := by
  have hu : Continuous (Function.uncurry (fun (x : Fin N → ℝ) (t : ℝ) =>
      symmetricExtension L c n (Function.update x i t))) := by
    apply (continuous_symmetricExtension L c n).comp
    fun_prop
  have hd := (measurable_deriv_with_param hu).comp
    (measurable_id.prodMk (measurable_pi_apply i))
  exact hd.ite (measurableSet_regular i) measurable_const

theorem gradient_eq_ansatzPartial {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (i : Fin N) (x : Fin N → ℝ) (hi : regular i x) :
    gradient L c n i x = ansatzPartial c (BetheSmooth.sourceRoots L n c)
      ((Tuple.sort (α := ℝᵒᵈ) x).symm i) (decreasing x) := by
  simp only [gradient, hi, ↓reduceIte]
  exact (symmetricExtension_update_hasDerivAt L c n i x hi).deriv

theorem norm_gradient_le {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (i : Fin N) (x : Fin N → ℝ) :
    ‖gradient L c n i x‖ ≤ gradientBound c (BetheSmooth.sourceRoots L n c) := by
  classical
  by_cases hi : regular i x
  · rw [gradient_eq_ansatzPartial L c n i x hi]
    exact norm_ansatzPartial_le _ _ _ _
  · simpa [gradient, hi] using gradientBound_nonneg c (BetheSmooth.sourceRoots L n c)

/-- Ordinary (mass L^N) Lebesgue measure on the closed fundamental cube. -/
def cubeMeasure (N : ℕ) (L : ℝ) : Measure (Fin N → ℝ) :=
  volume.restrict (Icc (fun _ => 0) (fun _ => L))

instance cubeMeasure_finite (N : ℕ) (L : ℝ) : IsFiniteMeasure (cubeMeasure N L) :=
  isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne

/-- All actual chamber gradients are square integrable, with arbitrary
particle count and without an assumed H1 extension theorem. -/
theorem gradient_memLp {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (i : Fin N) :
    MemLp (gradient L c n i) 2 (cubeMeasure N L) :=
  MemLp.of_bound (measurable_gradient L c n i).aestronglyMeasurable
    (gradientBound c (BetheSmooth.sourceRoots L n c))
    (Filter.Eventually.of_forall (norm_gradient_le L c n i))

/-- A slice has finitely many exceptional values, even at simultaneous
collisions. This directly supplies the derivative used in FTC. -/
theorem slice_hasDerivAt {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (i : Fin N) (x : Fin N → ℝ) {t : ℝ} (ht : t ∉ Set.range x) :
    HasDerivAt (fun s => symmetricExtension L c n (Function.update x i s))
      (gradient L c n i (Function.update x i t)) t := by
  classical
  have hi : regular i (Function.update x i t) := by
    intro j hj he
    exact ht ⟨j, by simpa [Function.update_of_ne hj] using he.symm⟩
  have hd := symmetricExtension_update_hasDerivAt L c n i (Function.update x i t) hi
  rw [← gradient_eq_ansatzPartial L c n i (Function.update x i t) hi] at hd
  simpa only [Function.update_idem, Function.update_self] using hd

theorem gradient_slice_intervalIntegrable {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (i : Fin N) (x : Fin N → ℝ) (a b : ℝ) :
    IntervalIntegrable (fun t => gradient L c n i (Function.update x i t)) volume a b := by
  have hm : AEStronglyMeasurable (fun t => gradient L c n i (Function.update x i t)) volume :=
    ((measurable_gradient L c n i).comp (show Measurable (fun t => Function.update x i t) by
      fun_prop)).aestronglyMeasurable
  constructor <;> exact (integrable_const (gradientBound c (BetheSmooth.sourceRoots L n c))).mono'
    hm.restrict (Filter.Eventually.of_forall (fun t => norm_gradient_le L c n i _))

/-- Piecewise integration by parts on any coordinate slice. Continuity from
the proved symmetric construction cancels every internal collision trace;
FTC off the finite spectator-value set includes multiple collisions. -/
theorem symmetricExtension_slice_integrationByParts {N : ℕ} (L c : ℝ)
    (n : Fin N → ℤ) (i : Fin N) (x : Fin N → ℝ) (a b : ℝ)
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ 1 φ) :
    (∫ t in a..b, symmetricExtension L c n (Function.update x i t) * deriv φ t) =
      symmetricExtension L c n (Function.update x i b) * φ b -
      symmetricExtension L c n (Function.update x i a) * φ a -
      ∫ t in a..b, gradient L c n i (Function.update x i t) * φ t := by
  have hf : Continuous (fun t => symmetricExtension L c n (Function.update x i t)) :=
    (continuous_symmetricExtension L c n).comp (by fun_prop)
  have hg := gradient_slice_intervalIntegrable L c n i x a b
  have hi₁ := hg.mul_continuousOn hφ.continuous.continuousOn
  have hi₂ : IntervalIntegrable
      (fun t => symmetricExtension L c n (Function.update x i t) * deriv φ t) volume a b :=
    (hφ.continuous_deriv_one.intervalIntegrable a b).continuousOn_mul hf.continuousOn
  have he := integral_eq_of_hasDerivAt_off_countable
    (fun t => symmetricExtension L c n (Function.update x i t) * φ t)
    (fun t => gradient L c n i (Function.update x i t) * φ t +
      symmetricExtension L c n (Function.update x i t) * deriv φ t)
    (Set.finite_range x).countable (hf.mul hφ.continuous).continuousOn
    (fun t ht => (slice_hasDerivAt L c n i x ht.2).mul
      ((hφ.differentiable (by norm_num)) t).hasDerivAt) (hi₁.add hi₂)
  rw [intervalIntegral.integral_add hi₁ hi₂] at he
  linear_combination he

/-- The proved opposite-face identity kills the outer trace for a periodic
test function. This is the first-derivative weak identity, not the contact
(second-derivative) form identity. -/
theorem symmetricExtension_slice_weak {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    (i : Fin (N+1)) (x : Fin (N+1) → ℝ) (hx : ∀ j, x j ∈ Icc 0 L)
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ 1 φ) (hper : φ L = φ 0) :
    (∫ t in (0 : ℝ)..L, symmetricExtension L c n (Function.update x i t) * deriv φ t) =
      -(∫ t in (0 : ℝ)..L, gradient L c n i (Function.update x i t) * φ t) := by
  rw [symmetricExtension_slice_integrationByParts L c n i x 0 L φ hφ,
    symmetricExtension_update_faces hL hc hn x hx i, hper, sub_self, zero_sub]

/-- The slice weak identity applies to the constructed periodic extension
itself, including endpoints of the closed fundamental cube. -/
theorem periodicExtension_slice_weak {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    (i : Fin (N+1)) (x : Fin (N+1) → ℝ) (hx : ∀ j, x j ∈ Icc 0 L)
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ 1 φ) (hper : φ L = φ 0) :
    (∫ t in (0 : ℝ)..L, periodicExtension L c n (Function.update x i t) * deriv φ t) =
      -(∫ t in (0 : ℝ)..L, gradient L c n i (Function.update x i t) * φ t) := by
  calc
    _ = ∫ t in (0 : ℝ)..L, symmetricExtension L c n (Function.update x i t) * deriv φ t := ?_
    _ = _ := symmetricExtension_slice_weak (Fact.out : 0 < L) hc hn i x hx φ hφ hper
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc 0 L := by simpa [uIcc_of_le (Fact.out : 0 < L).le] using ht
  have he : periodicExtension L c n (Function.update x i t) =
      symmetricExtension L c n (Function.update x i t) := by
    change torusExtension L c n (fun j => (Function.update x i t j : AddCircle L)) = _
    apply torusExtension_closed_cube hc hn
    intro j
    by_cases h : j = i
    · subst j; simpa using ht'
    · simpa [Function.update_of_ne h] using hx j
  exact congrArg (fun z : ℂ => z * deriv φ t) he

theorem cubeMeasure_eq_pi (N : ℕ) (L : ℝ) :
    cubeMeasure N L = Measure.pi (fun _ : Fin N => volume.restrict (Icc (0 : ℝ) L)) := by
  rw [cubeMeasure, ← pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]

/-- Fubini in any designated coordinate, with ordinary Lebesgue mass. -/
theorem cube_integral_slice {N : ℕ} {L : ℝ} (hL : 0 ≤ L) (i : Fin (N+1))
    (f : (Fin (N+1) → ℝ) → ℂ) (hf : Integrable f (cubeMeasure (N+1) L)) :
    (∫ x, f x ∂cubeMeasure (N+1) L) =
      ∫ y, (∫ t in (0 : ℝ)..L, f (i.insertNth t y)) ∂cubeMeasure N L := by
  let μ : Measure ℝ := volume.restrict (Icc 0 L)
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => ℝ) i).symm
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => μ) i).symm
  have hi : Integrable (fun p => f (e p)) (μ.prod (Measure.pi (fun _ : Fin N => μ))) := by
    apply (hp.integrable_comp_emb e.measurableEmbedding).mpr
    simpa only [cubeMeasure_eq_pi, μ] using hf
  calc
    _ = ∫ p, f (e p) ∂μ.prod (Measure.pi (fun _ : Fin N => μ)) := by
      simpa only [cubeMeasure_eq_pi, μ] using (hp.integral_comp' f).symm
    _ = ∫ y, (∫ t, f (e (t, y)) ∂μ) ∂Measure.pi (fun _ : Fin N => μ) :=
      integral_prod_symm _ hi
    _ = _ := by
      rw [cubeMeasure_eq_pi]
      apply integral_congr_ae
      filter_upwards with y
      change (∫ t in Icc 0 L, f (i.insertNth t y)) = _
      rw [intervalIntegral.integral_of_le hL, integral_Icc_eq_integral_Ioc]

/-- Classical coordinate partial of a smooth test. -/
def testPartial {N : ℕ} (φ : (Fin N → ℝ) → ℂ) (i : Fin N) (x : Fin N → ℝ) : ℂ :=
  fderiv ℝ φ x (Pi.single i 1)

theorem continuous_testPartial {N : ℕ} {φ : (Fin N → ℝ) → ℂ}
    (hφ : ContDiff ℝ 1 φ) (i : Fin N) : Continuous (testPartial φ i) :=
  (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem testPartial_update {N : ℕ} {φ : (Fin N → ℝ) → ℂ}
    (hφ : ContDiff ℝ 1 φ) (i : Fin N) (x : Fin N → ℝ) (t : ℝ) :
    deriv (fun s => φ (Function.update x i s)) t = testPartial φ i (Function.update x i t) := by
  classical
  exact ((hφ.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_update x i t)).deriv

/-- The wavefunction itself is L2 on the compact cube. -/
theorem symmetricExtension_memLp {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) :
    MemLp (symmetricExtension L c n) 2 (cubeMeasure N L) := by
  have hf := continuous_symmetricExtension L c n
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hf).isBounded.exists_norm_le
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hC _ (Set.mem_image_of_mem _ hx)

/-- Weak first derivatives against arbitrary smooth periodic tests on the
whole cube, obtained from the actual slice derivatives by Fubini. -/
theorem symmetricExtension_cube_weak {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    (i : Fin (N+1)) (φ : (Fin (N+1) → ℝ) → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hper : ∀ x, φ (Function.update x i L) = φ (Function.update x i 0)) :
    (∫ x, symmetricExtension L c n x * testPartial φ i x ∂cubeMeasure (N+1) L) =
      -(∫ x, gradient L c n i x * φ x ∂cubeMeasure (N+1) L) := by
  classical
  have hA : Integrable (fun x => symmetricExtension L c n x * testPartial φ i x)
      (cubeMeasure (N+1) L) :=
    ((continuous_symmetricExtension L c n).mul (continuous_testPartial hφ i)).integrableOn_Icc
  have hg : IntegrableOn (gradient L c n i) (Icc (fun _ => 0) (fun _ => L)) volume :=
    (gradient_memLp L c n i).integrable (by norm_num)
  have hB : Integrable (fun x => gradient L c n i x * φ x) (cubeMeasure (N+1) L) :=
    hg.mul_continuousOn hφ.continuous.continuousOn isCompact_Icc
  rw [cube_integral_slice hL.le i _ hA, cube_integral_slice hL.le i _ hB,
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  let x : Fin (N+1) → ℝ := i.insertNth (0 : ℝ) y
  have hx : ∀ j, x j ∈ Icc 0 L := by
    refine (Fin.forall_iff_succAbove (P := fun j => x j ∈ Icc 0 L) i).mpr ?_
    constructor
    · simp [x, hL.le]
    · intro j; simpa [x] using show y j ∈ Icc 0 L from ⟨hy.1 j, hy.2 j⟩
  have htest : ContDiff ℝ 1 (fun t => φ (Function.update x i t)) :=
    hφ.comp (contDiff_update 1 x i)
  have he := symmetricExtension_slice_weak hL hc hn i x hx
    (fun t => φ (Function.update x i t)) htest (hper x)
  simp_rw [testPartial_update hφ] at he
  simpa only [Fin.update_insertNth, x] using he

/-- The constructed periodic Bethe function satisfies the cube weak identity
with the L2 gradient already proved above. No face/gluing premise remains. -/
theorem periodicExtension_cube_weak {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    (i : Fin (N+1)) (φ : (Fin (N+1) → ℝ) → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hper : ∀ x, φ (Function.update x i L) = φ (Function.update x i 0)) :
    (∫ x, periodicExtension L c n x * testPartial φ i x ∂cubeMeasure (N+1) L) =
      -(∫ x, gradient L c n i x * φ x ∂cubeMeasure (N+1) L) := by
  calc
    _ = ∫ x, symmetricExtension L c n x * testPartial φ i x ∂cubeMeasure (N+1) L := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [show periodicExtension L c n x = symmetricExtension L c n x from
        torusExtension_closed_cube hc hn x (fun j => ⟨hx.1 j, hx.2 j⟩)]
    _ = _ := symmetricExtension_cube_weak (Fact.out : 0 < L) hc hn i φ hφ hper

/-- On the source open chamber the L2 gradient is literally the derivative
of the printed finite ansatz, with the same unnormalized coefficients. -/
theorem gradient_chamber {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (i : Fin N) {x : Fin N → ℝ} (hx : x ∈ chamber N L) :
    gradient L c n i x = ansatzPartial c (BetheSmooth.sourceRoots L n c) i x := by
  have hi : regular i x := fun j hj => fun h => hj (hx.1.injective h.symm)
  rw [gradient_eq_ansatzPartial L c n i x hi, decreasing_eq hx.1.antitone]
  have hs : Tuple.sort (α := ℝᵒᵈ) x = Equiv.refl _ :=
    Tuple.sort_eq_refl_iff_monotone.mpr hx.1.antitone
  simp [hs]

theorem periodicExtension_memLp {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    MemLp (periodicExtension L c n) 2 (cubeMeasure (N+1) L) := by
  apply MemLp.ae_eq (hf_Lp := symmetricExtension_memLp L c n)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact (torusExtension_closed_cube hc hn x (fun j => ⟨hx.1 j, hx.2 j⟩)).symm

/-- A concrete periodic W^(1,2) certificate: the actual extension and all
its explicitly constructed weak coordinate derivatives lie in L2, and the
weak identity holds against every C1 periodic test. No abstract Sobolev
gluing theorem or Fourier equivalence is assumed in this certificate. -/
theorem periodicExtension_has_L2_weak_gradient {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    MemLp (periodicExtension L c n) 2 (cubeMeasure (N+1) L) ∧
      ∃ g : Fin (N+1) → (Fin (N+1) → ℝ) → ℂ,
        (∀ i, MemLp (g i) 2 (cubeMeasure (N+1) L)) ∧
        ∀ (i : Fin (N+1)) (φ : (Fin (N+1) → ℝ) → ℂ), ContDiff ℝ 1 φ →
          (∀ x, φ (Function.update x i L) = φ (Function.update x i 0)) →
          (∫ x, periodicExtension L c n x * testPartial φ i x ∂cubeMeasure (N+1) L) =
            -(∫ x, g i x * φ x ∂cubeMeasure (N+1) L) := by
  refine ⟨periodicExtension_memLp hc hn, gradient L c n, gradient_memLp L c n, ?_⟩
  intro i φ hφ hper
  exact periodicExtension_cube_weak hc hn i φ hφ hper

/-- Coordinate representatives used by the frozen torus construction. -/
def representatives {N : ℕ} (L : ℝ) [Fact (0 < L)]
    (y : Fin N → AddCircle L) : Fin N → ℝ :=
  fun j => (AddCircle.equivIco L 0 (y j) : ℝ)

theorem measurable_representatives (N : ℕ) (L : ℝ) [Fact (0 < L)] :
    Measurable (representatives (N := N) L) := by
  apply Measurable.of_eval
  intro j
  exact (measurable_subtype_coe.comp (AddCircle.measurableEquivIco L 0).measurable).comp
    (measurable_pi_apply j)

/-- A periodic gradient on the actual product torus. Values on the chosen
seam representatives have no effect on its L2 class. -/
def torusGradient {N : ℕ} (L : ℝ) [Fact (0 < L)] (c : ℝ) (n : Fin N → ℤ)
    (i : Fin N) (y : Fin N → AddCircle L) : ℂ :=
  gradient L c n i (representatives L y)

theorem measurable_torusGradient {N : ℕ} (L : ℝ) [Fact (0 < L)]
    (c : ℝ) (n : Fin N → ℤ) (i : Fin N) : Measurable (torusGradient L c n i) :=
  (measurable_gradient L c n i).comp (measurable_representatives N L)

theorem torusGradient_memLp {N : ℕ} (L : ℝ) [Fact (0 < L)]
    (c : ℝ) (n : Fin N → ℤ) (i : Fin N) :
    MemLp (torusGradient L c n i) 2 (volume : Measure (Fin N → AddCircle L)) :=
  MemLp.of_bound (measurable_torusGradient L c n i).aestronglyMeasurable
    (gradientBound c (BetheSmooth.sourceRoots L n c))
    (Filter.Eventually.of_forall (fun y => norm_gradient_le L c n i (representatives L y)))

theorem torusExtension_memLp {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    MemLp (torusExtension L c n) 2 (volume : Measure (Fin (N+1) → AddCircle L)) := by
  have hf := continuous_torusExtension (L := L) hc hn
  obtain ⟨C, hC⟩ := (isCompact_univ.image hf).isBounded.exists_norm_le
  exact MemLp.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun y => hC _ (Set.mem_image_of_mem _ (Set.mem_univ y))))

/-- The quotient cube-to-torus map preserves ordinary measure; no probability
normalization is introduced. -/
theorem cube_to_torus_measurePreserving (N : ℕ) (L : ℝ) [Fact (0 < L)] :
    MeasurePreserving (fun x : Fin N → ℝ => fun j => (x j : AddCircle L))
      (cubeMeasure N L) volume := by
  have hp : MeasurePreserving ((↑) : ℝ → AddCircle L)
      (volume.restrict (Icc (0 : ℝ) L)) volume := by
    have he : volume.restrict (Icc (0 : ℝ) L) = volume.restrict (Ioc (0 : ℝ) L) :=
      Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
    rw [he]
    simpa only [zero_add] using AddCircle.measurePreserving_mk L 0
  simpa only [cubeMeasure_eq_pi, volume_pi] using
    (measurePreserving_pi (fun _ : Fin N => volume.restrict (Icc (0 : ℝ) L))
      (fun _ : Fin N => (volume : Measure (AddCircle L))) (fun _ => hp))

/-- Representatives agree with cube coordinates almost everywhere. The only
removed sets are finitely many upper faces, proved null as hyperplanes. -/
theorem representatives_coe_ae (N : ℕ) (L : ℝ) [Fact (0 < L)] :
    (fun x : Fin N → ℝ => representatives L (fun j => (x j : AddCircle L))) =ᵐ[cubeMeasure N L]
      (fun x => x) := by
  have hne : ∀ᵐ x ∂cubeMeasure N L, ∀ j, x j ≠ L := by
    apply ae_restrict_of_ae
    rw [volume_pi]
    exact Filter.eventually_all.mpr (fun j => Measure.ae_eval_ne (fun _ : Fin N => (volume : Measure ℝ)) j L)
  filter_upwards [ae_restrict_mem measurableSet_Icc, hne] with x hx hn
  funext j
  exact AddCircle.equivIco_coe_of_mem (by
    simpa using (show x j ∈ Ico 0 L from ⟨hx.1 j, lt_of_le_of_ne (hx.2 j) (hn j)⟩))

/-- Integrals of measurable torus functions equal cube integrals of their
pullbacks under the ordinary-measure quotient. -/
theorem torus_integral_cube {N : ℕ} (L : ℝ) [Fact (0 < L)]
    (f : (Fin N → AddCircle L) → ℂ)
    (hf : AEStronglyMeasurable f (volume : Measure (Fin N → AddCircle L))) :
    (∫ y, f y) = ∫ x, f (fun j => (x j : AddCircle L)) ∂cubeMeasure N L := by
  have hp := cube_to_torus_measurePreserving N L
  calc
    _ = ∫ y, f y ∂Measure.map (fun x : Fin N → ℝ => fun j => (x j : AddCircle L))
        (cubeMeasure N L) := by rw [hp.map_eq]
    _ = _ := integral_map hp.aemeasurable (by rwa [hp.map_eq])

/-- The classical partial of a smooth torus test in its real periodic lift,
evaluated in the same representatives as the actual gradient. -/
def torusTestPartial {N : ℕ} (L : ℝ) [Fact (0 < L)]
    (φ : (Fin N → AddCircle L) → ℂ) (i : Fin N) (y : Fin N → AddCircle L) : ℂ :=
  testPartial (fun x : Fin N → ℝ => φ (fun j => (x j : AddCircle L))) i (representatives L y)

/-- Smooth test partials are L2 for ordinary product-torus measure. -/
theorem torusTestPartial_memLp {N : ℕ} (L : ℝ) [Fact (0 < L)]
    (φ : (Fin N → AddCircle L) → ℂ)
    (hs : ContDiff ℝ 1 (fun x : Fin N → ℝ => φ (fun j => (x j : AddCircle L)))) (i : Fin N) :
    MemLp (torusTestPartial L φ i) 2 (volume : Measure (Fin N → AddCircle L)) := by
  have hd := continuous_testPartial hs i
  have hm : Measurable (torusTestPartial L φ i) := hd.measurable.comp (measurable_representatives N L)
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hd).isBounded.exists_norm_le
  apply MemLp.of_bound hm.aestronglyMeasurable C
  apply Filter.Eventually.of_forall
  intro y
  have hr : representatives L y ∈ Icc (fun _ => 0) (fun _ => L) := by
    have hj (j : Fin N) : representatives L y j ∈ Ico 0 L := by
      simpa [representatives] using (AddCircle.equivIco L 0 (y j)).property
    exact ⟨fun j => (hj j).1, fun j => (hj j).2.le⟩
  exact hC _ (Set.mem_image_of_mem _ hr)

/-- The full weak first-derivative identity on the product torus itself.
The test is any continuous torus function with C1 real periodic lift. -/
theorem torusExtension_weak {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) (i : Fin (N+1))
    (φ : (Fin (N+1) → AddCircle L) → ℂ) (hφ : Continuous φ)
    (hs : ContDiff ℝ 1 (fun x : Fin (N+1) → ℝ => φ (fun j => (x j : AddCircle L)))) :
    (∫ y, torusExtension L c n y * torusTestPartial L φ i y) =
      -(∫ y, torusGradient L c n i y * φ y) := by
  let Φ := fun x : Fin (N+1) → ℝ => φ (fun j => (x j : AddCircle L))
  have hper : ∀ x, Φ (Function.update x i L) = Φ (Function.update x i 0) := by
    intro x
    apply congrArg φ
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [Function.update_of_ne h]
  have he := periodicExtension_cube_weak hc hn i Φ hs hper
  have hm : Measurable (torusTestPartial L φ i) :=
    (continuous_testPartial hs i).measurable.comp (measurable_representatives (N+1) L)
  rw [torus_integral_cube L (fun y => torusExtension L c n y * torusTestPartial L φ i y)
      ((continuous_torusExtension hc hn).measurable.mul hm).aestronglyMeasurable,
    torus_integral_cube L (fun y => torusGradient L c n i y * φ y)
      ((measurable_torusGradient L c n i).mul hφ.measurable).aestronglyMeasurable]
  have ha : (∫ x, periodicExtension L c n x *
      torusTestPartial L φ i (fun j => (x j : AddCircle L)) ∂cubeMeasure (N+1) L) =
      ∫ x, periodicExtension L c n x * testPartial Φ i x ∂cubeMeasure (N+1) L := by
    apply integral_congr_ae
    filter_upwards [representatives_coe_ae (N+1) L] with x hx
    simp only [torusTestPartial, hx, Φ]
  have hb : (∫ x, torusGradient L c n i (fun j => (x j : AddCircle L)) * Φ x
      ∂cubeMeasure (N+1) L) = ∫ x, gradient L c n i x * Φ x ∂cubeMeasure (N+1) L := by
    apply integral_congr_ae
    filter_upwards [representatives_coe_ae (N+1) L] with x hx
    simp only [torusGradient, hx]
  exact ha.trans (he.trans (congrArg Neg.neg hb.symm))

/-- Actual L2 product-torus classes ready for the separately owned Fourier
H1 characterization. This introduces no assumed equivalence. -/
def gradientLp {N : ℕ} (L : ℝ) [Fact (0 < L)] (c : ℝ) (n : Fin N → ℤ) (i : Fin N) :
    Lp ℂ 2 (volume : Measure (Fin N → AddCircle L)) :=
  (torusGradient_memLp L c n i).toLp (torusGradient L c n i)

def waveLp {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    Lp ℂ 2 (volume : Measure (Fin (N+1) → AddCircle L)) :=
  (torusExtension_memLp hc hn).toLp (torusExtension L c n)

theorem coe_gradientLp {N : ℕ} (L : ℝ) [Fact (0 < L)] (c : ℝ) (n : Fin N → ℤ) (i : Fin N) :
    (gradientLp L c n i : (Fin N → AddCircle L) → ℂ) =ᵐ[volume] torusGradient L c n i :=
  MemLp.coeFn_toLp _

theorem coe_waveLp {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    (waveLp hc hn : (Fin (N+1) → AddCircle L) → ℂ) =ᵐ[volume] torusExtension L c n :=
  MemLp.coeFn_toLp _

/-- The weak identity holds for the genuine L2 representatives as well as
the literal formulas. This is ready to consume a product Fourier theorem. -/
theorem waveLp_weak {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) (i : Fin (N+1))
    (φ : (Fin (N+1) → AddCircle L) → ℂ) (hφ : Continuous φ)
    (hs : ContDiff ℝ 1 (fun x : Fin (N+1) → ℝ => φ (fun j => (x j : AddCircle L)))) :
    (∫ y, (waveLp (L := L) hc hn : (Fin (N+1) → AddCircle L) → ℂ) y * torusTestPartial L φ i y) =
      -(∫ y, (gradientLp L c n i : (Fin (N+1) → AddCircle L) → ℂ) y * φ y) := by
  calc
    _ = ∫ y, torusExtension L c n y * torusTestPartial L φ i y := by
      apply integral_congr_ae
      filter_upwards [coe_waveLp (L := L) hc hn] with y hy
      rw [hy]
    _ = -(∫ y, torusGradient L c n i y * φ y) := torusExtension_weak hc hn i φ hφ hs
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [coe_gradientLp L c n i] with y hy
      rw [hy]

/-- The actual product-torus Bethe L2 vector has all weak coordinate
derivatives in L2. This is the direct weak H1 certificate; its identification
with the existing Fourier-defined PhysH1 carrier is a separate bridge. -/
theorem waveLp_has_L2_weak_gradient {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    ∃ g : Fin (N+1) → Lp ℂ 2 (volume : Measure (Fin (N+1) → AddCircle L)),
      ∀ (i : Fin (N+1)) (φ : (Fin (N+1) → AddCircle L) → ℂ), Continuous φ →
        ContDiff ℝ 1 (fun x : Fin (N+1) → ℝ => φ (fun j => (x j : AddCircle L))) →
        (∫ y, (waveLp (L := L) hc hn : (Fin (N+1) → AddCircle L) → ℂ) y *
          torusTestPartial L φ i y) =
          -(∫ y, (g i : (Fin (N+1) → AddCircle L) → ℂ) y * φ y) := by
  refine ⟨gradientLp L c n, ?_⟩
  intro i φ hφ hs
  exact waveLp_weak hc hn i φ hφ hs

end QuantumNLS.BetheWeakGradient

#print axioms QuantumNLS.BetheWeakGradient.ansatzPartial
#print axioms QuantumNLS.BetheWeakGradient.gradientBound
#print axioms QuantumNLS.BetheWeakGradient.gradientBound_nonneg
#print axioms QuantumNLS.BetheWeakGradient.norm_ansatzPartial_le
#print axioms QuantumNLS.BetheWeakGradient.planeWave_update_hasDerivAt
#print axioms QuantumNLS.BetheWeakGradient.coordinateAnsatz_update_hasDerivAt
#print axioms QuantumNLS.BetheWeakGradient.regular
#print axioms QuantumNLS.BetheWeakGradient.gradient
#print axioms QuantumNLS.BetheWeakGradient.eventually_antitone_update
#print axioms QuantumNLS.BetheWeakGradient.regular_permute
#print axioms QuantumNLS.BetheWeakGradient.symmetricExtension_update_hasDerivAt
#print axioms QuantumNLS.BetheWeakGradient.measurableSet_regular
#print axioms QuantumNLS.BetheWeakGradient.measurable_gradient
#print axioms QuantumNLS.BetheWeakGradient.gradient_eq_ansatzPartial
#print axioms QuantumNLS.BetheWeakGradient.norm_gradient_le
#print axioms QuantumNLS.BetheWeakGradient.cubeMeasure
#print axioms QuantumNLS.BetheWeakGradient.cubeMeasure_finite
#print axioms QuantumNLS.BetheWeakGradient.gradient_memLp
#print axioms QuantumNLS.BetheWeakGradient.slice_hasDerivAt
#print axioms QuantumNLS.BetheWeakGradient.gradient_slice_intervalIntegrable
#print axioms QuantumNLS.BetheWeakGradient.symmetricExtension_slice_integrationByParts
#print axioms QuantumNLS.BetheWeakGradient.symmetricExtension_slice_weak
#print axioms QuantumNLS.BetheWeakGradient.periodicExtension_slice_weak
#print axioms QuantumNLS.BetheWeakGradient.cubeMeasure_eq_pi
#print axioms QuantumNLS.BetheWeakGradient.cube_integral_slice
#print axioms QuantumNLS.BetheWeakGradient.testPartial
#print axioms QuantumNLS.BetheWeakGradient.continuous_testPartial
#print axioms QuantumNLS.BetheWeakGradient.testPartial_update
#print axioms QuantumNLS.BetheWeakGradient.symmetricExtension_memLp
#print axioms QuantumNLS.BetheWeakGradient.symmetricExtension_cube_weak
#print axioms QuantumNLS.BetheWeakGradient.periodicExtension_cube_weak
#print axioms QuantumNLS.BetheWeakGradient.gradient_chamber
#print axioms QuantumNLS.BetheWeakGradient.periodicExtension_memLp
#print axioms QuantumNLS.BetheWeakGradient.periodicExtension_has_L2_weak_gradient
#print axioms QuantumNLS.BetheWeakGradient.representatives
#print axioms QuantumNLS.BetheWeakGradient.measurable_representatives
#print axioms QuantumNLS.BetheWeakGradient.torusGradient
#print axioms QuantumNLS.BetheWeakGradient.measurable_torusGradient
#print axioms QuantumNLS.BetheWeakGradient.torusGradient_memLp
#print axioms QuantumNLS.BetheWeakGradient.torusExtension_memLp
#print axioms QuantumNLS.BetheWeakGradient.cube_to_torus_measurePreserving
#print axioms QuantumNLS.BetheWeakGradient.representatives_coe_ae
#print axioms QuantumNLS.BetheWeakGradient.torus_integral_cube
#print axioms QuantumNLS.BetheWeakGradient.torusTestPartial
#print axioms QuantumNLS.BetheWeakGradient.torusTestPartial_memLp
#print axioms QuantumNLS.BetheWeakGradient.torusExtension_weak
#print axioms QuantumNLS.BetheWeakGradient.gradientLp
#print axioms QuantumNLS.BetheWeakGradient.waveLp
#print axioms QuantumNLS.BetheWeakGradient.coe_gradientLp
#print axioms QuantumNLS.BetheWeakGradient.coe_waveLp
#print axioms QuantumNLS.BetheWeakGradient.waveLp_weak
#print axioms QuantumNLS.BetheWeakGradient.waveLp_has_L2_weak_gradient

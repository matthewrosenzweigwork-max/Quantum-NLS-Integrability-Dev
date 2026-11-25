import NlsGge.GK38.PairPotential
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# F5: finite-window Fourier bounds

Local prerequisites for Grébert–Kappeler Appendix D, Lemma D.2. The polynomially weighted
coefficient is truncated at time t; Parseval is used only after square integrability.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.GK38

noncomputable section

def seqWeight38 (f : ℝ → ℂ) (t : ℝ) (k : ℕ) : ℝ → ℂ :=
  Set.indicator (Set.Iic t) (fun s => (((t - 2 * s : ℝ) : ℂ) ^ k) * f s)

def seqLattice38 (f : ℝ → ℂ) (t : ℝ) (k : ℕ) (n : ℤ) : ℂ :=
  ∫ s in (0 : ℝ)..t, Complex.exp (Complex.I * (n : ℂ) * (Real.pi : ℂ) *
    ((t - 2 * s : ℝ) : ℂ)) * (((t - 2 * s : ℝ) : ℂ) ^ k) * f s

theorem seqWeight38_measurable {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (t : ℝ) (k : ℕ) : AEStronglyMeasurable (seqWeight38 f t k) volume := by
  have hp : Continuous (fun s : ℝ => (((t - 2 * s : ℝ) : ℂ) ^ k)) := by fun_prop
  exact (hp.aestronglyMeasurable.mul hf).indicator measurableSet_Iic

theorem seqWeight38_norm_le {f : ℝ → ℂ} {t s : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) : ‖seqWeight38 f t k s‖ ≤ ‖f s‖ := by
  unfold seqWeight38
  by_cases hst : s ≤ t
  · rw [Set.indicator_of_mem (show s ∈ Set.Iic t from hst), norm_mul, norm_pow, Complex.norm_real]
    have hw : |t - 2 * s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hs.1]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg _) hw) (norm_nonneg _)).trans_eq
      (one_mul _)
  · simp [Set.indicator_of_notMem (show s ∉ Set.Iic t from hst)]

theorem seqWeight38_memLp {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hfs : IntervalIntegrable (fun s => ‖f s‖ ^ 2) volume 0 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) :
    MemLp (seqWeight38 f t k) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hm : MemLp f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm hf.restrict).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hfs)
  apply hm.of_le_mul (c := 1) (seqWeight38_measurable hf t k).restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  simpa using seqWeight38_norm_le ht ⟨hs.1.le, hs.2⟩ k


/-! Phase and restriction helpers coauthored in the independent implementation replan. -/

lemma seqPhase38 (n : ℤ) (t s : ℝ) :
    Complex.exp (Complex.I * (n : ℂ) * (Real.pi : ℂ) * ((t - 2 * s : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (n : ℂ) * (Real.pi : ℂ) * (t : ℂ)) *
        Complex.exp (-(2 * Complex.I * (Real.pi : ℂ) * (n : ℂ) * (s : ℂ))) := by
  have exponent_eq :
      Complex.I * (n : ℂ) * (Real.pi : ℂ) * ((t - 2 * s : ℝ) : ℂ) =
        Complex.I * (n : ℂ) * (Real.pi : ℂ) * (t : ℂ) +
          (-(2 * Complex.I * (Real.pi : ℂ) * (n : ℂ) * (s : ℂ))) := by
    push_cast
    ring
  rw [exponent_eq, Complex.exp_add]

lemma seqWeightedPhase38 (n : ℤ) (t s : ℝ) (k : ℕ) (v : ℂ) :
    Complex.exp (Complex.I * (n : ℂ) * (Real.pi : ℂ) * ((t - 2 * s : ℝ) : ℂ)) *
        (((t - 2 * s : ℝ) : ℂ) ^ k) * v =
      Complex.exp (Complex.I * (n : ℂ) * (Real.pi : ℂ) * (t : ℂ)) *
        (Complex.exp (-(2 * Complex.I * (Real.pi : ℂ) * (n : ℂ) * (s : ℂ))) *
          (((t - 2 * s : ℝ) : ℂ) ^ k) * v) := by
  rw [seqPhase38]
  ring

lemma seqIntervalRestrict38 (g : ℝ → ℂ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..1, Set.indicator (Set.Iic t) g s) =
      ∫ s in (0 : ℝ)..t, g s := by
  exact intervalIntegral.integral_indicator (f := g) (μ := volume) ht

lemma seqFourierNegative38 (n : ℤ) (s : ℝ) :
    fourier (-n) (s : AddCircle (1 : ℝ)) =
      Complex.exp (-(2 * Complex.I * (Real.pi : ℂ) * (n : ℂ) * (s : ℂ))) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring


theorem seqLattice38_eq_fourier (f : ℝ → ℂ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) (n : ℤ) :
    seqLattice38 f t k n = Complex.exp (Complex.I * (n : ℂ) * (Real.pi : ℂ) * t) *
      fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (seqWeight38 f t k) n := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, div_one, one_smul]
  have he : (fun s : ℝ => fourier (-n) (s : AddCircle ((1 : ℝ) - 0)) • seqWeight38 f t k s) =
      Set.indicator (Set.Iic t) (fun s : ℝ =>
        Complex.exp (-(2 * Complex.I * (Real.pi : ℂ) * (n : ℂ) * s)) *
          (((t - 2 * s : ℝ) : ℂ) ^ k) * f s) := by
    funext s
    by_cases hs : s ∈ Set.Iic t
    · simp only [seqWeight38, Set.indicator_of_mem hs, smul_eq_mul]
      have hc : fourier (-n) (s : AddCircle ((1 : ℝ) - 0)) =
          Complex.exp (-(2 * Complex.I * (Real.pi : ℂ) * (n : ℂ) * (s : ℂ))) := by
        rw [fourier_coe_apply]
        congr 1
        push_cast
        ring
      rw [hc]
      ring
    · simp [seqWeight38, Set.indicator_of_notMem hs]
  rw [he, seqIntervalRestrict38 _ ht, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr (fun s _ => seqWeightedPhase38 n t s k (f s))

theorem seqLattice38_sum_sq_le {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hfs : IntervalIntegrable (fun s => ‖f s‖ ^ 2) volume 0 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) (T : Finset ℤ) :
    ∑ n ∈ T, ‖seqLattice38 f t k n‖ ^ 2 ≤ ∫ s in (0 : ℝ)..1, ‖f s‖ ^ 2 := by
  have hm := seqWeight38_memLp hf hfs ht k
  have hp := hasSum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1) hm
  have hmass : IntervalIntegrable (fun s => ‖seqWeight38 f t k s‖ ^ 2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm)
  have hnorm : ∀ n : ℤ, ‖seqLattice38 f t k n‖ =
      ‖fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (seqWeight38 f t k) n‖ := by
    intro n
    rw [seqLattice38_eq_fourier f ht, norm_mul, Complex.norm_exp]
    simp
  simp_rw [hnorm]
  have hsum := hp.summable.sum_le_tsum T (fun _ _ => sq_nonneg _)
  rw [hp.tsum_eq] at hsum
  simp only [sub_zero, inv_one, one_smul] at hsum
  refine hsum.trans (intervalIntegral.integral_mono_on zero_le_one hmass hfs ?_)
  intro s hs
  exact pow_le_pow_left₀ (norm_nonneg _) (seqWeight38_norm_le (f := f) ht hs k) 2

end

end NlsGge.GK38

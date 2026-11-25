import NlsGge.GK38.PairAsymptoticsSeqSeries

/-!
# F5: bounded perturbations of the lattice frequencies

Grébert–Kappeler Appendix D, Lemma D.2, proved locally by expanding the bounded perturbation
in the exponential. All frequency bounds are for complex perturbations.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.GK38

noncomputable section

def seqOsc38 (f : ℝ → ℂ) (z : ℂ) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..t, Complex.exp (Complex.I * z * ((t - 2 * s : ℝ) : ℂ)) * f s

theorem seqL2_intervalIntegrable {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hfs : IntervalIntegrable (fun s => ‖f s‖ ^ 2) volume 0 1) :
    IntervalIntegrable f volume 0 1 := by
  have hm : MemLp f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm hf.restrict).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hfs)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
    (hm.integrable (by norm_num))

theorem seq_norm_lattice_exp (n : ℤ) (r : ℝ) :
    ‖Complex.exp (Complex.I * (n : ℂ) * (Real.pi : ℂ) * r)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem seq_pert_coeff_norm_le {c : ℝ} (_hc : 0 ≤ c) {δ : ℂ} (hδ : ‖δ‖ ≤ c) (k : ℕ) :
    ‖(Complex.I * δ) ^ k / (k.factorial : ℂ)‖ ≤ c ^ k / (k.factorial : ℝ) := by
  rw [norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hδ k) (by positivity)

theorem seqOsc38_hasSum {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hfs : IntervalIntegrable (fun s => ‖f s‖ ^ 2) volume 0 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {c : ℝ} (hc : 0 ≤ c)
    (n : ℤ) (δ : ℂ) (hδ : ‖δ‖ ≤ c) :
    HasSum (fun k : ℕ => ((Complex.I * δ) ^ k / (k.factorial : ℂ)) * seqLattice38 f t k n)
      (seqOsc38 f ((n : ℂ) * (Real.pi : ℂ) + δ) t) := by
  let F : ℕ → ℝ → ℂ := fun k s => ((Complex.I * δ) ^ k / (k.factorial : ℂ)) *
    (Complex.exp (Complex.I * (n : ℂ) * (Real.pi : ℂ) * ((t - 2 * s : ℝ) : ℂ)) *
      (((t - 2 * s : ℝ) : ℂ) ^ k) * f s)
  let bound : ℕ → ℝ → ℝ := fun k s => (c ^ k / (k.factorial : ℝ)) * ‖f s‖
  have hw : HasSum (fun k : ℕ => c ^ k / (k.factorial : ℝ)) (Real.exp c) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp c
  have hfi := seqL2_intervalIntegrable hf hfs
  have hfit : IntervalIntegrable f volume 0 t := hfi.mono_set (by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc le_rfl ht.2)
  have hFM : ∀ k, AEStronglyMeasurable (F k) (volume.restrict (Set.uIoc 0 t)) := by
    intro k
    have hK : Continuous (fun s : ℝ => ((Complex.I * δ) ^ k / (k.factorial : ℂ)) *
        (Complex.exp (Complex.I * (n : ℂ) * (Real.pi : ℂ) * ((t - 2 * s : ℝ) : ℂ)) *
          (((t - 2 * s : ℝ) : ℂ) ^ k))) := by fun_prop
    have he : F k = fun s => (((Complex.I * δ) ^ k / (k.factorial : ℂ)) *
        (Complex.exp (Complex.I * (n : ℂ) * (Real.pi : ℂ) * ((t - 2 * s : ℝ) : ℂ)) *
          (((t - 2 * s : ℝ) : ℂ) ^ k))) * f s := by funext s; simp only [F]; ring
    rw [he]
    exact (hK.aestronglyMeasurable.mul hf).restrict
  have hb : ∀ k, ∀ᵐ s : ℝ, s ∈ Set.uIoc 0 t → ‖F k s‖ ≤ bound k s := by
    intro k
    exact Filter.Eventually.of_forall fun s hs => by
      have hs' : s ∈ Set.Ioc (0 : ℝ) t := by simpa [Set.uIoc_of_le ht.1] using hs
      have hp : |t - 2 * s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hs'.1, hs'.2]
      simp only [F, bound, norm_mul, norm_pow, seq_norm_lattice_exp, one_mul, Complex.norm_real]
      have hk := pow_le_one₀ (abs_nonneg (t - 2 * s)) hp (n := k)
      have hC := seq_pert_coeff_norm_le hc hδ k
      calc ‖(Complex.I * δ) ^ k / (k.factorial : ℂ)‖ * (|t - 2 * s| ^ k * ‖f s‖)
          ≤ (c ^ k / (k.factorial : ℝ)) * (1 * ‖f s‖) :=
            mul_le_mul hC (mul_le_mul_of_nonneg_right hk (norm_nonneg _))
              (by positivity) (by positivity)
        _ = _ := by ring
  have hbs : ∀ᵐ s : ℝ, s ∈ Set.uIoc 0 t → Summable (fun k => bound k s) :=
    Filter.Eventually.of_forall fun s _ => hw.summable.mul_right ‖f s‖
  have hbi : IntervalIntegrable (fun s => ∑' k, bound k s) volume 0 t := by
    have he : (fun s => ∑' k, bound k s) = fun s => Real.exp c * ‖f s‖ := by
      funext s
      exact (hw.mul_right ‖f s‖).tsum_eq
    rw [he]
    exact hfit.norm.const_mul _
  have hlim : ∀ᵐ s : ℝ, s ∈ Set.uIoc 0 t →
      HasSum (fun k => F k s)
        (Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ) + δ) * ((t - 2 * s : ℝ) : ℂ)) * f s) := by
    exact Filter.Eventually.of_forall fun s _ => by
      have h := (NormedSpace.expSeries_div_hasSum_exp
        (Complex.I * δ * ((t - 2 * s : ℝ) : ℂ))).mul_right
          (Complex.exp (Complex.I * (n : ℂ) * (Real.pi : ℂ) * ((t - 2 * s : ℝ) : ℂ)) * f s)
      rw [← Complex.exp_eq_exp_ℂ] at h
      have he : Complex.exp (Complex.I * δ * ((t - 2 * s : ℝ) : ℂ)) *
          (Complex.exp (Complex.I * (n : ℂ) * (Real.pi : ℂ) * ((t - 2 * s : ℝ) : ℂ)) * f s) =
          Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ) + δ) * ((t - 2 * s : ℝ) : ℂ)) * f s := by
        rw [← mul_assoc, ← Complex.exp_add]
        congr 2
        ring
      rw [he] at h
      apply h.congr_fun
      intro k
      simp only [F, mul_pow]
      ring
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence bound hFM hb hbs hbi hlim
  convert hsum using 1
  · funext k
    exact (intervalIntegral.integral_const_mul _ _).symm
  · rfl


/-- The finite-window form of Appendix D, Lemma D.2. -/
theorem seqOsc38_sum_sq_le {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hfs : IntervalIntegrable (fun s => ‖f s‖ ^ 2) volume 0 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {c : ℝ} (hc : 0 ≤ c)
    (υ : ℤ → ℂ) (hυ : ∀ n : ℤ, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c)
    (T : Finset ℤ) :
    ∑ n ∈ T, ‖seqOsc38 f (υ n) t‖ ^ 2 ≤
      Real.exp c ^ 2 * (∫ s in (0 : ℝ)..1, ‖f s‖ ^ 2) := by
  let a : ℕ → ℤ → ℂ := fun k n =>
    ((Complex.I * (υ n - (n : ℂ) * (Real.pi : ℂ))) ^ k / (k.factorial : ℂ)) *
      seqLattice38 f t k n
  let w : ℕ → ℝ := fun k => c ^ k / (k.factorial : ℝ)
  have hw : HasSum w (Real.exp c) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp c
  apply seqSeries38_sum_sq_le a (fun n => seqOsc38 f (υ n) t) w
    (∫ s in (0 : ℝ)..1, ‖f s‖ ^ 2) (Real.exp c)
    (intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _))
    (fun k => by dsimp [w]; positivity) hw ?_ ?_ T
  · intro n
    have h := seqOsc38_hasSum hf hfs ht hc n (υ n - (n : ℂ) * (Real.pi : ℂ)) (hυ n)
    have he : (n : ℂ) * (Real.pi : ℂ) + (υ n - (n : ℂ) * (Real.pi : ℂ)) = υ n := by ring
    rw [he] at h
    exact h
  · intro k S
    have hb : ∀ n : ℤ,
        ‖(Complex.I * (υ n - (n : ℂ) * (Real.pi : ℂ))) ^ k / (k.factorial : ℂ)‖ ≤ w k :=
      fun n => seq_pert_coeff_norm_le hc (hυ n) k
    calc ∑ n ∈ S, ‖a k n‖ ^ 2 = ∑ n ∈ S,
        ‖(Complex.I * (υ n - (n : ℂ) * (Real.pi : ℂ))) ^ k / (k.factorial : ℂ)‖ ^ 2 *
          ‖seqLattice38 f t k n‖ ^ 2 := by simp only [a, norm_mul, mul_pow]
      _ ≤ ∑ n ∈ S, w k ^ 2 * ‖seqLattice38 f t k n‖ ^ 2 :=
        Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (hb n) 2) (sq_nonneg _))
      _ = w k ^ 2 * ∑ n ∈ S, ‖seqLattice38 f t k n‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ w k ^ 2 * (∫ s in (0 : ℝ)..1, ‖f s‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (seqLattice38_sum_sq_le hf hfs ht k S) (sq_nonneg _)

/-- Square summability is derived after the bound on every finite window. -/
theorem seqOsc38_l2 {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hfs : IntervalIntegrable (fun s => ‖f s‖ ^ 2) volume 0 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {c : ℝ} (hc : 0 ≤ c)
    (υ : ℤ → ℂ) (hυ : ∀ n : ℤ, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c) :
    Summable (fun n : ℤ => ‖seqOsc38 f (υ n) t‖ ^ 2) ∧
      ∑' n : ℤ, ‖seqOsc38 f (υ n) t‖ ^ 2 ≤
        Real.exp c ^ 2 * (∫ s in (0 : ℝ)..1, ‖f s‖ ^ 2) := by
  have hb := seqOsc38_sum_sq_le hf hfs ht hc υ hυ
  have hs := summable_of_sum_le (fun n : ℤ => sq_nonneg (‖seqOsc38 f (υ n) t‖)) hb
  exact ⟨hs, hs.tsum_le_of_sum_le hb⟩

/-- The same bound for the negative frequencies, by reflecting the spectral index. -/
theorem seqOsc38_neg_sum_sq_le {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hfs : IntervalIntegrable (fun s => ‖f s‖ ^ 2) volume 0 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) {c : ℝ} (hc : 0 ≤ c)
    (υ : ℤ → ℂ) (hυ : ∀ n : ℤ, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c)
    (T : Finset ℤ) :
    ∑ n ∈ T, ‖seqOsc38 f (-υ n) t‖ ^ 2 ≤
      Real.exp c ^ 2 * (∫ s in (0 : ℝ)..1, ‖f s‖ ^ 2) := by
  have hv : ∀ n : ℤ, ‖(-υ (-n)) - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c := by
    intro n
    have he : (-υ (-n)) - (n : ℂ) * (Real.pi : ℂ) =
        -(υ (-n) - ((-n : ℤ) : ℂ) * (Real.pi : ℂ)) := by push_cast; ring
    rw [he, norm_neg]
    exact hυ (-n)
  have h := seqOsc38_sum_sq_le hf hfs ht hc (fun n => -υ (-n)) hv
    (T.map (Equiv.neg ℤ).toEmbedding)
  rw [Finset.sum_map] at h
  simpa only [Equiv.toEmbedding_apply, Equiv.neg_apply, neg_neg] using h

end

end NlsGge.GK38

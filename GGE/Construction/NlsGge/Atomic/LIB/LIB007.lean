import NlsGge.NLS38.SeqConv38a
import NlsGge.Atomic.LIB.LIB001

set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace NlsGge.Atomic.LIB007

/-- Absolute convergence of each actual coefficient sum. -/
private theorem convolution_l1_l2_coefficient_summable {f g : ℤ → ℂ}
    (hf : NlsGge.NLS38.IsL1 f)
    (hg : Summable (fun n : ℤ => ‖g n‖ ^ 2)) (n : ℤ) :
    Summable (fun k : ℤ => f k * g (n - k)) :=
  NlsGge.NLS38.summable_conv_term_l2 hf hg n

/-- The actual complex discrete convolution belongs to ℓ² and obeys Young's bound. -/
theorem convolution_l1_l2_bound {f g : ℤ → ℂ}
    (hf : NlsGge.NLS38.IsL1 f)
    (hg : Summable (fun n : ℤ => ‖g n‖ ^ 2)) :
    Summable (fun n : ℤ => ‖NlsGge.NLS38.conv f g n‖ ^ 2) ∧
      Real.sqrt (∑' n : ℤ, ‖NlsGge.NLS38.conv f g n‖ ^ 2) ≤
        NlsGge.NLS38.l1 f * Real.sqrt (∑' n : ℤ, ‖g n‖ ^ 2) := by
  obtain ⟨hout, hsq⟩ := NlsGge.NLS38.summable_sq_conv hf hg
  have hnorm : 0 ≤ NlsGge.NLS38.l1 f := by
    unfold NlsGge.NLS38.l1
    exact tsum_nonneg (fun n => norm_nonneg _)
  refine ⟨hout, ?_⟩
  calc
    Real.sqrt (∑' n : ℤ, ‖NlsGge.NLS38.conv f g n‖ ^ 2) ≤
        Real.sqrt ((NlsGge.NLS38.l1 f) ^ 2 * ∑' n : ℤ, ‖g n‖ ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = NlsGge.NLS38.l1 f * Real.sqrt (∑' n : ℤ, ‖g n‖ ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hnorm]

def translate (r : ℤ) (f : ℤ → ℂ) : ℤ → ℂ := fun n => f (n - r)

def reflect (f : ℤ → ℂ) : ℤ → ℂ := fun n => f (-n)

theorem l1_translate (r : ℤ) (f : ℤ → ℂ) :
    NlsGge.NLS38.IsL1 (translate r f) ↔ NlsGge.NLS38.IsL1 f := by
  unfold NlsGge.NLS38.IsL1 translate
  exact (Equiv.addRight (-r)).summable_iff (f := fun n : ℤ => ‖f n‖)

theorem square_summable_translate (r : ℤ) (f : ℤ → ℂ) :
    Summable (fun n : ℤ => ‖translate r f n‖ ^ 2) ↔
      Summable (fun n : ℤ => ‖f n‖ ^ 2) := by
  unfold translate
  exact (Equiv.addRight (-r)).summable_iff (f := fun n : ℤ => ‖f n‖ ^ 2)

theorem l1_translate_tsum_eq (r : ℤ) (f : ℤ → ℂ) :
    NlsGge.NLS38.l1 (translate r f) = NlsGge.NLS38.l1 f := by
  unfold NlsGge.NLS38.l1 translate
  exact (Equiv.addRight (-r)).tsum_eq (fun n : ℤ => ‖f n‖)

theorem square_tsum_translate_eq (r : ℤ) (f : ℤ → ℂ) :
    (∑' n : ℤ, ‖translate r f n‖ ^ 2) = ∑' n : ℤ, ‖f n‖ ^ 2 := by
  unfold translate
  exact (Equiv.addRight (-r)).tsum_eq (fun n : ℤ => ‖f n‖ ^ 2)

theorem conv_translate (r s : ℤ) (f g : ℤ → ℂ) :
    NlsGge.NLS38.conv (translate r f) (translate s g) =
      translate (r + s) (NlsGge.NLS38.conv f g) := by
  funext n
  unfold NlsGge.NLS38.conv translate
  rw [← (Equiv.addRight r).tsum_eq
    (fun a : ℤ => f (a - r) * g (n - a - s))]
  refine tsum_congr fun a => ?_
  rw [show (Equiv.addRight r) a = a + r by rfl]
  congr 2 <;> omega

theorem l1_reflect (f : ℤ → ℂ) :
    NlsGge.NLS38.IsL1 (reflect f) ↔ NlsGge.NLS38.IsL1 f := by
  unfold NlsGge.NLS38.IsL1 reflect
  exact (Equiv.neg ℤ).summable_iff (f := fun n : ℤ => ‖f n‖)

theorem square_summable_reflect (f : ℤ → ℂ) :
    Summable (fun n : ℤ => ‖reflect f n‖ ^ 2) ↔
      Summable (fun n : ℤ => ‖f n‖ ^ 2) := by
  unfold reflect
  exact (Equiv.neg ℤ).summable_iff (f := fun n : ℤ => ‖f n‖ ^ 2)

theorem l1_reflect_tsum_eq (f : ℤ → ℂ) :
    NlsGge.NLS38.l1 (reflect f) = NlsGge.NLS38.l1 f := by
  unfold NlsGge.NLS38.l1 reflect
  exact (Equiv.neg ℤ).tsum_eq (fun n : ℤ => ‖f n‖)

theorem square_tsum_reflect_eq (f : ℤ → ℂ) :
    (∑' n : ℤ, ‖reflect f n‖ ^ 2) = ∑' n : ℤ, ‖f n‖ ^ 2 := by
  unfold reflect
  exact (Equiv.neg ℤ).tsum_eq (fun n : ℤ => ‖f n‖ ^ 2)

theorem conv_reflect (f g : ℤ → ℂ) :
    NlsGge.NLS38.conv (reflect f) (reflect g) =
      reflect (NlsGge.NLS38.conv f g) := by
  funext n
  unfold NlsGge.NLS38.conv reflect
  simp only [neg_sub]
  have hterm : ∀ a : ℤ,
      f (-a) * g (a - n) = (fun k : ℤ => f k * g (-n - k)) (-a) := by
    intro a
    congr 2 <;> omega
  rw [tsum_congr hterm]
  exact (Equiv.neg ℤ).tsum_eq (fun k : ℤ => f k * g (-n - k))

/-- The raw ℓ¹-by-ℓ² theorem on the actual `ℤ → ℂ` carrier, with input and
output membership stated in mathlib's genuine `Memℓp` predicates. -/
theorem convolution_memLp_one_two {f g : ℤ → ℂ}
    (hf : Memℓp f (1 : ℝ≥0∞)) (hg : Memℓp g (2 : ℝ≥0∞)) :
    Memℓp (fun n : ℤ => NlsGge.NLS38.conv f g n) (2 : ℝ≥0∞) ∧
      Real.sqrt (∑' n : ℤ, ‖NlsGge.NLS38.conv f g n‖ ^ 2) ≤
        NlsGge.NLS38.l1 f * Real.sqrt (∑' n : ℤ, ‖g n‖ ^ 2) := by
  have hfL1 : NlsGge.NLS38.IsL1 f := by
    unfold NlsGge.NLS38.IsL1
    simpa using hf.summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  have hg2 : Summable (fun n : ℤ => ‖g n‖ ^ 2) := by
    simpa using hg.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have h := convolution_l1_l2_bound hfL1 hg2
  refine ⟨?_, h.2⟩
  exact memℓp_gen (by simpa using h.1)

/-- Simultaneously translate both sequence inputs. The transformed output is
in genuine `ℓ²`; its bound keeps the original, untranslated `ℓ¹` and `ℓ²`
quantities and constant one. -/
theorem convolution_memLp_one_two_translate {f g : ℤ → ℂ}
    (r s : ℤ) (hf : Memℓp f (1 : ℝ≥0∞)) (hg : Memℓp g (2 : ℝ≥0∞)) :
    Memℓp (fun n : ℤ => NlsGge.NLS38.conv (translate r f) (translate s g) n)
        (2 : ℝ≥0∞) ∧
      Real.sqrt (∑' n : ℤ,
        ‖NlsGge.NLS38.conv (translate r f) (translate s g) n‖ ^ 2) ≤
        NlsGge.NLS38.l1 f * Real.sqrt (∑' n : ℤ, ‖g n‖ ^ 2) := by
  have hfL1 : NlsGge.NLS38.IsL1 f := by
    unfold NlsGge.NLS38.IsL1
    simpa using hf.summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  have hg2 : Summable (fun n : ℤ => ‖g n‖ ^ 2) := by
    simpa using hg.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hfT : NlsGge.NLS38.IsL1 (translate r f) := (l1_translate r f).2 hfL1
  have hgT : Summable (fun n : ℤ => ‖translate s g n‖ ^ 2) :=
    (square_summable_translate s g).2 hg2
  have h := convolution_l1_l2_bound hfT hgT
  refine ⟨memℓp_gen (by simpa using h.1), ?_⟩
  calc
    Real.sqrt (∑' n : ℤ,
        ‖NlsGge.NLS38.conv (translate r f) (translate s g) n‖ ^ 2) ≤
        NlsGge.NLS38.l1 (translate r f) *
          Real.sqrt (∑' n : ℤ, ‖translate s g n‖ ^ 2) := h.2
    _ = NlsGge.NLS38.l1 f * Real.sqrt (∑' n : ℤ, ‖g n‖ ^ 2) := by
      rw [l1_translate_tsum_eq, square_tsum_translate_eq]

/-- Simultaneously reflect both sequence inputs across zero. The bound again
uses exactly the original norms and constant one. -/
theorem convolution_memLp_one_two_reflect {f g : ℤ → ℂ}
    (hf : Memℓp f (1 : ℝ≥0∞)) (hg : Memℓp g (2 : ℝ≥0∞)) :
    Memℓp (fun n : ℤ => NlsGge.NLS38.conv (reflect f) (reflect g) n)
        (2 : ℝ≥0∞) ∧
      Real.sqrt (∑' n : ℤ,
        ‖NlsGge.NLS38.conv (reflect f) (reflect g) n‖ ^ 2) ≤
        NlsGge.NLS38.l1 f * Real.sqrt (∑' n : ℤ, ‖g n‖ ^ 2) := by
  have hfL1 : NlsGge.NLS38.IsL1 f := by
    unfold NlsGge.NLS38.IsL1
    simpa using hf.summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  have hg2 : Summable (fun n : ℤ => ‖g n‖ ^ 2) := by
    simpa using hg.summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hfR : NlsGge.NLS38.IsL1 (reflect f) := (l1_reflect f).2 hfL1
  have hgR : Summable (fun n : ℤ => ‖reflect g n‖ ^ 2) :=
    (square_summable_reflect g).2 hg2
  have h := convolution_l1_l2_bound hfR hgR
  refine ⟨memℓp_gen (by simpa using h.1), ?_⟩
  calc
    Real.sqrt (∑' n : ℤ,
        ‖NlsGge.NLS38.conv (reflect f) (reflect g) n‖ ^ 2) ≤
        NlsGge.NLS38.l1 (reflect f) *
          Real.sqrt (∑' n : ℤ, ‖reflect g n‖ ^ 2) := h.2
    _ = NlsGge.NLS38.l1 f * Real.sqrt (∑' n : ℤ, ‖g n‖ ^ 2) := by
      rw [l1_reflect_tsum_eq, square_tsum_reflect_eq]


/-- The genuine period-one Fourier coefficients of a physical L² class form
an actual `ℓ²` sequence with the norm of that class. -/
private theorem periodOneFourierL2_norm_sq (u : NlsGge.Pilot.PhysicalL2) :
    ‖NlsGge.Atomic.LIB001.periodOneFourierL2 u‖ ^ 2 =
      ∑' n : ℤ, ‖NlsGge.Atomic.LIB001.periodOneFourierL2 u n‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
      (NlsGge.Atomic.LIB001.periodOneFourierL2 u))

/-- The generic sequence estimate with its ℓ² input taken from the actual
period-one Fourier isometry on `PhysicalL2`; the output is genuine `ℓ²` and
the constant remains one in the actual Fourier-space norm. -/
theorem convolution_l1_periodOneFourierL2_bound {a : ℤ → ℂ}
    (ha : NlsGge.NLS38.IsL1 a) (u : NlsGge.Pilot.PhysicalL2) :
    Memℓp (fun n : ℤ => NlsGge.NLS38.conv a
      (NlsGge.Atomic.LIB001.periodOneFourierL2 u) n) (2 : ℝ≥0∞) ∧
      Real.sqrt (∑' n : ℤ, ‖NlsGge.NLS38.conv a
        (NlsGge.Atomic.LIB001.periodOneFourierL2 u) n‖ ^ 2) ≤
        NlsGge.NLS38.l1 a * ‖NlsGge.Atomic.LIB001.periodOneFourierL2 u‖ := by
  have hb : Summable (fun n : ℤ =>
      ‖NlsGge.Atomic.LIB001.periodOneFourierL2 u n‖ ^ 2) := by
    have h := (lp.memℓp (NlsGge.Atomic.LIB001.periodOneFourierL2 u)).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa using h
  have h := convolution_l1_l2_bound ha hb
  refine ⟨memℓp_gen (by simpa using h.1), ?_⟩
  calc
    Real.sqrt (∑' n : ℤ, ‖NlsGge.NLS38.conv a
        (NlsGge.Atomic.LIB001.periodOneFourierL2 u) n‖ ^ 2) ≤
        NlsGge.NLS38.l1 a *
          Real.sqrt (∑' n : ℤ,
            ‖NlsGge.Atomic.LIB001.periodOneFourierL2 u n‖ ^ 2) := h.2
    _ = NlsGge.NLS38.l1 a * ‖NlsGge.Atomic.LIB001.periodOneFourierL2 u‖ := by
      rw [← periodOneFourierL2_norm_sq]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

end NlsGge.Atomic.LIB007

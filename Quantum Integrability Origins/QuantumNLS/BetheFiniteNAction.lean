import QuantumNLS.BethePhysicalTransfer
import QuantumNLS.BetheH1
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Literal finite-particle ordered-kernel action before imposing Bethe equations.
The source coordinates decrease. For fixed output x in the strict chamber,
each alternating input chamber is a product of adjacent open intervals.
The endpoint products below retain all off-shell boundary terms.
Source: periodic_basis.tex:316–333, Vlaar (2.4.1)–(2.4.4).
The full placement sum and interacting transfer eigenrelation remain open. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate InnerProductSpace
set_option maxHeartbeats 2000000

namespace QuantumNLS.BetheFiniteNAction
open BetheTransferKernelAdjoint BetheTransferOperators BetheWeakGradient
open BetheWavefunctions BetheExtension

variable {m : ℕ}

/-- The next lower output coordinate, with the physical boundary zero. -/
def lower (x : Fin m → ℝ) (i : Fin m) : ℝ :=
  if h : i.val + 1 < m then x ⟨i.val+1, h⟩ else 0

/-- The preceding upper output coordinate, with the physical boundary L. -/
def upper (L : ℝ) (x : Fin m → ℝ) (i : Fin m) : ℝ :=
  if h : 0 < i.val then x ⟨i.val-1, by omega⟩ else L

theorem lower_bounds {L : ℝ} {x : Fin m → ℝ} (hx : x ∈ chamber m L) (i : Fin m) :
    0 ≤ lower x i ∧ lower x i < x i := by
  unfold lower
  split_ifs with h
  · exact ⟨(hx.2 _).1.le, hx.1 (by change i.val < i.val+1; omega)⟩
  · exact ⟨le_rfl, (hx.2 i).1⟩

theorem upper_bounds {L : ℝ} {x : Fin m → ℝ} (hx : x ∈ chamber m L) (i : Fin m) :
    x i < upper L x i ∧ upper L x i ≤ L := by
  unfold upper
  split_ifs with h
  · exact ⟨hx.1 (by change i.val-1 < i.val; omega), (hx.2 _).2.le⟩
  · exact ⟨(hx.2 i).2, le_rfl⟩

/-- The printed upper alternating chain is exactly its adjacent rectangle. -/
theorem plusOrder_box {L : ℝ} {x : Fin m → ℝ} (hx : x ∈ chamber m L)
    (y : Fin m → ℝ) :
    PlusOrder L x y ↔ ∀ i, y i ∈ Ioo (lower x i) (x i) := by
  constructor
  · intro h i
    refine ⟨?_, (h.1 i).2.1⟩
    unfold lower
    split_ifs with hi
    · exact h.2 i ⟨i.val+1, hi⟩ (by exact Nat.lt_succ_self i.val)
    · exact (h.1 i).1
  · intro h
    constructor
    · intro i
      exact ⟨(lower_bounds hx i).1.trans_lt (h i).1, (h i).2, (hx.2 i).2⟩
    · intro i j hij
      have hi : i.val+1 < m := by have := j.isLt; change i.val < j.val at hij; omega
      have hj : x j ≤ lower x i := by
        simp only [lower, dite_eq_left hi]
        apply hx.1.antitone
        change i.val+1 ≤ j.val
        change i.val < j.val at hij
        omega
      exact hj.trans_lt (h i).1

/-- The lower branch retains the upper boundary L, including its full phase. -/
theorem minusOrder_box {L : ℝ} {x : Fin m → ℝ} (hx : x ∈ chamber m L)
    (y : Fin m → ℝ) :
    MinusOrder L x y ↔ ∀ i, y i ∈ Ioo (x i) (upper L x i) := by
  constructor
  · intro h i
    refine ⟨(h.1 i).2.1, ?_⟩
    unfold upper
    split_ifs with hi
    · exact h.2 ⟨i.val-1, by omega⟩ i (by change i.val-1 < i.val; omega)
    · exact (h.1 i).2.2
  · intro h
    constructor
    · intro i
      exact ⟨(hx.2 i).1, (h i).1, (h i).2.trans_le (upper_bounds hx i).2⟩
    · intro i j hij
      have hj : 0 < j.val := by change i.val < j.val at hij; omega
      have hi : upper L x j ≤ x i := by
        simp only [upper, dite_eq_left hj]
        apply hx.1.antitone
        change i.val ≤ j.val-1
        change i.val < j.val at hij
        omega
      exact (h j).2.trans_le hi

/-- An input in either literal alternating chamber is already decreasing. -/
theorem plusOrder_input_strictAnti {L : ℝ} {x y : Fin m → ℝ}
    (h : PlusOrder L x y) : StrictAnti y := by
  intro i j hij
  exact ((h.1 j).2.1).trans (h.2 i j hij)

theorem minusOrder_input_strictAnti {L : ℝ} {x y : Fin m → ℝ}
    (h : MinusOrder L x y) : StrictAnti y := by
  intro i j hij
  exact (h.2 i j hij).trans (h.1 i).2.1

/-- A single exact endpoint difference; no on-shell cancellation is applied. -/
def endpoint (z : ℂ) (q a b : ℝ) : ℂ :=
  (Complex.exp (Complex.I * ((q : ℂ)-z) * b) -
    Complex.exp (Complex.I * ((q : ℂ)-z) * a)) / (Complex.I * ((q : ℂ)-z))

theorem interval_endpoint {L a b q : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L)
    {z : ℂ} (hz : z ≠ (q : ℂ)) :
    (∫ t in Icc 0 L, (Ioo a b).indicator
      (fun t => Complex.exp (Complex.I * ((q : ℂ)-z) * t)) t) = endpoint z q a b := by
  rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
  have hs : Ioo a b ∩ Icc 0 L = Ioo a b := inter_eq_left.mpr
    (fun t ht => ⟨ha.trans ht.1.le, ht.2.le.trans hb⟩)
  rw [hs, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
    integral_exp_mul_complex (mul_ne_zero Complex.I_ne_zero (sub_ne_zero.mpr hz.symm))]
  rfl

theorem planeWave_prod (q y : Fin m → ℝ) :
    planeWave q y = ∏ i, Complex.exp (Complex.I * (q i : ℂ) * y i) := by
  rw [planeWave, ← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, mul_assoc]

theorem phase_prod (z : ℂ) (x : Fin m → ℝ) :
    Complex.exp (Complex.I*z*(∑ i, x i : ℝ)) =
      ∏ i, Complex.exp (Complex.I*z*x i) := by
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_sum, Finset.mul_sum]

/-- Factor the actual upper kernel integrand, not a supplied action formula. -/
theorem plus_integrand {L : ℝ} {x : Fin m → ℝ} (hx : x ∈ chamber m L)
    (q y : Fin m → ℝ) (z : ℂ) :
    rawPlus L z x y * planeWave q y =
      Complex.exp (Complex.I*z*(∑ i, x i : ℝ)) *
        ∏ i, (Ioo (lower x i) (x i)).indicator
          (fun t => Complex.exp (Complex.I*((q i : ℂ)-z)*t)) (y i) := by
  classical
  by_cases h : PlusOrder L x y
  · have hb := (plusOrder_box hx y).mp h
    simp only [rawPlus, ite_eq_left h, indicator_of_mem (hb _), planeWave,
      ← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    simp only [displacement, Complex.ofReal_sum, Complex.ofReal_sub, Complex.ofReal_mul,
      Finset.mul_sum, Finset.sum_sub_distrib, mul_sub, sub_mul, mul_assoc]
    ring
  · have hb : ∃ i, y i ∉ Ioo (lower x i) (x i) := by
      simpa only [not_forall] using (mt (plusOrder_box hx y).mpr h)
    obtain ⟨i, hi⟩ := hb
    simp only [rawPlus, ite_eq_right h, zero_mul]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _), mul_zero]

/-- Exact factorization of the lower branch, including exp(izL). -/
theorem minus_integrand {L : ℝ} {x : Fin m → ℝ} (hx : x ∈ chamber m L)
    (q y : Fin m → ℝ) (z : ℂ) :
    rawMinus L z x y * planeWave q y =
      Complex.exp (Complex.I*z*L + Complex.I*z*(∑ i, x i : ℝ)) *
        ∏ i, (Ioo (x i) (upper L x i)).indicator
          (fun t => Complex.exp (Complex.I*((q i : ℂ)-z)*t)) (y i) := by
  classical
  by_cases h : MinusOrder L x y
  · have hb := (minusOrder_box hx y).mp h
    simp only [rawMinus, ite_eq_left h, indicator_of_mem (hb _), planeWave,
      ← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_sum, Complex.ofReal_sub, Complex.ofReal_mul,
      Finset.mul_sum, Finset.sum_sub_distrib, mul_sub, sub_mul, mul_assoc]
    ring
  · have hb : ∃ i, y i ∉ Ioo (x i) (upper L x i) := by
      simpa only [not_forall] using (mt (minusOrder_box hx y).mpr h)
    obtain ⟨i, hi⟩ := hb
    simp only [rawMinus, ite_eq_right h, zero_mul]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _), mul_zero]

/-- Computed upper action on every finite-particle plane wave. -/
theorem rawPlus_planeWave {L : ℝ} {x : Fin m → ℝ} (hx : x ∈ chamber m L)
    (q : Fin m → ℝ) {z : ℂ} (hz : ∀ i, z ≠ (q i : ℂ)) :
    (∫ y, rawPlus L z x y * planeWave q y ∂cubeMeasure m L) =
      Complex.exp (Complex.I*z*(∑ i, x i : ℝ)) *
        ∏ i, endpoint z (q i) (lower x i) (x i) := by
  simp_rw [plus_integrand hx q _ z]
  rw [integral_const_mul, cubeMeasure_eq_pi, integral_fin_nat_prod_eq_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact interval_endpoint (lower_bounds hx i).1 (lower_bounds hx i).2.le (hx.2 i).2.le (hz i)

/-- Computed lower action, retaining the full interval phase and endpoints. -/
theorem rawMinus_planeWave {L : ℝ} {x : Fin m → ℝ} (hx : x ∈ chamber m L)
    (q : Fin m → ℝ) {z : ℂ} (hz : ∀ i, z ≠ (q i : ℂ)) :
    (∫ y, rawMinus L z x y * planeWave q y ∂cubeMeasure m L) =
      Complex.exp (Complex.I*z*L + Complex.I*z*(∑ i, x i : ℝ)) *
        ∏ i, endpoint z (q i) (x i) (upper L x i) := by
  simp_rw [minus_integrand hx q _ z]
  rw [integral_const_mul, cubeMeasure_eq_pi, integral_fin_nat_prod_eq_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact interval_endpoint (hx.2 i).1.le (upper_bounds hx i).1.le (upper_bounds hx i).2 (hz i)

/-- The evaluated endpoint product for the upper physical integral. -/
def plusValue (q x : Fin m → ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I*z*(∑ i, x i : ℝ)) *
    ∏ i, endpoint z (q i) (lower x i) (x i)

/-- The evaluated endpoint product for the lower physical integral. -/
def minusValue (L : ℝ) (q x : Fin m → ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I*z*L + Complex.I*z*(∑ i, x i : ℝ)) *
    ∏ i, endpoint z (q i) (x i) (upper L x i)

theorem integrable_plus_planeWave {L : ℝ} (hL : 0 ≤ L)
    (x q : Fin m → ℝ) (z : ℂ) :
    Integrable (fun y => rawPlus L z x y * planeWave q y) (cubeMeasure m L) := by
  have hm : Measurable (fun y => rawPlus L z x y * planeWave q y) := by
    apply Measurable.mul
    · exact (measurable_rawPlus m L z).comp (measurable_const.prodMk measurable_id)
    · unfold planeWave; fun_prop
  apply (integrable_const (Real.exp (L * |z.im|))).mono' hm.aestronglyMeasurable
  filter_upwards with y
  rw [norm_mul, planeWave_norm, mul_one]
  exact norm_rawPlus_le L hL z x y

theorem integrable_minus_planeWave {L : ℝ} (hL : 0 ≤ L)
    (x q : Fin m → ℝ) (z : ℂ) :
    Integrable (fun y => rawMinus L z x y * planeWave q y) (cubeMeasure m L) := by
  have hm : Measurable (fun y => rawMinus L z x y * planeWave q y) := by
    apply Measurable.mul
    · exact (measurable_rawMinus m L z).comp (measurable_const.prodMk measurable_id)
    · unfold planeWave; fun_prop
  apply (integrable_const (Real.exp (L * |z.im|))).mono' hm.aestronglyMeasurable
  filter_upwards with y
  rw [norm_mul, planeWave_norm, mul_one]
  exact norm_rawMinus_le L hL z x y

/-- The complete permutation sum is integrated, with every scattering factor. -/
theorem rawPlus_coordinateAnsatz {L : ℝ} (hL : 0 ≤ L) {x : Fin m → ℝ}
    (hx : x ∈ chamber m L) (c : ℝ) (q : Fin m → ℝ) {z : ℂ}
    (hz : ∀ i, z ≠ (q i : ℂ)) :
    (∫ y, rawPlus L z x y * coordinateAnsatz c q y ∂cubeMeasure m L) =
      ∑ σ : Equiv.Perm (Fin m), coefficient c (q ∘ σ) * plusValue (q ∘ σ) x z := by
  classical
  calc
    _ = ∫ y, ∑ σ : Equiv.Perm (Fin m), coefficient c (q ∘ σ) *
        (rawPlus L z x y * planeWave (q ∘ σ) y) ∂cubeMeasure m L := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [coordinateAnsatz, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      ring
    _ = _ := by
      rw [integral_finsetSum _ (fun (σ : Equiv.Perm (Fin m)) _ =>
        (integrable_plus_planeWave hL x (q ∘ σ) z).const_mul (coefficient c (q ∘ σ)))]
      apply Finset.sum_congr rfl
      intro σ _
      rw [integral_const_mul, rawPlus_planeWave hx (q ∘ σ) (fun i => hz (σ i))]
      rfl

theorem rawMinus_coordinateAnsatz {L : ℝ} (hL : 0 ≤ L) {x : Fin m → ℝ}
    (hx : x ∈ chamber m L) (c : ℝ) (q : Fin m → ℝ) {z : ℂ}
    (hz : ∀ i, z ≠ (q i : ℂ)) :
    (∫ y, rawMinus L z x y * coordinateAnsatz c q y ∂cubeMeasure m L) =
      ∑ σ : Equiv.Perm (Fin m), coefficient c (q ∘ σ) * minusValue L (q ∘ σ) x z := by
  classical
  calc
    _ = ∫ y, ∑ σ : Equiv.Perm (Fin m), coefficient c (q ∘ σ) *
        (rawMinus L z x y * planeWave (q ∘ σ) y) ∂cubeMeasure m L := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [coordinateAnsatz, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      ring
    _ = _ := by
      rw [integral_finsetSum _ (fun (σ : Equiv.Perm (Fin m)) _ =>
        (integrable_minus_planeWave hL x (q ∘ σ) z).const_mul (coefficient c (q ∘ σ)))]
      apply Finset.sum_congr rfl
      intro σ _
      rw [integral_const_mul, rawMinus_planeWave hx (q ∘ σ) (fun i => hz (σ i))]
      rfl

/-- On its support the actual kernel sees the original chamber wave. -/
theorem rawPlus_symmetricExtension (L c : ℝ) (n : Fin m → ℤ)
    (x y : Fin m → ℝ) (z : ℂ) :
    rawPlus L z x y * symmetricExtension L c n y =
      rawPlus L z x y * coordinateAnsatz c (BetheSmooth.sourceRoots L n c) y := by
  classical
  by_cases h : PlusOrder L x y
  · rw [symmetricExtension_eq L c n (plusOrder_input_strictAnti h).antitone]
    rfl
  · simp only [rawPlus, ite_eq_right h, zero_mul]

theorem rawMinus_symmetricExtension (L c : ℝ) (n : Fin m → ℤ)
    (x y : Fin m → ℝ) (z : ℂ) :
    rawMinus L z x y * symmetricExtension L c n y =
      rawMinus L z x y * coordinateAnsatz c (BetheSmooth.sourceRoots L n c) y := by
  classical
  by_cases h : MinusOrder L x y
  · rw [symmetricExtension_eq L c n (minusOrder_input_strictAnti h).antitone]
    rfl
  · simp only [rawMinus, ite_eq_right h, zero_mul]

/-- Ordinary physical torus measure becomes the cube measure of mass L^m. -/
theorem integral_representatives (L : ℝ) [Fact (0 < L)]
    (f : (Fin m → ℝ) → ℂ) (hf : Measurable f) :
    (∫ y, f (representatives L y) ∂PhysicalTensor.torusPiMeasure L m) =
      ∫ y, f y ∂cubeMeasure m L := by
  have hm := hf.comp (measurable_representatives m L)
  simp only [PhysicalTensor.torusPiMeasure]
  rw [← volume_pi, torus_integral_cube L (fun y => f (representatives L y))
    hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [representatives_coe_ae m L] with y hy
  rw [hy]

/-- Actual upper bounded-kernel integral on the constructed physical Bethe wave. -/
theorem plusKernel_sourceWave_integral (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    (x : Fin (N+1) → AddCircle L) {z : ℂ}
    (hx : representatives L x ∈ chamber (N+1) L)
    (hz : ∀ i, z ≠ (BetheSmooth.sourceRoots L n c i : ℂ)) :
    (∫ y, (plusKernel L (N+1) z).fn (x,y) * BetheH1.wave (L := L) hc hn y
      ∂PhysicalTensor.torusPiMeasure L (N+1)) =
      ∑ σ : Equiv.Perm (Fin (N+1)),
        coefficient c (BetheSmooth.sourceRoots L n c ∘ σ) *
          plusValue (BetheSmooth.sourceRoots L n c ∘ σ) (representatives L x) z := by
  have hm : Measurable (fun y => rawPlus L z (representatives L x) y *
      symmetricExtension L c n y) := by
    exact ((measurable_rawPlus (N+1) L z).comp
      (measurable_const.prodMk measurable_id)).mul (continuous_symmetricExtension L c n).measurable
  calc
    _ = ∫ y, rawPlus L z (representatives L x) (representatives L y) *
        symmetricExtension L c n (representatives L y)
        ∂PhysicalTensor.torusPiMeasure L (N+1) := by
      apply integral_congr_ae
      filter_upwards [BetheH1.coe_wave (L := L) hc hn] with y hy
      change rawPlus L z (representatives L x) (representatives L y) * _ = _
      rw [hy]
      rfl
    _ = ∫ y, rawPlus L z (representatives L x) y * symmetricExtension L c n y
        ∂cubeMeasure (N+1) L := integral_representatives L _ hm
    _ = _ := by
      simp_rw [rawPlus_symmetricExtension]
      exact rawPlus_coordinateAnsatz (Fact.out : 0 < L).le hx c _ hz

theorem minusKernel_sourceWave_integral (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    (x : Fin (N+1) → AddCircle L) {z : ℂ}
    (hx : representatives L x ∈ chamber (N+1) L)
    (hz : ∀ i, z ≠ (BetheSmooth.sourceRoots L n c i : ℂ)) :
    (∫ y, (minusKernel L (N+1) z).fn (x,y) * BetheH1.wave (L := L) hc hn y
      ∂PhysicalTensor.torusPiMeasure L (N+1)) =
      ∑ σ : Equiv.Perm (Fin (N+1)),
        coefficient c (BetheSmooth.sourceRoots L n c ∘ σ) *
          minusValue L (BetheSmooth.sourceRoots L n c ∘ σ) (representatives L x) z := by
  have hm : Measurable (fun y => rawMinus L z (representatives L x) y *
      symmetricExtension L c n y) := by
    exact ((measurable_rawMinus (N+1) L z).comp
      (measurable_const.prodMk measurable_id)).mul (continuous_symmetricExtension L c n).measurable
  calc
    _ = ∫ y, rawMinus L z (representatives L x) (representatives L y) *
        symmetricExtension L c n (representatives L y)
        ∂PhysicalTensor.torusPiMeasure L (N+1) := by
      apply integral_congr_ae
      filter_upwards [BetheH1.coe_wave (L := L) hc hn] with y hy
      change rawMinus L z (representatives L x) (representatives L y) * _ = _
      rw [hy]
      rfl
    _ = ∫ y, rawMinus L z (representatives L x) y * symmetricExtension L c n y
        ∂cubeMeasure (N+1) L := integral_representatives L _ hm
    _ = _ := by
      simp_rw [rawMinus_symmetricExtension]
      exact rawMinus_coordinateAnsatz (Fact.out : 0 < L).le hx c _ hz

/-- Concrete finite-N action of the existing raw bounded operator on the
actual physical wave. The endpoint products still contain unwanted terms.
This is the uncompressed degree-(N+1) constituent, not the full transfer. -/
theorem rawOperator_sourceWave (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) {z : ℂ}
    (hz : ∀ i, z ≠ (BetheSmooth.sourceRoots L n c i : ℂ)) :
    ∀ᵐ x ∂PhysicalTensor.torusPiMeasure L (N+1),
      representatives L x ∈ chamber (N+1) L →
      rawOperator L (N+1) z (BetheH1.wave (L := L) hc hn) x =
        ∑ σ : Equiv.Perm (Fin (N+1)),
          coefficient c (BetheSmooth.sourceRoots L n c ∘ σ) *
            (plusValue (BetheSmooth.sourceRoots L n c ∘ σ) (representatives L x) z +
              minusValue L (BetheSmooth.sourceRoots L n c ∘ σ) (representatives L x) z) := by
  let g := BetheH1.wave (L := L) hc hn
  filter_upwards [Lp.coeFn_add ((plusKernel L (N+1) z).operator g)
      ((minusKernel L (N+1) z).operator g),
    (plusKernel L (N+1) z).operator_apply_ae g,
    (minusKernel L (N+1) z).operator_apply_ae g] with x ha hp hm
  intro hx
  change (((plusKernel L (N+1) z).operator g + (minusKernel L (N+1) z).operator g) x) = _
  rw [ha]
  simp only [Pi.add_apply]
  rw [hp, hm, plusKernel_sourceWave_integral L hc hn x hx hz,
    minusKernel_sourceWave_integral L hc hn x hx hz, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  ring

/-- All 2^m endpoint choices are explicit, with their original signs.
This is the off-shell boundary expansion of the computed kernel integral. -/
theorem endpoint_product_expansion (q a b : Fin m → ℝ) (z : ℂ) :
    (∏ i, endpoint z (q i) (a i) (b i)) =
      (∑ t ∈ (Finset.univ : Finset (Fin m)).powerset,
        (-1 : ℂ) ^ t.card *
          (∏ i ∈ Finset.univ \ t, Complex.exp (Complex.I*((q i : ℂ)-z)*b i)) *
          ∏ i ∈ t, Complex.exp (Complex.I*((q i : ℂ)-z)*a i)) /
        ∏ i, (Complex.I*((q i : ℂ)-z)) := by
  classical
  simp only [endpoint, Finset.prod_div_distrib]
  rw [Finset.prod_sub]

/-- Two-particle upper action has four literal endpoint contributions. -/
theorem plusValue_two (q x : Fin 2 → ℝ) (z : ℂ) :
    plusValue q x z = Complex.exp (Complex.I*z*(x 0+x 1)) *
      (endpoint z (q 0) (x 1) (x 0) * endpoint z (q 1) 0 (x 1)) := by
  simp [plusValue, lower, Fin.prod_univ_two, Fin.sum_univ_two]

theorem minusValue_two (L : ℝ) (q x : Fin 2 → ℝ) (z : ℂ) :
    minusValue L q x z = Complex.exp (Complex.I*z*L + Complex.I*z*(x 0+x 1)) *
      (endpoint z (q 0) (x 0) L * endpoint z (q 1) (x 1) (x 0)) := by
  simp [minusValue, upper, Fin.prod_univ_two, Fin.sum_univ_two]

/-- Explicit nonempty interacting output chamber. -/
theorem chamber_two_nonempty {L : ℝ} (hL : 0 < L) :
    (![2*L/3, L/3] : Fin 2 → ℝ) ∈ chamber 2 L := by
  constructor
  · intro i j hij
    have hi : i = (0 : Fin 2) := by omega
    have hj : j = (1 : Fin 2) := by omega
    rw [hi, hj]
    dsimp
    linarith
  · intro i
    fin_cases i <;> simp <;> (constructor <;> linarith)

theorem plusOrder_output_chamber {L : ℝ} {x y : Fin m → ℝ}
    (h : PlusOrder L x y) : x ∈ chamber m L := by
  constructor
  · intro i j hij
    exact (h.2 i j hij).trans (h.1 i).2.1
  · intro i
    exact ⟨(h.1 i).1.trans (h.1 i).2.1, (h.1 i).2.2⟩

theorem minusOrder_output_chamber {L : ℝ} {x y : Fin m → ℝ}
    (h : MinusOrder L x y) : x ∈ chamber m L := by
  constructor
  · intro i j hij
    exact (h.1 j).2.1.trans (h.2 i j hij)
  · intro i
    exact ⟨(h.1 i).1, (h.1 i).2.1.trans (h.1 i).2.2⟩

theorem rawPlus_zero_off_chamber {L : ℝ} {x : Fin m → ℝ}
    (hx : x ∉ chamber m L) (y : Fin m → ℝ) (z : ℂ) : rawPlus L z x y = 0 := by
  have h : ¬ PlusOrder L x y := fun hh => hx (plusOrder_output_chamber hh)
  simp only [rawPlus, ite_eq_right h]

theorem rawMinus_zero_off_chamber {L : ℝ} {x : Fin m → ℝ}
    (hx : x ∉ chamber m L) (y : Fin m → ℝ) (z : ℂ) : rawMinus L z x y = 0 := by
  have h : ¬ MinusOrder L x y := fun hh => hx (minusOrder_output_chamber hh)
  simp only [rawMinus, ite_eq_right h]

/-- The full computed finite-N boundary sum, before any Bethe cancellation. -/
def boundaryValue (L c : ℝ) (q x : Fin m → ℝ) (z : ℂ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin m), coefficient c (q ∘ σ) *
    (plusValue (q ∘ σ) x z + minusValue L (q ∘ σ) x z)

/-- Unconditional physical L² action, including the zero output off the
strict chamber. Valid for every positive particle number, hence N≥2.
The source transfer also has lower degrees and symmetric placements; they
are not included or assumed here. -/
theorem rawOperator_sourceWave_ae (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) {z : ℂ}
    (hz : ∀ i, z ≠ (BetheSmooth.sourceRoots L n c i : ℂ)) :
    rawOperator L (N+1) z (BetheH1.wave (L := L) hc hn) =ᵐ[
      PhysicalTensor.torusPiMeasure L (N+1)]
      fun x => (chamber (N+1) L).indicator
        (fun v => boundaryValue L c (BetheSmooth.sourceRoots L n c) v z)
        (representatives L x) := by
  classical
  let g := BetheH1.wave (L := L) hc hn
  filter_upwards [rawOperator_sourceWave L hc hn hz,
    Lp.coeFn_add ((plusKernel L (N+1) z).operator g)
      ((minusKernel L (N+1) z).operator g),
    (plusKernel L (N+1) z).operator_apply_ae g,
    (minusKernel L (N+1) z).operator_apply_ae g] with x hact ha hp hm
  by_cases hx : representatives L x ∈ chamber (N+1) L
  · rw [indicator_of_mem hx]
    exact hact hx
  · rw [indicator_of_notMem hx]
    change (((plusKernel L (N+1) z).operator g + (minusKernel L (N+1) z).operator g) x) = _
    rw [ha]
    simp only [Pi.add_apply]
    rw [hp, hm]
    have hp0 : ∀ y, (plusKernel L (N+1) z).fn (x,y) * g y = 0 := by
      intro y
      change rawPlus L z (representatives L x) (representatives L y) * g y = 0
      rw [rawPlus_zero_off_chamber hx, zero_mul]
    have hm0 : ∀ y, (minusKernel L (N+1) z).fn (x,y) * g y = 0 := by
      intro y
      change rawMinus L z (representatives L x) (representatives L y) * g y = 0
      rw [rawMinus_zero_off_chamber hx, zero_mul]
    simp_rw [hp0, hm0]
    simp only [integral_zero, add_zero]

/-- The actual source Bethe wave in the completed symmetric tensor sector. -/
def physicalWave (L : ℝ) [Fact (0 < L)] {N : ℕ} {c : ℝ} (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    TensorCarrier.SymSector ℂ (PhysicalTensor.L2T L) (N+1) :=
  (BethePhysicalTransfer.symmetricPosition L (N+1)).symm
    (ContactOperator.valSym (BetheH1.waveH1Sym (L := L) hc hn))

theorem positionInclusion_physicalWave (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    BethePhysicalTransfer.positionInclusion L (N+1) (physicalWave L hc hn) =
      BetheH1.wave (L := L) hc hn := by
  change (((BethePhysicalTransfer.symmetricPosition L (N+1))
    ((BethePhysicalTransfer.symmetricPosition L (N+1)).symm
      (ContactOperator.valSym (BetheH1.waveH1Sym (L := L) hc hn)))) :
        PhysicalTensor.L2TN L (N+1)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact BetheH1.waveH1_val hc hn

/-- Concrete action of the actual compressed physical degree-m kernel,
in weak form against every symmetric tensor vector. This binds the endpoint
calculation to P_m(Kplus+Kminus)P_m, before any lower-degree placement sum. -/
theorem inner_physicalKernel_sourceWave (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) {z : ℂ}
    (hz : ∀ i, z ≠ (BetheSmooth.sourceRoots L n c i : ℂ))
    (f : TensorCarrier.SymSector ℂ (PhysicalTensor.L2T L) (N+1)) :
    ⟪f, BethePhysicalTransfer.physicalKernel L (N+1) z (physicalWave L hc hn)⟫_ℂ =
      ∫ x, conj (BethePhysicalTransfer.positionInclusion L (N+1) f x) *
        (chamber (N+1) L).indicator
          (fun v => boundaryValue L c (BetheSmooth.sourceRoots L n c) v z)
          (representatives L x) ∂PhysicalTensor.torusPiMeasure L (N+1) := by
  rw [BethePhysicalTransfer.inner_physicalKernel, positionInclusion_physicalWave, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [rawOperator_sourceWave_ae L hc hn hz] with x hx
  simp only [hx, RCLike.inner_apply']

end QuantumNLS.BetheFiniteNAction

#print axioms QuantumNLS.BetheFiniteNAction.lower
#print axioms QuantumNLS.BetheFiniteNAction.upper
#print axioms QuantumNLS.BetheFiniteNAction.lower_bounds
#print axioms QuantumNLS.BetheFiniteNAction.upper_bounds
#print axioms QuantumNLS.BetheFiniteNAction.plusOrder_box
#print axioms QuantumNLS.BetheFiniteNAction.minusOrder_box
#print axioms QuantumNLS.BetheFiniteNAction.plusOrder_input_strictAnti
#print axioms QuantumNLS.BetheFiniteNAction.minusOrder_input_strictAnti
#print axioms QuantumNLS.BetheFiniteNAction.endpoint
#print axioms QuantumNLS.BetheFiniteNAction.interval_endpoint
#print axioms QuantumNLS.BetheFiniteNAction.planeWave_prod
#print axioms QuantumNLS.BetheFiniteNAction.phase_prod
#print axioms QuantumNLS.BetheFiniteNAction.plus_integrand
#print axioms QuantumNLS.BetheFiniteNAction.minus_integrand
#print axioms QuantumNLS.BetheFiniteNAction.rawPlus_planeWave
#print axioms QuantumNLS.BetheFiniteNAction.rawMinus_planeWave
#print axioms QuantumNLS.BetheFiniteNAction.plusValue
#print axioms QuantumNLS.BetheFiniteNAction.minusValue
#print axioms QuantumNLS.BetheFiniteNAction.integrable_plus_planeWave
#print axioms QuantumNLS.BetheFiniteNAction.integrable_minus_planeWave
#print axioms QuantumNLS.BetheFiniteNAction.rawPlus_coordinateAnsatz
#print axioms QuantumNLS.BetheFiniteNAction.rawMinus_coordinateAnsatz
#print axioms QuantumNLS.BetheFiniteNAction.rawPlus_symmetricExtension
#print axioms QuantumNLS.BetheFiniteNAction.rawMinus_symmetricExtension
#print axioms QuantumNLS.BetheFiniteNAction.integral_representatives
#print axioms QuantumNLS.BetheFiniteNAction.plusKernel_sourceWave_integral
#print axioms QuantumNLS.BetheFiniteNAction.minusKernel_sourceWave_integral
#print axioms QuantumNLS.BetheFiniteNAction.rawOperator_sourceWave
#print axioms QuantumNLS.BetheFiniteNAction.endpoint_product_expansion
#print axioms QuantumNLS.BetheFiniteNAction.plusValue_two
#print axioms QuantumNLS.BetheFiniteNAction.minusValue_two
#print axioms QuantumNLS.BetheFiniteNAction.chamber_two_nonempty
#print axioms QuantumNLS.BetheFiniteNAction.plusOrder_output_chamber
#print axioms QuantumNLS.BetheFiniteNAction.minusOrder_output_chamber
#print axioms QuantumNLS.BetheFiniteNAction.rawPlus_zero_off_chamber
#print axioms QuantumNLS.BetheFiniteNAction.rawMinus_zero_off_chamber
#print axioms QuantumNLS.BetheFiniteNAction.boundaryValue
#print axioms QuantumNLS.BetheFiniteNAction.rawOperator_sourceWave_ae
#print axioms QuantumNLS.BetheFiniteNAction.physicalWave
#print axioms QuantumNLS.BetheFiniteNAction.positionInclusion_physicalWave
#print axioms QuantumNLS.BetheFiniteNAction.inner_physicalKernel_sourceWave

run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.BetheFiniteNAction.inner_physicalKernel_sourceWave,
    ``QuantumNLS.BetheFiniteNAction.endpoint_product_expansion,
    ``QuantumNLS.BetheFiniteNAction.plusValue_two,
    ``QuantumNLS.BetheFiniteNAction.minusValue_two,
    ``QuantumNLS.BetheFiniteNAction.chamber_two_nonempty]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[``QuantumNLS.BethePhysicalTransfer.physicalKernel,
      ``QuantumNLS.BethePhysicalTransfer.positionInclusion,
      ``QuantumNLS.BethePhysicalTransfer.symmetricPosition,
      ``QuantumNLS.BetheTransferOperators.rawOperator,
      ``QuantumNLS.BetheTransferOperators.plusKernel,
      ``QuantumNLS.BetheTransferOperators.minusKernel,
      ``QuantumNLS.BetheTransferKernelAdjoint.rawPlus,
      ``QuantumNLS.BetheTransferKernelAdjoint.rawMinus,
      ``QuantumNLS.BetheTransferKernelAdjoint.PlusOrder,
      ``QuantumNLS.BetheIntegralOperator.Kernel.operator_apply_ae,
      ``QuantumNLS.BetheFiniteNAction.rawOperator_sourceWave_ae,
      ``QuantumNLS.BetheFiniteNAction.rawPlus_planeWave,
      ``QuantumNLS.BetheFiniteNAction.rawMinus_planeWave,
      ``QuantumNLS.BetheFiniteNAction.plusOrder_box,
      ``QuantumNLS.BetheFiniteNAction.minusOrder_box,
      ``QuantumNLS.BetheFiniteNAction.interval_endpoint,
      ``QuantumNLS.BetheWeakGradient.cube_to_torus_measurePreserving,
      ``QuantumNLS.BetheWeakGradient.cubeMeasure,
      ``QuantumNLS.BetheH1.wave,
      ``QuantumNLS.BetheH1.coe_wave,
      ``QuantumNLS.BetheWavefunctions.coordinateAnsatz,
      ``QuantumNLS.BetheWavefunctions.coefficient,
      ``QuantumNLS.BetheSmooth.sourceRoots,
      ``MeasureTheory.integral_fin_nat_prod_eq_prod] do
    unless seen.contains n do
      throwError "Finite-N action route missed literal source ingredient: {n}"
  for n in seen.toArray do
    if n.toString.startsWith "QuantumNLS.BetheOneParticleAction." then
      throwError "Finite-N action incorrectly depends on one-particle seed: {n}"
  Lean.logInfo m!"Finite-N physical kernel action route PASS: {seen.size} transitive constants; literal upper/lower integrals, full endpoint expansion, actual finite-N Bethe wave, ordinary physical measure and compressed physical tensor kernel reached. Lower-degree placements, cross-degree cancellation and full interacting eigenrelation remain open."

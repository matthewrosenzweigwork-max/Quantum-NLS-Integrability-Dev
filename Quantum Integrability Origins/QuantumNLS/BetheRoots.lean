import QuantumNLS.BetheAdmission
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Yang--Yang root construction for DEF-006 / R-4C8D7C9E.
Report pin: 3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f.
Source: periodic_basis.tex:133--162; root_response/F01.tex:4--20.
The interaction is written as the ordered double sum of the even primitive,
equivalent to twice the sum over unordered pairs. No root or basis is assumed.
-/

noncomputable section
open scoped BigOperators
open Set

namespace QuantumNLS.BetheRoots
open BetheAdmission

/-- The literal pair primitive in the source Yang--Yang functional. -/
def pairPrimitive (c x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, Real.arctan (s / c)

theorem pairPrimitive_zero (c : ℝ) : pairPrimitive c 0 = 0 := by
  simp [pairPrimitive]

theorem pairPrimitive_nonneg {c : ℝ} (hc : 0 < c) (x : ℝ) :
    0 ≤ pairPrimitive c x := by
  by_cases hx : 0 ≤ x
  · exact intervalIntegral.integral_nonneg hx
      (fun s hs => Real.arctan_nonneg.mpr (div_nonneg hs.1 hc.le))
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [pairPrimitive, intervalIntegral.integral_symm]
    apply neg_nonneg.mpr
    have h : 0 ≤ ∫ s in x..(0 : ℝ), -Real.arctan (s / c) := by
      apply intervalIntegral.integral_nonneg hx'
      intro s hs
      have hm := Real.arctan_mono (div_nonpos_of_nonpos_of_nonneg hs.2 hc.le)
      simpa using hm
    simpa only [intervalIntegral.integral_neg, neg_nonneg] using h

theorem pairPrimitive_even (c x : ℝ) : pairPrimitive c (-x) = pairPrimitive c x := by
  have h := intervalIntegral.integral_comp_neg (fun s : ℝ => Real.arctan (s / c))
    (a := (0 : ℝ)) (b := x)
  simp only [neg_div, Real.arctan_neg, intervalIntegral.integral_neg, neg_zero] at h
  unfold pairPrimitive
  rw [intervalIntegral.integral_symm (-x) (0 : ℝ), ← h]
  simp

theorem pairPrimitive_hasDerivAt (c x : ℝ) :
    HasDerivAt (pairPrimitive c) (Real.arctan (x / c)) x := by
  have h : Continuous (fun s : ℝ => Real.arctan (s / c)) := by fun_prop
  exact intervalIntegral.integral_hasDerivAt_right (h.intervalIntegrable _ _)
    h.aestronglyMeasurable.stronglyMeasurableAtFilter h.continuousAt

theorem pairPrimitive_continuous (c : ℝ) : Continuous (pairPrimitive c) :=
by
  have h : Differentiable ℝ (pairPrimitive c) :=
    fun x => (pairPrimitive_hasDerivAt c x).differentiableAt
  exact h.continuous

/-- Arbitrary real forcing; the Bethe forcing is `2*pi*quantumNumbers n`. -/
def yangYang {N : ℕ} (L c : ℝ) (b q : Fin N → ℝ) : ℝ :=
  (∑ i, (L / 2 * (q i)^2 - b i * q i)) +
    ∑ i, ∑ j, pairPrimitive c (q i - q j)

theorem yangYang_zero {N : ℕ} (L c : ℝ) (b : Fin N → ℝ) :
    yangYang L c b 0 = 0 := by simp [yangYang, pairPrimitive_zero]

theorem yangYang_continuous {N : ℕ} (L c : ℝ) (b : Fin N → ℝ) :
    Continuous (yangYang L c b) := by
  unfold yangYang
  exact (continuous_finsetSum _ fun i _ => by fun_prop).add
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (pairPrimitive_continuous c).comp (by fun_prop))

/-- Quantitative coercive lower bound, by completing the square in each
coordinate and retaining the nonnegative pair primitives. -/
theorem yangYang_lower_bound {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (b q : Fin N → ℝ) :
    L * ((∑ i, (q i)^2) / 4 - ∑ i, (b i / L)^2) ≤ yangYang L c b q := by
  have hi (i : Fin N) : L * ((q i)^2 / 4 - (b i / L)^2) ≤
      L / 2 * (q i)^2 - b i * q i := by
    have hs := mul_nonneg hL.le (sq_nonneg (q i / 2 - b i / L))
    have he : L * (q i / 2 - b i / L)^2 =
        (L / 2 * (q i)^2 - b i * q i) - L * ((q i)^2 / 4 - (b i / L)^2) := by
      field_simp
      ring
    linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  have hp : 0 ≤ ∑ i, ∑ j, pairPrimitive c (q i - q j) := by
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun j _ => pairPrimitive_nonneg hc _))
  have he : L * ((∑ i, (q i)^2) / 4 - ∑ i, (b i / L)^2) =
      ∑ i, L * ((q i)^2 / 4 - (b i / L)^2) := by
    simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_div]
  rw [he]
  exact hs.trans (le_add_of_nonneg_right hp)

/-- A bounded zero sublevel gives a global minimum on the actual finite
dimensional configuration space, including every N >= 2. -/
theorem yangYang_exists_min {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (b : Fin N → ℝ) : ∃ q, ∀ r, yangYang L c b q ≤ yangYang L c b r := by
  apply (yangYang_continuous L c b).exists_forall_le_of_isBounded 0
  apply isBounded_iff_forall_norm_le.mpr
  let C : ℝ := ∑ i, (b i / L)^2
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  refine ⟨4 * C + 1, ?_⟩
  intro q hq
  have hq0 : yangYang L c b q ≤ 0 := by simpa only [Set.mem_ofPred_eq, yangYang_zero] using hq
  have hb := yangYang_lower_bound hL hc b q
  have hs : (∑ i, (q i)^2) ≤ 4 * C := by dsimp [C]; nlinarith
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 4 * C + 1)).mpr
  intro i
  have hi : (q i)^2 ≤ ∑ j, (q j)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [Real.norm_eq_abs]
  have ha := sq_abs (q i)
  have hsq := sq_nonneg (|q i| - 1)
  nlinarith [abs_nonneg (q i)]

/-- Algebraic pairing of an odd interaction with a displacement. -/
theorem antisymmetric_pairing {N : ℕ} (a : Fin N → Fin N → ℝ)
    (ha : ∀ i j, a j i = -a i j) (v : Fin N → ℝ) :
    (∑ i, ∑ j, a i j * (v i - v j)) = 2 * ∑ i, (∑ j, a i j) * v i := by
  have hs : (∑ i, ∑ j, a i j * v j) = -(∑ i, ∑ j, a i j * v i) := by
    calc
      _ = ∑ i, ∑ j, a j i * v i := Finset.sum_comm
      _ = _ := by
        simp only [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [ha i j, neg_mul]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hs]
  simp only [← Finset.sum_mul]
  ring

/-- The first variation is exactly the logarithmic Bethe map minus forcing. -/
theorem yangYang_line_hasDerivAt {N : ℕ} (L c : ℝ) (b q v : Fin N → ℝ) :
    HasDerivAt (fun t : ℝ => yangYang L c b (fun i => q i + t * v i))
      (∑ i, (logMap L c q i - b i) * v i) 0 := by
  have hl (i : Fin N) : HasDerivAt (fun t : ℝ => q i + t * v i) (v i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (q i)
  have hk : HasDerivAt
      (fun t : ℝ => ∑ i, (L / 2 * (q i + t * v i)^2 - b i * (q i + t * v i)))
      (∑ i, (L * q i - b i) * v i) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    convert ((hl i).pow 2 |>.const_mul (L / 2)).sub ((hl i).const_mul (b i)) using 1
    simp
    ring
  have hp : HasDerivAt
      (fun t : ℝ => ∑ i, ∑ j, pairPrimitive c
        ((q i + t * v i) - (q j + t * v j)))
      (∑ i, ∑ j, Real.arctan ((q i - q j) / c) * (v i - v j)) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j _
    convert! (pairPrimitive_hasDerivAt c ((q i + 0 * v i) - (q j + 0 * v j))).comp 0
        ((hl i).sub (hl j)) using 1
    simp
  have ha (i j : Fin N) : Real.arctan ((q j - q i) / c) =
      -Real.arctan ((q i - q j) / c) := by
    rw [← Real.arctan_neg]
    congr 1
    ring
  convert hk.add hp using 1
  · rfl
  · rw [antisymmetric_pairing _ ha]
    simp only [logMap, add_sub_assoc, add_mul, sub_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, mul_assoc]
    ring

/-- A global minimum solves the literal equations; no inverse map is supplied. -/
theorem yangYang_min_solves {N : ℕ} (L c : ℝ) (b q : Fin N → ℝ)
    (hq : ∀ r, yangYang L c b q ≤ yangYang L c b r) : logMap L c q = b := by
  classical
  funext i
  let v : Fin N → ℝ := fun j => if j = i then 1 else 0
  have hm : IsLocalMin (fun t : ℝ => yangYang L c b (fun j => q j + t * v j)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa only [zero_mul, add_zero] using hq (fun j => q j + t * v j)
  have hz := hm.hasDerivAt_eq_zero (yangYang_line_hasDerivAt L c b q v)
  have hi : logMap L c q i - b i = 0 := by simpa [v] using hz
  linarith

/-- Surjectivity of the actual repulsive Bethe map, for every finite N. -/
theorem logMap_surjective {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c) :
    Function.Surjective (logMap (N := N) L c) := by
  intro b
  obtain ⟨q, hq⟩ := yangYang_exists_min hL hc b
  exact ⟨q, yangYang_min_solves L c b q hq⟩

/-- Actual existence and uniqueness at corrected integer labels. -/
theorem roots_existsUnique {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (n : Fin N → ℤ) : ∃! q : Fin N → ℝ, Solves L c n q := by
  obtain ⟨q, hq⟩ := logMap_surjective (N := N) hL hc
    (fun i => 2 * Real.pi * quantumNumbers n i)
  have hsol : Solves L c n q := fun i => congrFun hq i
  exact ⟨q, hsol, fun r hr => roots_unique hL hc hr hsol⟩

/-- Sorted corrected labels yield the unique strictly increasing tuple,
including repeated Bose labels and the interacting sectors N >= 2. -/
theorem sorted_roots_existsUnique {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (n : CorrectedLabels N) :
    ∃! q : Fin N → ℝ, Solves L c n.val q ∧ StrictMono q := by
  obtain ⟨q, hq, hu⟩ := roots_existsUnique hL hc n.val
  exact ⟨q, ⟨hq, roots_strictMono hL hc n hq⟩, fun r hr => hu r hr.1⟩

/-- The ordered double sum is exactly the source's twice-unordered-pair
sum; evenness also shows why reversal never negates a rapidity. -/
theorem pairPrimitive_sum_eq {N : ℕ} (c : ℝ) (q : Fin N → ℝ) :
    (∑ i, ∑ j, pairPrimitive c (q i - q j)) =
      2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        pairPrimitive c (q i - q j) := by
  classical
  have he (i j : Fin N) : pairPrimitive c (q j - q i) =
      pairPrimitive c (q i - q j) := by
    convert pairPrimitive_even c (q i - q j) using 1
    congr 1
    ring
  have hp (i j : Fin N) : pairPrimitive c (q i - q j) =
      (if i < j then pairPrimitive c (q i - q j) else 0) +
      (if j < i then pairPrimitive c (q j - q i) else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_ge h.le]
    · subst j; simp [pairPrimitive_zero]
    · simp [h, not_lt_of_ge h.le, he i j]
  calc
    _ = ∑ i, ∑ j,
        ((if i < j then pairPrimitive c (q i - q j) else 0) +
         (if j < i then pairPrimitive c (q j - q i) else 0)) := by
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hp i j))
    _ = (∑ i, ∑ j, if i < j then pairPrimitive c (q i - q j) else 0) +
        (∑ i, ∑ j, if j < i then pairPrimitive c (q j - q i) else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = _ := by
      rw [Finset.sum_comm (f := fun i j : Fin N =>
        if j < i then pairPrimitive c (q j - q i) else 0)]
      simp only [Finset.sum_filter]
      ring

/-- The exact source functional, including its factor two. -/
theorem yangYang_eq_source {N : ℕ} (L c : ℝ) (b q : Fin N → ℝ) :
    yangYang L c b q = L / 2 * ∑ i, (q i)^2 - ∑ i, b i * q i +
      2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        pairPrimitive c (q i - q j) := by
  rw [yangYang, pairPrimitive_sum_eq]
  simp only [Finset.sum_sub_distrib, Finset.mul_sum]

/-- Positive edge weights of the source Gaudin matrix. -/
def edgeWeight {N : ℕ} (c : ℝ) (q : Fin N → ℝ) (i j : Fin N) : ℝ :=
  2 * c / (c^2 + (q i - q j)^2)

theorem edgeWeight_pos {N : ℕ} {c : ℝ} (hc : 0 < c) (q : Fin N → ℝ) (i j : Fin N) :
    0 < edgeWeight c q i j := by
  unfold edgeWeight
  exact div_pos (by positivity) (add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg _))

theorem edgeWeight_symm {N : ℕ} (c : ℝ) (q : Fin N → ℝ) (i j : Fin N) :
    edgeWeight c q j i = edgeWeight c q i j := by
  unfold edgeWeight
  congr 1
  ring

/-- The actual Gaudin derivative, as a continuous linear map. -/
def gaudin {N : ℕ} (L c : ℝ) (q : Fin N → ℝ) :
    (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi (fun i : Fin N =>
    L • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i) : (Fin N → ℝ) →L[ℝ] ℝ) +
    ∑ j : Fin N, edgeWeight c q i j •
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i) - (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) j)))

theorem gaudin_apply {N : ℕ} (L c : ℝ) (q v : Fin N → ℝ) (i : Fin N) :
    gaudin L c q v i = L * v i + ∑ j, edgeWeight c q i j * (v i - v j) := by
  simp [gaudin]

theorem logMap_hasFDerivAt {N : ℕ} (L : ℝ) {c : ℝ} (hc : 0 < c) (q : Fin N → ℝ) :
    HasFDerivAt (logMap L c) (gaudin L c q) q := by
  have hw (d : ℝ) : 2 * (1 / (1 + (d / c)^2) * c⁻¹) =
      2 * c / (c^2 + d^2) := by
    have hden : c^2 + d^2 ≠ 0 := ne_of_gt
      (add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg d))
    have hden' : 1 + (d / c)^2 ≠ 0 := by positivity
    field_simp
  unfold gaudin
  apply hasFDerivAt_pi.mpr
  intro i
  have hj (j : Fin N) : HasFDerivAt
      (fun x : Fin N → ℝ => Real.arctan ((x i - x j) / c))
      ((1 / (1 + ((q i - q j) / c)^2)) •
        (c⁻¹ • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i) - (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) j)))) q := by
    have hd := ((hasFDerivAt_apply (𝕜 := ℝ) i q).sub (hasFDerivAt_apply (𝕜 := ℝ) j q)).const_mul c⁻¹
    simpa only [Pi.sub_apply, div_eq_mul_inv, mul_comm] using hd.arctan
  convert! ((hasFDerivAt_apply (𝕜 := ℝ) i q).const_mul L).add
    ((HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hj j)).const_mul 2) using 1
  simp only [Finset.smul_sum, smul_smul, hw, edgeWeight]

/-- The graph-Laplacian quadratic identity, with no symmetry/positivity
hypothesis supplied by a caller: both come from the actual arctangent. -/
theorem gaudin_quadratic {N : ℕ} (L c : ℝ) (q v : Fin N → ℝ) :
    (∑ i, v i * gaudin L c q v i) = L * ∑ i, (v i)^2 +
      (1 / 2 : ℝ) * ∑ i, ∑ j, edgeWeight c q i j * (v i - v j)^2 := by
  have hs : (∑ i, ∑ j, edgeWeight c q i j * (v i - v j) * v j) =
      -(∑ i, ∑ j, edgeWeight c q i j * (v i - v j) * v i) := by
    calc
      _ = ∑ i, ∑ j, edgeWeight c q j i * (v j - v i) * v i := Finset.sum_comm
      _ = _ := by
        simp only [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [edgeWeight_symm]
        ring
  have he : (∑ i, ∑ j, edgeWeight c q i j * (v i - v j)^2) =
      2 * ∑ i, ∑ j, edgeWeight c q i j * (v i - v j) * v i := by
    have hp (i j : Fin N) : edgeWeight c q i j * (v i - v j)^2 =
        edgeWeight c q i j * (v i - v j) * v i -
        edgeWeight c q i j * (v i - v j) * v j := by ring
    simp_rw [hp]
    simp only [Finset.sum_sub_distrib]
    rw [hs]
    ring
  have hk : (∑ i, v i * (L * v i)) = L * ∑ i, (v i)^2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hp : (∑ i, v i * ∑ j, edgeWeight c q i j * (v i - v j)) =
      ∑ i, ∑ j, edgeWeight c q i j * (v i - v j) * v i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [he]
  simp only [gaudin_apply, mul_add, Finset.sum_add_distrib]
  rw [hk, hp]
  ring

/-- Uniform positive lower bound of the Gaudin quadratic form. -/
theorem gaudin_lower_bound {N : ℕ} (L : ℝ) {c : ℝ} (hc : 0 < c) (q v : Fin N → ℝ) :
    L * ∑ i, (v i)^2 ≤ ∑ i, v i * gaudin L c q v i := by
  rw [gaudin_quadratic]
  exact le_add_of_nonneg_right (mul_nonneg (by norm_num)
    (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (edgeWeight_pos hc q i j).le (sq_nonneg _)))))

/-- Strict positive definiteness at every real configuration. -/
theorem gaudin_pos {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (q : Fin N → ℝ) {v : Fin N → ℝ} (hv : v ≠ 0) :
    0 < ∑ i, v i * gaudin L c q v i := by
  have hv' : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    simpa using not_exists.mp h i
  obtain ⟨i, hi⟩ := hv'
  have hs : 0 < ∑ j, (v j)^2 := lt_of_lt_of_le (sq_pos_of_ne_zero hi)
    (Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  exact lt_of_lt_of_le (mul_pos hL hs) (gaudin_lower_bound L hc q v)

/-- Finite-dimensional invertibility is proved from positive definiteness. -/
theorem gaudin_bijective {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (q : Fin N → ℝ) : Function.Bijective (gaudin L c q) := by
  have hi : Function.Injective (gaudin L c q) := by
    apply (gaudin L c q).ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    by_contra hne
    have hp := gaudin_pos hL hc q hne
    change gaudin L c q v = 0 at hv
    rw [hv] at hp
    simp at hp
  exact ⟨hi, (LinearMap.injective_iff_surjective (f := (gaudin L c q).toLinearMap)).mp hi⟩

/-- The source scalar-product estimate; the odd interaction contributes
nonnegative work in the radial direction. -/
theorem logMap_radial_lower {N : ℕ} (L : ℝ) {c : ℝ} (hc : 0 < c) (q : Fin N → ℝ) :
    L * ∑ i, (q i)^2 ≤ ∑ i, logMap L c q i * q i := by
  have ha (i j : Fin N) : Real.arctan ((q j - q i) / c) =
      -Real.arctan ((q i - q j) / c) := by
    rw [← Real.arctan_neg]
    congr 1
    ring
  have hp : 0 ≤ ∑ i, ∑ j, Real.arctan ((q i - q j) / c) * (q i - q j) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    by_cases hd : 0 ≤ q i - q j
    · exact mul_nonneg (Real.arctan_nonneg.mpr (div_nonneg hd hc.le)) hd
    · have hm : Real.arctan ((q i - q j) / c) ≤ 0 := by
        simpa using Real.arctan_mono (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hd) hc.le)
      exact mul_nonneg_of_nonpos_of_nonpos hm (le_of_not_ge hd)
  rw [antisymmetric_pairing _ ha q] at hp
  simp only [logMap, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, pow_two]
  exact le_add_of_nonneg_right hp

/-- A source Euclidean estimate, squared and for arbitrary real forcing. -/
theorem solution_sq_bound {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (b q : Fin N → ℝ) (hq : logMap L c q = b) :
    L^2 * (∑ i, (q i)^2) ≤ ∑ i, (b i)^2 := by
  have hQ : 0 ≤ ∑ i, (q i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hB : 0 ≤ ∑ i, (b i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hb := logMap_radial_lower L hc q
  rw [hq] at hb
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ b q
  rcases hQ.eq_or_lt with hzero | hpos
  · rw [← hzero, mul_zero]
    exact hB
  · apply (mul_le_mul_iff_of_pos_right hpos).mp
    calc
      (L^2 * ∑ i, (q i)^2) * (∑ i, (q i)^2) =
          (L * ∑ i, (q i)^2)^2 := by ring
      _ ≤ (∑ i, b i * q i)^2 :=
        (sq_le_sq₀ (mul_nonneg hL.le hQ) (le_trans (mul_nonneg hL.le hQ) hb)).mpr hb
      _ ≤ _ := hCS

/-- The exact bound |q| <= 2*pi*|I|/L from basis:eq:rootbound, with
Euclidean lengths expressed by square roots of finite sums of squares. -/
theorem roots_norm_bound {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin N → ℤ} {q : Fin N → ℝ} (hq : Solves L c n q) :
    Real.sqrt (∑ i, (q i)^2) ≤
      2 * Real.pi * Real.sqrt (∑ i, (quantumNumbers n i)^2) / L := by
  have he : logMap L c q = fun i => 2 * Real.pi * quantumNumbers n i := funext hq
  have hb := solution_sq_bound hL hc _ q he
  have hsum : (∑ i, (2 * Real.pi * quantumNumbers n i)^2) =
      (2 * Real.pi)^2 * ∑ i, (quantumNumbers n i)^2 := by
    simp only [mul_pow, Finset.mul_sum]
  rw [hsum] at hb
  have hQ : 0 ≤ ∑ i, (q i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hI : 0 ≤ ∑ i, (quantumNumbers n i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  apply (le_div_iff₀ hL).mpr
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hL.le)
    (mul_nonneg (by positivity) (Real.sqrt_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt hQ, Real.sq_sqrt hI, mul_comm] using hb

end QuantumNLS.BetheRoots

#print axioms QuantumNLS.BetheRoots.pairPrimitive
#print axioms QuantumNLS.BetheRoots.pairPrimitive_zero
#print axioms QuantumNLS.BetheRoots.pairPrimitive_nonneg
#print axioms QuantumNLS.BetheRoots.pairPrimitive_even
#print axioms QuantumNLS.BetheRoots.pairPrimitive_hasDerivAt
#print axioms QuantumNLS.BetheRoots.pairPrimitive_continuous
#print axioms QuantumNLS.BetheRoots.yangYang
#print axioms QuantumNLS.BetheRoots.yangYang_zero
#print axioms QuantumNLS.BetheRoots.yangYang_continuous
#print axioms QuantumNLS.BetheRoots.yangYang_lower_bound
#print axioms QuantumNLS.BetheRoots.yangYang_exists_min
#print axioms QuantumNLS.BetheRoots.antisymmetric_pairing
#print axioms QuantumNLS.BetheRoots.yangYang_line_hasDerivAt
#print axioms QuantumNLS.BetheRoots.yangYang_min_solves
#print axioms QuantumNLS.BetheRoots.logMap_surjective
#print axioms QuantumNLS.BetheRoots.roots_existsUnique
#print axioms QuantumNLS.BetheRoots.sorted_roots_existsUnique
#print axioms QuantumNLS.BetheRoots.pairPrimitive_sum_eq
#print axioms QuantumNLS.BetheRoots.yangYang_eq_source
#print axioms QuantumNLS.BetheRoots.edgeWeight
#print axioms QuantumNLS.BetheRoots.edgeWeight_pos
#print axioms QuantumNLS.BetheRoots.edgeWeight_symm
#print axioms QuantumNLS.BetheRoots.gaudin
#print axioms QuantumNLS.BetheRoots.gaudin_apply
#print axioms QuantumNLS.BetheRoots.logMap_hasFDerivAt
#print axioms QuantumNLS.BetheRoots.gaudin_quadratic
#print axioms QuantumNLS.BetheRoots.gaudin_lower_bound
#print axioms QuantumNLS.BetheRoots.gaudin_pos
#print axioms QuantumNLS.BetheRoots.gaudin_bijective
#print axioms QuantumNLS.BetheRoots.logMap_radial_lower
#print axioms QuantumNLS.BetheRoots.solution_sq_bound
#print axioms QuantumNLS.BetheRoots.roots_norm_bound

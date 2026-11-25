import QuantumNLS.BetheFiniteNAction
import QuantumNLS.BetheOnShell

/-! Literal degree-one coordinate integrations in the two-particle sector.
The spectator forces a split at its coordinate. All physical endpoints and
the lower-branch exp(izL) are retained. Source: periodic_basis.tex:316–365.
The completed-tensor placement identification is a separate obligation. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ComplexConjugate InnerProductSpace
set_option maxHeartbeats 2000000

namespace QuantumNLS.BetheTwoParticleAction
open BetheWavefunctions BetheExtension BetheTransferKernelAdjoint BetheFiniteNAction

/-- The actual two-particle chamber formula extended by decreasing rearrangement. -/
def pair (c a b x y : ℝ) : ℂ := pairWave c a b (max x y) (min x y)

theorem pair_swap (c a b x y : ℝ) : pair c a b y x = pair c a b x y := by
  simp only [pair, max_comm y x, min_comm y x]

theorem pair_of_le (c a b : ℝ) {x y : ℝ} (h : y ≤ x) :
    pair c a b x y = pairWave c a b x y := by
  simp only [pair, max_eq_left h, min_eq_right h]

theorem continuous_pair (c a b : ℝ) : Continuous (fun p : ℝ × ℝ => pair c a b p.1 p.2) := by
  unfold pair pairWave
  fun_prop

theorem tuple_antitone {x y : ℝ} (h : y ≤ x) : Antitone (![x,y] : Fin 2 → ℝ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- Exact identification with the existing source-root extension, including the wall. -/
theorem symmetricExtension_two (L c : ℝ) (n : Fin 2 → ℤ) (x y : ℝ) :
    symmetricExtension L c n ![x,y] =
      pair c (BetheSmooth.sourceRoots L n c 0) (BetheSmooth.sourceRoots L n c 1) x y := by
  by_cases h : y ≤ x
  · rw [symmetricExtension_eq L c n (tuple_antitone h)]
    simpa only [wavefunction, coordinateAnsatz_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons] using (pair_of_le c
        (BetheSmooth.sourceRoots L n c 0) (BetheSmooth.sourceRoots L n c 1) h).symm
  · have hp : (![x,y] : Fin 2 → ℝ) = ![y,x] ∘ Equiv.swap 0 1 := by
      ext i; fin_cases i <;> simp
    rw [hp, symmetricExtension_permute, symmetricExtension_eq L c n (tuple_antitone (le_of_not_ge h))]
    simp only [wavefunction, coordinateAnsatz_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [pair_swap, pair_of_le _ _ _ (le_of_not_ge h)]

/-- One integrated frequency, with the unevaluated spectator multiplier. -/
def segment (z : ℂ) (q s u lo hi : ℝ) : ℂ :=
  Complex.exp (Complex.I*z*u) * Complex.exp (Complex.I*s) * endpoint z q lo hi

theorem phase_integral (z : ℂ) (q s u lo hi : ℝ) (hz : z ≠ (q : ℂ)) :
    (∫ t in lo..hi, Complex.exp (Complex.I*z*(u-t)) *
      Complex.exp (Complex.I*((q*t+s : ℝ) : ℂ))) = segment z q s u lo hi := by
  have he (t : ℝ) : Complex.exp (Complex.I*z*(u-t)) *
      Complex.exp (Complex.I*((q*t+s : ℝ) : ℂ)) =
      (Complex.exp (Complex.I*z*u) * Complex.exp (Complex.I*s)) *
        Complex.exp ((Complex.I*((q : ℂ)-z))*t) := by
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex
    (mul_ne_zero Complex.I_ne_zero (sub_ne_zero.mpr hz.symm))]
  rfl

/-- Integral when the integrated coordinate lies above the spectator. -/
def above (c a b s u lo hi : ℝ) (z : ℂ) : ℂ :=
  factor c a b * segment z a (b*s) u lo hi +
    factor c b a * segment z b (a*s) u lo hi

/-- Integral when the integrated coordinate lies below the spectator. -/
def below (c a b s u lo hi : ℝ) (z : ℂ) : ℂ :=
  factor c a b * segment z b (a*s) u lo hi +
    factor c b a * segment z a (b*s) u lo hi

theorem integral_above (c a b s u lo hi : ℝ) (z : ℂ)
    (ha : z ≠ (a : ℂ)) (hb : z ≠ (b : ℂ)) :
    (∫ t in lo..hi, Complex.exp (Complex.I*z*(u-t)) * pairWave c a b t s) =
      above c a b s u lo hi z := by
  have hc (v w : ℝ) : IntervalIntegrable (fun t : ℝ =>
      Complex.exp (Complex.I*z*(u-t)) * Complex.exp (Complex.I*((v*t+w : ℝ) : ℂ))) volume lo hi :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  calc
    _ = ∫ t in lo..hi, factor c a b * (Complex.exp (Complex.I*z*(u-t)) *
          Complex.exp (Complex.I*((a*t+b*s : ℝ) : ℂ))) +
        factor c b a * (Complex.exp (Complex.I*z*(u-t)) *
          Complex.exp (Complex.I*((b*t+a*s : ℝ) : ℂ))) := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [pairWave]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add ((hc a (b*s)).const_mul _) ((hc b (a*s)).const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        phase_integral z a (b*s) u lo hi ha, phase_integral z b (a*s) u lo hi hb]
      rfl

theorem integral_below (c a b s u lo hi : ℝ) (z : ℂ)
    (ha : z ≠ (a : ℂ)) (hb : z ≠ (b : ℂ)) :
    (∫ t in lo..hi, Complex.exp (Complex.I*z*(u-t)) * pairWave c a b s t) =
      below c a b s u lo hi z := by
  have hc (v w : ℝ) : IntervalIntegrable (fun t : ℝ =>
      Complex.exp (Complex.I*z*(u-t)) * Complex.exp (Complex.I*((v*t+w : ℝ) : ℂ))) volume lo hi :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  calc
    _ = ∫ t in lo..hi, factor c a b * (Complex.exp (Complex.I*z*(u-t)) *
          Complex.exp (Complex.I*((b*t+a*s : ℝ) : ℂ))) +
        factor c b a * (Complex.exp (Complex.I*z*(u-t)) *
          Complex.exp (Complex.I*((a*t+b*s : ℝ) : ℂ))) := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [pairWave]
      rw [show a*s+b*t=b*t+a*s by ring, show b*s+a*t=a*t+b*s by ring]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add ((hc b (a*s)).const_mul _) ((hc a (b*s)).const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        phase_integral z b (a*s) u lo hi hb, phase_integral z a (b*s) u lo hi ha]
      rfl

/-- Exact upper one-body kernel acting on a two-body slice. -/
theorem rawPlus_slice {L u : ℝ} (hu : u ∈ Ioo 0 L) (c a b s : ℝ) (z : ℂ) :
    (∫ t in Icc 0 L, rawPlus L z (fun _ : Fin 1 => u) (fun _ => t) * pair c a b t s) =
      ∫ t in 0..u, Complex.exp (Complex.I*z*(u-t)) * pair c a b t s := by
  have he (t : ℝ) : rawPlus L z (fun _ : Fin 1 => u) (fun _ => t) * pair c a b t s =
      (Ioo 0 u).indicator (fun t => Complex.exp (Complex.I*z*(u-t)) * pair c a b t s) t := by
    have ho : PlusOrder L (fun _ : Fin 1 => u) (fun _ => t) ↔ t ∈ Ioo 0 u := by
      simp [PlusOrder, hu.2]
    simp only [rawPlus, ho, displacement, Fin.sum_univ_one]
    by_cases ht : t ∈ Ioo 0 u <;> simp [ht]
  simp_rw [he]
  rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr (show Ioo 0 u ⊆ Icc 0 L from fun t ht => ⟨ht.1.le, ht.2.le.trans hu.2.le⟩),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hu.1.le]

/-- Exact lower branch, with its full physical exp(izL) multiplier. -/
theorem rawMinus_slice {L u : ℝ} (hu : u ∈ Ioo 0 L) (c a b s : ℝ) (z : ℂ) :
    (∫ t in Icc 0 L, rawMinus L z (fun _ : Fin 1 => u) (fun _ => t) * pair c a b t s) =
      Complex.exp (Complex.I*z*L) *
        ∫ t in u..L, Complex.exp (Complex.I*z*(u-t)) * pair c a b t s := by
  have he (t : ℝ) : rawMinus L z (fun _ : Fin 1 => u) (fun _ => t) * pair c a b t s =
      (Ioo u L).indicator (fun t => Complex.exp (Complex.I*z*L) *
        (Complex.exp (Complex.I*z*(u-t)) * pair c a b t s)) t := by
    have ho : MinusOrder L (fun _ : Fin 1 => u) (fun _ => t) ↔ t ∈ Ioo u L := by
      simp [MinusOrder, PlusOrder, hu.1]
    simp only [rawMinus, ho, Fin.sum_univ_one]
    by_cases ht : t ∈ Ioo u L
    · simp only [ht, ite_true, indicator_of_mem ht, ← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    · simp [ht]
  simp_rw [he]
  rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr (show Ioo u L ⊆ Icc 0 L from fun t ht => ⟨hu.1.le.trans ht.1.le, ht.2.le⟩),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hu.2.le,
    intervalIntegral.integral_const_mul]

/-- Both degree-one placements, before their normalized average. -/
def lowerDegree (L c a b x y : ℝ) (z : ℂ) : ℂ :=
  below c a b y x 0 y z + above c a b y x y x z +
    Complex.exp (Complex.I*z*L) * above c a b y x x L z +
    below c a b x y 0 y z +
    Complex.exp (Complex.I*z*L) *
      (below c a b x y y x z + above c a b x y x L z)

theorem lowerDegree_integrals {L x y : ℝ} (hy : 0 < y) (hyx : y < x) (hx : x < L)
    (c a b : ℝ) (z : ℂ) (ha : z ≠ (a : ℂ)) (hb : z ≠ (b : ℂ)) :
    ((∫ t in Icc 0 L, rawPlus L z (fun _ : Fin 1 => x) (fun _ => t) * pair c a b t y) +
      (∫ t in Icc 0 L, rawMinus L z (fun _ : Fin 1 => x) (fun _ => t) * pair c a b t y)) +
    ((∫ t in Icc 0 L, rawPlus L z (fun _ : Fin 1 => y) (fun _ => t) * pair c a b t x) +
      (∫ t in Icc 0 L, rawMinus L z (fun _ : Fin 1 => y) (fun _ => t) * pair c a b t x)) =
      lowerDegree L c a b x y z := by
  let f (u s : ℝ) := fun t : ℝ => Complex.exp (Complex.I*z*(u-t)) * pair c a b t s
  have hf (u s : ℝ) : Continuous (f u s) := by
    exact (by fun_prop : Continuous (fun t : ℝ => Complex.exp (Complex.I*z*(u-t)))).mul
      ((continuous_pair c a b).comp (continuous_id.prodMk continuous_const))
  have habove (u s lo hi : ℝ) (hs : s ≤ lo) (hh : lo ≤ hi) :
      (∫ t in lo..hi, f u s t) = above c a b s u lo hi z := by
    rw [← integral_above c a b s u lo hi z ha hb]
    apply intervalIntegral.integral_congr_Ioo_of_le hh
    intro t ht
    dsimp [f]
    rw [pair_of_le _ _ _ (hs.trans ht.1.le)]
  have hbelow (u s lo hi : ℝ) (hs : hi ≤ s) (hh : lo ≤ hi) :
      (∫ t in lo..hi, f u s t) = below c a b s u lo hi z := by
    rw [← integral_below c a b s u lo hi z ha hb]
    apply intervalIntegral.integral_congr_Ioo_of_le hh
    intro t ht
    dsimp [f]
    rw [pair_swap, pair_of_le _ _ _ (ht.2.le.trans hs)]
  rw [rawPlus_slice ⟨hy.trans hyx, hx⟩, rawMinus_slice ⟨hy.trans hyx, hx⟩,
    rawPlus_slice ⟨hy, hyx.trans hx⟩, rawMinus_slice ⟨hy, hyx.trans hx⟩]
  change (∫ t in 0..x, f x y t) + Complex.exp (Complex.I*z*L) * (∫ t in x..L, f x y t) +
    ((∫ t in 0..y, f y x t) + Complex.exp (Complex.I*z*L) * (∫ t in y..L, f y x t)) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals ((hf x y).intervalIntegrable 0 y)
      ((hf x y).intervalIntegrable y x),
    ← intervalIntegral.integral_add_adjacent_intervals ((hf y x).intervalIntegrable y x)
      ((hf y x).intervalIntegrable x L),
    hbelow x y 0 y le_rfl hy.le, habove x y y x le_rfl hyx.le,
    habove x y x L hyx.le hx.le, hbelow y x 0 y hyx.le hy.le,
    hbelow y x y x le_rfl hyx.le, habove y x x L le_rfl hx.le]
  unfold lowerDegree
  ring

/-- The four integrals are on the existing source-root wave, rather than a
supplied off-shell action. The two spectator choices are explicit. -/
theorem sourceRoots_lowerDegree_integrals {L c x y : ℝ} (hy : 0 < y) (hyx : y < x)
    (hx : x < L) (n : Fin 2 → ℤ) (z : ℂ)
    (hz : ∀ i, z ≠ (BetheSmooth.sourceRoots L n c i : ℂ)) :
    ((∫ t in Icc 0 L, rawPlus L z (fun _ : Fin 1 => x) (fun _ => t) *
        symmetricExtension L c n ![t,y]) +
      (∫ t in Icc 0 L, rawMinus L z (fun _ : Fin 1 => x) (fun _ => t) *
        symmetricExtension L c n ![t,y])) +
    ((∫ t in Icc 0 L, rawPlus L z (fun _ : Fin 1 => y) (fun _ => t) *
        symmetricExtension L c n ![t,x]) +
      (∫ t in Icc 0 L, rawMinus L z (fun _ : Fin 1 => y) (fun _ => t) *
        symmetricExtension L c n ![t,x])) =
      lowerDegree L c (BetheSmooth.sourceRoots L n c 0)
        (BetheSmooth.sourceRoots L n c 1) x y z := by
  simp_rw [symmetricExtension_two]
  exact lowerDegree_integrals hy hyx hx c _ _ z (hz 0) (hz 1)

end QuantumNLS.BetheTwoParticleAction

#print axioms QuantumNLS.BetheTwoParticleAction.pair
#print axioms QuantumNLS.BetheTwoParticleAction.pair_swap
#print axioms QuantumNLS.BetheTwoParticleAction.pair_of_le
#print axioms QuantumNLS.BetheTwoParticleAction.continuous_pair
#print axioms QuantumNLS.BetheTwoParticleAction.tuple_antitone
#print axioms QuantumNLS.BetheTwoParticleAction.symmetricExtension_two
#print axioms QuantumNLS.BetheTwoParticleAction.segment
#print axioms QuantumNLS.BetheTwoParticleAction.phase_integral
#print axioms QuantumNLS.BetheTwoParticleAction.above
#print axioms QuantumNLS.BetheTwoParticleAction.below
#print axioms QuantumNLS.BetheTwoParticleAction.integral_above
#print axioms QuantumNLS.BetheTwoParticleAction.integral_below
#print axioms QuantumNLS.BetheTwoParticleAction.rawPlus_slice
#print axioms QuantumNLS.BetheTwoParticleAction.rawMinus_slice
#print axioms QuantumNLS.BetheTwoParticleAction.lowerDegree
#print axioms QuantumNLS.BetheTwoParticleAction.lowerDegree_integrals
#print axioms QuantumNLS.BetheTwoParticleAction.sourceRoots_lowerDegree_integrals


import QuantumNLS.Reg013OCorrection
import QuantumNLS.Reg013OCells

/-! REG-013 (`lem:regularity-induction`, `fractional_moments.tex:610`), opus_tensor stage O4:
moment characterization, weighted-action continuity and the bounded-set clause at an order
`k < s ≤ k+1`, from the order-`k` hypotheses and the order-`s` identity of stage O2.

* `momentChar_of`: the three-way equivalence at order `s` ("the positive integral identity and
  the same cutoff argument therefore give the moment characterization").
* `weightedCont_of`: weighted-action continuity at order `s` ("Confinement then gives weighted
  action continuity"): `𝓜_{2s}` is continuous on `H^s` (identity, `Q_s` and `J_s` continuous),
  weak continuity turns this into uniform moment tails, confinement into uniform action tails.
* `boundedActions_of`: the bounded-set clause under the lower-moment hypothesis. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Fourier
open QuantumNLS.RootWeightedCellsR26 QuantumNLS.TranslatedCorrelation
open QuantumNLS.Reg015Setting QuantumNLS.Reg013OAnalysis QuantumNLS.Reg013OCorrection
open QuantumNLS.Reg013OCells
namespace QuantumNLS.Reg013OOrder
variable {L κ : ℝ} [Fact (0 < L)]

/-! ### Generic convergence helpers -/

theorem abs_sub_tendsto {ι : Type*} (x a : ℕ → ι → ℝ) (y b : ι → ℝ)
    (hx0 : ∀ j n, 0 ≤ x j n) (hy0 : ∀ n, 0 ≤ y n)
    (hxa : ∀ j n, x j n ≤ a j n) (hyb : ∀ n, y n ≤ b n)
    (ha0 : ∀ j n, 0 ≤ a j n) (hb0 : ∀ n, 0 ≤ b n)
    (has : ∀ j, Summable (a j)) (hbs : Summable b)
    (hpt : ∀ n, Tendsto (fun j => x j n) atTop (𝓝 (y n)))
    (htail : ∀ ε > 0, ∃ F : Finset ι, ∀ᶠ j in atTop, ∑' n : {n // n ∉ F}, a j n ≤ ε) :
    Tendsto (fun j => ∑' n, |x j n - y n|) atTop (𝓝 0) := by
  refine tsum_tendsto_zero_of_dom (fun j n => |x j n - y n|) a b zero_le_one
    (fun j n => abs_nonneg _) ha0 hb0 (fun j n => ?_) has hbs (fun n => ?_) htail
  · rw [one_mul, abs_le]
    constructor <;> linarith [hx0 j n, hy0 n, hxa j n, hyb n]
  · have h := ((hpt n).sub_const (y n)).abs
    simpa using h

theorem tsum_tendsto_of_abs {ι : Type*} (x : ℕ → ι → ℝ) (y : ι → ℝ)
    (hxs : ∀ j, Summable (x j)) (hys : Summable y)
    (h : Tendsto (fun j => ∑' n, |x j n - y n|) atTop (𝓝 0)) :
    Tendsto (fun j => ∑' n, x j n) atTop (𝓝 (∑' n, y n)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) h
  rw [← Summable.tsum_sub (hxs j) hys]
  exact (norm_tsum_le_tsum_norm ((hxs j).sub hys).norm).trans_eq (by simp [Real.norm_eq_abs])

theorem lp_coord_tendsto {f : ℕ → lp (fun _ : ℤ => ℂ) 2}
    {g : lp (fun _ : ℤ => ℂ) 2} (h : Tendsto f atTop (𝓝 g)) (n : ℤ) :
    Tendsto (fun j => (f j : ℤ → ℂ) n) atTop (𝓝 ((g : ℤ → ℂ) n)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) h
  have := lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) (f j - g) n
  simpa using this

/-! ### Elementary moment facts on finite measures -/

theorem shifted_integrable_iff (μ : Measure ℝ) [IsFiniteMeasure μ] {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun x : ℝ => (1+|x|)^(2*s)) μ ↔ Integrable (fun x : ℝ => |x|^(2*s)) μ := by
  have hm1 : AEStronglyMeasurable (fun x : ℝ => (1+|x|)^(2*s)) μ :=
    (by fun_prop : Measurable fun x : ℝ => (1+|x|)^(2*s)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun x : ℝ => |x|^(2*s)) μ :=
    (by fun_prop : Measurable fun x : ℝ => |x|^(2*s)).aestronglyMeasurable
  constructor
  · intro h
    refine h.mono' hm2 (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
    exact Real.rpow_le_rpow (abs_nonneg x) (by linarith) (by linarith)
  · intro h
    refine ((integrable_const (1:ℝ)).add h |>.const_mul (2^(2*s))).mono' hm1
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact one_add_rpow_le |x| (2*s) (abs_nonneg x) (by linarith)

theorem power_integrable_iff (μ : Measure ℝ) (s : ℝ) :
    Integrable (fun x : ℝ => |x|^(2*s)) μ ↔
      (∫⁻ x, ENNReal.ofReal (|x|^(2*s)) ∂μ) ≠ ⊤ :=
  (lintegral_ofReal_ne_top_iff_integrable
    (by fun_prop : Measurable fun x : ℝ => |x|^(2*s)).aestronglyMeasurable
    (ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg x) _)).symm

/-- `Integrable (1+|t|)^{2s} ↔ Summable (1+|p_n|)^{2s} I_n` (accepted weight comparison). -/
theorem moment_action_iff (hκ : 0 < κ) (u : L2T L) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
      Summable (fun n : ℤ => (1+|momentum L n|)^(2*s) *
        (QuantumNLS.RootIndexedMasses.masses hκ u).1 n) := by
  have hc := QuantumNLS.TerraMultiRound70ExtendedWeights.extended_weight_comparison hκ u (2*s)
    (by linarith)
  obtain ⟨h1, h2⟩ := hc
  rw [← lintegral_ofReal_ne_top_iff_integrable
      (by fun_prop : Measurable fun t : ℝ => (1+|t|)^(2*s)).aestronglyMeasurable
      (ae_of_all _ fun t => Real.rpow_nonneg (by positivity) _),
    ← tsum_ofReal_ne_top_iff _ (fun n => mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (masses_nonneg hκ u n))]
  constructor
  · intro h htop
    exact absurd (top_le_iff.mp (htop ▸ h2)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h)
  · intro h htop
    exact absurd (top_le_iff.mp (htop ▸ h1)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h)

theorem mono_val {s t : ℝ} (h : s ≤ t) (v : H02 L t) : (H02.mono h v).val = v.val :=
  fieldIncl_val _ _ _ _ v

/-! ### Moment characterization at order `s` -/

theorem momentChar_of (hκ : 0 < κ) {k : ℕ} (hmc : MomentChar (L := L) hκ k) {s : ℝ}
    (hs : (k:ℝ) < s) {Jc : Hk L k → ℝ} (hId : Identity hκ k s Jc) :
    MomentChar (L := L) hκ s := by
  have hs0 : 0 ≤ s := le_trans (Nat.cast_nonneg k) hs.le
  intro u
  refine ⟨?_, moment_action_iff hκ u hs0⟩
  rw [shifted_integrable_iff _ hs0, power_integrable_iff]
  constructor
  · rintro ⟨v, rfl⟩
    have hsum := (summable_weight_iff hs0 v.val).mp v.summable
    have h := (hId (H02.mono hs.le v)).1
    rw [mono_val] at h
    exact h.mpr hsum
  · intro hfin
    have hint : Integrable (fun x : ℝ => (1+|x|)^(2*(k:ℝ)))
        (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) := by
      have h1 := ((shifted_integrable_iff (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) hs0).mpr
        ((power_integrable_iff _ s).mpr hfin))
      refine h1.mono' (by fun_prop : Measurable fun x : ℝ => (1+|x|)^(2*(k:ℝ))).aestronglyMeasurable
        (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg x]) (by linarith)
    obtain ⟨w, hw⟩ := (hmc u).1.mpr hint
    rw [← hw] at hfin ⊢
    exact (mem_iff s w.val).mpr ((summable_weight_iff hs0 w.val).mpr ((hId w).1.mp hfin))

/-! ### The weighted action map at order `s` -/

theorem actions_summable (hκ : 0 < κ) {s : ℝ} (hmcs : MomentChar (L := L) hκ s) (u : H02 L s) :
    Summable (fun n : ℤ => (1+|momentum L n|)^(2*s) *
      (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n) :=
  (hmcs u.val).2.mp ((hmcs u.val).1.mp ⟨u, rfl⟩)

/-- The weighted action carrier at order `s`. -/
def Aof (hκ : 0 < κ) {s : ℝ} (hmcs : MomentChar (L := L) hκ s) (u : H02 L s) :
    lp (fun _ : ℤ => ℝ) 1 :=
  ⟨fun n => (1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n,
    memℓp_gen (by
      refine (actions_summable hκ hmcs u).congr (fun n => ?_)
      rw [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _)
          (masses_nonneg hκ u.val _))])⟩

theorem Aof_apply (hκ : 0 < κ) {s : ℝ} (hmcs : MomentChar (L := L) hκ s) (u : H02 L s) (n : ℤ) :
    Aof hκ hmcs u n = (1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n :=
  rfl

/-! ### Convergence along `H^s` convergent sequences -/

theorem val_tendsto {s : ℝ} (hs0 : 0 ≤ s) {us : ℕ → H02 L s} {u : H02 L s}
    (h : Tendsto us atTop (𝓝 u)) : Tendsto (fun j => (us j).val) atTop (𝓝 u.val) :=
  ((H02.toL2 (L := L) hs0).continuous.tendsto u).comp h

theorem coeff_tendsto {us : ℕ → L2T L} {u : L2T L} (h : Tendsto us atTop (𝓝 u)) (n : ℤ) :
    Tendsto (fun j => ‖fourierL2 L (us j) n‖^2) atTop (𝓝 (‖fourierL2 L u n‖^2)) := by
  have h1 : Tendsto (fun j => fourierL2 L (us j)) atTop (𝓝 (fourierL2 L u)) :=
    ((fourierL2 L).continuous.tendsto u).comp h
  exact ((continuous_norm.tendsto _).comp (lp_coord_tendsto h1 n)).pow 2

/-- Uniform tails of the `H^s` weights along an `H^s` convergent sequence. -/
theorem sobolev_tails {s : ℝ} (hs0 : 0 ≤ s) {us : ℕ → H02 L s} {u : H02 L s}
    (h : Tendsto us atTop (𝓝 u)) :
    ∀ ε > 0, ∃ F : Finset ℤ, ∀ᶠ j in atTop, ∑' n : {n // n ∉ F},
      (1+|momentum L n|)^(2*s) * ‖fourierL2 L (us j).val n‖^2 ≤ ε := by
  refine tails_of_tsum_tendsto _ _ (fun j => (us j).summable) u.summable
    (fun n => (coeff_tendsto (val_tendsto hs0 h) n).const_mul _) ?_
  have hn : Tendsto (fun j => ‖us j‖^2) atTop (𝓝 (‖u‖^2)) :=
    ((continuous_norm.tendsto u).comp h).pow 2
  simp_rw [WField.norm_sq_eq_tsum] at hn
  exact hn

/-- `Q_s` is continuous along `H^s` convergent sequences. -/
theorem Q_tendsto {s : ℝ} (hs0 : 0 ≤ s) {us : ℕ → H02 L s} {u : H02 L s}
    (h : Tendsto us atTop (𝓝 u)) :
    Tendsto (fun j => ∑' n : ℤ, |momentum L n|^(2*s) * ‖fourierL2 L (us j).val n‖^2) atTop
      (𝓝 (∑' n : ℤ, |momentum L n|^(2*s) * ‖fourierL2 L u.val n‖^2)) := by
  have hle : ∀ (v : H02 L s) (n : ℤ), |momentum L n|^(2*s) * ‖fourierL2 L v.val n‖^2 ≤
      (1+|momentum L n|)^(2*s) * ‖fourierL2 L v.val n‖^2 := fun v n =>
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (abs_nonneg _) (by linarith) (by linarith))
      (sq_nonneg _)
  have hnn : ∀ (v : H02 L s) (n : ℤ), 0 ≤ |momentum L n|^(2*s) * ‖fourierL2 L v.val n‖^2 :=
    fun v n => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _)
  have hsum : ∀ v : H02 L s, Summable fun n : ℤ => |momentum L n|^(2*s) * ‖fourierL2 L v.val n‖^2 :=
    fun v => v.summable.of_nonneg_of_le (hnn v) (hle v)
  refine tsum_tendsto_of_abs _ _ (fun j => hsum (us j)) (hsum u) ?_
  exact abs_sub_tendsto _ (fun j n => (1+|momentum L n|)^(2*s) * ‖fourierL2 L (us j).val n‖^2) _
    (fun n => (1+|momentum L n|)^(2*s) * ‖fourierL2 L u.val n‖^2)
    (fun j n => hnn _ n) (hnn u) (fun j n => hle _ n) (hle u)
    (fun j n => mul_nonneg (by positivity) (sq_nonneg _))
    (fun n => mul_nonneg (by positivity) (sq_nonneg _))
    (fun j => (us j).summable) u.summable
    (fun n => (coeff_tendsto (val_tendsto hs0 h) n).const_mul _) (sobolev_tails hs0 h)

/-- `𝓜_{2s}` is continuous along `H^s` convergent sequences. -/
theorem moment_tendsto (hκ : 0 < κ) {k : ℕ} {s : ℝ} (hks : (k:ℝ) ≤ s)
    {Jc : Hk L k → ℝ} (hJc : Continuous Jc) (hId : Identity hκ k s Jc)
    {us : ℕ → H02 L s} {u : H02 L s} (h : Tendsto us atTop (𝓝 u)) :
    Tendsto (fun j => ∫ x, |x|^(2*s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (us j).val))
      atTop (𝓝 (∫ x, |x|^(2*s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val))) := by
  have hs0 : 0 ≤ s := le_trans (Nat.cast_nonneg k) hks
  have hsum : ∀ v : H02 L s, Summable fun n : ℤ => |momentum L n|^(2*s) * ‖fourierL2 L v.val n‖^2 :=
    fun v => (summable_weight_iff hs0 v.val).mp v.summable
  have e : ∀ v : H02 L s, (∫ x, |x|^(2*s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v.val)) =
      (∑' n : ℤ, |momentum L n|^(2*s) * ‖fourierL2 L v.val n‖^2) + Jc (H02.mono hks v) :=
    fun v => by
      have h := (hId (H02.mono hks v)).2
      rw [mono_val] at h
      exact h (hsum v)
  simp_rw [e]
  exact (Q_tendsto hs0 h).add ((hJc.tendsto _).comp (((H02.mono hks).continuous.tendsto u).comp h))

/-! ### Weighted-action continuity at order `s` -/

theorem continuous_power (s : ℝ) (hs0 : 0 ≤ s) : Continuous (fun x : ℝ => |x|^(2*s)) :=
  continuous_abs.rpow_const (fun _ => Or.inr (by linarith))

theorem power_integrable (hκ : 0 < κ) {s : ℝ} (hs0 : 0 ≤ s) (hmcs : MomentChar (L := L) hκ s)
    (u : H02 L s) :
    Integrable (fun x : ℝ => |x|^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) :=
  (shifted_integrable_iff _ hs0).mp ((hmcs u.val).1.mp ⟨u, rfl⟩)

/-- Along an `H^s` convergent sequence the weighted actions have uniformly small tails. -/
theorem action_tails_of_Hs (hκ : 0 < κ) {k : ℕ} {s : ℝ} (hks : (k:ℝ) ≤ s)
    (hmcs : MomentChar (L := L) hκ s)
    {Jc : Hk L k → ℝ} (hJc : Continuous Jc) (hId : Identity hκ k s Jc)
    {us : ℕ → H02 L s} {u : H02 L s} (h : Tendsto us atTop (𝓝 u)) :
    ∀ ε > 0, ∃ F : Finset ℤ, ∀ᶠ j in atTop, ∑' n : {n // n ∉ F},
      (1 + |momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ (us j).val).1 n ≤ ε := by
  have hs0 : 0 ≤ s := le_trans (Nat.cast_nonneg k) hks
  obtain ⟨MU, hMU⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ h)
  refine action_tails hκ (fun j => (us j).val) (MU := MU)
    (fun j => (norm_val_le s hs0 (us j)).trans (hMU _ ⟨j, rfl⟩)) hs0
    (fun j => power_integrable hκ hs0 hmcs (us j)) (fun j => actions_summable hκ hmcs (us j)) ?_
  exact uniform_tail _ _ (weak_tendsto hκ (val_tendsto hs0 h)) _ (continuous_power s hs0)
    (fun x => Real.rpow_nonneg (abs_nonneg x) _) (fun j => power_integrable hκ hs0 hmcs (us j))
    (power_integrable hκ hs0 hmcs u) (moment_tendsto hκ hks hJc hId h)

theorem weightedCont_of (hκ : 0 < κ) {k : ℕ} {s : ℝ} (hks : (k:ℝ) ≤ s)
    (hmcs : MomentChar (L := L) hκ s)
    {Jc : Hk L k → ℝ} (hJc : Continuous Jc) (hId : Identity hκ k s Jc) :
    WeightedCont (L := L) hκ s := by
  have hs0 : 0 ≤ s := le_trans (Nat.cast_nonneg k) hks
  refine ⟨Aof hκ hmcs, Aof_apply hκ hmcs, ?_⟩
  rw [continuous_iff_seqContinuous]
  intro us u h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ j, ‖Aof hκ hmcs (us j) - Aof hκ hmcs u‖ =
      ∑' n, |Aof hκ hmcs (us j) n - Aof hκ hmcs u n| := fun j => by
    rw [lp_one_norm]; rfl
  have hw0 : ∀ (v : H02 L s) (n : ℤ), 0 ≤ (1+|momentum L n|)^(2*s) *
      (QuantumNLS.RootIndexedMasses.masses hκ v.val).1 n :=
    fun v n => mul_nonneg (by positivity) (masses_nonneg hκ _ n)
  have hcoord : ∀ n : ℤ, Tendsto (fun j => (1+|momentum L n|)^(2*s) *
      (QuantumNLS.RootIndexedMasses.masses hκ (us j).val).1 n) atTop
      (𝓝 ((1+|momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n)) :=
    fun n => ((((QuantumNLS.DEF014Continuity.continuous_physical_coordinate hκ n).tendsto
      u.val).comp (val_tendsto hs0 h))).const_mul _
  have key := abs_sub_tendsto _ _ _ _ (fun j => hw0 (us j)) (hw0 u) (fun j n => le_rfl)
    (fun n => le_rfl) (fun j => hw0 (us j)) (hw0 u) (fun j => actions_summable hκ hmcs (us j))
    (actions_summable hκ hmcs u) hcoord (action_tails_of_Hs hκ hks hmcs hJc hId h)
  refine key.congr (fun j => ?_)
  exact (hnorm j).symm

/-! ### The bounded-set clause at order `s` -/

theorem boundedActions_of (hκ : 0 < κ) {k : ℕ} {s : ℝ} (hks : (k:ℝ) < s)
    (hmcs : MomentChar (L := L) hκ s)
    {Jc : Hk L k → ℝ} (hId : Identity hκ k s Jc)
    (hJb : ∀ B : Set (Hk L k), Bornology.IsBounded B → ∃ M : ℝ, ∀ u ∈ B, |Jc u| ≤ M) :
    BoundedActions (L := L) hκ s := by
  have hs0 : 0 ≤ s := le_trans (Nat.cast_nonneg k) hks.le
  have hs1 : 0 < 2 * s := by
    have := Nat.cast_nonneg (α := ℝ) k; linarith
  refine ⟨Aof hκ hmcs, Aof_apply hκ hmcs, fun B hB => ?_⟩
  obtain ⟨MU, hMU⟩ := isBounded_iff_forall_norm_le.mp hB
  obtain ⟨MJ, hMJ⟩ := hJb ((H02.mono hks.le) '' B)
    ((H02.mono (L := L) hks.le).lipschitzWith.isBounded_image hB)
  set D := Drad κ L MU
  refine isBounded_iff_forall_norm_le.mpr ⟨(1+D)^(2*s) * (2^(2*s) * (MU^2 + (MU^2 + MJ))), ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have hMUu : ‖u‖ ≤ MU := hMU u hu
  have hval : ‖u.val‖ ≤ MU := (norm_val_le s hs0 u).trans hMUu
  set μ := QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val with hμ
  have : IsFiniteMeasure μ := QuantumNLS.PhysicalQuantumMeasure.finite_measure hκ u.val
  have hint := (hmcs u.val).1.mp ⟨u, rfl⟩
  have hpow := power_integrable hκ hs0 hmcs u
  rw [actions_norm hκ s (Aof hκ hmcs) (Aof_apply hκ hmcs) u]
  have hcmp := (QuantumNLS.TerraMultiRound70WeightComparison.physical_indexed_weight_bounds
    hκ u.val (2*s) hs1 hint).2
  have hD : 2 * Real.sqrt (κ * ‖u.val‖^2 / L) ≤ D := Drad_mono hκ (norm_nonneg _) hval
  have hDpos : 0 ≤ 2 * Real.sqrt (κ * ‖u.val‖^2 / L) := by positivity
  -- the shifted moment
  have hmass : μ.real univ = ‖u.val‖^2 := by
    rw [measureReal_def, hμ, QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas,
      QuantumNLS.FullMass.Mmeas_univ, ENNReal.toReal_ofReal (sq_nonneg _)]
  have hshift : (∫ t, (1+|t|)^(2*s) ∂μ) ≤ 2^(2*s) * (‖u.val‖^2 + ∫ t, |t|^(2*s) ∂μ) := by
    calc (∫ t, (1+|t|)^(2*s) ∂μ) ≤ ∫ t, 2^(2*s) * (1 + |t|^(2*s)) ∂μ :=
          integral_mono hint (((integrable_const (1:ℝ)).add hpow).const_mul _)
            (fun t => one_add_rpow_le |t| (2*s) (abs_nonneg t) (by linarith))
      _ = 2^(2*s) * ((∫ _t, (1:ℝ) ∂μ) + ∫ t, |t|^(2*s) ∂μ) := by
          rw [integral_const_mul, integral_add (integrable_const _) hpow]
      _ = 2^(2*s) * (‖u.val‖^2 + ∫ t, |t|^(2*s) ∂μ) := by
          rw [integral_const, smul_eq_mul, mul_one, hmass]
  have hmom : (∫ t, |t|^(2*s) ∂μ) ≤ MU^2 + MJ := by
    have hsum := (summable_weight_iff hs0 u.val).mp u.summable
    have hidu := (hId (H02.mono hks.le u)).2
    rw [mono_val, ← hμ] at hidu
    rw [hidu hsum]
    have hQ : (∑' n : ℤ, |momentum L n|^(2*s) * ‖fourierL2 L u.val n‖^2) ≤ ‖u‖^2 := by
      rw [WField.norm_sq_eq_tsum]
      exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (abs_nonneg _) (by unfold momentum; linarith) (by linarith))
        (sq_nonneg _)) hsum u.summable
    have hJ := hMJ _ ⟨u, hu, rfl⟩
    have hsq : ‖u‖^2 ≤ MU^2 := pow_le_pow_left₀ (norm_nonneg _) hMUu 2
    linarith [le_abs_self (Jc (H02.mono hks.le u))]
  have hsq : ‖u.val‖^2 ≤ MU^2 := pow_le_pow_left₀ (norm_nonneg _) hval 2
  have hint0 : 0 ≤ ∫ t, (1+|t|)^(2*s) ∂μ := integral_nonneg fun t => by positivity
  calc _ ≤ (1 + 2 * Real.sqrt (κ * ‖u.val‖^2 / L))^(2*s) * (∫ t, (1+|t|)^(2*s) ∂μ) := hcmp
    _ ≤ (1+D)^(2*s) * (2^(2*s) * (MU^2 + (MU^2 + MJ))) := by
        apply mul_le_mul (Real.rpow_le_rpow (by linarith) (by linarith) hs1.le) _ hint0
          (Real.rpow_nonneg (by linarith [Drad_nonneg hκ (L := L) MU]) _)
        refine hshift.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        linarith

end QuantumNLS.Reg013OOrder

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg013OOrder." ||
        n.toString.startsWith "_private.QuantumNLS.Reg013OOrder." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        if n.toString.endsWith "HeldGP14Tonelli" || n.toString.endsWith "RegularCut" then
          throwError "Held name in closure: {n}"
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Reg013OOrder aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."

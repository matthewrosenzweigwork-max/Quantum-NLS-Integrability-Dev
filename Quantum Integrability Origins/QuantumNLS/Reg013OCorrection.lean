import QuantumNLS.Reg015Setting
import QuantumNLS.Reg013OAnalysis

/-! REG-013 (`lem:regularity-induction`, `fractional_moments.tex:610`), opus_tensor stage O2:
the order-`s` identity on `H^k` with an `H^k`-continuous correction, `k < s ≤ k+1`.

For `k < s < k+1` the correction is the printed absolutely convergent integral
`J_s(u) = c_{s-k} ∫_0^∞ Y^{2s-2k-3} D_{k+1,u}(Y) dY`, written in the squared parameter
`t = Y²` (`J`, `E_eq`). Its integrability uses the small-`Y` bound
`Y²(𝓜_{2k}(u) + Q_k(u))` (from the order-`k` hypotheses) and the assumed large-`Y` bound
(`FiniteYAssertion`); its continuity uses the assumed fixed-`Y` continuity and dominated
convergence along `H^k` convergent sequences. At `s = k+1` the correction is the assumed `R`.
The vocabulary (`MomentChar`, `WeightedCont`, `IntegerAssertion`, `FiniteYAssertion`,
`LowerBounded`) is that of `Reg015Setting`, where `Reg013InductionInput` is stated. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Fourier
open QuantumNLS.RootWeightedCellsR26 QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound64ExtendedMeasure
open QuantumNLS.Reg015Setting QuantumNLS.Reg013OAnalysis
namespace QuantumNLS.Reg013OCorrection
variable {L κ : ℝ} [Fact (0 < L)]

/-! ### The free measure `Σ |û(n)|² δ_{p_n}` -/

theorem free_lintegral (u : L2T L) (g : ℝ → ℝ≥0∞) :
    ∫⁻ x, g x ∂(QuantumNLS.FreeLimit.freeMeasure L u) =
      ∑' n : ℤ, ENNReal.ofReal (‖fourierL2 L u n‖^2) * g (momentum L n) := by
  unfold QuantumNLS.FreeLimit.freeMeasure
  rw [lintegral_sum_measure]
  refine tsum_congr fun n => ?_
  rw [lintegral_smul_measure, lintegral_dirac, fourierL2_apply]
  rfl

instance free_isFinite (u : L2T L) : IsFiniteMeasure (QuantumNLS.FreeLimit.freeMeasure L u) := by
  refine ⟨?_⟩
  rw [← lintegral_one, free_lintegral]
  simp only [mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) (PosWeight.summable_sq_of_lp (fourierL2 L u))]
  exact ENNReal.ofReal_lt_top

theorem free_integral (u : L2T L) (f : ℝ → ℝ) (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hs : Summable fun n : ℤ => f (momentum L n) * ‖fourierL2 L u n‖^2) :
    Integrable f (QuantumNLS.FreeLimit.freeMeasure L u) ∧
      ∫ x, f x ∂(QuantumNLS.FreeLimit.freeMeasure L u) =
        ∑' n : ℤ, f (momentum L n) * ‖fourierL2 L u n‖^2 := by
  have hl : ∫⁻ x, ENNReal.ofReal (f x) ∂(QuantumNLS.FreeLimit.freeMeasure L u) =
      ENNReal.ofReal (∑' n : ℤ, f (momentum L n) * ‖fourierL2 L u n‖^2) := by
    rw [free_lintegral, ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (hf0 _) (sq_nonneg _)) hs]
    refine tsum_congr fun n => ?_
    rw [← ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
  have hint : Integrable f (QuantumNLS.FreeLimit.freeMeasure L u) := by
    rw [← lintegral_ofReal_ne_top_iff_integrable hfm.aestronglyMeasurable (ae_of_all _ hf0), hl]
    exact ENNReal.ofReal_ne_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hfm.aestronglyMeasurable, hl,
    ENNReal.toReal_ofReal (tsum_nonneg fun n => mul_nonneg (hf0 _) (sq_nonneg _))]

theorem free_power_lintegral (u : L2T L) (r : ℝ) :
    (∫⁻ x, ENNReal.ofReal (|x|^r) ∂(QuantumNLS.FreeLimit.freeMeasure L u)) ≠ ⊤ ↔
      Summable (fun n : ℤ => |momentum L n|^r * ‖fourierL2 L u n‖^2) := by
  rw [free_lintegral, ← tsum_ofReal_ne_top_iff _
    (fun n => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _))]
  have e : ∀ n : ℤ, ENNReal.ofReal (‖fourierL2 L u n‖^2) * ENNReal.ofReal (|momentum L n|^r) =
      ENNReal.ofReal (|momentum L n|^r * ‖fourierL2 L u n‖^2) := fun n => by
    rw [← ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
  simp_rw [e]

/-! ### Weights and Sobolev membership -/

omit [Fact (0 < L)] in
theorem weight_eq (s : ℝ) (n : ℤ) : (def002 L s).w n = (1 + |momentum L n|)^(2*s) := rfl

theorem mem_iff (s : ℝ) (u : L2T L) :
    (∃ v : H02 L s, v.val = u) ↔
      Summable (fun n : ℤ => (1 + |momentum L n|)^(2*s) * ‖fourierL2 L u n‖^2) := by
  constructor
  · rintro ⟨v, rfl⟩; exact v.summable
  · intro h; exact ⟨WField.mk u h, rfl⟩

theorem summable_weight_iff {s : ℝ} (hs : 0 ≤ s) (u : L2T L) :
    Summable (fun n : ℤ => (1 + |momentum L n|)^(2*s) * ‖fourierL2 L u n‖^2) ↔
      Summable (fun n : ℤ => |momentum L n|^(2*s) * ‖fourierL2 L u n‖^2) := by
  have hc := PosWeight.summable_sq_of_lp (fourierL2 L u)
  constructor
  · intro h
    refine h.of_nonneg_of_le (fun n => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
      (sq_nonneg _)) (fun n => mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (abs_nonneg _) (by linarith) (by linarith)) (sq_nonneg _))
  · intro h
    refine ((hc.add h).mul_left (2^(2*s))).of_nonneg_of_le
      (fun n => mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)) (fun n => ?_)
    have := one_add_rpow_le |momentum L n| (2*s) (abs_nonneg _) (by linarith)
    have h2 := sq_nonneg ‖fourierL2 L u n‖
    calc (1 + |momentum L n|)^(2*s) * ‖fourierL2 L u n‖^2
        ≤ 2^(2*s) * (1 + |momentum L n|^(2*s)) * ‖fourierL2 L u n‖^2 :=
          mul_le_mul_of_nonneg_right this h2
      _ = 2^(2*s) * (‖(fourierL2 L u : ℤ → ℂ) n‖^2 +
            |momentum L n|^(2*s) * ‖fourierL2 L u n‖^2) := by ring

theorem rpow_two_mul_natCast (k : ℕ) (x : ℝ) :
    |x|^(2*(k:ℝ)) = x^(2*k) := by
  rw [show 2*(k:ℝ) = ((2*k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
    (even_two_mul k).pow_abs]

theorem pow_le_weight (k : ℕ) (x : ℝ) : x^(2*k) ≤ (1+|x|)^(2*(k:ℝ)) := by
  rw [show 2*(k:ℝ) = ((2*k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
    ← (even_two_mul k).pow_abs]
  exact pow_le_pow_left₀ (abs_nonneg x) (by linarith) _

theorem phys_moment_integrable (hκ : 0 < κ) {k : ℕ} (hmc : MomentChar (L := L) hκ k)
    (u : Hk L k) :
    Integrable (fun x : ℝ => x^(2*k)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) := by
  have h := (hmc u.val).1.mp ⟨u, rfl⟩
  refine h.mono' (by fun_prop : Measurable fun x : ℝ => x^(2*k)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg ((even_two_mul k).pow_nonneg x)]
  exact pow_le_weight k x

theorem free_moment (k : ℕ) (u : Hk L k) :
    Integrable (fun x : ℝ => x^(2*k)) (QuantumNLS.FreeLimit.freeMeasure L u.val) ∧
      (∫ x, x^(2*k) ∂(QuantumNLS.FreeLimit.freeMeasure L u.val)) ≤ ‖u‖^2 := by
  have hs : Summable fun n : ℤ => (momentum L n)^(2*k) * ‖fourierL2 L u.val n‖^2 :=
    u.summable.of_nonneg_of_le (fun n => mul_nonneg ((even_two_mul k).pow_nonneg _) (sq_nonneg _))
      (fun n => mul_le_mul_of_nonneg_right (pow_le_weight k _) (sq_nonneg _))
  obtain ⟨h1, h2⟩ := free_integral u.val (fun x => x^(2*k)) (by fun_prop)
    (fun x => (even_two_mul k).pow_nonneg x) hs
  refine ⟨h1, ?_⟩
  rw [h2, WField.norm_sq_eq_tsum]
  exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (pow_le_weight k _)
    (sq_nonneg _)) hs u.summable

/-! ### The printed difference `D_{k+1,u}(Y)` and the correction -/

/-- `D_{k+1,u}(Y)`, literally as in `FiniteYAssertion`. -/
def Dfun (hκ : 0 < κ) (k : ℕ) (u : Hk L k) (Y : ℝ) : ℝ :=
  (∫ t : ℝ, Y ^ 2 * t ^ (2 * (k+1)) / (Y ^ 2 + t ^ 2)
      ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) -
    ∑' n : ℤ, Y ^ 2 * (momentum L n) ^ (2 * (k+1)) /
      (Y ^ 2 + (momentum L n) ^ 2) * ‖QuantumNLS.Fourier.coeff L u.val n‖ ^ 2

/-- The kernel difference in the squared parameter `t = Y²`. -/
def E (hκ : 0 < κ) (k : ℕ) (α : ℝ) (u : Hk L k) (t : ℝ) : ℝ :=
  P k α (QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) t -
    P k α (QuantumNLS.FreeLimit.freeMeasure L u.val) t

/-- The correction `J_s(u) = C_α⁻¹ ∫_0^∞ E_u(t) dt`, `α = s - k`. -/
def J (hκ : 0 < κ) (k : ℕ) (α : ℝ) (u : Hk L k) : ℝ :=
  (∫ t in Ioi 0, E hκ k α u t) / Cα α

theorem E_eq (hκ : 0 < κ) (k : ℕ) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) (u : Hk L k) {t : ℝ}
    (ht : 0 < t) : E hκ k α u t = t^(α-2) * Dfun hκ k u (Real.sqrt t) := by
  have hs : Summable fun n : ℤ => K k (Real.sqrt t) (momentum L n) * ‖fourierL2 L u.val n‖^2 :=
    ((u.summable.mul_left (Real.sqrt t ^ 2))).of_nonneg_of_le
      (fun n => mul_nonneg (K_nonneg _ _ _) (sq_nonneg _))
      (fun n => by
        rw [← mul_assoc]
        refine mul_le_mul_of_nonneg_right ((K_le k _ _).trans ?_) (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left (pow_le_weight k _) (sq_nonneg _))
  have hfree := (free_integral u.val (K k (Real.sqrt t)) (K_measurable k _)
    (K_nonneg k _) hs).2
  unfold E
  rw [P_eq_K k hα _ ht, P_eq_K k hα _ ht, hfree, ← mul_sub]
  congr 1
  unfold Dfun
  congr 1
  refine tsum_congr fun n => ?_
  rw [fourierL2_apply]; rfl

theorem E_measurable (hκ : 0 < κ) (k : ℕ) (α : ℝ) (u : Hk L k) :
    StronglyMeasurable (E hκ k α u) :=
  (P_measurable k α _).sub (P_measurable k α _)

/-- The two-regime domination of `E_u`. -/
theorem E_le_majorant (hκ : 0 < κ) {k : ℕ} {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1)
    (hmc : MomentChar (L := L) hκ k) (u : Hk L k) {A C Y₀ : ℝ} (hY₀ : 0 < Y₀)
    (hA : (∫ x, x^(2*k) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) +
      (∫ x, x^(2*k) ∂(QuantumNLS.FreeLimit.freeMeasure L u.val)) ≤ A)
    (hC : ∀ Y : ℝ, Y₀ ≤ Y → |Dfun hκ k u Y| ≤ C) {t : ℝ} (ht : 0 < t) :
    ‖E hκ k α u t‖ ≤ majorant α A C (Y₀^2) t := by
  apply le_majorant (f := E hκ k α u) (t := t)
  · refine (abs_P_sub_le k hα (phys_moment_integrable hκ hmc u) (free_moment k u).1 ht.le).trans ?_
    exact mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg ht.le _)
  · intro hT
    rw [E_eq hκ k hα u ht, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _), mul_comm C]
    refine mul_le_mul_of_nonneg_left (hC _ ?_) (Real.rpow_nonneg ht.le _)
    exact (Real.lt_sqrt hY₀.le).mpr hT |>.le

theorem E_integrable (hκ : 0 < κ) {k : ℕ} {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1)
    (hmc : MomentChar (L := L) hκ k) (hfy : FiniteYAssertion (L := L) hκ k) (u : Hk L k) :
    IntegrableOn (E hκ k α u) (Ioi 0) := by
  obtain ⟨C, Y₀, -, hY₀, hC⟩ := hfy.2 {u} Bornology.isBounded_singleton
  refine Integrable.mono' (majorant_integrable hα
    ((∫ x, x^(2*k) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) +
      (∫ x, x^(2*k) ∂(QuantumNLS.FreeLimit.freeMeasure L u.val))) C (by positivity : 0 < Y₀^2))
    (E_measurable hκ k α u).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact E_le_majorant hκ hα hmc u hY₀ le_rfl (fun Y hY => hC u rfl Y hY) ht

/-- The order-`s` identity on `H^k` for `k < s < k+1` (`s = k + α`). -/
theorem frac_identity (hκ : 0 < κ) {k : ℕ} {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1)
    (hmc : MomentChar (L := L) hκ k) (hfy : FiniteYAssertion (L := L) hκ k) (u : Hk L k) :
    ((∫⁻ x, ENNReal.ofReal (|x|^(2*((k:ℝ)+α)))
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) ≠ ⊤ ↔
      Summable (fun n : ℤ => |momentum L n|^(2*((k:ℝ)+α)) * ‖fourierL2 L u.val n‖^2)) ∧
    (Summable (fun n : ℤ => |momentum L n|^(2*((k:ℝ)+α)) * ‖fourierL2 L u.val n‖^2) →
      (∫ x, |x|^(2*((k:ℝ)+α)) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) =
        (∑' n : ℤ, |momentum L n|^(2*((k:ℝ)+α)) * ‖fourierL2 L u.val n‖^2) + J hκ k α u) := by
  have hc := criterion k hα _ _ (phys_moment_integrable hκ hmc u) (free_moment k u).1
    (E_integrable hκ hα hmc hfy u)
  refine ⟨hc.1.trans (free_power_lintegral u.val _), fun hsum => ?_⟩
  rw [hc.2 ((free_power_lintegral u.val _).mpr hsum)]
  rw [(free_integral u.val (fun x => |x|^(2*((k:ℝ)+α))) (by fun_prop)
    (fun x => Real.rpow_nonneg (abs_nonneg x) _) hsum).2]
  rfl

/-! ### Uniform bounds along bounded sets -/

theorem norm_val_le (s : ℝ) (hs : 0 ≤ s) (u : H02 L s) : ‖u.val‖ ≤ ‖u‖ :=
  WField.norm_val_le (one_le_def002 L hs) u

/-- Physical `2k` moments are bounded on a set where the order-`k` actions are bounded. -/
theorem phys_moment_bound (hκ : 0 < κ) {k : ℕ} (hmc : MomentChar (L := L) hκ k)
    (A : H02 L k → lp (fun _ : ℤ => ℝ) 1)
    (hA : ∀ u n, A u n = (1+|momentum L n|)^(2*(k:ℝ)) *
      (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n)
    {MU MA : ℝ} (u : Hk L k) (hu : ‖u‖ ≤ MU) (hAu : ‖A u‖ ≤ MA) :
    (∫ x, x^(2*k) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) ≤
      (1 + 2 * Real.sqrt (κ * MU^2 / L))^(2*(k:ℝ)) * MA := by
  have hint := (hmc u.val).1.mp ⟨u, rfl⟩
  have hsum := (hmc u.val).2.mp hint
  have h := moment_le_actions hκ u.val k (by positivity) hint hsum
  rw [← actions_norm hκ k A hA u] at h
  simp_rw [rpow_two_mul_natCast] at h
  refine h.trans ?_
  have hL : 0 < L := Fact.out
  have h0 : 0 ≤ ‖u.val‖ := norm_nonneg _
  have h1 : ‖u.val‖ ≤ MU := (norm_val_le _ (by positivity) u).trans hu
  have hsq : Real.sqrt (κ * ‖u.val‖^2 / L) ≤ Real.sqrt (κ * MU^2 / L) := by
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ hL.le
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 2) hκ.le
  apply mul_le_mul (Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)) hAu
    (norm_nonneg _) (by positivity)

/-- `J` is continuous on `H^k` (dominated convergence; fixed-`Y` continuity, small-`Y` bound
from the order-`k` hypotheses, large-`Y` bound on the bounded range of the sequence). -/
theorem J_continuous (hκ : 0 < κ) {k : ℕ} {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1)
    (hmc : MomentChar (L := L) hκ k) (hwc : WeightedCont (L := L) hκ k)
    (hfy : FiniteYAssertion (L := L) hκ k) : Continuous (J (L := L) hκ k α) := by
  rw [continuous_iff_seqContinuous]
  intro us u hus
  obtain ⟨A, hA, hAc⟩ := hwc
  have hAt : Tendsto (fun j => A (us j)) atTop (𝓝 (A u)) := (hAc.tendsto u).comp hus
  obtain ⟨MA, hMA⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto _ hAt)
  obtain ⟨MU, hMU⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto _ hus)
  obtain ⟨C, Y₀, -, hY₀, hC⟩ := hfy.2 (range us) (Metric.isBounded_range_of_tendsto _ hus)
  set Mμ := (1 + 2 * Real.sqrt (κ * MU^2 / L))^(2*(k:ℝ)) * MA
  have hdom : ∀ j, ∀ t ∈ Ioi (0:ℝ), ‖E hκ k α (us j) t‖ ≤ majorant α (Mμ + MU^2) C (Y₀^2) t := by
    intro j t ht
    refine E_le_majorant hκ hα hmc (us j) hY₀ ?_ (fun Y hY => hC (us j) ⟨j, rfl⟩ Y hY) ht
    have h1 := phys_moment_bound hκ hmc A hA (us j) (hMU _ ⟨j, rfl⟩) (hMA _ ⟨j, rfl⟩)
    have h2 := (free_moment k (us j)).2
    have h3 : ‖us j‖^2 ≤ MU^2 := pow_le_pow_left₀ (norm_nonneg _) (hMU _ ⟨j, rfl⟩) 2
    linarith
  unfold J
  apply Tendsto.div_const
  apply tendsto_integral_of_dominated_convergence (majorant α (Mμ + MU^2) C (Y₀^2))
  · exact fun j => (E_measurable hκ k α (us j)).aestronglyMeasurable
  · exact majorant_integrable hα _ _ (by positivity)
  · intro j
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hdom j t ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp_rw [E_eq hκ k hα _ ht]
    exact (((hfy.1 (Real.sqrt t) (Real.sqrt_pos.mpr ht)).tendsto u).comp hus).const_mul _

/-- `J` is bounded on bounded subsets of `H^k` under the lower-moment hypothesis. -/
theorem J_bounded (hκ : 0 < κ) {k : ℕ} {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1)
    (hmc : MomentChar (L := L) hκ k) (hfy : FiniteYAssertion (L := L) hκ k)
    (R : Hk L k → ℝ) (hlb : LowerBounded (L := L) hκ k R)
    (B : Set (Hk L k)) (hB : Bornology.IsBounded B) :
    ∃ M : ℝ, ∀ u ∈ B, |J hκ k α u| ≤ M := by
  obtain ⟨C₁, hC₁⟩ := hlb.1 k (Nat.cast_nonneg k) le_rfl B hB
  obtain ⟨MU, hMU⟩ := isBounded_iff_forall_norm_le.mp hB
  obtain ⟨C, Y₀, -, hY₀, hC⟩ := hfy.2 B hB
  refine ⟨(∫ t in Ioi 0, majorant α (C₁ + MU^2) C (Y₀^2) t) / Cα α, fun u hu => ?_⟩
  unfold J
  rw [abs_div, abs_of_pos (Cα_pos hα)]
  apply div_le_div_of_nonneg_right _ (Cα_pos hα).le
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (majorant_integrable hα _ _ (by positivity)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  refine E_le_majorant hκ hα hmc u hY₀ ?_ (fun Y hY => hC u hu Y hY) ht
  have h1 := hC₁ u hu
  simp_rw [rpow_two_mul_natCast] at h1
  have h2 := (free_moment k u).2
  have h3 : ‖u‖^2 ≤ MU^2 := pow_le_pow_left₀ (norm_nonneg _) (hMU u hu) 2
  linarith

/-! ### The unified order-`s` identity, `k < s ≤ k+1` -/

/-- The order-`s` identity on `H^k` with correction `J`: `𝓜_{2s}(u) < ∞ ⟺ Q_s(u) < ∞`, and then
`𝓜_{2s}(u) = Q_s(u) + J(u)`. -/
def Identity (hκ : 0 < κ) (k : ℕ) (s : ℝ) (Jc : Hk L k → ℝ) : Prop :=
  ∀ u : Hk L k,
    ((∫⁻ x, ENNReal.ofReal (|x|^(2*s)) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) ≠ ⊤ ↔
      Summable (fun n : ℤ => |momentum L n|^(2*s) * ‖fourierL2 L u.val n‖^2)) ∧
    (Summable (fun n : ℤ => |momentum L n|^(2*s) * ‖fourierL2 L u.val n‖^2) →
      (∫ x, |x|^(2*s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) =
        (∑' n : ℤ, |momentum L n|^(2*s) * ‖fourierL2 L u.val n‖^2) + Jc u)

theorem ennrealToWithTop_eq_top (a : ℝ≥0∞) : ennrealToWithTop a = ⊤ ↔ a = ⊤ := by
  unfold ennrealToWithTop
  by_cases h : a = ⊤ <;> simp [h]

theorem ennrealToWithTop_of_ne (a : ℝ≥0∞) (h : a ≠ ⊤) : ennrealToWithTop a = ↑a.toReal := by
  unfold ennrealToWithTop; simp [h]

/-- At `s = k+1` the identity is the assumed extended identity with correction `R`. -/
theorem integer_identity (hκ : 0 < κ) {k : ℕ} (R : Hk L k → ℝ)
    (hIA : IntegerAssertion (L := L) hκ k R) : Identity hκ k ((k:ℝ)+1) R := by
  intro u
  have e1 : ∀ x : ℝ, |x|^(2*((k:ℝ)+1)) = x^(2*(k+1)) := fun x => by
    rw [show 2*((k:ℝ)+1) = ((2*(k+1) : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
      (even_two_mul (k+1)).pow_abs]
  have e2 : ∀ n : ℤ, |momentum L n|^(2*((k:ℝ)+1)) * ‖fourierL2 L u.val n‖^2 =
      (momentum L n)^(2*(k+1)) * ‖QuantumNLS.Fourier.coeff L u.val n‖^2 := fun n => by
    rw [e1, fourierL2_apply]
  have f1 : (fun n : ℤ => |momentum L n|^(2*((k:ℝ)+1)) * ‖fourierL2 L u.val n‖^2) =
      fun n : ℤ => (momentum L n)^(2*(k+1)) * ‖QuantumNLS.Fourier.coeff L u.val n‖^2 :=
    funext e2
  have f2 : (fun x : ℝ => ENNReal.ofReal (|x|^(2*((k:ℝ)+1)))) =
      fun x : ℝ => ENNReal.ofReal (x^(2*(k+1))) := funext fun x => by rw [e1]
  have f3 : (fun x : ℝ => |x|^(2*((k:ℝ)+1))) = fun x : ℝ => x^(2*(k+1)) := funext e1
  rw [f1, f2, f3]
  have hid := hIA.2.2 u
  set a := ∫⁻ t : ℝ, ENNReal.ofReal (t^(2*(k+1)))
    ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) with ha
  set b := ∑' n : ℤ, ENNReal.ofReal ((momentum L n)^(2*(k+1)) *
    ‖QuantumNLS.Fourier.coeff L u.val n‖^2) with hb
  have hnn : ∀ n : ℤ, 0 ≤ (momentum L n)^(2*(k+1)) * ‖QuantumNLS.Fourier.coeff L u.val n‖^2 :=
    fun n => mul_nonneg ((even_two_mul (k+1)).pow_nonneg _) (sq_nonneg _)
  have hbs : b ≠ ⊤ ↔ Summable (fun n : ℤ =>
      (momentum L n)^(2*(k+1)) * ‖QuantumNLS.Fourier.coeff L u.val n‖^2) :=
    tsum_ofReal_ne_top_iff _ hnn
  have hab : a ≠ ⊤ ↔ b ≠ ⊤ := by
    constructor
    · intro h hbt
      rw [ennrealToWithTop_of_ne a h, (ennrealToWithTop_eq_top b).mpr hbt, WithTop.top_add] at hid
      exact WithTop.coe_ne_top hid
    · intro h hat
      rw [(ennrealToWithTop_eq_top a).mpr hat, ennrealToWithTop_of_ne b h] at hid
      exact WithTop.coe_ne_top (by rw [← WithTop.coe_add] at hid; exact hid.symm)
  refine ⟨hab.trans hbs, fun hsum => ?_⟩
  have hbt := hbs.mpr hsum
  have hat := hab.mpr hbt
  rw [ennrealToWithTop_of_ne a hat, ennrealToWithTop_of_ne b hbt, ← WithTop.coe_add,
    WithTop.coe_inj] at hid
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x^(2*(k+1)))
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val) :=
    (by fun_prop : Measurable fun x : ℝ => x^(2*(k+1))).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => (even_two_mul (k+1)).pow_nonneg x)
    hmeas, ← ha, hid, hb, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  simp_rw [ENNReal.toReal_ofReal (hnn _)]

/-- **The order-`s` identity for every `k < s ≤ k+1`**, with an `H^k`-continuous correction,
bounded on bounded sets under the lower-moment hypothesis. -/
theorem identity_exists (hκ : 0 < κ) {k : ℕ}
    (hmc : MomentChar (L := L) hκ k) (hwc : WeightedCont (L := L) hκ k)
    (R : Hk L k → ℝ) (hIA : IntegerAssertion (L := L) hκ k R)
    (hfy : FiniteYAssertion (L := L) hκ k) {s : ℝ} (hs : (k:ℝ) < s) (hs' : s ≤ (k:ℝ)+1) :
    ∃ Jc : Hk L k → ℝ, Continuous Jc ∧ Identity hκ k s Jc ∧
      (LowerBounded (L := L) hκ k R → ∀ B : Set (Hk L k), Bornology.IsBounded B →
        ∃ M : ℝ, ∀ u ∈ B, |Jc u| ≤ M) := by
  rcases hs'.lt_or_eq with hlt | heq
  · have hα : s - k ∈ Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
    refine ⟨J hκ k (s-k), J_continuous hκ hα hmc hwc hfy, fun u => ?_,
      fun hlb B hB => J_bounded hκ hα hmc hfy R hlb B hB⟩
    have h := frac_identity hκ hα hmc hfy u
    rwa [show (k:ℝ) + (s - k) = s by ring] at h
  · subst heq
    exact ⟨R, hIA.2.1, integer_identity hκ R hIA, fun hlb B hB => hlb.2 B hB⟩

end QuantumNLS.Reg013OCorrection

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg013OCorrection." ||
        n.toString.startsWith "_private.QuantumNLS.Reg013OCorrection." then
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
  Lean.logInfo m!"Reg013OCorrection aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."

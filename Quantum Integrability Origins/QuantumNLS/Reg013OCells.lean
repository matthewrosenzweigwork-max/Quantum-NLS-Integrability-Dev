import QuantumNLS.Reg015Setting
import QuantumNLS.Reg013OAnalysis

/-! REG-013 (`lem:regularity-induction`, `fractional_moments.tex:610`), opus_tensor stage O3:
confinement ("Confinement then gives weighted action continuity as above").

* Convergence of nonnegative sequences from coordinatewise convergence and uniform tails.
* Weak continuity of `u ↦ M_u` on `L²` (accepted `FullMassLimit.continuous_Mfin`).
* Root-label confinement on tails (accepted cell displacement bound): tails of the weighted
  indexed actions are controlled by tails of the shifted moment and conversely, uniformly along
  `L²`-bounded sequences. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Fourier
open QuantumNLS.RootWeightedCellsR26 QuantumNLS.RootWeightedMomentsR26
open QuantumNLS.TerraMultiRound60IndexedMoment QuantumNLS.TerraMultiRound70WeightComparison
open QuantumNLS.Reg013OAnalysis
namespace QuantumNLS.Reg013OCells
variable {L κ : ℝ} [Fact (0 < L)]

/-! ### Sequences -/

theorem tail_anti {ι : Type*} {F G : Finset ι} (hFG : F ⊆ G) {a : ι → ℝ} (ha0 : ∀ n, 0 ≤ a n)
    (ha : Summable a) : ∑' n : {n // n ∉ G}, a n ≤ ∑' n : {n // n ∉ F}, a n := by
  have e : ∀ H : Finset ι, (∑' n : {n // n ∉ H}, a n) = ∑' n, ({n | n ∉ H} : Set ι).indicator a n :=
    fun H => tsum_subtype ({n | n ∉ H} : Set ι) a
  rw [e, e]
  refine Summable.tsum_le_tsum (fun n => ?_) (ha.indicator _) (ha.indicator _)
  exact indicator_le_indicator_of_subset (fun n (hn : n ∉ G) (hF : n ∈ F) => hn (hFG hF)) ha0 n

theorem tail_le {ι : Type*} {F : Finset ι} {a b : ι → ℝ} (ha0 : ∀ n, 0 ≤ a n)
    (hab : ∀ n, a n ≤ b n) (hb : Summable b) :
    ∑' n : {n // n ∉ F}, a n ≤ ∑' n : {n // n ∉ F}, b n :=
  Summable.tsum_le_tsum (fun n => hab n) ((hb.of_nonneg_of_le ha0 hab).subtype _) (hb.subtype _)

/-- A nonnegative sequence dominated by `C (a_j + b)` tends to zero in sum when it tends to zero
coordinatewise and the `a_j` have uniformly small tails. -/
theorem tsum_tendsto_zero_of_dom {ι : Type*} (c a : ℕ → ι → ℝ) (b : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hc0 : ∀ j n, 0 ≤ c j n) (ha0 : ∀ j n, 0 ≤ a j n) (hb0 : ∀ n, 0 ≤ b n)
    (hcd : ∀ j n, c j n ≤ C * (a j n + b n))
    (has : ∀ j, Summable (a j)) (hbs : Summable b)
    (hpt : ∀ n, Tendsto (fun j => c j n) atTop (𝓝 0))
    (htail : ∀ ε > 0, ∃ F : Finset ι, ∀ᶠ j in atTop, ∑' n : {n // n ∉ F}, a j n ≤ ε) :
    Tendsto (fun j => ∑' n, c j n) atTop (𝓝 0) := by
  classical
  have hsd : ∀ j, Summable (fun n => C * (a j n + b n)) := fun j => ((has j).add hbs).mul_left C
  have hcs : ∀ j, Summable (c j) := fun j => (hsd j).of_nonneg_of_le (hc0 j) (hcd j)
  refine tendsto_tsum_zero_of_tails c hc0 hcs hpt (fun ε hε => ?_)
  set δ := ε / (2 * (C + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨F₁, hF₁⟩ := htail δ hδ0
  obtain ⟨F₂, hF₂⟩ := eventually_atTop.mp
    ((tendsto_tsum_compl_atTop_zero b).eventually (gt_mem_nhds hδ0))
  refine ⟨F₁ ∪ F₂, ?_⟩
  filter_upwards [hF₁] with j hj
  have h1 := tail_le (F := F₁ ∪ F₂) (hc0 j) (hcd j) (hsd j)
  have h2 : (∑' n : {n // n ∉ F₁ ∪ F₂}, C * (a j n + b n)) =
      C * ((∑' n : {n // n ∉ F₁ ∪ F₂}, a j n) + ∑' n : {n // n ∉ F₁ ∪ F₂}, b n) := by
    rw [tsum_mul_left]; congr 1
    exact Summable.tsum_add ((has j).comp_injective Subtype.val_injective)
      (hbs.comp_injective Subtype.val_injective)
  have h3 := tail_anti (F := F₁) (G := F₁ ∪ F₂) Finset.subset_union_left (ha0 j) (has j)
  have h4 := hF₂ (F₁ ∪ F₂) Finset.subset_union_right
  have h5 : 0 ≤ ∑' n : {n // n ∉ F₁ ∪ F₂}, b n := tsum_nonneg fun n => hb0 n
  have h6 : C * ((∑' n : {n // n ∉ F₁ ∪ F₂}, a j n) + ∑' n : {n // n ∉ F₁ ∪ F₂}, b n) ≤
      C * (2 * δ) := mul_le_mul_of_nonneg_left (by linarith) hC
  have h7 : C * (2 * δ) ≤ ε := by
    rw [hδ]; field_simp; nlinarith
  linarith

theorem tail_ofReal_le (a : ℤ → ℝ) (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (F : Finset ℤ)
    (c : ℤ → Prop) [DecidablePred c] (hc : ∀ n, n ∉ F → c n) :
    ENNReal.ofReal (∑' n : {n // n ∉ F}, a n) ≤
      ∑' n : ℤ, ENNReal.ofReal (if c n then a n else 0) := by
  rw [ENNReal.ofReal_tsum_of_nonneg (f := fun n : {n // n ∉ F} => a n.1) (fun n => ha n.1)
    (hs.comp_injective Subtype.val_injective)]
  refine le_trans (ENNReal.tsum_le_tsum fun n => ?_)
    (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
      (fun n => ENNReal.ofReal (if c n then a n else 0)))
  rw [ite_eq_left_of_eq_true _ _ (eq_true (hc n.1 n.2))]

theorem tail_ofReal_ge (a : ℤ → ℝ) (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (F : Finset ℤ)
    (c : ℤ → Prop) [DecidablePred c] (hc : ∀ n, c n → n ∉ F) :
    ∑' n : ℤ, ENNReal.ofReal (if c n then a n else 0) ≤
      ENNReal.ofReal (∑' n : {n // n ∉ F}, a n) := by
  rw [ENNReal.ofReal_tsum_of_nonneg (f := fun n : {n // n ∉ F} => a n.1) (fun n => ha n.1)
    (hs.comp_injective Subtype.val_injective)]
  have hsupp : Function.support (fun n : ℤ => ENNReal.ofReal (if c n then a n else 0)) ⊆
      {n | n ∉ F} := by
    intro n hn
    by_contra h
    have : ¬ c n := fun hcn => h (hc n hcn)
    exact hn (by simp [this])
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  refine ENNReal.tsum_le_tsum fun n => ?_
  split_ifs <;> simp

/-! ### Weak continuity of the physical measures -/

theorem weak_tendsto (hκ : 0 < κ) {us : ℕ → L2T L} {u : L2T L} (h : Tendsto us atTop (𝓝 u))
    (g : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun j => ∫ x, g x ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (us j))) atTop
      (𝓝 (∫ x, g x ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u))) := by
  have hT : Tendsto (fun j => QuantumNLS.FullMass.Mfin κ (us j)) atTop
      (𝓝 (QuantumNLS.FullMass.Mfin κ u)) :=
    ((QuantumNLS.FullMassLimit.continuous_Mfin (L := L)).tendsto (⟨κ, hκ.le⟩, u)).comp
      (tendsto_const_nhds.prodMk_nhds h)
  have := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hT) g
  simp_rw [QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas]
  exact this

/-! ### Confinement on tails -/

theorem cell_lintegral (hκ : 0 < κ) (u : L2T L) (g : ℤ → ℝ≥0∞) :
    ∫⁻ t, g (cellIndex hκ u t) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u) =
      ∑' n, g n * ENNReal.ofReal ((QuantumNLS.RootIndexedMasses.masses hκ u).1 n) := by
  have : IsFiniteMeasure (indexLaw hκ u) := by unfold indexLaw; infer_instance
  rw [← lintegral_map (Measurable.of_discrete : Measurable g) (measurable_cellIndex hκ u)]
  change (∫⁻ n, g n ∂indexLaw hκ u) = _
  rw [lintegral_countable']
  refine tsum_congr fun n => ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top (indexLaw hκ u) {n}), indexLaw_singleton]

/-- The confinement radius `D_u = 2 √(κ ‖u‖²/L)`. -/
def Drad (κ : ℝ) (L : ℝ) (m : ℝ) : ℝ := 2 * Real.sqrt (κ * m^2 / L)

omit [Fact (0 < L)] in
theorem Drad_nonneg (_hκ : 0 < κ) (m : ℝ) : 0 ≤ Drad κ L m := by
  have : 0 ≤ Real.sqrt (κ * m^2 / L) := Real.sqrt_nonneg _
  unfold Drad; linarith

theorem Drad_mono (hκ : 0 < κ) {m M : ℝ} (hm : 0 ≤ m) (h : m ≤ M) :
    Drad κ L m ≤ Drad κ L M := by
  have hL : 0 < L := Fact.out
  unfold Drad
  have : Real.sqrt (κ * m^2 / L) ≤ Real.sqrt (κ * M^2 / L) := by
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ hL.le
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm h 2) hκ.le
  linarith

/-- Tails of the weighted indexed actions are controlled by tails of the shifted moment. -/
theorem cell_action_tail (hκ : 0 < κ) (u : L2T L) {p : ℝ} (hp : 0 ≤ p) (T : ℝ) :
    ∑' n : ℤ, ENNReal.ofReal (if T < |momentum L n| then
        (1 + |momentum L n|)^p * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n else 0) ≤
      ENNReal.ofReal ((1 + Drad κ L ‖u‖)^p) *
        ∫⁻ x in {x : ℝ | T - Drad κ L ‖u‖ < |x|}, ENNReal.ofReal ((1 + |x|)^p)
          ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u) := by
  set D := Drad κ L ‖u‖
  have hD : 0 ≤ D := Drad_nonneg hκ _
  have e : ∀ n : ℤ, ENNReal.ofReal (if T < |momentum L n| then
        (1 + |momentum L n|)^p * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n else 0) =
      ENNReal.ofReal (if T < |momentum L n| then (1 + |momentum L n|)^p else 0) *
        ENNReal.ofReal ((QuantumNLS.RootIndexedMasses.masses hκ u).1 n) := fun n => by
    split_ifs
    · rw [ENNReal.ofReal_mul (by positivity)]
    · simp
  simp_rw [e]
  rw [← cell_lintegral hκ u (fun n => ENNReal.ofReal (if T < |momentum L n| then
    (1 + |momentum L n|)^p else 0)), ← lintegral_indicator (measurableSet_tail _),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [displacement_bound_ae hκ u] with t ht
  have ht' : |t - cellMomentum hκ u t| ≤ D := by simpa [D, Drad, Real.norm_eq_abs] using ht
  split_ifs with hc
  · have hm : T - D < |t| := by
      have := abs_sub_abs_le_abs_sub (cellMomentum hκ u t) t
      rw [abs_sub_comm] at this
      unfold cellMomentum at this ht'
      linarith
    rw [indicator_of_mem (show t ∈ {x : ℝ | T - D < |x|} from hm), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := shifted_weight_le (cellMomentum hκ u t) t D p hD hp
      (by rw [abs_sub_comm]; exact ht')
    exact h
  · simp

/-- Tails of the shifted moment are controlled by tails of the weighted indexed actions. -/
theorem cell_moment_tail (hκ : 0 < κ) (u : L2T L) {p : ℝ} (hp : 0 ≤ p) (T : ℝ) :
    ∫⁻ x in {x : ℝ | T < |x|}, ENNReal.ofReal ((1 + |x|)^p)
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ≤
      ENNReal.ofReal ((1 + Drad κ L ‖u‖)^p) *
        ∑' n : ℤ, ENNReal.ofReal (if T - Drad κ L ‖u‖ < |momentum L n| then
          (1 + |momentum L n|)^p * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n else 0) := by
  set D := Drad κ L ‖u‖
  have hD : 0 ≤ D := Drad_nonneg hκ _
  have e : ∀ n : ℤ, ENNReal.ofReal (if T - D < |momentum L n| then
        (1 + |momentum L n|)^p * (QuantumNLS.RootIndexedMasses.masses hκ u).1 n else 0) =
      ENNReal.ofReal (if T - D < |momentum L n| then (1 + |momentum L n|)^p else 0) *
        ENNReal.ofReal ((QuantumNLS.RootIndexedMasses.masses hκ u).1 n) := fun n => by
    split_ifs
    · rw [ENNReal.ofReal_mul (by positivity)]
    · simp
  simp_rw [e]
  rw [← cell_lintegral hκ u (fun n => ENNReal.ofReal (if T - D < |momentum L n| then
    (1 + |momentum L n|)^p else 0)), ← lintegral_indicator (measurableSet_tail _),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [displacement_bound_ae hκ u] with t ht
  have ht' : |t - cellMomentum hκ u t| ≤ D := by simpa [D, Drad, Real.norm_eq_abs] using ht
  by_cases hc : t ∈ {x : ℝ | T < |x|}
  · have hm : T - D < |momentum L (cellIndex hκ u t)| := by
      have := abs_sub_abs_le_abs_sub t (cellMomentum hκ u t)
      unfold cellMomentum at this ht'
      have hc' : T < |t| := hc
      linarith
    rw [indicator_of_mem hc, ite_eq_left_of_eq_true _ _ (eq_true hm), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (shifted_weight_le t (cellMomentum hκ u t) D p hD hp ht')
  · rw [indicator_of_notMem hc]; exact zero_le

/-! ### Uniform tail transfer along bounded sequences -/

theorem setLIntegral_ofReal_le {μ : Measure ℝ} {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf : Integrable f μ) (S : Set ℝ) {δ : ℝ} (h : ∫ x in S, f x ∂μ ≤ δ) :
    ∫⁻ x in S, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal δ := by
  rw [← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_of_all _ hf0)]
  exact ENNReal.ofReal_le_ofReal h

/-- Moment tails give action tails (weights `(1+|p_n|)^{2s}`), uniformly along an `L²`-bounded
sequence. -/
theorem action_tails (hκ : 0 < κ) (us : ℕ → L2T L) {MU : ℝ} (hMU : ∀ j, ‖us j‖ ≤ MU)
    {s : ℝ} (hs : 0 ≤ s)
    (hint : ∀ j, Integrable (fun x : ℝ => |x|^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ (us j)))
    (hsum : ∀ j, Summable (fun n : ℤ => (1 + |momentum L n|)^(2*s) *
      (QuantumNLS.RootIndexedMasses.masses hκ (us j)).1 n))
    (htail : ∀ ε > 0, ∃ T : ℝ, ∀ᶠ j in atTop,
      ∫ x in {x | T < |x|}, |x|^(2*s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (us j)) ≤ ε) :
    ∀ ε > 0, ∃ F : Finset ℤ, ∀ᶠ j in atTop, ∑' n : {n // n ∉ F},
      (1 + |momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ (us j)).1 n ≤ ε := by
  intro ε hε
  have hL : 0 < L := Fact.out
  set D := Drad κ L MU
  have hD : 0 ≤ D := Drad_nonneg hκ MU
  set c := (1 + D)^(2*s) * 2^(2*s) with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨T₀, hT₀⟩ := htail (ε / c) (by positivity)
  set T₁ := max T₀ 1
  set N : ℕ := ⌈(T₁ + D) * L / (2 * Real.pi)⌉₊
  refine ⟨Finset.Icc (-(N:ℤ)) N, ?_⟩
  filter_upwards [hT₀] with j hj
  have hDj : Drad κ L ‖us j‖ ≤ D := Drad_mono hκ (norm_nonneg _) (hMU j)
  have hw0 : ∀ n : ℤ, 0 ≤ (1 + |momentum L n|)^(2*s) *
      (QuantumNLS.RootIndexedMasses.masses hκ (us j)).1 n :=
    fun n => mul_nonneg (by positivity) (QuantumNLS.Reg015Setting.masses_nonneg hκ _ n)
  -- outside the index window the momentum is beyond `T₁ + D`
  have hfar : ∀ n : ℤ, n ∉ Finset.Icc (-(N:ℤ)) N → T₁ + D < |momentum L n| := by
    intro n hn
    have hn' : (N:ℤ) < |n| := by
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
      rcases hn with h | h <;> [rw [abs_of_neg (by omega)]; rw [abs_of_pos (by omega)]] <;> omega
    have hn'' : ((N:ℝ)) + 1 ≤ |(n:ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast hn'
    have hNle : (T₁ + D) * L / (2 * Real.pi) ≤ N := Nat.le_ceil _
    have hmom : |momentum L n| = 2 * Real.pi * |(n:ℝ)| / L := by
      unfold momentum
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi), abs_of_pos hL]
    rw [hmom, lt_div_iff₀ hL]
    rw [div_le_iff₀ (by positivity)] at hNle
    nlinarith [Real.pi_pos]
  -- ENNReal chain
  have h1 : ENNReal.ofReal (∑' n : {n // n ∉ Finset.Icc (-(N:ℤ)) N},
      (1 + |momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ (us j)).1 n) ≤
      ∑' n : ℤ, ENNReal.ofReal (if T₁ + D < |momentum L n| then
        (1 + |momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ (us j)).1 n else 0) := by
    exact tail_ofReal_le _ hw0 (hsum j) _ _ hfar
  have h2 := cell_action_tail hκ (us j) (p := 2*s) (by positivity) (T₁ + D)
  have h3 : ∫⁻ x in {x : ℝ | T₁ + D - Drad κ L ‖us j‖ < |x|}, ENNReal.ofReal ((1 + |x|)^(2*s))
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (us j)) ≤
      ∫⁻ x in {x : ℝ | T₀ < |x|}, ENNReal.ofReal (2^(2*s) * |x|^(2*s))
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (us j)) := by
    rw [← lintegral_indicator (measurableSet_tail _), ← lintegral_indicator (measurableSet_tail _)]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ {x : ℝ | T₁ + D - Drad κ L ‖us j‖ < |x|}
    · have hx' : T₁ < |x| := by
        have : T₁ + D - Drad κ L ‖us j‖ < |x| := hx
        linarith
      have h0 : T₀ < |x| := lt_of_le_of_lt (le_max_left T₀ 1) hx'
      have hx1 : 1 ≤ |x| := (le_max_right T₀ 1).trans hx'.le
      have hle : (1 + |x|)^(2*s) ≤ 2^(2*s) * |x|^(2*s) := by
        rw [← Real.mul_rpow (by norm_num) (abs_nonneg x)]
        exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      rw [indicator_of_mem hx, indicator_of_mem (show x ∈ {x : ℝ | T₀ < |x|} from h0)]
      exact ENNReal.ofReal_le_ofReal hle
    · rw [indicator_of_notMem hx]; exact zero_le
  have h4 : ∫⁻ x in {x : ℝ | T₀ < |x|}, ENNReal.ofReal (2^(2*s) * |x|^(2*s))
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (us j)) ≤
      ENNReal.ofReal (2^(2*s) * (ε / c)) := by
    simp_rw [ENNReal.ofReal_mul (show (0:ℝ) ≤ 2^(2*s) by positivity)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul' le_rfl (setLIntegral_ofReal_le (fun x => Real.rpow_nonneg (abs_nonneg x) _)
      (hint j) _ hj)
  have h5 : ENNReal.ofReal ((1 + Drad κ L ‖us j‖)^(2*s)) ≤ ENNReal.ofReal ((1 + D)^(2*s)) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by linarith [Drad_nonneg hκ (L := L) ‖us j‖])
      (by linarith) (by positivity))
  have hfin : ENNReal.ofReal (∑' n : {n // n ∉ Finset.Icc (-(N:ℤ)) N},
      (1 + |momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ (us j)).1 n) ≤
      ENNReal.ofReal ε := by
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ ENNReal.ofReal ((1 + D)^(2*s)) * ENNReal.ofReal (2^(2*s) * (ε / c)) :=
          mul_le_mul' h5 (h3.trans h4)
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hc]; field_simp
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp hfin

/-- Action tails give moment tails, uniformly along an `L²`-bounded sequence. -/
theorem moment_tails (hκ : 0 < κ) (us : ℕ → L2T L) {MU : ℝ} (hMU : ∀ j, ‖us j‖ ≤ MU)
    {s : ℝ} (hs : 0 ≤ s)
    (hint : ∀ j, Integrable (fun x : ℝ => |x|^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ (us j)))
    (hsum : ∀ j, Summable (fun n : ℤ => (1 + |momentum L n|)^(2*s) *
      (QuantumNLS.RootIndexedMasses.masses hκ (us j)).1 n))
    (htail : ∀ ε > 0, ∃ F : Finset ℤ, ∀ᶠ j in atTop, ∑' n : {n // n ∉ F},
      (1 + |momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ (us j)).1 n ≤ ε) :
    ∀ ε > 0, ∃ T : ℝ, ∀ᶠ j in atTop,
      ∫ x in {x | T < |x|}, |x|^(2*s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (us j)) ≤ ε := by
  intro ε hε
  set D := Drad κ L MU
  have hD : 0 ≤ D := Drad_nonneg hκ MU
  set c := (1 + D)^(2*s) with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨F, hF⟩ := htail (ε / c) (by positivity)
  set T := D + ∑ n ∈ F, |momentum L n|
  refine ⟨T, ?_⟩
  filter_upwards [hF] with j hj
  have hDj : Drad κ L ‖us j‖ ≤ D := Drad_mono hκ (norm_nonneg _) (hMU j)
  have hw0 : ∀ n : ℤ, 0 ≤ (1 + |momentum L n|)^(2*s) *
      (QuantumNLS.RootIndexedMasses.masses hκ (us j)).1 n :=
    fun n => mul_nonneg (by positivity) (QuantumNLS.Reg015Setting.masses_nonneg hκ _ n)
  have h1 : ∫⁻ x in {x : ℝ | T < |x|}, ENNReal.ofReal (|x|^(2*s))
      ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (us j)) ≤
      ∫⁻ x in {x : ℝ | T < |x|}, ENNReal.ofReal ((1 + |x|)^(2*s))
      ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (us j)) :=
    lintegral_mono fun x => ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow (abs_nonneg x) (by linarith) (by positivity))
  have h2 := cell_moment_tail hκ (us j) (p := 2*s) (by positivity) T
  have h3 : ∑' n : ℤ, ENNReal.ofReal (if T - Drad κ L ‖us j‖ < |momentum L n| then
        (1 + |momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ (us j)).1 n else 0) ≤
      ENNReal.ofReal (∑' n : {n // n ∉ F},
        (1 + |momentum L n|)^(2*s) * (QuantumNLS.RootIndexedMasses.masses hκ (us j)).1 n) := by
    refine tail_ofReal_ge _ hw0 (hsum j) F _ (fun n hcnd hnF => ?_)
    have : |momentum L n| ≤ ∑ m ∈ F, |momentum L m| :=
      Finset.single_le_sum (f := fun m => |momentum L m|) (fun m _ => abs_nonneg _) hnF
    linarith
  have h5 : ENNReal.ofReal ((1 + Drad κ L ‖us j‖)^(2*s)) ≤ ENNReal.ofReal c :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by linarith [Drad_nonneg hκ (L := L) ‖us j‖])
      (by linarith) (by positivity))
  have hfin : ENNReal.ofReal (∫ x in {x | T < |x|}, |x|^(2*s)
      ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (us j))) ≤ ENNReal.ofReal ε := by
    rw [ofReal_integral_eq_lintegral_ofReal (hint j).integrableOn
      (ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg x) _)]
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal (ε / c) :=
          mul_le_mul' h5 (h3.trans (ENNReal.ofReal_le_ofReal hj))
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_mul hc0.le]
          congr 1; field_simp
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp hfin

end QuantumNLS.Reg013OCells

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg013OCells." ||
        n.toString.startsWith "_private.QuantumNLS.Reg013OCells." then
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
  Lean.logInfo m!"Reg013OCells aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."

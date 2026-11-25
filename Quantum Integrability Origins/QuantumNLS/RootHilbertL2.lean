import Mathlib
import QuantumNLS.RootHilbertEnergy

/-!
# R-064239ED `lem:root-Hilbert-truncations` (ROOT_scalar_uniqueness.tex:11-67), part (ii): `L²` convergence

Hypotheses `HilbertHyp ρ` (`ρ ≥ 0`, `ρ ∈ L¹ ∩ L^∞`, locally Hölder).  Proved (printed argument:
Plancherel + the multiplier `𝓕 K_{a,R}`, uniform bound and `min(4, 2π|ξ|δ)` Lipschitz bound, then limit `R → ∞`):

* `memLp_hilbertTrunc`: `H_ε ρ ∈ L²(dx)` for `ε > 0`;
* `memLp_trunc_sub`: for `0 < ε' ≤ ε`, `∫ |H_ε' ρ - H_ε ρ|² ≤ Eρ(ε - ε')` (Fatou in `R → ∞`);
* `memLp_trunc_sub_PV`: `Hρ ∈ L²(dx)` and `∫ |H_ε ρ - Hρ|² ≤ Eρ(ε)` (Fatou along `ε'_n = ε/(n+2) → 0`
  using the pointwise limit `tendsto_hilbertPV`), and `Eρ(ε) → 0` (`tendsto_Eρ`);
* weighted version: `L²(ρ dx)` with `ρ dx = volume.withDensity (ofReal ∘ ρ)`, via `ρ dx ≤ ‖ρ‖_∞ dx`;
* `root_Hilbert_truncations`: the full statement (i) + (ii).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform ENNReal NNReal

namespace QuantumNLS.RootHilbert

/-! ### Generic Fatou step -/

theorem fatou_sq {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} (hf : ∀ n, AEStronglyMeasurable (f n) (volume : Measure ℝ))
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) (C : ℝ≥0∞)
    (hC : ∀ n, ∫⁻ x, ‖f n x‖ₑ ^ 2 ≤ C) :
    AEStronglyMeasurable g (volume : Measure ℝ) ∧ ∫⁻ x, ‖g x‖ₑ ^ 2 ≤ C := by
  have hg : AEStronglyMeasurable g (volume : Measure ℝ) :=
    aestronglyMeasurable_of_tendsto_ae atTop hf (ae_of_all _ hlim)
  refine ⟨hg, ?_⟩
  have h1 : ∀ x, ‖g x‖ₑ ^ 2 = liminf (fun n => ‖f n x‖ₑ ^ 2) atTop := by
    intro x
    have ht : Tendsto (fun n => ‖f n x‖ₑ ^ 2) atTop (𝓝 (‖g x‖ₑ ^ 2)) :=
      ((ENNReal.continuous_pow 2).tendsto _).comp ((continuous_enorm.tendsto _).comp (hlim x))
    exact ht.liminf_eq.symm
  calc ∫⁻ x, ‖g x‖ₑ ^ 2 = ∫⁻ x, liminf (fun n => ‖f n x‖ₑ ^ 2) atTop := lintegral_congr h1
    _ ≤ liminf (fun n => ∫⁻ x, ‖f n x‖ₑ ^ 2) atTop :=
        lintegral_liminf_le' (fun n => (hf n).enorm.pow_const 2)
    _ ≤ C := liminf_le_of_frequently_le' (Frequently.of_forall hC)

theorem lintegral_enorm_sq_le {F : ℝ → ℝ} (hi : Integrable (fun x => ‖F x‖ ^ 2) (volume : Measure ℝ))
    {E : ℝ} (h : ∫ x, ‖F x‖ ^ 2 ≤ E) : ∫⁻ x, ‖F x‖ₑ ^ 2 ≤ ENNReal.ofReal E := by
  have h1 : ∀ x, ‖F x‖ₑ ^ 2 = ENNReal.ofReal (‖F x‖ ^ 2) := fun x => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [lintegral_congr h1,
    ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => by positivity)]
  exact ENNReal.ofReal_le_ofReal h

theorem memLp_two_of_lintegral {g : ℝ → ℝ} (hg : AEStronglyMeasurable g (volume : Measure ℝ)) {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (h : ∫⁻ x, ‖g x‖ₑ ^ 2 ≤ C) :
    MemLp g 2 (volume : Measure ℝ) ∧ ∫ x, ‖g x‖ ^ 2 ≤ C.toReal := by
  have h1 : ∀ x, ‖g x‖ₑ ^ 2 = ENNReal.ofReal (‖g x‖ ^ 2) := fun x => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hmeas : AEStronglyMeasurable (fun x => ‖g x‖ ^ 2) (volume : Measure ℝ) :=
    (hg.norm.aemeasurable.pow_const 2).aestronglyMeasurable
  have hint : Integrable (fun x => ‖g x‖ ^ 2) (volume : Measure ℝ) := by
    refine ⟨hmeas, ?_⟩
    have e : ∀ x, ‖(‖g x‖ ^ 2)‖ₑ = ‖g x‖ₑ ^ 2 := fun x => by rw [enorm_pow, enorm_norm]
    unfold HasFiniteIntegral
    rw [lintegral_congr e]
    exact lt_of_le_of_lt h (lt_top_iff_ne_top.2 hC)
  refine ⟨(memLp_two_iff_integrable_sq_norm hg).2 hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => by positivity) hmeas]
  refine ENNReal.toReal_mono hC ?_
  rw [← lintegral_congr h1]
  exact h

theorem fatou_L2 {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} (hf : ∀ n, AEStronglyMeasurable (f n) (volume : Measure ℝ))
    (hfi : ∀ n, Integrable (fun x => ‖f n x‖ ^ 2) (volume : Measure ℝ))
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) {E : ℝ}
    (hE : ∀ n, ∫ x, ‖f n x‖ ^ 2 ≤ E) :
    MemLp g 2 (volume : Measure ℝ) ∧ ∫ x, ‖g x‖ ^ 2 ≤ E := by
  obtain ⟨hg, hl⟩ := fatou_sq hf hlim (ENNReal.ofReal E) (fun n => lintegral_enorm_sq_le (hfi n) (hE n))
  obtain ⟨h1, h2⟩ := memLp_two_of_lintegral hg ENNReal.ofReal_ne_top hl
  have hE0 : 0 ≤ E := le_trans (integral_nonneg (fun x => by positivity)) (hE 0)
  refine ⟨h1, ?_⟩
  rwa [ENNReal.toReal_ofReal hE0] at h2

/-! ### The truncation sequences `R_n → ∞` -/

/-- `R_n = ε + n + 1`. -/
def Rseq (ε : ℝ) (n : ℕ) : ℝ := ε + n + 1

theorem tendsto_Rseq (ε : ℝ) (hε : 0 ≤ ε) : Tendsto (Rseq ε) atTop atTop :=
  tendsto_atTop_mono (fun n => by unfold Rseq; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    tendsto_natCast_atTop_atTop

theorem tendsto_Tr {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) {ε' ε : ℝ} (hε' : 0 < ε') (hle : ε' ≤ ε) (x : ℝ) :
    Tendsto (fun n => Tr ρ ε' (Rseq ε n) x) atTop (𝓝 (hilbertTrunc ρ ε' x)) := by
  have hR := tendsto_Rseq ε (hε'.le.trans hle)
  have hb : Tendsto (fun n => (∫ y, ρ y) / Rseq ε n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hR
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hb
  rw [Real.dist_eq, abs_sub_comm]
  exact abs_hilbertTrunc_sub_Tr_le hρ hε'
    (by unfold Rseq; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) x

theorem aesm_Tr {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    AEStronglyMeasurable (Tr ρ a b) (volume : Measure ℝ) := by
  refine (Complex.continuous_re.comp_aestronglyMeasurable (integrable_Gc hρ ha b).1).congr
    (Eventually.of_forall (fun x => ?_))
  simp [Gc_eq]

theorem norm_Tr_eq (ρ : ℝ → ℝ) (a b x : ℝ) : ‖Tr ρ a b x‖ = ‖Gc ρ a b x‖ := by
  rw [Gc_eq, Complex.norm_real]

theorem norm_Tr_sub_eq (ρ : ℝ → ℝ) (a' a R x : ℝ) :
    ‖Tr ρ a' R x - Tr ρ a R x‖ = ‖Gc ρ a' R x - Gc ρ a R x‖ := by
  rw [Gc_eq, Gc_eq, ← Complex.ofReal_sub, Complex.norm_real]

/-! ### `L²` bounds -/

theorem memLp_hilbertTrunc {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) {ε : ℝ} (hε : 0 < ε) :
    MemLp (hilbertTrunc ρ ε) 2 (volume : Measure ℝ) ∧
      ∫ x, ‖hilbertTrunc ρ ε x‖ ^ 2 ≤ 64 * ∫ x, ‖rhoc ρ x‖ ^ 2 := by
  refine fatou_L2 (f := fun n => Tr ρ ε (Rseq ε n)) (fun n => aesm_Tr hρ hε _) (fun n => ?_)
    (tendsto_Tr hρ hε le_rfl) (fun n => ?_)
  · have h := (memLp_two_iff_integrable_sq_norm (memLp_Gc hρ hε (Rseq ε n)).aestronglyMeasurable).1
      (memLp_Gc hρ hε _)
    simpa only [norm_Tr_eq] using h
  · have h := energy_Gc hρ hε (a := ε) (R := Rseq ε n)
      (by unfold Rseq; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    simpa only [norm_Tr_eq] using h

theorem memLp_trunc_sub {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) {ε' ε : ℝ} (hε' : 0 < ε') (hle : ε' ≤ ε) :
    MemLp (fun x => hilbertTrunc ρ ε' x - hilbertTrunc ρ ε x) 2 (volume : Measure ℝ) ∧
      ∫ x, ‖hilbertTrunc ρ ε' x - hilbertTrunc ρ ε x‖ ^ 2 ≤ Eρ ρ (ε - ε') := by
  have hε : 0 < ε := lt_of_lt_of_le hε' hle
  have hR : ∀ n, ε ≤ Rseq ε n := fun n => by
    unfold Rseq; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  refine fatou_L2 (f := fun n x => Tr ρ ε' (Rseq ε n) x - Tr ρ ε (Rseq ε n) x)
    (fun n => (aesm_Tr hρ hε' _).sub (aesm_Tr hρ hε _)) (fun n => ?_)
    (fun x => (tendsto_Tr hρ hε' hle x).sub (tendsto_Tr hρ hε le_rfl x)) (fun n => ?_)
  · simpa only [norm_Tr_sub_eq] using (energy_diff hρ hε' hle (hR n)).1
  · simpa only [norm_Tr_sub_eq] using (energy_diff hρ hε' hle (hR n)).2

theorem Eρ_mono {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) {δ₁ δ₂ : ℝ} (h0 : 0 ≤ δ₁) (h : δ₁ ≤ δ₂) :
    Eρ ρ δ₁ ≤ Eρ ρ δ₂ := by
  refine integral_mono (integrable_Eρ_integrand hρ h0) (integrable_Eρ_integrand hρ (h0.trans h))
    (fun ξ => ?_)
  have hm : min 4 (2 * Real.pi * |ξ| * δ₁) ≤ min 4 (2 * Real.pi * |ξ| * δ₂) :=
    min_le_min_left _ (by gcongr)
  have h0' : 0 ≤ min 4 (2 * Real.pi * |ξ| * δ₁) := le_min (by norm_num) (by positivity)
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by linarith) 2

theorem Eρ_nonneg (ρ : ℝ → ℝ) (δ : ℝ) : 0 ≤ Eρ ρ δ :=
  integral_nonneg (fun ξ => by positivity)

theorem tendsto_seq_nhdsGT (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => ε / ((n : ℝ) + 2)) atTop (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall (fun n => ?_)⟩
  · exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  · show (0 : ℝ) < ε / ((n : ℝ) + 2)
    positivity

theorem memLp_trunc_sub_PV {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) {ε : ℝ} (hε : 0 < ε) :
    MemLp (fun x => hilbertTrunc ρ ε x - hilbertPV ρ x) 2 (volume : Measure ℝ) ∧
      ∫ x, ‖hilbertTrunc ρ ε x - hilbertPV ρ x‖ ^ 2 ≤ Eρ ρ ε := by
  have hpos : ∀ n : ℕ, 0 < ε / ((n : ℝ) + 2) := fun n => by positivity
  have hle : ∀ n : ℕ, ε / ((n : ℝ) + 2) ≤ ε := fun n => by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hsub : ∀ n : ℕ, 0 ≤ ε - ε / ((n : ℝ) + 2) := fun n => sub_nonneg.2 (hle n)
  have hmain : MemLp (fun x => hilbertPV ρ x - hilbertTrunc ρ ε x) 2 (volume : Measure ℝ) ∧
      ∫ x, ‖hilbertPV ρ x - hilbertTrunc ρ ε x‖ ^ 2 ≤ Eρ ρ ε := by
    refine fatou_L2 (f := fun n x => hilbertTrunc ρ (ε / ((n : ℝ) + 2)) x - hilbertTrunc ρ ε x)
      (fun n => (memLp_trunc_sub hρ (hpos n) (hle n)).1.aestronglyMeasurable) (fun n => ?_)
      (fun x => ((tendsto_hilbertPV hρ x).comp (tendsto_seq_nhdsGT ε hε)).sub tendsto_const_nhds)
      (fun n => ?_)
    · have h := memLp_trunc_sub hρ (hpos n) (hle n)
      exact (memLp_two_iff_integrable_sq_norm h.1.aestronglyMeasurable).1 h.1
    · exact ((memLp_trunc_sub hρ (hpos n) (hle n)).2).trans (Eρ_mono hρ (hsub n) (by
        have := (div_pos hε (show (0 : ℝ) < (n : ℝ) + 2 by positivity)); linarith))
  have e : (fun x => hilbertTrunc ρ ε x - hilbertPV ρ x) =
      fun x => -(hilbertPV ρ x - hilbertTrunc ρ ε x) := funext fun x => (neg_sub _ _).symm
  refine ⟨?_, ?_⟩
  · rw [e]; exact hmain.1.neg
  · have e2 : ∀ x, ‖hilbertTrunc ρ ε x - hilbertPV ρ x‖ = ‖hilbertPV ρ x - hilbertTrunc ρ ε x‖ :=
      fun x => norm_sub_rev _ _
    simp_rw [e2]; exact hmain.2

theorem memLp_hilbertPV {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) :
    MemLp (hilbertPV ρ) 2 (volume : Measure ℝ) := by
  have h1 := (memLp_hilbertTrunc hρ (zero_lt_one : (0 : ℝ) < 1)).1
  have h2 := (memLp_trunc_sub_PV hρ (zero_lt_one : (0 : ℝ) < 1)).1
  have := h1.sub h2
  refine this.ae_eq (Eventually.of_forall (fun x => ?_))
  simp

theorem tendsto_L2_trunc {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) :
    Tendsto (fun ε => ∫ x, ‖hilbertTrunc ρ ε x - hilbertPV ρ x‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ (tendsto_Eρ hρ)
  · exact Eventually.of_forall (fun ε => integral_nonneg (fun x => by positivity))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (memLp_trunc_sub_PV hρ hε).2

/-! ### The weighted space `L²(ρ dx)` -/

/-- The measure `ρ dx`. -/
def rhoMeasure (ρ : ℝ → ℝ) : Measure ℝ := (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (ρ x))

theorem rhoMeasure_le {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) :
    ∃ M : ℝ, 0 ≤ M ∧ rhoMeasure ρ ≤ ENNReal.ofReal M • (volume : Measure ℝ) := by
  obtain ⟨M, hM⟩ := hρ.ae_le
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  have := withDensity_mono (μ := (volume : Measure ℝ)) (f := fun x => ENNReal.ofReal (ρ x))
    (g := fun _ => ENNReal.ofReal (max M 0))
    (by filter_upwards [hM] with x hx; exact ENNReal.ofReal_le_ofReal (hx.trans (le_max_left _ _)))
  rwa [withDensity_const] at this

theorem memLp_rho_of_memLp {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) {F : ℝ → ℝ}
    (hF : MemLp F 2 (volume : Measure ℝ)) : MemLp F 2 (rhoMeasure ρ) := by
  obtain ⟨M, -, hle⟩ := rhoMeasure_le hρ
  exact hF.of_measure_le_smul ENNReal.ofReal_ne_top hle

theorem integral_rho_le {ρ : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hle : rhoMeasure ρ ≤ ENNReal.ofReal M • (volume : Measure ℝ)) {F : ℝ → ℝ}
    (hF : MemLp F 2 (volume : Measure ℝ)) :
    ∫ x, ‖F x‖ ^ 2 ∂(rhoMeasure ρ) ≤ M * ∫ x, ‖F x‖ ^ 2 := by
  have hint : Integrable (fun x => ‖F x‖ ^ 2) (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).1 hF
  have h1 := integral_mono_measure (f := fun x => ‖F x‖ ^ 2) hle
    (Eventually.of_forall (fun x => by positivity)) (hint.smul_measure ENNReal.ofReal_ne_top)
  rw [integral_smul_measure, ENNReal.toReal_ofReal hM, smul_eq_mul] at h1
  exact h1

/-! ### The lemma -/

/-- **`lem:root-Hilbert-truncations`.**  Let `ρ ≥ 0` be in `L¹ ∩ L^∞`, locally Hölder.  Then
(i) the principal value `Hρ(x) = lim_{ε↓0} H_ε ρ(x)` exists at every `x`;
(ii) `H_ε ρ, Hρ ∈ L²(dx)` and `H_ε ρ → Hρ` in `L²(dx)` as `ε ↓ 0`;
(iii) the same in `L²(ρ dx)`. -/
theorem root_Hilbert_truncations {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) :
    (∀ x, Tendsto (fun ε => hilbertTrunc ρ ε x) (𝓝[>] (0 : ℝ)) (𝓝 (hilbertPV ρ x))) ∧
    ((∀ ε : ℝ, 0 < ε → MemLp (hilbertTrunc ρ ε) 2 (volume : Measure ℝ)) ∧
      MemLp (hilbertPV ρ) 2 (volume : Measure ℝ) ∧
      Tendsto (fun ε => ∫ x, ‖hilbertTrunc ρ ε x - hilbertPV ρ x‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0)) ∧
    ((∀ ε : ℝ, 0 < ε → MemLp (hilbertTrunc ρ ε) 2 (rhoMeasure ρ)) ∧
      MemLp (hilbertPV ρ) 2 (rhoMeasure ρ) ∧
      Tendsto (fun ε => ∫ x, ‖hilbertTrunc ρ ε x - hilbertPV ρ x‖ ^ 2 ∂(rhoMeasure ρ))
        (𝓝[>] (0 : ℝ)) (𝓝 0)) := by
  refine ⟨tendsto_hilbertPV hρ, ⟨fun ε hε => (memLp_hilbertTrunc hρ hε).1, memLp_hilbertPV hρ,
    tendsto_L2_trunc hρ⟩, ⟨fun ε hε => memLp_rho_of_memLp hρ (memLp_hilbertTrunc hρ hε).1,
    memLp_rho_of_memLp hρ (memLp_hilbertPV hρ), ?_⟩⟩
  obtain ⟨M, hM, hle⟩ := rhoMeasure_le hρ
  have hlim : Tendsto (fun ε => M * ∫ x, ‖hilbertTrunc ρ ε x - hilbertPV ρ x‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (tendsto_L2_trunc hρ).const_mul M
  refine squeeze_zero' ?_ ?_ hlim
  · exact Eventually.of_forall (fun ε => integral_nonneg (fun x => by positivity))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact integral_rho_le hM hle (memLp_trunc_sub_PV hρ hε).1

theorem integral_rhoMeasure {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) (F : ℝ → ℝ) :
    ∫ x, F x ∂(rhoMeasure ρ) = ∫ x, ρ x * F x := by
  have hm : Measurable (fun x => ENNReal.ofReal (ρ x)) := ENNReal.measurable_ofReal.comp hρ.continuous.measurable
  rw [rhoMeasure, integral_withDensity_eq_integral_toReal_smul hm (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
  simp [ENNReal.toReal_ofReal (hρ.nonneg x)]

/-- The `L²(ρ dx)` statement in the literal form `∫ |H_ε ρ - Hρ|² ρ dx → 0`. -/
theorem tendsto_L2_weighted {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) :
    Tendsto (fun ε => ∫ x, ρ x * ‖hilbertTrunc ρ ε x - hilbertPV ρ x‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have := (root_Hilbert_truncations hρ).2.2.2.2
  simpa only [integral_rhoMeasure hρ (fun x => ‖hilbertTrunc ρ _ x - hilbertPV ρ x‖ ^ 2)] using this

#print axioms root_Hilbert_truncations
#print axioms tendsto_L2_weighted

end QuantumNLS.RootHilbert

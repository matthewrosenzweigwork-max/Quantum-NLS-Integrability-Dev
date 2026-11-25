import Mathlib
import NlsGge.Birkhoff.BirkhoffAPI38

/- MTAILGEN PRODUCTION01 (proof development, AUTHOR; not reviewed). Proposed target NlsGge/ThirdConsultation/M/CarrierTails.lean,
   namespace NlsGge.ThirdConsultation.MTails. Generic support for Pro round 16 §Q2 `odd_higher_action_tails_of_tendsto`
   (no packet increment): weighted tails t_L(z) = Σ_{|n| ≥ L} w_n |z_n|² on the Sobolev carrier h^r, their basic
   properties, and uniform smallness along ONE convergent sequence (Pro L522-527: "for each tolerance choose one tail
   cutoff for the limiting sequence, then use norm convergence for all sufficiently late terms and enlarge the cutoff to
   cover the finitely many earlier terms"). Not a claim about uniform tails on a ball. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.MTails

/-- The weighted tail beyond `|n| ≥ L`. -/
def tail (r : ℝ) (L : ℕ) (z : SobolevCarrier38 r) : ℝ :=
  ∑' n : ℤ, if L ≤ n.natAbs then sobolevModeWeight r n * ‖carrierCoe38 r z n‖ ^ 2 else 0

theorem term_nonneg (r : ℝ) (z : SobolevCarrier38 r) (n : ℤ) :
    0 ≤ sobolevModeWeight r n * ‖carrierCoe38 r z n‖ ^ 2 :=
  mul_nonneg (sobolevModeWeight_pos r n).le (sq_nonneg _)

theorem ite_term_nonneg (r : ℝ) (L : ℕ) (z : SobolevCarrier38 r) (n : ℤ) :
    0 ≤ (if L ≤ n.natAbs then sobolevModeWeight r n * ‖carrierCoe38 r z n‖ ^ 2 else 0) := by
  split_ifs
  · exact term_nonneg r z n
  · exact le_rfl

theorem ite_term_le (r : ℝ) (L : ℕ) (z : SobolevCarrier38 r) (n : ℤ) :
    (if L ≤ n.natAbs then sobolevModeWeight r n * ‖carrierCoe38 r z n‖ ^ 2 else 0) ≤
      sobolevModeWeight r n * ‖carrierCoe38 r z n‖ ^ 2 := by
  split_ifs
  · exact le_rfl
  · exact term_nonneg r z n

theorem summable_tail_terms (r : ℝ) (L : ℕ) (z : SobolevCarrier38 r) :
    Summable (fun n : ℤ =>
      if L ≤ n.natAbs then sobolevModeWeight r n * ‖carrierCoe38 r z n‖ ^ 2 else 0) :=
  Summable.of_nonneg_of_le (ite_term_nonneg r L z) (ite_term_le r L z)
    (carrier_hasSum_norm_sq38 r z).summable

theorem tail_nonneg (r : ℝ) (L : ℕ) (z : SobolevCarrier38 r) : 0 ≤ tail r L z :=
  tsum_nonneg (ite_term_nonneg r L z)

theorem tail_le_norm_sq (r : ℝ) (L : ℕ) (z : SobolevCarrier38 r) : tail r L z ≤ ‖z‖ ^ 2 := by
  rw [← (carrier_hasSum_norm_sq38 r z).tsum_eq]
  exact Summable.tsum_le_tsum (ite_term_le r L z) (summable_tail_terms r L z)
    (carrier_hasSum_norm_sq38 r z).summable

theorem tail_anti (r : ℝ) {L L' : ℕ} (h : L ≤ L') (z : SobolevCarrier38 r) :
    tail r L' z ≤ tail r L z := by
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_tail_terms r L' z) (summable_tail_terms r L z)
  by_cases h1 : L' ≤ n.natAbs
  · rw [if_pos h1, if_pos (le_trans h h1)]
  · rw [if_neg h1]
    exact ite_term_nonneg r L z n

theorem tail_add_le (r : ℝ) (L : ℕ) (x y : SobolevCarrier38 r) :
    tail r L (x + y) ≤ 2 * tail r L x + 2 * tail r L y := by
  unfold tail
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← ((summable_tail_terms r L x).mul_left 2).tsum_add ((summable_tail_terms r L y).mul_left 2)]
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_tail_terms r L (x + y))
    (((summable_tail_terms r L x).mul_left 2).add ((summable_tail_terms r L y).mul_left 2))
  by_cases h1 : L ≤ n.natAbs
  · rw [if_pos h1, if_pos h1, if_pos h1]
    have e : carrierCoe38 r (x + y) n = carrierCoe38 r x n + carrierCoe38 r y n := rfl
    rw [e]
    have hw := (sobolevModeWeight_pos r n).le
    have ht := norm_add_le (carrierCoe38 r x n) (carrierCoe38 r y n)
    have ha := norm_nonneg (carrierCoe38 r x n)
    have hb := norm_nonneg (carrierCoe38 r y n)
    have hs : ‖carrierCoe38 r x n + carrierCoe38 r y n‖ ^ 2 ≤
        2 * ‖carrierCoe38 r x n‖ ^ 2 + 2 * ‖carrierCoe38 r y n‖ ^ 2 := by
      nlinarith [sq_nonneg (‖carrierCoe38 r x n‖ - ‖carrierCoe38 r y n‖),
        norm_nonneg (carrierCoe38 r x n + carrierCoe38 r y n)]
    nlinarith [mul_le_mul_of_nonneg_left hs hw]
  · rw [if_neg h1, if_neg h1, if_neg h1]
    norm_num

theorem tail_tendsto_zero (r : ℝ) (z : SobolevCarrier38 r) :
    Tendsto (fun L : ℕ => tail r L z) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℕ))
    (f := fun (L : ℕ) (n : ℤ) =>
      if L ≤ n.natAbs then sobolevModeWeight r n * ‖carrierCoe38 r z n‖ ^ 2 else 0)
    (g := fun _ : ℤ => (0 : ℝ))
    (bound := fun n : ℤ => sobolevModeWeight r n * ‖carrierCoe38 r z n‖ ^ 2)
    (carrier_hasSum_norm_sq38 r z).summable
    (fun n => tendsto_const_nhds.congr' (eventually_atTop.2 ⟨n.natAbs + 1, fun L hL => by
      show (0 : ℝ) = if L ≤ n.natAbs then sobolevModeWeight r n * ‖carrierCoe38 r z n‖ ^ 2 else 0
      rw [if_neg (by omega)]⟩))
    (Eventually.of_forall (fun L n => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ite_term_nonneg r L z n)]
      exact ite_term_le r L z n))
  simpa [tail] using h

/-- Uniform tails along one convergent sequence. -/
theorem uniform_tails (r : ℝ) (z : ℕ → SobolevCarrier38 r) (z0 : SobolevCarrier38 r)
    (hz : Tendsto z atTop (𝓝 z0)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ L : ℕ, ∀ j : ℕ, tail r L (z j) < δ := by
  have hn : Tendsto (fun j => ‖z j - z0‖ ^ 2) atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hz).pow 2
    simpa using this
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hn.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ / 4)))
  obtain ⟨L0, hL0⟩ := ((tail_tendsto_zero r z0).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < δ / 4))).exists
  have hLj : ∀ j : ℕ, ∃ Lj : ℕ, tail r Lj (z j) < δ := fun j =>
    ((tail_tendsto_zero r (z j)).eventually (gt_mem_nhds hδ)).exists
  choose Lj hLj using hLj
  refine ⟨max L0 ((Finset.range J).sup Lj), fun j => ?_⟩
  by_cases hj : J ≤ j
  · have h1 := tail_add_le r (max L0 ((Finset.range J).sup Lj)) (z j - z0) z0
    rw [sub_add_cancel] at h1
    have h2 := tail_le_norm_sq r (max L0 ((Finset.range J).sup Lj)) (z j - z0)
    have h3 := tail_anti r (le_max_left L0 ((Finset.range J).sup Lj)) z0
    have h4 := hJ j hj
    linarith
  · have hjr : j ∈ Finset.range J := Finset.mem_range.2 (by omega)
    have hle : Lj j ≤ max L0 ((Finset.range J).sup Lj) :=
      le_trans (Finset.le_sup hjr) (le_max_right _ _)
    exact lt_of_le_of_lt (tail_anti r hle (z j)) (hLj j)

end NlsGge.ThirdConsultation.MTails

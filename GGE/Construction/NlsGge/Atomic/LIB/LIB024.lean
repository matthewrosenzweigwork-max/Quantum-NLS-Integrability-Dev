import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic

/-!
# LIB-024: local autonomous Banach ODEs on open domains

The Picard hypotheses are constructed from local Lipschitz continuity. The
solution stays in a closed ball within the open domain, and uniqueness holds
on any common interval on which both curves stay in that Lipschitz ball.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology
open scoped NNReal

namespace NlsGge.Atomic.LIB024

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private theorem picard_solution_in_ball {V : E → E} {tmin tmax : ℝ}
    {t₀ : Icc tmin tmax} {x₀ : E} {a L K : ℝ≥0}
    (hPL : IsPicardLindelof (fun _ => V) t₀ x₀ a 0 L K) :
    ∃ x : ℝ → E, x t₀ = x₀ ∧ ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt x (V (x t)) (Icc tmin tmax) t ∧
        x t ∈ closedBall x₀ a := by
  have hx : x₀ ∈ closedBall x₀ ((0 : ℝ≥0) : ℝ) := mem_closedBall_self le_rfl
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hPL hx
  refine ⟨α.compProj, ?_, fun t ht => ⟨?_, α.compProj_mem_closedBall hPL.mul_max_le⟩⟩
  · rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hPL.continuousOn_uncurry
      α.continuous_compProj.continuousOn
      (fun _ _ => α.compProj_mem_closedBall hPL.mul_max_le) x₀ ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

omit [CompleteSpace E] in
/-- Actual uniqueness on a common open interval in any common Lipschitz region. -/
theorem solution_unique_in_lipschitz_region {V : E → E} {W : Set E} {K : ℝ≥0}
    (hV : LipschitzOnWith K V W) {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    {x y : ℝ → E}
    (hx : ∀ t ∈ Ioo a b, HasDerivAt x (V (x t)) t ∧ x t ∈ W)
    (hy : ∀ t ∈ Ioo a b, HasDerivAt y (V (y t)) t ∧ y t ∈ W)
    (hinit : x t₀ = y t₀) : EqOn x y (Ioo a b) :=
  ODE_solution_unique_of_mem_Ioo (fun _ _ => hV) ht₀ hx hy hinit


/-- Every initial point of an open Banach domain carrying a locally Lipschitz
vector field has a local solution inside the domain. Any two solutions with
the same initial value agree on every common open interval containing zero
on which both remain in the displayed common Lipschitz neighborhood. -/
theorem localFlow_exists_unique {U : Set E} {V : E → E}
    (hU : IsOpen U) (hV : LocallyLipschitzOn U V) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ r > (0 : ℝ), ∃ K : ℝ≥0,
      closedBall x₀ r ⊆ U ∧ LipschitzOnWith K V (closedBall x₀ r) ∧
      ∃ ε > (0 : ℝ), ∃ x : ℝ → E, x 0 = x₀ ∧
        (∀ t ∈ Ioo (-ε) ε, HasDerivAt x (V (x t)) t ∧ x t ∈ closedBall x₀ r) ∧
        ∀ (a b : ℝ) (y z : ℝ → E), 0 ∈ Ioo a b →
          (∀ t ∈ Ioo a b, HasDerivAt y (V (y t)) t ∧ y t ∈ closedBall x₀ r) →
          (∀ t ∈ Ioo a b, HasDerivAt z (V (z t)) t ∧ z t ∈ closedBall x₀ r) →
          y 0 = z 0 → EqOn y z (Ioo a b) := by
  obtain ⟨K, s, hs, hVs⟩ := hV hx₀
  rw [hU.nhdsWithin_eq hx₀] at hs
  obtain ⟨d, hd, hds⟩ := Metric.mem_nhds_iff.mp (inter_mem hs (hU.mem_nhds hx₀))
  let r : ℝ := d / 2
  have hr : 0 < r := half_pos hd
  have hBsub : closedBall x₀ r ⊆ s ∩ U :=
    (closedBall_subset_ball (half_lt_self hd)).trans hds
  have hBU : closedBall x₀ r ⊆ U := hBsub.trans inter_subset_right
  have hLip : LipschitzOnWith K V (closedBall x₀ r) :=
    hVs.mono (hBsub.trans inter_subset_left)
  let M : ℝ := (K : ℝ) * r + ‖V x₀‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hb (u : E) (hu : u ∈ closedBall x₀ r) : ‖V u‖ ≤ M := by
    calc
      ‖V u‖ ≤ ‖V u - V x₀‖ + ‖V x₀‖ := norm_le_norm_sub_add _ _
      _ ≤ (K : ℝ) * ‖u - x₀‖ + ‖V x₀‖ := by
        exact add_le_add (by
          simpa only [dist_eq_norm] using
            hLip.dist_le_mul u hu x₀ (mem_closedBall_self hr.le)) le_rfl
      _ ≤ (K : ℝ) * r + ‖V x₀‖ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.mp hu) K.coe_nonneg) le_rfl
      _ ≤ M := by dsimp [M]; linarith
  let aNN : ℝ≥0 := ⟨r, hr.le⟩
  let LNN : ℝ≥0 := ⟨M, hM.le⟩
  let ε : ℝ := r / (2 * M)
  have hε : 0 < ε := div_pos hr (mul_pos (by norm_num) hM)
  let t₀ : Icc (-ε) ε := ⟨0, by constructor <;> linarith⟩
  have htime : M * ε ≤ r := by
    calc
      M * ε = r / 2 := by
        dsimp [ε]
        field_simp [ne_of_gt hM]
      _ ≤ r := by linarith
  have hPL : IsPicardLindelof (fun _ => V) t₀ x₀ aNN 0 LNN K := by
    apply IsPicardLindelof.of_time_independent hb hLip
    change M * max (ε - 0) (0 - (-ε)) ≤ r - 0
    simpa only [sub_zero, zero_sub, neg_neg, max_self] using htime
  obtain ⟨x, hinit, hder⟩ := picard_solution_in_ball hPL
  refine ⟨r, hr, K, hBU, hLip, ε, hε, x, hinit, ?_, ?_⟩
  · intro t ht
    have hx := hder t (Ioo_subset_Icc_self ht)
    exact ⟨hx.1.hasDerivAt (Icc_mem_nhds ht.1 ht.2), hx.2⟩
  · intro a b y z hzero hy hz heq
    exact solution_unique_in_lipschitz_region hLip hzero hy hz heq

end NlsGge.Atomic.LIB024

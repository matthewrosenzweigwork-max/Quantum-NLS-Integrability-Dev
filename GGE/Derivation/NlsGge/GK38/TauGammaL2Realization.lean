import NlsGge.GK38.TauGammaDefs
import NlsGge.GK38.Lib.HilbertValuedAnalytic
import NlsGge.GK38.Lib.InterpolationHilbertOp

/-! Summable coordinates first define an actual Hilbert-valued map. Its norm continuity earns tails. -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

open Classical in
def l2SequenceOf38 (a : ℤ → ℂ) : Lib.L2Z :=
  if h : Summable (fun n : ℤ => ‖a n‖ ^ 2) then
    ⟨a, (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr (by simpa using h)⟩
  else 0

theorem l2SequenceOf_apply38 (a : ℤ → ℂ) (h : Summable (fun n : ℤ => ‖a n‖ ^ 2)) (n : ℤ) :
    l2SequenceOf38 a n = a n := by
  simp only [l2SequenceOf38, dite_eq_left h]

theorem l2SequenceOf_norm_sq38 (a : ℤ → ℂ) (h : Summable (fun n : ℤ => ‖a n‖ ^ 2)) :
    ‖l2SequenceOf38 a‖ ^ 2 = ∑' n : ℤ, ‖a n‖ ^ 2 := by
  have he := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) (l2SequenceOf38 a)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, l2SequenceOf_apply38 a h] using he

theorem local_l2_analytic_realization38 (V : Set PotPair) (a : PotPair → ℤ → ℂ)
    (hV : IsOpen V) (ha : ∀ n : ℤ, AnalyticOnNhd ℂ (fun φ => a φ n) V)
    (hb : ∀ φ₀ ∈ V, IsLocUnifL2Seq a φ₀) :
    ∃ A : PotPair → Lib.L2Z, (∀ φ ∈ V, ∀ n : ℤ, A φ n = a φ n) ∧ AnalyticOnNhd ℂ A V := by
  let A : PotPair → Lib.L2Z := fun φ => l2SequenceOf38 (a φ)
  have hs (φ : PotPair) (hφ : φ ∈ V) : Summable (fun n : ℤ => ‖a φ n‖ ^ 2) := by
    obtain ⟨U, hU, c, hc⟩ := hb φ hφ
    exact (hc φ (mem_of_mem_nhds hU)).1
  have he (φ : PotPair) (hφ : φ ∈ V) (n : ℤ) : A φ n = a φ n :=
    l2SequenceOf_apply38 (a φ) (hs φ hφ) n
  refine ⟨A, he, Lib.analyticOnNhd_of_coords_of_locBdd A hV ?_ ?_⟩
  · intro n φ hφ
    apply (ha n φ hφ).congr
    filter_upwards [hV.mem_nhds hφ] with ψ hψ
    exact (he ψ hψ n).symm
  · intro φ hφ
    obtain ⟨U, hU, c, hc⟩ := hb φ hφ
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hU (hV.mem_nhds hφ))
    refine ⟨r, hr, max c 0 + 1, fun ψ hψ => ?_⟩
    have hψV := (hsub hψ).2
    have hbound := (hc ψ (hsub hψ).1).2
    have hnorm : ‖A ψ‖ ^ 2 = ∑' n : ℤ, ‖a ψ n‖ ^ 2 :=
      l2SequenceOf_norm_sq38 (a ψ) (hs ψ hψV)
    have hc0 : 0 ≤ max c 0 := le_max_right _ _
    have hcle : c ≤ max c 0 := le_max_left _ _
    have hsquare : 0 ≤ (max c 0) ^ 2 := sq_nonneg _
    nlinarith [norm_nonneg (A ψ)]

theorem l2_coordinate_tail38 (a : Lib.L2Z) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) < |n| → ‖a n‖ < ε := by
  have hs : Summable (fun n : ℤ => ‖a n‖ ^ 2) := by
    simpa using (lp.hasSum_norm (p := (2 : ENNReal)) (E := fun _ : ℤ => ℂ) (by norm_num) a).summable
  have ht := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (sq_pos_of_pos hε))
  have hf : {n : ℤ | ¬ ‖a n‖ ^ 2 < ε ^ 2}.Finite := Filter.eventually_cofinite.mp ht
  obtain ⟨b, hb⟩ := (hf.image (fun n : ℤ => |n|)).bddAbove
  refine ⟨b.natAbs, fun n hn => ?_⟩
  have hsq : ‖a n‖ ^ 2 < ε ^ 2 := by
    by_contra hnot
    have hnle : |n| ≤ b := hb ⟨n, hnot, rfl⟩
    have hbabs : b ≤ (b.natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact le_abs_self b
    omega
  nlinarith [norm_nonneg (a n)]

theorem l2_continuous_local_tails38 (A : PotPair → Lib.L2Z) (φ₀ : PotPair)
    (hA : ContinuousAt A φ₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, ∀ φ ∈ V, ∀ n : ℤ,
      (N : ℤ) < |n| → ‖A φ n‖ < ε := by
  obtain ⟨N, hN⟩ := l2_coordinate_tail38 (A φ₀) (ε / 2) (half_pos hε)
  have ht : {φ : PotPair | ‖A φ - A φ₀‖ < ε / 2} ∈ 𝓝 φ₀ := by
    apply Filter.eventually_iff.mp
    have h := Metric.tendsto_nhds.mp hA (ε / 2) (half_pos hε)
    simpa only [dist_eq_norm] using h
  refine ⟨_, ht, N, fun φ hφ n hn => ?_⟩
  have hp := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (A φ - A φ₀) n
  have hcoord : ‖A φ n - A φ₀ n‖ ≤ ‖A φ - A φ₀‖ := by simpa using hp
  have hnorm := norm_le_norm_sub_add (A φ n) (A φ₀ n)
  have hsmall := hN n hn
  change ‖A φ - A φ₀‖ < ε / 2 at hφ
  linarith

end
end NlsGge.GK38

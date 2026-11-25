import NlsGge.GK38.StdRootBranchesPairLocal
import NlsGge.GK38.StdRootBranchesDomain

/-! Genuine pair summability and symmetric multipliability precede all identities. -/
set_option autoImplicit false
open Set Metric Filter Topology SummationFilter
namespace NlsGge.GK38
noncomputable section

theorem root_pair_summable38 (p : PotPair × ℂ) (hp : p ∈ rootDomain38) :
    Summable (fun m : ℕ => ‖Lib.pairDev (fun n => rootFactor38 n p) m‖) := by
  obtain ⟨r, hr, R, hb⟩ := root_pair_local_bound38 p hp
  obtain ⟨s, hs, B, hmass⟩ := rootTauQ_local_mass38 p hp
  have hQ := (hmass p (mem_ball_self hs) hp).1
  exact (Lib.summable_pairMaj hQ R).of_nonneg_of_le (fun _ => norm_nonneg _)
    (hb p (mem_ball_self hr) hp)

theorem root_multipliable38 (p : PotPair × ℂ) (hp : p ∈ rootDomain38) :
    Multipliable (fun n => rootFactor38 n p) (symmetricIcc ℤ) :=
  Lib.multipliable_symm_of_summable_pairDev (root_pair_summable38 p hp)

theorem root_line_majorant38 (p : PotPair × ℂ) (hp : p ∈ rootDomain38)
    (h : PotPair × ℂ) : ∃ ρ : ℝ, 0 < ρ ∧ ∃ q : ℕ → ℝ, Summable q ∧
      ∀ ζ : ℂ, ‖ζ‖ < ρ → p + ζ • h ∈ rootDomain38 → ∀ m : ℕ,
        ‖Lib.pairDev (fun n => rootFactor38 n (p + ζ • h)) m‖ ≤ q m := by
  obtain ⟨r, hr, R, hb⟩ := root_pair_local_bound38 p hp
  obtain ⟨ρ, hρ, q, hq, hQ⟩ := rootTauQ_line_majorant38 p hp h
  refine ⟨min ρ (r / (‖h‖ + 1)), lt_min hρ (by positivity), Lib.pairMaj q R,
    Lib.summable_pairMaj hq R, fun ζ hζ hζU m => ?_⟩
  have hζρ : ‖ζ‖ < ρ := hζ.trans_le (min_le_left _ _)
  have hζr : ‖ζ‖ < r / (‖h‖ + 1) := hζ.trans_le (min_le_right _ _)
  have hball : p + ζ • h ∈ ball p r := by
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul]
    have h1 : ‖ζ‖ * (‖h‖ + 1) < r := (lt_div_iff₀ (by positivity)).mp hζr
    nlinarith [norm_nonneg ζ, norm_nonneg h]
  exact (hb _ hball hζU m).trans (Lib.pairMaj_mono (hQ ζ hζρ hζU) R m)

theorem root_local_mass38 (p : PotPair × ℂ) (hp : p ∈ rootDomain38) :
    ∃ r : ℝ, 0 < r ∧ ∃ B : ℝ, ∀ q ∈ ball p r, q ∈ rootDomain38 →
      Summable (fun m : ℕ => ‖Lib.pairDev (fun n => rootFactor38 n q) m‖) ∧
        (∑' m : ℕ, ‖Lib.pairDev (fun n => rootFactor38 n q) m‖) ≤ B := by
  obtain ⟨r, hr, R, hb⟩ := root_pair_local_bound38 p hp
  obtain ⟨s, hs, B, hQ⟩ := rootTauQ_local_mass38 p hp
  refine ⟨min r s, lt_min hr hs, 2 * Lib.majC1 * B + Lib.majC2 R * Lib.sumInvSq,
    fun q hq hqU => ?_⟩
  have hqr := ball_subset_ball (min_le_left r s) hq
  have hqs := ball_subset_ball (min_le_right r s) hq
  obtain ⟨hQsum, hQbound⟩ := hQ q hqs hqU
  have hsum := root_pair_summable38 q hqU
  refine ⟨hsum, ?_⟩
  refine (Summable.tsum_le_tsum (hb q hqr hqU) hsum (Lib.summable_pairMaj hQsum R)).trans ?_
  refine (Lib.tsum_pairMaj_le hQsum (rootTauQ_nonneg38 q) R).trans ?_
  have h1 := Lib.majC1_nonneg
  nlinarith

theorem canonRoot_analytic38 :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => canonRoot38 p.1 p.2) rootDomain38 := by
  have hprod := Lib.analyticOnNhd_symm_tprod isOpen_rootDomain38 rootFactor_analytic38
    root_line_majorant38 (fun p hp => by
      obtain ⟨r, hr, B, hb⟩ := root_local_mass38 p hp
      exact ⟨r, hr, B, fun q hq hqU => (hb q hq hqU).2⟩)
  exact analyticOnNhd_const.mul hprod

end
end NlsGge.GK38

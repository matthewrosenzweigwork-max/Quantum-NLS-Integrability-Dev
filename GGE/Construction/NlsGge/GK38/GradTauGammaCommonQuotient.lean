import NlsGge.GK38.GradTauGammaLocalQuotient
import NlsGge.GK38.GradTauGammaFarQuotient
import NlsGge.GK38.IsolatingGeometryBounds

/-! One fixed isolating family and one common complex L2 neighborhood control
every signed spectral label. Finite compact circles and actual far asymptotics
are joined before any mode or contour point is quantified. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem k4aCommonCircleQuotient38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ U : Set PotPair, U ∈ nhds φ₀ ∧ U ⊆ gkW ∧ IsOpen U ∧
      ∃ C : ℤ → ℂ, ∃ R : ℤ → ℝ, ∃ K : ℝ, 0 < K ∧
        ∀ φ ∈ U, IsolatingFamily38 φ C R ∧ ∀ n : ℤ, R n ≤ K ∧
          ∀ z ∈ sphere (C n) (R n),
            ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ≤ K ∧ perChar φ z ≠ 0 ∧
              ‖discrim φ z / perChar φ z‖ ≤ K := by
  classical
  obtain ⟨V, hV, hVW, hVo, _, C, R, c, N, hg, hs⟩ :=
    local_isolatingFamily_common38 φ₀ hφ₀
  have hf₀ : IsolatingFamily38 φ₀ C R := ⟨c, N, hg, hs φ₀ (mem_of_mem_nhds hV)⟩
  obtain ⟨L, hL, hshift⟩ := isolating_deviation_bound38 C R N
    (fun n hn => ⟨(hg.2.2.2.2 n hn).1, (hg.2.2.2.2 n hn).2.1⟩)
  have hpoint (n : ℤ) (z : ℂ) (hz : z ∈ sphere (C n) (R n)) :
      ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ≤ L := by
    have hrad : ‖z - C n‖ = R n := mem_sphere_iff_norm.mp hz
    calc
      _ = ‖(z - C n) + (C n - countingCenter38 n)‖ := by
        rw [sub_add_sub_cancel]; rfl
      _ ≤ ‖z - C n‖ + ‖C n - countingCenter38 n‖ := norm_add_le _ _
      _ ≤ L := by rw [hrad]; linarith [hshift n]
  have him (n : ℤ) (z : ℂ) (hz : z ∈ sphere (C n) (R n)) : |z.im| ≤ L := by
    have he : (z - (n : ℂ) * (Real.pi : ℂ)).im = z.im := by simp
    rw [← he]
    exact (Complex.abs_im_le_norm _).trans (hpoint n z hz)
  obtain ⟨Uf, hUf, T, Bf, hBf, hfar⟩ := k4aQuotient_far_bound38 φ₀ (‖φ₀‖ + 1) L
  obtain ⟨q, hq⟩ := exists_nat_gt (T / Real.pi)
  let M : ℕ := max N q
  have hNM : N ≤ M := le_max_left _ _
  have hT : T ≤ countingRadius38 M := by
    have hlt := (div_lt_iff₀ Real.pi_pos).mp hq
    have hqM : (q : ℝ) ≤ (M : ℝ) := by exact_mod_cast (le_max_right N q)
    dsimp [countingRadius38]
    nlinarith [Real.pi_pos]
  have hlocal (n : ℤ) := k4aQuotient_local_bound38 φ₀ (C n) (R n)
    (isolating_radius_pos38 hf₀ n) (isolating_periodic_boundary38 hf₀ n)
  choose Un hUn Bn hBn hbound using hlocal
  let S : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)
  let Bc : ℝ := ∑ n ∈ S, Bn n
  have hBc : 0 ≤ Bc := Finset.sum_nonneg fun n _ => hBn n
  have hfinite : ∀ᶠ φ in nhds φ₀, ∀ n ∈ S, φ ∈ Un n :=
    (Filter.eventually_all_finset S).mpr fun n _ => hUn n
  have hnear := inter_mem hV (inter_mem hUf
    (inter_mem (ball_mem_nhds φ₀ zero_lt_one) hfinite))
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hnear
  let K : ℝ := max L (max Bf Bc) + 1
  have hLK : L ≤ K := by dsimp [K]; linarith [le_max_left L (max Bf Bc)]
  have hfK : Bf ≤ K := by
    dsimp [K]; linarith [(le_max_left Bf Bc).trans (le_max_right L (max Bf Bc))]
  have hcK : Bc ≤ K := by
    dsimp [K]; linarith [(le_max_right Bf Bc).trans (le_max_right L (max Bf Bc))]
  refine ⟨ball φ₀ ρ, ball_mem_nhds φ₀ hρ,
    fun φ hφ => hVW (hρsub hφ).1, isOpen_ball, C, R, K, hL.trans_le hLK, ?_⟩
  intro φ hφ
  obtain ⟨hφV, hφf, hφball, hφfinite⟩ := hρsub hφ
  refine ⟨⟨c, N, hg, hs φ hφV⟩, fun n => ⟨?_, fun z hz => ⟨(hpoint n z hz).trans hLK, ?_⟩⟩⟩
  · exact (le_add_of_nonneg_left (norm_nonneg _)).trans ((hshift n).trans hLK)
  · by_cases hn : |n| ≤ (M : ℤ)
    · have hnS : n ∈ S := Finset.mem_Icc.mpr (abs_le.mp hn)
      have hb := hbound n φ (hφfinite n hnS) z hz
      exact ⟨hb.1, hb.2.trans
        ((Finset.single_le_sum (fun m _ => hBn m) hnS).trans hcK)⟩
    · have hnM : (M : ℤ) < |n| := lt_of_not_ge hn
      have hnN : (N : ℤ) < |n| := lt_of_le_of_lt (by exact_mod_cast hNM) hnM
      obtain ⟨hc, hr, _⟩ := hg.2.2.2.2 n hnN
      have hzs : z ∈ sphere (countingCenter38 n) (Real.pi / 4) := by simpa [hc, hr] using hz
      have hφR : ‖φ‖ ≤ ‖φ₀‖ + 1 := by
        have ht := norm_add_le (φ - φ₀) φ₀
        rw [sub_add_cancel] at ht
        have hd := (mem_ball_iff_norm.mp hφball).le
        linarith
      have hb := hfar φ hφf hφR z (hT.trans (counting_far_sphere_norm38 hnM hzs))
        (counting_small_sphere_separated38 n hzs) (him n z hz)
      exact ⟨hb.1, hb.2.trans hfK⟩

end
end NlsGge.GK38

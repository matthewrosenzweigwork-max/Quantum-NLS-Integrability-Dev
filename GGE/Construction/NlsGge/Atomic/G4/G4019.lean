import Mathlib
import NlsGge.Atomic.G4.G4018
import NlsGge.GK38.IsolatingBoundaryStability
import NlsGge.GK38.DirichletAsymptotics
import NlsGge.GK38.PairAsymptoticsCharacteristic
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.GK38.DirichletLabels
import NlsGge.GK38.CountingLemmaGeometry
import NlsGge.GK38.IsolatingDefs

                                                                              
                                                                                                             
                                                                                
                                                                                                               
                                                                                                             
                                                                                                             
                                                                                                            
                                           
set_option autoImplicit false

open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.G4019Support
noncomputable section

/-- Sine lower bound off the open `π/8` lattice discs (boundaries included). -/
theorem sine_off_eighth_discs (z : ℂ)
    (hdisc : ∀ m : ℤ, Real.pi / 8 ≤ ‖z - (m : ℂ) * (Real.pi : ℂ)‖) :
    Real.exp |z.im| ≤ max (8 * Real.exp (Real.pi / 16)) (2 + 16 / Real.pi) * ‖Complex.sin z‖ := by
  by_cases him : |z.im| ≤ Real.pi / 16
  · obtain ⟨n, hn⟩ := exists_nearest_pi_lattice38 z.re
    have hnorm := Complex.norm_le_abs_re_add_abs_im (z - (n : ℂ) * (Real.pi : ℂ))
    have hnorm' : ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ≤ |z.re - (n : ℝ) * Real.pi| + |z.im| := by
      simpa using hnorm
    have hsmall : Real.pi / 16 ≤ |z.re - (n : ℝ) * Real.pi| := by
      linarith [hdisc n]
    have hchord := Real.mul_abs_le_abs_sin hn
    rw [abs_sin_sub_int_pi38] at hchord
    have h8 : (1 / 8 : ℝ) = (2 / Real.pi) * (Real.pi / 16) := by
      field_simp
      norm_num
    have hsin : 1 / 8 ≤ ‖Complex.sin z‖ := by
      calc (1 / 8 : ℝ) = (2 / Real.pi) * (Real.pi / 16) := h8
        _ ≤ (2 / Real.pi) * |z.re - (n : ℝ) * Real.pi| :=
          mul_le_mul_of_nonneg_left hsmall (by positivity)
        _ ≤ |Real.sin z.re| := hchord
        _ ≤ ‖Complex.sin z‖ := abs_real_sin_le_complex_sin38 z
    have he := Real.exp_le_exp.mpr him
    have hpos := Real.exp_pos (Real.pi / 16)
    calc Real.exp |z.im| ≤ Real.exp (Real.pi / 16) := he
      _ ≤ (8 * Real.exp (Real.pi / 16)) * ‖Complex.sin z‖ := by nlinarith
      _ ≤ max (8 * Real.exp (Real.pi / 16)) (2 + 16 / Real.pi) * ‖Complex.sin z‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · have ht : Real.pi / 16 ≤ |z.im| := (lt_of_not_ge him).le
    have hs := sinh_abs_im_le_complex_sin38 z
    have ht0 : 0 ≤ |z.im| := abs_nonneg _
    have hst : |z.im| ≤ Real.sinh |z.im| := Real.self_le_sinh_iff.mpr ht0
    have he1 : Real.exp (-|z.im|) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hidentity : Real.exp |z.im| = 2 * Real.sinh |z.im| + Real.exp (-|z.im|) := by
      rw [Real.sinh_eq]; ring
    have hunit : 1 ≤ (16 / Real.pi) * Real.sinh |z.im| := by
      have hp : 0 < Real.pi := Real.pi_pos
      have hmul := mul_le_mul_of_nonneg_left (ht.trans hst) (by positivity : 0 ≤ 16 / Real.pi)
      have hcancel : (16 / Real.pi) * (Real.pi / 16) = 1 := by field_simp
      rwa [hcancel] at hmul
    have hexp : Real.exp |z.im| ≤ (2 + 16 / Real.pi) * Real.sinh |z.im| := by
      rw [hidentity]; nlinarith
    calc Real.exp |z.im| ≤ (2 + 16 / Real.pi) * Real.sinh |z.im| := hexp
      _ ≤ (2 + 16 / Real.pi) * ‖Complex.sin z‖ :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ max (8 * Real.exp (Real.pi / 16)) (2 + 16 / Real.pi) * ‖Complex.sin z‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

theorem sineEighthConst_pos :
    0 < max (8 * Real.exp (Real.pi / 16)) (2 + 16 / Real.pi) :=
  lt_of_lt_of_le (by positivity) (le_max_left _ _)

/-- Far from the lattice discs of radius `π/8`, neither `perChar` nor `dirichletChar` vanishes,
uniformly on a neighbourhood of `φ₀` and outside a radius. -/
theorem no_zero_off_eighth_discs (φ₀ : PotPair) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ R : ℝ, ∀ φ ∈ U, ∀ z : ℂ, R ≤ ‖z‖ →
      (∀ m : ℤ, Real.pi / 8 ≤ ‖z - (m : ℂ) * (Real.pi : ℂ)‖) →
      perChar φ z ≠ 0 ∧ dirichletChar φ z ≠ 0 := by
  set C : ℝ := max (8 * Real.exp (Real.pi / 16)) (2 + 16 / Real.pi) with hCdef
  have hC : 0 < C := sineEighthConst_pos
  let δ : ℝ := min 1 (1 / (5 * C ^ 2))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ 1 / (5 * C ^ 2) := min_le_right _ _
  obtain ⟨U₁, hU₁, R₁, h₁⟩ := discrim_asymp φ₀ δ hδ
  obtain ⟨U₂, hU₂, R₂, h₂⟩ := dirichletChar_asymp φ₀ (1 / (2 * C)) (by positivity)
  refine ⟨U₁ ∩ U₂, inter_mem hU₁ hU₂, max R₁ R₂, fun φ hφ z hz hsep => ?_⟩
  have hsin := sine_off_eighth_discs z hsep
  have hexp := Real.exp_pos |z.im|
  have hs : 0 < ‖Complex.sin z‖ := by
    by_contra hneg
    have h0 : ‖Complex.sin z‖ = 0 := le_antisymm (not_lt.mp hneg) (norm_nonneg _)
    rw [h0, mul_zero] at hsin
    linarith
  constructor
  · intro h0
    have he : ‖discrim φ z - 2 * Complex.cos z‖ ≤ δ * Real.exp |z.im| :=
      h₁ φ hφ.1 z ((le_max_left _ _).trans hz)
    have hplus : ‖discrim φ z + 2 * Complex.cos z‖ ≤ (δ + 4) * Real.exp |z.im| := by
      have heq : discrim φ z + 2 * Complex.cos z =
          (discrim φ z - 2 * Complex.cos z) + 4 * Complex.cos z := by ring
      rw [heq]
      calc ‖(discrim φ z - 2 * Complex.cos z) + 4 * Complex.cos z‖
          ≤ ‖discrim φ z - 2 * Complex.cos z‖ + ‖4 * Complex.cos z‖ := norm_add_le _ _
        _ ≤ δ * Real.exp |z.im| + 4 * Real.exp |z.im| := by
          rw [norm_mul, Complex.norm_ofNat]
          exact add_le_add he (mul_le_mul_of_nonneg_left (norm_cos_le_exp_im38 z) (by norm_num))
        _ = _ := by ring
    have halg : perChar φ z - (-4 * Complex.sin z ^ 2) =
        (discrim φ z - 2 * Complex.cos z) * (discrim φ z + 2 * Complex.cos z) := by
      rw [perChar_eq]
      have htrig := Complex.sin_sq_add_cos_sq z
      linear_combination 4 * htrig
    rw [h0, zero_sub] at halg
    have hn : 4 * ‖Complex.sin z‖ ^ 2 ≤ δ * (δ + 4) * (C * ‖Complex.sin z‖) ^ 2 := by
      have h1 : ‖(4 : ℂ) * Complex.sin z ^ 2‖ = 4 * ‖Complex.sin z‖ ^ 2 := by
        rw [norm_mul, norm_pow, Complex.norm_ofNat]
      have h2 : ‖(4 : ℂ) * Complex.sin z ^ 2‖ ≤ (δ * Real.exp |z.im|) * ((δ + 4) * Real.exp |z.im|) := by
        have h3 : (4 : ℂ) * Complex.sin z ^ 2 =
            (discrim φ z - 2 * Complex.cos z) * (discrim φ z + 2 * Complex.cos z) := by
          rw [← halg]; ring
        rw [h3, norm_mul]
        exact mul_le_mul he hplus (norm_nonneg _) (by positivity)
      rw [h1] at h2
      calc 4 * ‖Complex.sin z‖ ^ 2 ≤ (δ * Real.exp |z.im|) * ((δ + 4) * Real.exp |z.im|) := h2
        _ = δ * (δ + 4) * (Real.exp |z.im|) ^ 2 := by ring
        _ ≤ δ * (δ + 4) * (C * ‖Complex.sin z‖) ^ 2 := by gcongr
    have hcoef : δ * (δ + 4) * C ^ 2 ≤ 1 := by
      have hp : δ * (δ + 4) ≤ 5 * δ := by nlinarith
      have h5 := (le_div_iff₀ (by positivity : 0 < 5 * C ^ 2)).mp hδ2
      calc δ * (δ + 4) * C ^ 2 ≤ (5 * δ) * C ^ 2 :=
            mul_le_mul_of_nonneg_right hp (sq_nonneg _)
        _ ≤ 1 := by nlinarith [h5]
    have hs2 : 0 < ‖Complex.sin z‖ ^ 2 := by positivity
    have : δ * (δ + 4) * (C * ‖Complex.sin z‖) ^ 2 ≤ ‖Complex.sin z‖ ^ 2 := by
      calc δ * (δ + 4) * (C * ‖Complex.sin z‖) ^ 2
          = (δ * (δ + 4) * C ^ 2) * ‖Complex.sin z‖ ^ 2 := by ring
        _ ≤ 1 * ‖Complex.sin z‖ ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
        _ = _ := one_mul _
    linarith
  · intro h0
    have h := h₂ φ hφ.2 z ((le_max_right _ _).trans hz)
    rw [h0, zero_sub, norm_neg] at h
    have h' : ‖Complex.sin z‖ ≤ 1 / (2 * C) * (C * ‖Complex.sin z‖) :=
      h.trans (mul_le_mul_of_nonneg_left hsin (by positivity))
    have hh : 1 / (2 * C) * (C * ‖Complex.sin z‖) = ‖Complex.sin z‖ / 2 := by
      field_simp
    rw [hh] at h'
    linarith

/-- Tube lemma for a compact set: nonvanishing at `φ₀` on `K` persists near `φ₀`. -/
theorem eventually_nonvanishing_compact (F : PotPair → ℂ → ℂ)
    (hF : Continuous (fun p : PotPair × ℂ => F p.1 p.2)) (φ₀ : PotPair) (K : Set ℂ)
    (hK : IsCompact K) (hne : ∀ z ∈ K, F φ₀ z ≠ 0) :
    ∀ᶠ φ in 𝓝 φ₀, ∀ z ∈ K, F φ z ≠ 0 := by
  have hopen : IsOpen {p : PotPair × ℂ | F p.1 p.2 ≠ 0} :=
    isOpen_ne_fun hF continuous_const
  have hsub : ({φ₀} : Set PotPair) ×ˢ K ⊆ {p : PotPair × ℂ | F p.1 p.2 ≠ 0} := by
    rintro ⟨a, z⟩ ⟨ha, hz⟩
    rw [mem_singleton_iff] at ha
    subst ha
    exact hne z hz
  obtain ⟨u, v, hu, hv, hsu, htv, huv⟩ := generalized_tube_lemma isCompact_singleton hK hopen hsub
  filter_upwards [hu.mem_nhds (hsu rfl)] with φ hφ z hz
  exact huv (show (φ, z) ∈ u ×ˢ v from ⟨hφ, htv hz⟩)

/-- A collar `{r ≤ ‖z - c‖ ≤ R}` free of zeros of two continuous functions. -/
theorem exists_collar (f g : ℂ → ℂ) (hf : Continuous f) (hg : Continuous g) (c : ℂ) (R : ℝ)
    (hR : 0 < R) (hne : ∀ z ∈ sphere c R, f z ≠ 0 ∧ g z ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ∀ z : ℂ, r ≤ ‖z - c‖ → ‖z - c‖ ≤ R → f z ≠ 0 ∧ g z ≠ 0 := by
  set Z : Set ℂ := closedBall c R ∩ {z | f z = 0 ∨ g z = 0} with hZ
  have hZc : IsCompact Z :=
    (isCompact_closedBall c R).inter_right
      ((isClosed_eq hf continuous_const).union (isClosed_eq hg continuous_const))
  by_cases hne' : Z.Nonempty
  · have hcn : Continuous (fun z : ℂ => ‖z - c‖) := (continuous_id.sub continuous_const).norm
    obtain ⟨z₀, hz₀, hmax⟩ := hZc.exists_isMaxOn hne' hcn.continuousOn
    have hle : ‖z₀ - c‖ ≤ R := by
      have := hz₀.1
      rwa [mem_closedBall, dist_eq_norm] at this
    have hlt : ‖z₀ - c‖ < R := by
      rcases hle.lt_or_eq with h | h
      · exact h
      · exfalso
        have hs : z₀ ∈ sphere c R := by rw [mem_sphere, dist_eq_norm]; exact h
        rcases hz₀.2 with h0 | h0
        · exact (hne z₀ hs).1 h0
        · exact (hne z₀ hs).2 h0
    refine ⟨(‖z₀ - c‖ + R) / 2, by positivity, by linarith, fun z hz1 hz2 => ?_⟩
    by_contra hbad
    have hzZ : z ∈ Z := by
      refine ⟨by rw [mem_closedBall, dist_eq_norm]; exact hz2, ?_⟩
      by_contra hh
      have hh' : ¬ (f z = 0 ∨ g z = 0) := hh
      exact hbad (not_or.mp hh')
    have := hmax hzZ
    simp only [mem_setOf_eq] at this
    linarith [norm_nonneg (z₀ - c)]
  · refine ⟨R / 2, by positivity, by linarith, fun z _ hz2 => ?_⟩
    by_contra hbad
    refine hne' ⟨z, ?_⟩
    refine ⟨by rw [mem_closedBall, dist_eq_norm]; exact hz2, ?_⟩
    by_contra hh
    have hh' : ¬ (f z = 0 ∨ g z = 0) := hh
    exact hbad (not_or.mp hh')

theorem small_collar (φ₀ : PotPair) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hne : ∀ z ∈ sphere c R, perChar φ₀ z ≠ 0 ∧ dirichletChar φ₀ z ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ∀ᶠ φ in 𝓝 φ₀, ∀ z : ℂ, r ≤ ‖z - c‖ → ‖z - c‖ ≤ R →
      perChar φ z ≠ 0 ∧ dirichletChar φ z ≠ 0 := by
  have hcP : Continuous (perChar φ₀) :=
    continuousOn_univ.mp ((analyticOnNhd_perChar_z φ₀).continuousOn)
  have hcD : Continuous (dirichletChar φ₀) :=
    continuousOn_univ.mp ((analyticOnNhd_dirichletChar_z φ₀).continuousOn)
  obtain ⟨r, hr0, hrR, hcol⟩ := exists_collar (perChar φ₀) (dirichletChar φ₀) hcP hcD c R hR hne
  refine ⟨r, hr0, hrR, ?_⟩
  set K : Set ℂ := closedBall c R \ ball c r with hK
  have hKc : IsCompact K := (isCompact_closedBall c R).diff isOpen_ball
  have hKmem : ∀ z : ℂ, r ≤ ‖z - c‖ → ‖z - c‖ ≤ R → z ∈ K := by
    intro z h1 h2
    refine ⟨by rw [mem_closedBall, dist_eq_norm]; exact h2, ?_⟩
    rw [mem_ball, dist_eq_norm, not_lt]; exact h1
  have hKcol : ∀ z ∈ K, perChar φ₀ z ≠ 0 ∧ dirichletChar φ₀ z ≠ 0 := by
    intro z hz
    refine hcol z ?_ ?_
    · have := hz.2; rwa [mem_ball, dist_eq_norm, not_lt] at this
    · have := hz.1; rwa [mem_closedBall, dist_eq_norm] at this
  have hjP : Continuous (fun p : PotPair × ℂ => perChar p.1 p.2) :=
    continuousOn_univ.mp ((analyticOnNhd_isolatingChar_joint38 0).continuousOn)
  have hjD : Continuous (fun p : PotPair × ℂ => dirichletChar p.1 p.2) :=
    continuousOn_univ.mp ((analyticOnNhd_isolatingChar_joint38 1).continuousOn)
  have e1 := eventually_nonvanishing_compact (fun φ z => perChar φ z) hjP φ₀ K hKc
    (fun z hz => (hKcol z hz).1)
  have e2 := eventually_nonvanishing_compact (fun φ z => dirichletChar φ z) hjD φ₀ K hKc
    (fun z hz => (hKcol z hz).2)
  filter_upwards [e1, e2] with φ h1 h2 z hz1 hz2
  exact ⟨h1 z (hKmem z hz1 hz2), h2 z (hKmem z hz1 hz2)⟩

/-- Large index: a zero of `perChar` or `dirichletChar` in the quarter disc lies in the eighth disc. -/
theorem large_index_localization (φ : PotPair) (n : ℤ) (R₀ : ℝ)
    (hR₀ : R₀ ≤ |(n : ℝ)| * Real.pi - Real.pi / 4)
    (hU : ∀ z : ℂ, R₀ ≤ ‖z‖ → (∀ m : ℤ, Real.pi / 8 ≤ ‖z - (m : ℂ) * (Real.pi : ℂ)‖) →
      perChar φ z ≠ 0 ∧ dirichletChar φ z ≠ 0)
    (z : ℂ) (hz : z ∈ ball (countingCenter38 n) (Real.pi / 4))
    (hzero : perChar φ z = 0 ∨ dirichletChar φ z = 0) :
    z ∈ ball (countingCenter38 n) (Real.pi / 8) := by
  by_contra hnot
  have hge : Real.pi / 8 ≤ ‖z - countingCenter38 n‖ := by
    rw [mem_ball, dist_eq_norm, not_lt] at hnot; exact hnot
  have hlt : ‖z - countingCenter38 n‖ < Real.pi / 4 := by
    rw [mem_ball, dist_eq_norm] at hz; exact hz
  have hzR : R₀ ≤ ‖z‖ := by
    have ht := norm_sub_norm_le (countingCenter38 n) z
    rw [norm_sub_rev, norm_countingCenter38] at ht
    linarith
  have hsep : ∀ m : ℤ, Real.pi / 8 ≤ ‖z - (m : ℂ) * (Real.pi : ℂ)‖ := by
    intro m
    by_cases hmn : m = n
    · subst hmn
      exact hge
    · have hc := countingCenter_separated38 (Ne.symm hmn)
      have ht : ‖countingCenter38 n - countingCenter38 m‖ ≤
          ‖z - countingCenter38 m‖ + ‖z - countingCenter38 n‖ := by
        calc _ = ‖(countingCenter38 n - z) + (z - countingCenter38 m)‖ := by congr 1; ring
          _ ≤ ‖countingCenter38 n - z‖ + ‖z - countingCenter38 m‖ := norm_add_le _ _
          _ = _ := by rw [norm_sub_rev (countingCenter38 n) z]; ring
      have : Real.pi / 8 ≤ ‖z - countingCenter38 m‖ := by linarith [Real.pi_pos]
      simpa [countingCenter38] using this
  have hnz := hU z hzR hsep
  rcases hzero with h | h
  · exact hnz.1 h
  · exact hnz.2 h

end
end NlsGge.G4019Support

namespace NlsGge.GKDefinitionDesign
noncomputable section

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.G4019Support

theorem G4019 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) :
  ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ IsOpen V ∧ V ⊆ sourceBetaW ∧
  ∃ (C : ℤ → ℂ) (R r : ℤ → ℝ) (ε M : ℝ), 0 < ε ∧ 0 < M ∧
    (∀ φ ∈ V, IsolatingFamily38 φ C R) ∧
    (∀ n : ℤ, 0 < r n ∧ r n + ε < R n) ∧
    (∀ φ ∈ V, ∀ n : ℤ, gapSegment φ n ⊆ Metric.ball (C n) (r n) ∧
      muSeq φ n ∈ Metric.ball (C n) (r n)) ∧
    ∀ φ ∈ V, ∀ n : ℤ, ∀ lam ∈ Metric.ball (C n) (r n),
      DifferentiableAt ℂ (normalizedZeta n φ) lam ∧
      ‖deriv (normalizedZeta n φ) lam‖ ≤ M := by
  classical
  obtain ⟨V0, hV0n, hV0o, hV0B, C, R, M0, hM0, hfam, hana, hbd⟩ := G4018 φ₀ hφ₀
  have hφ0V0 : φ₀ ∈ V0 := mem_of_mem_nhds hV0n
  obtain ⟨c, N, hgeom, hspec0⟩ := hfam φ₀ hφ0V0
  have hRpos : ∀ n : ℤ, 0 < R n := fun n => (hgeom.1 n).1
  have hcol : ∀ n : ℤ, ∃ r0 : ℝ, 0 < r0 ∧ r0 < R n ∧ ∀ᶠ φ in 𝓝 φ₀, ∀ z : ℂ,
      r0 ≤ ‖z - C n‖ → ‖z - C n‖ ≤ R n → perChar φ z ≠ 0 ∧ dirichletChar φ z ≠ 0 := by
    intro n
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hs⟩ := hspec0.1 n
    exact small_collar φ₀ (C n) (R n) (hRpos n) (fun z hz => ⟨(hs z hz).1, (hs z hz).2.1⟩)
  choose r0 hr0pos hr0lt hr0ev using hcol
  obtain ⟨U₁, hU₁, Rr, hlarge⟩ := no_zero_off_eighth_discs φ₀
  obtain ⟨K, hK⟩ := exists_nat_gt ((Rr + Real.pi / 4) / Real.pi)
  obtain ⟨N', hN'N, hN'K⟩ : ∃ N' : ℕ, N ≤ N' ∧ K ≤ N' := ⟨max N K, le_max_left _ _, le_max_right _ _⟩
  let S : Finset ℤ := Finset.Icc (-(N' : ℤ)) (N' : ℤ)
  have hSmem : ∀ n : ℤ, n ∈ S ↔ |n| ≤ (N' : ℤ) := fun n => by
    simp only [S, Finset.mem_Icc]
    exact abs_le.symm
  have hevS : ∀ᶠ φ in 𝓝 φ₀, ∀ n ∈ S, ∀ z : ℂ, r0 n ≤ ‖z - C n‖ → ‖z - C n‖ ≤ R n →
      perChar φ z ≠ 0 ∧ dirichletChar φ z ≠ 0 :=
    (Filter.eventually_all_finset S).mpr (fun n _ => hr0ev n)
  let Uset : Set PotPair := {φ | ∀ n ∈ S, ∀ z : ℂ, r0 n ≤ ‖z - C n‖ → ‖z - C n‖ ≤ R n →
      perChar φ z ≠ 0 ∧ dirichletChar φ z ≠ 0}
  have hUset : Uset ∈ 𝓝 φ₀ := hevS
  have hSne : S.Nonempty := ⟨0, (hSmem 0).mpr (by simp)⟩
  let ε : ℝ := min (Real.pi / 16) (S.inf' hSne (fun n => (R n - r0 n) / 2))
  have hεpos : 0 < ε :=
    lt_min (by positivity) ((Finset.lt_inf'_iff hSne).mpr (fun n _ => by
      have := hr0lt n
      linarith))
  have hεS : ∀ n ∈ S, ε ≤ (R n - r0 n) / 2 := fun n hn =>
    (min_le_right _ _).trans (Finset.inf'_le _ hn)
  have hεπ : ε ≤ Real.pi / 16 := min_le_left _ _
  let r : ℤ → ℝ := fun n => if |n| ≤ (N' : ℤ) then r0 n else Real.pi / 8
  have hfar : ∀ n : ℤ, ¬ |n| ≤ (N' : ℤ) → C n = countingCenter38 n ∧ R n = Real.pi / 4 := by
    intro n hn
    have h1 : (N' : ℤ) < |n| := lt_of_not_ge hn
    have h2 : (N : ℤ) < |n| := lt_of_le_of_lt (by exact_mod_cast hN'N) h1
    obtain ⟨hC, hR, -⟩ := hgeom.2.2.2.2 n h2
    exact ⟨hC, hR⟩
  have hr : ∀ n : ℤ, 0 < r n ∧ r n + ε < R n := by
    intro n
    by_cases hn : |n| ≤ (N' : ℤ)
    · simp only [r, if_pos hn]
      refine ⟨hr0pos n, ?_⟩
      have h1 := hεS n ((hSmem n).mpr hn)
      have h2 := hr0lt n
      linarith
    · simp only [r, if_neg hn]
      obtain ⟨-, hR⟩ := hfar n hn
      rw [hR]
      constructor
      · positivity
      · linarith [hεπ, Real.pi_pos]
  have hloc : ∀ φ : PotPair, φ ∈ V0 → φ ∈ U₁ → φ ∈ Uset → ∀ n : ℤ,
      lamMinus φ n ∈ Metric.ball (C n) (r n) ∧ lamPlus φ n ∈ Metric.ball (C n) (r n) ∧
        muSeq φ n ∈ Metric.ball (C n) (r n) := by
    intro φ hφV0 hφU hφS
    have key : ∀ n : ℤ, ∀ z : ℂ, z ∈ Metric.ball (C n) (R n) →
        (perChar φ z = 0 ∨ dirichletChar φ z = 0) → z ∈ Metric.ball (C n) (r n) := by
      intro n z hz hzero
      by_cases hn : |n| ≤ (N' : ℤ)
      · simp only [r, if_pos hn]
        by_contra hnot
        have h1 : r0 n ≤ ‖z - C n‖ := by
          rw [mem_ball, dist_eq_norm, not_lt] at hnot
          exact hnot
        have h2 : ‖z - C n‖ ≤ R n := by
          rw [mem_ball, dist_eq_norm] at hz
          exact hz.le
        have h3 := hφS n ((hSmem n).mpr hn) z h1 h2
        rcases hzero with h | h
        · exact h3.1 h
        · exact h3.2 h
      · simp only [r, if_neg hn]
        obtain ⟨hC, hR⟩ := hfar n hn
        rw [hC, hR] at hz
        rw [hC]
        refine large_index_localization φ n Rr ?_ (hlarge φ hφU) z hz hzero
        have h1 : (K : ℤ) < |n| := lt_of_le_of_lt (by exact_mod_cast hN'K) (lt_of_not_ge hn)
        have h2 : (K : ℝ) < |(n : ℝ)| := by
          have : ((K : ℤ) : ℝ) < ((|n| : ℤ) : ℝ) := by exact_mod_cast h1
          simpa using this
        have h3 := (div_lt_iff₀ Real.pi_pos).mp hK
        nlinarith [Real.pi_pos]
    intro n
    obtain ⟨-, -, -, hs⟩ := hfam φ hφV0
    obtain ⟨hseg, hmu, -⟩ := hs.1 n
    have hm : lamMinus φ n ∈ Metric.ball (C n) (R n) := hseg (left_mem_segment ℝ _ _)
    have hp : lamPlus φ n ∈ Metric.ball (C n) (R n) := hseg (right_mem_segment ℝ _ _)
    have hm0 : perChar φ (lamMinus φ n) = 0 := (lamSeq_enumeration38 φ).1 (2 * n)
    have hp0 : perChar φ (lamPlus φ n) = 0 := (lamSeq_enumeration38 φ).1 (2 * n + 1)
    have hu0 : dirichletChar φ (muSeq φ n) = 0 := muSeq_root38 φ n
    exact ⟨key n _ hm (Or.inl hm0), key n _ hp (Or.inl hp0), key n _ hmu (Or.inr hu0)⟩
  let V : Set PotPair := (V0 ∩ interior U₁) ∩ interior Uset
  have hVn : V ∈ 𝓝 φ₀ :=
    inter_mem (inter_mem hV0n (interior_mem_nhds.mpr hU₁)) (interior_mem_nhds.mpr hUset)
  have hVo : IsOpen V := (hV0o.inter isOpen_interior).inter isOpen_interior
  have hVB : V ⊆ sourceBetaW := fun φ hφ => hV0B hφ.1.1
  refine ⟨V, hVn, hVo, hVB, C, R, r, ε, M0 / ε, hεpos, div_pos hM0 hεpos,
    fun φ hφ => hfam φ hφ.1.1, hr, ?_, ?_⟩
  · intro φ hφ n
    obtain ⟨h1, h2, h3⟩ := hloc φ hφ.1.1 (interior_subset hφ.1.2) (interior_subset hφ.2) n
    exact ⟨(convex_ball _ _).segment_subset h1 h2, h3⟩
  · intro φ hφ n lam hlam
    have hrR : r n < R n := by
      have := (hr n).2
      linarith
    have hlamR : lam ∈ Metric.ball (C n) (R n) := ball_subset_ball hrR.le hlam
    have hfan : AnalyticOnNhd ℂ (normalizedZeta n φ) (Metric.ball (C n) (R n)) := fun z hz => by
      have hpair : AnalyticAt ℂ (fun w : ℂ => (φ, w)) z :=
        AnalyticAt.prod analyticAt_const analyticAt_id
      exact (hana n (φ, z) ⟨hφ.1.1, hz⟩).comp hpair
    have hsub : closedBall lam ε ⊆ Metric.ball (C n) (R n) := by
      intro z hz
      rw [mem_closedBall] at hz
      rw [mem_ball] at hlam ⊢
      have h1 := dist_triangle z lam (C n)
      have h2 := (hr n).2
      linarith
    refine ⟨(hfan lam hlamR).differentiableAt, ?_⟩
    have hdiff : DifferentiableOn ℂ (normalizedZeta n φ) (closedBall lam ε) := fun z hz =>
      (hfan z (hsub hz)).differentiableAt.differentiableWithinAt
    have hd : DiffContOnCl ℂ (normalizedZeta n φ) (Metric.ball lam ε) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball lam hεpos.ne']
      exact hdiff
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hεpos hd
      (fun z hz => hbd φ hφ.1.1 n z (hsub (sphere_subset_closedBall hz)))

end
end NlsGge.GKDefinitionDesign

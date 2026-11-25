import NlsGge.GK38.AbelianRatioCutBound
import NlsGge.GK38.IsolatingPersistence
import NlsGge.GK38.AngleRegularFactor
import NlsGge.GK38.AbelianJacobianOffDiagonalRows
import Mathlib.Order.Filter.Finite

/-!
# Local regular-factor bounds on the original filled discs

GK Lemma 15.1, equation (15.7), references/gk/gk.txt:5047-5053.
The tail estimate is extracted from the existing arbitrary-input square-mass
majorant; finitely many original discs use compactness only in the spectral
variable. Compact input globalization keeps the original isolating family.
This is working proof code, not independently accepted graph-node closure.
-/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem gk151_omitted_ratio_original_discs_bound38
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : IsolatingFamily38 φ₀ C R) (s₀ : Lib.L2Seq) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧
      ∃ V : Set Lib.L2Seq, V ∈ 𝓝 s₀ ∧ ∃ B : ℝ, 0 ≤ B ∧
        ∀ φ ∈ U, IsolatingFamily38 φ C R ∧
          ∀ s ∈ V, ∀ m : ℤ, ∀ z ∈ ball (C m) (R m),
            ‖p2OmittedRatio38 m ((φ, s), z)‖ ≤ B := by
  classical
  obtain ⟨Ut, hUt, hUtW, Vt, hVt, Nt, Bt, hBt, ht⟩ :=
    p2OmittedRatio_Dn_l2_majorant38 φ₀ hφ₀ s₀
  obtain ⟨ρ, hρ, c, Ng, hgeom, hpersist⟩ :=
    fixed_family_persistence38 φ₀ C R hfamily
  let N : ℕ := max Nt Ng
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  obtain ⟨ε, hε, Bh, hBh, hh⟩ := p2FiniteCompact_parameter_bound38 S
    (fun m p z => p2OmittedRatio38 m (p, z)) (φ₀, s₀)
    (fun m => closedBall (C m) (R m))
    (fun _ _ => isCompact_closedBall _ _)
    (fun m _ z hz => p2OmittedRatio_analytic38 m ((φ₀, s₀), z)
      (a5OwnClosedBall_omittedDomain38 φ₀ hφ₀ C R hfamily m z hz))
  let U : Set PotPair := Ut ∩ (ball φ₀ ρ ∩ ball φ₀ ε)
  let V : Set Lib.L2Seq := Vt ∩ ball s₀ ε
  refine ⟨U, inter_mem hUt (inter_mem (ball_mem_nhds _ hρ) (ball_mem_nhds _ hε)),
    fun φ hφ => hUtW hφ.1, V, inter_mem hVt (ball_mem_nhds _ hε),
    max Bh (1 + Real.sqrt Bt), hBh.trans (le_max_left _ _), ?_⟩
  intro φ hφ
  refine ⟨⟨c, Ng, hgeom, hpersist φ hφ.2.1⟩, ?_⟩
  intro s hs m z hz
  by_cases hm : (N : ℤ) < |m|
  · have hmt : (Nt : ℤ) < |m| := by
      have hle := le_max_left Nt Ng
      omega
    have hmg : (Ng : ℤ) < |m| := by
      have hle := le_max_right Nt Ng
      omega
    obtain ⟨b, hb0, hbs, hbB, hb⟩ := ht φ hφ.1 s hs.1
    have hterm : b m ^ 2 ≤ ∑' j : ℤ, b j ^ 2 := by
      simpa only [Finset.sum_singleton] using
        hbs.sum_le_tsum ({m} : Finset ℤ) (fun _ _ => sq_nonneg _)
    have hpoint : b m ^ 2 ≤ Bt := hterm.trans hbB
    have hbm : b m ≤ Real.sqrt Bt := by
      nlinarith only [hpoint, Real.sq_sqrt hBt, Real.sqrt_nonneg Bt]
    obtain ⟨hC, hR, _⟩ := hgeom.2.2.2.2 m hmg
    have hzDn : z ∈ Lib.Dn m := by
      simpa only [Lib.Dn, hC, hR, countingCenter38] using hz
    have herror := hb m hmt z hzDn
    have hnorm := norm_le_norm_sub_add (p2OmittedRatio38 m ((φ, s), z)) (1 : ℂ)
    rw [norm_one] at hnorm
    exact (show ‖p2OmittedRatio38 m ((φ, s), z)‖ ≤ 1 + Real.sqrt Bt by
      linarith only [hnorm, herror, hbm]).trans (le_max_right _ _)
  · have hmS : m ∈ S := by
      simpa only [S, Finset.mem_Icc] using abs_le.mp (not_lt.mp hm)
    have hp : (φ, s) ∈ ball (φ₀, s₀) ε := by
      change dist (φ, s) (φ₀, s₀) < ε
      rw [Prod.dist_eq]
      exact max_lt (mem_ball.mp hφ.2.2) (mem_ball.mp hs.2)
    exact (hh (φ, s) hp m hmS z (ball_subset_closedBall hz)).trans (le_max_left _ _)

/-- A compact set of input sequences has one common open input tube, one
potential neighborhood and one bound before all labels. The only placement
premise concerns the omitted nth completion, not the sought regular-factor bound. -/
theorem gk151_regular_factor_compact_original_discs38
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : IsolatingFamily38 φ₀ C R)
    (K : Set Lib.L2Seq) (hK : IsCompact K) :
    ∃ U : Set PotPair, ∃ V : Set Lib.L2Seq, ∃ B : ℝ,
      IsOpen U ∧ IsOpen V ∧ φ₀ ∈ U ∧ U ⊆ gkW ∧ K ⊆ V ∧ 0 ≤ B ∧
      ∀ φ ∈ U, IsolatingFamily38 φ C R ∧
        ∀ s ∈ V, ∀ n : ℤ,
          Lib.sigmaOf s n ∈ closedBall (C n) (R n) →
          ∀ m : ℤ, n ≠ m → ∀ z ∈ ball (C m) (R m),
            AnalyticAt ℂ (angleRegularFactor38 n m) ((φ, s), z) ∧
              ‖angleRegularFactor38 n m ((φ, s), z)‖ ≤ B * Lib.c3w n m := by
  classical
  choose U hU hUW V hV B hB hspec using
    (fun s₀ : Lib.L2Seq =>
      gk151_omitted_ratio_original_discs_bound38 φ₀ hφ₀ C R hfamily s₀)
  obtain ⟨F, _hFK, hcover⟩ := hK.elim_nhds_subcover
    (fun s₀ => interior (V s₀))
    (fun s₀ _ => isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr (hV s₀)))
  let H : Set PotPair := {φ | ∀ s₀ ∈ F, φ ∈ U s₀}
  have hH : H ∈ nhds φ₀ := F.eventually_all.mpr (fun s₀ _ => hU s₀)
  obtain ⟨ρ, hρ, c, N, hgeom, hpersist⟩ := fixed_family_persistence38 φ₀ C R hfamily
  let U₀ : Set PotPair := gkW ∩ (ball φ₀ ρ ∩ interior H)
  let V₀ : Set Lib.L2Seq := ⋃ s₀ ∈ F, interior (V s₀)
  have hc : 0 ≤ c := (by norm_num : (0 : ℝ) ≤ 1).trans hgeom.2.2.1
  have hsum : 0 ≤ ∑ s₀ ∈ F, B s₀ := Finset.sum_nonneg (fun s₀ _ => hB s₀)
  refine ⟨U₀, V₀, c * ∑ s₀ ∈ F, B s₀,
    isOpen_gkW.inter (isOpen_ball.inter isOpen_interior),
    isOpen_biUnion (fun s₀ _ => isOpen_interior),
    ⟨hφ₀, mem_ball_self hρ, mem_interior_iff_mem_nhds.mpr hH⟩,
    fun φ hφ => hφ.1, hcover, mul_nonneg hc hsum, ?_⟩
  intro φ hφ
  have hfam : IsolatingFamily38 φ C R := ⟨c, N, hgeom, hpersist φ hφ.2.1⟩
  refine ⟨hfam, ?_⟩
  intro s hs n hσ m hnm z hz
  obtain ⟨s₀, hs₀F, hs₀V⟩ := mem_iUnion₂.mp hs
  have hφU : φ ∈ U s₀ := (interior_subset hφ.2.2) s₀ hs₀F
  have hratio := (hspec s₀ φ hφU).2 s (interior_subset hs₀V) m z hz
  have hrecip := P3JacobianColumns.original_disc_reciprocal_bound
    C R c N hgeom n m hnm s hσ z (ball_subset_closedBall hz)
  have hw : Lib.c3w m n = Lib.c3w n m := by
    simp only [Lib.c3w, abs_sub_comm]
  rw [hw] at hrecip
  refine ⟨angleRegularFactor_joint_own_disc38 n m hnm φ hφ.1 C R hfam
    s hσ z (ball_subset_closedBall hz), ?_⟩
  have heq : ‖angleRegularFactor38 n m ((φ, s), z)‖ =
      ‖p2OmittedRatio38 m ((φ, s), z)‖ * ‖1 / (Lib.sigmaOf s n - z)‖ := by
    simp only [angleRegularFactor38, norm_mul, Complex.norm_I, one_mul, div_eq_mul_inv]
  rw [heq]
  calc
    _ ≤ B s₀ * (c * Lib.c3w n m) :=
      mul_le_mul hratio hrecip (norm_nonneg _) (hB s₀)
    _ ≤ (∑ t ∈ F, B t) * (c * Lib.c3w n m) :=
      mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun t _ => hB t) hs₀F)
        (mul_nonneg hc (Lib.c3w_nonneg n m))
    _ = (c * ∑ t ∈ F, B t) * Lib.c3w n m := by ring

end
end NlsGge.GK38

import Mathlib
import NlsGge.GK38.IsolatingPersistence
import NlsGge.GK38.TauGammaContourGlue
import NlsGge.GK38.StdRootBranchesScalar
import NlsGge.GK38.IsolatingDistance

/- G2-019 PRODUCTION01 (proof development landing kit; HELD for landing). Source: proof development/G2019_PROOF02.lean (author proof development; independent review proof development/REVIEW_G2019_01.md), byte-identical except this header and the removed `#print axioms` line. Target NlsGge/Atomic/G2/G2019.lean. -/
/- G2-019 PROOF01 (proof development, AUTHOR; not self-reviewed).
   `standardRoot` copied verbatim from DEFINITIONS/G2.lean.md lines 44-46.
   Production identities used: tau_pair_mean38, gamma2_pair_gap38 (TauGammaContourGlue),
   stdRoot_sq38 (StdRootBranchesScalar), ballDistance38_le_pair / ballDistance38_eq
   (IsolatingDistance), fixed_family_persistence38 (IsolatingPersistence). -/

set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def standardRoot (φ : PotPair) (n : ℤ) (z : ℂ) : ℂ :=
  stdRoot38 (tauN φ n) (gamma2 φ n) z

theorem g2019_leaf_family (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ U : Set PotPair, IsOpen U ∧ φ₀ ∈ U ∧ U ⊆ gkW ∧
      ∃ C : ℤ → ℂ, ∃ R : ℤ → ℝ, ∃ c : ℝ, ∃ N : ℕ,
        IsolatingGeometry38 C R c N ∧ ∀ φ ∈ U, IsolatingSpectral38 φ C R := by
  obtain ⟨u, ρ0, hcert, hmem⟩ := hφ₀
  obtain ⟨hρ0, C, R, c, N, hgeom, hall⟩ := hcert
  have hfam : IsolatingFamily38 φ₀ C R := ⟨c, N, hgeom, hall φ₀ hmem⟩
  obtain ⟨ρ, hρ, c', N', hgeom', hsp⟩ := fixed_family_persistence38 φ₀ C R hfam
  refine ⟨ball φ₀ ρ ∩ ball (realSlice u) ρ0, ?_, ⟨mem_ball_self hρ, hmem⟩, ?_,
    C, R, c', N', hgeom', ?_⟩
  · exact Metric.isOpen_ball.inter Metric.isOpen_ball
  · rintro φ ⟨_, hφ⟩
    exact ⟨u, ρ0, ⟨hρ0, C, R, c, N, hgeom, hall⟩, hφ⟩
  · rintro φ ⟨hφ1, _⟩
    exact hsp φ hφ1

/-- The standard root is the pair root with the production midpoint and gap. -/
theorem g2019_standardRoot_pair (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (z : ℂ) :
    standardRoot φ n z = stdRoot38 ((lamMinus φ n + lamPlus φ n) / 2)
      ((lamPlus φ n - lamMinus φ n) ^ 2) z := by
  have h1 : tauN φ n = (lamPlus φ n + lamMinus φ n) / 2 :=
    tau_pair_mean38 discC discR isolating_selectors_admissible38 φ hφ n
  have h2 : gamma2 φ n = (lamPlus φ n - lamMinus φ n) ^ 2 :=
    gamma2_pair_gap38 discC discR isolating_selectors_admissible38 φ hφ n
  unfold standardRoot
  rw [h1, h2, add_comm (lamPlus φ n) (lamMinus φ n)]

theorem g2019_radius_bound (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℤ, R k ≤ M := by
  have hs : 0 ≤ ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), R j :=
    Finset.sum_nonneg (fun j _ => (hg.1 j).1.le)
  have hp := Real.pi_pos
  refine ⟨(∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), R j) + Real.pi / 4, by linarith, ?_⟩
  intro k
  by_cases hk : (N : ℤ) < |k|
  · rw [(hg.2.2.2.2 k hk).2.1]
    linarith
  · have hmem : k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      rw [Finset.mem_Icc]
      exact abs_le.mp (not_lt.mp hk)
    have := Finset.single_le_sum (fun j _ => (hg.1 j).1.le) hmem
    linarith

theorem g2019_geometry_mono (C : ℤ → ℂ) (R : ℤ → ℝ) (c c' : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hcc : c ≤ c') :
    IsolatingGeometry38 C R c' N := by
  have hc1 : 1 ≤ c := hg.2.2.1
  have hc0 : 0 < c := by linarith
  refine ⟨hg.1, hg.2.1, le_trans hc1 hcc, ?_, hg.2.2.2.2⟩
  intro m n hmn
  obtain ⟨hl, hu⟩ := hg.2.2.2.1 m n hmn
  have habs : 0 ≤ |((m - n : ℤ) : ℝ)| := abs_nonneg _
  constructor
  · have hinv : c'⁻¹ ≤ c⁻¹ := inv_anti₀ hc0 hcc
    exact le_trans (mul_le_mul_of_nonneg_right hinv habs) hl
  · exact le_trans hu (mul_le_mul_of_nonneg_right hcc habs)

theorem g2019_closed_ball_dist (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) {m n : ℤ} {z w : ℂ}
    (hz : z ∈ closedBall (C m) (R m)) (hw : w ∈ ball (C n) (R n)) :
    ballDistance38 (C m) (C n) (R m) (R n) ≤ dist z w := by
  have hRm : 0 < R m := (hg.1 m).1
  have hsub : ball (C m) (R m) ⊆ {x : ℂ | ballDistance38 (C m) (C n) (R m) (R n) ≤ dist x w} :=
    fun x hx => ballDistance38_le_pair (C m) (C n) (R m) (R n) hx hw
  have hclosed : IsClosed {x : ℂ | ballDistance38 (C m) (C n) (R m) (R n) ≤ dist x w} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hcl := closure_minimal hsub hclosed
  rw [closure_ball (C m) hRm.ne'] at hcl
  exact hcl hz

theorem g2019_centre_dist (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (m n : ℤ) (hmn : m ≠ n) :
    dist (C m) (C n) ≤ R m + R n + c * |((m - n : ℤ) : ℝ)| := by
  have hRm : 0 < R m := (hg.1 m).1
  have hRn : 0 < R n := (hg.1 n).1
  have hu := (hg.2.2.2.1 m n hmn).2
  have he := ballDistance38_eq (C m) (C n) hRm hRn
  have h1 : dist (C m) (C n) - R m - R n ≤ ballDistance38 (C m) (C n) (R m) (R n) := by
    rw [he]
    exact le_max_right _ _
  linarith

theorem g2019_norm_upper (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (M : ℝ) (hRM : ∀ k : ℤ, R k ≤ M)
    {m n : ℤ} (hmn : m ≠ n) {w z : ℂ} (hw : w ∈ ball (C n) (R n))
    (hz : z ∈ closedBall (C m) (R m)) :
    ‖w - z‖ ≤ (4 * M + c) * |((m - n : ℤ) : ℝ)| := by
  have hd0 : 0 ≤ |((m - n : ℤ) : ℝ)| := abs_nonneg _
  have hd1 : (1 : ℝ) ≤ |((m - n : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmn)
  have hM : 0 ≤ M := le_trans (hg.1 m).1.le (hRM m)
  have hcd : dist (C n) (C m) ≤ R m + R n + c * |((m - n : ℤ) : ℝ)| := by
    rw [dist_comm]
    exact g2019_centre_dist C R c N hg m n hmn
  have hwn : dist w (C n) ≤ R n := (mem_ball.mp hw).le
  have hmz : dist (C m) z ≤ R m := by
    rw [dist_comm]
    exact mem_closedBall.mp hz
  have t := dist_triangle4 w (C n) (C m) z
  rw [← dist_eq_norm]
  nlinarith [mul_nonneg hM (sub_nonneg.mpr hd1), hRM m, hRM n]

theorem g2019_root_sep_core (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (M : ℝ) (hM : 0 ≤ M) (hRM : ∀ k : ℤ, R k ≤ M)
    {m n : ℤ} (hmn : m ≠ n) (a b : ℂ)
    (hseg : segment ℝ a b ⊆ ball (C n) (R n)) (z : ℂ)
    (hz : z ∈ closedBall (C m) (R m)) :
    c⁻¹ * |((m - n : ℤ) : ℝ)| ≤ ‖stdRoot38 ((a + b) / 2) ((b - a) ^ 2) z‖ ∧
      ‖stdRoot38 ((a + b) / 2) ((b - a) ^ 2) z‖ ≤ (4 * M + c) * |((m - n : ℤ) : ℝ)| := by
  have hc1 : 1 ≤ c := hg.2.2.1
  have hc0 : 0 < c := by linarith
  have hd1 : (1 : ℝ) ≤ |((m - n : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmn)
  have hd0 : 0 ≤ |((m - n : ℤ) : ℝ)| := abs_nonneg _
  have hD : c⁻¹ * |((m - n : ℤ) : ℝ)| ≤ ballDistance38 (C m) (C n) (R m) (R n) :=
    (hg.2.2.2.1 m n hmn).1
  have hpos : 0 < c⁻¹ * |((m - n : ℤ) : ℝ)| :=
    mul_pos (inv_pos.mpr hc0) (by linarith)
  have ha : a ∈ ball (C n) (R n) := hseg (left_mem_segment ℝ a b)
  have hb : b ∈ ball (C n) (R n) := hseg (right_mem_segment ℝ a b)
  have hzn : z ∉ segment ℝ a b := by
    intro hzs
    have h0 := g2019_closed_ball_dist C R c N hg hz (hseg hzs)
    rw [dist_self] at h0
    linarith
  have hsq : ‖stdRoot38 ((a + b) / 2) ((b - a) ^ 2) z‖ ^ 2 = ‖a - z‖ * ‖b - z‖ := by
    rw [← norm_pow, stdRoot_sq38 a b z hzn, norm_mul]
  have hpa : ballDistance38 (C m) (C n) (R m) (R n) ≤ ‖a - z‖ := by
    rw [← dist_eq_norm, dist_comm]
    exact g2019_closed_ball_dist C R c N hg hz ha
  have hpb : ballDistance38 (C m) (C n) (R m) (R n) ≤ ‖b - z‖ := by
    rw [← dist_eq_norm, dist_comm]
    exact g2019_closed_ball_dist C R c N hg hz hb
  have hD0 : 0 ≤ ballDistance38 (C m) (C n) (R m) (R n) := le_trans hpos.le hD
  have hlow : ballDistance38 (C m) (C n) (R m) (R n) ≤
      ‖stdRoot38 ((a + b) / 2) ((b - a) ^ 2) z‖ := by
    nlinarith [mul_le_mul hpa hpb hD0 (le_trans hD0 hpa),
      norm_nonneg (stdRoot38 ((a + b) / 2) ((b - a) ^ 2) z)]
  have hA := g2019_norm_upper C R c N hg M hRM hmn ha hz
  have hB := g2019_norm_upper C R c N hg M hRM hmn hb hz
  have hK0 : 0 ≤ (4 * M + c) * |((m - n : ℤ) : ℝ)| := mul_nonneg (by linarith) hd0
  refine ⟨le_trans hD hlow, ?_⟩
  nlinarith [mul_le_mul hA hB (norm_nonneg (b - z)) hK0,
    norm_nonneg (stdRoot38 ((a + b) / 2) ((b - a) ^ 2) z)]

theorem G2_019 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ U : Set PotPair, IsOpen U ∧ φ₀ ∈ U ∧ U ⊆ gkW ∧
      ∃ C : ℤ → ℂ, ∃ R : ℤ → ℝ, ∃ c : ℝ, ∃ N : ℕ,
        IsolatingGeometry38 C R c N ∧
        (∀ φ ∈ U, IsolatingSpectral38 φ C R) ∧
        ∀ φ ∈ U, ∀ m n : ℤ, m ≠ n →
          ∀ z ∈ Metric.closedBall (C m) (R m),
            c⁻¹ * |((m-n : ℤ) : ℝ)| ≤ ‖standardRoot φ n z‖ ∧
            ‖standardRoot φ n z‖ ≤ c * |((m-n : ℤ) : ℝ)| := by
  obtain ⟨U, hU, hφU, hUgk, C, R, c, N, hgeom, hsp⟩ := g2019_leaf_family φ₀ hφ₀
  obtain ⟨M, hM0, hRM⟩ := g2019_radius_bound C R c N hgeom
  have hc1 : 1 ≤ c := hgeom.2.2.1
  have hc0 : 0 < c := by linarith
  have hcM : c ≤ 4 * M + c := by linarith
  refine ⟨U, hU, hφU, hUgk, C, R, 4 * M + c, N,
    g2019_geometry_mono C R c (4 * M + c) N hgeom hcM, hsp, ?_⟩
  intro φ hφ m n hmn z hz
  have hφgk := hUgk hφ
  have hs := ((hsp φ hφ).1 n).1
  rw [g2019_standardRoot_pair φ hφgk n z]
  have hk := g2019_root_sep_core C R c N hgeom M hM0 hRM hmn _ _ hs z hz
  exact ⟨le_trans (mul_le_mul_of_nonneg_right (inv_anti₀ hc0 hcM) (abs_nonneg _)) hk.1, hk.2⟩

end
end NlsGge.GKDefinitionDesign


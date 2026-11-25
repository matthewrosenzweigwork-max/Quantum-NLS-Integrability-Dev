import NlsGge.GK38.TauGammaValueBounds
import NlsGge.GK38.DirichletL2

/-!
# Local square mass for the GK15.1 inverse-distance numerator

The real nonnegative sequence
  gap_m + |mu_m - tau_m|
is embedded into C so it can feed the generic inverse-distance analytic-series
library. This is ordinary working infrastructure.
-/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

def gk151BetaMass38 (phi : PotPair) (m : ℤ) : ℂ :=
  ((‖lamPlus phi m - lamMinus phi m‖ +
    ‖muSeq phi m - tauN phi m‖ : ℝ) : ℂ)

theorem norm_gk151BetaMass38 (phi : PotPair) (m : ℤ) :
    ‖gk151BetaMass38 phi m‖ =
      ‖lamPlus phi m - lamMinus phi m‖ +
        ‖muSeq phi m - tauN phi m‖ := by
  unfold gk151BetaMass38
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]

theorem gk151BetaMass_local_l2_38 (phi0 : PotPair) (hphi0 : phi0 ∈ gkW) :
    ∃ U : Set PotPair, U ∈ 𝓝 phi0 ∧ U ⊆ gkW ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ phi ∈ U,
        Summable (fun m : ℤ => ‖gk151BetaMass38 phi m‖^2) ∧
        (∑' m : ℤ, ‖gk151BetaMass38 phi m‖^2) ≤ M := by
  obtain ⟨Ug, hUg, hUgW, Bg, hBg, hg⟩ :=
    tauGamma_common_value_bound38 discC discR
      isolating_selectors_admissible38 phi0 hphi0
  obtain ⟨Um, hUm, Bm, hBm, hm⟩ := muSeq_local_l2_38 phi0
  let U : Set PotPair := Ug ∩ Um
  let M : ℝ := 6 * Bg + 4 * Bm
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  refine ⟨U, inter_mem hUg hUm, fun phi hphi => hUgW hphi.1,
    M, hM, ?_⟩
  intro phi hphi
  have hphiGK := hUgW hphi.1
  obtain ⟨htau0, hgap, _hgamma, htauB0, hgapB, _hgammaB⟩ := hg phi hphi.1
  have htau : Summable (fun n : ℤ =>
      ‖tauN phi n - (n : ℂ) * (Real.pi : ℂ)‖^2) := by
    simpa only [tauN] using htau0
  have htauB : (∑' n : ℤ,
      ‖tauN phi n - (n : ℂ) * (Real.pi : ℂ)‖^2) ≤ Bg := by
    simpa only [tauN] using htauB0
  obtain ⟨hmu, hmuB⟩ := hm phi hphi.2
  have hmutau_point (m : ℤ) :
      ‖muSeq phi m - tauN phi m‖^2 ≤
        2 * (‖muSeq phi m - (m : ℂ) * (Real.pi : ℂ)‖^2 +
          ‖tauN phi m - (m : ℂ) * (Real.pi : ℂ)‖^2) := by
    have he :
        muSeq phi m - tauN phi m =
          (muSeq phi m - (m : ℂ) * (Real.pi : ℂ)) +
            -(tauN phi m - (m : ℂ) * (Real.pi : ℂ)) := by ring
    rw [he]
    simpa only [norm_neg] using
      norm_add_square_le_twice38
        (muSeq phi m - (m : ℂ) * (Real.pi : ℂ))
        (-(tauN phi m - (m : ℂ) * (Real.pi : ℂ)))
  have hmutauDom :
      Summable (fun m : ℤ =>
        2 * (‖muSeq phi m - (m : ℂ) * (Real.pi : ℂ)‖^2 +
          ‖tauN phi m - (m : ℂ) * (Real.pi : ℂ)‖^2)) :=
    (hmu.add htau).mul_left 2
  have hmutau :
      Summable (fun m : ℤ => ‖muSeq phi m - tauN phi m‖^2) :=
    hmutauDom.of_nonneg_of_le (fun m => sq_nonneg _) hmutau_point
  have hmutauB :
      (∑' m : ℤ, ‖muSeq phi m - tauN phi m‖^2) ≤
        2 * (Bm + Bg) := by
    calc
      _ ≤ ∑' m : ℤ,
          2 * (‖muSeq phi m - (m : ℂ) * (Real.pi : ℂ)‖^2 +
            ‖tauN phi m - (m : ℂ) * (Real.pi : ℂ)‖^2) :=
        hmutau.tsum_le_tsum hmutau_point hmutauDom
      _ = 2 * ((∑' m : ℤ,
          ‖muSeq phi m - (m : ℂ) * (Real.pi : ℂ)‖^2) +
          (∑' m : ℤ,
          ‖tauN phi m - (m : ℂ) * (Real.pi : ℂ)‖^2)) := by
        rw [tsum_mul_left, hmu.tsum_add htau]
      _ ≤ 2 * (Bm + Bg) :=
        mul_le_mul_of_nonneg_left (add_le_add hmuB htauB) (by norm_num)
  have hmass_point (m : ℤ) :
      ‖gk151BetaMass38 phi m‖^2 ≤
        2 * (‖lamPlus phi m - lamMinus phi m‖^2 +
          ‖muSeq phi m - tauN phi m‖^2) := by
    rw [norm_gk151BetaMass38]
    nlinarith [sq_nonneg
      (‖lamPlus phi m - lamMinus phi m‖ -
        ‖muSeq phi m - tauN phi m‖)]
  have hmassDom :
      Summable (fun m : ℤ =>
        2 * (‖lamPlus phi m - lamMinus phi m‖^2 +
          ‖muSeq phi m - tauN phi m‖^2)) :=
    (hgap.add hmutau).mul_left 2
  have hmass :=
    hmassDom.of_nonneg_of_le (fun m => sq_nonneg _) hmass_point
  refine ⟨hmass, ?_⟩
  calc
    (∑' m : ℤ, ‖gk151BetaMass38 phi m‖^2) ≤
        ∑' m : ℤ,
          2 * (‖lamPlus phi m - lamMinus phi m‖^2 +
            ‖muSeq phi m - tauN phi m‖^2) :=
      hmass.tsum_le_tsum hmass_point hmassDom
    _ = 2 * ((∑' m : ℤ, ‖lamPlus phi m - lamMinus phi m‖^2) +
        (∑' m : ℤ, ‖muSeq phi m - tauN phi m‖^2)) := by
      rw [tsum_mul_left, hgap.tsum_add hmutau]
    _ ≤ 2 * (Bg + 2 * (Bm + Bg)) :=
      mul_le_mul_of_nonneg_left (add_le_add hgapB hmutauB) (by norm_num)
    _ = M := by
      dsimp [M]
      ring

end
end NlsGge.GK38

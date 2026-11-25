import Mathlib
import NlsGge.ThirdConsultation.M.M029Core
import NlsGge.Atomic.M.M025Weighted
import NlsGge.Atomic.M.M027
import NlsGge.GK38.PeriodicLabellingCanonical

/-!
# M-030 support: `local_roots_gap_square_bound` (proof development, AUTHOR; not self-reviewed)

The ROOT form of Molnar Lemma 10: for ANY two zeros `xi1, xi2` of `schurDet` in the closed local spectral disc,
`|xi1 - xi2|^2 <= 6 sup |b_+ b_-|` (the sup taken over the whole spectral strip, with nonemptiness and boundedness).
Route (Pro/packet skeleton): equal diagonals `a` (landed M-025), Cauchy derivative estimate `|a'| <= A / (9/10) <= 5/36`
on the closed disc of radius `pi/5` (the disc of radius `9/10` around each point stays in the strip), the root identity
`(xi - c - a(xi))^2 = b_+ b_-(xi)`, then `(31/36)|xi1-xi2| <= |d1| + |d2|` and `(d1+d2)^2 <= 2(d1^2+d2^2) <= 4 sup`.
No multiplicity is used; the label identification `gap = xi_+ - xi_-` (Pro's M-030 head) is NOT proved here.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation

theorem local_roots_gap_square_bound
    (w : ℤ → ℝ) (hw : OneDerivativeWeight w) (φ : PotPair)
    (hφ : MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ)
    (hthreshold : 8 * MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
      NlsGge.Atomic.M.M054.indexWeight n)
    (ξ1 ξ2 : ℂ)
    (h1 : ξ1 ∈ MTwoMode.localSpectralDisc w φ n)
    (h2 : ξ2 ∈ MTwoMode.localSpectralDisc w φ n)
    (hz1 : ξ1 ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hz2 : ξ2 ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hd1 : MTwoMode.schurDet φ n ξ1 hz1 = 0)
    (hd2 : MTwoMode.schurDet φ n ξ2 hz2 = 0) :
    let P : Set ℝ := {r : ℝ | ∃ z : ℂ,
      ∃ hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n,
        r = ‖MTwoMode.offDiagonal φ n z hz true *
          MTwoMode.offDiagonal φ n z hz false‖}
    P.Nonempty ∧ BddAbove P ∧ ‖ξ1 - ξ2‖ ^ 2 ≤ 6 * sSup P := by
  intro P
  classical
  set Q := MTwoMode.potentialCoefficientNorm w φ with hQdef
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  set ρ := NlsGge.Atomic.M.M054.indexWeight n with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]; unfold NlsGge.Atomic.M.M054.indexWeight; have := abs_nonneg (n : ℝ); linarith
  set c : ℂ := (n : ℂ) * (Real.pi : ℂ) with hc
  set S := NlsGge.Atomic.KST004.spectralStrip n with hS
  set A : ℝ := Q ^ 2 / ρ with hA
  set B : ℝ := Real.sqrt 2 * Q / NlsGge.Atomic.M.M054.indexWeight (2 * n) with hB
  have hA0 : 0 ≤ A := by positivity
  have hA8 : A ≤ 1 / 8 := by
    rw [hA, div_le_iff₀ hρpos]; linarith
  have hpi : 3 < Real.pi := Real.pi_gt_three
  -- the diagonal extension and its bound
  obtain ⟨a, haan, haeq⟩ := schur_diagonal_analytic_extension w hw φ hφ n hthreshold true
  have haA : ∀ z (hz : z ∈ S), ‖a z‖ ≤ A := by
    intro z hz
    have := schur_diagonal_bound w hw φ hφ n z hz hthreshold true
    rw [haeq z hz]; simpa using this
  have hPeq : ∀ z (hz : z ∈ S), MTwoMode.schurDiagonalMinus φ n z hz = a z := by
    intro z hz
    rw [haeq z hz]
    simp only [if_true]
    exact (schur_diagonals_equal_weighted w hw φ hφ n z hz hthreshold).symm
  -- the product set
  have hPne : P.Nonempty := by
    have hcS : c ∈ S := by
      show |c.re - (n : ℝ) * Real.pi| ≤ Real.pi / 2
      simp [hc]; positivity
    exact ⟨_, c, hcS, rfl⟩
  have hPbdd : BddAbove P := by
    refine ⟨B ^ 2, ?_⟩
    rintro r ⟨z, hz, rfl⟩
    exact NlsGge.ThirdConsultation.M029R.offdiag_prod_le w hw φ hφ n z hz hthreshold
  refine ⟨hPne, hPbdd, ?_⟩
  set M := sSup P with hM
  have hM0 : 0 ≤ M := by
    obtain ⟨r, hr⟩ := hPne
    obtain ⟨z, hz, rfl⟩ := hr
    exact le_trans (norm_nonneg _) (le_csSup hPbdd ⟨z, hz, rfl⟩)
  -- root identity
  have hroot : ∀ (ξ : ℂ) (hz : ξ ∈ S), MTwoMode.schurDet φ n ξ hz = 0 →
      ‖ξ - c - a ξ‖ ^ 2 ≤ M := by
    intro ξ hz hd
    unfold MTwoMode.schurDet MTwoMode.schurMatrix at hd
    rw [Matrix.det_fin_two_of] at hd
    have hPlus : MTwoMode.schurDiagonalPlus φ n ξ hz = a ξ := by
      have := haeq ξ hz; simpa using this.symm
    rw [hPlus, hPeq ξ hz] at hd
    have e : (ξ - c - a ξ) ^ 2 = MTwoMode.offDiagonal φ n ξ hz true *
        MTwoMode.offDiagonal φ n ξ hz false := by
      linear_combination hd
    rw [← norm_pow, e]
    exact le_csSup hPbdd ⟨ξ, hz, rfl⟩
  have hr1 := hroot ξ1 hz1 hd1
  have hr2 := hroot ξ2 hz2 hd2
  -- Lipschitz bound for a on the closed disc of radius pi/5
  have hK : ∀ z ∈ Metric.closedBall c (Real.pi / 5), Metric.closedBall z (9 / 10) ⊆ S := by
    intro z hz w hw'
    rw [Metric.mem_closedBall, dist_eq_norm] at hz hw'
    show |w.re - (n : ℝ) * Real.pi| ≤ Real.pi / 2
    have e1 : |z.re - (n : ℝ) * Real.pi| ≤ ‖z - c‖ := by
      have := Complex.abs_re_le_norm (z - c)
      simpa [hc] using this
    have e2 : |w.re - z.re| ≤ ‖w - z‖ := by
      have := Complex.abs_re_le_norm (w - z)
      simpa using this
    have : |w.re - (n : ℝ) * Real.pi| ≤ |w.re - z.re| + |z.re - (n : ℝ) * Real.pi| := by
      have := abs_add_le (w.re - z.re) (z.re - (n : ℝ) * Real.pi)
      simpa using this
    linarith
  have hderiv : ∀ z ∈ Metric.closedBall c (Real.pi / 5), ‖deriv a z‖ ≤ 5 / 36 := by
    intro z hz
    have hsub := hK z hz
    have hdiff : DifferentiableOn ℂ a (Metric.closedBall z (9 / 10)) := fun y hy =>
      (haan y (hsub hy)).differentiableAt.differentiableWithinAt
    have hcl : DiffContOnCl ℂ a (Metric.ball z (9 / 10)) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball z (by norm_num)]
      exact hdiff
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 9 / 10) hcl
      (C := A) (fun y hy => haA y (hsub (Metric.sphere_subset_closedBall hy)))
    refine this.trans ?_
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have hconv : Convex ℝ (Metric.closedBall c (Real.pi / 5)) := convex_closedBall _ _
  have hmem : ∀ ξ ∈ MTwoMode.localSpectralDisc w φ n, ξ ∈ Metric.closedBall c (Real.pi / 5) :=
    fun ξ hξ => (local_spectral_disc_in_strip w hw φ hφ n hthreshold).1 hξ
  have hlip : ‖a ξ1 - a ξ2‖ ≤ 5 / 36 * ‖ξ1 - ξ2‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x hx => (haan x ((local_spectral_disc_in_strip w hw φ hφ n hthreshold).2 hx)).differentiableAt)
      hderiv hconv (hmem ξ2 h2) (hmem ξ1 h1)
  -- algebra
  set d1 := ‖ξ1 - c - a ξ1‖ with hd1'
  set d2 := ‖ξ2 - c - a ξ2‖ with hd2'
  have hg : ‖ξ1 - ξ2‖ ≤ d1 + d2 + ‖a ξ1 - a ξ2‖ := by
    have e : ξ1 - ξ2 = (ξ1 - c - a ξ1) - (ξ2 - c - a ξ2) + (a ξ1 - a ξ2) := by ring
    calc ‖ξ1 - ξ2‖ = ‖(ξ1 - c - a ξ1) - (ξ2 - c - a ξ2) + (a ξ1 - a ξ2)‖ := by rw [← e]
      _ ≤ ‖(ξ1 - c - a ξ1) - (ξ2 - c - a ξ2)‖ + ‖a ξ1 - a ξ2‖ := norm_add_le _ _
      _ ≤ d1 + d2 + ‖a ξ1 - a ξ2‖ := by
        gcongr
        exact norm_sub_le _ _
  have hd1n : 0 ≤ d1 := norm_nonneg _
  have hd2n : 0 ≤ d2 := norm_nonneg _
  have hgn : 0 ≤ ‖ξ1 - ξ2‖ := norm_nonneg _
  have hs : 31 / 36 * ‖ξ1 - ξ2‖ ≤ d1 + d2 := by linarith
  have hs2 : (31 / 36 * ‖ξ1 - ξ2‖) ^ 2 ≤ (d1 + d2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hs 2
  have hs3 : (d1 + d2) ^ 2 ≤ 4 * M := by nlinarith [sq_nonneg (d1 - d2)]
  nlinarith

/-- CONDITIONAL reduction of Pro's printed M-030 head `gap_square_schur_bound`: if the two labelled periodic
eigenvalues `lamMinus φ n`, `lamPlus φ n` are zeros of `schurDet` in the closed local disc (the label identification that
is the content of M-031, NOT proved here), the printed M-030 conclusion follows from `local_roots_gap_square_bound`.
The hypothesis `hlab` is satisfiable for the actual model (it is the M-031 localization of the labelled roots) and is
NOT a restatement of the conclusion. -/
theorem gap_square_schur_bound_of_label_roots
    (w : ℤ → ℝ) (hw : OneDerivativeWeight w) (φ : PotPair)
    (hφ : MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ)
    (hthreshold : 8 * MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
      NlsGge.Atomic.M.M054.indexWeight n)
    (hlab : ∃ (h1 : lamMinus φ n ∈ NlsGge.Atomic.KST004.spectralStrip n)
        (h2 : lamPlus φ n ∈ NlsGge.Atomic.KST004.spectralStrip n),
      lamMinus φ n ∈ MTwoMode.localSpectralDisc w φ n ∧
      lamPlus φ n ∈ MTwoMode.localSpectralDisc w φ n ∧
      MTwoMode.schurDet φ n (lamMinus φ n) h1 = 0 ∧
      MTwoMode.schurDet φ n (lamPlus φ n) h2 = 0) :
    let P : Set ℝ := {r : ℝ | ∃ z : ℂ,
      ∃ hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n,
        r = ‖MTwoMode.offDiagonal φ n z hz true *
          MTwoMode.offDiagonal φ n z hz false‖}
    P.Nonempty ∧ BddAbove P ∧
    ‖(lamPlus φ n - lamMinus φ n)‖ ^ 2 ≤ 6 * sSup P := by
  obtain ⟨h1, h2, d1, d2, z1, z2⟩ := hlab
  intro P
  obtain ⟨hne, hbdd, hle⟩ := local_roots_gap_square_bound w hw φ hφ n hthreshold
    (lamMinus φ n) (lamPlus φ n) d1 d2 h1 h2 z1 z2
  refine ⟨hne, hbdd, ?_⟩
  rw [norm_sub_rev]
  exact hle

end NlsGge.ThirdConsultation.M

end

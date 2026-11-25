import Armstrong.Work.RawBetaFixedAnalytic
import NlsGge.GK38.AbelianRatioCutBound
import NlsGge.GK38.AngleDirichletAnalytic
import NlsGge.GK38.DirichletL2
import NlsGge.GK38.TauGammaL2Realization
import NlsGge.GK38.IsolatingGeometryBounds

/-!
SPECULATIVE_NOT_ACCEPTED. Actual common fixed-circle geometry for the
own-correction Cauchy estimate. No compiler has been run by the author.

The Dirichlet tail is earned from an actual analytic Hilbert realization and
its norm continuity. Finite heads use compactness only of spectral circles.
Persistence independently earns nonzero denominators before reciprocal bounds
are converted to lower bounds. No numerator or correction bound is assumed.
-/

set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

/-- Actual Dirichlet deviations have uniformly small far coordinates on one
complex neighborhood, by norm continuity of their earned Hilbert realization. -/
theorem gk16_muSeq_uniform_tail38
    (phi0 : PotPair) (hphi0 : phi0 ∈ gkW) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ U : Set PotPair, U ∈ nhds phi0 ∧ U ⊆ gkW ∧ ∃ N : ℕ,
      ∀ phi ∈ U, ∀ n : ℤ, (N : ℤ) < |n| →
        ‖muSeq phi n - (n : ℂ)*(Real.pi : ℂ)‖ < epsilon := by
  obtain ⟨A, he, ha⟩ := local_l2_analytic_realization38 gkW
    (fun phi n => muSeq phi n - (n : ℂ)*(Real.pi : ℂ)) isOpen_gkW
    (fun n => (analyticOnNhd_muSeq_complex38 n).sub analyticOnNhd_const)
    (fun phi _ => muSeq_l2 phi)
  obtain ⟨V, hV, N, ht⟩ := l2_continuous_local_tails38 A phi0
    (ha phi0 hphi0).continuousAt epsilon hepsilon
  refine ⟨V ∩ gkW, inter_mem hV (isOpen_gkW.mem_nhds hphi0),
    inter_subset_right, N, ?_⟩
  intro phi hphi n hn
  rw [← he phi hphi.2 n]
  exact ht phi hphi.1 n hn

/-- One real-centered complex ball controls every signed fixed circle. The
standard-root and actual-Dirichlet denominators remain separated uniformly,
including potentials with collapsed own gaps or a Dirichlet point at a tip. -/
theorem gk16_fixed_real_circle_uniform_geometry38 (u : PhysicalL2) :
    ∃ delta rmax s0 d0 : ℝ,
      0 < delta ∧ 0 < rmax ∧ 0 < s0 ∧ 0 < d0 ∧
      ball (realSlice u) delta ⊆ gkW ∧
      ∀ phi ∈ ball (realSlice u) delta,
        IsolatingFamily38 phi (discC (realSlice u)) (discR (realSlice u)) ∧
        ∀ n : ℤ, discR (realSlice u) n ≤ rmax ∧
          ∀ z ∈ sphere (discC (realSlice u) n) (discR (realSlice u) n),
            s0 ≤ ‖stdRoot38 ((lamMinus phi n+lamPlus phi n)/2)
              ((lamPlus phi n-lamMinus phi n)^2) z‖ ∧
            d0 ≤ ‖z-muSeq phi n‖ := by
  classical
  let phi0 : PotPair := realSlice u
  let C : ℤ → ℂ := discC phi0
  let rho : ℤ → ℝ := discR phi0
  have hphi0 : phi0 ∈ gkW := realSlice_mem_gkW u
  have hfam0 : IsolatingFamily38 phi0 C rho := isolating_family38 phi0 hphi0
  obtain ⟨rp, hrp, c, Ng, hgeom, hpersist⟩ :=
    fixed_family_persistence38 phi0 C rho hfam0
  let V : Set PotPair := ball phi0 rp ∩ gkW
  have hV0 : phi0 ∈ V := ⟨mem_ball_self hrp, hphi0⟩
  have hVg : V ⊆ gkW := inter_subset_right
  have hVnhds : V ∈ nhds phi0 :=
    inter_mem (ball_mem_nhds phi0 hrp) (isOpen_gkW.mem_nhds hphi0)
  have hfamily : ∀ phi ∈ V, IsolatingFamily38 phi C rho :=
    fun phi hphi => ⟨c, Ng, hgeom, hpersist phi hphi.1⟩
  have hmuNonzero : ∀ phi ∈ V, ∀ n : ℤ, ∀ z ∈ sphere (C n) (rho n),
      z-muSeq phi n ≠ 0 := by
    intro phi hphi n z hz hzero
    obtain ⟨c', N', hg', hs'⟩ := hfamily phi hphi
    have hmuBall : muSeq phi n ∈ ball (C n) (rho n) := (hs'.1 n).2.1
    have hdist := mem_sphere.mp hz
    rw [sub_eq_zero.mp hzero] at hdist
    exact (ne_of_lt (mem_ball.mp hmuBall)) hdist
  obtain ⟨Uo, hUo, hUog, No, hown⟩ :=
    a5OwnCut_uniform_ball38 phi0 hphi0 (Real.pi/16) (by positivity)
  obtain ⟨Um, hUm, hUmg, Nm, hmuTail⟩ :=
    gk16_muSeq_uniform_tail38 phi0 hphi0 (Real.pi/16) (by positivity)
  let N : ℕ := max Ng (max No Nm)
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hLattice : ∀ n : ℤ, (Ng : ℤ) < |n| →
      C n = countingCenter38 n ∧ rho n = Real.pi/4 := by
    intro n hn
    exact ⟨(hgeom.2.2.2.2 n hn).1, (hgeom.2.2.2.2 n hn).2.1⟩
  obtain ⟨rmax, hrmax, hdeviation⟩ := isolating_deviation_bound38 C rho Ng hLattice
  have hradius : ∀ n : ℤ, rho n ≤ rmax := by
    intro n
    linarith [hdeviation n, norm_nonneg (C n-countingCenter38 n)]
  obtain ⟨er, her, Br, hBr, hrootHead⟩ := p2FiniteCompact_parameter_bound38 S
    (fun n phi z => (stdRoot38 (tauN phi n) (gamma2 phi n) z)⁻¹) phi0
    (fun n => sphere (C n) (rho n)) (fun _ _ => isCompact_sphere _ _)
    (fun n _ z hz =>
      ((rawBetaFixedStandardRoot_analytic38 V hVg C rho hfamily n)
        (phi0,z) ⟨hV0,hz⟩).inv
        (((rawBetaFixedBoundaryRoot38 phi0 hphi0 C rho hfam0 n).2.2 z hz).1))
  obtain ⟨em, hem, Bm, hBm, hmuHead⟩ := p2FiniteCompact_parameter_bound38 S
    (fun n phi z => (z-muSeq phi n)⁻¹) phi0
    (fun n => sphere (C n) (rho n)) (fun _ _ => isCompact_sphere _ _)
    (by
      intro n _ z hz
      have hfst : AnalyticAt ℂ (fun q : PotPair × ℂ => q.1) (phi0,z) :=
        analyticAt_fst
      have hmu : AnalyticAt ℂ (fun q : PotPair × ℂ => muSeq q.1 n) (phi0,z) :=
        AnalyticAt.comp
          (g := fun phi : PotPair => muSeq phi n)
          (f := fun q : PotPair × ℂ => q.1) (x := (phi0,z))
          (analyticOnNhd_muSeq_complex38 n phi0 hphi0) hfst
      exact (analyticAt_snd.sub hmu).inv (hmuNonzero phi0 hV0 n z hz))
  have hlowerOfInverse : ∀ (w : ℂ) (B : ℝ), w ≠ 0 → 0 ≤ B →
      ‖w⁻¹‖ ≤ B → 1/(B+1) ≤ ‖w‖ := by
    intro w B hw hB hbound
    have hn : ‖w‖ ≠ 0 := (norm_pos_iff.mpr hw).ne'
    have hmul := mul_le_mul_of_nonneg_right hbound (norm_nonneg w)
    rw [norm_inv, inv_mul_cancel₀ hn] at hmul
    apply (div_le_iff₀ (by linarith : 0 < B+1)).mpr
    nlinarith [norm_nonneg w]
  let dfar : ℝ := 3*Real.pi/16
  have hdfar : 0 < dfar := by dsimp [dfar]; positivity
  have hsHead : 0 < (1 : ℝ)/(Br+1) := by positivity
  have hdHead : 0 < (1 : ℝ)/(Bm+1) := by positivity
  have hCommon : V ∩ (Uo ∩ (Um ∩ (ball phi0 er ∩ ball phi0 em))) ∈ nhds phi0 :=
    inter_mem hVnhds (inter_mem hUo (inter_mem hUm
      (inter_mem (ball_mem_nhds phi0 her) (ball_mem_nhds phi0 hem))))
  obtain ⟨delta, hdelta, hsub⟩ := Metric.mem_nhds_iff.mp hCommon
  refine ⟨delta, rmax, min (1/(Br+1)) dfar, min (1/(Bm+1)) dfar,
    hdelta, hrmax, lt_min hsHead hdfar, lt_min hdHead hdfar, ?_, ?_⟩
  · intro phi hphi
    exact hVg (hsub hphi).1
  · intro phi hphi
    have hv : phi ∈ V := (hsub hphi).1
    have ho : phi ∈ Uo := (hsub hphi).2.1
    have hm : phi ∈ Um := (hsub hphi).2.2.1
    have hr : phi ∈ ball phi0 er := (hsub hphi).2.2.2.1
    have hd : phi ∈ ball phi0 em := (hsub hphi).2.2.2.2
    have hphiGK : phi ∈ gkW := hVg hv
    have hfam : IsolatingFamily38 phi C rho := hfamily phi hv
    refine ⟨hfam, fun n => ⟨hradius n, ?_⟩⟩
    intro z hz
    have hzLocal : z ∈ sphere (C n) (rho n) := hz
    have htau : tauN phi n = (lamMinus phi n+lamPlus phi n)/2 := by
      rw [tauN_value38 phi hphiGK n]
      ring
    rw [← htau, ← gamma2_value38 phi hphiGK n]
    by_cases hn : (N : ℤ) < |n|
    · have hng : (Ng : ℤ) < |n| := by
        have h := le_max_left Ng (max No Nm)
        dsimp only [N] at hn
        omega
      have hno : (No : ℤ) < |n| := by
        have h := (le_max_left No Nm).trans (le_max_right Ng (max No Nm))
        dsimp only [N] at hn
        omega
      have hnm : (Nm : ℤ) < |n| := by
        have h := (le_max_right No Nm).trans (le_max_right Ng (max No Nm))
        dsimp only [N] at hn
        omega
      obtain ⟨hC, hrho⟩ := hLattice n hng
      have hzdist : ‖z-(n : ℂ)*(Real.pi : ℂ)‖ = Real.pi/4 := by
        have hdist : dist z (C n) = rho n := mem_sphere.mp hzLocal
        rw [hC,hrho] at hdist
        simpa only [dist_eq_norm,countingCenter38] using hdist
      have hseparate : ∀ x : ℂ, ‖x-(n : ℂ)*(Real.pi : ℂ)‖ < Real.pi/16 →
          dfar ≤ ‖z-x‖ := by
        intro x hx
        have htriangle : ‖z-(n : ℂ)*(Real.pi : ℂ)‖ ≤
            ‖z-x‖+‖x-(n : ℂ)*(Real.pi : ℂ)‖ := by
          calc
            _ = ‖(z-x)+(x-(n : ℂ)*(Real.pi : ℂ))‖ := by congr 1; ring
            _ ≤ _ := norm_add_le _ _
        rw [hzdist] at htriangle
        dsimp only [dfar]
        linarith
      have haSmall : ‖lamMinus phi n-(n : ℂ)*(Real.pi : ℂ)‖ < Real.pi/16 :=
        mem_ball_iff_norm.mp (hown phi ho n hno (left_mem_segment ℝ _ _))
      have hbSmall : ‖lamPlus phi n-(n : ℂ)*(Real.pi : ℂ)‖ < Real.pi/16 :=
        mem_ball_iff_norm.mp (hown phi ho n hno (right_mem_segment ℝ _ _))
      have haSep : dfar ≤ ‖lamMinus phi n-z‖ := by
        rw [norm_sub_rev]
        exact hseparate _ haSmall
      have hbSep : dfar ≤ ‖lamPlus phi n-z‖ := by
        rw [norm_sub_rev]
        exact hseparate _ hbSmall
      have hp : (phi,z) ∈ rootDomain38 :=
        ⟨hphiGK, fixed_sphere_subset phi C rho hfam n hzLocal⟩
      have hoff : z ∉ segment ℝ (lamMinus phi n) (lamPlus phi n) :=
        rootDomain_avoids38 (p := (phi,z)) hp n
      have hsquare := stdRoot_sq38 (lamMinus phi n) (lamPlus phi n) z hoff
      rw [← htau, ← gamma2_value38 phi hphiGK n] at hsquare
      have hnormSquare : ‖stdRoot38 (tauN phi n) (gamma2 phi n) z‖^2 =
          ‖lamMinus phi n-z‖*‖lamPlus phi n-z‖ := by
        simpa only [norm_pow,norm_mul] using congrArg norm hsquare
      have hprod : dfar^2 ≤ ‖lamMinus phi n-z‖*‖lamPlus phi n-z‖ := by
        calc
          _ = dfar*dfar := by ring
          _ ≤ _ := mul_le_mul haSep hbSep hdfar.le (norm_nonneg _)
      have hrootFar : dfar ≤ ‖stdRoot38 (tauN phi n) (gamma2 phi n) z‖ := by
        nlinarith [norm_nonneg (stdRoot38 (tauN phi n) (gamma2 phi n) z)]
      exact ⟨(min_le_right _ _).trans hrootFar,
        (min_le_right _ _).trans (hseparate _ (hmuTail phi hm n hnm))⟩
    · have hnS : n ∈ S := by
        simpa only [S,Finset.mem_Icc] using abs_le.mp (not_lt.mp hn)
      have hrootNonzero : stdRoot38 (tauN phi n) (gamma2 phi n) z ≠ 0 :=
        ((rawBetaFixedBoundaryRoot38 phi hphiGK C rho hfam n).2.2 z hzLocal).1
      have hs := hlowerOfInverse _ Br hrootNonzero hBr (hrootHead phi hr n hnS z hzLocal)
      have hdm := hlowerOfInverse _ Bm (hmuNonzero phi hv n z hzLocal) hBm
        (hmuHead phi hd n hnS z hzLocal)
      exact ⟨(min_le_left _ _).trans hs, (min_le_left _ _).trans hdm⟩

end
end NlsGge.GK38

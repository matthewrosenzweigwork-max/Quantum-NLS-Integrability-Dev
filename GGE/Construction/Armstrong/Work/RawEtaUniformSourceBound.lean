import Armstrong.Work.RawBetaMagnitudeRegularFactor
import Armstrong.Work.RawBetaMagnitudeSameFamily
import Mathlib.Topology.Order.OrderClosed

/-!
# Common closed-disc bound for the actual own quotient

The actual compact real full-gap cube supplies a finite input cover and one
common bound for the literal omitted quotient. The bound extends from each
open fixed disc to its closure using the quotient's earned closed-disc
continuity. A common input tube then produces analytic completions of the
SAME supplied W/F with that bound, numerator identity and normalized periods.

SPECULATIVE: no compiler or integration has been run by the author. This is
one quantitative producer, not a correction-exponent or Cartesian theorem.
-/
set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem gk16_own_ratio_compact_closed_discs38
    (u : PhysicalL2) (C : ℤ → ℂ) (rho : ℤ → ℝ)
    (hfamily : IsolatingFamily38 (realSlice u) C rho) :
    ∃ U : Set PotPair, ∃ V : Set Lib.L2Seq, ∃ H : ℝ,
      IsOpen U ∧ IsOpen V ∧ realSlice u ∈ U ∧ U ⊆ gkW ∧
      p6RealInclude38 '' p5FullRealGapCube38 u ⊆ V ∧ 0 ≤ H ∧
      ∀ phi ∈ U, IsolatingFamily38 phi C rho ∧
        ∀ s ∈ V, ∀ m : ℤ, ∀ z ∈ closedBall (C m) (rho m),
          ‖p2OmittedRatio38 m ((phi,s),z)‖ ≤ H := by
  classical
  have huGK : realSlice u ∈ gkW := realSlice_mem_gkW u
  let K : Set Lib.L2Seq := p6RealInclude38 '' p5FullRealGapCube38 u
  have hK : IsCompact K :=
    (p5FullRealGapCube_isCompact38 u).image p6RealInclude38.continuous
  choose U hU _hUW V hV B hB hspec using
    (fun s0 : Lib.L2Seq => gk151_omitted_ratio_original_discs_bound38
      (realSlice u) huGK C rho hfamily s0)
  obtain ⟨T, _hTK, hcover⟩ := hK.elim_nhds_subcover
    (fun s0 => interior (V s0))
    (fun s0 _ => isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr (hV s0)))
  let P : Set PotPair := {phi | ∀ s0 ∈ T, phi ∈ U s0}
  have hP : P ∈ nhds (realSlice u) := T.eventually_all.mpr (fun s0 _ => hU s0)
  obtain ⟨r, hr, c, N, hgeom, hpersist⟩ :=
    fixed_family_persistence38 (realSlice u) C rho hfamily
  let U0 : Set PotPair := gkW ∩ (ball (realSlice u) r ∩ interior P)
  let V0 : Set Lib.L2Seq := ⋃ s0 ∈ T, interior (V s0)
  have hsum : 0 ≤ ∑ s0 ∈ T, B s0 := Finset.sum_nonneg (fun s0 _ => hB s0)
  refine ⟨U0, V0, ∑ s0 ∈ T, B s0,
    isOpen_gkW.inter (isOpen_ball.inter isOpen_interior),
    isOpen_biUnion (fun s0 _ => isOpen_interior),
    ⟨huGK, mem_ball_self hr, mem_interior_iff_mem_nhds.mpr hP⟩,
    fun phi hphi => hphi.1, hcover, hsum, ?_⟩
  intro phi hphi
  have hfam : IsolatingFamily38 phi C rho :=
    ⟨c, N, hgeom, hpersist phi hphi.2.1⟩
  refine ⟨hfam, ?_⟩
  intro s hs m z hz
  obtain ⟨s0, hs0T, hs0V⟩ := mem_iUnion₂.mp hs
  have hphiU : phi ∈ U s0 := (interior_subset hphi.2.2) s0 hs0T
  have hopen : ∀ w ∈ ball (C m) (rho m),
      ‖p2OmittedRatio38 m ((phi,s),w)‖ ≤ ∑ t ∈ T, B t := by
    intro w hw
    exact ((hspec s0 phi hphiU).2 s (interior_subset hs0V) m w hw).trans
      (Finset.single_le_sum (fun t _ => hB t) hs0T)
  have hclosure : closure (ball (C m) (rho m)) = closedBall (C m) (rho m) :=
    closure_ball (C m) (isolating_radius_pos38 hfam m).ne'
  have hcont : ContinuousOn (fun w : ℂ => ‖p2OmittedRatio38 m ((phi,s),w)‖)
      (closure (ball (C m) (rho m))) := by
    rw [hclosure]
    exact (p2OmittedRatio_own_disc_analytic38 m phi hphi.1 C rho hfam s).continuousOn.norm
  have hzClosure : z ∈ closure (ball (C m) (rho m)) := by
    rw [hclosure]
    exact hz
  exact le_on_closure hopen hcont continuousOn_const hzClosure

theorem gk16_same_family_own_ratio_closed_bound38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      p2Fn38 n (phi, F n phi) = 0)
    (hFinv : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (phi,y))
        (F n phi)).IsInvertible)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2 * (Real.pi : ℂ) else 0)
    (hFreal : ∀ (n : ℤ) (u : PhysicalL2), ∃ t : P3RealSpace38 n,
      t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t = 0 ∧
        F n (realSlice u) = p3RealInclude38 n t)
    (u : PhysicalL2) :
    ∃ delta H : ℝ, 0 < delta ∧ 0 ≤ H ∧ ball (realSlice u) delta ⊆ W ∧
      (∀ phi ∈ ball (realSlice u) delta,
        IsolatingFamily38 phi (discC (realSlice u)) (discR (realSlice u))) ∧
      ∀ n : ℤ, ∃ S : PotPair → Lib.L2Seq,
        AnalyticOnNhd ℂ S (ball (realSlice u) delta) ∧
        ∀ phi ∈ ball (realSlice u) delta,
          F n phi = p2Restrict38 n (S phi) ∧
          p6PsiNumerator38 n (F n) phi = p2FullNumerator38 n (S phi) ∧
          (∀ m : ℤ, abelianPeriod38 m phi (p2FullNumerator38 n (S phi)) =
            if m = n then 2 * (Real.pi : ℂ) else 0) ∧
          ∀ z ∈ closedBall (discC (realSlice u) n) (discR (realSlice u) n),
            ‖p2OmittedRatio38 n ((phi,S phi),z)‖ ≤ H := by
  have huGK : realSlice u ∈ gkW := hWgk (hreal (mem_range_self u))
  let C : ℤ → ℂ := discC (realSlice u)
  let rho : ℤ → ℝ := discR (realSlice u)
  have hfam0 : IsolatingFamily38 (realSlice u) C rho :=
    isolating_family38 (realSlice u) huGK
  obtain ⟨U, V, H, hUopen, hVopen, huU, _hUg, hKV, hH, hbound⟩ :=
    gk16_own_ratio_compact_closed_discs38 u C rho hfam0
  obtain ⟨a, ha, haW, hbranches⟩ :=
    gk151_same_family_common_input_tube38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal u V hVopen hKV
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds huU)
  let delta : ℝ := min a r
  have hdelta : 0 < delta := lt_min ha hr
  have hsuba : ball (realSlice u) delta ⊆ ball (realSlice u) a :=
    ball_subset_ball (min_le_left _ _)
  have hsubU : ball (realSlice u) delta ⊆ U :=
    (ball_subset_ball (min_le_right _ _)).trans hrU
  refine ⟨delta, H, hdelta, hH, hsuba.trans haW,
    fun phi hphi => (hbound phi (hsubU hphi)).1, ?_⟩
  intro n
  obtain ⟨t, _ht, _htzero, S, _hSbase, hSan, hSspec⟩ := hbranches n
  refine ⟨S, hSan.mono hsuba, ?_⟩
  intro phi hphi
  obtain ⟨hSV, hrestrict, _hSn, _hcoords, hnum, _hroots, hperiods⟩ :=
    hSspec phi (hsuba hphi)
  refine ⟨hrestrict, hnum, hperiods, ?_⟩
  exact (hbound phi (hsubU hphi)).2 (S phi) hSV n

end
end NlsGge.GK38

import Mathlib
import NlsGge.Atomic.G6.G6039Sup1Core
import NlsGge.Atomic.G6.G6039Sup2Core
import NlsGge.Atomic.G6.G6037Core
import NlsGge.Atomic.G4.G4004
import NlsGge.Atomic.G4.G4011

/- G6039 SUP3 CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6039Sup3Core.lean, namespace NlsGge.ThirdConsultation.G6039S.  SUPPORT (no packet
   increment): descent_analytic = the first conjunct of Pro's parametric_even_tail_descent (round 14,
   followup13 STATEMENTS/G6.md:1312-1330).  Route (Pro: "finite-dimensional tail descent with the head P as
   parameters ... pass to the limit along finite tail truncations. Local boundedness and one-complex-variable Vitali
   on each affine line give the holomorphic limit ...; then use the Banach analytic criterion"):
   * landed G4-004 on U ×ˢ ball(0, r²): bounded by M since ‖root I‖² = ‖I‖; weak analyticity reduces to the line
     φ ζ = f (p + ζh, root (I + ζJ)) being analytic at 0;
   * truncations φ_N ζ = f (p + ζh, root (trunc_N (I + ζJ))): for ANY base c, φ_N = f (p+ζh, Σ_{win N} e_n br(c_n, ·))
     (finite sign flips, f_of_sq_fin); recentring at each point gives differentiability off a finite set and
     continuity, so φ_N is analytic on a disc W (Mathlib removable singularity);
   * φ_N → φ uniformly on W: lipschitz_of_bdd (Schwarz) and ‖root(trunc K) - root K‖² ≤ window tail of
     ‖I_n‖ + δ‖J_n‖;
   * landed G4-011 (locally uniform analytic limit).
   Mathlib names verified in this repo's pinned tree (.lake/packages/mathlib @ d13f23b7). -/
set_option autoImplicit false

open Set Filter Topology Metric
open scoped ENNReal
open NlsGge.GK38 NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.G6039S
noncomputable section

/-! ### Branches and finite vectors -/

def br (c z : ℂ) : ℂ := if c = 0 then Complex.sqrt z else Complex.sqrt c * Complex.sqrt (z / c)

theorem br_sq (c z : ℂ) : br c z ^ 2 = z := by
  unfold br
  split_ifs with hc
  · exact NlsGge.GK38.Lib.sqrt_sq z
  · rw [mul_pow, NlsGge.GK38.Lib.sqrt_sq, NlsGge.GK38.Lib.sqrt_sq]; field_simp

theorem single_eq_smul (n : ℤ) (b : ℂ) :
    (lp.single 2 n b : ComplexDiagonalSpace) = b • (lp.single 2 n (1 : ℂ) : ComplexDiagonalSpace) := by
  rw [← lp.single_smul, smul_eq_mul, mul_one]

theorem norm_eq_of_sq_eq {a b : ℂ} (h : a ^ 2 = b ^ 2) : ‖a‖ = ‖b‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_pow, ← norm_pow, h]

theorem f_of_sq_fin (g : ComplexDiagonalSpace → ℂ) (r : ℝ)
    (hev : CoordinatewiseEvenOn g Set.univ (ball (0 : ComplexDiagonalSpace) r))
    {x y : ComplexDiagonalSpace} (hx : x ∈ ball (0 : ComplexDiagonalSpace) r) (T : Finset ℤ)
    (hT : ∀ n, n ∉ T → y n = x n) (hsq : ∀ n, y n ^ 2 = x n ^ 2) : g y = g x := by
  classical
  have hy : y = flipD (T.filter (fun n => y n ≠ x n)) x := by
    apply lp.ext; funext m
    rw [flipD_apply]
    by_cases hmT : m ∈ T
    · by_cases hne : y m = x m
      · rw [if_neg (by simp [hne])]; exact hne
      · rw [if_pos (by simp [hmT, hne])]
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hsq m) with h | h
        · exact absurd h hne
        · exact h
    · rw [if_neg (by simp [hmT])]; exact hT m hmT
  rw [hy]; exact f_flipD g r hev _ x hx

theorem mem_ball_of_sq_eq {r : ℝ} {x y : ComplexDiagonalSpace} (hx : x ∈ ball (0 : ComplexDiagonalSpace) r)
    (hsq : ∀ n, y n ^ 2 = x n ^ 2) : y ∈ ball (0 : ComplexDiagonalSpace) r := by
  rw [mem_ball, dist_zero_right] at hx ⊢
  rwa [norm_sq_eq_of_norm_coord y x (fun n => norm_eq_of_sq_eq (hsq n))]

theorem root_trunc_apply (N : ℕ) (K : ComplexActionSpace) (n : ℤ) :
    complexActionRoot (truncateComplexActions N K) n = if n ∈ Lib.win N then Complex.sqrt (K n) else 0 := by
  rw [NlsGge.ThirdConsultation.G6038S.root_apply, NlsGge.ThirdConsultation.G6038S.trunc_apply]
  split_ifs <;> simp

theorem norm_root_lt {ρ : ℝ} (hρ : 0 < ρ) (K : ComplexActionSpace) (hK : ‖K‖ < ρ ^ 2) :
    ‖complexActionRoot K‖ < ρ :=
  lt_of_pow_lt_pow_left₀ 2 hρ.le (by rw [NlsGge.ThirdConsultation.G6038S.norm_root_sq]; exact hK)

theorem norm_root_trunc_lt {ρ : ℝ} (hρ : 0 < ρ) (N : ℕ) (K : ComplexActionSpace) (hK : ‖K‖ < ρ ^ 2) :
    ‖complexActionRoot (truncateComplexActions N K)‖ < ρ :=
  norm_root_lt hρ _ (lt_of_le_of_lt (NlsGge.ThirdConsultation.G6038S.norm_trunc_le N K) hK)

/-- The base-`c` finite representative of `root (trunc_N K)`. -/
def finRep (N : ℕ) (c K : ComplexActionSpace) : ComplexDiagonalSpace :=
  ∑ n ∈ Lib.win N, br (c n) (K n) • (lp.single 2 n (1 : ℂ) : ComplexDiagonalSpace)

theorem finRep_eq (N : ℕ) (c K : ComplexActionSpace) :
    finRep N c K = ∑ n ∈ Lib.win N, lp.single 2 n (br (c n) (K n)) :=
  Finset.sum_congr rfl fun n _ => (single_eq_smul n _).symm

theorem finRep_sq (N : ℕ) (c K : ComplexActionSpace) (n : ℤ) :
    (finRep N c K n) ^ 2 = (complexActionRoot (truncateComplexActions N K) n) ^ 2 := by
  rw [finRep_eq, coe_finsum_single, root_trunc_apply]
  split_ifs
  · rw [br_sq, NlsGge.GK38.Lib.sqrt_sq]
  · rfl

theorem rep_eq (g : ComplexDiagonalSpace → ℂ) (r : ℝ) (hr : 0 < r)
    (hev : CoordinatewiseEvenOn g Set.univ (ball (0 : ComplexDiagonalSpace) r))
    (N : ℕ) (c K : ComplexActionSpace) (hK : ‖K‖ < r ^ 2) :
    g (complexActionRoot (truncateComplexActions N K)) = g (finRep N c K) := by
  have hx : complexActionRoot (truncateComplexActions N K) ∈ ball (0 : ComplexDiagonalSpace) r := by
    rw [mem_ball, dist_zero_right]; exact norm_root_trunc_lt hr N K hK
  refine (f_of_sq_fin g r hev hx (Lib.win N) (fun n hn => ?_) (finRep_sq N c K)).symm
  rw [finRep_eq, coe_finsum_single, root_trunc_apply, if_neg hn, if_neg hn]

theorem finRep_mem (r : ℝ) (hr : 0 < r) (N : ℕ) (c K : ComplexActionSpace) (hK : ‖K‖ < r ^ 2) :
    finRep N c K ∈ ball (0 : ComplexDiagonalSpace) r := by
  have hx : complexActionRoot (truncateComplexActions N K) ∈ ball (0 : ComplexDiagonalSpace) r := by
    rw [mem_ball, dist_zero_right]; exact norm_root_trunc_lt hr N K hK
  exact mem_ball_of_sq_eq hx (finRep_sq N c K)

/-! ### Lines -/

section Line
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

theorem Kline_apply (I J : ComplexActionSpace) (ζ : ℂ) (n : ℤ) : (I + ζ • J) n = I n + ζ * J n := by
  rw [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem finRep_differentiableAt (N : ℕ) (I J : ComplexActionSpace) (ζ₀ : ℂ)
    (hgood : ∀ n ∈ Lib.win N, (I + ζ₀ • J) n = 0 → J n = 0) :
    DifferentiableAt ℂ (fun ζ : ℂ => finRep N (I + ζ₀ • J) (I + ζ • J)) ζ₀ := by
  unfold finRep
  refine DifferentiableAt.fun_sum (fun n hn => ?_)
  refine DifferentiableAt.smul_const ?_ _
  simp only [Kline_apply, br]
  by_cases hc : I n + ζ₀ * J n = 0
  · simp only [hc, if_true]
    have hJ : J n = 0 := hgood n hn (by rw [Kline_apply]; exact hc)
    simp only [hJ, mul_zero, add_zero]
    exact differentiableAt_const _
  · simp only [hc, if_false]
    refine (differentiableAt_const _).mul ?_
    have hq : DifferentiableAt ℂ (fun ζ : ℂ => (I n + ζ * J n) / (I n + ζ₀ * J n)) ζ₀ :=
      ((differentiableAt_const _).add (differentiableAt_id.mul (differentiableAt_const _))).div_const _
    have h1 : (I n + ζ₀ * J n) / (I n + ζ₀ * J n) ∈ Complex.slitPlane := by
      rw [div_self hc]; exact Complex.one_mem_slitPlane
    exact (Complex.differentiableAt_sqrt h1).comp ζ₀ hq

theorem finRep_continuousAt (N : ℕ) (I J : ComplexActionSpace) (ζ₁ : ℂ) :
    ContinuousAt (fun ζ : ℂ => finRep N (I + ζ₁ • J) (I + ζ • J)) ζ₁ := by
  have hterm : ∀ n ∈ Lib.win N, ContinuousAt (fun ζ : ℂ => br ((I + ζ₁ • J) n) ((I + ζ • J) n) •
      (lp.single 2 n (1 : ℂ) : ComplexDiagonalSpace)) ζ₁ := by
    intro n _
    have hb : ContinuousAt (fun ζ : ℂ => br ((I + ζ₁ • J) n) ((I + ζ • J) n)) ζ₁ := by
      simp only [Kline_apply, br]
      have hlin : Continuous (fun ζ : ℂ => I n + ζ * J n) := by continuity
      by_cases hc : I n + ζ₁ * J n = 0
      · simp only [hc, if_true]
        exact NlsGge.ThirdConsultation.G6037S.continuousAt_sqrt_zero.comp_of_eq hlin.continuousAt hc
      · simp only [hc, if_false]
        refine continuousAt_const.mul ?_
        have h1 : (I n + ζ₁ * J n) / (I n + ζ₁ * J n) ∈ Complex.slitPlane := by
          rw [div_self hc]; exact Complex.one_mem_slitPlane
        exact ContinuousAt.comp (f := fun ζ : ℂ => (I n + ζ * J n) / (I n + ζ₁ * J n)) (x := ζ₁)
          (Complex.differentiableAt_sqrt h1).continuousAt ((hlin.div_const _).continuousAt)
    exact hb.smul (continuousAt_const (y := (lp.single 2 n (1 : ℂ) : ComplexDiagonalSpace)))
  unfold finRep
  exact tendsto_finsetSum _ hterm

theorem eventually_ne_at (ζ₁ c : ℂ) : ∀ᶠ ζ in 𝓝[≠] ζ₁, ζ ≠ c := by
  by_cases hc : c = ζ₁
  · subst hc; exact eventually_nhdsWithin_of_forall (fun ζ hζ => hζ)
  · exact nhdsWithin_le_nhds (eventually_ne_nhds (Ne.symm hc))

/-- The truncated descents are analytic on any open disc on which the line stays in the good region. -/
theorem trunc_line_analytic (U : Set P) (f : P × ComplexDiagonalSpace → ℂ) (r : ℝ) (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (U ×ˢ Metric.ball (0 : ComplexDiagonalSpace) r))
    (heven : ∀ p : P, p ∈ U →
      CoordinatewiseEvenOn (fun x : ComplexDiagonalSpace => f (p, x))
        Set.univ (Metric.ball (0 : ComplexDiagonalSpace) r))
    (p h : P) (I J : ComplexActionSpace) (W : Set ℂ) (hW : IsOpen W)
    (hWU : ∀ ζ ∈ W, p + ζ • h ∈ U ∧ ‖I + ζ • J‖ < r ^ 2) (N : ℕ) :
    AnalyticOnNhd ℂ (fun ζ : ℂ => f (p + ζ • h, complexActionRoot (truncateComplexActions N (I + ζ • J)))) W := by
  intro ζ₁ hζ₁
  have hrep : ∀ c : ComplexActionSpace, ∀ ζ ∈ W,
      f (p + ζ • h, complexActionRoot (truncateComplexActions N (I + ζ • J))) =
        f (p + ζ • h, finRep N c (I + ζ • J)) := fun c ζ hζ =>
    rep_eq (fun x => f (p + ζ • h, x)) r hr (heven _ (hWU ζ hζ).1) N c _ (hWU ζ hζ).2
  have hloc : ∀ c : ComplexActionSpace, ∀ ζ₀ ∈ W,
      (fun ζ : ℂ => f (p + ζ • h, complexActionRoot (truncateComplexActions N (I + ζ • J)))) =ᶠ[𝓝 ζ₀]
        fun ζ => f (p + ζ • h, finRep N c (I + ζ • J)) := fun c ζ₀ hζ₀ =>
    Filter.eventually_of_mem (hW.mem_nhds hζ₀) fun ζ hζ => hrep c ζ hζ
  have hfat : ∀ ζ₀ ∈ W, AnalyticAt ℂ f (p + ζ₀ • h, finRep N (I + ζ₀ • J) (I + ζ₀ • J)) := fun ζ₀ hζ₀ =>
    hf _ ⟨(hWU ζ₀ hζ₀).1, finRep_mem r hr N _ _ (hWU ζ₀ hζ₀).2⟩
  have hq : ∀ ζ₀ : ℂ, DifferentiableAt ℂ (fun ζ : ℂ => p + ζ • h) ζ₀ := fun ζ₀ =>
    (differentiableAt_id.smul_const h).const_add p
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · have hE1 : ∀ᶠ ζ in 𝓝[≠] ζ₁, ζ ∈ W := nhdsWithin_le_nhds (hW.mem_nhds hζ₁)
    have hE2 : ∀ᶠ ζ in 𝓝[≠] ζ₁, ∀ n ∈ Lib.win N, J n ≠ 0 → ζ ≠ -I n / J n :=
      (eventually_all_finset _).2 fun n _ => (eventually_ne_at ζ₁ (-I n / J n)).mono fun ζ hζ _ => hζ
    filter_upwards [hE1, hE2] with ζ₀ hζ₀W hζ₀Z
    have hgood : ∀ n ∈ Lib.win N, (I + ζ₀ • J) n = 0 → J n = 0 := by
      intro n hn hz
      by_contra hJ
      apply hζ₀Z n hn hJ
      rw [eq_div_iff hJ]
      rw [Kline_apply] at hz
      linear_combination hz
    have hcomp : DifferentiableAt ℂ (fun ζ : ℂ => f (p + ζ • h, finRep N (I + ζ₀ • J) (I + ζ • J))) ζ₀ :=
      (hfat ζ₀ hζ₀W).differentiableAt.comp ζ₀ ((hq ζ₀).prodMk (finRep_differentiableAt N I J ζ₀ hgood))
    exact hcomp.congr_of_eventuallyEq (hloc _ ζ₀ hζ₀W)
  · have hc : ContinuousAt (fun ζ : ℂ => f (p + ζ • h, finRep N (I + ζ₁ • J) (I + ζ • J))) ζ₁ :=
      (hfat ζ₁ hζ₁).continuousAt.comp (f := fun ζ : ℂ => (p + ζ • h, finRep N (I + ζ₁ • J) (I + ζ • J)))
        ((hq ζ₁).continuousAt.prodMk (finRep_continuousAt N I J ζ₁))
    exact hc.congr (hloc _ ζ₁ hζ₁).symm

/-- Root difference of a truncation, bounded by the window tail of a dominating summable sequence. -/
theorem root_trunc_sub_sq_le (N : ℕ) (K : ComplexActionSpace) (a : ℤ → ℝ)
    (ha : Summable a) (hKa : ∀ n, ‖K n‖ ≤ a n) :
    ‖complexActionRoot (truncateComplexActions N K) - complexActionRoot K‖ ^ 2 ≤
      (∑' n, a n) - ∑ n ∈ Lib.win N, a n := by
  classical
  set R := complexActionRoot (truncateComplexActions N K) - complexActionRoot K with hR
  have hRs := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) R
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hRs
  have hfin : HasSum (fun n => if n ∈ Lib.win N then a n else 0) (∑ n ∈ Lib.win N, a n) := by
    have h : HasSum (fun n => if n ∈ Lib.win N then a n else 0)
        (∑ n ∈ Lib.win N, (if n ∈ Lib.win N then a n else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun n hn => by simp [hn])
    rwa [Finset.sum_congr rfl (fun n hn => if_pos hn)] at h
  have hT := ha.hasSum.sub hfin
  refine hasSum_le (fun n => ?_) hRs hT
  have hRn : R n = (if n ∈ Lib.win N then Complex.sqrt (K n) else 0) - complexActionRoot K n := by
    rw [hR, lp.coeFn_sub, Pi.sub_apply, root_trunc_apply]
  rw [hRn, NlsGge.ThirdConsultation.G6038S.root_apply]
  split_ifs
  · simp
  · rw [zero_sub, norm_neg, NlsGge.ThirdConsultation.G6037S.norm_sqrt_sq, sub_zero]; exact hKa n

end Line

/-! ### The analyticity conjunct -/

theorem slice_differentiableOn {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    (U : Set P) (f : P × ComplexDiagonalSpace → ℂ) (r : ℝ)
    (hf : AnalyticOnNhd ℂ f (U ×ˢ Metric.ball (0 : ComplexDiagonalSpace) r)) (q : P) (hq : q ∈ U) :
    DifferentiableOn ℂ (fun x : ComplexDiagonalSpace => f (q, x)) (ball (0 : ComplexDiagonalSpace) r) := by
  intro x hx
  have h1 : DifferentiableAt ℂ f (q, x) := (hf (q, x) ⟨hq, hx⟩).differentiableAt
  have h2 : DifferentiableAt ℂ (fun y : ComplexDiagonalSpace => (q, y)) x :=
    (differentiableAt_const q).prodMk differentiableAt_id
  exact (h1.comp x h2).differentiableWithinAt

theorem tail_tendsto (a : ℤ → ℝ) (ha : Summable a) :
    Tendsto (fun N : ℕ => (∑' n, a n) - ∑ n ∈ Lib.win N, a n) atTop (𝓝 0) := by
  have hw : Tendsto (fun N : ℕ => Lib.win N) atTop atTop :=
    tendsto_atTop_finset_of_monotone (fun a b h => Lib.win_mono h)
      (fun n => ⟨n.natAbs, Lib.mem_win_of_natAbs_le le_rfl⟩)
  have h1 := ha.hasSum.comp hw
  simpa using (tendsto_const_nhds (x := ∑' n, a n)).sub h1

theorem small_mul_lt {L ε : ℝ} (hL0 : 0 ≤ L) (hε : 0 < ε) : L * (ε / (L + 1)) < ε := by
  calc L * (ε / (L + 1)) = ε * (L / (L + 1)) := by ring
    _ < ε * 1 := mul_lt_mul_of_pos_left ((div_lt_one (by linarith)).2 (by linarith)) hε
    _ = ε := mul_one ε

theorem line_analytic
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    (U : Set P) (hU : IsOpen U)
    (f : P × ComplexDiagonalSpace → ℂ) (r : ℝ) (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (U ×ˢ Metric.ball (0 : ComplexDiagonalSpace) r))
    (heven : ∀ p : P, p ∈ U →
      CoordinatewiseEvenOn (fun x : ComplexDiagonalSpace => f (p, x))
        Set.univ (Metric.ball (0 : ComplexDiagonalSpace) r))
    (M : ℝ) (hM : ∀ (p : P) (x : ComplexDiagonalSpace),
      p ∈ U → x ∈ Metric.ball (0 : ComplexDiagonalSpace) r → ‖f (p, x)‖ ≤ M)
    (p h : P) (I J : ComplexActionSpace) (hp : p ∈ U) (hI : ‖I‖ < r ^ 2) :
    AnalyticAt ℂ (fun ζ : ℂ => f (p + ζ • h, complexActionRoot (I + ζ • J))) 0 := by
  -- radii
  set s : ℝ := (‖I‖ + r ^ 2) / 2 with hs
  have hs0 : 0 < s := by have := norm_nonneg I; rw [hs]; positivity
  have hIs : ‖I‖ < s := by rw [hs]; linarith
  have hsr : s < r ^ 2 := by rw [hs]; linarith
  set ρ : ℝ := Real.sqrt s with hρdef
  have hρ : 0 < ρ := Real.sqrt_pos.2 hs0
  have hρ2 : ρ ^ 2 = s := Real.sq_sqrt hs0.le
  have hρr : ρ < r := (Real.sqrt_lt' hr).2 hsr
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p 0 hp (mem_ball_self hr))
  -- the disc
  have hc1 : Continuous (fun ζ : ℂ => p + ζ • h) := continuous_const.add (continuous_id.smul continuous_const)
  have hc2 : Continuous (fun ζ : ℂ => I + ζ • J) := continuous_const.add (continuous_id.smul continuous_const)
  have hO : IsOpen {ζ : ℂ | p + ζ • h ∈ U ∧ ‖I + ζ • J‖ < s} :=
    (hU.preimage hc1).inter (isOpen_lt hc2.norm continuous_const)
  have h0O : (0 : ℂ) ∈ {ζ : ℂ | p + ζ • h ∈ U ∧ ‖I + ζ • J‖ < s} := by
    show p + (0 : ℂ) • h ∈ U ∧ ‖I + (0 : ℂ) • J‖ < s
    rw [zero_smul, add_zero, zero_smul, add_zero]; exact ⟨hp, hIs⟩
  obtain ⟨δ, hδ, hδO⟩ := Metric.isOpen_iff.1 hO 0 h0O
  have hWU : ∀ ζ ∈ ball (0 : ℂ) δ, p + ζ • h ∈ U ∧ ‖I + ζ • J‖ < s := fun ζ hζ => hδO hζ
  have hWr : ∀ ζ ∈ ball (0 : ℂ) δ, p + ζ • h ∈ U ∧ ‖I + ζ • J‖ < r ^ 2 := fun ζ hζ =>
    ⟨(hWU ζ hζ).1, (hWU ζ hζ).2.trans hsr⟩
  have hanN : ∀ N : ℕ, AnalyticOnNhd ℂ
      (fun ζ : ℂ => f (p + ζ • h, complexActionRoot (truncateComplexActions N (I + ζ • J))))
      (ball (0 : ℂ) δ) :=
    trunc_line_analytic U f r hr hf heven p h I J (ball (0 : ℂ) δ) isOpen_ball hWr
  -- domination and tail
  set a : ℤ → ℝ := fun n => ‖I n‖ + δ * ‖J n‖ with ha_def
  have ha : Summable a :=
    (NlsGge.ThirdConsultation.G6038S.hasSum_norm1 I).summable.add
      ((NlsGge.ThirdConsultation.G6038S.hasSum_norm1 J).summable.mul_left δ)
  have hKa : ∀ ζ ∈ ball (0 : ℂ) δ, ∀ n, ‖(I + ζ • J) n‖ ≤ a n := by
    intro ζ hζ n
    rw [Kline_apply]
    have hζδ : ‖ζ‖ < δ := by rwa [mem_ball, dist_zero_right] at hζ
    have hJn := norm_nonneg (J n)
    calc ‖I n + ζ * J n‖ ≤ ‖I n‖ + ‖ζ * J n‖ := norm_add_le _ _
      _ = ‖I n‖ + ‖ζ‖ * ‖J n‖ := by rw [norm_mul]
      _ ≤ ‖I n‖ + δ * ‖J n‖ := by nlinarith
  have htail := tail_tendsto a ha
  set L : ℝ := 2 * M / (r - ρ) with hL
  have hL0 : 0 ≤ L := div_nonneg (by linarith) (by linarith)
  have hunif : TendstoUniformlyOn
      (fun (N : ℕ) (ζ : ℂ) => f (p + ζ • h, complexActionRoot (truncateComplexActions N (I + ζ • J))))
      (fun ζ => f (p + ζ • h, complexActionRoot (I + ζ • J))) atTop (ball (0 : ℂ) δ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hε'0 : 0 < ε / (L + 1) := div_pos hε (by linarith)
    have hev := htail.eventually (gt_mem_nhds (pow_pos hε'0 2))
    filter_upwards [hev] with N hN ζ hζ
    have hq : p + ζ • h ∈ U := (hWU ζ hζ).1
    have hKρ : ‖I + ζ • J‖ < ρ ^ 2 := by rw [hρ2]; exact (hWU ζ hζ).2
    have hlip : ‖f (p + ζ • h, complexActionRoot (truncateComplexActions N (I + ζ • J))) -
        f (p + ζ • h, complexActionRoot (I + ζ • J))‖ ≤
        L * ‖complexActionRoot (truncateComplexActions N (I + ζ • J)) - complexActionRoot (I + ζ • J)‖ :=
      lipschitz_of_bdd (fun x => f (p + ζ • h, x)) r ρ M hρr
        (slice_differentiableOn U f r hf _ hq) (fun x hx => hM _ x hq hx)
        _ _ (norm_root_trunc_lt hρ N _ hKρ).le (norm_root_lt hρ _ hKρ).le
    have hsq := root_trunc_sub_sq_le N (I + ζ • J) a ha (hKa ζ hζ)
    have hRlt : ‖complexActionRoot (truncateComplexActions N (I + ζ • J)) - complexActionRoot (I + ζ • J)‖
        < ε / (L + 1) := lt_of_pow_lt_pow_left₀ 2 hε'0.le (lt_of_le_of_lt hsq hN)
    rw [dist_eq_norm, norm_sub_rev]
    calc _ ≤ _ := hlip
      _ ≤ L * (ε / (L + 1)) := mul_le_mul_of_nonneg_left hRlt.le hL0
      _ < ε := small_mul_lt hL0 hε
  have hlim : AnalyticOnNhd ℂ (fun ζ => f (p + ζ • h, complexActionRoot (I + ζ • J))) (ball (0 : ℂ) δ) :=
    NlsGge.Atomic.G4.analyticOnNhd_of_locally_uniform_limit isOpen_ball hanN
      hunif.tendstoLocallyUniformlyOn
  exact hlim 0 (mem_ball_self hδ)

theorem descent_analytic
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    (U : Set P) (hU : IsOpen U)
    (f : P × ComplexDiagonalSpace → ℂ) (r : ℝ) (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (U ×ˢ Metric.ball (0 : ComplexDiagonalSpace) r))
    (heven : ∀ p : P, p ∈ U →
      CoordinatewiseEvenOn (fun x : ComplexDiagonalSpace => f (p, x))
        Set.univ (Metric.ball (0 : ComplexDiagonalSpace) r))
    (hbd : ∃ M : ℝ, ∀ (p : P) (x : ComplexDiagonalSpace),
      p ∈ U → x ∈ Metric.ball (0 : ComplexDiagonalSpace) r → ‖f (p, x)‖ ≤ M) :
    AnalyticOnNhd ℂ (parametricActionDescent f)
      (U ×ˢ Metric.ball (0 : ComplexActionSpace) (r^2)) := by
  obtain ⟨M, hM⟩ := hbd
  have hΩ : IsOpen (U ×ˢ Metric.ball (0 : ComplexActionSpace) (r^2)) := hU.prod isOpen_ball
  apply NlsGge.Atomic.G4.analyticOnNhd_of_weakAnalytic_locallyBounded hΩ
  · intro q hq v ℓ
    have hI : ‖q.2‖ < r ^ 2 := by
      have := hq.2; rwa [mem_ball, dist_zero_right] at this
    have hline : (fun ζ : ℂ => parametricActionDescent f (q + ζ • v)) =
        fun ζ => f (q.1 + ζ • v.1, complexActionRoot (q.2 + ζ • v.2)) := by
      funext ζ
      simp only [parametricActionDescent, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
    have hA := line_analytic U hU f r hr hf heven M hM q.1 v.1 q.2 v.2 hq.1 hI
    rw [← hline] at hA
    exact (ℓ.analyticAt _).comp hA
  · intro q hq
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hΩ q hq
    refine ⟨ε, hε, M, fun y hy => ?_⟩
    obtain ⟨hy1, hy2⟩ := hεsub hy
    rw [mem_ball, dist_zero_right] at hy2
    exact hM _ _ hy1 (by rw [mem_ball, dist_zero_right]; exact norm_root_lt hr _ hy2)

end
end NlsGge.ThirdConsultation.G6039S

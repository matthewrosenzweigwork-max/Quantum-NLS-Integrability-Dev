import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G2.RootProductSq
import NlsGge.Atomic.G2.G2046
import NlsGge.Atomic.G2.G2021
import NlsGge.GK38.DirichletRealBridge
import NlsGge.GK38.StdRootBranchesProducts
import NlsGge.GK38.StdRootBranchesConvergence
import NlsGge.GK38.StdRootBranchesDomain
import NlsGge.GK38.AngleDirichletAnalytic
import NlsGge.GK38.DirichletLabels
import NlsGge.GK38.IsolatingDistance
import NlsGge.GK38.GradFundamentalDefs
import NlsGge.GK38.XiSqOmittedRoot
import NlsGge.GK38.ProductRepr
import NlsGge.GK38.StdRootBranchesFactors

/- G3-014 (proof development, AUTHOR; not self-reviewed).  Head from followup2 STATEMENTS/G3.md G3-014 verbatim; LocalEndpointSegmentSeparation and AnalyticSegmentRoots verbatim from
   DEFINITIONS/G3.lean.md; sourceW/collapsedSet/endpointSet from the SourceFamilyBasic host (X-006 family); gap (landed G2046); rootProduct (landed G2021); the sign clause
   uses the supporting result rootProduct_sq_identity (ROOTPRODUCTSQ kit).
   Route (analytic branches): at phi0 pick c with Re(c·G0), Re(c·G1) > 0 for G0 = a-b, G1 = mu-b (their segment avoids 0 by the separation hypothesis), so
   Re(c·G(phi,t)) > 0 for phi near phi0, t in [0,1]; rseg = σ · e·(c·G)^(1/2) with e^2 = c^-1; rω likewise from c1 = conj(mu-a); σ ∈ {±1} is the locally constant sign
   s = antiDiscrim / (2 I rootProduct rω r(·,1)), s^2 = 1 by rootProduct_sq_identity + dirichlet_perChar_eq_anti_sq38. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def LocalEndpointSegmentSeparation (m : ℤ) (V : Set PotPair)
    (a b : PotPair → ℂ) : Prop :=
  IsOpen V ∧ V ⊆ sourceW \ (collapsedSet m ∪ endpointSet m) ∧
  AnalyticOnNhd ℂ a V ∧ AnalyticOnNhd ℂ b V ∧
  ∀ φ ∈ V, ({a φ,b φ} : Set ℂ) = {lamMinus φ m,lamPlus φ m} ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      ‖a φ + (t : ℂ)*(muSeq φ m-a φ)-b φ‖ ≥ ‖gap φ m‖/3

def AnalyticSegmentRoots (m : ℤ) (V : Set PotPair)
    (a b rω : PotPair → ℂ) (rseg : PotPair → ℝ → ℂ) : Prop :=
  AnalyticOnNhd ℂ rω V ∧
  (∀ t ∈ Icc (0 : ℝ) 1, AnalyticOnNhd ℂ (fun φ => rseg φ t) V) ∧
  ContinuousOn (fun p : PotPair × ℝ => rseg p.1 p.2) (V ×ˢ Icc (0 : ℝ) 1) ∧
  ∀ φ ∈ V,
    rω φ ≠ 0 ∧ rω φ^2 = muSeq φ m-a φ ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      rseg φ t ≠ 0 ∧ rseg φ t^2 = a φ+(t : ℂ)*(muSeq φ m-a φ)-b φ) ∧
    2*Complex.I*rootProduct m (φ,muSeq φ m)*rω φ*rseg φ 1 =
      antiDiscrim φ (muSeq φ m)

namespace G3014Aux

/-- principal square root branch rotated by c: (e * (c x)^(1/2))^2 = x. -/
def sqrtB (c x : ℂ) : ℂ := Complex.exp (-(Complex.log c) / 2) * (c * x) ^ (2⁻¹ : ℂ)

theorem sqrtB_sq {c : ℂ} (hc : c ≠ 0) (x : ℂ) : sqrtB c x ^ 2 = x := by
  unfold sqrtB
  rw [mul_pow, Complex.cpow_ofNat_inv_pow (c * x) 2, ← Complex.exp_nat_mul]
  have : ((2 : ℕ) : ℂ) * (-(Complex.log c) / 2) = -(Complex.log c) := by push_cast; ring
  rw [this, Complex.exp_neg, Complex.exp_log hc]
  field_simp

theorem sqrtB_ne {c : ℂ} (hc : c ≠ 0) {x : ℂ} (hx : x ≠ 0) : sqrtB c x ≠ 0 := by
  intro h
  have := sqrtB_sq hc x
  rw [h] at this
  exact hx (by simpa using this.symm)

theorem sqrtB_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {h : E → ℂ} {x : E} {c : ℂ}
    (hh : AnalyticAt ℂ h x) (hs : c * h x ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun y => sqrtB c (h y)) x := by
  unfold sqrtB
  exact analyticAt_const.mul
    (AnalyticAt.cpow (analyticAt_const.mul hh) analyticAt_const hs)

/-- the n-th Dirichlet root avoids every other gap segment (isolating certificate). -/
theorem avoids_other (φ : PotPair) (hφ : φ ∈ gkW) (m : ℤ) :
    ∀ n : ℤ, n ≠ m → muSeq φ m ∉ segment ℝ (lamMinus φ n) (lamPlus φ n) := by
  obtain ⟨u, ρ0, hcert, hmem⟩ := hφ
  obtain ⟨hρ0, C, R, c, N, hgeom, hall⟩ := hcert
  have hsp := hall φ hmem
  intro n hnm hz
  have h1 := (hsp.1 n).1 hz
  have h2 := (hsp.1 m).2.1
  have hd := (hgeom.2.2.2.1 n m hnm).1
  have hpos : 0 < ballDistance38 (C n) (C m) (R n) (R m) := by
    have hc1 : 1 ≤ c := hgeom.2.2.1
    have hd1 : (1 : ℝ) ≤ |((n - m : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hnm)
    have : 0 < c⁻¹ * |((n - m : ℤ) : ℝ)| := by
      have hc0 : 0 < c := by linarith
      positivity
    exact lt_of_lt_of_le this hd
  have hle := ballDistance38_le_pair (C n) (C m) (R n) (R m) h1 h2
  rw [dist_self] at hle
  linarith

end G3014Aux


namespace G3014Aux

theorem exists_pos_rot (g0 g1 : ℂ) (h0 : g0 ≠ 0) (h1 : g1 ≠ 0)
    (hseg : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → (1 - (t : ℂ)) * g0 + (t : ℂ) * g1 ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ 0 < (c * g0).re ∧ 0 < (c * g1).re := by
  set n0 : ℝ := ‖g0‖ with hn0
  set n1 : ℝ := ‖g1‖ with hn1
  have hn0p : 0 < n0 := norm_pos_iff.2 h0
  have hn1p : 0 < n1 := norm_pos_iff.2 h1
  have e0 : n0 ^ 2 = g0.re ^ 2 + g0.im ^ 2 := by
    rw [hn0, Complex.sq_norm, Complex.normSq_apply]; ring
  have e1 : n1 ^ 2 = g1.re ^ 2 + g1.im ^ 2 := by
    rw [hn1, Complex.sq_norm, Complex.normSq_apply]; ring
  set ρ : ℝ := g0.re * g1.re + g0.im * g1.im with hρ
  have hkey : 0 < n0 * n1 + ρ := by
    by_contra hle
    push_neg at hle
    have hcs : ρ ^ 2 ≤ (n0 * n1) ^ 2 := by
      have : (n0 * n1) ^ 2 = (g0.re ^ 2 + g0.im ^ 2) * (g1.re ^ 2 + g1.im ^ 2) := by
        rw [mul_pow, e0, e1]
      rw [this, hρ]
      nlinarith [sq_nonneg (g0.re * g1.im - g0.im * g1.re)]
    have hρneg : ρ = -(n0 * n1) := by
      have h2 : 0 ≤ n0 * n1 := by positivity
      nlinarith [sq_nonneg (ρ + n0 * n1)]
    -- w = n1 g0 + n0 g1 vanishes
    have hw : (n1 : ℂ) * g0 + (n0 : ℂ) * g1 = 0 := by
      apply Complex.ext
      · have h3 : ((n1 * g0.re + n0 * g1.re)) ^ 2 + ((n1 * g0.im + n0 * g1.im)) ^ 2 = 0 := by
          have hx : ((n1 * g0.re + n0 * g1.re)) ^ 2 + ((n1 * g0.im + n0 * g1.im)) ^ 2 =
              n1 ^ 2 * (g0.re ^ 2 + g0.im ^ 2) + n0 ^ 2 * (g1.re ^ 2 + g1.im ^ 2) + 2 * n0 * n1 * ρ := by
            rw [hρ]; ring
          rw [hx, ← e0, ← e1, hρneg]; ring
        have := sq_nonneg (n1 * g0.re + n0 * g1.re)
        have := sq_nonneg (n1 * g0.im + n0 * g1.im)
        have h4 : n1 * g0.re + n0 * g1.re = 0 := by nlinarith
        simpa using h4
      · have h3 : ((n1 * g0.re + n0 * g1.re)) ^ 2 + ((n1 * g0.im + n0 * g1.im)) ^ 2 = 0 := by
          have hx : ((n1 * g0.re + n0 * g1.re)) ^ 2 + ((n1 * g0.im + n0 * g1.im)) ^ 2 =
              n1 ^ 2 * (g0.re ^ 2 + g0.im ^ 2) + n0 ^ 2 * (g1.re ^ 2 + g1.im ^ 2) + 2 * n0 * n1 * ρ := by
            rw [hρ]; ring
          rw [hx, ← e0, ← e1, hρneg]; ring
        have := sq_nonneg (n1 * g0.re + n0 * g1.re)
        have := sq_nonneg (n1 * g0.im + n0 * g1.im)
        have h4 : n1 * g0.im + n0 * g1.im = 0 := by nlinarith
        simpa using h4
    set t0 : ℝ := n0 / (n0 + n1) with ht0
    have hS : 0 < n0 + n1 := by linarith
    have ht0I : t0 ∈ Icc (0 : ℝ) 1 := ⟨by positivity, by rw [ht0, div_le_one hS]; linarith⟩
    apply hseg t0 ht0I
    have hSc : ((n0 + n1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
    have : (1 - (t0 : ℂ)) * g0 + (t0 : ℂ) * g1 =
        ((n1 : ℂ) * g0 + (n0 : ℂ) * g1) / ((n0 + n1 : ℝ) : ℂ) := by
      rw [ht0]; push_cast at hSc ⊢; field_simp; ring
    rw [this, hw, zero_div]
  have hp0 : 0 < ((⟨n1 * g0.re + n0 * g1.re, -(n1 * g0.im + n0 * g1.im)⟩ : ℂ) * g0).re := by
    simp only [Complex.mul_re]
    nlinarith [e0, hkey, hn0p]
  have hp1 : 0 < ((⟨n1 * g0.re + n0 * g1.re, -(n1 * g0.im + n0 * g1.im)⟩ : ℂ) * g1).re := by
    simp only [Complex.mul_re]
    nlinarith [e1, hkey, hn1p]
  refine ⟨⟨n1 * g0.re + n0 * g1.re, -(n1 * g0.im + n0 * g1.im)⟩, ?_, hp0, hp1⟩
  intro hc
  rw [hc] at hp0
  simp at hp0

end G3014Aux

theorem G3_014 (m : ℤ) (V : Set PotPair) (a b : PotPair → ℂ)
    (hV : LocalEndpointSegmentSeparation m V a b) (φ0 : PotPair) (hφ0 : φ0 ∈ V) :
  ∃ U : Set PotPair, ∃ rω : PotPair → ℂ, ∃ rseg : PotPair → ℝ → ℂ,
    IsOpen U ∧ φ0 ∈ U ∧ U ⊆ V ∧ AnalyticSegmentRoots m U a b rω rseg := by
  classical
  obtain ⟨hVo, hVsub, haA, hbA, hVp⟩ := hV
  have hgk : ∀ φ ∈ V, φ ∈ gkW := fun φ hφ => sourceFamily.W_gk (hVsub hφ).1
  have hμA : ∀ φ ∈ V, AnalyticAt ℂ (fun ψ : PotPair => muSeq ψ m) φ :=
    fun φ hφ => (analyticOnNhd_muSeq_complex38 m) φ (hgk φ hφ)
  have hg2 : ∀ φ ∈ V, gamma2 φ m = gap φ m ^ 2 := fun φ hφ =>
    gamma2_pair_gap38 discC discR isolating_selectors_admissible38 φ (hgk φ hφ) m
  have hgap : ∀ φ ∈ V, gap φ m ≠ 0 := by
    intro φ hφ h
    apply (hVsub hφ).2
    left
    exact ⟨(hVsub hφ).1, by rw [hg2 φ hφ, h]; ring⟩
  have hper : ∀ φ ∈ V, perChar φ (muSeq φ m) ≠ 0 := by
    intro φ hφ h
    apply (hVsub hφ).2
    right
    exact ⟨(hVsub hφ).1, h⟩
  have hmroot : ∀ φ : PotPair, perChar φ (lamMinus φ m) = 0 := fun φ =>
    (lamSeq_enumeration38 φ).1 (2 * m)
  have hproot : ∀ φ : PotPair, perChar φ (lamPlus φ m) = 0 := fun φ =>
    (lamSeq_enumeration38 φ).1 (2 * m + 1)
  have hab : ∀ φ ∈ V, (a φ = lamMinus φ m ∧ b φ = lamPlus φ m) ∨
      (a φ = lamPlus φ m ∧ b φ = lamMinus φ m) := fun φ hφ =>
    Set.pair_eq_pair_iff.1 (hVp φ hφ).1
  have hμa : ∀ φ ∈ V, muSeq φ m - a φ ≠ 0 := by
    intro φ hφ h
    apply hper φ hφ
    have h' : muSeq φ m = a φ := sub_eq_zero.1 h
    rcases hab φ hφ with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h', h1]; exact hmroot φ
    · rw [h', h1]; exact hproot φ
  have hμb : ∀ φ ∈ V, muSeq φ m - b φ ≠ 0 := by
    intro φ hφ h
    apply hper φ hφ
    have h' : muSeq φ m = b φ := sub_eq_zero.1 h
    rcases hab φ hφ with ⟨-, h1⟩ | ⟨-, h1⟩
    · rw [h', h1]; exact hproot φ
    · rw [h', h1]; exact hmroot φ
  have hsw : ∀ φ ∈ V, (muSeq φ m - a φ) * (muSeq φ m - b φ) =
      (muSeq φ m - lamMinus φ m) * (muSeq φ m - lamPlus φ m) := by
    intro φ hφ
    rcases hab φ hφ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]; ring
  have hG : ∀ φ ∈ V, ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      a φ + (t : ℂ) * (muSeq φ m - a φ) - b φ ≠ 0 := by
    intro φ hφ t ht h
    have hb := (hVp φ hφ).2 t ht
    rw [h, norm_zero] at hb
    have : 0 < ‖gap φ m‖ := norm_pos_iff.2 (hgap φ hφ)
    linarith
  have hdom : ∀ φ ∈ V, (φ, muSeq φ m) ∈ a5OmittedRootDomain38 m := fun φ hφ =>
    ⟨hgk φ hφ, G3014Aux.avoids_other φ (hgk φ hφ) m⟩
  -- abbreviations
  set G : PotPair → ℝ → ℂ := fun φ t => a φ + (t : ℂ) * (muSeq φ m - a φ) - b φ with hGdef
  set g1 : PotPair → ℂ := fun φ => muSeq φ m - a φ with hg1def
  -- the rotation for the segment
  have hG0 : ∀ φ ∈ V, a φ - b φ ≠ 0 := by
    intro φ hφ h
    exact hG φ hφ 0 ⟨le_rfl, zero_le_one⟩ (by simpa using h)
  have hG1 : ∀ φ ∈ V, muSeq φ m - b φ ≠ 0 := hμb
  obtain ⟨c, hc0, hcr0, hcr1⟩ := G3014Aux.exists_pos_rot (a φ0 - b φ0) (muSeq φ0 m - b φ0)
    (hG0 φ0 hφ0) (hG1 φ0 hφ0) (by
      intro t ht h
      apply hG φ0 hφ0 t ht
      rw [← h]; ring)
  -- the rotation for rω
  set c1 : ℂ := (starRingEnd ℂ) (g1 φ0) with hc1def
  have hg1ne : g1 φ0 ≠ 0 := hμa φ0 hφ0
  have hc10 : c1 ≠ 0 := by simpa [hc1def] using hg1ne
  have hc1r : 0 < (c1 * g1 φ0).re := by
    rw [hc1def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    have := Complex.normSq_pos.2 hg1ne
    rw [Complex.normSq_apply] at this
    nlinarith [this]
  -- continuity facts at φ0
  have hAc : ∀ φ ∈ V, AnalyticAt ℂ a φ := fun φ hφ => haA φ hφ
  have hBc : ∀ φ ∈ V, AnalyticAt ℂ b φ := fun φ hφ => hbA φ hφ
  have hV0 : V ∈ 𝓝 φ0 := hVo.mem_nhds hφ0
  have hcont_re : ∀ (f : PotPair → ℂ), ContinuousAt f φ0 → ∀ (k : ℂ), 0 < (k * f φ0).re →
      ∀ᶠ φ in 𝓝 φ0, 0 < (k * f φ).re := by
    intro f hf k hk
    have : ContinuousAt (fun φ => (k * f φ).re) φ0 :=
      Complex.continuous_re.continuousAt.comp (continuousAt_const.mul hf)
    exact this.eventually (lt_mem_nhds hk)
  have hAcont : ContinuousAt (fun φ => a φ - b φ) φ0 := ((hAc φ0 hφ0).continuousAt).sub (hBc φ0 hφ0).continuousAt
  have hBcont : ContinuousAt (fun φ => muSeq φ m - b φ) φ0 :=
    (hμA φ0 hφ0).continuousAt.sub (hBc φ0 hφ0).continuousAt
  have hg1cont : ContinuousAt g1 φ0 := (hμA φ0 hφ0).continuousAt.sub (hAc φ0 hφ0).continuousAt
  have ev0 := hcont_re _ hAcont c hcr0
  have ev1 := hcont_re _ hBcont c hcr1
  have evω := hcont_re g1 hg1cont c1 hc1r
  -- sign function
  set r0 : PotPair → ℝ → ℂ := fun φ t => G3014Aux.sqrtB c (G φ t) with hr0
  set rω0 : PotPair → ℂ := fun φ => G3014Aux.sqrtB c1 (g1 φ) with hrω0
  set D : PotPair → ℂ := fun φ =>
    2 * Complex.I * rootProduct m (φ, muSeq φ m) * rω0 φ * r0 φ 1 with hD
  set s : PotPair → ℂ := fun φ => antiDiscrim φ (muSeq φ m) / D φ with hs
  -- real-part positivity on the good set
  have hgood : ∀ φ ∈ V, 0 < (c * (a φ - b φ)).re → 0 < (c * (muSeq φ m - b φ)).re →
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → 0 < (c * G φ t).re := by
    intro φ hφ h0 h1 t ht
    have e : c * G φ t = ((1 - t : ℝ) : ℂ) * (c * (a φ - b φ)) + (t : ℂ) * (c * (muSeq φ m - b φ)) := by
      simp only [hGdef]; push_cast; ring
    rw [e, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    rcases ht with ⟨ht0, ht1⟩
    rcases lt_or_eq_of_le ht1 with h | h
    · nlinarith [mul_pos (sub_pos.2 h) h0, mul_nonneg ht0 h1.le]
    · rw [h]; simpa using h1
  have hI : (2 * Complex.I) ^ 2 = -4 := by
    rw [mul_pow, Complex.I_sq]; norm_num
  have hDne : ∀ φ ∈ V, D φ ≠ 0 := by
    intro φ hφ
    have hrp0 : rootProduct m (φ, muSeq φ m) ≠ 0 := by
      have := a5OmittedRoot_ne_zero38 m (φ, muSeq φ m) (hdom φ hφ)
      unfold rootProduct
      exact mul_ne_zero (inv_ne_zero (by exact_mod_cast Lib.piN_ne_zero m)) this
    have h1 : rω0 φ ≠ 0 := G3014Aux.sqrtB_ne hc10 (hμa φ hφ)
    have h2 : r0 φ 1 ≠ 0 := G3014Aux.sqrtB_ne hc0 (hG φ hφ 1 ⟨zero_le_one, le_rfl⟩)
    simp only [hD]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hrp0) h1) h2
  have hDsq : ∀ φ ∈ V, D φ ^ 2 = antiDiscrim φ (muSeq φ m) ^ 2 := by
    intro φ hφ
    have hr1sq : r0 φ 1 ^ 2 = muSeq φ m - b φ := by
      simp only [hr0]
      rw [G3014Aux.sqrtB_sq hc0]
      simp only [hGdef]; push_cast; ring
    have hrωsq : rω0 φ ^ 2 = g1 φ := G3014Aux.sqrtB_sq hc10 _
    have hrp := rootProduct_sq_identity m φ (hgk φ hφ) (muSeq φ m)
      (G3014Aux.avoids_other φ (hgk φ hφ) m)
    have hA := dirichlet_perChar_eq_anti_sq38 φ (muSeq φ m) (muSeq_root38 φ m)
    have hex : D φ ^ 2 = (2 * Complex.I) ^ 2 * rootProduct m (φ, muSeq φ m) ^ 2 *
        rω0 φ ^ 2 * r0 φ 1 ^ 2 := by simp only [hD]; ring
    rw [hex, hI, hrωsq, hr1sq, ← hA, hrp]
    have := hsw φ hφ
    simp only [hg1def]
    linear_combination (-4 * rootProduct m (φ, muSeq φ m) ^ 2) * this
  have hspm : ∀ φ ∈ V, s φ = 1 ∨ s φ = -1 := by
    intro φ hφ
    have hd := hDne φ hφ
    have h1 : s φ ^ 2 = 1 := by
      simp only [hs]
      rw [div_pow, ← hDsq φ hφ]
      exact div_self (pow_ne_zero 2 hd)
    have : (s φ - 1) * (s φ + 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  -- continuity of s at φ0
  have hg1an : AnalyticAt ℂ g1 φ0 := (hμA φ0 hφ0).sub (hAc φ0 hφ0)
  have hslitω : c1 * g1 φ0 ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.2 (Or.inl hc1r)
  have hGan : ∀ t : ℝ, ∀ φ ∈ V, AnalyticAt ℂ (fun ψ => G ψ t) φ := by
    intro t φ hφ
    simp only [hGdef]
    exact ((hAc φ hφ).add (analyticAt_const.mul ((hμA φ hφ).sub (hAc φ hφ)))).sub (hBc φ hφ)
  have hslit1 : c * G φ0 1 ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
    exact hgood φ0 hφ0 hcr0 hcr1 1 ⟨zero_le_one, le_rfl⟩
  have hrωan : AnalyticAt ℂ rω0 φ0 := G3014Aux.sqrtB_analyticAt hg1an hslitω
  have hr1an : AnalyticAt ℂ (fun φ => r0 φ 1) φ0 := G3014Aux.sqrtB_analyticAt (hGan 1 φ0 hφ0) hslit1
  have hμcont : ContinuousAt (fun φ : PotPair => (φ, muSeq φ m)) φ0 :=
    continuousAt_id.prodMk (hμA φ0 hφ0).continuousAt
  have hrpcont : ContinuousAt (fun φ : PotPair => rootProduct m (φ, muSeq φ m)) φ0 := by
    have h1 : ContinuousAt (a5OmittedRootProduct38 m) (φ0, muSeq φ0 m) :=
      (a5OmittedRoot_analytic38 m _ (hdom φ0 hφ0)).continuousAt
    have h2 : ContinuousAt (fun φ : PotPair => a5OmittedRootProduct38 m (φ, muSeq φ m)) φ0 :=
      ContinuousAt.comp (g := a5OmittedRootProduct38 m) (f := fun φ : PotPair => (φ, muSeq φ m)) h1 hμcont
    exact continuousAt_const.mul h2
  have hAnti : ContinuousAt (fun φ : PotPair => antiDiscrim φ (muSeq φ m)) φ0 := by
    have h1 : ContinuousAt (fun p : PotPair × ℂ => antiDiscrim p.1 p.2) (φ0, muSeq φ0 m) :=
      (analyticOnNhd_antiDiscrim _ (Set.mem_univ _)).continuousAt
    exact ContinuousAt.comp (g := fun p : PotPair × ℂ => antiDiscrim p.1 p.2)
      (f := fun φ : PotPair => (φ, muSeq φ m)) h1 hμcont
  have hDcont : ContinuousAt D φ0 := by
    exact (((continuousAt_const.mul hrpcont).mul hrωan.continuousAt).mul hr1an.continuousAt)
  have hscont : ContinuousAt s φ0 := hAnti.div hDcont (hDne φ0 hφ0)
  set σ0 : ℂ := s φ0 with hσ0
  have hσpm : σ0 = 1 ∨ σ0 = -1 := hspm φ0 hφ0
  have hσsq : σ0 ^ 2 = 1 := by rcases hσpm with h | h <;> rw [h] <;> norm_num
  have evs : ∀ᶠ φ in 𝓝 φ0, ‖s φ - σ0‖ < 1 := by
    have := hscont.eventually (Metric.ball_mem_nhds σ0 one_pos)
    filter_upwards [this] with φ hφ
    rw [← dist_eq_norm]; exact hφ
  have hev : ∀ᶠ φ in 𝓝 φ0, φ ∈ V ∧ 0 < (c * (a φ - b φ)).re ∧ 0 < (c * (muSeq φ m - b φ)).re ∧
      0 < (c1 * g1 φ).re ∧ ‖s φ - σ0‖ < 1 := by
    filter_upwards [hV0, ev0, ev1, evω, evs] with φ h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨U, hUsub, hUopen, hφ0U⟩ := _root_.mem_nhds_iff.1 hev
  have hsU : ∀ φ ∈ U, s φ = σ0 := by
    intro φ hφ
    obtain ⟨hφV, -, -, -, hn⟩ := hUsub hφ
    rcases hspm φ hφV with h | h <;> rcases hσpm with h' | h' <;> rw [h, h'] at hn ⊢ <;>
      first | rfl | (norm_num at hn)
  have hUV : U ⊆ V := fun φ hφ => (hUsub hφ).1
  have hGslit : ∀ φ ∈ U, ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → c * G φ t ∈ Complex.slitPlane := by
    intro φ hφ t ht
    obtain ⟨hφV, h0, h1, -, -⟩ := hUsub hφ
    exact Complex.mem_slitPlane_iff.2 (Or.inl (hgood φ hφV h0 h1 t ht))
  refine ⟨U, rω0, fun φ t => σ0 * r0 φ t, hUopen, hφ0U, hUV, ?_, ?_, ?_, ?_⟩
  · intro φ hφ
    obtain ⟨hφV, -, -, h3, -⟩ := hUsub hφ
    exact G3014Aux.sqrtB_analyticAt ((hμA φ hφV).sub (hAc φ hφV))
      (Complex.mem_slitPlane_iff.2 (Or.inl h3))
  · intro t ht φ hφ
    exact analyticAt_const.mul
      (G3014Aux.sqrtB_analyticAt (hGan t φ (hUV hφ)) (hGslit φ hφ t ht))
  · have hGc : ContinuousOn (fun p : PotPair × ℝ => c * G p.1 p.2) (U ×ˢ Icc (0 : ℝ) 1) := by
      intro p hp
      apply ContinuousAt.continuousWithinAt
      have hpV : p.1 ∈ V := hUV hp.1
      have h1 : ContinuousAt (fun q : PotPair × ℝ => a q.1) p :=
        (hAc p.1 hpV).continuousAt.comp continuousAt_fst
      have h2 : ContinuousAt (fun q : PotPair × ℝ => b q.1) p :=
        (hBc p.1 hpV).continuousAt.comp continuousAt_fst
      have h3 : ContinuousAt (fun q : PotPair × ℝ => muSeq q.1 m) p :=
        (hμA p.1 hpV).continuousAt.comp continuousAt_fst
      have h4 : ContinuousAt (fun q : PotPair × ℝ => ((q.2 : ℝ) : ℂ)) p :=
        Complex.continuous_ofReal.continuousAt.comp continuousAt_snd
      simp only [hGdef]
      exact continuousAt_const.mul ((h1.add (h4.mul (h3.sub h1))).sub h2)
    have hcp : ContinuousOn (fun p : PotPair × ℝ => (c * G p.1 p.2) ^ (2⁻¹ : ℂ))
        (U ×ˢ Icc (0 : ℝ) 1) :=
      ContinuousOn.cpow hGc continuousOn_const (fun p hp => hGslit p.1 hp.1 p.2 hp.2)
    simp only [hr0, G3014Aux.sqrtB]
    exact continuousOn_const.mul (continuousOn_const.mul hcp)
  · intro φ hφ
    have hφV : φ ∈ V := hUV hφ
    refine ⟨G3014Aux.sqrtB_ne hc10 (hμa φ hφV), G3014Aux.sqrtB_sq hc10 _, ?_, ?_⟩
    · intro t ht
      have hne := hG φ hφV t ht
      have hsq : r0 φ t ^ 2 = G φ t := G3014Aux.sqrtB_sq hc0 _
      refine ⟨?_, ?_⟩
      · intro h
        have h0 : r0 φ t = 0 := by
          rcases mul_eq_zero.1 h with h' | h'
          · exact absurd h' (by rcases hσpm with h'' | h'' <;> rw [h''] <;> norm_num)
          · exact h'
        apply hne
        have : G φ t = 0 := by rw [← hsq, h0]; ring
        exact this
      · show (σ0 * r0 φ t) ^ 2 = _
        rw [mul_pow, hσsq, one_mul, hsq]
    · have hsφ := hsU φ hφ
      have hd := hDne φ hφV
      have hrel : antiDiscrim φ (muSeq φ m) = σ0 * D φ := by
        rw [← hsφ]; simp only [hs]; field_simp
      rw [hrel]
      simp only [hD]
      ring

end
end NlsGge.GKDefinitionDesign

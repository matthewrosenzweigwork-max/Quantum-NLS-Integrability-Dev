import Mathlib
import QuantumNLS.Local003Final
import QuantumNLS.Local007MassN
import QuantumNLS.Local007Rfun
import QuantumNLS.Local007Lp
import QuantumNLS.Local007AlgA
import QuantumNLS.Fourier

/-! LOCAL-007 `prop:reset-exact-factor`, the factorization part (everything except the final conditional
`ζ` clause, which is in `Local007Zeta`/`Local007Statement`).

`Pkg L κ r ρ C n a b` is the conjunction printed in the accepted `Local003Final.reset_uniform_reduction_profile`
(the polar-normalized Riesz reduction `B_n(u) = [[a_n, conj b_n],[b_n, a_n]]`, the eigenvalue structure of the
rank-two cluster, and the estimates on `g_n = √L/(2i√κ) b_n`).

`reset_exact_factor_main`: there are `ρ, C`, the LOCAL-003 data `(a_n, b_n)`, and an analytic
`rr : L²(𝕋_L) → ℓ∞(ℤ)` with `I_n(u) = |g_n(u)|² rr(u)_n`, `1/2 < rr_n < 3/2`, `rr(0) = 1`,
`‖rr(u) - 1‖_∞ ≤ C‖u‖²`, `‖D rr(u)‖ ≤ C‖u‖`. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric Filter Topology BoundedContinuousFunction
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local007Final
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002SA QuantumNLS.Local003Analytic
  QuantumNLS.Local003Isometry QuantumNLS.Local003Inst QuantumNLS.Local003First
open QuantumNLS.Local002Bridge QuantumNLS.PhysicalTensor
variable {L κ r : ℝ} [Fact (0 < L)]

/-- The coefficient `√L / (2 i √κ)` of `g_n = gcoef · b_n`. -/
def gcoef (L κ : ℝ) : ℂ := ((Real.sqrt L : ℝ) : ℂ) / (2 * Complex.I * (Real.sqrt κ : ℂ))

def Pkg (L κ r ρ C : ℝ) [Fact (0 < L)] (n : ℤ) (a : L2T L → ℝ) (b : L2T L → ℂ) : Prop :=
  AnalyticOnNhd ℝ a (ball 0 ρ) ∧ AnalyticOnNhd ℝ b (ball 0 ρ) ∧
    (∀ u ∈ ball (0 : L2T L) ρ, SmallCompression L κ (circleRep u) n r) ∧
    (∀ u ∈ ball (0 : L2T L) ρ, ∀ h : SmallCompression L κ (circleRep u) n r, ∀ v : E2,
      reducedMatrix2 L κ (circleRep u) n r h v =
        vec2 ((a u : ℂ) * v 0 + conj (b u) * v 1) (b u * v 0 + (a u : ℂ) * v 1)) ∧
    (∀ u ∈ ball (0 : L2T L) ρ,
      (∀ lam : ℂ, ‖lam - (pm L n : ℂ)‖ < r →
        ∃ Eig : Submodule ℂ (H2 L),
          (∀ f : H2 L, f ∈ Eig ↔ (f, lam • f) ∈ LuGraph L κ (circleRep u) (parity n)) ∧
          Module.finrank ℂ Eig =
            Multiset.count lam {((a u + ‖b u‖ : ℝ) : ℂ), ((a u - ‖b u‖ : ℝ) : ℂ)}) ∧
      ‖((a u + ‖b u‖ : ℝ) : ℂ) - (pm L n : ℂ)‖ < r ∧ ‖((a u - ‖b u‖ : ℝ) : ℂ) - (pm L n : ℂ)‖ < r ∧
      (∀ lam : ℂ, ‖lam - (pm L n : ℂ)‖ < r → lam ≠ ((a u + ‖b u‖ : ℝ) : ℂ) →
        lam ≠ ((a u - ‖b u‖ : ℝ) : ℂ) →
        ∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ (circleRep u) (parity n) lam R) ∧
      (((a u + ‖b u‖ : ℝ) : ℂ) = ((a u - ‖b u‖ : ℝ) : ℂ) ↔ b u = 0)) ∧
    AnalyticOnNhd ℝ (fun u : L2T L => gcoef L κ * b u) (ball 0 ρ) ∧
    (∀ u ∈ ball (0 : L2T L) ρ,
      ‖gcoef L κ * b u - QuantumNLS.Fourier.coeff L (u : AddCircle L → ℂ) n‖ ≤ C * ‖u‖ ^ 3) ∧
    (∀ u ∈ ball (0 : L2T L) ρ,
      DifferentiableAt ℝ (fun w : L2T L => gcoef L κ * b w) u ∧
      ‖fderiv ℝ (fun w : L2T L => gcoef L κ * b w) u -
        fderiv ℝ (fun w : L2T L => gcoef L κ * b w) 0‖ ≤ C * ‖u‖ ^ 2)

theorem Pkg.mono {ρ ρ' C C' : ℝ} (h : ρ' ≤ ρ) (hC : C ≤ C') {n : ℤ} {a : L2T L → ℝ} {b : L2T L → ℂ}
    (hp : Pkg L κ r ρ C n a b) : Pkg L κ r ρ' C' n a b := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hp
  have hs : ball (0 : L2T L) ρ' ⊆ ball (0 : L2T L) ρ := ball_subset_ball h
  refine ⟨h1.mono hs, h2.mono hs, fun u hu => h3 u (hs hu), fun u hu => h4 u (hs hu),
    fun u hu => h5 u (hs hu), h6.mono hs, fun u hu => (h7 u (hs hu)).trans ?_, fun u hu => ⟨(h8 u (hs hu)).1, (h8 u (hs hu)).2.trans ?_⟩⟩
  · exact mul_le_mul_of_nonneg_right hC (by positivity)
  · exact mul_le_mul_of_nonneg_right hC (by positivity)

theorem norm_gcoef_sq (hκ : 0 < κ) : ‖gcoef L κ‖ ^ 2 = L / (4 * κ) := by
  have hL : 0 < L := Fact.out
  unfold gcoef
  rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (Real.sqrt_nonneg _), Complex.norm_two]
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hL.le, Real.sq_sqrt hκ.le]
  norm_num

theorem boost_zero_int (v : L2T L) : QuantumNLS.RootMassBoostSymbol.boost 0 v = v := by
  apply Lp.ext
  filter_upwards [QuantumNLS.RootMassBoostSymbol.coe_boost 0 v] with x hx
  rw [hx]; simp [fourier_apply]

theorem boost_zero_zero (k : ℤ) : QuantumNLS.RootMassBoostSymbol.boost k (0 : L2T L) = 0 := by
  have := QuantumNLS.Local007Gauge.boost_smul k (0 : ℂ) (0 : L2T L)
  simpa using this

theorem free_zero {κ : ℝ} {a : ℝ} (ha : |a| < 2 * Real.pi / L)
    (h : QuantumNLS.L2SpatialTransfer.discriminant κ (0 : L2T L) (a : ℂ) = 2) : a = 0 := by
  have hL : 0 < L := Fact.out
  rw [QuantumNLS.PhysicalVacuumSourceFacts.discriminant_zero] at h
  have e : (L : ℂ) * (a : ℂ) / 2 = ((L * a / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e] at h
  have h2 : Real.cos (L * a / 2) = 1 := by
    have h3 : Complex.cos ((L * a / 2 : ℝ) : ℂ) = 1 := by linear_combination h / 2
    have h4 : ((Real.cos (L * a / 2) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [Complex.ofReal_cos, h3]; simp
    exact Complex.ofReal_injective h4
  obtain ⟨k, hk⟩ := Real.cos_eq_one_iff _ |>.1 h2
  have hb : |L * a / 2| < Real.pi := by
    rw [abs_div, abs_mul, abs_of_pos hL, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have : L * |a| < 2 * Real.pi := by
      have := mul_lt_mul_of_pos_left ha hL
      rwa [mul_div_cancel₀ _ hL.ne'] at this
    linarith
  have hk0 : (k : ℝ) = 0 := by
    have h1 : |(k : ℝ) * (2 * Real.pi)| < Real.pi := by rw [hk]; exact hb
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h1
    have h2 : |(k : ℝ)| < 1 := by nlinarith [Real.pi_pos]
    have h3 : |k| < 1 := by exact_mod_cast h2
    have h3' := abs_lt.1 h3
    have : k = 0 := by omega
    simp [this]
  rw [hk0, zero_mul] at hk
  have : L * a = 0 := by linarith
  exact (mul_eq_zero.1 this).resolve_left hL.ne'

theorem abs_add_lt {a p t r : ℝ} (ht : 0 ≤ t)
    (h1 : ‖((a + t : ℝ) : ℂ) - (p : ℂ)‖ < r) (h2 : ‖((a - t : ℝ) : ℂ) - (p : ℂ)‖ < r) :
    |a - p| + t < r := by
  have e1 : ‖((a + t : ℝ) : ℂ) - (p : ℂ)‖ = |a - p + t| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; congr 1; ring
  have e2 : ‖((a - t : ℝ) : ℂ) - (p : ℂ)‖ = |a - p - t| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; congr 1; ring
  rw [e1] at h1; rw [e2] at h2
  have h1' := abs_lt.1 h1
  have h2' := abs_lt.1 h2
  rcases abs_cases (a - p) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]


theorem reset_exact_factor_main (hκ : 0 < κ) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)),
        (∀ n, Pkg L κ r ρ C n (a n) (b n)) ∧ AnalyticOnNhd ℝ rr (ball (0 : L2T L) ρ) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
          (QuantumNLS.RootIndexedMasses.masses hκ u).1 n = ‖gcoef L κ * b n u‖ ^ 2 * rr u n) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, 1 / 2 < rr u n ∧ rr u n < 3 / 2) ∧ rr 0 = 1 ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ‖rr u - 1‖ ≤ C * ‖u‖ ^ 2) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ‖fderiv ℝ rr u‖ ≤ C * ‖u‖) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, rr u n = rr (QuantumNLS.RootMassBoostSymbol.boost (-n) u) 0) := by
  have hL : 0 < L := Fact.out
  obtain ⟨ρ3, hρ3, C3, hC3, hall⟩ := QuantumNLS.Local003Final.reset_uniform_reduction_profile hL hκ hr hr2
  choose a b hab using hall
  have hpk : ∀ n, Pkg L κ r ρ3 C3 n (a n) (b n) := fun n => hab n
  set c : ℝ := 1 / (8 * L) with hc
  obtain ⟨Fh, hFa, hFh⟩ := QuantumNLS.Local007AlgA.Fhat_pkg (L := L) κ c
  have hF0 : Fh 0 = QuantumNLS.Local007AlgB.F0 c L := by
    ext θ
    rw [hFh 0 (by simp) θ, QuantumNLS.Local007AlgB.F0_apply]
    exact QuantumNLS.PhysicalVacuumSourceFacts.discriminant_zero κ _
  have h0ball : (0 : L2T L) ∈ ball (0 : L2T L) ρ3 := mem_ball_self hρ3
  -- index-0 data vanish at 0
  have hb0 : b 0 0 = 0 := by
    have h7 := (hpk 0).2.2.2.2.2.2.1 0 h0ball
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h7
    have hc0 : QuantumNLS.Fourier.coeff L ((0 : L2T L) : AddCircle L → ℂ) 0 = 0 := by
      rw [← QuantumNLS.Fourier.fourierL2_apply]; simp
    have : gcoef L κ * b 0 0 = 0 := by
      have := norm_le_zero_iff.1 h7
      rw [hc0] at this; simpa using this
    have hg : gcoef L κ ≠ 0 := by
      intro h; have := norm_gcoef_sq (L := L) hκ; rw [h, norm_zero] at this
      have : 0 < L / (4 * κ) := by positivity
      norm_num at *; linarith
    exact (mul_eq_zero.1 this).resolve_left hg
  have ha0 : a 0 0 = 0 := by
    obtain ⟨hE, h1, h2, hRs, -⟩ := (hpk 0).2.2.2.2.1 0 h0ball
    have hbn : ‖b 0 0‖ = 0 := by rw [hb0, norm_zero]
    have hp0 : QuantumNLS.LocalSpectral.pm L 0 = 0 := by simp [QuantumNLS.LocalSpectral.pm]
    have hw : ‖((a 0 0 : ℝ) : ℂ)‖ < r := by
      have := h1
      rw [hbn, hp0] at this
      simpa using this
    have hz := QuantumNLS.Local007Link.zero_char (r := r) (0 : L2T L) 0 (a 0 0) (b 0 0) hE hRs hκ.le
      ((a 0 0 : ℝ) : ℂ) hw
    have hD := hz.2 (Or.inl (by rw [hbn, hp0]; simp))
    rw [neg_zero, boost_zero_int] at hD
    refine free_zero (κ := κ) ?_ hD
    have : |a 0 0| < r := by simpa [Complex.norm_real] using hw
    exact lt_trans this hr2
  have hRa : AnalyticAt ℝ (QuantumNLS.Local007Rfun.Rfun c L Fh (a 0) (b 0)) 0 :=
    QuantumNLS.Local007Rfun.analyticAt_Rfun hc hFa hF0 ((hpk 0).1 0 h0ball) ((hpk 0).2.1 0 h0ball) ha0 hb0
  have hR0 : QuantumNLS.Local007Rfun.Rfun c L Fh (a 0) (b 0) 0 = 1 :=
    QuantumNLS.Local007Rfun.Rfun_zero hc hF0 ha0 hb0
  have hpm0 : QuantumNLS.LocalSpectral.pm L 0 = 0 := by simp [QuantumNLS.LocalSpectral.pm]
  have heven : ∀ v ∈ ball (0 : L2T L) (min ρ3 1),
      QuantumNLS.Local007Rfun.Rfun c L Fh (a 0) (b 0) (-v) = QuantumNLS.Local007Rfun.Rfun c L Fh (a 0) (b 0) v := by
    intro v hv
    have hvn : ‖v‖ < min ρ3 1 := by simpa using hv
    have hv3 : v ∈ ball (0 : L2T L) ρ3 := by simpa using lt_of_lt_of_le hvn (min_le_left _ _)
    have hv1 : ‖v‖ < 1 := lt_of_lt_of_le hvn (min_le_right _ _)
    have hnv3 : -v ∈ ball (0 : L2T L) ρ3 := by simpa using hv3
    obtain ⟨hE, h1, h2, hRs, -⟩ := (hpk 0).2.2.2.2.1 v hv3
    obtain ⟨hE', h1', h2', hRs', -⟩ := (hpk 0).2.2.2.2.1 (-v) hnv3
    have c1 := QuantumNLS.Local007Link.zero_char (r := r) v 0 (a 0 v) (b 0 v) hE hRs hκ.le
    have c2 := QuantumNLS.Local007Link.zero_char (r := r) (-v) 0 (a 0 (-v)) (b 0 (-v)) hE' hRs' hκ.le
    simp only [neg_zero, boost_zero_int] at c1 c2
    simp only [QuantumNLS.Local007Gauge.disc_neg] at c2
    have hα1 := abs_add_lt (norm_nonneg (b 0 v)) h1 h2
    have hα2 := abs_add_lt (norm_nonneg (b 0 (-v))) h1' h2'
    obtain ⟨hA, hT⟩ := QuantumNLS.Local007Link.params_unique (norm_nonneg _) (norm_nonneg _) hα1 hα2
      (P := fun w => QuantumNLS.L2SpatialTransfer.discriminant κ v w = 2) c1 c2
    have hA' : a 0 v = a 0 (-v) := by simpa [hpm0] using hA
    have hFeq : Fh (-v) = Fh v := by
      ext θ
      rw [hFh (-v) (by simpa using hv1) θ, hFh v hv1 θ]
      exact QuantumNLS.Local007Gauge.disc_neg κ v _
    unfold QuantumNLS.Local007Rfun.Rfun
    rw [hFeq, ← hA', ← hT]
  obtain ⟨ρb, hρb, Cb, hCb, hbd⟩ := QuantumNLS.Local007Lp.analytic_even_bounds hRa hR0
    (Filter.eventually_of_mem (ball_mem_nhds (0 : L2T L) (lt_min hρ3 one_pos)) heven)
  let T : ℤ → L2T L →L[ℝ] L2T L := fun n =>
    ((QuantumNLS.Local007Gauge.boostLI (L := L) (-n)).toContinuousLinearMap).restrictScalars ℝ
  have hT : ∀ n u, ‖T n u‖ ≤ ‖u‖ := fun n u => ((QuantumNLS.Local007Gauge.boostLI (L := L) (-n)).norm_map u).le
  obtain ⟨ρl, hρl, rr, hrr, hrrv⟩ := QuantumNLS.Local007Lp.lp_lift T hT hRa
  obtain ⟨ρm, hρm, hmass⟩ := QuantumNLS.Local007MassN.mass_n hκ hr hr2 hc Fh hFh
  set ρ : ℝ := min (min ρ3 1) (min (min ρl ρb) ρm) with hρ
  have hρpos : 0 < ρ := lt_min (lt_min hρ3 one_pos) (lt_min (lt_min hρl hρb) hρm)
  have hu_le : ∀ u : L2T L, u ∈ ball (0 : L2T L) ρ →
      ‖u‖ < ρ3 ∧ ‖u‖ < 1 ∧ ‖u‖ < ρl ∧ ‖u‖ < ρb ∧ ‖u‖ < ρm := by
    intro u hu
    have h : ‖u‖ < ρ := by simpa using hu
    exact ⟨lt_of_lt_of_le h ((min_le_left _ _).trans (min_le_left _ _)),
      lt_of_lt_of_le h ((min_le_left _ _).trans (min_le_right _ _)),
      lt_of_lt_of_le h ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))),
      lt_of_lt_of_le h ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))),
      lt_of_lt_of_le h ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hTn : ∀ n (u : L2T L), T n u = QuantumNLS.RootMassBoostSymbol.boost (-n) u := fun n u => rfl
  have hnorm : ∀ n (u : L2T L), ‖T n u‖ = ‖u‖ := fun n u => (QuantumNLS.Local007Gauge.boostLI (L := L) (-n)).norm_map u
  refine ⟨ρ, hρpos, max C3 Cb, le_max_of_le_left hC3, a, b, rr,
    fun n => (hpk n).mono (le_trans (min_le_left _ _) (min_le_left _ _)) (le_max_left _ _), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hrr.mono (ball_subset_ball (le_trans (min_le_right _ _) ((min_le_left _ _).trans (min_le_left _ _))))
  · intro u hu n
    obtain ⟨hu3', hu1, hul, hub, hum⟩ := hu_le u hu
    have hu3 : u ∈ ball (0 : L2T L) ρ3 := by simpa using hu3'
    have hul' : u ∈ ball (0 : L2T L) ρl := by simpa using hul
    set v : L2T L := QuantumNLS.RootMassBoostSymbol.boost (-n) u with hv
    have hvn : ‖v‖ = ‖u‖ := QuantumNLS.RootMassBoostSymbol.norm_boost _ _
    have hv3 : v ∈ ball (0 : L2T L) ρ3 := by rw [mem_ball_zero_iff, hvn]; exact hu3'
    obtain ⟨hE, h1, h2, hRs, -⟩ := (hpk n).2.2.2.2.1 u hu3
    obtain ⟨hE0, h10, h20, hRs0, -⟩ := (hpk 0).2.2.2.2.1 v hv3
    have cn := QuantumNLS.Local007Link.zero_char (r := r) u n (a n u) (b n u) hE hRs hκ.le
    have c0 := QuantumNLS.Local007Link.zero_char (r := r) v 0 (a 0 v) (b 0 v) hE0 hRs0 hκ.le
    simp only [neg_zero, boost_zero_int] at c0
    have hα1 := abs_add_lt (norm_nonneg (b n u)) h1 h2
    have hα2 := abs_add_lt (norm_nonneg (b 0 v)) h10 h20
    obtain ⟨hA, hT'⟩ := QuantumNLS.Local007Link.params_unique (norm_nonneg _) (norm_nonneg _) hα1 hα2
      (P := fun w => QuantumNLS.L2SpatialTransfer.discriminant κ v w = 2) cn c0
    have hA' : a 0 v = a n u - QuantumNLS.LocalSpectral.pm L n := by simpa [hpm0] using hA.symm
    have hm := hmass u hum n (a n u) (b n u) hE hRs h1 h2
    have hrv : rr u n = QuantumNLS.Local007Rfun.Rfun c L Fh (a 0) (b 0) v := hrrv u hul' n
    rw [hm, hrv, norm_mul, mul_pow, norm_gcoef_sq hκ]
    unfold QuantumNLS.Local007Rfun.Rfun
    rw [hA', ← hT']
    ring
  · intro u hu n
    obtain ⟨hu3', hu1, hul, hub, hum⟩ := hu_le u hu
    have hul' : u ∈ ball (0 : L2T L) ρl := by simpa using hul
    have hTb : T n u ∈ ball (0 : L2T L) ρb := by rw [mem_ball_zero_iff, hnorm]; exact hub
    rw [hrrv u hul' n]
    have := (hbd _ hTb).2.2.2
    rw [abs_lt] at this
    constructor <;> linarith [this.1, this.2]
  · ext n
    rw [hrrv 0 (mem_ball_self hρl) n, map_zero, hR0]
    rfl
  · intro u hu
    obtain ⟨hu3', hu1, hul, hub, hum⟩ := hu_le u hu
    have hul' : u ∈ ball (0 : L2T L) ρl := by simpa using hul
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun n => ?_
    have hTb : T n u ∈ ball (0 : L2T L) ρb := by rw [mem_ball_zero_iff, hnorm]; exact hub
    have h1 := (hbd _ hTb).2.1
    rw [hnorm] at h1
    change ‖rr u n - 1‖ ≤ _
    rw [hrrv u hul' n, Real.norm_eq_abs]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  · intro u hu
    obtain ⟨hu3', hu1, hul, hub, hum⟩ := hu_le u hu
    have hul' : u ∈ ball (0 : L2T L) ρl := by simpa using hul
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun n => ?_
    have hTb : T n u ∈ ball (0 : L2T L) ρb := by rw [mem_ball_zero_iff, hnorm]; exact hub
    have hd := (hbd _ hTb).1
    have hder := QuantumNLS.Local007Lp.lp_deriv T hT hrr hrrv hul' n hd h
    rw [hder, Real.norm_eq_abs]
    have h2 := (hbd _ hTb).2.2.1
    rw [hnorm] at h2
    calc |(fderiv ℝ (QuantumNLS.Local007Rfun.Rfun c L Fh (a 0) (b 0)) (T n u)) (T n h)|
        ≤ ‖fderiv ℝ (QuantumNLS.Local007Rfun.Rfun c L Fh (a 0) (b 0)) (T n u)‖ * ‖T n h‖ := by
          rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (Cb * ‖u‖) * ‖h‖ := mul_le_mul h2 (hT n h) (norm_nonneg _) (by positivity)
      _ ≤ (max C3 Cb * ‖u‖) * ‖h‖ := by gcongr; exact le_max_right _ _
      _ = max C3 Cb * ‖u‖ * ‖h‖ := by ring

  · intro u hu n
    obtain ⟨hu3', hu1, hul, hub, hum⟩ := hu_le u hu
    have hul' : u ∈ ball (0 : L2T L) ρl := by simpa using hul
    have hTl : T n u ∈ ball (0 : L2T L) ρl := by rw [mem_ball_zero_iff, hnorm]; exact hul
    show rr u n = (rr (T n u)) 0
    rw [hrrv u hul' n, hrrv (T n u) hTl 0]
    have : T 0 (T n u) = T n u := by
      show QuantumNLS.RootMassBoostSymbol.boost (-(0 : ℤ)) (T n u) = T n u
      rw [neg_zero]; exact boost_zero_int _
    rw [this]

end QuantumNLS.Local007Final
#print axioms QuantumNLS.Local007Final.reset_exact_factor_main

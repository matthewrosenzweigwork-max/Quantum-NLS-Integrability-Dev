import NlsGge.Hierarchy.ALLaurentFourier38
import NlsGge.Weights.Entire
import NlsGge.Definitions.PilotInterfaces

/-! # L02a (batch 38): the full lattice energy `E_{W,h}` of `D:thm:ALfinite`

Source: `paper/v2.tex` `D:eq:ALQ`, `D:eq:ALspectralmoment`, `D:eq:ALfullenergy` (l.1931-1977).
`alMomentK38` is `K_j` of `D:eq:Kj` (binomial form).  Its spectral form is proved here from the
κ Fourier identities of `ALLaurentFourier38` (name distinct from any `alK38` of L01).
The weight is `NlsGge.Weights.weight c` with `β_j = coefficient c j = c_j/(j!)^4`, for coefficients
in the coefficient class `lo ≤ c_j ≤ up` (`[1,2]` of v2 is the special case). -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open MeasureTheory Set Filter
open scoped ENNReal

/-! ### Elementary trigonometric binomial identity -/

theorem symm_sum_Icc38 (g : ℤ → ℝ) (j : ℕ) :
    ∑ k ∈ Finset.Icc (-(j:ℤ)) j, g k = g 0 + ∑ k ∈ Finset.Icc 1 j, (g k + g (-(k:ℤ))) := by
  induction j with
  | zero => simp
  | succ n ih =>
    have h1 : Finset.Icc (-((n+1:ℕ):ℤ)) ((n+1:ℕ):ℤ) =
        insert (-((n+1:ℕ):ℤ)) (insert ((n+1:ℕ):ℤ) (Finset.Icc (-(n:ℤ)) n)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [h1, Finset.sum_insert (by simp; try omega), Finset.sum_insert (by simp; try omega), ih,
      Finset.sum_Icc_succ_top (by omega)]
    push_cast; ring

theorem two_sub_cos38 (θ : ℝ) :
    ((2 - 2 * Real.cos (2 * θ) : ℝ) : ℂ) =
      -(Complex.exp (θ * Complex.I) - Complex.exp (-(θ * Complex.I))) ^ 2 := by
  have h : Complex.cos ((2 * θ : ℝ) : ℂ) =
      (Complex.exp (θ * Complex.I) ^ 2 + Complex.exp (-(θ * Complex.I)) ^ 2) / 2 := by
    rw [Complex.cos, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    push_cast; ring_nf
  have hm : Complex.exp (θ * Complex.I) * Complex.exp (-(θ * Complex.I)) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_cos, h]
  push_cast
  linear_combination (-2) * hm

theorem cosBinomC38 (j : ℕ) (θ : ℝ) :
    ((2 - 2 * Real.cos (2 * θ) : ℝ) : ℂ) ^ j = ∑ m ∈ Finset.range (2*j+1),
      (-1:ℂ) ^ (j + (2*j - m)) * (Nat.choose (2*j) m : ℂ) *
        Complex.exp (((2 * ((m:ℝ) - j) * θ : ℝ) : ℂ) * Complex.I) := by
  rw [two_sub_cos38, neg_pow, ← pow_mul, sub_eq_add_neg, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ 2 * j := by simpa [Nat.lt_succ_iff] using hm
  have e1 : Complex.exp (θ * Complex.I) ^ m = Complex.exp ((m * θ : ℝ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]; push_cast; ring_nf
  have e2 : (Complex.exp (-(θ * Complex.I))) ^ (2*j - m) =
      Complex.exp ((-((2*j - m : ℕ) * θ) : ℝ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]; push_cast; ring_nf
  have e3 : Complex.exp ((m * θ : ℝ) * Complex.I) *
      Complex.exp ((-((2*j - m : ℕ) * θ) : ℝ) * Complex.I)
      = Complex.exp (((2 * ((m:ℝ) - j) * θ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; rw [← add_mul, ← Complex.ofReal_add]; congr 2
    rw [Nat.cast_sub hm']; push_cast; ring
  rw [neg_pow (Complex.exp (-(θ * Complex.I))) (2*j-m), e1, e2, ← e3]
  have hs : (-1:ℂ) ^ (j + (2 * j - m)) = (-1) ^ j * (-1) ^ (2 * j - m) := pow_add _ _ _
  rw [hs]; ring

theorem cosBinomR38 (j : ℕ) (θ : ℝ) :
    (2 - 2 * Real.cos (2 * θ)) ^ j = ∑ m ∈ Finset.range (2*j+1),
      (-1:ℝ) ^ (j + (2*j - m)) * (Nat.choose (2*j) m : ℝ) * Real.cos (2 * ((m:ℝ) - j) * θ) := by
  have h := congrArg Complex.re (cosBinomC38 j θ)
  rw [← Complex.ofReal_pow, Complex.ofReal_re, Complex.re_sum] at h
  rw [h]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : ((-1:ℂ) ^ (j + (2*j - m)) * (Nat.choose (2*j) m : ℂ)) =
      (((-1:ℝ) ^ (j + (2*j - m)) * (Nat.choose (2*j) m : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- `(2 - 2cos 2θ)^j = C(2j,j) + 2 Σ_{k=1}^j (-1)^k C(2j,j-k) cos(2kθ)`
(the elementary Fourier expansion of `D:prop:ALmoments`). -/
theorem cosBinom38 (j : ℕ) (θ : ℝ) :
    (2 - 2 * Real.cos (2 * θ)) ^ j = (Nat.choose (2*j) j : ℝ) +
      2 * ∑ k ∈ Finset.Icc 1 j,
        (-1:ℝ) ^ k * (Nat.choose (2*j) (j-k) : ℝ) * Real.cos (2 * k * θ) := by
  rw [cosBinomR38]
  set g : ℤ → ℝ := fun k => (-1:ℝ) ^ k.natAbs * (Nat.choose (2*j) (j+k).toNat : ℝ) *
    Real.cos (2 * (k:ℝ) * θ) with hg
  have h1 : ∑ m ∈ Finset.range (2*j+1),
      (-1:ℝ) ^ (j + (2*j - m)) * (Nat.choose (2*j) m : ℝ) * Real.cos (2 * ((m:ℝ) - j) * θ) =
      ∑ k ∈ Finset.Icc (-(j:ℤ)) j, g k := by
    refine Finset.sum_nbij' (fun m => (m:ℤ) - j) (fun k => (j + k).toNat) ?_ ?_ ?_ ?_ ?_
    · intro m hm; simp only [Finset.mem_range] at hm; simp only [Finset.mem_Icc]; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_range]; omega
    · intro m hm; simp only [Finset.mem_range] at hm; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk; omega
    · intro m hm
      simp only [Finset.mem_range] at hm
      simp only [hg]
      have e1 : (-1:ℝ) ^ (j + (2*j - m)) = (-1:ℝ) ^ (((m:ℤ) - j).natAbs) := by
        rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := (((m:ℤ) - j).natAbs))]
        congr 1; omega
      have e2 : (j + ((m:ℤ) - j)).toNat = m := by omega
      rw [e1, e2]; push_cast; ring_nf
  rw [h1, symm_sum_Icc38, Finset.mul_sum]
  have g0 : g 0 = (Nat.choose (2*j) j : ℝ) := by simp [hg]
  rw [g0]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_Icc] at hk
  simp only [hg]
  have a1 : (j + (k:ℤ)).toNat = j + k := by omega
  have a2 : (j + (-(k:ℤ))).toNat = j - k := by omega
  have a3 : Nat.choose (2*j) (j+k) = Nat.choose (2*j) (j-k) := by
    rw [← Nat.choose_symm (show j + k ≤ 2*j by omega)]; congr 1; omega
  rw [a1, a2, a3]
  simp only [Int.natAbs_neg, Int.natAbs_natCast, Int.cast_natCast, Int.cast_neg, mul_neg, neg_mul,
    Real.cos_neg]
  ring

/-! ### The moments `K_j` (binomial form, `D:eq:Kj`) and their spectral form -/

variable {L : ℕ} [NeZero L]

/-- `K_j = C(2j,j) M_d + 2 Σ_{k=1}^j (-1)^k C(2j,j-k) Re C_k` (`D:eq:Kj`).  (Distinct name from
the L01 `alK38`; to be unified by the integrator.) -/
def alMomentK38 (α : ZMod L → ℂ) (j : ℕ) : ℝ :=
  (Nat.choose (2*j) j : ℝ) * alMass38 L α +
    2 * ∑ k ∈ Finset.Icc 1 j, (-1:ℝ) ^ k * (Nat.choose (2*j) (j-k) : ℝ) * (alC38 α k).re

/-- `D:eq:Kjpositive`: `K_j = (L/π) ∫_0^{2π} (2 - 2cos 2θ)^j κ(θ) dθ`. -/
theorem alMomentK38_spectral {α : ZMod L → ℂ} (hα : IsALField38 α) (j : ℕ) :
    alMomentK38 α j = (L / Real.pi) *
      ∫ θ in (0:ℝ)..(2 * Real.pi), (2 - 2 * Real.cos (2 * θ)) ^ j * alKappa38 α θ := by
  have hκ := continuous_alKappa38 hα
  have hpi := Real.pi_pos
  have hL : (0:ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have e : ∀ θ : ℝ, (2 - 2 * Real.cos (2 * θ)) ^ j * alKappa38 α θ =
      (Nat.choose (2*j) j : ℝ) * alKappa38 α θ +
      2 * ∑ k ∈ Finset.Icc 1 j, (-1:ℝ) ^ k * (Nat.choose (2*j) (j-k) : ℝ) *
        (alKappa38 α θ * Real.cos (2 * k * θ)) := by
    intro θ
    rw [cosBinom38, add_mul, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => by ring
  have hc : ∀ k : ℕ, Continuous fun θ : ℝ => alKappa38 α θ * Real.cos (2 * k * θ) :=
    fun k => hκ.mul (by fun_prop)
  have hsum : Continuous fun θ : ℝ => ∑ k ∈ Finset.Icc 1 j,
      (-1:ℝ) ^ k * (Nat.choose (2*j) (j-k) : ℝ) * (alKappa38 α θ * Real.cos (2 * k * θ)) :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (hc k)
  have hI : ∫ θ in (0:ℝ)..(2 * Real.pi), (2 - 2 * Real.cos (2 * θ)) ^ j * alKappa38 α θ =
      (Nat.choose (2*j) j : ℝ) * (∫ θ in (0:ℝ)..(2 * Real.pi), alKappa38 α θ) +
      2 * ∑ k ∈ Finset.Icc 1 j, (-1:ℝ) ^ k * (Nat.choose (2*j) (j-k) : ℝ) *
        (∫ θ in (0:ℝ)..(2 * Real.pi), alKappa38 α θ * Real.cos (2 * k * θ)) := by
    have i1 : IntervalIntegrable (fun θ : ℝ => (Nat.choose (2*j) j : ℝ) * alKappa38 α θ)
        volume 0 (2 * Real.pi) := (continuous_const.mul hκ).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun θ : ℝ => 2 * ∑ k ∈ Finset.Icc 1 j,
        (-1:ℝ) ^ k * (Nat.choose (2*j) (j-k) : ℝ) *
          (alKappa38 α θ * Real.cos (2 * k * θ))) volume 0 (2 * Real.pi) :=
      (continuous_const.mul hsum).intervalIntegrable _ _
    rw [intervalIntegral.integral_congr (fun θ _ => e θ),
      intervalIntegral.integral_add i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun k _ =>
        (show IntervalIntegrable (fun x : ℝ => (-1:ℝ) ^ k * (Nat.choose (2*j) (j-k) : ℝ) *
          (alKappa38 α x * Real.cos (2 * k * x))) volume 0 (2 * Real.pi) from
          (continuous_const.mul (hc k)).intervalIntegrable _ _))]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul]
  rw [hI, integral_alKappa38 hα, alMomentK38]
  have hk : ∀ k ∈ Finset.Icc 1 j, (-1:ℝ) ^ k * (Nat.choose (2*j) (j-k) : ℝ) *
      (∫ θ in (0:ℝ)..(2 * Real.pi), alKappa38 α θ * Real.cos (2 * k * θ)) =
      (L / Real.pi)⁻¹ * ((-1:ℝ) ^ k * (Nat.choose (2*j) (j-k) : ℝ) * (alC38 α k).re) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [integral_alKappa38_cos hα hk.1]
    field_simp
  rw [Finset.sum_congr rfl hk, ← Finset.mul_sum]
  field_simp

theorem two_sub_cos_nonneg38 (θ : ℝ) : 0 ≤ 2 - 2 * Real.cos (2 * θ) := by
  nlinarith [Real.cos_le_one (2 * θ)]

theorem two_sub_cos_le38 (θ : ℝ) : 2 - 2 * Real.cos (2 * θ) ≤ 4 := by
  nlinarith [Real.neg_one_le_cos (2 * θ)]

theorem alMomentK38_zero (α : ZMod L → ℂ) : alMomentK38 α 0 = alMass38 L α := by
  simp [alMomentK38]

theorem alMomentK38_nonneg {α : ZMod L → ℂ} (hα : IsALField38 α) (j : ℕ) :
    0 ≤ alMomentK38 α j := by
  rw [alMomentK38_spectral hα]
  have hL : (0:ℝ) ≤ L := Nat.cast_nonneg _
  refine mul_nonneg (div_nonneg hL Real.pi_pos.le) (intervalIntegral.integral_nonneg
    (by linarith [Real.pi_pos]) fun θ _ => mul_nonneg (pow_nonneg (two_sub_cos_nonneg38 θ) j)
      (alKappa38_nonneg α θ))

theorem alMass38_nonneg {α : ZMod L → ℂ} (hα : IsALField38 α) : 0 ≤ alMass38 L α := by
  rw [← alMomentK38_zero]; exact alMomentK38_nonneg hα 0

/-- `0 ≤ K_j ≤ 4^j M_d`, from `0 ≤ 2 - 2cos 2θ ≤ 4` and `D:eq:Kjpositive`. -/
theorem alMomentK38_le {α : ZMod L → ℂ} (hα : IsALField38 α) (j : ℕ) :
    alMomentK38 α j ≤ 4 ^ j * alMass38 L α := by
  have hκ := continuous_alKappa38 hα
  have hL : (0:ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hpi := Real.pi_pos
  rw [alMomentK38_spectral hα]
  have h1 : ∫ θ in (0:ℝ)..(2 * Real.pi), (2 - 2 * Real.cos (2 * θ)) ^ j * alKappa38 α θ ≤
      ∫ θ in (0:ℝ)..(2 * Real.pi), (4:ℝ) ^ j * alKappa38 α θ :=
    intervalIntegral.integral_mono_on (by linarith)
      ((by fun_prop : Continuous fun θ : ℝ => (2 - 2 * Real.cos (2 * θ)) ^ j * alKappa38 α θ).intervalIntegrable _ _)
      ((continuous_const.mul hκ : Continuous fun θ : ℝ => (4:ℝ) ^ j * alKappa38 α θ).intervalIntegrable _ _)
      fun θ _ => mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (two_sub_cos_nonneg38 θ) (two_sub_cos_le38 θ) j) (alKappa38_nonneg α θ)
  rw [intervalIntegral.integral_const_mul, integral_alKappa38 hα] at h1
  calc (L / Real.pi) * _ ≤ (L / Real.pi) * (4 ^ j * (Real.pi * alMass38 L α / L)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by field_simp

/-! ### `Q_{2j,h}`, `v_h` (`D:eq:ALQ`) and the spectral moment formula -/

/-- `Q_{2j,h} = h^{-2j-1} K_j`. -/
def alQ38 (h : ℝ) (α : ZMod L → ℂ) (j : ℕ) : ℝ := (h⁻¹) ^ (2 * j + 1) * alMomentK38 α j

/-- `v_h(λ) = h^{-1} κ(hλ)`. -/
def alVh38 (h : ℝ) (α : ZMod L → ℂ) (lam : ℝ) : ℝ := h⁻¹ * alKappa38 α (h * lam)

omit [NeZero L] in
theorem alVh38_nonneg (h : ℝ) (hh : 0 < h) (α : ZMod L → ℂ) (lam : ℝ) : 0 ≤ alVh38 h α lam :=
  mul_nonneg (inv_nonneg.2 hh.le) (alKappa38_nonneg α _)

theorem continuous_alVh38 {α : ZMod L → ℂ} (hα : IsALField38 α) (h : ℝ) :
    Continuous (alVh38 h α) :=
  continuous_const.mul ((continuous_alKappa38 hα).comp (continuous_const.mul continuous_id))

theorem alQ38_nonneg {α : ZMod L → ℂ} (hα : IsALField38 α) {h : ℝ} (hh : 0 < h) (j : ℕ) :
    0 ≤ alQ38 h α j :=
  mul_nonneg (pow_nonneg (inv_nonneg.2 hh.le) _) (alMomentK38_nonneg hα j)

/-- `Q_{2j,h} ≤ (2/h)^{2j} M_d / h` (spectral argument at most `2/h`). -/
theorem alQ38_le {α : ZMod L → ℂ} (hα : IsALField38 α) {h : ℝ} (hh : 0 < h) (j : ℕ) :
    alQ38 h α j ≤ (2 / h) ^ (2 * j) * (alMass38 L α / h) := by
  unfold alQ38
  calc (h⁻¹) ^ (2 * j + 1) * alMomentK38 α j
      ≤ (h⁻¹) ^ (2 * j + 1) * (4 ^ j * alMass38 L α) :=
        mul_le_mul_of_nonneg_left (alMomentK38_le hα j) (by positivity)
    _ = (2 / h) ^ (2 * j) * (alMass38 L α / h) := by
        have e : (2 / h) ^ (2 * j) = 4 ^ j * (h⁻¹) ^ (2 * j) := by
          rw [div_eq_mul_inv, mul_pow, pow_mul]; norm_num
        rw [e, pow_succ, div_eq_mul_inv]; ring

theorem alQ38_zero (α : ZMod L → ℂ) (h : ℝ) : alQ38 h α 0 = alMass38 L α / h := by
  simp [alQ38, alMomentK38_zero, div_eq_inv_mul]

theorem sin_sq_two38 (x : ℝ) : (2 * Real.sin x) ^ 2 = 2 - 2 * Real.cos (2 * x) := by
  rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq x]

/-- `D:eq:ALspectralmoment`: with `h = 1/L`, `L` odd,
`Q_{2j,h} = (2/π) ∫_{-π/(2h)}^{π/(2h)} (2 sin(hλ)/h)^{2j} v_h(λ) dλ`. -/
theorem alQ38_spectral {α : ZMod L → ℂ} (hα : IsALField38 α) (hodd : Odd L) {h : ℝ}
    (hh : h = (L:ℝ)⁻¹) (j : ℕ) :
    alQ38 h α j = (2 / Real.pi) *
      ∫ lam in (-(Real.pi / (2 * h)))..(Real.pi / (2 * h)),
        (2 * Real.sin (h * lam) / h) ^ (2 * j) * alVh38 h α lam := by
  have hL : (0:ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hpi := Real.pi_pos
  have hh0 : 0 < h := by rw [hh]; positivity
  have hne : h ≠ 0 := hh0.ne'
  set G : ℝ → ℝ := fun θ => (2 - 2 * Real.cos (2 * θ)) ^ j * alKappa38 α θ with hG
  have hGc : Continuous G := by
    have := continuous_alKappa38 hα
    simp only [hG]; fun_prop
  have hper : Function.Periodic G Real.pi := by
    intro θ
    simp only [hG]
    rw [alKappa38_add_pi_odd hodd, show 2 * (θ + Real.pi) = 2 * θ + 2 * Real.pi by ring,
      Real.cos_add_two_pi]
  -- pointwise rewriting of the integrand
  have hpt : ∀ lam : ℝ, (2 * Real.sin (h * lam) / h) ^ (2 * j) * alVh38 h α lam =
      (h⁻¹) ^ (2 * j + 1) * G (h * lam) := by
    intro lam
    simp only [hG, alVh38]
    rw [div_eq_mul_inv, mul_pow, pow_mul (2 * Real.sin (h * lam)), sin_sq_two38,
      pow_succ, pow_mul]
    ring
  have hsub : ∫ lam in (-(Real.pi / (2 * h)))..(Real.pi / (2 * h)), G (h * lam) =
      h⁻¹ * ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), G θ := by
    rw [intervalIntegral.integral_comp_mul_left (fun θ => G θ) hne]
    have e1 : h * (-(Real.pi / (2 * h))) = -(Real.pi / 2) := by field_simp
    have e2 : h * (Real.pi / (2 * h)) = Real.pi / 2 := by field_simp
    rw [e1, e2, smul_eq_mul]
  have hhalf : ∫ θ in (0:ℝ)..(2 * Real.pi), G θ = 2 * ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), G θ := by
    have a1 : ∫ x in (-(Real.pi / 2))..(-(Real.pi / 2) + Real.pi), G x = ∫ x in (0:ℝ)..(0 + Real.pi), G x :=
      hper.intervalIntegral_add_eq _ _
    have a2 : ∫ x in Real.pi..(Real.pi + Real.pi), G x = ∫ x in (0:ℝ)..(0 + Real.pi), G x :=
      hper.intervalIntegral_add_eq _ _
    have s1 : -(Real.pi / 2) + Real.pi = Real.pi / 2 := by ring
    have s2 : Real.pi + Real.pi = 2 * Real.pi := by ring
    rw [s1, zero_add] at a1
    rw [s2, zero_add] at a2
    rw [← intervalIntegral.integral_add_adjacent_intervals (hGc.intervalIntegrable 0 Real.pi)
      (hGc.intervalIntegrable Real.pi (2 * Real.pi)), a2, ← a1]
    ring
  have hK := alMomentK38_spectral hα j
  have hGK : ∫ θ in (0:ℝ)..(2 * Real.pi), G θ = Real.pi * h * alMomentK38 α j := by
    rw [hK]; simp only [hG]; rw [hh]; field_simp
  simp only [hpt]
  rw [intervalIntegral.integral_const_mul, hsub]
  have : ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), G θ = Real.pi * h * alMomentK38 α j / 2 := by
    linarith
  rw [this]
  unfold alQ38
  field_simp

/-! ### The full energy as the full charge series -/

section Energy

variable {lo up : ℝ} {c : ℕ → ℝ}

theorem coefficient_nonneg_of_class38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c)
    (j : ℕ) : 0 ≤ NlsGge.coefficient c j :=
  (NlsGge.Weights.coefficient_pos lo c hc.1 (fun i => (hc.2.2 i).1) j).le

/-- The `j`-th summand `β_j Q_{2j,h}` of `D:eq:ALfullenergy`, `β_j = c_j/(j!)^4`. -/
def alEnergyTerm38 (c : ℕ → ℝ) (h : ℝ) (α : ZMod L → ℂ) (j : ℕ) : ℝ :=
  NlsGge.coefficient c j * alQ38 h α j

theorem alEnergyTerm38_nonneg (hc : NlsGge.Pilot.AdmittedCoefficients lo up c)
    {α : ZMod L → ℂ} (hα : IsALField38 α) {h : ℝ} (hh : 0 < h) (j : ℕ) :
    0 ≤ alEnergyTerm38 c h α j :=
  mul_nonneg (coefficient_nonneg_of_class38 hc j) (alQ38_nonneg hα hh j)

theorem alEnergyTerm38_le (hc : NlsGge.Pilot.AdmittedCoefficients lo up c)
    {α : ZMod L → ℂ} (hα : IsALField38 α) {h : ℝ} (hh : 0 < h) (j : ℕ) :
    alEnergyTerm38 c h α j ≤ NlsGge.weightTerm c (2 / h) j * (alMass38 L α / h) := by
  unfold alEnergyTerm38 NlsGge.weightTerm
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (alQ38_le hα hh j) (coefficient_nonneg_of_class38 hc j)

/-- Summability is proved first (nonnegative terms, majorised by the entire weight series). -/
theorem alEnergy38_summable (hc : NlsGge.Pilot.AdmittedCoefficients lo up c)
    {α : ZMod L → ℂ} (hα : IsALField38 α) {h : ℝ} (hh : 0 < h) :
    Summable (alEnergyTerm38 c h α) :=
  ((NlsGge.Weights.weightTerm_summable lo up c hc.1 (fun i => (hc.2.2 i).1) (fun i => (hc.2.2 i).2)
    (2 / h)).mul_right (alMass38 L α / h)).of_nonneg_of_le
    (alEnergyTerm38_nonneg hc hα hh) (alEnergyTerm38_le hc hα hh)

/-- The finite energy `E_{W,h}(α) = Σ_j β_j Q_{2j,h}(α)` (real value; summability above). -/
def alEnergy38 (c : ℕ → ℝ) (h : ℝ) (α : ZMod L → ℂ) : ℝ := ∑' j, alEnergyTerm38 c h α j

/-- The same series as a nonnegative extended-real sum (the genuine energy, possibly `∞`). -/
def alEnergyENN38 (c : ℕ → ℝ) (h : ℝ) (α : ZMod L → ℂ) : ℝ≥0∞ :=
  ∑' j, ENNReal.ofReal (alEnergyTerm38 c h α j)

theorem alEnergyENN38_eq (hc : NlsGge.Pilot.AdmittedCoefficients lo up c)
    {α : ZMod L → ℂ} (hα : IsALField38 α) {h : ℝ} (hh : 0 < h) :
    alEnergyENN38 c h α = ENNReal.ofReal (alEnergy38 c h α) :=
  (ENNReal.ofReal_tsum_of_nonneg (alEnergyTerm38_nonneg hc hα hh)
    (alEnergy38_summable hc hα hh)).symm

theorem alEnergyENN38_lt_top (hc : NlsGge.Pilot.AdmittedCoefficients lo up c)
    {α : ZMod L → ℂ} (hα : IsALField38 α) {h : ℝ} (hh : 0 < h) :
    alEnergyENN38 c h α < ⊤ := by
  rw [alEnergyENN38_eq hc hα hh]; exact ENNReal.ofReal_lt_top

theorem alEnergy38_nonneg (hc : NlsGge.Pilot.AdmittedCoefficients lo up c)
    {α : ZMod L → ℂ} (hα : IsALField38 α) {h : ℝ} (hh : 0 < h) : 0 ≤ alEnergy38 c h α :=
  tsum_nonneg (alEnergyTerm38_nonneg hc hα hh)

/-- Sandwich of `D:thm:ALfinite`: `β₀ M_d / h ≤ E_{W,h} ≤ W(2/h) M_d / h`,
`β₀ = c₀`, `W = NlsGge.Weights.weight c`. -/
theorem alEnergy38_sandwich (hc : NlsGge.Pilot.AdmittedCoefficients lo up c)
    {α : ZMod L → ℂ} (hα : IsALField38 α) {h : ℝ} (hh : 0 < h) :
    c 0 * alMass38 L α / h ≤ alEnergy38 c h α ∧
    alEnergy38 c h α ≤ NlsGge.Weights.weight c (2 / h) * alMass38 L α / h := by
  constructor
  · have := (alEnergy38_summable hc hα hh).le_tsum 0 (fun j _ => alEnergyTerm38_nonneg hc hα hh j)
    have e : alEnergyTerm38 c h α 0 = c 0 * alMass38 L α / h := by
      simp [alEnergyTerm38, alQ38_zero, mul_div_assoc]
    rw [← e]; exact this
  · have hw := (NlsGge.Weights.weightTerm_summable lo up c hc.1 (fun i => (hc.2.2 i).1)
      (fun i => (hc.2.2 i).2) (2 / h)).mul_right (alMass38 L α / h)
    calc alEnergy38 c h α ≤ ∑' j, NlsGge.weightTerm c (2 / h) j * (alMass38 L α / h) :=
          (alEnergy38_summable hc hα hh).tsum_le_tsum (alEnergyTerm38_le hc hα hh) hw
      _ = _ := by
          rw [tsum_mul_right]; unfold NlsGge.Weights.weight; ring

end Energy

section EnergySpectral

variable {lo up : ℝ} {c : ℕ → ℝ}

/-- `D:eq:ALfullenergy`: for `h = 1/L`, `L` odd,
`E_{W,h} = (2/π) ∫_{B_h} W(2 sin(hλ)/h) v_h(λ) dλ`, by termwise integration of a nonnegative
series with summable integrals (`D:eq:ALspectralmoment`). -/
theorem alEnergy38_spectral (hc : NlsGge.Pilot.AdmittedCoefficients lo up c)
    {α : ZMod L → ℂ} (hα : IsALField38 α) (hodd : Odd L) {h : ℝ} (hh : h = (L:ℝ)⁻¹) :
    alEnergy38 c h α = (2 / Real.pi) *
      ∫ lam in (-(Real.pi / (2 * h)))..(Real.pi / (2 * h)),
        NlsGge.Weights.weight c (2 * Real.sin (h * lam) / h) * alVh38 h α lam := by
  have hL : (0:ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hpi := Real.pi_pos
  have hh0 : 0 < h := by rw [hh]; positivity
  have hab : -(Real.pi / (2 * h)) ≤ Real.pi / (2 * h) := by
    have : 0 ≤ Real.pi / (2 * h) := by positivity
    linarith
  set a := -(Real.pi / (2 * h)) with ha
  set b := Real.pi / (2 * h) with hb
  have hV := continuous_alVh38 hα h
  set F : ℕ → ℝ → ℝ := fun j lam =>
    NlsGge.weightTerm c (2 * Real.sin (h * lam) / h) j * alVh38 h α lam with hF
  have hFc : ∀ j, Continuous (F j) := fun j => by
    simp only [hF, NlsGge.weightTerm, NlsGge.coefficient]
    have : Continuous fun lam : ℝ => 2 * Real.sin (h * lam) / h := by fun_prop
    exact (continuous_const.mul (this.pow _)).mul hV
  have hF0 : ∀ j lam, 0 ≤ F j lam := fun j lam =>
    mul_nonneg (NlsGge.Weights.weightTerm_nonneg lo c hc.1 (fun i => (hc.2.2 i).1) _ j)
      (alVh38_nonneg h hh0 α lam)
  have hFint : ∀ j, ∫ lam in a..b, F j lam = (Real.pi / 2) * alEnergyTerm38 c h α j := by
    intro j
    have e := alQ38_spectral hα hodd hh j
    have e2 : ∀ lam, F j lam = NlsGge.coefficient c j *
        ((2 * Real.sin (h * lam) / h) ^ (2 * j) * alVh38 h α lam) := by
      intro lam; simp only [hF, NlsGge.weightTerm]; ring
    rw [intervalIntegral.integral_congr (fun lam _ => e2 lam), intervalIntegral.integral_const_mul,
      ← ha, ← hb] at *
    unfold alEnergyTerm38
    rw [e]; field_simp
  have hnorm : ∀ j, ∫ lam in Ioc a b, ‖F j lam‖ = (Real.pi / 2) * alEnergyTerm38 c h α j := by
    intro j
    have : ∀ lam, ‖F j lam‖ = F j lam := fun lam => by rw [Real.norm_of_nonneg (hF0 j lam)]
    simp_rw [this]
    rw [← intervalIntegral.integral_of_le hab]; exact hFint j
  have hsum : Summable fun j => ∫ lam in Ioc a b, ‖F j lam‖ := by
    simp_rw [hnorm]; exact (alEnergy38_summable hc hα hh0).mul_left _
  have hint : ∀ j, Integrable (F j) (volume.restrict (Ioc a b)) := fun j =>
    (hFc j).integrableOn_Ioc
  have key := integral_tsum_of_summable_integral_norm hint hsum
  have h1 : ∀ lam, ∑' j, F j lam =
      NlsGge.Weights.weight c (2 * Real.sin (h * lam) / h) * alVh38 h α lam := by
    intro lam; simp only [hF, NlsGge.Weights.weight]; rw [tsum_mul_right]
  have h2 : ∫ lam in a..b, NlsGge.Weights.weight c (2 * Real.sin (h * lam) / h) * alVh38 h α lam
      = (Real.pi / 2) * alEnergy38 c h α := by
    rw [intervalIntegral.integral_of_le hab]
    simp_rw [← h1]
    rw [← key]
    have hIoc : ∀ j, ∫ lam in Ioc a b, F j lam = (Real.pi / 2) * alEnergyTerm38 c h α j :=
      fun j => by rw [← intervalIntegral.integral_of_le hab]; exact hFint j
    simp_rw [hIoc]
    rw [tsum_mul_left]; rfl
  rw [h2]; field_simp

end EnergySpectral

/-- Summary of the energy part of `D:thm:ALfinite` (finiteness of `E_{W,h}` as an extended-real
series, its real value, the spectral formula and the sandwich), for `h = 1/L`, `L` odd. -/
theorem alFullEnergy_finite38 {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {α : ZMod L → ℂ} (hα : IsALField38 α)
    (hodd : Odd L) {h : ℝ} (hh : h = (L:ℝ)⁻¹) :
    alEnergyENN38 c h α < ⊤ ∧ alEnergyENN38 c h α = ENNReal.ofReal (alEnergy38 c h α) ∧
    alEnergy38 c h α = (2 / Real.pi) *
      ∫ lam in (-(Real.pi / (2 * h)))..(Real.pi / (2 * h)),
        NlsGge.Weights.weight c (2 * Real.sin (h * lam) / h) * alVh38 h α lam ∧
    (c 0 * alMass38 L α / h ≤ alEnergy38 c h α ∧
      alEnergy38 c h α ≤ NlsGge.Weights.weight c (2 / h) * alMass38 L α / h) := by
  have hh0 : 0 < h := by
    rw [hh]; have : (0:ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  exact ⟨alEnergyENN38_lt_top hc hα hh0, alEnergyENN38_eq hc hα hh0,
    alEnergy38_spectral hc hα hodd hh, alEnergy38_sandwich hc hα hh0⟩

end NlsGge.AblowitzLadik
end

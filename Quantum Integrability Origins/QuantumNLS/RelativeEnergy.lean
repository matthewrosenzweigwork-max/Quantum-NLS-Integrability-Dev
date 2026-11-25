import QuantumNLS.ChargeEnergy

/-!
# ENERGY-006 `lem:A1-relative` (source `energy_prepared/cubic_charge.tex`, subsection
"A relative energy on the space of rays"): coercive and structural clauses

Source objects, formalised literally on `𝕋_L = AddCircle L` (mass-`L` Lebesgue measure, DEF-001):
* `E(u) = I_3(u) + I_1(u) = ‖u_x‖₂² + ‖u‖₂² + κ‖u‖₄⁴` (`eq:A1-E`): `Efun κ = energyH1 κ + I1`,
  reusing the frozen `ChargeEnergy.energyH1` for `I_3` and `I1 f = ∫|f|²`; `Efun_eq_charge`
  proves `I_3 + I_1 = E` against the DEF-022 charges on smooth profiles.
* `dE(q)[h] = d/dt|₀ E(q + t h)` (`dE`, real directional derivative; `dE_eq` computes it:
  `2 Re Σ(1+p²) conj(q̂) ĥ + 4κ ∫|q|² Re(q̄ h)`).
* `α = ⟨v,u⟩`, `q = αv`, `w = u − q`, `F_v(u) = E(u) − E(q) − dE(q)[w]` (`eq:A1-projection`:
  `alpha`, `projF`, `wF`, `Fv`), `S_v(u) = E(u) − F_v(u)` (`Sv`).

Proved (no placeholder proofs, no custom axioms):
* `ip_wF`, `I1_wF`: `⟨v,w⟩ = 0`, `1 − |α|² = ‖w‖₂²` (unit `u,v`);
  `Fv_phase_v`, `Fv_phase_u`: `F_v(u)` unchanged by a constant phase of `v` or `u`.
* `Fv_coercive_general`, `energy006_A1_relative` (2.): `F_v(u) ≥ ‖w‖²_{H¹} + (κ/3)‖w‖₄⁴`
  (`eq:A1-coercive`), via the exact Bregman expansion `bregman_eq` and the pointwise identity
  `|q+w|⁴ − |q|⁴ − 4|q|²Re(q̄w) = 6(r+|w|²/3)² + 2s² + |w|⁴/3` (as the inequality
  `4r²+2|q|²|w|²+4r|w|²+(2/3)|w|⁴ ≥ 0`, `r² ≤ |q|²|w|²`).
* `Sv_explicit` (`eq:A1-S`): `S_v(u) = 2Re(ᾱ⟨ℓ,u⟩) − |α|²E₂(v) + 4κ|α|²Re(ᾱ⟨r_v,u⟩) − 3κ|α|⁴V₄(v)`,
  `ℓ = (1−∂²)v`, `r_v = |v|²v`; `Sv_structure`: `S_v(u) = a_{J₂}(u) + a_{J₄}(u)` with the printed
  rank-one operator `J₂ = |v⟩⟨ℓ|+|ℓ⟩⟨v|−E₂(v)|v⟩⟨v|` and rank-two operator
  `J₄ = 2κ(|v^{⊗2}⟩⟨z|+|z⟩⟨v^{⊗2}|) − 3κV₄(v)|v^{⊗2}⟩⟨v^{⊗2}|`, `z = Sym(v⊗r_v)`;
  smooth data (`J2_smooth`, `J4_smooth`), selfadjoint kernels (`J2_herm`, `J4_herm`), gauge
  invariance and degree-`2`/`4` homogeneity of `a_J` (`FR1.poly_gauge`, `FR1.poly_smul`, …).

NOT formalised here (listed in the review record): the transport clause `eq:A1-transport` of the same
lemma (flow `X`, time-dependent smooth solution `v(t)`, `(∂_t + d_u[X(u)])S_{v(t)}(u) ≤ C F`) and
its proof (`eq:A1-R` … `eq:A1-relative-identity`, final `H¹`-approximation).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ComplexConjugate ContDiff
open MeasureTheory QuantumNLS.Fourier QuantumNLS.WeakDerivatives QuantumNLS.ClassicalCharges
  QuantumNLS.ChargeEnergy

noncomputable section

namespace QuantumNLS.RelativeEnergy

variable {L : ℝ}

/-! ## Part 1: the objects `E`, `dE`, `α`, `q`, `w`, `F_v`, `S_v` on `𝕋_L` -/

section Defs

variable [Fact (0 < L)]

/-- The `L²(𝕋_L)` inner product, linear in the second slot (DEF-001). -/
def ip (f g : AddCircle L → ℂ) : ℂ := ∫ x, conj (f x) * g x ∂(volume : Measure (AddCircle L))

/-- The mass `I_1(f) = ‖f‖₂² = ∫ |f|²`. -/
def I1 (f : AddCircle L → ℂ) : ℝ := ∫ x, ‖f x‖ ^ 2 ∂(volume : Measure (AddCircle L))

/-- `E(u) = I_3(u) + I_1(u) = ‖u_x‖₂² + ‖u‖₂² + κ‖u‖₄⁴` (`eq:A1-E`) on `H¹(𝕋_L)`, with
`I_3 = energyH1` (the frozen `ChargeEnergy` extension) and `I_1 = ‖·‖₂²`. -/
def Efun (κ : ℝ) (f : AddCircle L → ℂ) : ℝ := energyH1 κ f + I1 f

/-- The line `t ↦ q + t h` (real `t`). -/
def lineF (q h : AddCircle L → ℂ) (t : ℝ) : AddCircle L → ℂ := fun x => q x + (t : ℂ) * h x

/-- The real directional derivative `dE(q)[h] = d/dt|_{t=0} E(q + t h)`. -/
def dE (κ : ℝ) (q h : AddCircle L → ℂ) : ℝ :=
  deriv (fun t : ℝ => Efun κ (lineF q h t)) 0

/-- `α = ⟨v,u⟩`. -/
def alpha (v u : AddCircle L → ℂ) : ℂ := ip v u

/-- `q = α v`. -/
def projF (v u : AddCircle L → ℂ) : AddCircle L → ℂ := fun x => alpha v u * v x

/-- `w = u − q`. -/
def wF (v u : AddCircle L → ℂ) : AddCircle L → ℂ := fun x => u x - alpha v u * v x

/-- `F_v(u) = E(u) − E(q) − dE(q)[w]` (`eq:A1-projection`). -/
def Fv (κ : ℝ) (v u : AddCircle L → ℂ) : ℝ :=
  Efun κ u - Efun κ (projF v u) - dE κ (projF v u) (wF v u)

/-- `S_v(u) = E(u) − F_v(u)`. -/
def Sv (κ : ℝ) (v u : AddCircle L → ℂ) : ℝ := Efun κ u - Fv κ v u

/-- The sequence-level `H¹` sesquilinear form `Σ (1+p_n²) conj(a_n) b_n`. -/
def ip1 (L : ℝ) (a b : ℤ → ℂ) : ℂ :=
  ∑' n : ℤ, ((f04Weight L 1 n : ℝ) : ℂ) * (conj (a n) * b n)

theorem summable_ip1 {a b : ℤ → ℂ} (ha : Mem04 L 1 a) (hb : Mem04 L 1 b) :
    Summable fun n : ℤ => ((f04Weight L 1 n : ℝ) : ℂ) * (conj (a n) * b n) := by
  refine Summable.of_norm_bounded (g := fun n => f04Weight L 1 n * ‖a n‖ ^ 2 +
    f04Weight L 1 n * ‖b n‖ ^ 2) (ha.add hb) (fun n => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, RCLike.norm_conj,
    Real.norm_of_nonneg (f04Weight_pos L 1 n).le]
  have hw := (f04Weight_pos L 1 n).le
  have h1 := norm_nonneg (a n)
  have h2 := norm_nonneg (b n)
  nlinarith [sq_nonneg (‖a n‖ - ‖b n‖), mul_nonneg hw (sq_nonneg (‖a n‖ - ‖b n‖))]

theorem mem04_smul {b : ℤ → ℂ} (hb : Mem04 L 1 b) (t : ℝ) : Mem04 L 1 (fun n => (t : ℂ) * b n) := by
  unfold Mem04 at *
  have := hb.mul_left (t ^ 2)
  refine this.congr (fun n => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]; ring

theorem f04NormSq_line {a b : ℤ → ℂ} (ha : Mem04 L 1 a) (hb : Mem04 L 1 b) (t : ℝ) :
    f04NormSq L 1 (fun n => a n + (t : ℂ) * b n) =
      f04NormSq L 1 a + 2 * t * (ip1 L a b).re + t ^ 2 * f04NormSq L 1 b := by
  have hs := summable_ip1 ha hb
  have hre : Summable fun n : ℤ => (((f04Weight L 1 n : ℝ) : ℂ) * (conj (a n) * b n)).re :=
    (Complex.hasSum_re hs.hasSum).summable
  have key : ∀ n : ℤ, f04Weight L 1 n * ‖a n + (t : ℂ) * b n‖ ^ 2 =
      f04Weight L 1 n * ‖a n‖ ^ 2 +
        (2 * t) * (((f04Weight L 1 n : ℝ) : ℂ) * (conj (a n) * b n)).re +
        t ^ 2 * (f04Weight L 1 n * ‖b n‖ ^ 2) := by
    intro n
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  unfold f04NormSq
  simp_rw [key]
  rw [Summable.tsum_add ((ha.add (hre.mul_left (2 * t))).congr (fun n => by ring)) (hb.mul_left (t ^ 2)),
    Summable.tsum_add ha (hre.mul_left (2 * t)), tsum_mul_left, tsum_mul_left]
  have : (ip1 L a b).re = ∑' n : ℤ, (((f04Weight L 1 n : ℝ) : ℂ) * (conj (a n) * b n)).re :=
    ((Complex.hasSum_re hs.hasSum).tsum_eq).symm
  rw [this]

theorem h04_line {q h : AddCircle L → ℂ} (hq : H04 L 1 q) (hh : H04 L 1 h) (t : ℝ) :
    H04 L 1 (lineF q h t) ∧
      coeff L (lineF q h t) = fun n => coeff L q n + (t : ℂ) * coeff L h n := by
  have hco : coeff L (lineF q h t) = fun n => coeff L q n + (t : ℂ) * coeff L h n := by
    funext n
    unfold lineF
    rw [coeff_add L (integrable_of_h04 hq.1) ((integrable_of_h04 hh.1).const_mul (t : ℂ)) n,
      coeff_const_mul]
  refine ⟨⟨hq.1.add (hh.1.const_smul (t : ℂ)), ?_⟩, hco⟩
  rw [hco]
  exact (mem04_le_add (c := fun n => coeff L q n + (t : ℂ) * coeff L h n) hq.2
    (mem04_smul hh.2 t) (fun n => by simpa using norm_add_le (coeff L q n) ((t : ℂ) * coeff L h n))).1

/-- `‖f‖²_{H¹} = ‖f_x‖₂² + ‖f‖₂²` on `H¹` (Fourier form). -/
theorem f04NormSq_eq {f : AddCircle L → ℂ} (hf : H04 L 1 f) :
    f04NormSq L 1 (coeff L f) = kinetic f + I1 f := by
  have hI : I1 f = ∑' n : ℤ, ‖coeff L f n‖ ^ 2 := (tsum_sq_coeff L hf.1).symm
  have h1 : Summable fun n : ℤ => ‖coeff L f n‖ ^ 2 := (hasSum_sq_coeff L hf.1).summable
  have h2 : Summable fun n : ℤ => freq L n ^ 2 * ‖coeff L f n‖ ^ 2 := by
    have := kin_summable hf.2
    rwa [kin_eq] at this
  unfold kinetic
  rw [hI, ← Summable.tsum_add h2 h1]
  unfold f04NormSq
  exact tsum_congr (fun n => by rw [f04Weight_one]; ring)

/-- `E = ‖·‖²_{H¹} + κ‖·‖₄⁴` on `H¹`. -/
theorem efun_eq (κ : ℝ) {f : AddCircle L → ℂ} (hf : H04 L 1 f) :
    Efun κ f = f04NormSq L 1 (coeff L f) + κ * quartic f := by
  rw [f04NormSq_eq hf]
  unfold Efun energyH1
  ring

end Defs

/-! ## Part 1b: exact expansion of `E` along a line, the derivative `dE`, and the Bregman identity -/

section Quartic

variable [Fact (0 < L)]

/-- `r = Re(q̄ h)`. -/
def rr (q h : AddCircle L → ℂ) (x : AddCircle L) : ℝ := (conj (q x) * h x).re

def qc1 (q h : AddCircle L → ℂ) (x : AddCircle L) : ℝ := 4 * ‖q x‖ ^ 2 * rr q h x
def qc2 (q h : AddCircle L → ℂ) (x : AddCircle L) : ℝ :=
  4 * rr q h x ^ 2 + 2 * ‖q x‖ ^ 2 * ‖h x‖ ^ 2
def qc3 (q h : AddCircle L → ℂ) (x : AddCircle L) : ℝ := 4 * rr q h x * ‖h x‖ ^ 2
def qc4 (_q h : AddCircle L → ℂ) (x : AddCircle L) : ℝ := ‖h x‖ ^ 4

def A1 (q h : AddCircle L → ℂ) : ℝ := ∫ x, qc1 q h x ∂(volume : Measure (AddCircle L))
def A2 (q h : AddCircle L → ℂ) : ℝ := ∫ x, qc2 q h x ∂(volume : Measure (AddCircle L))
def A3 (q h : AddCircle L → ℂ) : ℝ := ∫ x, qc3 q h x ∂(volume : Measure (AddCircle L))
def A4 (q h : AddCircle L → ℂ) : ℝ := ∫ x, qc4 q h x ∂(volume : Measure (AddCircle L))

theorem A4_eq (q h : AddCircle L → ℂ) : A4 q h = quartic h := rfl

theorem norm_pow4_eq (z : ℂ) : ‖z‖ ^ 4 = (z.re * z.re + z.im * z.im) ^ 2 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.sq_norm, Complex.normSq_apply]

/-- Pointwise expansion `|q + t h|⁴ = |q|⁴ + t c₁ + t² c₂ + t³ c₃ + t⁴ c₄`. -/
theorem pow4_line (q h : ℂ) (t : ℝ) :
    ‖q + (t : ℂ) * h‖ ^ 4 = ‖q‖ ^ 4 + t * (4 * ‖q‖ ^ 2 * (conj q * h).re) +
      t ^ 2 * (4 * (conj q * h).re ^ 2 + 2 * ‖q‖ ^ 2 * ‖h‖ ^ 2) +
      t ^ 3 * (4 * (conj q * h).re * ‖h‖ ^ 2) + t ^ 4 * ‖h‖ ^ 4 := by
  rw [norm_pow4_eq, norm_pow4_eq, norm_pow4_eq, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem rr_sq_le (q h : ℂ) : (conj q * h).re ^ 2 ≤ ‖q‖ ^ 2 * ‖h‖ ^ 2 := by
  have h1 : |(conj q * h).re| ≤ ‖q‖ * ‖h‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, RCLike.norm_conj]
  have h2 := sq_le_sq' (neg_le_of_abs_le h1) (le_of_abs_le h1)
  nlinarith [h2]

theorem abs_rr_le (q h : ℂ) : |(conj q * h).re| ≤ ‖q‖ * ‖h‖ := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, RCLike.norm_conj]

theorem integrable_qc {q h : AddCircle L → ℂ} (hq : H04 L 1 q) (hh : H04 L 1 h) :
    Integrable (qc1 q h) (volume : Measure (AddCircle L)) ∧
    Integrable (qc2 q h) (volume : Measure (AddCircle L)) ∧
    Integrable (qc3 q h) (volume : Measure (AddCircle L)) ∧
    Integrable (qc4 q h) (volume : Measure (AddCircle L)) := by
  have hqm : AEStronglyMeasurable q (volume : Measure (AddCircle L)) := hq.1.aestronglyMeasurable
  have hhm : AEStronglyMeasurable h (volume : Measure (AddCircle L)) := hh.1.aestronglyMeasurable
  have hrm : AEStronglyMeasurable (rr q h) (volume : Measure (AddCircle L)) :=
    Complex.continuous_re.comp_aestronglyMeasurable
      ((Complex.continuous_conj.comp_aestronglyMeasurable hqm).mul hhm)
  have hqn : AEStronglyMeasurable (fun x => ‖q x‖) (volume : Measure (AddCircle L)) := hqm.norm
  have hhn : AEStronglyMeasurable (fun x => ‖h x‖) (volume : Measure (AddCircle L)) := hhm.norm
  set A := cL L * h04Norm L 1 q
  set B := cL L * h04Norm L 1 h
  have bq := ae_norm_le hq
  have bh := ae_norm_le hh
  have hpt : ∀ᵐ x ∂(volume : Measure (AddCircle L)),
      ‖q x‖ ≤ A ∧ ‖h x‖ ≤ B := by
    filter_upwards [bq, bh] with x h1 h2 using ⟨h1, h2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Integrable.of_bound (C := 4 * A ^ 2 * (A * B)) ?_ ?_
    · exact ((hqn.pow 2).const_mul 4).mul hrm
    · filter_upwards [hpt] with x ⟨h1, h2⟩
      have a0 := norm_nonneg (q x)
      have b0 := norm_nonneg (h x)
      have A0 : 0 ≤ A := a0.trans h1
      have B0 : 0 ≤ B := b0.trans h2
      have hr := abs_rr_le (q x) (h x)
      unfold qc1 rr
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4),
        abs_of_nonneg (by positivity : 0 ≤ ‖q x‖ ^ 2)]
      have : |(conj (q x) * h x).re| ≤ A * B :=
        hr.trans (mul_le_mul h1 h2 b0 (a0.trans h1))
      gcongr
  · refine Integrable.of_bound (C := 4 * (A * B) ^ 2 + 2 * A ^ 2 * B ^ 2) ?_ ?_
    · exact (((hrm.pow 2).const_mul 4).add (((hqn.pow 2).const_mul 2).mul (hhn.pow 2)))
    · filter_upwards [hpt] with x ⟨h1, h2⟩
      have a0 := norm_nonneg (q x)
      have b0 := norm_nonneg (h x)
      have A0 : 0 ≤ A := a0.trans h1
      have B0 : 0 ≤ B := b0.trans h2
      have hr := abs_rr_le (q x) (h x)
      have hr' : |(conj (q x) * h x).re| ≤ A * B :=
        hr.trans (mul_le_mul h1 h2 b0 (a0.trans h1))
      have hr2 : rr q h x ^ 2 ≤ (A * B) ^ 2 := by
        unfold rr; exact sq_le_sq' (neg_le_of_abs_le hr') (le_of_abs_le hr')
      unfold qc2
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr
  · refine Integrable.of_bound (C := 4 * (A * B) * B ^ 2) ?_ ?_
    · exact ((hrm.const_mul 4).mul (hhn.pow 2))
    · filter_upwards [hpt] with x ⟨h1, h2⟩
      have a0 := norm_nonneg (q x)
      have b0 := norm_nonneg (h x)
      have A0 : 0 ≤ A := a0.trans h1
      have B0 : 0 ≤ B := b0.trans h2
      have hr := abs_rr_le (q x) (h x)
      have hr' : |(conj (q x) * h x).re| ≤ A * B :=
        hr.trans (mul_le_mul h1 h2 b0 (a0.trans h1))
      unfold qc3 rr
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4),
        abs_of_nonneg (by positivity : 0 ≤ ‖h x‖ ^ 2)]
      gcongr
  · exact quartic_integrable hh

theorem quartic_line {q h : AddCircle L → ℂ} (hq : H04 L 1 q) (hh : H04 L 1 h) (t : ℝ) :
    quartic (lineF q h t) =
      quartic q + t * A1 q h + t ^ 2 * A2 q h + t ^ 3 * A3 q h + t ^ 4 * A4 q h := by
  obtain ⟨i1, i2, i3, i4⟩ := integrable_qc hq hh
  have i0 := quartic_integrable hq
  have hfun : (fun x => ‖lineF q h t x‖ ^ 4) = fun x => ‖q x‖ ^ 4 + t * qc1 q h x +
      t ^ 2 * qc2 q h x + t ^ 3 * qc3 q h x + t ^ 4 * qc4 q h x := by
    funext x
    unfold lineF qc1 qc2 qc3 qc4 rr
    exact pow4_line (q x) (h x) t
  unfold quartic
  rw [hfun]
  have j1 := i1.const_mul t
  have j2 := i2.const_mul (t ^ 2)
  have j3 := i3.const_mul (t ^ 3)
  have j4 := i4.const_mul (t ^ 4)
  have k1 : Integrable (fun x => ‖q x‖ ^ 4 + t * qc1 q h x) (volume : Measure (AddCircle L)) :=
    i0.add j1
  have k2 : Integrable (fun x => ‖q x‖ ^ 4 + t * qc1 q h x + t ^ 2 * qc2 q h x)
      (volume : Measure (AddCircle L)) := k1.add j2
  have k3 : Integrable (fun x => ‖q x‖ ^ 4 + t * qc1 q h x + t ^ 2 * qc2 q h x +
      t ^ 3 * qc3 q h x) (volume : Measure (AddCircle L)) := k2.add j3
  rw [integral_add k3 j4, integral_add k2 j3, integral_add k1 j2, integral_add i0 j1,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  rfl

theorem efun_line (κ : ℝ) {q h : AddCircle L → ℂ} (hq : H04 L 1 q) (hh : H04 L 1 h) (t : ℝ) :
    Efun κ (lineF q h t) =
      Efun κ q + t * (2 * (ip1 L (coeff L q) (coeff L h)).re + κ * A1 q h) +
        t ^ 2 * (f04NormSq L 1 (coeff L h) + κ * A2 q h) + t ^ 3 * (κ * A3 q h) +
        t ^ 4 * (κ * A4 q h) := by
  obtain ⟨hl, hco⟩ := h04_line hq hh t
  rw [efun_eq κ hl, efun_eq κ hq, hco, f04NormSq_line hq.2 hh.2 t, quartic_line hq hh t]
  ring

theorem dE_eq (κ : ℝ) {q h : AddCircle L → ℂ} (hq : H04 L 1 q) (hh : H04 L 1 h) :
    dE κ q h = 2 * (ip1 L (coeff L q) (coeff L h)).re + κ * A1 q h := by
  unfold dE
  set c0 := Efun κ q
  set D1 := 2 * (ip1 L (coeff L q) (coeff L h)).re + κ * A1 q h
  set D2 := f04NormSq L 1 (coeff L h) + κ * A2 q h
  set D3 := κ * A3 q h
  set D4 := κ * A4 q h
  have hfun : (fun t : ℝ => Efun κ (lineF q h t)) =
      fun t : ℝ => c0 + t * D1 + t ^ 2 * D2 + t ^ 3 * D3 + t ^ 4 * D4 :=
    funext fun t => efun_line κ hq hh t
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => t * D1) D1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const D1
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 * D2) 0 0 := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ)).mul_const D2
  have h3 : HasDerivAt (fun t : ℝ => t ^ 3 * D3) 0 0 := by
    simpa using (hasDerivAt_pow 3 (0 : ℝ)).mul_const D3
  have h4 : HasDerivAt (fun t : ℝ => t ^ 4 * D4) 0 0 := by
    simpa using (hasDerivAt_pow 4 (0 : ℝ)).mul_const D4
  have hd : HasDerivAt (fun t : ℝ => c0 + t * D1 + t ^ 2 * D2 + t ^ 3 * D3 + t ^ 4 * D4)
      (0 + D1 + 0 + 0 + 0) 0 :=
    ((((hasDerivAt_const (0 : ℝ) c0).add h1).add h2).add h3).add h4
  rw [hd.deriv]; ring

/-- **Bregman identity**: for `H¹` fields `q, w`,
`E(q + w) − E(q) − dE(q)[w] = ‖w‖²_{H¹} + κ (A₂ + A₃ + A₄)`. -/
theorem bregman_eq (κ : ℝ) {q w : AddCircle L → ℂ} (hq : H04 L 1 q) (hw : H04 L 1 w) :
    Efun κ (fun x => q x + w x) - Efun κ q - dE κ q w =
      f04NormSq L 1 (coeff L w) + κ * (A2 q w + A3 q w + A4 q w) := by
  have e := efun_line κ hq hw 1
  have hl : lineF q w 1 = fun x => q x + w x := by funext x; simp [lineF]
  rw [hl] at e
  rw [dE_eq κ hq hw]
  simp only [one_mul, one_pow] at e
  linarith

/-- **`eq:A1-coercive`, general form.**  For `H¹` fields `q, w` and `κ ≥ 0`,
`E(q+w) − E(q) − dE(q)[w] ≥ ‖w‖²_{H¹} + (κ/3)‖w‖₄⁴`. -/
theorem bregman_ge {κ : ℝ} (hκ : 0 ≤ κ) {q w : AddCircle L → ℂ} (hq : H04 L 1 q) (hw : H04 L 1 w) :
    f04NormSq L 1 (coeff L w) + κ / 3 * quartic w ≤
      Efun κ (fun x => q x + w x) - Efun κ q - dE κ q w := by
  rw [bregman_eq κ hq hw]
  obtain ⟨i1, i2, i3, i4⟩ := integrable_qc hq hw
  have hnn : 0 ≤ ∫ x, (qc2 q w x + qc3 q w x + (2 / 3) * qc4 q w x)
      ∂(volume : Measure (AddCircle L)) := by
    refine integral_nonneg (fun x => ?_)
    have h1 := rr_sq_le (q x) (w x)
    show (0 : ℝ) ≤ qc2 q w x + qc3 q w x + (2 / 3) * qc4 q w x
    unfold qc2 qc3 qc4 rr
    have e4 : ‖w x‖ ^ 4 = (‖w x‖ ^ 2) ^ 2 := by ring
    rw [e4]
    nlinarith [h1, sq_nonneg ((conj (q x) * w x).re + ‖w x‖ ^ 2 / 3)]
  have k : Integrable (fun x => qc2 q w x + qc3 q w x) (volume : Measure (AddCircle L)) := i2.add i3
  have k4 := i4.const_mul (2 / 3)
  have hI : ∫ x, (qc2 q w x + qc3 q w x + (2 / 3) * qc4 q w x)
      ∂(volume : Measure (AddCircle L)) = A2 q w + A3 q w + 2 / 3 * A4 q w := by
    rw [integral_add k k4, integral_add i2 i3, integral_const_mul]; rfl
  rw [hI] at hnn
  have h4 : A4 q w = quartic w := rfl
  have := mul_nonneg hκ hnn
  rw [h4] at hnn this ⊢
  nlinarith [this]

end Quartic

/-! ## Part 2: smooth profiles, Parseval for the inner product, and the `H¹` pairing with `(1−∂²)v` -/

section Smooth

variable [Fact (0 < L)]

/-- The torus field of a smooth periodic profile. -/
def lift {v : ℝ → ℂ} (hv : SmoothPeriodic L v) : AddCircle L → ℂ :=
  (liftC hv.smooth.continuous hv.periodic : AddCircle L → ℂ)

theorem lift_coe {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (x : ℝ) :
    lift hv (x : AddCircle L) = v x := liftC_coe hv.smooth.continuous hv.periodic x

theorem continuous_lift {v : ℝ → ℂ} (hv : SmoothPeriodic L v) : Continuous (lift hv) :=
  (liftC hv.smooth.continuous hv.periodic).continuous

theorem sp_deriv {v : ℝ → ℂ} (hv : SmoothPeriodic L v) :
    SmoothPeriodic L (deriv v) :=
  ⟨(contDiff_infty_iff_deriv.mp hv.smooth).2, periodic_deriv hv.periodic⟩

theorem integrable_conj_mul {f g : AddCircle L → ℂ} (hf : MemLp f 2 (volume : Measure (AddCircle L)))
    (hg : MemLp g 2 (volume : Measure (AddCircle L))) :
    Integrable (fun x => conj (f x) * g x) (volume : Measure (AddCircle L)) := by
  have := (hf.star).integrable_mul hg
  exact this

/-- **Parseval for the inner product**: `⟨f,g⟩ = Σ conj(f̂(n)) ĝ(n)`. -/
theorem hasSum_ip {f g : AddCircle L → ℂ} (hf : MemLp f 2 (volume : Measure (AddCircle L)))
    (hg : MemLp g 2 (volume : Measure (AddCircle L))) :
    HasSum (fun n : ℤ => conj (coeff L f n) * coeff L g n) (ip f g) := by
  set F : Lp ℂ 2 (volume : Measure (AddCircle L)) := hf.toLp f with hFd
  set G : Lp ℂ 2 (volume : Measure (AddCircle L)) := hg.toLp g with hGd
  have h1 := lp.hasSum_inner (𝕜 := ℂ) (fourierL2 L F) (fourierL2 L G)
  rw [LinearIsometryEquiv.inner_map_map, MeasureTheory.L2.inner_def] at h1
  have e1 : ∫ a, inner ℂ ((F : AddCircle L → ℂ) a) ((G : AddCircle L → ℂ) a)
      ∂(volume : Measure (AddCircle L)) = ip f g := by
    unfold ip
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    rw [hFd, hGd] at *
    simp only [hx, hy, RCLike.inner_apply]
    ring
  rw [e1] at h1
  convert h1 using 2 with n
  rw [fourierL2_apply, fourierL2_apply, coeff_congr_ae L hf.coeFn_toLp,
    coeff_congr_ae L hg.coeFn_toLp]
  simp only [RCLike.inner_apply]
  ring

theorem ip_eq_tsum {f g : AddCircle L → ℂ} (hf : MemLp f 2 (volume : Measure (AddCircle L)))
    (hg : MemLp g 2 (volume : Measure (AddCircle L))) :
    ip f g = ∑' n : ℤ, conj (coeff L f n) * coeff L g n := (hasSum_ip hf hg).tsum_eq.symm

end Smooth

/-! ## Part 3: the vectors `ℓ = (1−∂²)v`, `r_v = |v|²v`, and the pairing `⟨g,u⟩ = ∫₀^L ḡ u` -/

section Vectors

variable [Fact (0 < L)]

/-- `ℓ = (1 − ∂ₓ²) v`. -/
def lvec (v : ℝ → ℂ) : ℝ → ℂ := fun x => v x - deriv (deriv v) x

/-- `r_v = |v|² v`. -/
def rvec (v : ℝ → ℂ) : ℝ → ℂ := fun x => ((‖v x‖ ^ 2 : ℝ) : ℂ) * v x

theorem sp_lvec {v : ℝ → ℂ} (hv : SmoothPeriodic L v) : SmoothPeriodic L (lvec v) :=
  ⟨hv.smooth.sub (sp_deriv (sp_deriv hv)).smooth, fun x => by
    simp only [lvec]
    rw [hv.periodic x, (sp_deriv (sp_deriv hv)).periodic x]⟩

theorem sp_rvec {v : ℝ → ℂ} (hv : SmoothPeriodic L v) : SmoothPeriodic L (rvec v) :=
  ⟨(Complex.ofRealCLM.contDiff.comp ((contDiff_norm_sq ℝ).comp hv.smooth)).mul hv.smooth,
    fun x => by simp only [rvec]; rw [hv.periodic x]⟩

/-- The pairing `⟨g, u⟩ = ∫₀^L conj(g(x)) u(x) dx` of a profile on `ℝ` with a torus field. -/
def pair1 (g : ℝ → ℂ) (u : AddCircle L → ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..L, conj (g x) * u (x : AddCircle L)

theorem pair1_eq_ip {g : ℝ → ℂ} (hg : SmoothPeriodic L g) (u : AddCircle L → ℂ) :
    pair1 g u = ip (lift hg) u := by
  unfold pair1 ip
  have := AddCircle.intervalIntegral_preimage L 0 (fun a : AddCircle L => conj (lift hg a) * u a)
  rw [zero_add] at this
  rw [← this]
  exact intervalIntegral.integral_congr (fun x _ => by simp only [lift_coe])

theorem coeff_lvec {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (n : ℤ) :
    coeff L (lift (sp_lvec hv)) n = ((1 + freq L n ^ 2 : ℝ) : ℂ) * coeff L (lift hv) n := by
  have hfun : lift (sp_lvec hv) = fun a => lift hv a - lift (sp_deriv (sp_deriv hv)) a := by
    funext a
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
    simp only [lift_coe, lvec]
  have i1 : Integrable (lift hv) (volume : Measure (AddCircle L)) :=
    integrable_of_h04 (memLp_of_continuous (continuous_lift hv))
  have i2 : Integrable (lift (sp_deriv (sp_deriv hv))) (volume : Measure (AddCircle L)) :=
    integrable_of_h04 (memLp_of_continuous (continuous_lift _))
  rw [hfun, coeff_sub_integrable i1 i2 n]
  have e2 : coeff L (lift (sp_deriv (sp_deriv hv))) n = ikn L n * coeff L (lift (sp_deriv hv)) n :=
    coeff_deriv (sp_deriv hv) n
  have e1 : coeff L (lift (sp_deriv hv)) n = ikn L n * coeff L (lift hv) n := coeff_deriv hv n
  rw [e2, e1]
  have : ikn L n * ikn L n = -((freq L n : ℝ) : ℂ) ^ 2 := by
    unfold ikn
    rw [mul_mul_mul_comm, Complex.I_mul_I]; ring
  push_cast
  linear_combination (-(coeff L (lift hv) n)) * this

/-- The `H¹` form against a smooth `v` is the `L²` pairing against `ℓ = (1−∂²)v`:
`Σ (1+p_n²) conj(v̂_n) û_n = ⟨ℓ, u⟩`. -/
theorem ip1_eq_ip_lvec {v : ℝ → ℂ} (hv : SmoothPeriodic L v) {u : AddCircle L → ℂ}
    (hu : H04 L 1 u) :
    ip1 L (coeff L (lift hv)) (coeff L u) = ip (lift (sp_lvec hv)) u := by
  rw [ip_eq_tsum (memLp_of_continuous (continuous_lift _)) hu.1]
  unfold ip1
  refine tsum_congr (fun n => ?_)
  rw [coeff_lvec hv n, map_mul, Complex.conj_ofReal, f04Weight_one]
  ring

end Vectors

/-! ## Part 4: the explicit polynomial form of `S_v` (`eq:A1-S`) -/

section Explicit

variable [Fact (0 < L)]

theorem h04Norm_sq (f : AddCircle L → ℂ) : h04Norm L 1 f ^ 2 = f04NormSq L 1 (coeff L f) := by
  unfold h04Norm
  exact Real.sq_sqrt (tsum_nonneg fun n => mul_nonneg (f04Weight_pos L 1 n).le (sq_nonneg _))

theorem h04_cmul {f : AddCircle L → ℂ} (hf : H04 L 1 f) (c : ℂ) :
    H04 L 1 (fun x => c * f x) ∧
      coeff L (fun x => c * f x) = fun n => c * coeff L f n := by
  have hco : coeff L (fun x => c * f x) = fun n => c * coeff L f n :=
    funext fun n => coeff_const_mul L c f n
  refine ⟨⟨hf.1.const_smul c, ?_⟩, hco⟩
  rw [hco]
  unfold Mem04
  refine (hf.2.mul_left (‖c‖ ^ 2)).congr (fun n => ?_)
  rw [norm_mul, mul_pow]; ring

theorem f04NormSq_cmul (c : ℂ) (a : ℤ → ℂ) :
    f04NormSq L 1 (fun n => c * a n) = ‖c‖ ^ 2 * f04NormSq L 1 a := by
  unfold f04NormSq
  rw [← tsum_mul_left]
  exact tsum_congr (fun n => by rw [norm_mul, mul_pow]; ring)

theorem quartic_cmul (c : ℂ) (f : AddCircle L → ℂ) :
    quartic (fun x => c * f x) = ‖c‖ ^ 4 * quartic f := by
  unfold quartic
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp only [norm_mul, mul_pow])

theorem efun_cmul (κ : ℝ) {f : AddCircle L → ℂ} (hf : H04 L 1 f) (c : ℂ) :
    Efun κ (fun x => c * f x) =
      ‖c‖ ^ 2 * f04NormSq L 1 (coeff L f) + κ * (‖c‖ ^ 4 * quartic f) := by
  obtain ⟨hc, hco⟩ := h04_cmul hf c
  rw [efun_eq κ hc, hco, f04NormSq_cmul, quartic_cmul]

theorem ip1_cmul_left (c : ℂ) (a b : ℤ → ℂ) :
    ip1 L (fun n => c * a n) b = conj c * ip1 L a b := by
  unfold ip1
  rw [← tsum_mul_left]
  exact tsum_congr (fun n => by rw [map_mul]; ring)

theorem ip1_self (a : ℤ → ℂ) : ip1 L a a = ((f04NormSq L 1 a : ℝ) : ℂ) := by
  unfold ip1 f04NormSq
  rw [Complex.ofReal_tsum]
  exact tsum_congr (fun n => by
    rw [show conj (a n) * a n = ((‖a n‖ ^ 2 : ℝ) : ℂ) by
      rw [Complex.conj_mul']; push_cast; rfl]
    push_cast; ring)

theorem ip1_sub_cmul {a b : ℤ → ℂ} (ha : Mem04 L 1 a) (hb : Mem04 L 1 b) (c : ℂ) :
    ip1 L a (fun n => b n - c * a n) = ip1 L a b - c * ip1 L a a := by
  unfold ip1
  have s1 := summable_ip1 ha hb
  have s2 := (summable_ip1 ha ha).mul_left c
  rw [← tsum_mul_left, ← Summable.tsum_sub s1 s2]
  exact tsum_congr (fun n => by ring)

theorem lift_rvec {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (a : AddCircle L) :
    lift (sp_rvec hv) a = ((‖lift hv a‖ ^ 2 : ℝ) : ℂ) * lift hv a := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
  simp only [lift_coe, rvec]

theorem h04_lift {v : ℝ → ℂ} (hv : SmoothPeriodic L v) : H04 L 1 (lift hv) := smooth_h04 hv

/-- **`eq:A1-S`.**  For a smooth profile `v` and `u ∈ H¹`, with `α = ⟨v,u⟩`,
`S_v(u) = 2 Re(ᾱ⟨ℓ,u⟩) − |α|² E₂(v) + 4κ|α|² Re(ᾱ⟨r_v,u⟩) − 3κ|α|⁴ V₄(v)`,
`ℓ = (1−∂²)v`, `r_v = |v|²v`, `E₂(v) = ‖v‖²_{H¹}`, `V₄(v) = ‖v‖₄⁴`. -/
theorem Sv_explicit (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) {u : AddCircle L → ℂ}
    (hu : H04 L 1 u) :
    Sv κ (lift hv) u =
      2 * (conj (alpha (lift hv) u) * pair1 (lvec v) u).re
        - ‖alpha (lift hv) u‖ ^ 2 * h04Norm L 1 (lift hv) ^ 2
        + 4 * κ * ‖alpha (lift hv) u‖ ^ 2 * (conj (alpha (lift hv) u) * pair1 (rvec v) u).re
        - 3 * κ * ‖alpha (lift hv) u‖ ^ 4 * quartic (lift hv) := by
  set α := alpha (lift hv) u with hα
  have hvH : H04 L 1 (lift hv) := h04_lift hv
  obtain ⟨hq, hqco⟩ := h04_cmul hvH α
  have hq' : H04 L 1 (projF (lift hv) u) := hq
  obtain ⟨hw, hwco⟩ := h04_sub hu hq
  have hw' : H04 L 1 (wF (lift hv) u) := hw
  -- S = E(q) + dE(q)[w]
  have hS : Sv κ (lift hv) u = Efun κ (projF (lift hv) u) + dE κ (projF (lift hv) u) (wF (lift hv) u) := by
    unfold Sv Fv; ring
  have hE : Efun κ (projF (lift hv) u) =
      ‖α‖ ^ 2 * f04NormSq L 1 (coeff L (lift hv)) + κ * (‖α‖ ^ 4 * quartic (lift hv)) :=
    efun_cmul κ hvH α
  have hdE := dE_eq κ hq' hw'
  -- the quadratic part
  have hcq : coeff L (projF (lift hv) u) = fun n => α * coeff L (lift hv) n := hqco
  have hcw : coeff L (wF (lift hv) u) = fun n => coeff L u n - α * coeff L (lift hv) n := by
    have := hwco
    rw [hqco] at this
    exact this
  have hip : ip1 L (coeff L (projF (lift hv) u)) (coeff L (wF (lift hv) u)) =
      conj α * (pair1 (lvec v) u - α * ((f04NormSq L 1 (coeff L (lift hv)) : ℝ) : ℂ)) := by
    rw [hcq, hcw, ip1_cmul_left, ip1_sub_cmul hvH.2 hu.2, ip1_self, ip1_eq_ip_lvec hv hu,
      pair1_eq_ip (sp_lvec hv)]
  have hre : (ip1 L (coeff L (projF (lift hv) u)) (coeff L (wF (lift hv) u))).re =
      (conj α * pair1 (lvec v) u).re - ‖α‖ ^ 2 * f04NormSq L 1 (coeff L (lift hv)) := by
    rw [hip, mul_sub, Complex.sub_re]
    congr 1
    have : conj α * (α * ((f04NormSq L 1 (coeff L (lift hv)) : ℝ) : ℂ)) =
        ((‖α‖ ^ 2 * f04NormSq L 1 (coeff L (lift hv)) : ℝ) : ℂ) := by
      rw [← mul_assoc, Complex.conj_mul']; push_cast; ring
    rw [this, Complex.ofReal_re]
  -- the quartic part
  have hA1 : A1 (projF (lift hv) u) (wF (lift hv) u) =
      4 * ‖α‖ ^ 2 * ((conj α * pair1 (rvec v) u).re - ‖α‖ ^ 2 * quartic (lift hv)) := by
    have hrF : MemLp (lift (sp_rvec hv)) 2 (volume : Measure (AddCircle L)) :=
      memLp_of_continuous (continuous_lift _)
    have hint : Integrable (fun x => conj α * (conj (lift (sp_rvec hv) x) * u x))
        (volume : Measure (AddCircle L)) := (integrable_conj_mul hrF hu.1).const_mul _
    have hpt : ∀ x : AddCircle L, qc1 (projF (lift hv) u) (wF (lift hv) u) x =
        4 * ‖α‖ ^ 2 * ((conj α * (conj (lift (sp_rvec hv) x) * u x)).re
          - ‖α‖ ^ 2 * ‖lift hv x‖ ^ 4) := by
      intro x
      set V := lift hv x
      set U := u x
      have e1 : conj (α * V) * (U - α * V) =
          conj α * (conj V * U) - (((‖α‖ ^ 2 * ‖V‖ ^ 2 : ℝ)) : ℂ) := by
        have h1 : conj α * α = ((‖α‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.conj_mul']; push_cast; rfl
        have h2 : conj V * V = ((‖V‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.conj_mul']; push_cast; rfl
        have h3 : (((‖α‖ ^ 2 * ‖V‖ ^ 2 : ℝ)) : ℂ) = (conj α * α) * (conj V * V) := by
          rw [Complex.ofReal_mul, h1, h2]
        rw [h3, map_mul]; ring
      have e2 : conj α * (conj (lift (sp_rvec hv) x) * U) =
          ((‖V‖ ^ 2 : ℝ) : ℂ) * (conj α * (conj V * U)) := by
        rw [lift_rvec hv x, map_mul, Complex.conj_ofReal]; ring
      unfold qc1 rr projF wF
      rw [e1, e2, Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul, norm_mul, mul_pow]
      ring
    have hq4 : Integrable (fun x : AddCircle L => ‖lift hv x‖ ^ 4) (volume : Measure (AddCircle L)) :=
      quartic_integrable hvH
    have hre' : Integrable (fun x => (conj α * (conj (lift (sp_rvec hv) x) * u x)).re)
        (volume : Measure (AddCircle L)) := hint.re
    unfold A1
    simp_rw [hpt]
    rw [integral_const_mul, integral_sub hre' (hq4.const_mul _), integral_const_mul]
    have e3 : ∫ x, (conj α * (conj (lift (sp_rvec hv) x) * u x)).re
        ∂(volume : Measure (AddCircle L)) = (conj α * pair1 (rvec v) u).re := by
      have := integral_re hint
      simp only [RCLike.re_to_complex] at this
      rw [this, integral_const_mul, pair1_eq_ip (sp_rvec hv)]
      rfl
    rw [e3]
    rfl
  rw [hS, hE, hdE, hre, hA1]
  have hn : h04Norm L 1 (lift hv) ^ 2 = f04NormSq L 1 (coeff L (lift hv)) := h04Norm_sq _
  rw [hn]
  ring

end Explicit

/-! ## Part 5: finite-rank polynomials `a_J(u) = ⟨u^{⊗k}, J u^{⊗k}⟩`, `k = 1, 2` -/

section FiniteRank

variable [Fact (0 < L)]

/-- A smooth function on `𝕋_L²`, as an `L`-periodic (in each variable) `C^∞` function on `ℝ²`. -/
structure SmoothPeriodic2 (L : ℝ) (F : ℝ → ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ (Function.uncurry F)
  per1 : ∀ x y, F (x + L) y = F x y
  per2 : ∀ x y, F x (y + L) = F x y

/-- A finite-rank operator on `L²(𝕋_L)` in normal form `J = Σ_r c_r |f_r⟩⟨g_r|`, `c_r` real,
`f_r, g_r` profiles on `ℝ`.  Its kernel is `Σ c_r f_r(x) conj(g_r(x'))`. -/
structure FR1 where
  n : ℕ
  c : Fin n → ℝ
  f : Fin n → ℝ → ℂ
  g : Fin n → ℝ → ℂ

/-- A finite-rank operator on `L²(𝕋_L²)`, `J = Σ_r c_r |f_r⟩⟨g_r|`, `f_r, g_r` functions on `ℝ²`. -/
structure FR2 where
  n : ℕ
  c : Fin n → ℝ
  f : Fin n → ℝ → ℝ → ℂ
  g : Fin n → ℝ → ℝ → ℂ

/-- Smooth kernel: every vector is a smooth periodic profile. -/
def FR1.IsSmooth (L : ℝ) (J : FR1) : Prop := ∀ r, SmoothPeriodic L (J.f r) ∧ SmoothPeriodic L (J.g r)

def FR2.IsSmooth (L : ℝ) (J : FR2) : Prop :=
  ∀ r, SmoothPeriodic2 L (J.f r) ∧ SmoothPeriodic2 L (J.g r)

/-- The kernel `K(x,x') = Σ c_r f_r(x) conj(g_r(x'))`. -/
def FR1.kernel (J : FR1) (x x' : ℝ) : ℂ :=
  ∑ r, ((J.c r : ℝ) : ℂ) * (J.f r x * conj (J.g r x'))

def FR2.kernel (J : FR2) (x y x' y' : ℝ) : ℂ :=
  ∑ r, ((J.c r : ℝ) : ℂ) * (J.f r x y * conj (J.g r x' y'))

/-- Selfadjointness of the operator, in kernel form `K(x,x') = conj K(x',x)`. -/
def FR1.Herm (J : FR1) : Prop := ∀ x x', J.kernel x x' = conj (J.kernel x' x)

def FR2.Herm (J : FR2) : Prop := ∀ x y x' y', J.kernel x y x' y' = conj (J.kernel x' y' x y)

/-- The pairing `⟨G, u ⊗ u⟩ = ∫₀^L∫₀^L conj(G(x,y)) u(x) u(y) dy dx`. -/
def pair2 (G : ℝ → ℝ → ℂ) (u : AddCircle L → ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..L, ∫ y in (0 : ℝ)..L, conj (G x y) * (u (x : AddCircle L) * u (y : AddCircle L))

/-- The degree-two polynomial `a_J(u) = ⟨u, J u⟩ = Σ c_r conj⟨f_r,u⟩ ⟨g_r,u⟩`. -/
def FR1.poly (J : FR1) (u : AddCircle L → ℂ) : ℂ :=
  ∑ r, ((J.c r : ℝ) : ℂ) * (conj (pair1 (J.f r) u) * pair1 (J.g r) u)

/-- The degree-four polynomial `a_J(u) = ⟨u⊗u, J u⊗u⟩ = Σ c_r conj⟨f_r,u⊗u⟩ ⟨g_r,u⊗u⟩`. -/
def FR2.poly (J : FR2) (u : AddCircle L → ℂ) : ℂ :=
  ∑ r, ((J.c r : ℝ) : ℂ) * (conj (pair2 (J.f r) u) * pair2 (J.g r) u)

theorem pair1_smul (g : ℝ → ℂ) (u : AddCircle L → ℂ) (z : ℂ) :
    pair1 g (fun x => z * u x) = z * pair1 g u := by
  unfold pair1
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr (fun x _ => by ring)

theorem pair2_smul (G : ℝ → ℝ → ℂ) (u : AddCircle L → ℂ) (z : ℂ) :
    pair2 G (fun x => z * u x) = z ^ 2 * pair2 G u := by
  unfold pair2
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr (fun y _ => by ring)

theorem FR1.poly_smul (J : FR1) (u : AddCircle L → ℂ) (z : ℂ) :
    J.poly (fun x => z * u x) = ((‖z‖ ^ 2 : ℝ) : ℂ) * J.poly u := by
  unfold FR1.poly
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [pair1_smul, pair1_smul, map_mul]
  have : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.conj_mul']; push_cast; rfl
  rw [← this]; ring

theorem FR2.poly_smul (J : FR2) (u : AddCircle L → ℂ) (z : ℂ) :
    J.poly (fun x => z * u x) = ((‖z‖ ^ 4 : ℝ) : ℂ) * J.poly u := by
  unfold FR2.poly
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [pair2_smul, pair2_smul, map_mul, map_pow]
  have : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.conj_mul']; push_cast; rfl
  have h4 : ((‖z‖ ^ 4 : ℝ) : ℂ) = (conj z * z) ^ 2 := by rw [this]; push_cast; ring
  rw [h4]; ring

/-- Gauge invariance: `a_J(e^{iθ} u) = a_J(u)` (any unimodular constant). -/
theorem FR1.poly_gauge (J : FR1) (u : AddCircle L → ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    J.poly (fun x => z * u x) = J.poly u := by
  rw [J.poly_smul, hz]; simp

theorem FR2.poly_gauge (J : FR2) (u : AddCircle L → ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    J.poly (fun x => z * u x) = J.poly u := by
  rw [J.poly_smul, hz]; simp

theorem intervalIntegrable_coe {u : AddCircle L → ℂ} (hu : Integrable u (volume : Measure (AddCircle L))) :
    IntervalIntegrable (fun x : ℝ => u (x : AddCircle L)) volume 0 L := by
  have hL : 0 < L := Fact.out
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le]
  have := (AddCircle.measurePreserving_mk L 0).integrable_comp_of_integrable hu
  rw [zero_add] at this
  exact this

theorem intervalIntegrable_pair {g : ℝ → ℂ} (hg : Continuous g) {u : AddCircle L → ℂ}
    (hu : MemLp u 2 (volume : Measure (AddCircle L))) :
    IntervalIntegrable (fun x : ℝ => conj (g x) * u (x : AddCircle L)) volume 0 L :=
  (intervalIntegrable_coe (integrable_of_h04 hu)).continuousOn_mul
    (Complex.continuous_conj.comp hg).continuousOn

theorem pair2_sep {a b : ℝ → ℂ} (u : AddCircle L → ℂ) :
    pair2 (fun x y => a x * b y) u = pair1 a u * pair1 b u := by
  unfold pair2 pair1
  have : ∀ x : ℝ, ∫ y in (0 : ℝ)..L, conj (a x * b y) * (u (x : AddCircle L) * u (y : AddCircle L)) =
      (conj (a x) * u (x : AddCircle L)) * ∫ y in (0 : ℝ)..L, conj (b y) * u (y : AddCircle L) := by
    intro x
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun y _ => by simp only [map_mul]; ring)
  simp_rw [this]
  rw [intervalIntegral.integral_mul_const]

theorem pair2_sym {a b : ℝ → ℂ} (ha : Continuous a) (hb : Continuous b) {u : AddCircle L → ℂ}
    (hu : MemLp u 2 (volume : Measure (AddCircle L))) :
    pair2 (fun x y => (2 : ℂ)⁻¹ * (a x * b y + b x * a y)) u = pair1 a u * pair1 b u := by
  unfold pair2 pair1
  set A : ℝ → ℂ := fun x => conj (a x) * u (x : AddCircle L) with hA
  set B : ℝ → ℂ := fun x => conj (b x) * u (x : AddCircle L) with hB
  have iA : IntervalIntegrable A volume 0 L := intervalIntegrable_pair ha hu
  have iB : IntervalIntegrable B volume 0 L := intervalIntegrable_pair hb hu
  have hpt : ∀ x y : ℝ, conj ((2 : ℂ)⁻¹ * (a x * b y + b x * a y)) *
      (u (x : AddCircle L) * u (y : AddCircle L)) =
      (2 : ℂ)⁻¹ * (A x * B y) + (2 : ℂ)⁻¹ * (B x * A y) := by
    intro x y
    simp only [hA, hB, map_mul, map_add, map_inv₀, map_ofNat]
    ring
  have inner : ∀ x : ℝ, ∫ y in (0 : ℝ)..L, conj ((2 : ℂ)⁻¹ * (a x * b y + b x * a y)) *
      (u (x : AddCircle L) * u (y : AddCircle L)) =
      (2 : ℂ)⁻¹ * (A x * ∫ y in (0 : ℝ)..L, B y) + (2 : ℂ)⁻¹ * (B x * ∫ y in (0 : ℝ)..L, A y) := by
    intro x
    simp_rw [hpt x]
    rw [intervalIntegral.integral_add ((iB.const_mul (A x)).const_mul _)
      ((iA.const_mul (B x)).const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  simp_rw [inner]
  rw [intervalIntegral.integral_add ((iA.mul_const _).const_mul _) ((iB.mul_const _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  ring

end FiniteRank

/-! ## Part 6: the printed operators of `S_v` and the structure theorem -/

section Data

variable [Fact (0 < L)]

/-- `E₂(v) = ‖v‖²_{H¹} = ∫₀^L (|v'|² + |v|²)`. -/
def E2 (L : ℝ) (v : ℝ → ℂ) : ℝ := ∫ x in (0 : ℝ)..L, (‖deriv v x‖ ^ 2 + ‖v x‖ ^ 2)

/-- `V₄(v) = ‖v‖₄⁴ = ∫₀^L |v|⁴`. -/
def V4 (L : ℝ) (v : ℝ → ℂ) : ℝ := ∫ x in (0 : ℝ)..L, ‖v x‖ ^ 4

theorem I1_smooth {v : ℝ → ℂ} (hv : SmoothPeriodic L v) :
    I1 (lift hv) = ∫ x in (0 : ℝ)..L, ‖v x‖ ^ 2 := by
  unfold I1
  have := AddCircle.intervalIntegral_preimage L 0 (fun a : AddCircle L => ‖lift hv a‖ ^ 2)
  rw [zero_add] at this
  rw [← this]
  exact intervalIntegral.integral_congr (fun x _ => by simp only [lift_coe])

theorem E2_eq {v : ℝ → ℂ} (hv : SmoothPeriodic L v) : h04Norm L 1 (lift hv) ^ 2 = E2 L v := by
  rw [h04Norm_sq, f04NormSq_eq (h04_lift hv), I1_smooth hv]
  have hk : kinetic (lift hv) = ∫ x in (0 : ℝ)..L, ‖deriv v x‖ ^ 2 := kinetic_smooth hv
  rw [hk]
  unfold E2
  rw [intervalIntegral.integral_add]
  · exact ((continuous_norm.comp (deriv_continuous hv)).pow 2).intervalIntegrable _ _
  · exact ((continuous_norm.comp hv.smooth.continuous).pow 2).intervalIntegrable _ _

theorem V4_eq {v : ℝ → ℂ} (hv : SmoothPeriodic L v) : quartic (lift hv) = V4 L v :=
  quartic_smooth hv

/-- `z = Sym(v ⊗ r_v)`, `z(x,y) = (v(x) r_v(y) + r_v(x) v(y))/2`. -/
def zvec (v : ℝ → ℂ) : ℝ → ℝ → ℂ := fun x y => (2 : ℂ)⁻¹ * (v x * rvec v y + rvec v x * v y)

/-- `v ⊗ v`. -/
def vv (v : ℝ → ℂ) : ℝ → ℝ → ℂ := fun x y => v x * v y

/-- The rank-one data of the degree-two part:
`|v⟩⟨ℓ| + |ℓ⟩⟨v| − E₂(v) |v⟩⟨v|`. -/
def J2 (L : ℝ) (v : ℝ → ℂ) : FR1 where
  n := 3
  c := ![1, 1, -E2 L v]
  f := ![v, lvec v, v]
  g := ![lvec v, v, v]

/-- The rank-two data of the degree-four part:
`2κ(|v^{⊗2}⟩⟨z| + |z⟩⟨v^{⊗2}|) − 3κ V₄(v) |v^{⊗2}⟩⟨v^{⊗2}|`. -/
def J4 (κ L : ℝ) (v : ℝ → ℂ) : FR2 where
  n := 3
  c := ![2 * κ, 2 * κ, -(3 * κ * V4 L v)]
  f := ![vv v, zvec v, vv v]
  g := ![zvec v, vv v, vv v]

theorem alpha_eq_pair1 {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (u : AddCircle L → ℂ) :
    alpha (lift hv) u = pair1 v u := (pair1_eq_ip hv u).symm

theorem poly_J2 {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (u : AddCircle L → ℂ) :
    (J2 L v).poly u =
      ((2 * (conj (alpha (lift hv) u) * pair1 (lvec v) u).re
        - ‖alpha (lift hv) u‖ ^ 2 * E2 L v : ℝ) : ℂ) := by
  rw [alpha_eq_pair1 hv]
  set a := pair1 v u
  set X := pair1 (lvec v) u
  have h1 : ((2 * (conj a * X).re : ℝ) : ℂ) = conj a * X + conj (conj a * X) :=
    (Complex.add_conj _).symm
  have h2 : conj a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.conj_mul']; push_cast; rfl
  have hsum : (J2 L v).poly u =
      ((1 : ℝ) : ℂ) * (conj a * X) + ((1 : ℝ) : ℂ) * (conj X * a) +
        ((-E2 L v : ℝ) : ℂ) * (conj a * a) := by
    unfold FR1.poly
    show ∑ r : Fin 3, _ = _
    rw [Fin.sum_univ_three]
    rfl
  have h3 : conj (conj a * X) = a * conj X := by rw [map_mul, Complex.conj_conj]
  have key : (((2 * (conj a * X).re - ‖a‖ ^ 2 * E2 L v : ℝ)) : ℂ) =
      (conj a * X + conj (conj a * X)) - ((‖a‖ ^ 2 : ℝ) : ℂ) * ((E2 L v : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, h1, Complex.ofReal_mul]
  rw [key, hsum, h3, ← h2]
  push_cast
  ring

theorem pair2_vv {v : ℝ → ℂ} (u : AddCircle L → ℂ) :
    pair2 (vv v) u = pair1 v u * pair1 v u := pair2_sep u

theorem pair2_zvec {v : ℝ → ℂ} (hv : SmoothPeriodic L v) {u : AddCircle L → ℂ} (hu : H04 L 1 u) :
    pair2 (zvec v) u = pair1 v u * pair1 (rvec v) u :=
  pair2_sym hv.smooth.continuous (sp_rvec hv).smooth.continuous hu.1

theorem poly_J4 (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) {u : AddCircle L → ℂ}
    (hu : H04 L 1 u) :
    (J4 κ L v).poly u =
      ((4 * κ * ‖alpha (lift hv) u‖ ^ 2 * (conj (alpha (lift hv) u) * pair1 (rvec v) u).re
        - 3 * κ * ‖alpha (lift hv) u‖ ^ 4 * V4 L v : ℝ) : ℂ) := by
  rw [alpha_eq_pair1 hv]
  set a := pair1 v u
  set X := pair1 (rvec v) u
  have h1 : ((2 * (conj a * X).re : ℝ) : ℂ) = conj a * X + conj (conj a * X) :=
    (Complex.add_conj _).symm
  have h2 : conj a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.conj_mul']; push_cast; rfl
  have hsum : (J4 κ L v).poly u =
      ((2 * κ : ℝ) : ℂ) * (conj (a * a) * (a * X)) +
        ((2 * κ : ℝ) : ℂ) * (conj (a * X) * (a * a)) +
        ((-(3 * κ * V4 L v) : ℝ) : ℂ) * (conj (a * a) * (a * a)) := by
    unfold FR2.poly
    show ∑ r : Fin 3, _ = _
    rw [Fin.sum_univ_three]
    show _ * (conj (pair2 (vv v) u) * pair2 (zvec v) u) + _ * (conj (pair2 (zvec v) u) * pair2 (vv v) u)
      + _ * (conj (pair2 (vv v) u) * pair2 (vv v) u) = _
    rw [pair2_vv, pair2_zvec hv hu]
    rfl
  have key : (((4 * κ * ‖a‖ ^ 2 * (conj a * X).re - 3 * κ * ‖a‖ ^ 4 * V4 L v : ℝ)) : ℂ) =
      ((2 * κ : ℝ) : ℂ) * ((‖a‖ ^ 2 : ℝ) : ℂ) * (conj a * X + conj (conj a * X))
        - ((3 * κ * V4 L v : ℝ) : ℂ) * ((‖a‖ ^ 2 : ℝ) : ℂ) ^ 2 := by
    have : ((4 * κ * ‖a‖ ^ 2 * (conj a * X).re : ℝ) : ℂ) =
        ((2 * κ : ℝ) : ℂ) * ((‖a‖ ^ 2 : ℝ) : ℂ) * ((2 * (conj a * X).re : ℝ) : ℂ) := by
      push_cast; ring
    rw [Complex.ofReal_sub, this, h1]
    push_cast; ring
  rw [key, hsum, ← h2]
  simp only [map_mul, Complex.conj_conj, Complex.ofReal_neg]
  ring

/-- **Structure of `S_v` (`eq:A1-S` and the printed rank-one / rank-two operators).**
For smooth `v`, `κ` real and `u ∈ H¹`, `S_v(u) = a_{J₂}(u) + a_{J₄}(u)`, a degree-two and a
degree-four finite-rank polynomial. -/
theorem Sv_structure (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) {u : AddCircle L → ℂ}
    (hu : H04 L 1 u) :
    ((Sv κ (lift hv) u : ℝ) : ℂ) = (J2 L v).poly u + (J4 κ L v).poly u := by
  have h := Sv_explicit κ hv hu
  rw [E2_eq hv, V4_eq hv] at h
  rw [h, poly_J2 hv u, poly_J4 κ hv hu]
  push_cast
  ring

theorem sp2_mul {a b : ℝ → ℂ} (ha : SmoothPeriodic L a) (hb : SmoothPeriodic L b) :
    SmoothPeriodic2 L (fun x y => a x * b y) :=
  ⟨(ha.smooth.comp contDiff_fst).mul (hb.smooth.comp contDiff_snd),
    fun x y => by rw [ha.periodic x],
    fun x y => by rw [hb.periodic y]⟩

theorem sp2_add {F G : ℝ → ℝ → ℂ} (hF : SmoothPeriodic2 L F) (hG : SmoothPeriodic2 L G) :
    SmoothPeriodic2 L (fun x y => F x y + G x y) :=
  ⟨hF.smooth.add hG.smooth, fun x y => by rw [hF.per1, hG.per1],
    fun x y => by rw [hF.per2, hG.per2]⟩

theorem sp2_const_mul {F : ℝ → ℝ → ℂ} (c : ℂ) (hF : SmoothPeriodic2 L F) :
    SmoothPeriodic2 L (fun x y => c * F x y) :=
  ⟨contDiff_const.mul hF.smooth, fun x y => by rw [hF.per1],
    fun x y => by rw [hF.per2]⟩

theorem J2_smooth {v : ℝ → ℂ} (hv : SmoothPeriodic L v) : (J2 L v).IsSmooth L := by
  intro r
  fin_cases r
  · exact ⟨hv, sp_lvec hv⟩
  · exact ⟨sp_lvec hv, hv⟩
  · exact ⟨hv, hv⟩

theorem J4_smooth (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) : (J4 κ L v).IsSmooth L := by
  have hvv : SmoothPeriodic2 L (vv v) := sp2_mul hv hv
  have hz : SmoothPeriodic2 L (zvec v) :=
    sp2_const_mul _ (sp2_add (sp2_mul hv (sp_rvec hv)) (sp2_mul (sp_rvec hv) hv))
  intro r
  fin_cases r
  · exact ⟨hvv, hz⟩
  · exact ⟨hz, hvv⟩
  · exact ⟨hvv, hvv⟩

theorem J2_kernel (L : ℝ) (v : ℝ → ℂ) (x x' : ℝ) :
    (J2 L v).kernel x x' = v x * conj (lvec v x') + lvec v x * conj (v x') -
      ((E2 L v : ℝ) : ℂ) * (v x * conj (v x')) := by
  unfold FR1.kernel
  show ∑ r : Fin 3, _ = _
  rw [Fin.sum_univ_three]
  simp only [J2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Complex.ofReal_one, Complex.ofReal_neg]
  ring

theorem J4_kernel (κ L : ℝ) (v : ℝ → ℂ) (x y x' y' : ℝ) :
    (J4 κ L v).kernel x y x' y' =
      ((2 * κ : ℝ) : ℂ) * (vv v x y * conj (zvec v x' y')) +
      ((2 * κ : ℝ) : ℂ) * (zvec v x y * conj (vv v x' y')) -
      ((3 * κ * V4 L v : ℝ) : ℂ) * (vv v x y * conj (vv v x' y')) := by
  unfold FR2.kernel
  show ∑ r : Fin 3, _ = _
  rw [Fin.sum_univ_three]
  simp only [J4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Complex.ofReal_neg]
  ring

theorem J2_herm (L : ℝ) (v : ℝ → ℂ) : (J2 L v).Herm := by
  intro x x'
  rw [J2_kernel, J2_kernel]
  simp only [map_sub, map_add, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

theorem J4_herm (κ L : ℝ) (v : ℝ → ℂ) : (J4 κ L v).Herm := by
  intro x y x' y'
  rw [J4_kernel, J4_kernel]
  simp only [map_sub, map_add, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

end Data

/-! ## Part 7: coercivity (`eq:A1-coercive`), the prefatory identities, and the headline statement -/

section Headline

variable [Fact (0 < L)]

/-- **`eq:A1-coercive`, `H¹` fields.**  For `κ ≥ 0` and `v, u ∈ H¹`:
`F_v(u) ≥ ‖w‖²_{H¹} + (κ/3)‖w‖₄⁴`.  (No unit-norm or smoothness hypothesis is needed.) -/
theorem Fv_coercive_general {κ : ℝ} (hκ : 0 ≤ κ) {v u : AddCircle L → ℂ} (hv : H04 L 1 v)
    (hu : H04 L 1 u) :
    h04Norm L 1 (wF v u) ^ 2 + κ / 3 * quartic (wF v u) ≤ Fv κ v u := by
  set α := alpha v u
  obtain ⟨hq, -⟩ := h04_cmul hv α
  obtain ⟨hw, -⟩ := h04_sub hu hq
  have h := bregman_ge hκ hq hw
  have e : (fun x => α * v x + (u x - α * v x)) = u := by funext x; ring
  rw [e] at h
  rw [h04Norm_sq]
  exact h

theorem ip_self_eq_I1 (f : AddCircle L → ℂ) : ip f f = ((I1 f : ℝ) : ℂ) := by
  unfold ip I1
  have h := integral_ofReal (𝕜 := ℂ) (μ := (volume : Measure (AddCircle L)))
    (f := fun x => ‖f x‖ ^ 2)
  refine Eq.trans ?_ h.symm.symm
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [Complex.conj_mul']; push_cast; rfl

/-- `⟨v, w⟩ = 0` for unit `v`. -/
theorem ip_wF {v u : AddCircle L → ℂ} (hv : H04 L 1 v) (hu : H04 L 1 u) (hvu : I1 v = 1) :
    ip v (wF v u) = 0 := by
  have i1 := integrable_conj_mul hv.1 hu.1
  have i2 := integrable_conj_mul hv.1 hv.1
  unfold ip at *
  have : ∫ x, conj (v x) * wF v u x ∂(volume : Measure (AddCircle L)) =
      ∫ x, conj (v x) * u x ∂(volume : Measure (AddCircle L)) -
        alpha v u * ∫ x, conj (v x) * v x ∂(volume : Measure (AddCircle L)) := by
    rw [← integral_const_mul, ← integral_sub i1 (i2.const_mul _)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by unfold wF; ring)
  rw [this]
  have h2 := ip_self_eq_I1 v
  unfold ip at h2
  rw [h2, hvu]
  simp [alpha, ip]

/-- `1 − |α|² = ‖w‖₂²` for unit `u, v`. -/
theorem I1_wF {v u : AddCircle L → ℂ} (hv : H04 L 1 v) (hu : H04 L 1 u) (hvu : I1 v = 1)
    (huu : I1 u = 1) : I1 (wF v u) = 1 - ‖alpha v u‖ ^ 2 := by
  set α := alpha v u with hα
  have i1 := integrable_conj_mul hv.1 hu.1
  have hint : Integrable (fun x => (conj α * (conj (v x) * u x)).re)
      (volume : Measure (AddCircle L)) := (i1.const_mul _).re
  have iu : Integrable (fun x => ‖u x‖ ^ 2) (volume : Measure (AddCircle L)) := hu.1.norm.integrable_sq
  have iv : Integrable (fun x => ‖v x‖ ^ 2) (volume : Measure (AddCircle L)) := hv.1.norm.integrable_sq
  have hpt : ∀ x, ‖wF v u x‖ ^ 2 =
      ‖u x‖ ^ 2 + ‖α‖ ^ 2 * ‖v x‖ ^ 2 - 2 * (conj α * (conj (v x) * u x)).re := by
    intro x
    unfold wF
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  unfold I1
  simp_rw [hpt]
  have k1 : Integrable (fun x => ‖u x‖ ^ 2 + ‖α‖ ^ 2 * ‖v x‖ ^ 2)
      (volume : Measure (AddCircle L)) := iu.add (iv.const_mul _)
  have k2 : Integrable (fun x => 2 * (conj α * (conj (v x) * u x)).re)
      (volume : Measure (AddCircle L)) := hint.const_mul 2
  rw [integral_sub k1 k2, integral_add iu (iv.const_mul _),
    integral_const_mul, integral_const_mul]
  have e3 : ∫ x, (conj α * (conj (v x) * u x)).re ∂(volume : Measure (AddCircle L)) = ‖α‖ ^ 2 := by
    have := integral_re (i1.const_mul (conj α))
    simp only [RCLike.re_to_complex] at this
    rw [this, integral_const_mul]
    have h3 : conj α * ∫ x, conj (v x) * u x ∂(volume : Measure (AddCircle L)) =
        ((‖α‖ ^ 2 : ℝ) : ℂ) := by
      rw [hα]
      unfold alpha ip
      rw [Complex.conj_mul']; push_cast; rfl
    rw [h3, Complex.ofReal_re]
  have hu1 : ∫ x, ‖u x‖ ^ 2 ∂(volume : Measure (AddCircle L)) = 1 := huu
  have hv1 : ∫ x, ‖v x‖ ^ 2 ∂(volume : Measure (AddCircle L)) = 1 := hvu
  rw [e3, hu1, hv1]
  ring

/-- **`ENERGY-006` / `lem:A1-relative`, coercive and structural clauses.**
For `L, κ > 0`, a smooth unit `v` on `𝕋_L` and a unit `u ∈ H¹(𝕋_L)`, with
`α = ⟨v,u⟩`, `q = αv`, `w = u − q`, `F_v(u) = E(u) − E(q) − dE(q)[w]`, `E = I_3 + I_1`:
1. `⟨v,w⟩ = 0` and `1 − |α|² = ‖w‖₂²`;
2. `F_v(u) ≥ ‖w‖²_{H¹} + (κ/3)‖w‖₄⁴` (`eq:A1-coercive`);
3. `S_v(u) = E(u) − F_v(u) = a_{J₂}(u) + a_{J₄}(u)` where `J₂ = |v⟩⟨ℓ| + |ℓ⟩⟨v| − E₂(v)|v⟩⟨v|`
   (degree two, rank ≤ 3) and `J₄ = 2κ(|v^{⊗2}⟩⟨z| + |z⟩⟨v^{⊗2}|) − 3κV₄(v)|v^{⊗2}⟩⟨v^{⊗2}|`
   (degree four, rank ≤ 3), both with smooth periodic data, selfadjoint kernels, and `a_J`
   gauge invariant. -/
theorem energy006_A1_relative {κ : ℝ} (hκ : 0 < κ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v)
    (hvu : I1 (lift hv) = 1) {u : AddCircle L → ℂ} (hu : H04 L 1 u) (huu : I1 u = 1) :
    (ip (lift hv) (wF (lift hv) u) = 0 ∧
        I1 (wF (lift hv) u) = 1 - ‖alpha (lift hv) u‖ ^ 2) ∧
    (h04Norm L 1 (wF (lift hv) u) ^ 2 + κ / 3 * quartic (wF (lift hv) u) ≤
        Fv κ (lift hv) u) ∧
    (((Sv κ (lift hv) u : ℝ) : ℂ) = (J2 L v).poly u + (J4 κ L v).poly u) ∧
    ((J2 L v).IsSmooth L ∧ (J4 κ L v).IsSmooth L) ∧
    ((J2 L v).Herm ∧ (J4 κ L v).Herm) ∧
    ((J2 L v).n = 3 ∧ (J4 κ L v).n = 3) ∧
    ((∀ (z : ℂ), ‖z‖ = 1 →
        (J2 L v).poly (fun x => z * u x) = (J2 L v).poly u ∧
        (J4 κ L v).poly (fun x => z * u x) = (J4 κ L v).poly u) ∧
      (∀ (z : ℂ),
        (J2 L v).poly (fun x => z * u x) = ((‖z‖ ^ 2 : ℝ) : ℂ) * (J2 L v).poly u ∧
        (J4 κ L v).poly (fun x => z * u x) = ((‖z‖ ^ 4 : ℝ) : ℂ) * (J4 κ L v).poly u)) := by
  have hvH := h04_lift hv
  refine ⟨⟨ip_wF hvH hu hvu, I1_wF hvH hu hvu huu⟩, Fv_coercive_general hκ.le hvH hu,
    Sv_structure κ hv hu, ⟨J2_smooth hv, J4_smooth κ hv⟩, ⟨J2_herm L v, J4_herm κ L v⟩,
    ⟨rfl, rfl⟩, ⟨fun z hz => ⟨(J2 L v).poly_gauge u hz, (J4 κ L v).poly_gauge u hz⟩,
      fun z => ⟨(J2 L v).poly_smul u z, (J4 κ L v).poly_smul u z⟩⟩⟩

/-- `E = I_3 + I_1` on smooth profiles: `charge 3 + charge 1 = E`. -/
theorem Efun_eq_charge (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) :
    charge L κ v 3 + charge L κ v 1 = ((Efun κ (lift hv) : ℝ) : ℂ) := by
  rw [charge_three_eq_energyH1 κ hv, charge_one, ← I1_smooth hv]
  unfold Efun
  push_cast
  rfl


/-! ## Part 8: `F_v` is unchanged by a constant phase of `u` or of `v` (printed after `eq:A1-projection`) -/

theorem conj_mul_unit {z : ℂ} (hz : ‖z‖ = 1) : conj z * z = 1 := by
  rw [Complex.conj_mul', hz]; simp

theorem ip_smul_right (f g : AddCircle L → ℂ) (z : ℂ) : ip f (fun x => z * g x) = z * ip f g := by
  unfold ip
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

theorem ip_smul_left (f g : AddCircle L → ℂ) (z : ℂ) :
    ip (fun x => z * f x) g = conj z * ip f g := by
  unfold ip
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [map_mul]; ring)

/-- `F_v(u)` is unchanged by a constant phase of `v`. -/
theorem Fv_phase_v (κ : ℝ) (v u : AddCircle L → ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    Fv κ (fun x => z * v x) u = Fv κ v u := by
  have hα : alpha (fun x => z * v x) u = conj z * alpha v u := ip_smul_left v u z
  have h1 := conj_mul_unit hz
  have hproj : projF (fun x => z * v x) u = projF v u := by
    funext x
    unfold projF
    rw [hα]
    linear_combination (alpha v u * v x) * h1
  have hw : wF (fun x => z * v x) u = wF v u := by
    funext x
    unfold wF
    rw [hα]
    linear_combination (-(alpha v u * v x)) * h1
  unfold Fv
  rw [hproj, hw]

theorem ip1_cmul_both (z : ℂ) (a b : ℤ → ℂ) :
    ip1 L (fun n => z * a n) (fun n => z * b n) = (conj z * z) * ip1 L a b := by
  unfold ip1
  rw [← tsum_mul_left]
  exact tsum_congr (fun n => by rw [map_mul]; ring)

theorem A1_phase (q h : AddCircle L → ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    A1 (fun x => z * q x) (fun x => z * h x) = A1 q h := by
  unfold A1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  unfold qc1 rr
  have h1 := conj_mul_unit hz
  have : conj (z * q x) * (z * h x) = conj (q x) * h x := by
    rw [map_mul]; linear_combination (conj (q x) * h x) * h1
  rw [this, norm_mul, hz]; ring

/-- `F_v(u)` is unchanged by a constant phase of `u`. -/
theorem Fv_phase_u (κ : ℝ) {v u : AddCircle L → ℂ} (hv : H04 L 1 v) (hu : H04 L 1 u) {z : ℂ}
    (hz : ‖z‖ = 1) : Fv κ v (fun x => z * u x) = Fv κ v u := by
  have hα : alpha v (fun x => z * u x) = z * alpha v u := ip_smul_right v u z
  obtain ⟨hq, hqco⟩ := h04_cmul hv (alpha v u)
  obtain ⟨hw, hwco⟩ := h04_sub hu hq
  have hq' : H04 L 1 (projF v u) := hq
  have hw' : H04 L 1 (wF v u) := hw
  have hproj : projF v (fun x => z * u x) = fun x => z * projF v u x := by
    funext x; unfold projF; rw [hα]; ring
  have hwf : wF v (fun x => z * u x) = fun x => z * wF v u x := by
    funext x; unfold wF; rw [hα]; ring
  have hE : Efun κ (fun x => z * u x) = Efun κ u := by
    rw [efun_cmul κ hu z, efun_eq κ hu, hz]; ring
  have hEq : Efun κ (fun x => z * projF v u x) = Efun κ (projF v u) := by
    rw [efun_cmul κ hq' z, efun_eq κ hq', hz]; ring
  have hd : dE κ (fun x => z * projF v u x) (fun x => z * wF v u x) = dE κ (projF v u) (wF v u) := by
    obtain ⟨hzq, hzqco⟩ := h04_cmul hq' z
    obtain ⟨hzw, hzwco⟩ := h04_cmul hw' z
    rw [dE_eq κ hzq hzw, dE_eq κ hq' hw', hzqco, hzwco, ip1_cmul_both, conj_mul_unit hz,
      A1_phase _ _ hz]
    simp
  unfold Fv
  rw [hproj, hwf, hE, hEq, hd]

end Headline

#print axioms energy006_A1_relative
#print axioms Fv_coercive_general
#print axioms bregman_ge
#print axioms bregman_eq
#print axioms dE_eq
#print axioms Sv_explicit
#print axioms Sv_structure
#print axioms ip_wF
#print axioms I1_wF
#print axioms Fv_phase_v
#print axioms Fv_phase_u
#print axioms Efun_eq_charge
#print axioms J2_smooth
#print axioms J4_smooth
#print axioms J2_herm
#print axioms J4_herm
#print axioms FR1.poly_gauge
#print axioms FR2.poly_gauge
#print axioms FR1.poly_smul
#print axioms FR2.poly_smul
#print axioms pair2_sym

end QuantumNLS.RelativeEnergy

import NlsGge.Hierarchy.ALPositiveDecompositions38
import NlsGge.Hierarchy.RiccatiPhysicalH1Q4LowerOrderRemainderAfterRawWeightedCrossPrerequisitesThird
import NlsGge.Hierarchy.RiccatiFinitePlaneQuarticExtensionIntegral
import NlsGge.Hierarchy.RiccatiPhysicalH1Q4SixthPowerIntegralIdentity
import NlsGge.Hierarchy.RiccatiUnitPeriodIntervalToPhysicalHaar
import NlsGge.Sobolev.PeriodicBridge
import Mathlib

/-! L05 (`C:lem:sampling`, paper/v2.tex l.2143-2183): sampling lemma for the AL ensemble through `Q₄`.
Part 1: grid, DFT/Parseval for finite Fourier planes, Riemann sums, F_N interface. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section

namespace NlsGge.AblowitzLadik

open Finset Filter Topology NlsGge.Pilot NlsGge.Analysis

def alh38 (N : ℕ) : ℝ := 1 / (2 * (N : ℝ) + 1)
def alt38 (N : ℕ) (j : ZMod (2 * N + 1)) : ℝ := (j.val : ℝ) * alh38 N
theorem alh38_pos (N : ℕ) : 0 < alh38 N := by
  unfold alh38; positivity
theorem alh38_mul (N : ℕ) : (2 * (N : ℝ) + 1) * alh38 N = 1 := by
  unfold alh38; field_simp

theorem alsum_zmod38 (N : ℕ) (G : ℕ → ℂ) :
    ∑ j : ZMod (2 * N + 1), G j.val = ∑ m ∈ range (2 * N + 1), G m := by
  have := Fin.sum_univ_eq_sum_range G (2 * N + 1)
  exact this

theorem planeReal_eq38 (N : ℕ) (z : FourierPlane N) (t : ℝ) :
    planeReal N z t = ∑ i : Fin (2 * N + 1),
      z i * Complex.exp (2 * Real.pi * Complex.I * ((modeIndex N i : ℤ) : ℂ) * (t : ℂ)) := by
  unfold planeReal planeField
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fourier_coe_apply]
  congr 2
  push_cast
  ring

theorem charsum38 (N : ℕ) (m : ℤ) (hm : |m| < 2 * (N : ℤ) + 1) :
    ∑ j : ZMod (2 * N + 1), Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (alt38 N j : ℂ))
      = if m = 0 then ((2 * N + 1 : ℕ) : ℂ) else 0 := by
  set r : ℂ := Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) / ((2 * N + 1 : ℕ) : ℂ)) with hr
  have hL : ((2 * N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * N)
  have hterm : ∀ j : ℕ, Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (((j : ℝ) * alh38 N : ℝ) : ℂ)) = r ^ j := by
    intro j
    rw [hr, ← Complex.exp_nat_mul _ j]
    congr 1
    have : (alh38 N : ℂ) = 1 / ((2 * N + 1 : ℕ) : ℂ) := by
      unfold alh38; push_cast; ring
    push_cast
    rw [show ((alh38 N : ℝ) : ℂ) = 1 / (2 * (N : ℂ) + 1) by unfold alh38; push_cast; ring]
    field_simp
  have hs : ∑ j : ZMod (2 * N + 1), Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (alt38 N j : ℂ))
      = ∑ j ∈ range (2 * N + 1), r ^ j := by
    rw [← alsum_zmod38 N (fun j => r ^ j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact hterm j.val
  rw [hs]
  by_cases h0 : m = 0
  · subst h0; simp [hr]
  · simp only [h0, if_false]
    have hr1 : r ≠ 1 := by
      intro h1
      rw [hr, Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      have h2 : (m : ℂ) = n * ((2 * N + 1 : ℕ) : ℂ) := by
        field_simp at hn
        rw [hn]; ring
      have h3 : m = n * ((2 * N + 1 : ℕ) : ℤ) := by exact_mod_cast h2
      apply h0
      rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
      · exfalso
        have : n ≤ -1 := by omega
        have : m ≤ -(2 * (N : ℤ) + 1) := by push_cast at h3; nlinarith
        have := abs_lt.mp hm; omega
      · subst hn0; simpa using h3
      · exfalso
        have : 1 ≤ n := by omega
        have : m ≥ 2 * (N : ℤ) + 1 := by push_cast at h3; nlinarith
        have := abs_lt.mp hm; omega
    have hrL : r ^ (2 * N + 1) = 1 := by
      rw [hr, ← Complex.exp_nat_mul _ (2 * N + 1)]
      rw [Complex.exp_eq_one_iff]
      exact ⟨m, by field_simp⟩
    rw [geom_sum_eq hr1, hrL]; simp

theorem planeReal_mul_conj38 (N : ℕ) (z w : FourierPlane N) (t : ℝ) :
    planeReal N z t * (starRingEnd ℂ) (planeReal N w t) =
      ∑ i : Fin (2 * N + 1), ∑ k : Fin (2 * N + 1), z i * (starRingEnd ℂ) (w k) *
        Complex.exp (2 * Real.pi * Complex.I *
          (((modeIndex N i : ℤ) : ℂ) - ((modeIndex N k : ℤ) : ℂ)) * (t : ℂ)) := by
  rw [planeReal_eq38, planeReal_eq38, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, ← Complex.exp_conj]
  have : (starRingEnd ℂ) (2 * Real.pi * Complex.I * ((modeIndex N k : ℤ) : ℂ) * (t : ℂ))
      = -(2 * Real.pi * Complex.I * ((modeIndex N k : ℤ) : ℂ) * (t : ℂ)) := by
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast]; ring
  rw [this]
  have e : Complex.exp (2 * Real.pi * Complex.I * ((modeIndex N i : ℤ) : ℂ) * (t : ℂ)) *
      Complex.exp (-(2 * Real.pi * Complex.I * ((modeIndex N k : ℤ) : ℂ) * (t : ℂ)))
      = Complex.exp (2 * Real.pi * Complex.I *
          (((modeIndex N i : ℤ) : ℂ) - ((modeIndex N k : ℤ) : ℂ)) * (t : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [← e]; ring

theorem parsevalInner38 (N : ℕ) (z w : FourierPlane N) :
    alh38 N * ∑ j : ZMod (2 * N + 1),
        planeReal N z (alt38 N j) * (starRingEnd ℂ) (planeReal N w (alt38 N j))
      = ∑ i : Fin (2 * N + 1), z i * (starRingEnd ℂ) (w i) := by
  simp_rw [planeReal_mul_conj38]
  have h1 : ∀ F : ZMod (2 * N + 1) → Fin (2 * N + 1) → Fin (2 * N + 1) → ℂ,
      ∑ j, ∑ i, ∑ k, F j i k = ∑ i, ∑ k, ∑ j, F j i k := by
    intro F
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  have hk : ∀ k : Fin (2 * N + 1), alh38 N * ∑ j : ZMod (2 * N + 1), z i * (starRingEnd ℂ) (w k) *
        Complex.exp (2 * Real.pi * Complex.I *
          (((modeIndex N i : ℤ) : ℂ) - ((modeIndex N k : ℤ) : ℂ)) * (alt38 N j : ℂ))
      = if k = i then z i * (starRingEnd ℂ) (w i) else 0 := by
    intro k
    rw [← Finset.mul_sum]
    have hb := modeIndex_bounds N i
    have hb' := modeIndex_bounds N k
    have hm : |modeIndex N i - modeIndex N k| < 2 * (N : ℤ) + 1 := by
      rw [abs_lt]; constructor <;> omega
    have hc := charsum38 N (modeIndex N i - modeIndex N k) hm
    push_cast at hc
    rw [hc]
    by_cases hki : k = i
    · rw [hki]
      simp only [sub_self, ite_true]
      have := alh38_mul N
      push_cast
      have h2 : alh38 N * (2 * (N : ℂ) + 1) = 1 := by exact_mod_cast (by linarith [this] : alh38 N * (2 * (N : ℝ) + 1) = 1)
      calc alh38 N * (z i * (starRingEnd ℂ) (w i) * (2 * (N : ℂ) + 1))
          = (alh38 N * (2 * (N : ℂ) + 1)) * (z i * (starRingEnd ℂ) (w i)) := by ring
        _ = _ := by rw [h2]; simp
    · have : modeIndex N i - modeIndex N k ≠ 0 := by
        intro h0
        exact hki (modeIndex_injective N (by omega)).symm
      simp only [this, ite_false, hki]
      simp
  rw [Finset.sum_congr rfl (fun k _ => hk k)]
  simp

theorem parseval38 (N : ℕ) (z : FourierPlane N) :
    alh38 N * ∑ j : ZMod (2 * N + 1), ‖planeReal N z (alt38 N j)‖ ^ 2
      = ∑ i : Fin (2 * N + 1), ‖z i‖ ^ 2 := by
  have h := parsevalInner38 N z z
  have e : ∀ c : ℂ, c * (starRingEnd ℂ) c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    intro c; rw [Complex.mul_conj']; push_cast; ring
  simp_rw [e] at h
  exact_mod_cast h

/-- The symbol `ω_{h,k} = 2 sin(π k h)/h`. -/
def alomega38 (N : ℕ) (k : ℤ) : ℝ := 2 * Real.sin (Real.pi * k * alh38 N) / alh38 N

theorem norm_fwdMul38 (N : ℕ) (k : ℤ) :
    ‖(Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (alh38 N : ℂ)) - 1) / (alh38 N : ℂ)‖
      = |alomega38 N k| := by
  have hh := alh38_pos N
  have : (2 * Real.pi * Complex.I * (k : ℂ) * (alh38 N : ℂ))
      = Complex.I * ((2 * Real.pi * k * alh38 N : ℝ) : ℂ) := by push_cast; ring
  rw [this, norm_div, Complex.norm_exp_I_mul_ofReal_sub_one]
  unfold alomega38
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh, abs_div]
  rw [show (2 * Real.pi * k * alh38 N) / 2 = Real.pi * k * alh38 N by ring]

theorem abs_alomega_le38 (N : ℕ) (k : ℤ) : |alomega38 N k| ≤ 2 * Real.pi * |(k : ℝ)| := by
  have hh := alh38_pos N
  unfold alomega38
  rw [abs_div, abs_of_pos hh, div_le_iff₀ hh]
  have h1 := Real.abs_sin_le_abs (x := Real.pi * k * alh38 N)
  rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hh] at h1
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  nlinarith [h1]

/-- Fourier multiplier of the forward difference quotient. -/
def alFwdMul38 (N : ℕ) (k : ℤ) : ℂ :=
  (Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (alh38 N : ℂ)) - 1) / (alh38 N : ℂ)

def alBwdMul38 (N : ℕ) (k : ℤ) : ℂ :=
  (1 - Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (alh38 N : ℂ)))) / (alh38 N : ℂ)

def alSecMul38 (N : ℕ) (k : ℤ) : ℂ :=
  (Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (alh38 N : ℂ)) - 2
    + Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (alh38 N : ℂ)))) / (alh38 N : ℂ) ^ 2

theorem norm_alFwdMul38 (N : ℕ) (k : ℤ) : ‖alFwdMul38 N k‖ = |alomega38 N k| :=
  norm_fwdMul38 N k

theorem alExpNorm38 (N : ℕ) (k : ℤ) (σ : ℝ) :
    ‖Complex.exp (σ * (2 * Real.pi * Complex.I * (k : ℂ) * (alh38 N : ℂ)))‖ = 1 := by
  have : (σ : ℂ) * (2 * Real.pi * Complex.I * (k : ℂ) * (alh38 N : ℂ))
      = Complex.I * ((σ * (2 * Real.pi * k * alh38 N) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_exp_I_mul_ofReal]

theorem norm_alBwdMul38 (N : ℕ) (k : ℤ) : ‖alBwdMul38 N k‖ = |alomega38 N k| := by
  rw [← norm_fwdMul38 N k]
  unfold alBwdMul38
  rw [norm_div, norm_div]
  congr 1
  set θ : ℂ := 2 * Real.pi * Complex.I * (k : ℂ) * (alh38 N : ℂ) with hθ
  have hn : ‖Complex.exp (((-1 : ℝ) : ℂ) * θ)‖ = 1 := alExpNorm38 N k (-1)
  have e1 : Complex.exp (((-1 : ℝ) : ℂ) * θ) = Complex.exp (-θ) := by congr 1; push_cast; ring
  rw [e1] at hn
  have : 1 - Complex.exp (-θ) = (Complex.exp (-θ)) * (Complex.exp θ - 1) := by
    rw [mul_sub, ← Complex.exp_add]; simp
  rw [this, norm_mul, hn, one_mul]

theorem norm_alSecMul38 (N : ℕ) (k : ℤ) : ‖alSecMul38 N k‖ = alomega38 N k ^ 2 := by
  have hh := alh38_pos N
  unfold alSecMul38
  set θ : ℂ := 2 * Real.pi * Complex.I * (k : ℂ) * (alh38 N : ℂ) with hθ
  have e : Complex.exp θ - 2 + Complex.exp (-θ) = (Complex.exp θ - 1) * (1 - Complex.exp (-θ)) := by
    rw [sub_mul, mul_sub, mul_sub, ← Complex.exp_add]; simp; ring
  have h1 := norm_fwdMul38 N k
  have h2 := norm_alBwdMul38 N k
  unfold alBwdMul38 at h2
  rw [← hθ] at h1 h2
  rw [e, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh] at h1 h2
  have ha : ‖Complex.exp θ - 1‖ = alh38 N * |alomega38 N k| := by
    rw [← h1]; field_simp
  have hb : ‖1 - Complex.exp (-θ)‖ = alh38 N * |alomega38 N k| := by
    rw [← h2]; field_simp
  rw [ha, hb]
  have : |alomega38 N k| * |alomega38 N k| = alomega38 N k ^ 2 := by rw [abs_mul_abs_self]; ring
  field_simp
  rw [← this]; ring


theorem alExpShift38 (k : ℤ) (t σ : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * ((t + σ : ℝ) : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (t : ℂ)) *
        Complex.exp (σ * (2 * Real.pi * Complex.I * (k : ℂ))) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem planeReal_fwd38 (N : ℕ) (z : FourierPlane N) (t : ℝ) :
    (planeReal N z (t + alh38 N) - planeReal N z t) / (alh38 N : ℂ)
      = planeReal N (fun i => z i * alFwdMul38 N (modeIndex N i)) t := by
  rw [planeReal_eq38, planeReal_eq38, planeReal_eq38, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [alExpShift38]
  unfold alFwdMul38
  have : (alh38 N : ℂ) * (2 * Real.pi * Complex.I * ((modeIndex N i : ℤ) : ℂ))
      = 2 * Real.pi * Complex.I * ((modeIndex N i : ℤ) : ℂ) * (alh38 N : ℂ) := by ring
  rw [show ((alh38 N : ℝ) : ℂ) * (2 * Real.pi * Complex.I * ((modeIndex N i : ℤ) : ℂ)) = _ from this]
  ring

theorem planeReal_bwd38 (N : ℕ) (z : FourierPlane N) (t : ℝ) :
    (planeReal N z t - planeReal N z (t - alh38 N)) / (alh38 N : ℂ)
      = planeReal N (fun i => z i * alBwdMul38 N (modeIndex N i)) t := by
  rw [planeReal_eq38, planeReal_eq38, planeReal_eq38, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sub_eq_add_neg t, alExpShift38]
  unfold alBwdMul38
  have : (((-alh38 N : ℝ) : ℂ)) * (2 * Real.pi * Complex.I * ((modeIndex N i : ℤ) : ℂ))
      = -(2 * Real.pi * Complex.I * ((modeIndex N i : ℤ) : ℂ) * (alh38 N : ℂ)) := by push_cast; ring
  rw [this]
  ring

theorem planeReal_sec38 (N : ℕ) (z : FourierPlane N) (t : ℝ) :
    (planeReal N z (t + alh38 N) - 2 * planeReal N z t + planeReal N z (t - alh38 N))
        / (alh38 N : ℂ) ^ 2
      = planeReal N (fun i => z i * alSecMul38 N (modeIndex N i)) t := by
  rw [planeReal_eq38, planeReal_eq38, planeReal_eq38, planeReal_eq38, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sub_eq_add_neg t, alExpShift38, alExpShift38]
  unfold alSecMul38
  have : (((-alh38 N : ℝ) : ℂ)) * (2 * Real.pi * Complex.I * ((modeIndex N i : ℤ) : ℂ))
      = -(2 * Real.pi * Complex.I * ((modeIndex N i : ℤ) : ℂ) * (alh38 N : ℂ)) := by push_cast; ring
  have h2 : (((alh38 N : ℝ)) : ℂ) * (2 * Real.pi * Complex.I * ((modeIndex N i : ℤ) : ℂ))
      = (2 * Real.pi * Complex.I * ((modeIndex N i : ℤ) : ℂ) * (alh38 N : ℂ)) := by ring
  rw [this, h2]
  ring

theorem parsevalFwd38 (N : ℕ) (z : FourierPlane N) :
    alh38 N * ∑ j : ZMod (2 * N + 1),
        ‖(planeReal N z (alt38 N j + alh38 N) - planeReal N z (alt38 N j)) / (alh38 N : ℂ)‖ ^ 2
      = ∑ i : Fin (2 * N + 1), alomega38 N (modeIndex N i) ^ 2 * ‖z i‖ ^ 2 := by
  simp_rw [planeReal_fwd38]
  rw [parseval38]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_mul, mul_pow, norm_alFwdMul38, sq_abs]; ring

theorem parsevalBwd38 (N : ℕ) (z : FourierPlane N) :
    alh38 N * ∑ j : ZMod (2 * N + 1),
        ‖(planeReal N z (alt38 N j) - planeReal N z (alt38 N j - alh38 N)) / (alh38 N : ℂ)‖ ^ 2
      = ∑ i : Fin (2 * N + 1), alomega38 N (modeIndex N i) ^ 2 * ‖z i‖ ^ 2 := by
  simp_rw [planeReal_bwd38]
  rw [parseval38]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_mul, mul_pow, norm_alBwdMul38, sq_abs]; ring

theorem parsevalSec38 (N : ℕ) (z : FourierPlane N) :
    alh38 N * ∑ j : ZMod (2 * N + 1),
        ‖(planeReal N z (alt38 N j + alh38 N) - 2 * planeReal N z (alt38 N j)
            + planeReal N z (alt38 N j - alh38 N)) / (alh38 N : ℂ) ^ 2‖ ^ 2
      = ∑ i : Fin (2 * N + 1), alomega38 N (modeIndex N i) ^ 4 * ‖z i‖ ^ 2 := by
  simp_rw [planeReal_sec38]
  rw [parseval38]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_mul, mul_pow, norm_alSecMul38]; ring

theorem alt38_add_nat (N : ℕ) (j : ZMod (2 * N + 1)) (k : ℕ) (f : ℝ → ℂ)
    (hf : Function.Periodic f 1) :
    f (alt38 N (j + (k : ZMod (2 * N + 1)))) = f (alt38 N j + k * alh38 N) := by
  have hj : j + (k : ZMod (2 * N + 1)) = ((j.val + k : ℕ) : ZMod (2 * N + 1)) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  have hv : (j + (k : ZMod (2 * N + 1))).val = (j.val + k) % (2 * N + 1) := by
    rw [hj, ZMod.val_natCast]
  unfold alt38
  rw [hv]
  have hm := Nat.mod_add_div (j.val + k) (2 * N + 1)
  have key : (((j.val + k) % (2 * N + 1) : ℕ) : ℝ) * alh38 N
      = ((j.val : ℝ) * alh38 N + k * alh38 N) - (((j.val + k) / (2 * N + 1) : ℕ) : ℝ) * 1 := by
    have h1 : (((j.val + k) % (2 * N + 1) : ℕ) : ℝ) = ((j.val + k : ℕ) : ℝ)
        - (2 * (N : ℝ) + 1) * (((j.val + k) / (2 * N + 1) : ℕ) : ℝ) := by
      have : ((j.val + k : ℕ) : ℝ) = (((j.val + k) % (2 * N + 1) : ℕ) : ℝ)
          + (2 * (N : ℝ) + 1) * (((j.val + k) / (2 * N + 1) : ℕ) : ℝ) := by
        exact_mod_cast hm.symm
      linarith
    rw [h1]; push_cast
    have := alh38_mul N
    nlinarith [this]
  rw [key]
  exact hf.sub_nat_mul_eq _

theorem periodic_uniformContinuous38 (f : ℝ → ℂ) (hc : Continuous f)
    (hp : Function.Periodic f 1) : UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hK : IsCompact (Set.Icc (-1 : ℝ) 2) := isCompact_Icc
  have hu := hK.uniformContinuousOn_of_continuous hc.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, hδ'⟩ := hu ε hε
  refine ⟨min δ 1, lt_min hδ one_pos, fun s t hst => ?_⟩
  have hst' : |s - t| < min δ 1 := by simpa [Real.dist_eq] using hst
  have h1 : |s - t| < 1 := lt_of_lt_of_le hst' (min_le_right _ _)
  have h2 : |s - t| < δ := lt_of_lt_of_le hst' (min_le_left _ _)
  set m : ℤ := ⌊s⌋ with hm
  have hs0 : 0 ≤ s - m := by simpa [hm] using Int.floor_le s
  have hs1 : s - m < 1 := by have := Int.lt_floor_add_one s; simp only [hm]; linarith
  have ht := abs_lt.mp h1
  have hfs : f s = f (s - m) := by
    have := hp.sub_int_mul_eq (x := s) m; simpa using this.symm
  have hft : f t = f (t - m) := by
    have := hp.sub_int_mul_eq (x := t) m; simpa using this.symm
  rw [Real.dist_eq] at *
  rw [dist_eq_norm, hfs, hft]
  have := hδ' (s - m) (by constructor <;> linarith) (t - m) (by constructor <;> linarith)
    (by rw [Real.dist_eq]; rw [show s - m - (t - m) = s - t by ring]; exact h2)
  simpa [dist_eq_norm] using this

theorem riemann38 (f : ℝ → ℂ) (hc : Continuous f) (hp : Function.Periodic f 1) :
    Tendsto (fun N : ℕ => (alh38 N : ℂ) * ∑ j : ZMod (2 * N + 1), f (alt38 N j)) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hu := periodic_uniformContinuous38 f hc hp
  rw [Metric.uniformContinuous_iff] at hu
  obtain ⟨δ, hδ, hδ'⟩ := hu (ε / 2) (by linarith)
  obtain ⟨N0, hN0⟩ := exists_nat_gt (1 / δ)
  refine ⟨N0, fun N hN => ?_⟩
  have hh := alh38_pos N
  have hhδ : alh38 N < δ := by
    unfold alh38
    have : 1 / δ < 2 * (N : ℝ) + 1 := by
      have : (N0 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at this
    linarith
  have hL := alh38_mul N
  set L : ℕ := 2 * N + 1 with hLdef
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun m : ℕ => (m : ℝ) * alh38 N)
    (f := f) (μ := MeasureTheory.volume) (n := L)
    (fun k _ => hc.intervalIntegrable _ _)
  have e0 : ((0 : ℕ) : ℝ) * alh38 N = 0 := by simp
  have eL : ((L : ℕ) : ℝ) * alh38 N = 1 := by simpa [hLdef] using hL
  rw [e0, eL] at hsum
  rw [← hsum]
  have hz : ∑ j : ZMod (2 * N + 1), f (alt38 N j) = ∑ m ∈ range L, f ((m : ℝ) * alh38 N) :=
    alsum_zmod38 N (fun m => f ((m : ℝ) * alh38 N))
  rw [hz]
  rw [dist_eq_norm]
  have hterm : ∀ m ∈ range L, ‖(alh38 N : ℂ) * f ((m : ℝ) * alh38 N)
      - ∫ x in ((m : ℝ) * alh38 N)..(((m + 1 : ℕ) : ℝ) * alh38 N), f x‖ ≤ (ε / 2) * alh38 N := by
    intro m _
    have hconst : ∫ x in ((m : ℝ) * alh38 N)..(((m + 1 : ℕ) : ℝ) * alh38 N),
        f ((m : ℝ) * alh38 N) = (alh38 N : ℂ) * f ((m : ℝ) * alh38 N) := by
      rw [intervalIntegral.integral_const]
      simp only [Complex.real_smul]
      congr 1
      push_cast; ring_nf
    have hsub : (alh38 N : ℂ) * f ((m : ℝ) * alh38 N)
        - ∫ x in ((m : ℝ) * alh38 N)..(((m + 1 : ℕ) : ℝ) * alh38 N), f x
        = - ∫ x in ((m : ℝ) * alh38 N)..(((m + 1 : ℕ) : ℝ) * alh38 N),
            (f x - f ((m : ℝ) * alh38 N)) := by
      rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const, hconst]
      ring
    rw [hsub, norm_neg]
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (m : ℝ) * alh38 N) (b := ((m + 1 : ℕ) : ℝ) * alh38 N)
      (f := fun x => f x - f ((m : ℝ) * alh38 N)) (C := ε / 2) (by
        intro x hx
        rw [Set.uIoc_of_le (by push_cast; nlinarith)] at hx
        have hx1 : |x - (m : ℝ) * alh38 N| < δ := by
          rw [abs_lt]; push_cast at hx; constructor <;> nlinarith [hx.1, hx.2]
        have := hδ' (a := x) (b := (m : ℝ) * alh38 N) (by rw [Real.dist_eq]; exact hx1)
        rw [dist_eq_norm] at this
        exact this.le)
    calc _ ≤ ε / 2 * |((m + 1 : ℕ) : ℝ) * alh38 N - (m : ℝ) * alh38 N| := this
      _ = ε / 2 * alh38 N := by
        congr 1; rw [show ((m + 1 : ℕ) : ℝ) * alh38 N - (m : ℝ) * alh38 N = alh38 N by push_cast; ring]
        exact abs_of_pos hh
  have := norm_sum_le_of_le (range L) hterm
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc _ ≤ _ := this
    _ = (L : ℝ) * ((ε / 2) * alh38 N) := by simp
    _ = ε / 2 := by
      have : (L : ℝ) * alh38 N = 1 := eL
      calc (L : ℝ) * ((ε / 2) * alh38 N) = (ε / 2) * ((L : ℝ) * alh38 N) := by ring
        _ = ε / 2 := by rw [this]; ring
    _ < ε := by linarith

def alCoefH1_38 (x : SobolevHilbert 1) (n : ℤ) : ℂ :=
  (show WeightedHilbert (sobolevModeWeight 1) from x) n

theorem alCoefH1_sub38 (x y : SobolevHilbert 1) (n : ℤ) :
    alCoefH1_38 (x - y) n = alCoefH1_38 x n - alCoefH1_38 y n := rfl

def alInF38 (N : ℕ) (x : SobolevHilbert 1) : Prop :=
  ∀ n : ℤ, n ∉ symmetricModes N → alCoefH1_38 x n = 0

theorem alInF_sub38 (N : ℕ) (x y : SobolevHilbert 1) (hx : alInF38 N x) (hy : alInF38 N y) :
    alInF38 N (x - y) := by
  intro n hn
  rw [alCoefH1_sub38, hx n hn, hy n hn]; simp

theorem alInF_mono38 {N M : ℕ} (h : M ≤ N) (x : SobolevHilbert 1) (hx : alInF38 M x) :
    alInF38 N x := by
  intro n hn
  apply hx
  simp only [symmetricModes, Finset.mem_Icc] at hn ⊢
  omega

theorem alProj_inF38 (M : ℕ) (u : SobolevHilbert 1) : alInF38 M (physicalH1FiniteProjection M u) := by
  intro n hn
  have := physicalH1FiniteProjection_fourier M u n
  rw [physicalH1CarrierToL2AfterAcceptedCoordinate_fourier, if_neg hn] at this
  exact this

theorem alProj_eq38 {N : ℕ} {x : SobolevHilbert 1} (hx : alInF38 N x) :
    physicalH1FiniteProjection N x = x := by
  apply Subtype.ext
  funext n
  have h1 := physicalH1FiniteProjection_fourier N x n
  rw [physicalH1CarrierToL2AfterAcceptedCoordinate_fourier] at h1
  by_cases hn : n ∈ symmetricModes N
  · rw [if_pos hn] at h1
    exact h1
  · rw [if_neg hn] at h1
    exact h1.trans (hx n hn).symm

theorem alCanon_eq_plane38 {N : ℕ} {x : SobolevHilbert 1} (hx : alInF38 N x) (y : PhysicalCircle) :
    physicalH1CanonicalContinuousRepresentativeCLM x y
      = planeField N (physicalH1FiniteProjectionPlane N x) y := by
  have := physicalH1CanonicalContinuousRepresentative_finiteProjection_eq_plane N x
  rw [alProj_eq38 hx] at this
  rw [this]; rfl


theorem alWeight1_38 (n : ℤ) : sobolevModeWeight 1 n = 1 + (n : ℝ) ^ 2 :=
  japaneseBracket_h1_weight n

theorem alNormSq_F38 {N : ℕ} {x : SobolevHilbert 1} (hx : alInF38 N x) :
    ‖x‖ ^ 2 = ∑ i : Fin (2 * N + 1), (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) *
      ‖physicalH1FiniteProjectionPlane N x i‖ ^ 2 := by
  have h := weightedHilbert_norm_sq (sobolevModeWeight 1)
    (show WeightedHilbert (sobolevModeWeight 1) from x)
  have h' : ‖x‖ ^ 2 = ∑' n : ℤ, sobolevModeWeight 1 n * ‖alCoefH1_38 x n‖ ^ 2 := h
  rw [h']
  rw [tsum_eq_sum (s := symmetricModes N)]
  · have himg : symmetricModes N = Finset.univ.image (modeIndex N) := by
      ext n
      simp only [symmetricModes, Finset.mem_Icc, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        exact modeIndex_covers N n h1 h2
      · rintro ⟨i, rfl⟩
        exact modeIndex_bounds N i
    rw [himg, Finset.sum_image (fun i _ j _ hij => modeIndex_injective N hij)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [alWeight1_38]; rfl
  · intro n hn
    rw [hx n hn]; simp

/-- Discrete `L²(h)` norm of a grid function. -/
def alGn38 (N : ℕ) (Y : ZMod (2 * N + 1) → ℂ) : ℝ :=
  Real.sqrt (alh38 N * ∑ j, ‖Y j‖ ^ 2)

theorem alGn_nonneg38 (N : ℕ) (Y : ZMod (2 * N + 1) → ℂ) : 0 ≤ alGn38 N Y := Real.sqrt_nonneg _

theorem alGn_sq38 (N : ℕ) (Y : ZMod (2 * N + 1) → ℂ) :
    alGn38 N Y ^ 2 = alh38 N * ∑ j, ‖Y j‖ ^ 2 := by
  unfold alGn38
  rw [Real.sq_sqrt]
  exact mul_nonneg (alh38_pos N).le (Finset.sum_nonneg fun j _ => by positivity)

theorem alGn_eq_pilp38 (N : ℕ) (Y : ZMod (2 * N + 1) → ℂ) :
    alGn38 N Y = Real.sqrt (alh38 N) * ‖(WithLp.toLp 2 Y : PiLp 2 (fun _ : ZMod (2 * N + 1) => ℂ))‖ := by
  unfold alGn38
  rw [PiLp.norm_eq_of_L2, Real.sqrt_mul (alh38_pos N).le]

theorem alGn_add38 (N : ℕ) (Y Y' : ZMod (2 * N + 1) → ℂ) :
    alGn38 N (Y + Y') ≤ alGn38 N Y + alGn38 N Y' := by
  rw [alGn_eq_pilp38, alGn_eq_pilp38, alGn_eq_pilp38, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  exact norm_add_le (WithLp.toLp 2 Y : PiLp 2 (fun _ : ZMod (2 * N + 1) => ℂ)) (WithLp.toLp 2 Y')

theorem alGn_smul_le38 (N : ℕ) (a Y : ZMod (2 * N + 1) → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ j, ‖a j‖ ≤ A) : alGn38 N (fun j => a j * Y j) ≤ A * alGn38 N Y := by
  unfold alGn38
  rw [← Real.sqrt_sq hA, ← Real.sqrt_mul (sq_nonneg A)]
  apply Real.sqrt_le_sqrt
  have : alh38 N * ∑ j, ‖a j * Y j‖ ^ 2 ≤ alh38 N * ∑ j, A ^ 2 * ‖Y j‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (alh38_pos N).le
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha j) 2) (sq_nonneg _)
  calc _ ≤ _ := this
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem alCSgrid38 (N : ℕ) (A B : ZMod (2 * N + 1) → ℂ) :
    alh38 N * ∑ j, ‖A j‖ * ‖B j‖ ≤ alGn38 N A * alGn38 N B := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (ZMod (2 * N + 1)))
    (fun j => ‖A j‖) (fun j => ‖B j‖)
  have hh := alh38_pos N
  unfold alGn38
  have e : Real.sqrt (alh38 N) * Real.sqrt (alh38 N) = alh38 N := Real.mul_self_sqrt hh.le
  calc alh38 N * ∑ j, ‖A j‖ * ‖B j‖
      ≤ alh38 N * (Real.sqrt (∑ j, ‖A j‖ ^ 2) * Real.sqrt (∑ j, ‖B j‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h hh.le
    _ = Real.sqrt (alh38 N * ∑ j, ‖A j‖ ^ 2) * Real.sqrt (alh38 N * ∑ j, ‖B j‖ ^ 2) := by
        rw [Real.sqrt_mul hh.le, Real.sqrt_mul hh.le]
        calc alh38 N * (Real.sqrt (∑ j, ‖A j‖ ^ 2) * Real.sqrt (∑ j, ‖B j‖ ^ 2))
            = (Real.sqrt (alh38 N) * Real.sqrt (alh38 N)) *
              (Real.sqrt (∑ j, ‖A j‖ ^ 2) * Real.sqrt (∑ j, ‖B j‖ ^ 2)) := by rw [e]
          _ = _ := by ring

theorem alQ_diff38 (Q : ℂ → ℂ) (hQ : ∀ a b, ‖Q a - Q b‖ ≤ ‖a - b‖ * (‖a‖ + ‖b‖))
    (N : ℕ) (Y Y' : ZMod (2 * N + 1) → ℂ) :
    ‖(alh38 N : ℂ) * ∑ j, Q (Y j) - (alh38 N : ℂ) * ∑ j, Q (Y' j)‖
      ≤ alGn38 N (fun j => Y j - Y' j) * (alGn38 N Y + alGn38 N Y') := by
  have hh := alh38_pos N
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hh]
  have h1 : ‖∑ j, (Q (Y j) - Q (Y' j))‖ ≤ ∑ j, ‖Y j - Y' j‖ * ‖Y j‖ + ∑ j, ‖Y j - Y' j‖ * ‖Y' j‖ := by
    calc _ ≤ ∑ j, ‖Q (Y j) - Q (Y' j)‖ := norm_sum_le _ _
      _ ≤ ∑ j, (‖Y j - Y' j‖ * ‖Y j‖ + ‖Y j - Y' j‖ * ‖Y' j‖) :=
        Finset.sum_le_sum fun j _ => by
          have := hQ (Y j) (Y' j); linarith [mul_add ‖Y j - Y' j‖ ‖Y j‖ ‖Y' j‖]
      _ = _ := Finset.sum_add_distrib
  have c1 := alCSgrid38 N (fun j => Y j - Y' j) Y
  have c2 := alCSgrid38 N (fun j => Y j - Y' j) Y'
  calc alh38 N * ‖∑ j, (Q (Y j) - Q (Y' j))‖
      ≤ alh38 N * (∑ j, ‖Y j - Y' j‖ * ‖Y j‖ + ∑ j, ‖Y j - Y' j‖ * ‖Y' j‖) :=
        mul_le_mul_of_nonneg_left h1 hh.le
    _ = alh38 N * ∑ j, ‖Y j - Y' j‖ * ‖Y j‖ + alh38 N * ∑ j, ‖Y j - Y' j‖ * ‖Y' j‖ := by ring
    _ ≤ _ := by nlinarith [c1, c2]

/-- The canonical continuous representative of an `H¹` element, as a function on `ℝ`. -/
def alCanon38 (x : SobolevHilbert 1) (t : ℝ) : ℂ :=
  physicalH1CanonicalContinuousRepresentativeCLM x (t : PhysicalCircle)

theorem alCanon_periodic38 (x : SobolevHilbert 1) : Function.Periodic (alCanon38 x) 1 := by
  intro t
  simp only [alCanon38, AddCircle.coe_add_period]

theorem alCanon_cont38 (x : SobolevHilbert 1) : Continuous (alCanon38 x) :=
  (physicalH1CanonicalContinuousRepresentativeCLM x).continuous.comp
    (continuous_quotient_mk' : Continuous ((↑) : ℝ → PhysicalCircle))

theorem alCanon_sub38 (x y : SobolevHilbert 1) (t : ℝ) :
    alCanon38 (x - y) t = alCanon38 x t - alCanon38 y t := by
  simp [alCanon38, map_sub]

theorem alCanon_norm_le38 (x : SobolevHilbert 1) (t : ℝ) :
    ‖alCanon38 x t‖ ≤ ‖x‖ * ‖reciprocalBracketL2‖ := by
  calc ‖alCanon38 x t‖ ≤ ‖physicalH1CanonicalContinuousRepresentativeCLM x‖ :=
        ContinuousMap.norm_coe_le_norm _ _
    _ ≤ _ := physicalH1CarrierContinuousAfterAcceptedCoordinate_norm_le x

/-- Forward difference quotient of the sampled field. -/
def alFd38 (N : ℕ) (x : SobolevHilbert 1) (j : ZMod (2 * N + 1)) : ℂ :=
  (alCanon38 x (alt38 N j + alh38 N) - alCanon38 x (alt38 N j)) / (alh38 N : ℂ)

/-- Backward difference quotient of the sampled field. -/
def alBd38 (N : ℕ) (x : SobolevHilbert 1) (j : ZMod (2 * N + 1)) : ℂ :=
  (alCanon38 x (alt38 N j) - alCanon38 x (alt38 N j - alh38 N)) / (alh38 N : ℂ)

theorem alFd_sub38 (N : ℕ) (x y : SobolevHilbert 1) (j : ZMod (2 * N + 1)) :
    alFd38 N (x - y) j = alFd38 N x j - alFd38 N y j := by
  unfold alFd38; rw [alCanon_sub38, alCanon_sub38]; ring

theorem alBd_sub38 (N : ℕ) (x y : SobolevHilbert 1) (j : ZMod (2 * N + 1)) :
    alBd38 N (x - y) j = alBd38 N x j - alBd38 N y j := by
  unfold alBd38; rw [alCanon_sub38, alCanon_sub38]; ring

theorem alCanon_plane38 {N : ℕ} {x : SobolevHilbert 1} (hx : alInF38 N x) (t : ℝ) :
    alCanon38 x t = planeReal N (physicalH1FiniteProjectionPlane N x) t := by
  unfold alCanon38 planeReal
  exact alCanon_eq_plane38 hx _

theorem alOmega_sq_le38 (N : ℕ) (k : ℤ) :
    alomega38 N k ^ 2 ≤ (2 * Real.pi) ^ 2 * (1 + (k : ℝ) ^ 2) := by
  have h := abs_alomega_le38 N k
  have h0 := abs_nonneg (alomega38 N k)
  have : alomega38 N k ^ 2 = |alomega38 N k| ^ 2 := (sq_abs _).symm
  rw [this]
  calc |alomega38 N k| ^ 2 ≤ (2 * Real.pi * |(k : ℝ)|) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = (2 * Real.pi) ^ 2 * (k : ℝ) ^ 2 := by rw [mul_pow, sq_abs]
    _ ≤ _ := by nlinarith [sq_nonneg (2 * Real.pi), sq_nonneg (k : ℝ)]

theorem alFd_gn38 {N : ℕ} {x : SobolevHilbert 1} (hx : alInF38 N x) :
    alGn38 N (alFd38 N x) ≤ 2 * Real.pi * ‖x‖ := by
  have h1 : alGn38 N (alFd38 N x) ^ 2 ≤ (2 * Real.pi * ‖x‖) ^ 2 := by
    rw [alGn_sq38]
    have : ∀ j, alFd38 N x j = (planeReal N (physicalH1FiniteProjectionPlane N x) (alt38 N j + alh38 N)
        - planeReal N (physicalH1FiniteProjectionPlane N x) (alt38 N j)) / (alh38 N : ℂ) := by
      intro j; unfold alFd38; rw [alCanon_plane38 hx, alCanon_plane38 hx]
    simp_rw [this]
    rw [parsevalFwd38, mul_pow, alNormSq_F38 hx, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc _ ≤ (2 * Real.pi) ^ 2 * (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) * ‖physicalH1FiniteProjectionPlane N x i‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (alOmega_sq_le38 N _) (sq_nonneg _)
      _ = _ := by ring
  exact le_of_sq_le_sq (by simpa using h1) (by positivity)

theorem alBd_gn38 {N : ℕ} {x : SobolevHilbert 1} (hx : alInF38 N x) :
    alGn38 N (alBd38 N x) ≤ 2 * Real.pi * ‖x‖ := by
  have h1 : alGn38 N (alBd38 N x) ^ 2 ≤ (2 * Real.pi * ‖x‖) ^ 2 := by
    rw [alGn_sq38]
    have : ∀ j, alBd38 N x j = (planeReal N (physicalH1FiniteProjectionPlane N x) (alt38 N j)
        - planeReal N (physicalH1FiniteProjectionPlane N x) (alt38 N j - alh38 N)) / (alh38 N : ℂ) := by
      intro j; unfold alBd38; rw [alCanon_plane38 hx, alCanon_plane38 hx]
    simp_rw [this]
    rw [parsevalBwd38, mul_pow, alNormSq_F38 hx, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc _ ≤ (2 * Real.pi) ^ 2 * (1 + ((modeIndex N i : ℤ) : ℝ) ^ 2) * ‖physicalH1FiniteProjectionPlane N x i‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (alOmega_sq_le38 N _) (sq_nonneg _)
      _ = _ := by ring
  exact le_of_sq_le_sq (by simpa using h1) (by positivity)

section Sec_b3
open Finset Filter Topology NlsGge.Pilot NlsGge.Analysis

theorem alPlaneNorm_le38 (M : ℕ) (z : FourierPlane M) (t : ℝ) :
    ‖planeReal M z t‖ ≤ ∑ i, ‖z i‖ := by
  rw [planeReal_eq38]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  have : ‖Complex.exp (2 * Real.pi * Complex.I * ((modeIndex M i : ℤ) : ℂ) * (t : ℂ))‖ = 1 := by
    have e : 2 * Real.pi * Complex.I * ((modeIndex M i : ℤ) : ℂ) * (t : ℂ)
        = Complex.I * ((2 * Real.pi * (modeIndex M i : ℤ) * t : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_exp_I_mul_ofReal]
  rw [this, mul_one]

theorem alNormH38 (h : ℝ) (hh : 0 < h) (k : ℤ) :
    ‖(h : ℂ) * (2 * Real.pi * Complex.I * (k : ℂ))‖ = h * (2 * Real.pi * |(k : ℝ)|) := by
  have : (h : ℂ) * (2 * Real.pi * Complex.I * (k : ℂ)) = Complex.I * ((h * (2 * Real.pi * k) : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos hh, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_two]

/-- Error of the forward difference quotient of a fixed trigonometric polynomial. -/
theorem alPlaneFwdErr38 (M : ℕ) (z : FourierPlane M) (h : ℝ) (hh : 0 < h)
    (hM : ∀ i, |2 * Real.pi * (modeIndex M i : ℤ) * h| ≤ 1) (t : ℝ) :
    ‖(planeReal M z (t + h) - planeReal M z t) / (h : ℂ) - planeReal M (derivativePlane M z) t‖
      ≤ h * ∑ i, ‖z i‖ * (2 * Real.pi * |((modeIndex M i : ℤ) : ℝ)|) ^ 2 := by
  have e : (planeReal M z (t + h) - planeReal M z t) / (h : ℂ) - planeReal M (derivativePlane M z) t
      = ∑ i, (z i * Complex.exp (2 * Real.pi * Complex.I * ((modeIndex M i : ℤ) : ℂ) * (t : ℂ))) *
        ((Complex.exp (h * (2 * Real.pi * Complex.I * ((modeIndex M i : ℤ) : ℂ))) - 1
          - h * (2 * Real.pi * Complex.I * ((modeIndex M i : ℤ) : ℂ))) / (h : ℂ)) := by
    unfold derivativePlane
    rw [planeReal_eq38, planeReal_eq38, planeReal_eq38, ← Finset.sum_sub_distrib, Finset.sum_div,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [alExpShift38]
    have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    field_simp
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  have hexp : ‖Complex.exp (2 * Real.pi * Complex.I * ((modeIndex M i : ℤ) : ℂ) * (t : ℂ))‖ = 1 := by
    have e : 2 * Real.pi * Complex.I * ((modeIndex M i : ℤ) : ℂ) * (t : ℂ)
        = Complex.I * ((2 * Real.pi * (modeIndex M i : ℤ) * t : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_exp_I_mul_ofReal]
  rw [hexp, mul_one]
  have hx : ‖(h : ℂ) * (2 * Real.pi * Complex.I * ((modeIndex M i : ℤ) : ℂ))‖ ≤ 1 := by
    rw [alNormH38 h hh]
    have := hM i
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hh, abs_two] at this
    nlinarith [this]
  have hb := Complex.norm_exp_sub_one_sub_id_le hx
  rw [alNormH38 h hh] at hb
  rw [mul_div_assoc']
  have : ‖z i‖ * (‖Complex.exp (↑h * (2 * ↑Real.pi * Complex.I * ↑(modeIndex M i))) - 1
        - ↑h * (2 * ↑Real.pi * Complex.I * ↑(modeIndex M i))‖ / h)
      ≤ ‖z i‖ * ((h * (2 * Real.pi * |((modeIndex M i : ℤ) : ℝ)|)) ^ 2 / h) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb hh.le) (norm_nonneg _)
  rw [← mul_div_assoc] at this
  refine this.trans (le_of_eq ?_)
  field_simp

/-- Error of the backward difference quotient of a fixed trigonometric polynomial. -/
theorem alPlaneBwdErr38 (M : ℕ) (z : FourierPlane M) (h : ℝ) (hh : 0 < h)
    (hM : ∀ i, |2 * Real.pi * (modeIndex M i : ℤ) * h| ≤ 1) (t : ℝ) :
    ‖(planeReal M z t - planeReal M z (t - h)) / (h : ℂ) - planeReal M (derivativePlane M z) t‖
      ≤ h * ∑ i, ‖z i‖ * (2 * Real.pi * |((modeIndex M i : ℤ) : ℝ)|) ^ 2 := by
  have e : (planeReal M z t - planeReal M z (t - h)) / (h : ℂ) - planeReal M (derivativePlane M z) t
      = ∑ i, (z i * Complex.exp (2 * Real.pi * Complex.I * ((modeIndex M i : ℤ) : ℂ) * (t : ℂ))) *
        ((Complex.exp (((-h : ℝ) : ℂ) * (2 * Real.pi * Complex.I * ((modeIndex M i : ℤ) : ℂ))) - 1
          - ((-h : ℝ) : ℂ) * (2 * Real.pi * Complex.I * ((modeIndex M i : ℤ) : ℂ))) / (-(h : ℂ))) := by
    unfold derivativePlane
    rw [planeReal_eq38, planeReal_eq38, planeReal_eq38, ← Finset.sum_sub_distrib, Finset.sum_div,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_eq_add_neg t, alExpShift38]
    have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    push_cast
    field_simp
    ring
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, norm_mul, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  have hexp : ‖Complex.exp (2 * Real.pi * Complex.I * ((modeIndex M i : ℤ) : ℂ) * (t : ℂ))‖ = 1 := by
    have e : 2 * Real.pi * Complex.I * ((modeIndex M i : ℤ) : ℂ) * (t : ℂ)
        = Complex.I * ((2 * Real.pi * (modeIndex M i : ℤ) * t : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_exp_I_mul_ofReal]
  rw [hexp, mul_one]
  have hnn : ‖((-h : ℝ) : ℂ) * (2 * Real.pi * Complex.I * ((modeIndex M i : ℤ) : ℂ))‖
      = h * (2 * Real.pi * |((modeIndex M i : ℤ) : ℝ)|) := by
    rw [Complex.ofReal_neg, neg_mul, norm_neg, alNormH38 h hh]
  have hx : ‖((-h : ℝ) : ℂ) * (2 * Real.pi * Complex.I * ((modeIndex M i : ℤ) : ℂ))‖ ≤ 1 := by
    rw [hnn]
    have := hM i
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hh, abs_two] at this
    nlinarith [this]
  have hb := Complex.norm_exp_sub_one_sub_id_le hx
  rw [hnn] at hb
  rw [mul_div_assoc']
  have : ‖z i‖ * (‖Complex.exp (((-h : ℝ) : ℂ) * (2 * Real.pi * Complex.I * ((modeIndex M i : ℤ) : ℂ))) - 1
        - ((-h : ℝ) : ℂ) * (2 * Real.pi * Complex.I * ((modeIndex M i : ℤ) : ℂ))‖ / h)
      ≤ ‖z i‖ * ((h * (2 * Real.pi * |((modeIndex M i : ℤ) : ℝ)|)) ^ 2 / h) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hb hh.le) (norm_nonneg _)
  rw [← mul_div_assoc] at this
  refine this.trans (le_of_eq ?_)
  field_simp
end Sec_b3

section Sec_b4
open Finset Filter Topology NlsGge.Pilot NlsGge.Analysis MeasureTheory
open scoped ENNReal

local instance alProb38 : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- Multiplication of an `L²` field by a continuous field (the CLM used in the `Q₄` pieces). -/
abbrev alMult38 : C(PhysicalCircle, ℂ) →L[ℂ] (PhysicalL2 →L[ℂ] PhysicalL2) :=
  physicalContinuousFieldMultiplierCLMAfterHolderInnerPrerequisites

theorem alMult_ae38 (γ : C(PhysicalCircle, ℂ)) (d : PhysicalL2) :
    ((alMult38 γ d : PhysicalL2) : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] fun y => γ y * d y := by
  change (((ContinuousLinearMap.mul ℂ ℂ).holder 2
      (ContinuousMap.toLp ∞ spatialMeasure ℂ γ) d : PhysicalL2) :
        PhysicalCircle → ℂ) =ᵐ[spatialMeasure] fun y => γ y * d y
  exact physicalContinuousHolderField_coe_ae γ d

theorem alMult_norm_sq38 (γ : C(PhysicalCircle, ℂ)) (d : PhysicalL2) :
    ‖alMult38 γ d‖ ^ 2 = ∫ y : PhysicalCircle, ‖γ y‖ ^ 2 * ‖d y‖ ^ 2 ∂spatialMeasure := by
  let m : PhysicalL2 := alMult38 γ d
  have hm := alMult_ae38 γ d
  have hnorm : ‖m‖ ^ 2 =
      ∫ y : PhysicalCircle, ‖(m : PhysicalCircle → ℂ) y‖ ^ 2 ∂spatialMeasure := by
    calc
      ‖m‖ ^ 2 = Complex.re (inner ℂ m m) := norm_sq_eq_re_inner (𝕜 := ℂ) m
      _ = Complex.re (∫ y : PhysicalCircle,
          inner ℂ ((m : PhysicalCircle → ℂ) y) ((m : PhysicalCircle → ℂ) y)
            ∂spatialMeasure) := by rw [L2.inner_def]
      _ = ∫ y : PhysicalCircle,
          Complex.re (inner ℂ ((m : PhysicalCircle → ℂ) y)
            ((m : PhysicalCircle → ℂ) y)) ∂spatialMeasure := by
        change Complex.reCLM (∫ y : PhysicalCircle,
          inner ℂ ((m : PhysicalCircle → ℂ) y) ((m : PhysicalCircle → ℂ) y)
            ∂spatialMeasure) = _
        rw [← ContinuousLinearMap.integral_comp_comm Complex.reCLM
          (L2.integrable_inner m m)]
        simp only [Complex.reCLM_apply]
      _ = ∫ y : PhysicalCircle, ‖(m : PhysicalCircle → ℂ) y‖ ^ 2
          ∂spatialMeasure := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y =>
          complex_inner_self_re_eq_norm_sq_actual ((m : PhysicalCircle → ℂ) y)
  change ‖m‖ ^ 2 = _
  rw [hnorm]
  apply integral_congr_ae
  filter_upwards [hm] with y hy
  rw [hy]
  simp only [Complex.norm_mul]
  ring

theorem alMult_prod_integral38 (γ : C(PhysicalCircle, ℂ)) (d : PhysicalL2) :
    MeasureTheory.L1.integral (physicalL2ProductL1CLM (alMult38 γ d) (alMult38 γ d))
      = ∫ y : PhysicalCircle, (γ y * d y) ^ 2 ∂spatialMeasure := by
  let v : PhysicalL2 := alMult38 γ d
  have hv := alMult_ae38 γ d
  have hprod := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    (r := (1 : ℝ≥0∞)) v v
  calc
    _ = ∫ y : PhysicalCircle,
        ((physicalL2ProductL1CLM v v : Lp ℂ 1 spatialMeasure) :
          PhysicalCircle → ℂ) y ∂spatialMeasure := by
      rw [MeasureTheory.L1.integral_eq_integral]
    _ = ∫ y : PhysicalCircle, (γ y * d y) ^ 2 ∂spatialMeasure := by
      apply integral_congr_ae
      filter_upwards [hprod, hv] with y hprod hv
      change ((physicalL2ProductL1CLM v v : Lp ℂ 1 spatialMeasure) :
        PhysicalCircle → ℂ) y = v y * v y at hprod
      change (v : PhysicalCircle → ℂ) y = γ y * d y at hv
      rw [hprod, hv]
      ring

theorem alPlane_ae38 (M : ℕ) (c : FourierPlane M) :
    (planeL2 M c : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] planeField M c := planeL2_ae M c

theorem alI1_classical38 (γ : C(PhysicalCircle, ℂ)) (M : ℕ) (c : FourierPlane M) :
    (((‖alMult38 γ (planeL2 M c)‖ ^ 2 : ℝ)) : ℂ)
      = ∫ t in (0 : ℝ)..1, (((‖γ (t : PhysicalCircle) * planeReal M c t‖ ^ 2 : ℝ)) : ℂ) := by
  rw [alMult_norm_sq38]
  have h1 : (∫ y : PhysicalCircle, ‖γ y‖ ^ 2 * ‖(planeL2 M c : PhysicalCircle → ℂ) y‖ ^ 2 ∂spatialMeasure)
      = ∫ y : PhysicalCircle, ‖γ y * planeField M c y‖ ^ 2 ∂spatialMeasure := by
    apply integral_congr_ae
    filter_upwards [alPlane_ae38 M c] with y hy
    rw [hy, norm_mul]; ring
  rw [h1]
  have h2 := NlsGge.HierarchyRiccati.unitIntervalIntegral_lift_eq_spatialHaar
    (fun y : PhysicalCircle => (((‖γ y * planeField M c y‖ ^ 2 : ℝ)) : ℂ))
  rw [integral_complex_ofReal] at h2
  exact h2.symm

theorem alI2_classical38 (γ : C(PhysicalCircle, ℂ)) (M : ℕ) (c : FourierPlane M) :
    MeasureTheory.L1.integral (physicalL2ProductL1CLM (alMult38 γ (planeL2 M c))
        (alMult38 γ (planeL2 M c)))
      = ∫ t in (0 : ℝ)..1, (γ (t : PhysicalCircle) * planeReal M c t) ^ 2 := by
  rw [alMult_prod_integral38]
  have h1 : (∫ y : PhysicalCircle, (γ y * (planeL2 M c : PhysicalCircle → ℂ) y) ^ 2 ∂spatialMeasure)
      = ∫ y : PhysicalCircle, (γ y * planeField M c y) ^ 2 ∂spatialMeasure := by
    apply integral_congr_ae
    filter_upwards [alPlane_ae38 M c] with y hy
    rw [hy]
  rw [h1]
  exact (NlsGge.HierarchyRiccati.unitIntervalIntegral_lift_eq_spatialHaar
    (fun y : PhysicalCircle => (γ y * planeField M c y) ^ 2)).symm
end Sec_b4

section Sec_b5
open Finset Filter Topology NlsGge.Pilot NlsGge.Analysis

theorem alApprox38 {S : ℕ → ℂ} {SM : ℕ → ℕ → ℂ} {IM : ℕ → ℂ} {I : ℂ}
    (hI : Tendsto IM atTop (𝓝 I))
    (hSM : ∀ M, Tendsto (fun N => SM N M) atTop (𝓝 (IM M)))
    (C : ℝ) (hC : 0 ≤ C) (a b : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0))
    (hbd : ∃ M0, ∀ M, M0 ≤ M → ∀ᶠ N in atTop, ‖S N - SM N M‖ ≤ C * (a N + b M)) :
    Tendsto S atTop (𝓝 I) := by
  obtain ⟨M0, hM0⟩ := hbd
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1 : ∀ᶠ M in atTop, dist (IM M) I < ε / 4 := (Metric.tendsto_nhds.mp hI) (ε / 4) (by linarith)
  have h2 : ∀ᶠ M in atTop, C * b M < ε / 4 := by
    have := (hb.const_mul C)
    rw [mul_zero] at this
    exact (Metric.tendsto_nhds.mp this) (ε / 4) (by linarith) |>.mono fun M hM => by
      rw [Real.dist_eq, sub_zero] at hM; exact (abs_lt.mp hM).2
  obtain ⟨M1, hM1⟩ := eventually_atTop.mp (h1.and (h2.and (eventually_ge_atTop M0)))
  obtain ⟨hM1a, hM1b, hM1c⟩ := hM1 M1 le_rfl
  have h3 : ∀ᶠ N in atTop, dist (SM N M1) (IM M1) < ε / 4 :=
    (Metric.tendsto_nhds.mp (hSM M1)) (ε / 4) (by linarith)
  have h4 : ∀ᶠ N in atTop, C * a N < ε / 4 := by
    have := (ha.const_mul C)
    rw [mul_zero] at this
    exact (Metric.tendsto_nhds.mp this) (ε / 4) (by linarith) |>.mono fun M hM => by
      rw [Real.dist_eq, sub_zero] at hM; exact (abs_lt.mp hM).2
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (h3.and (h4.and (hM0 M1 hM1c)))
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨c3, c4, c5⟩ := hN0 N hN
  rw [dist_eq_norm] at c3 hM1a ⊢
  calc ‖S N - I‖ = ‖(S N - SM N M1) + (SM N M1 - IM M1) + (IM M1 - I)‖ := by ring_nf
    _ ≤ ‖S N - SM N M1‖ + ‖SM N M1 - IM M1‖ + ‖IM M1 - I‖ := norm_add₃_le
    _ < ε := by
      have : C * (a N + b M1) = C * a N + C * b M1 := by ring
      linarith

theorem alQ_sup38 (Q : ℂ → ℂ) (hQ : ∀ a b, ‖Q a - Q b‖ ≤ ‖a - b‖ * (‖a‖ + ‖b‖))
    (N : ℕ) (Y Z : ZMod (2 * N + 1) → ℂ) (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hYZ : ∀ j, ‖Y j - Z j‖ ≤ δ) (hY : ∀ j, ‖Y j‖ ≤ B) (hZ : ∀ j, ‖Z j‖ ≤ B) :
    ‖(alh38 N : ℂ) * ∑ j, Q (Y j) - (alh38 N : ℂ) * ∑ j, Q (Z j)‖ ≤ δ * (2 * B) := by
  have hh := alh38_pos N
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hh]
  have : ‖∑ j, (Q (Y j) - Q (Z j))‖ ≤ ∑ _j : ZMod (2 * N + 1), δ * (2 * B) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (hQ _ _).trans ?_
    exact mul_le_mul (hYZ j) (by linarith [hY j, hZ j]) (by positivity) hδ
  have hL : (Finset.univ : Finset (ZMod (2 * N + 1))).card = 2 * N + 1 := by
    simp [ZMod.card]
  rw [Finset.sum_const, hL, nsmul_eq_mul] at this
  calc alh38 N * ‖∑ j, (Q (Y j) - Q (Z j))‖ ≤ alh38 N * (((2 * N + 1 : ℕ) : ℝ) * (δ * (2 * B))) :=
        mul_le_mul_of_nonneg_left this hh.le
    _ = ((2 * (N : ℝ) + 1) * alh38 N) * (δ * (2 * B)) := by push_cast; ring
    _ = δ * (2 * B) := by rw [alh38_mul]; ring

theorem alh_tendsto38 : Tendsto alh38 atTop (𝓝 0) := by
  unfold alh38
  have : Tendsto (fun N : ℕ => 2 * (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  exact tendsto_const_nhds.div_atTop this

theorem alGnY38 (N : ℕ) (a b e1 e2 : ZMod (2 * N + 1) → ℂ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ j, ‖a j‖ ≤ A) (hb : ∀ j, ‖b j‖ ≤ B) :
    alGn38 N (fun j => a j * e1 j + b j * e2 j) ≤ A * alGn38 N e1 + B * alGn38 N e2 := by
  have h := alGn_add38 N (fun j => a j * e1 j) (fun j => b j * e2 j)
  have h1 := alGn_smul_le38 N a e1 A hA ha
  have h2 := alGn_smul_le38 N b e2 B hB hb
  exact (le_trans (le_of_eq rfl) h).trans (add_le_add h1 h2)

theorem alGnYF38 {N : ℕ} {x : SobolevHilbert 1} (hx : alInF38 N x)
    (a b : ZMod (2 * N + 1) → ℂ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ j, ‖a j‖ ≤ A) (hb : ∀ j, ‖b j‖ ≤ B) :
    alGn38 N (fun j => a j * alFd38 N x j + b j * alBd38 N x j) ≤ (A + B) * (2 * Real.pi * ‖x‖) := by
  refine (alGnY38 N a b _ _ A B hA hB ha hb).trans ?_
  have h1 := alFd_gn38 hx
  have h2 := alBd_gn38 hx
  nlinarith [mul_le_mul_of_nonneg_left h1 hA, mul_le_mul_of_nonneg_left h2 hB]

theorem alGCbound38 (Q : ℂ → ℂ) (hQ : ∀ a b, ‖Q a - Q b‖ ≤ ‖a - b‖ * (‖a‖ + ‖b‖))
    {N : ℕ} {x y : SobolevHilbert 1} (hx : alInF38 N x) (hy : alInF38 N y)
    (a b : ZMod (2 * N + 1) → ℂ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ j, ‖a j‖ ≤ A) (hb : ∀ j, ‖b j‖ ≤ B) :
    ‖(alh38 N : ℂ) * ∑ j, Q (a j * alFd38 N x j + b j * alBd38 N x j)
      - (alh38 N : ℂ) * ∑ j, Q (a j * alFd38 N y j + b j * alBd38 N y j)‖
      ≤ ((A + B) * (2 * Real.pi * ‖x - y‖)) * ((A + B) * (2 * Real.pi * ‖x‖) + (A + B) * (2 * Real.pi * ‖y‖)) := by
  refine (alQ_diff38 Q hQ N _ _).trans ?_
  have hxy := alInF_sub38 N x y hx hy
  have e : (fun j => (a j * alFd38 N x j + b j * alBd38 N x j) - (a j * alFd38 N y j + b j * alBd38 N y j))
      = fun j => a j * alFd38 N (x - y) j + b j * alBd38 N (x - y) j := by
    funext j; rw [alFd_sub38, alBd_sub38]; ring
  rw [e]
  have h1 := alGnYF38 hxy a b A B hA hB ha hb
  have h2 := alGnYF38 hx a b A B hA hB ha hb
  have h3 := alGnYF38 hy a b A B hA hB ha hb
  exact mul_le_mul h1 (add_le_add h2 h3) (add_nonneg (alGn_nonneg38 _ _) (alGn_nonneg38 _ _))
    (by positivity)

theorem alCoe_periodic38 (γ : C(PhysicalCircle, ℂ)) :
    Function.Periodic (fun t : ℝ => γ (t : PhysicalCircle)) 1 := by
  intro t
  simp only [AddCircle.coe_add_period]

theorem alCoe_continuous38 (γ : C(PhysicalCircle, ℂ)) :
    Continuous (fun t : ℝ => γ (t : PhysicalCircle)) :=
  γ.continuous.comp (continuous_quotient_mk' : Continuous ((↑) : ℝ → PhysicalCircle))

theorem alPlane_continuous38 (M : ℕ) (z : FourierPlane M) : Continuous (planeReal M z) :=
  (contDiff_planeReal M z).continuous

set_option maxHeartbeats 1600000 in
/-- Limit of the sampled quadratic expression for a fixed trigonometric polynomial. -/
theorem alSmooth38 (Q : ℂ → ℂ) (hQ : ∀ a b, ‖Q a - Q b‖ ≤ ‖a - b‖ * (‖a‖ + ‖b‖))
    (hQc : Continuous Q) (M : ℕ) (cM : FourierPlane M) (α β : C(PhysicalCircle, ℂ))
    (a b : (N : ℕ) → ZMod (2 * N + 1) → ℂ)
    (ha : ∀ ε > 0, ∀ᶠ N in atTop, ∀ j, ‖a N j - α (alt38 N j : PhysicalCircle)‖ < ε)
    (hb : ∀ ε > 0, ∀ᶠ N in atTop, ∀ j, ‖b N j - β (alt38 N j : PhysicalCircle)‖ < ε) :
    Tendsto (fun N : ℕ => (alh38 N : ℂ) * ∑ j : ZMod (2 * N + 1),
      Q (a N j * ((planeReal M cM (alt38 N j + alh38 N) - planeReal M cM (alt38 N j)) / (alh38 N : ℂ))
        + b N j * ((planeReal M cM (alt38 N j) - planeReal M cM (alt38 N j - alh38 N)) / (alh38 N : ℂ))))
      atTop (𝓝 (∫ t in (0 : ℝ)..1,
        Q ((α + β) (t : PhysicalCircle) * planeReal M (derivativePlane M cM) t))) := by
  set z' : FourierPlane M := derivativePlane M cM with hz'
  set γ : C(PhysicalCircle, ℂ) := α + β with hγ
  have hFc : Continuous (fun t : ℝ => Q (γ (t : PhysicalCircle) * planeReal M z' t)) :=
    hQc.comp ((alCoe_continuous38 γ).mul (alPlane_continuous38 M z'))
  have hFp : Function.Periodic (fun t : ℝ => Q (γ (t : PhysicalCircle) * planeReal M z' t)) 1 := by
    intro t
    simp only [alCoe_periodic38 γ t, planeReal_periodic M z' t]
  have hR := riemann38 _ hFc hFp
  set P' : ℝ := ∑ i, ‖z' i‖ with hP'
  set Cm : ℝ := ∑ i, ‖cM i‖ * (2 * Real.pi * |((modeIndex M i : ℤ) : ℝ)|) ^ 2 with hCm
  have hP'0 : 0 ≤ P' := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hCm0 : 0 ≤ Cm := Finset.sum_nonneg fun i _ => by positivity
  set A1 : ℝ := ‖α‖ + 1 with hA1
  set B1 : ℝ := ‖β‖ + 1 with hB1
  set G : ℝ := ‖α‖ + ‖β‖ with hG
  have hA10 : 0 ≤ A1 := by positivity
  have hB10 : 0 ≤ B1 := by positivity
  have hG0 : 0 ≤ G := by positivity
  set B : ℝ := (A1 + B1) * (P' + Cm) + G * P' with hBdef
  have hB0 : 0 ≤ B := by positivity
  -- difference tends to zero
  have hdiff : Tendsto (fun N : ℕ => (alh38 N : ℂ) * ∑ j : ZMod (2 * N + 1),
      Q (a N j * ((planeReal M cM (alt38 N j + alh38 N) - planeReal M cM (alt38 N j)) / (alh38 N : ℂ))
        + b N j * ((planeReal M cM (alt38 N j) - planeReal M cM (alt38 N j - alh38 N)) / (alh38 N : ℂ)))
      - (alh38 N : ℂ) * ∑ j : ZMod (2 * N + 1),
        Q (γ (alt38 N j : PhysicalCircle) * planeReal M z' (alt38 N j))) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    set δ : ℝ := min η 1 / (4 * (B + 1)) with hδ
    have hmin0 : 0 < min η 1 := lt_min hη one_pos
    have hδ0 : 0 < δ := by positivity
    have hδ1 : δ ≤ 1 := by
      rw [hδ, div_le_one (by positivity)]
      nlinarith [min_le_right η 1]
    set ε : ℝ := δ / (4 * (P' + 1)) with hε
    have hε0 : 0 < ε := by positivity
    have e1 : ∀ᶠ N in atTop, alh38 N ≤ δ / (2 * ((A1 + B1) * Cm + 1)) := by
      have hpos : 0 < δ / (2 * ((A1 + B1) * Cm + 1)) := by positivity
      exact (alh_tendsto38.eventually (Iic_mem_nhds hpos))
    have e2 : ∀ᶠ N in atTop, alh38 N ≤ 1 := alh_tendsto38.eventually (Iic_mem_nhds one_pos)
    have e3 : ∀ᶠ N in atTop, alh38 N ≤ 1 / (2 * Real.pi * M + 1) :=
      alh_tendsto38.eventually (Iic_mem_nhds (by positivity))
    filter_upwards [e1, e2, e3, ha ε hε0, hb ε hε0, ha 1 one_pos, hb 1 one_pos] with
      N h1 h2 h3 hNa hNb hNa1 hNb1
    have hh := alh38_pos N
    have hM : ∀ i, |2 * Real.pi * (modeIndex M i : ℤ) * alh38 N| ≤ 1 := by
      intro i
      have hbd := modeIndex_bounds M i
      have hn : |((modeIndex M i : ℤ) : ℝ)| ≤ M := by
        rw [abs_le]; constructor <;> [skip; skip] <;> (norm_cast; omega)
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hh, abs_two]
      have : 2 * Real.pi * |((modeIndex M i : ℤ) : ℝ)| ≤ 2 * Real.pi * M :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      calc 2 * Real.pi * |((modeIndex M i : ℤ) : ℝ)| * alh38 N ≤ (2 * Real.pi * M) * alh38 N :=
            mul_le_mul_of_nonneg_right this hh.le
        _ ≤ (2 * Real.pi * M) * (1 / (2 * Real.pi * M + 1)) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ ≤ 1 := by
            rw [mul_one_div, div_le_one (by positivity)]; linarith
    set Y : ZMod (2 * N + 1) → ℂ := fun j => a N j *
        ((planeReal M cM (alt38 N j + alh38 N) - planeReal M cM (alt38 N j)) / (alh38 N : ℂ))
        + b N j * ((planeReal M cM (alt38 N j) - planeReal M cM (alt38 N j - alh38 N)) / (alh38 N : ℂ)) with hY
    set Z : ZMod (2 * N + 1) → ℂ := fun j => γ (alt38 N j : PhysicalCircle) *
        planeReal M z' (alt38 N j) with hZ
    have hp'b : ∀ t, ‖planeReal M z' t‖ ≤ P' := fun t => alPlaneNorm_le38 M z' t
    have hγb : ∀ t : ℝ, ‖γ (t : PhysicalCircle)‖ ≤ G := by
      intro t
      calc ‖γ (t : PhysicalCircle)‖ = ‖α (t : PhysicalCircle) + β (t : PhysicalCircle)‖ := rfl
        _ ≤ ‖α (t : PhysicalCircle)‖ + ‖β (t : PhysicalCircle)‖ := norm_add_le _ _
        _ ≤ ‖α‖ + ‖β‖ := add_le_add (ContinuousMap.norm_coe_le_norm _ _) (ContinuousMap.norm_coe_le_norm _ _)
    have hZb : ∀ j, ‖Z j‖ ≤ B := by
      intro j
      calc ‖Z j‖ = ‖γ (alt38 N j : PhysicalCircle)‖ * ‖planeReal M z' (alt38 N j)‖ := norm_mul _ _
        _ ≤ G * P' := mul_le_mul (hγb _) (hp'b _) (norm_nonneg _) hG0
        _ ≤ B := by rw [hBdef]; nlinarith [mul_nonneg (add_nonneg hA10 hB10) (add_nonneg hP'0 hCm0)]
    have hDp : ∀ j, ‖(planeReal M cM (alt38 N j + alh38 N) - planeReal M cM (alt38 N j)) / (alh38 N : ℂ)
        - planeReal M z' (alt38 N j)‖ ≤ alh38 N * Cm := fun j => alPlaneFwdErr38 M cM _ hh hM _
    have hDm : ∀ j, ‖(planeReal M cM (alt38 N j) - planeReal M cM (alt38 N j - alh38 N)) / (alh38 N : ℂ)
        - planeReal M z' (alt38 N j)‖ ≤ alh38 N * Cm := fun j => alPlaneBwdErr38 M cM _ hh hM _
    have hakb : ∀ j, ‖a N j‖ ≤ A1 := by
      intro j
      have := hNa1 j
      have h0 : ‖α (alt38 N j : PhysicalCircle)‖ ≤ ‖α‖ := ContinuousMap.norm_coe_le_norm _ _
      calc ‖a N j‖ = ‖(a N j - α (alt38 N j : PhysicalCircle)) + α (alt38 N j : PhysicalCircle)‖ := by ring_nf
        _ ≤ ‖a N j - α (alt38 N j : PhysicalCircle)‖ + ‖α (alt38 N j : PhysicalCircle)‖ := norm_add_le _ _
        _ ≤ A1 := by rw [hA1]; linarith
    have hbkb : ∀ j, ‖b N j‖ ≤ B1 := by
      intro j
      have := hNb1 j
      have h0 : ‖β (alt38 N j : PhysicalCircle)‖ ≤ ‖β‖ := ContinuousMap.norm_coe_le_norm _ _
      calc ‖b N j‖ = ‖(b N j - β (alt38 N j : PhysicalCircle)) + β (alt38 N j : PhysicalCircle)‖ := by ring_nf
        _ ≤ ‖b N j - β (alt38 N j : PhysicalCircle)‖ + ‖β (alt38 N j : PhysicalCircle)‖ := norm_add_le _ _
        _ ≤ B1 := by rw [hB1]; linarith
    have hYZ : ∀ j, ‖Y j - Z j‖ ≤ δ := by
      intro j
      have eq : Y j - Z j = a N j * (((planeReal M cM (alt38 N j + alh38 N) - planeReal M cM (alt38 N j))
            / (alh38 N : ℂ)) - planeReal M z' (alt38 N j))
          + (a N j - α (alt38 N j : PhysicalCircle)) * planeReal M z' (alt38 N j)
          + (b N j * (((planeReal M cM (alt38 N j) - planeReal M cM (alt38 N j - alh38 N))
            / (alh38 N : ℂ)) - planeReal M z' (alt38 N j))
          + (b N j - β (alt38 N j : PhysicalCircle)) * planeReal M z' (alt38 N j)) := by
        simp only [hY, hZ, hγ, ContinuousMap.add_apply]; ring
      rw [eq]
      have t1 : ‖a N j * (((planeReal M cM (alt38 N j + alh38 N) - planeReal M cM (alt38 N j))
            / (alh38 N : ℂ)) - planeReal M z' (alt38 N j))‖ ≤ A1 * (alh38 N * Cm) := by
        rw [norm_mul]; exact mul_le_mul (hakb j) (hDp j) (norm_nonneg _) hA10
      have t2 : ‖(a N j - α (alt38 N j : PhysicalCircle)) * planeReal M z' (alt38 N j)‖ ≤ ε * P' := by
        rw [norm_mul]; exact mul_le_mul (hNa j).le (hp'b _) (norm_nonneg _) hε0.le
      have t3 : ‖b N j * (((planeReal M cM (alt38 N j) - planeReal M cM (alt38 N j - alh38 N))
            / (alh38 N : ℂ)) - planeReal M z' (alt38 N j))‖ ≤ B1 * (alh38 N * Cm) := by
        rw [norm_mul]; exact mul_le_mul (hbkb j) (hDm j) (norm_nonneg _) hB10
      have t4 : ‖(b N j - β (alt38 N j : PhysicalCircle)) * planeReal M z' (alt38 N j)‖ ≤ ε * P' := by
        rw [norm_mul]; exact mul_le_mul (hNb j).le (hp'b _) (norm_nonneg _) hε0.le
      have hh1 : (A1 + B1) * Cm * alh38 N ≤ δ / 2 := by
        have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ (A1 + B1) * Cm)
        calc (A1 + B1) * Cm * alh38 N ≤ (A1 + B1) * Cm * (δ / (2 * ((A1 + B1) * Cm + 1))) := this
          _ ≤ δ / 2 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith [mul_nonneg (mul_nonneg (add_nonneg hA10 hB10) hCm0) hδ0.le, hδ0]
      have hh2 : 2 * (ε * P') ≤ δ / 2 := by
        have : ε * P' ≤ δ / 4 := by
          rw [hε, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [hδ0, hP'0]
        linarith
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ (‖a N j * _‖ + ‖_ * _‖) + (‖b N j * _‖ + ‖_ * _‖) := add_le_add (norm_add_le _ _) (norm_add_le _ _)
        _ ≤ (A1 * (alh38 N * Cm) + ε * P') + (B1 * (alh38 N * Cm) + ε * P') := by
          gcongr
        _ ≤ δ := by
          have e5 : A1 * (alh38 N * Cm) + B1 * (alh38 N * Cm) = (A1 + B1) * Cm * alh38 N := by ring
          linarith [hh1, hh2, e5]
    have hYb : ∀ j, ‖Y j‖ ≤ B + 1 := by
      intro j
      have h1' : ‖Y j‖ ≤ ‖Z j‖ + ‖Y j - Z j‖ := by
        have := norm_add_le (Z j) (Y j - Z j)
        simpa using this
      linarith [hYZ j, hZb j]
    have hZb' : ∀ j, ‖Z j‖ ≤ B + 1 := fun j => by linarith [hZb j]
    have hsup := alQ_sup38 Q hQ N Y Z δ (B + 1) hδ0.le (by linarith) hYZ hYb hZb'
    have hfin : δ * (2 * (B + 1)) < η := by
      have : δ * (2 * (B + 1)) = min η 1 / 2 := by
        rw [hδ]; field_simp; ring
      rw [this]
      linarith [min_le_left η 1]
    rw [dist_zero_right]
    exact lt_of_le_of_lt hsup hfin
  have := hdiff.add hR
  simpa using this

theorem alProjPlane_eq38 (M : ℕ) (u : SobolevHilbert 1) :
    physicalH1FiniteProjectionPlane M (physicalH1FiniteProjection M u)
      = physicalH1FiniteProjectionPlane M u := by
  funext i
  have h1 := physicalH1FiniteProjection_fourier M u (modeIndex M i)
  rw [physicalH1CarrierToL2AfterAcceptedCoordinate_fourier] at h1
  have hm : modeIndex M i ∈ symmetricModes M := by
    have := modeIndex_bounds M i
    simp only [symmetricModes, Finset.mem_Icc]; exact this
  rw [if_pos hm] at h1
  exact h1

theorem alGC38 (Q : ℂ → ℂ) (hQ : ∀ a b, ‖Q a - Q b‖ ≤ ‖a - b‖ * (‖a‖ + ‖b‖))
    (hQc : Continuous Q) (I : PhysicalL2 → ℂ) (hIc : Continuous I)
    (hIcl : ∀ (γ : C(PhysicalCircle, ℂ)) (M : ℕ) (c : FourierPlane M),
      I (alMult38 γ (planeL2 M c)) =
        ∫ t in (0 : ℝ)..1, Q (γ (t : PhysicalCircle) * planeReal M c t))
    (x : ℕ → SobolevHilbert 1) (u : SobolevHilbert 1) (hF : ∀ N, alInF38 N (x N))
    (hx : Tendsto x atTop (𝓝 u)) (α β : C(PhysicalCircle, ℂ))
    (a b : (N : ℕ) → ZMod (2 * N + 1) → ℂ)
    (ha : ∀ ε > 0, ∀ᶠ N in atTop, ∀ j, ‖a N j - α (alt38 N j : PhysicalCircle)‖ < ε)
    (hb : ∀ ε > 0, ∀ᶠ N in atTop, ∀ j, ‖b N j - β (alt38 N j : PhysicalCircle)‖ < ε) :
    Tendsto (fun N : ℕ => (alh38 N : ℂ) * ∑ j : ZMod (2 * N + 1),
        Q (a N j * alFd38 N (x N) j + b N j * alBd38 N (x N) j)) atTop
      (𝓝 (I (alMult38 (α + β) (physicalH1DerivativeL2CLM u)))) := by
  have hp : Tendsto (fun M : ℕ => physicalH1FiniteProjection M u) atTop (𝓝 u) :=
    physicalH1FiniteProjection_tendsto u
  have hpn : Tendsto (fun M : ℕ => ‖u - physicalH1FiniteProjection M u‖) atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hp)
    simpa [norm_sub_rev] using this
  have hxn : Tendsto (fun N : ℕ => ‖x N - u‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hx
  set A : ℝ := ‖α‖ + 1 with hA
  set B : ℝ := ‖β‖ + 1 with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  set K : ℝ := ((A + B) * (2 * Real.pi)) ^ 2 * (2 * (‖u‖ + 1)) with hK
  have hK0 : 0 ≤ K := by positivity
  refine alApprox38
    (SM := fun N M => (alh38 N : ℂ) * ∑ j : ZMod (2 * N + 1),
      Q (a N j * alFd38 N (physicalH1FiniteProjection M u) j
        + b N j * alBd38 N (physicalH1FiniteProjection M u) j))
    (IM := fun M => I (alMult38 (α + β)
      (physicalH1DerivativeL2CLM (physicalH1FiniteProjection M u)))) ?_ ?_ K hK0
    (fun N => ‖x N - u‖) (fun M => ‖u - physicalH1FiniteProjection M u‖) hxn hpn ?_
  · exact (hIc.tendsto _).comp (((alMult38 (α + β)).continuous.tendsto _).comp
      ((physicalH1DerivativeL2CLM.continuous.tendsto u).comp hp))
  · intro M
    have hd := physicalH1FiniteProjection_derivative_isPlane M u
    have hIM : I (alMult38 (α + β) (physicalH1DerivativeL2CLM (physicalH1FiniteProjection M u)))
        = ∫ t in (0 : ℝ)..1, Q ((α + β) (t : PhysicalCircle) *
            planeReal M (derivativePlane M (physicalH1FiniteProjectionPlane M u)) t) := by
      rw [hd]; exact hIcl _ _ _
    simp only [hIM]
    have hFM := alProj_inF38 M u
    have := alSmooth38 Q hQ hQc M (physicalH1FiniteProjectionPlane M u) α β a b ha hb
    refine this.congr (fun N => ?_)
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold alFd38 alBd38
    rw [alCanon_plane38 hFM, alCanon_plane38 hFM, alCanon_plane38 hFM, alProjPlane_eq38]
  · have hM0 : ∀ᶠ M in atTop, ‖u - physicalH1FiniteProjection M u‖ < 1 :=
      (Metric.tendsto_nhds.mp hpn) 1 one_pos |>.mono fun M hM => by
        rw [Real.dist_eq, sub_zero] at hM; exact (abs_lt.mp hM).2
    obtain ⟨M0, hM0⟩ := eventually_atTop.mp hM0
    refine ⟨M0, fun M hM => ?_⟩
    have hxb : ∀ᶠ N in atTop, ‖x N‖ ≤ ‖u‖ + 1 := by
      have := (Metric.tendsto_nhds.mp hxn) 1 one_pos
      filter_upwards [this] with N hN
      rw [Real.dist_eq, sub_zero] at hN
      have := (abs_lt.mp hN).2
      have h2 := norm_le_norm_add_norm_sub' (x N) u
      have h3 := norm_sub_rev (x N) u
      linarith
    filter_upwards [hxb, ha 1 one_pos, hb 1 one_pos, eventually_ge_atTop M] with N hN hNa hNb hNM
    have hbA : ∀ j, ‖a N j‖ ≤ A := by
      intro j
      have h0 : ‖α (alt38 N j : PhysicalCircle)‖ ≤ ‖α‖ := ContinuousMap.norm_coe_le_norm _ _
      have := hNa j
      calc ‖a N j‖ = ‖(a N j - α (alt38 N j : PhysicalCircle)) + α (alt38 N j : PhysicalCircle)‖ := by ring_nf
        _ ≤ ‖a N j - α (alt38 N j : PhysicalCircle)‖ + ‖α (alt38 N j : PhysicalCircle)‖ := norm_add_le _ _
        _ ≤ A := by rw [hA]; linarith
    have hbB : ∀ j, ‖b N j‖ ≤ B := by
      intro j
      have h0 : ‖β (alt38 N j : PhysicalCircle)‖ ≤ ‖β‖ := ContinuousMap.norm_coe_le_norm _ _
      have := hNb j
      calc ‖b N j‖ = ‖(b N j - β (alt38 N j : PhysicalCircle)) + β (alt38 N j : PhysicalCircle)‖ := by ring_nf
        _ ≤ ‖b N j - β (alt38 N j : PhysicalCircle)‖ + ‖β (alt38 N j : PhysicalCircle)‖ := norm_add_le _ _
        _ ≤ B := by rw [hB]; linarith
    have hmain := alGCbound38 Q hQ (hF N) (alInF_mono38 hNM _ (alProj_inF38 M u)) (a N) (b N) A B hA0 hB0 hbA hbB
    refine hmain.trans ?_
    have hpb : ‖physicalH1FiniteProjection M u‖ ≤ ‖u‖ + 1 := by
      have := hM0 M hM
      have h2 := norm_le_norm_add_norm_sub' (physicalH1FiniteProjection M u) u
      have h3 := norm_sub_rev (physicalH1FiniteProjection M u) u
      linarith
    have hxy : ‖x N - physicalH1FiniteProjection M u‖ ≤ ‖x N - u‖ + ‖u - physicalH1FiniteProjection M u‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    set c0 : ℝ := (A + B) * (2 * Real.pi) with hc0
    have hc00 : 0 ≤ c0 := by positivity
    calc _ = c0 * ‖x N - physicalH1FiniteProjection M u‖ * (c0 * ‖x N‖ + c0 * ‖physicalH1FiniteProjection M u‖) := by
          rw [hc0]; ring
      _ ≤ c0 * (‖x N - u‖ + ‖u - physicalH1FiniteProjection M u‖) * (c0 * (‖u‖ + 1) + c0 * (‖u‖ + 1)) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hxy hc00
          · exact add_le_add (mul_le_mul_of_nonneg_left hN hc00) (mul_le_mul_of_nonneg_left hpb hc00)
          · positivity
          · positivity
      _ = K * (‖x N - u‖ + ‖u - physicalH1FiniteProjection M u‖) := by rw [hK]; ring

section Lim
open MeasureTheory
local instance alProb38'' : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- The two quadratic forms used for the squares of difference quotients. -/
def alQ1_38 (y : ℂ) : ℂ := ((‖y‖ ^ 2 : ℝ) : ℂ)
def alQ2_38 (y : ℂ) : ℂ := y ^ 2

theorem alQ1_lip38 (a b : ℂ) : ‖alQ1_38 a - alQ1_38 b‖ ≤ ‖a - b‖ * (‖a‖ + ‖b‖) := by
  unfold alQ1_38
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have : ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) := by ring
  rw [this, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖a‖ + ‖b‖)]
  exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le a b) (by positivity)

theorem alQ2_lip38 (a b : ℂ) : ‖alQ2_38 a - alQ2_38 b‖ ≤ ‖a - b‖ * (‖a‖ + ‖b‖) := by
  unfold alQ2_38
  have : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [this, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_add_le a b) (norm_nonneg _)

theorem alQ1_cont38 : Continuous alQ1_38 := by
  unfold alQ1_38; fun_prop

theorem alQ2_cont38 : Continuous alQ2_38 := by
  unfold alQ2_38; fun_prop

def alI1_38 (g : PhysicalL2) : ℂ := ((‖g‖ ^ 2 : ℝ) : ℂ)

def alI2_38 (g : PhysicalL2) : ℂ :=
  MeasureTheory.L1.integral (physicalL2ProductL1CLM g g)

theorem alI1_cont38 : Continuous alI1_38 := by
  unfold alI1_38; fun_prop

theorem alI2_cont38 : Continuous alI2_38 := by
  have hfun : alI2_38 = fun g => MeasureTheory.L1.integralCLM
      (α := PhysicalCircle) (E := ℂ) (μ := spatialMeasure) (physicalL2ProductL1CLM g g) := by
    funext g
    unfold alI2_38
    exact MeasureTheory.L1.integral_eq _
  rw [hfun]
  exact (MeasureTheory.L1.integralCLM (α := PhysicalCircle) (E := ℂ)
    (μ := spatialMeasure)).continuous.comp
      ((physicalL2ProductL1CLM.continuous.comp continuous_id).clm_apply continuous_id)

theorem alLim1_38 (x : ℕ → SobolevHilbert 1) (u : SobolevHilbert 1) (hF : ∀ N, alInF38 N (x N))
    (hx : Tendsto x atTop (𝓝 u)) (α β : C(PhysicalCircle, ℂ))
    (a b : (N : ℕ) → ZMod (2 * N + 1) → ℂ)
    (ha : ∀ ε > 0, ∀ᶠ N in atTop, ∀ j, ‖a N j - α (alt38 N j : PhysicalCircle)‖ < ε)
    (hb : ∀ ε > 0, ∀ᶠ N in atTop, ∀ j, ‖b N j - β (alt38 N j : PhysicalCircle)‖ < ε) :
    Tendsto (fun N : ℕ => alh38 N * ∑ j : ZMod (2 * N + 1),
        ‖a N j * alFd38 N (x N) j + b N j * alBd38 N (x N) j‖ ^ 2) atTop
      (𝓝 (‖alMult38 (α + β) (physicalH1DerivativeL2CLM u)‖ ^ 2)) := by
  have h := alGC38 alQ1_38 alQ1_lip38 alQ1_cont38 alI1_38 alI1_cont38
    (fun γ M c => alI1_classical38 γ M c) x u hF hx α β a b ha hb
  rw [Complex.isometry_ofReal.isEmbedding.tendsto_nhds_iff]
  refine h.congr (fun N => ?_)
  simp only [Function.comp_def, alQ1_38]
  push_cast
  rfl

theorem alLim2_38 (x : ℕ → SobolevHilbert 1) (u : SobolevHilbert 1) (hF : ∀ N, alInF38 N (x N))
    (hx : Tendsto x atTop (𝓝 u)) (α β : C(PhysicalCircle, ℂ))
    (a b : (N : ℕ) → ZMod (2 * N + 1) → ℂ)
    (ha : ∀ ε > 0, ∀ᶠ N in atTop, ∀ j, ‖a N j - α (alt38 N j : PhysicalCircle)‖ < ε)
    (hb : ∀ ε > 0, ∀ᶠ N in atTop, ∀ j, ‖b N j - β (alt38 N j : PhysicalCircle)‖ < ε) :
    Tendsto (fun N : ℕ => (alh38 N : ℂ) * ∑ j : ZMod (2 * N + 1),
        (a N j * alFd38 N (x N) j + b N j * alBd38 N (x N) j) ^ 2) atTop
      (𝓝 (MeasureTheory.L1.integral (physicalL2ProductL1CLM
        (alMult38 (α + β) (physicalH1DerivativeL2CLM u))
        (alMult38 (α + β) (physicalH1DerivativeL2CLM u))))) :=
  alGC38 alQ2_38 alQ2_lip38 alQ2_cont38 alI2_38 alI2_cont38
    (fun γ M c => by
      show MeasureTheory.L1.integral _ = _
      exact alI2_classical38 γ M c) x u hF hx α β a b ha hb

end Lim
end Sec_b5

section Sec_c1
open Finset Filter Topology NlsGge.Pilot NlsGge.Analysis

/-- Samples `v_j = u_h(jh)` of the canonical continuous representative. -/
def alSample38 (N : ℕ) (x : SobolevHilbert 1) (j : ZMod (2 * N + 1)) : ℂ :=
  alCanon38 x (alt38 N j)

theorem alSample_succ38 (N : ℕ) (x : SobolevHilbert 1) (j : ZMod (2 * N + 1)) :
    alSample38 N x (j + 1) = alCanon38 x (alt38 N j + alh38 N) := by
  have := alt38_add_nat N j 1 (alCanon38 x) (alCanon_periodic38 x)
  unfold alSample38
  simpa using this

theorem alSample_pred38 (N : ℕ) (x : SobolevHilbert 1) (j : ZMod (2 * N + 1)) :
    alSample38 N x (j - 1) = alCanon38 x (alt38 N j - alh38 N) := by
  have h2N : (((2 * N : ℕ)) : ZMod (2 * N + 1)) = -1 := by
    have : ((2 * N + 1 : ℕ) : ZMod (2 * N + 1)) = 0 := ZMod.natCast_self _
    push_cast at this
    exact eq_neg_of_add_eq_zero_left (by push_cast; exact this)
  have hj : j - 1 = j + ((2 * N : ℕ) : ZMod (2 * N + 1)) := by rw [h2N]; ring
  have := alt38_add_nat N j (2 * N) (alCanon38 x) (alCanon_periodic38 x)
  unfold alSample38
  rw [hj, this]
  have hmul := alh38_mul N
  have : alt38 N j + ((2 * N : ℕ) : ℝ) * alh38 N = (alt38 N j - alh38 N) + 1 := by
    push_cast; nlinarith [hmul]
  rw [this]
  exact alCanon_periodic38 x _

/-- Discrete Fourier coordinate `z_k = h ∑_j v_j e^{-2πikjh}`. -/
def alDFT38 (N : ℕ) (v : ZMod (2 * N + 1) → ℂ) (k : ℤ) : ℂ :=
  (alh38 N : ℂ) * ∑ j : ZMod (2 * N + 1),
    v j * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (alt38 N j : ℂ)))

theorem planeReal_single38 (N : ℕ) (i : Fin (2 * N + 1)) (t : ℝ) :
    planeReal N (Pi.single i (1 : ℂ)) t
      = Complex.exp (2 * Real.pi * Complex.I * ((modeIndex N i : ℤ) : ℂ) * (t : ℂ)) := by
  classical
  rw [planeReal_eq38]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [Pi.single_apply, hk]
  · simp

theorem alDFT_plane38 (N : ℕ) (z : FourierPlane N) (i : Fin (2 * N + 1)) :
    alDFT38 N (fun j => planeReal N z (alt38 N j)) (modeIndex N i) = z i := by
  classical
  have h := parsevalInner38 N z (Pi.single i (1 : ℂ))
  have hconj : ∀ j : ZMod (2 * N + 1), (starRingEnd ℂ) (planeReal N (Pi.single i (1 : ℂ)) (alt38 N j))
      = Complex.exp (-(2 * Real.pi * Complex.I * ((modeIndex N i : ℤ) : ℂ) * (alt38 N j : ℂ))) := by
    intro j
    rw [planeReal_single38, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast]; ring
  simp_rw [hconj] at h
  unfold alDFT38
  rw [h, Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [Pi.single_apply, hk]
  · simp

theorem alIcc_sum38 (N : ℕ) (F : ℤ → ℝ) :
    ∑ k ∈ Finset.Icc (-(N : ℤ)) N, F k = ∑ i : Fin (2 * N + 1), F (modeIndex N i) := by
  have himg : Finset.Icc (-(N : ℤ)) N = Finset.univ.image (modeIndex N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact modeIndex_covers N n h1 h2
    · rintro ⟨i, rfl⟩
      exact modeIndex_bounds N i
  rw [himg, Finset.sum_image (fun i _ j _ hij => modeIndex_injective N hij)]

/-- The symbol `a_{h,k} = β₀ - h + β₁ ω² + β₂ ω⁴`. -/
def alSymbol38 (β₀ β₁ β₂ : ℝ) (N : ℕ) (k : ℤ) : ℝ :=
  β₀ - alh38 N + β₁ * alomega38 N k ^ 2 + β₂ * alomega38 N k ^ 4

open NlsGge.HierarchyRiccati.Core in
/-- `R_h(v)`: nonlinear part of the exponent after the mass shift, with the quadratic form
`∑_{|k|≤N} a_{h,k}|z_k|²` subtracted; here `α_j = h v_j`. -/
def alRh38 (β₀ β₁ β₂ : ℝ) (N : ℕ) (v : ZMod (2 * N + 1) → ℂ) : ℝ :=
  (β₀ - alh38 N) / alh38 N * alMd (fun j => (alh38 N : ℂ) * v j)
    + β₁ / alh38 N ^ 3 * alHd (fun j => (alh38 N : ℂ) * v j)
    + β₂ / alh38 N ^ 5 * alKd (fun j => (alh38 N : ℂ) * v j)
    - ∑ k ∈ Finset.Icc (-(N : ℤ)) N, alSymbol38 β₀ β₁ β₂ N k * ‖alDFT38 N v k‖ ^ 2

theorem alSample_plane38 {N : ℕ} {x : SobolevHilbert 1} (hx : alInF38 N x) :
    alSample38 N x = fun j => planeReal N (physicalH1FiniteProjectionPlane N x) (alt38 N j) := by
  funext j; unfold alSample38; exact alCanon_plane38 hx _

open NlsGge.HierarchyRiccati.Core in
theorem alQuad_eq38 (β₀ β₁ β₂ : ℝ) {N : ℕ} {x : SobolevHilbert 1} (hx : alInF38 N x) :
    (β₀ - alh38 N) / alh38 N * ∑ j : ZMod (2 * N + 1),
        alR (fun j => (alh38 N : ℂ) * alSample38 N x j) j
      + β₁ / alh38 N ^ 3 * ∑ j : ZMod (2 * N + 1),
        ‖(alh38 N : ℂ) * alSample38 N x j - (alh38 N : ℂ) * alSample38 N x (j - 1)‖ ^ 2
      + β₂ / alh38 N ^ 5 * ∑ j : ZMod (2 * N + 1),
        ‖(alh38 N : ℂ) * alSample38 N x (j + 1) - 2 * ((alh38 N : ℂ) * alSample38 N x j)
          + (alh38 N : ℂ) * alSample38 N x (j - 1)‖ ^ 2
      = ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
          alSymbol38 β₀ β₁ β₂ N k * ‖alDFT38 N (alSample38 N x) k‖ ^ 2 := by
  have hh := alh38_pos N
  set z := physicalH1FiniteProjectionPlane N x with hz
  have hc : ∀ t, alCanon38 x t = planeReal N z t := fun t => alCanon_plane38 hx t
  have hsucc : ∀ j, alSample38 N x (j + 1) = planeReal N z (alt38 N j + alh38 N) := by
    intro j; rw [alSample_succ38, hc]
  have hpred : ∀ j, alSample38 N x (j - 1) = planeReal N z (alt38 N j - alh38 N) := by
    intro j; rw [alSample_pred38, hc]
  have hself : ∀ j, alSample38 N x j = planeReal N z (alt38 N j) := fun j => hc _
  have hhc : (alh38 N : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  -- mass
  have m0 : ∑ j : ZMod (2 * N + 1), alR (fun j => (alh38 N : ℂ) * alSample38 N x j) j
      = alh38 N ^ 2 * ∑ j : ZMod (2 * N + 1), ‖planeReal N z (alt38 N j)‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold alR
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh, hself]; ring
  have m1 : ∑ j : ZMod (2 * N + 1),
        ‖(alh38 N : ℂ) * alSample38 N x j - (alh38 N : ℂ) * alSample38 N x (j - 1)‖ ^ 2
      = alh38 N ^ 4 * ∑ j : ZMod (2 * N + 1),
        ‖(planeReal N z (alt38 N j) - planeReal N z (alt38 N j - alh38 N)) / (alh38 N : ℂ)‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hself, hpred, ← mul_sub, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hh]
    field_simp
  have m2 : ∑ j : ZMod (2 * N + 1),
        ‖(alh38 N : ℂ) * alSample38 N x (j + 1) - 2 * ((alh38 N : ℂ) * alSample38 N x j)
          + (alh38 N : ℂ) * alSample38 N x (j - 1)‖ ^ 2
      = alh38 N ^ 6 * ∑ j : ZMod (2 * N + 1),
        ‖(planeReal N z (alt38 N j + alh38 N) - 2 * planeReal N z (alt38 N j)
            + planeReal N z (alt38 N j - alh38 N)) / (alh38 N : ℂ) ^ 2‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsucc, hpred, hself]
    have : (alh38 N : ℂ) * planeReal N z (alt38 N j + alh38 N)
          - 2 * ((alh38 N : ℂ) * planeReal N z (alt38 N j))
          + (alh38 N : ℂ) * planeReal N z (alt38 N j - alh38 N)
        = (alh38 N : ℂ) ^ 3 * ((planeReal N z (alt38 N j + alh38 N) - 2 * planeReal N z (alt38 N j)
            + planeReal N z (alt38 N j - alh38 N)) / (alh38 N : ℂ) ^ 2) := by
      field_simp
    rw [this, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    ring
  rw [m0, m1, m2]
  have p0 := parseval38 N z
  have p1 := parsevalBwd38 N z
  have p2 := parsevalSec38 N z
  rw [alIcc_sum38]
  have hd : ∀ i : Fin (2 * N + 1), alDFT38 N (alSample38 N x) (modeIndex N i) = z i := by
    intro i
    rw [alSample_plane38 hx]
    exact alDFT_plane38 N z i
  simp_rw [hd]
  unfold alSymbol38
  simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [← p0, ← p1, ← p2]
  field_simp

open NlsGge.HierarchyRiccati.Core in
theorem alKd_explicit38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) :
    alKd α = ∑ j, ‖α (j + 1) - 2 * α j + α (j - 1)‖ ^ 2
      + (3 / 2) * ∑ j, (alR α (j + 1) - alR α j) ^ 2
      + ∑ j, alR α j * ‖α (j + 1) - α (j - 1)‖ ^ 2
      + 2 * ∑ j, ((α j * (starRingEnd ℂ) (α (j - 1))).im) ^ 2
      + 6 * ∑ j, (-Real.log (1 - alR α j) - alR α j - (1 / 2) * alR α j ^ 2) := by
  rw [alKd_squares]; rfl

open NlsGge.HierarchyRiccati.Core in
/-- Exact expression of `R_h` on samples of `F_N` fields: the quadratic parts cancel. -/
theorem alRh_eq38 (β₀ β₁ β₂ : ℝ) {N : ℕ} {x : SobolevHilbert 1} (hx : alInF38 N x) :
    alRh38 β₀ β₁ β₂ N (alSample38 N x) =
      ((β₀ - alh38 N) / alh38 N + 2 * β₁ / alh38 N ^ 3) * ∑ j : ZMod (2 * N + 1),
          alEll (alR (fun j => (alh38 N : ℂ) * alSample38 N x j) j)
        + β₂ / alh38 N ^ 5 * ((3 / 2) * ∑ j : ZMod (2 * N + 1),
            (alR (fun j => (alh38 N : ℂ) * alSample38 N x j) (j + 1)
              - alR (fun j => (alh38 N : ℂ) * alSample38 N x j) j) ^ 2
          + ∑ j : ZMod (2 * N + 1), alR (fun j => (alh38 N : ℂ) * alSample38 N x j) j *
              ‖(alh38 N : ℂ) * alSample38 N x (j + 1) - (alh38 N : ℂ) * alSample38 N x (j - 1)‖ ^ 2
          + 2 * ∑ j : ZMod (2 * N + 1),
              (((alh38 N : ℂ) * alSample38 N x j * (starRingEnd ℂ)
                ((alh38 N : ℂ) * alSample38 N x (j - 1))).im) ^ 2
          + 6 * ∑ j : ZMod (2 * N + 1),
              (-Real.log (1 - alR (fun j => (alh38 N : ℂ) * alSample38 N x j) j)
                - alR (fun j => (alh38 N : ℂ) * alSample38 N x j) j
                - (1 / 2) * alR (fun j => (alh38 N : ℂ) * alSample38 N x j) j ^ 2)) := by
  have hq := alQuad_eq38 β₀ β₁ β₂ hx
  unfold alRh38
  rw [alMd_split, alHd_split, alKd_explicit38]
  set α : ZMod (2 * N + 1) → ℂ := fun j => (alh38 N : ℂ) * alSample38 N x j with hα
  have hsum : ∑ j : ZMod (2 * N + 1), ‖α (j + 1) - 2 * α j + α (j - 1)‖ ^ 2
      = ∑ j : ZMod (2 * N + 1),
        ‖(alh38 N : ℂ) * alSample38 N x (j + 1) - 2 * ((alh38 N : ℂ) * alSample38 N x j)
          + (alh38 N : ℂ) * alSample38 N x (j - 1)‖ ^ 2 := rfl
  have hsum2 : ∑ j : ZMod (2 * N + 1), ‖α j - α (j - 1)‖ ^ 2
      = ∑ j : ZMod (2 * N + 1),
        ‖(alh38 N : ℂ) * alSample38 N x j - (alh38 N : ℂ) * alSample38 N x (j - 1)‖ ^ 2 := rfl
  rw [hsum, hsum2]
  linear_combination hq
end Sec_c1

section Sec_c2
open Finset Filter Topology NlsGge.Pilot NlsGge.Analysis
open NlsGge.HierarchyRiccati.Core

theorem alLog4_38 {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) :
    |(-Real.log (1 - r) - r - r ^ 2 / 2 - r ^ 3 / 3)| ≤ 2 * r ^ 4 := by
  have hr : |r| < 1 := by rw [abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hr 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_of_nonneg h0] at h
  have e : (-Real.log (1 - r) - r - r ^ 2 / 2 - r ^ 3 / 3)
      = -((0 + r ^ (0 + 1) / (↑(0 : ℕ) + 1) + r ^ (1 + 1) / (↑(1 : ℕ) + 1) + r ^ (2 + 1) / (↑(2 : ℕ) + 1)) + Real.log (1 - r)) := by
    push_cast; ring
  rw [e, abs_neg]
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith)]
  have e4 : r ^ (3 + 1) = r ^ 4 := by norm_num
  rw [e4]
  nlinarith [mul_nonneg (pow_nonneg h0 4) (by linarith : 0 ≤ 1 / 2 - r)]

theorem alEll_quad_38 {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) :
    |alEll r - r ^ 2 / 2| ≤ 2 * r ^ 3 := by
  have h := alLog4_38 h0 h1
  have e : alEll r - r ^ 2 / 2 = (-Real.log (1 - r) - r - r ^ 2 / 2 - r ^ 3 / 3) + r ^ 3 / 3 := by
    unfold alEll; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg (by positivity : 0 ≤ r ^ 3 / 3)]
  nlinarith [pow_nonneg h0 3, pow_nonneg h0 4, mul_nonneg (pow_nonneg h0 3) (by linarith : 0 ≤ 1 / 2 - r)]

theorem alEll_le_38 {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) : |alEll r| ≤ 2 * r ^ 2 := by
  have h := alEll_quad_38 h0 h1
  have hn : 0 ≤ alEll r := alEll_nonneg h0 (by linarith)
  rw [abs_of_nonneg hn]
  have := (abs_le.mp h).2
  nlinarith [pow_nonneg h0 2, pow_nonneg h0 3, mul_nonneg (pow_nonneg h0 2) (by linarith : 0 ≤ 1 / 2 - r)]

theorem alEll2_cubic_38 {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) :
    |(-Real.log (1 - r) - r - (1 / 2) * r ^ 2) - r ^ 3 / 3| ≤ 2 * r ^ 4 := by
  have := alLog4_38 h0 h1
  convert this using 2; ring

theorem alCard38 (N : ℕ) (c : ℝ) :
    ∑ _j : ZMod (2 * N + 1), c = (2 * (N : ℝ) + 1) * c := by
  rw [Finset.sum_const, nsmul_eq_mul]
  have : (Finset.univ : Finset (ZMod (2 * N + 1))).card = 2 * N + 1 := by simp [ZMod.card]
  rw [this]; push_cast; ring

theorem alLogSums38 (N : ℕ) (w : ZMod (2 * N + 1) → ℝ) (W : ℝ) (hw0 : ∀ j, 0 ≤ w j)
    (hwW : ∀ j, w j ≤ W) (hr : alh38 N ^ 2 * W ≤ 1 / 2) :
    |∑ j, alEll (alh38 N ^ 2 * w j)| ≤ 2 * alh38 N ^ 3 * W ^ 2
    ∧ |∑ j, alEll (alh38 N ^ 2 * w j) - alh38 N ^ 4 / 2 * ∑ j, w j ^ 2| ≤ 2 * alh38 N ^ 5 * W ^ 3
    ∧ |∑ j, (-Real.log (1 - alh38 N ^ 2 * w j) - alh38 N ^ 2 * w j - (1 / 2) * (alh38 N ^ 2 * w j) ^ 2)
        - alh38 N ^ 6 / 3 * ∑ j, w j ^ 3| ≤ 2 * alh38 N ^ 7 * W ^ 4 := by
  have hh := alh38_pos N
  have hL := alh38_mul N
  have hr0 : ∀ j, 0 ≤ alh38 N ^ 2 * w j := fun j => by have := hw0 j; positivity
  have hr1 : ∀ j, alh38 N ^ 2 * w j ≤ 1 / 2 := fun j =>
    (mul_le_mul_of_nonneg_left (hwW j) (by positivity)).trans hr
  have hW0 : 0 ≤ W := (hw0 (0 : ZMod (2 * N + 1))).trans (hwW 0)
  refine ⟨?_, ?_, ?_⟩
  · calc |∑ j, alEll (alh38 N ^ 2 * w j)| ≤ ∑ j, |alEll (alh38 N ^ 2 * w j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : ZMod (2 * N + 1), 2 * (alh38 N ^ 2 * W) ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine (alEll_le_38 (hr0 j) (hr1 j)).trans ?_
          have : alh38 N ^ 2 * w j ≤ alh38 N ^ 2 * W := mul_le_mul_of_nonneg_left (hwW j) (by positivity)
          nlinarith [hr0 j]
      _ = 2 * alh38 N ^ 3 * W ^ 2 := by
          rw [alCard38]
          have : (2 * (N : ℝ) + 1) * alh38 N = 1 := hL
          calc (2 * (N : ℝ) + 1) * (2 * (alh38 N ^ 2 * W) ^ 2)
              = ((2 * (N : ℝ) + 1) * alh38 N) * (2 * alh38 N ^ 3 * W ^ 2) := by ring
            _ = _ := by rw [this]; ring
  · have e : ∑ j, alEll (alh38 N ^ 2 * w j) - alh38 N ^ 4 / 2 * ∑ j, w j ^ 2
        = ∑ j, (alEll (alh38 N ^ 2 * w j) - (alh38 N ^ 2 * w j) ^ 2 / 2) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_; ring
    rw [e]
    calc _ ≤ ∑ j, |alEll (alh38 N ^ 2 * w j) - (alh38 N ^ 2 * w j) ^ 2 / 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : ZMod (2 * N + 1), 2 * (alh38 N ^ 2 * W) ^ 3 := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine (alEll_quad_38 (hr0 j) (hr1 j)).trans ?_
          have : alh38 N ^ 2 * w j ≤ alh38 N ^ 2 * W := mul_le_mul_of_nonneg_left (hwW j) (by positivity)
          have := pow_le_pow_left₀ (hr0 j) this 3
          linarith
      _ = 2 * alh38 N ^ 5 * W ^ 3 := by
          rw [alCard38]
          calc (2 * (N : ℝ) + 1) * (2 * (alh38 N ^ 2 * W) ^ 3)
              = ((2 * (N : ℝ) + 1) * alh38 N) * (2 * alh38 N ^ 5 * W ^ 3) := by ring
            _ = _ := by rw [hL]; ring
  · have e : ∑ j, (-Real.log (1 - alh38 N ^ 2 * w j) - alh38 N ^ 2 * w j - (1 / 2) * (alh38 N ^ 2 * w j) ^ 2)
        - alh38 N ^ 6 / 3 * ∑ j, w j ^ 3
        = ∑ j, ((-Real.log (1 - alh38 N ^ 2 * w j) - alh38 N ^ 2 * w j - (1 / 2) * (alh38 N ^ 2 * w j) ^ 2)
          - (alh38 N ^ 2 * w j) ^ 3 / 3) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_; ring
    rw [e]
    calc _ ≤ ∑ j, |(-Real.log (1 - alh38 N ^ 2 * w j) - alh38 N ^ 2 * w j - (1 / 2) * (alh38 N ^ 2 * w j) ^ 2)
          - (alh38 N ^ 2 * w j) ^ 3 / 3| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : ZMod (2 * N + 1), 2 * (alh38 N ^ 2 * W) ^ 4 := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine (alEll2_cubic_38 (hr0 j) (hr1 j)).trans ?_
          have : alh38 N ^ 2 * w j ≤ alh38 N ^ 2 * W := mul_le_mul_of_nonneg_left (hwW j) (by positivity)
          have := pow_le_pow_left₀ (hr0 j) this 4
          linarith
      _ = 2 * alh38 N ^ 7 * W ^ 4 := by
          rw [alCard38]
          calc (2 * (N : ℝ) + 1) * (2 * (alh38 N ^ 2 * W) ^ 4)
              = ((2 * (N : ℝ) + 1) * alh38 N) * (2 * alh38 N ^ 7 * W ^ 4) := by ring
            _ = _ := by rw [hL]; ring
end Sec_c2

section Sec_c3
open Finset Filter Topology NlsGge.Pilot NlsGge.Analysis

theorem alUnif_close38 (x : ℕ → SobolevHilbert 1) (u : SobolevHilbert 1)
    (hx : Tendsto x atTop (𝓝 u)) (σ : ℕ → ℝ) (hσ : Tendsto σ atTop (𝓝 0)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ t : ℝ, ‖alCanon38 (x N) (t + σ N) - alCanon38 u t‖ < ε := by
  have hxn : Tendsto (fun N : ℕ => ‖x N - u‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hx
  have hU := periodic_uniformContinuous38 (alCanon38 u) (alCanon_cont38 u) (alCanon_periodic38 u)
  rw [Metric.uniformContinuous_iff] at hU
  obtain ⟨δ, hδ, hδ'⟩ := hU (ε / 2) (by linarith)
  have hC0 : 0 < ‖reciprocalBracketL2‖ + 1 := by positivity
  have e1 : ∀ᶠ N in atTop, ‖x N - u‖ < ε / 2 / (‖reciprocalBracketL2‖ + 1) := by
    have := (Metric.tendsto_nhds.mp hxn) (ε / 2 / (‖reciprocalBracketL2‖ + 1)) (by positivity)
    exact this.mono fun N hN => by
      rw [Real.dist_eq, sub_zero] at hN; exact (abs_lt.mp hN).2
  have e2 : ∀ᶠ N in atTop, |σ N| < δ := by
    have := (Metric.tendsto_nhds.mp hσ) δ hδ
    exact this.mono fun N hN => by rw [Real.dist_eq, sub_zero] at hN; exact hN
  filter_upwards [e1, e2] with N h1 h2 t
  have c1 : ‖alCanon38 (x N) (t + σ N) - alCanon38 u (t + σ N)‖ < ε / 2 := by
    rw [← alCanon_sub38]
    calc _ ≤ ‖x N - u‖ * ‖reciprocalBracketL2‖ := alCanon_norm_le38 _ _
      _ ≤ ‖x N - u‖ * (‖reciprocalBracketL2‖ + 1) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _ < ε / 2 := by
          rwa [lt_div_iff₀ hC0] at h1
  have c2 : ‖alCanon38 u (t + σ N) - alCanon38 u t‖ < ε / 2 := by
    have := hδ' (a := t + σ N) (b := t) (by rw [Real.dist_eq]; simpa using h2)
    rwa [dist_eq_norm] at this
  calc _ = ‖(alCanon38 (x N) (t + σ N) - alCanon38 u (t + σ N)) + (alCanon38 u (t + σ N) - alCanon38 u t)‖ := by
        congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ < ε := by linarith

theorem alRe_sq38 (w : ℂ) : w.re ^ 2 = (‖w‖ ^ 2 + (w ^ 2).re) / 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp [sq]

theorem alIm_sq38 (w : ℂ) : w.im ^ 2 = (‖w‖ ^ 2 - (w ^ 2).re) / 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp [sq]

theorem alDeltaRe38 (p q : ℂ) (h : ℝ) (hh : h ≠ 0) :
    (‖p‖ ^ 2 - ‖q‖ ^ 2) / h = ((starRingEnd ℂ) (p + q) * ((p - q) / (h : ℂ))).re := by
  have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  rw [show (p - q) / (h : ℂ) = ((p - q) * ((h⁻¹ : ℝ) : ℂ)) by push_cast; ring]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  field_simp
  ring

theorem alNormMul38 (h : ℝ) (hh : 0 < h) (z : ℂ) : ‖(h : ℂ) * z‖ ^ 2 = h ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]; ring

theorem alP3A38 (h : ℝ) (hh : 0 < h) (p q d : ℂ) (hd : d = (p - q) / (h : ℂ)) :
    (3 / 2) * (‖(h : ℂ) * p‖ ^ 2 - ‖(h : ℂ) * q‖ ^ 2) ^ 2
      = h ^ 6 * (3 * ‖(starRingEnd ℂ) (p + q) / 2 * d‖ ^ 2
          + 3 * (((starRingEnd ℂ) (p + q) / 2 * d) ^ 2).re) := by
  have h1 := alDeltaRe38 p q h hh.ne'
  rw [← hd] at h1
  set Y : ℂ := (starRingEnd ℂ) (p + q) / 2 * d with hY
  have h2 : ((starRingEnd ℂ) (p + q) * d).re = 2 * Y.re := by
    have : (starRingEnd ℂ) (p + q) * d = 2 * Y := by rw [hY]; ring
    rw [this]; simp
  rw [h2] at h1
  have h3 : ‖p‖ ^ 2 - ‖q‖ ^ 2 = h * (2 * Y.re) := by
    rw [← h1]; field_simp
  rw [alNormMul38 h hh, alNormMul38 h hh]
  have h4 : h ^ 2 * ‖p‖ ^ 2 - h ^ 2 * ‖q‖ ^ 2 = h ^ 2 * (h * (2 * Y.re)) := by rw [← h3]; ring
  rw [h4]
  have h5 := alRe_sq38 Y
  calc (3 / 2) * (h ^ 2 * (h * (2 * Y.re))) ^ 2 = (3 / 2) * (4 * h ^ 6) * Y.re ^ 2 := by ring
    _ = _ := by rw [h5]; ring

theorem alP3B38 (h : ℝ) (hh : 0 < h) (p q m d bd : ℂ)
    (hd : d = (p - q) / (h : ℂ)) (hb : bd = (q - m) / (h : ℂ)) :
    ‖(h : ℂ) * q‖ ^ 2 * ‖(h : ℂ) * p - (h : ℂ) * m‖ ^ 2 = h ^ 6 * ‖q * d + q * bd‖ ^ 2 := by
  have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have e : (h : ℂ) * p - (h : ℂ) * m = (h : ℂ) ^ 2 * (d + bd) := by
    rw [hd, hb]; field_simp; ring
  have e2 : q * d + q * bd = q * (d + bd) := by ring
  have e3 : (h : ℂ) ^ 2 = ((h ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hh2 : 0 < h ^ 2 := by positivity
  rw [e, e2, alNormMul38 h hh, e3, alNormMul38 (h ^ 2) hh2, norm_mul, mul_pow]
  ring

theorem alP3C38 (h : ℝ) (hh : 0 < h) (q m bd : ℂ) (hb : bd = (q - m) / (h : ℂ)) :
    2 * (((h : ℂ) * q * (starRingEnd ℂ) ((h : ℂ) * m)).im) ^ 2
      = h ^ 6 * (‖0 * 0 + (starRingEnd ℂ) m * bd‖ ^ 2
          - (((0 : ℂ) * 0 + (starRingEnd ℂ) m * bd) ^ 2).re) := by
  have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  set Y : ℂ := (starRingEnd ℂ) m * bd with hY
  have e : (h : ℂ) * q * (starRingEnd ℂ) ((h : ℂ) * m)
      = ((h ^ 3 : ℝ) : ℂ) * Y + ((h ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) m * m) := by
    rw [hY, hb, map_mul, Complex.conj_ofReal]
    push_cast
    field_simp
    ring
  have hmm : ((starRingEnd ℂ) m * m).im = 0 := by simp [Complex.mul_im]; ring
  have him : ((h : ℂ) * q * (starRingEnd ℂ) ((h : ℂ) * m)).im = h ^ 3 * Y.im := by
    rw [e]
    rw [Complex.add_im, Complex.im_ofReal_mul, Complex.im_ofReal_mul, hmm]; ring
  rw [him]
  have h5 := alIm_sq38 Y
  simp only [zero_mul, zero_add]
  calc 2 * (h ^ 3 * Y.im) ^ 2 = h ^ 6 * (2 * Y.im ^ 2) := by ring
    _ = _ := by rw [h5]; ring

theorem alSupSum38 (N : ℕ) (e : ZMod (2 * N + 1) → ℝ) (δ : ℝ) (he : ∀ j, |e j| ≤ δ) :
    |alh38 N * ∑ j, e j| ≤ δ := by
  have hh := alh38_pos N
  have hL := alh38_mul N
  rw [abs_mul, abs_of_pos hh]
  have : |∑ j, e j| ≤ ∑ _j : ZMod (2 * N + 1), δ :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => he j)
  rw [alCard38 N δ] at this
  calc alh38 N * |∑ j, e j| ≤ alh38 N * ((2 * (N : ℝ) + 1) * δ) := mul_le_mul_of_nonneg_left this hh.le
    _ = ((2 * (N : ℝ) + 1) * alh38 N) * δ := by ring
    _ = δ := by rw [hL]; ring

theorem alPow38 (x : ℕ → SobolevHilbert 1) (u : SobolevHilbert 1) (hx : Tendsto x atTop (𝓝 u))
    (p : ℕ) :
    Tendsto (fun N : ℕ => alh38 N * ∑ j : ZMod (2 * N + 1), ‖alSample38 N (x N) j‖ ^ p) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, ‖alCanon38 u t‖ ^ p)) := by
  have hc : Continuous (fun t : ℝ => (((‖alCanon38 u t‖ ^ p : ℝ)) : ℂ)) := by
    have := alCanon_cont38 u
    fun_prop
  have hp : Function.Periodic (fun t : ℝ => (((‖alCanon38 u t‖ ^ p : ℝ)) : ℂ)) 1 := by
    intro t; simp only [alCanon_periodic38 u t]
  have hR := riemann38 _ hc hp
  rw [intervalIntegral.integral_ofReal] at hR
  have hR' : Tendsto (fun N : ℕ => alh38 N * ∑ j : ZMod (2 * N + 1), ‖alCanon38 u (alt38 N j)‖ ^ p)
      atTop (𝓝 (∫ t in (0 : ℝ)..1, ‖alCanon38 u t‖ ^ p)) := by
    rw [Complex.isometry_ofReal.isEmbedding.tendsto_nhds_iff]
    refine hR.congr (fun N => ?_)
    simp only [Function.comp_def]
    push_cast
    rfl
  set C0 : ℝ := ‖reciprocalBracketL2‖ with hC0
  set R : ℝ := (‖u‖ + 1) * C0 with hRdef
  have hR0 : 0 ≤ R := by positivity
  have hxb : ∀ᶠ N in atTop, ‖x N‖ ≤ ‖u‖ + 1 := by
    have hxn : Tendsto (fun N : ℕ => ‖x N - u‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hx
    have := (Metric.tendsto_nhds.mp hxn) 1 one_pos
    filter_upwards [this] with N hN
    rw [Real.dist_eq, sub_zero] at hN
    have := (abs_lt.mp hN).2
    have h2 := norm_le_norm_add_norm_sub' (x N) u
    have h3 := norm_sub_rev (x N) u
    linarith
  have hdiff : Tendsto (fun N : ℕ => alh38 N * ∑ j : ZMod (2 * N + 1), ‖alSample38 N (x N) j‖ ^ p
      - alh38 N * ∑ j : ZMod (2 * N + 1), ‖alCanon38 u (alt38 N j)‖ ^ p) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set η : ℝ := ε / 2 / ((p : ℝ) * R ^ (p - 1) + 1) with hη
    have hη0 : 0 < η := by positivity
    filter_upwards [alUnif_close38 x u hx (fun _ => 0) tendsto_const_nhds η hη0, hxb] with N hN hxN
    rw [Real.dist_eq, sub_zero, ← mul_sub, ← Finset.sum_sub_distrib]
    have := alSupSum38 N (fun j => ‖alSample38 N (x N) j‖ ^ p - ‖alCanon38 u (alt38 N j)‖ ^ p)
      (η * ((p : ℝ) * R ^ (p - 1))) (by
        intro j
        have h1 := abs_pow_sub_pow_le (‖alSample38 N (x N) j‖) (‖alCanon38 u (alt38 N j)‖) p
        have hs : ‖alSample38 N (x N) j‖ ≤ R := by
          calc _ ≤ ‖x N‖ * C0 := alCanon_norm_le38 _ _
            _ ≤ (‖u‖ + 1) * C0 := mul_le_mul_of_nonneg_right hxN (norm_nonneg _)
        have hu' : ‖alCanon38 u (alt38 N j)‖ ≤ R := by
          calc _ ≤ ‖u‖ * C0 := alCanon_norm_le38 _ _
            _ ≤ (‖u‖ + 1) * C0 := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
        have hm : max |‖alSample38 N (x N) j‖| |‖alCanon38 u (alt38 N j)‖| ≤ R := by
          apply max_le
          · rw [abs_of_nonneg (norm_nonneg _)]; exact hs
          · rw [abs_of_nonneg (norm_nonneg _)]; exact hu'
        have hd : |‖alSample38 N (x N) j‖ - ‖alCanon38 u (alt38 N j)‖| ≤ η := by
          refine (abs_norm_sub_norm_le _ _).trans ?_
          have := hN (alt38 N j)
          simpa [alSample38] using this.le
        calc _ ≤ _ := h1
          _ ≤ η * (p : ℝ) * R ^ (p - 1) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right hd (by positivity))
              (pow_le_pow_left₀ (by positivity) hm _) (by positivity) (by positivity)
          _ = _ := by ring)
    refine lt_of_le_of_lt this ?_
    rw [hη]
    have hq : 0 < (p : ℝ) * R ^ (p - 1) + 1 := by positivity
    calc ε / 2 / ((p : ℝ) * R ^ (p - 1) + 1) * ((p : ℝ) * R ^ (p - 1))
        ≤ ε / 2 / ((p : ℝ) * R ^ (p - 1) + 1) * ((p : ℝ) * R ^ (p - 1) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  have := hdiff.add hR'
  simpa using this
end Sec_c3

section Sec_c4
open Finset Filter Topology NlsGge.Pilot NlsGge.Analysis
open NlsGge.HierarchyRiccati.Core

theorem alR_sample38 (N : ℕ) (v : ZMod (2 * N + 1) → ℂ) (j : ZMod (2 * N + 1)) :
    alR (fun j => (alh38 N : ℂ) * v j) j = alh38 N ^ 2 * ‖v j‖ ^ 2 := by
  unfold alR; exact alNormMul38 _ (alh38_pos N) _

theorem alSampleBound38 (x : ℕ → SobolevHilbert 1) (u : SobolevHilbert 1)
    (hx : Tendsto x atTop (𝓝 u)) :
    ∀ᶠ N in atTop, ∀ j, ‖alSample38 N (x N) j‖ ≤ (‖u‖ + 1) * ‖reciprocalBracketL2‖ := by
  have hxn : Tendsto (fun N : ℕ => ‖x N - u‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hx
  have := (Metric.tendsto_nhds.mp hxn) 1 one_pos
  filter_upwards [this] with N hN j
  rw [Real.dist_eq, sub_zero] at hN
  have h1 := (abs_lt.mp hN).2
  have h2 := norm_le_norm_add_norm_sub' (x N) u
  have h3 := norm_sub_rev (x N) u
  calc _ ≤ ‖x N‖ * ‖reciprocalBracketL2‖ := alCanon_norm_le38 _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

theorem alDiskSample38 (x : ℕ → SobolevHilbert 1) (u : SobolevHilbert 1)
    (hx : Tendsto x atTop (𝓝 u)) :
    ∀ᶠ N in atTop, ∀ j, alh38 N * ‖alSample38 N (x N) j‖ < 1 := by
  set R : ℝ := (‖u‖ + 1) * ‖reciprocalBracketL2‖ with hR
  have hR0 : 0 ≤ R := by positivity
  have h1 : ∀ᶠ N in atTop, alh38 N < 1 / (R + 1) :=
    alh_tendsto38.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [h1, alSampleBound38 x u hx] with N hN hb j
  have hh := alh38_pos N
  calc alh38 N * ‖alSample38 N (x N) j‖ ≤ alh38 N * R := mul_le_mul_of_nonneg_left (hb j) hh.le
    _ ≤ 1 / (R + 1) * R := mul_le_mul_of_nonneg_right hN.le hR0
    _ < 1 := by
        rw [one_div, inv_mul_lt_iff₀ (by positivity)]; linarith

theorem alP12bound38 (β₀ β₁ β₂ h W Sl Sl2 S4 S6 : ℝ) (hh : 0 < h) (h1 : h ≤ 1) (hW0 : 0 ≤ W)
    (l1 : |Sl| ≤ 2 * h ^ 3 * W ^ 2) (l2 : |Sl - h ^ 4 / 2 * S4| ≤ 2 * h ^ 5 * W ^ 3)
    (l3 : |Sl2 - h ^ 6 / 3 * S6| ≤ 2 * h ^ 7 * W ^ 4) :
    |((β₀ - h) / h + 2 * β₁ / h ^ 3) * Sl + β₂ / h ^ 5 * (6 * Sl2)
        - (β₁ * (h * S4) + 2 * β₂ * (h * S6))|
      ≤ (2 * (|β₀| + 1) * W ^ 2 + 4 * |β₁| * W ^ 3 + 12 * |β₂| * W ^ 4) * h ^ 2 := by
  have eq : ((β₀ - h) / h + 2 * β₁ / h ^ 3) * Sl + β₂ / h ^ 5 * (6 * Sl2)
      - (β₁ * (h * S4) + 2 * β₂ * (h * S6))
      = (β₀ - h) / h * Sl + 2 * β₁ / h ^ 3 * (Sl - h ^ 4 / 2 * S4)
        + 6 * β₂ / h ^ 5 * (Sl2 - h ^ 6 / 3 * S6) := by
    field_simp
    ring
  rw [eq]
  have b1 : |(β₀ - h) / h * Sl| ≤ 2 * (|β₀| + 1) * W ^ 2 * h ^ 2 := by
    rw [abs_mul, abs_div, abs_of_pos hh]
    have hb0 : |β₀ - h| ≤ |β₀| + 1 := by
      calc |β₀ - h| ≤ |β₀| + |h| := abs_sub _ _
        _ ≤ |β₀| + 1 := by rw [abs_of_pos hh]; linarith
    calc |β₀ - h| / h * |Sl| ≤ (|β₀| + 1) / h * (2 * h ^ 3 * W ^ 2) :=
          mul_le_mul (div_le_div_of_nonneg_right hb0 hh.le) l1 (abs_nonneg _) (by positivity)
      _ = 2 * (|β₀| + 1) * W ^ 2 * h ^ 2 := by field_simp
  have b2 : |2 * β₁ / h ^ 3 * (Sl - h ^ 4 / 2 * S4)| ≤ 4 * |β₁| * W ^ 3 * h ^ 2 := by
    rw [abs_mul, abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < h ^ 3), abs_two]
    calc 2 * |β₁| / h ^ 3 * |Sl - h ^ 4 / 2 * S4|
        ≤ 2 * |β₁| / h ^ 3 * (2 * h ^ 5 * W ^ 3) :=
          mul_le_mul_of_nonneg_left l2 (by positivity)
      _ = 4 * |β₁| * W ^ 3 * h ^ 2 := by field_simp; ring
  have b3 : |6 * β₂ / h ^ 5 * (Sl2 - h ^ 6 / 3 * S6)| ≤ 12 * |β₂| * W ^ 4 * h ^ 2 := by
    rw [abs_mul, abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < h ^ 5)]
    rw [show |(6 : ℝ)| = 6 by norm_num]
    calc 6 * |β₂| / h ^ 5 * |Sl2 - h ^ 6 / 3 * S6|
        ≤ 6 * |β₂| / h ^ 5 * (2 * h ^ 7 * W ^ 4) :=
          mul_le_mul_of_nonneg_left l3 (by positivity)
      _ = 12 * |β₂| * W ^ 4 * h ^ 2 := by field_simp; ring
  have e2 : (2 * (|β₀| + 1) * W ^ 2 + 4 * |β₁| * W ^ 3 + 12 * |β₂| * W ^ 4) * h ^ 2
      = 2 * (|β₀| + 1) * W ^ 2 * h ^ 2 + 4 * |β₁| * W ^ 3 * h ^ 2 + 12 * |β₂| * W ^ 4 * h ^ 2 := by ring
  rw [e2]
  exact (abs_add_three _ _ _).trans (add_le_add (add_le_add b1 b2) b3)

theorem alP12_38 (β₀ β₁ β₂ : ℝ) (x : ℕ → SobolevHilbert 1) (u : SobolevHilbert 1)
    (hx : Tendsto x atTop (𝓝 u)) :
    Tendsto (fun N : ℕ =>
      ((β₀ - alh38 N) / alh38 N + 2 * β₁ / alh38 N ^ 3) * ∑ j : ZMod (2 * N + 1),
          alEll (alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j)
        + β₂ / alh38 N ^ 5 * (6 * ∑ j : ZMod (2 * N + 1),
              (-Real.log (1 - alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j)
                - alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j
                - (1 / 2) * alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j ^ 2))) atTop
      (𝓝 (β₁ * (∫ t in (0 : ℝ)..1, ‖alCanon38 u t‖ ^ 4)
          + 2 * β₂ * (∫ t in (0 : ℝ)..1, ‖alCanon38 u t‖ ^ 6))) := by
  have m4 := alPow38 x u hx 4
  have m6 := alPow38 x u hx 6
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (2 * (|β₀| + 1) * ((((‖u‖ + 1) * ‖reciprocalBracketL2‖)) ^ 2) ^ 2
          + 4 * |β₁| * ((((‖u‖ + 1) * ‖reciprocalBracketL2‖)) ^ 2) ^ 3
          + 12 * |β₂| * ((((‖u‖ + 1) * ‖reciprocalBracketL2‖)) ^ 2) ^ 4) := ⟨_, rfl⟩
  have hE : Tendsto (fun N : ℕ =>
      (((β₀ - alh38 N) / alh38 N + 2 * β₁ / alh38 N ^ 3) * ∑ j : ZMod (2 * N + 1),
          alEll (alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j)
        + β₂ / alh38 N ^ 5 * (6 * ∑ j : ZMod (2 * N + 1),
              (-Real.log (1 - alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j)
                - alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j
                - (1 / 2) * alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j ^ 2)))
      - (β₁ * (alh38 N * ∑ j : ZMod (2 * N + 1), ‖alSample38 N (x N) j‖ ^ 4)
        + 2 * β₂ * (alh38 N * ∑ j : ZMod (2 * N + 1), ‖alSample38 N (x N) j‖ ^ 6))) atTop (𝓝 0) := by
    have hbd : ∀ᶠ N in atTop, ‖(((β₀ - alh38 N) / alh38 N + 2 * β₁ / alh38 N ^ 3) * ∑ j : ZMod (2 * N + 1),
          alEll (alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j)
        + β₂ / alh38 N ^ 5 * (6 * ∑ j : ZMod (2 * N + 1),
              (-Real.log (1 - alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j)
                - alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j
                - (1 / 2) * alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j ^ 2)))
      - (β₁ * (alh38 N * ∑ j : ZMod (2 * N + 1), ‖alSample38 N (x N) j‖ ^ 4)
        + 2 * β₂ * (alh38 N * ∑ j : ZMod (2 * N + 1), ‖alSample38 N (x N) j‖ ^ 6))‖
        ≤ K * alh38 N ^ 2 := by
      have e1 : ∀ᶠ N in atTop, alh38 N ≤ 1 := alh_tendsto38.eventually (Iic_mem_nhds one_pos)
      have e2 : ∀ᶠ N in atTop, alh38 N ^ 2 * (((‖u‖ + 1) * ‖reciprocalBracketL2‖) ^ 2) ≤ 1 / 2 := by
        have : Tendsto (fun N => alh38 N ^ 2 * (((‖u‖ + 1) * ‖reciprocalBracketL2‖) ^ 2)) atTop
            (𝓝 (0 ^ 2 * (((‖u‖ + 1) * ‖reciprocalBracketL2‖) ^ 2))) :=
          ((alh_tendsto38.pow 2).mul_const _)
        rw [show (0 : ℝ) ^ 2 * (((‖u‖ + 1) * ‖reciprocalBracketL2‖) ^ 2) = 0 by ring] at this
        exact this.eventually (Iic_mem_nhds (by norm_num))
      filter_upwards [e1, e2, alSampleBound38 x u hx] with N h1 h2 hb
      have hh := alh38_pos N
      have hw0 : ∀ j : ZMod (2 * N + 1), 0 ≤ ‖alSample38 N (x N) j‖ ^ 2 := fun j => by positivity
      have hwW : ∀ j : ZMod (2 * N + 1), ‖alSample38 N (x N) j‖ ^ 2
          ≤ ((‖u‖ + 1) * ‖reciprocalBracketL2‖) ^ 2 := fun j =>
        pow_le_pow_left₀ (norm_nonneg _) (hb j) 2
      obtain ⟨l1, l2, l3⟩ := alLogSums38 N (fun j => ‖alSample38 N (x N) j‖ ^ 2)
        (((‖u‖ + 1) * ‖reciprocalBracketL2‖) ^ 2) hw0 hwW h2
      have hrs : ∀ j, alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j
          = alh38 N ^ 2 * ‖alSample38 N (x N) j‖ ^ 2 := fun j => alR_sample38 N _ j
      simp_rw [hrs]
      have hs4 : ∑ j : ZMod (2 * N + 1), (‖alSample38 N (x N) j‖ ^ 2) ^ 2
          = ∑ j : ZMod (2 * N + 1), ‖alSample38 N (x N) j‖ ^ 4 :=
        Finset.sum_congr rfl fun j _ => by ring
      have hs6 : ∑ j : ZMod (2 * N + 1), (‖alSample38 N (x N) j‖ ^ 2) ^ 3
          = ∑ j : ZMod (2 * N + 1), ‖alSample38 N (x N) j‖ ^ 6 :=
        Finset.sum_congr rfl fun j _ => by ring
      rw [hs4] at l2
      rw [hs6] at l3
      rw [Real.norm_eq_abs]
      rw [hK]
      exact alP12bound38 β₀ β₁ β₂ (alh38 N) _ _ _ _ _ hh h1 (by positivity) l1 l2 l3
    have hK0 : Tendsto (fun N : ℕ => K * alh38 N ^ 2) atTop (𝓝 0) := by
      have := (alh_tendsto38.pow 2).const_mul K
      rwa [show K * (0 : ℝ) ^ 2 = 0 by ring] at this
    exact squeeze_zero_norm' hbd hK0
  have hmain : Tendsto (fun N : ℕ => β₁ * (alh38 N * ∑ j : ZMod (2 * N + 1), ‖alSample38 N (x N) j‖ ^ 4)
        + 2 * β₂ * (alh38 N * ∑ j : ZMod (2 * N + 1), ‖alSample38 N (x N) j‖ ^ 6)) atTop
      (𝓝 (β₁ * (∫ t in (0 : ℝ)..1, ‖alCanon38 u t‖ ^ 4)
          + 2 * β₂ * (∫ t in (0 : ℝ)..1, ‖alCanon38 u t‖ ^ 6))) :=
    (m4.const_mul β₁).add (m6.const_mul (2 * β₂))
  simpa using hE.add hmain
end Sec_c4

section Sec_c5
open Finset Filter Topology NlsGge.Pilot NlsGge.Analysis
open NlsGge.HierarchyRiccati.Core

/-- Coefficient arrays for the three squared difference quotients of `C:eq:Ksquares`. -/
def alArrA38 (N : ℕ) (x : SobolevHilbert 1) (j : ZMod (2 * N + 1)) : ℂ :=
  (starRingEnd ℂ) (alSample38 N x (j + 1) + alSample38 N x j) / 2

def alArrC38 (N : ℕ) (x : SobolevHilbert 1) (j : ZMod (2 * N + 1)) : ℂ :=
  (starRingEnd ℂ) (alSample38 N x (j - 1))

theorem alFd_sample38 (N : ℕ) (x : SobolevHilbert 1) (j : ZMod (2 * N + 1)) :
    alFd38 N x j = (alSample38 N x (j + 1) - alSample38 N x j) / (alh38 N : ℂ) := by
  unfold alFd38; rw [alSample_succ38]; rfl

theorem alBd_sample38 (N : ℕ) (x : SobolevHilbert 1) (j : ZMod (2 * N + 1)) :
    alBd38 N x j = (alSample38 N x j - alSample38 N x (j - 1)) / (alh38 N : ℂ) := by
  unfold alBd38; rw [alSample_pred38]; rfl

theorem alP3j38 (N : ℕ) (x : SobolevHilbert 1) (j : ZMod (2 * N + 1)) :
    (3 / 2) * (alR (fun j => (alh38 N : ℂ) * alSample38 N x j) (j + 1)
        - alR (fun j => (alh38 N : ℂ) * alSample38 N x j) j) ^ 2
      + alR (fun j => (alh38 N : ℂ) * alSample38 N x j) j *
          ‖(alh38 N : ℂ) * alSample38 N x (j + 1) - (alh38 N : ℂ) * alSample38 N x (j - 1)‖ ^ 2
      + 2 * (((alh38 N : ℂ) * alSample38 N x j * (starRingEnd ℂ)
          ((alh38 N : ℂ) * alSample38 N x (j - 1))).im) ^ 2
    = alh38 N ^ 6 * (3 * ‖alArrA38 N x j * alFd38 N x j + 0 * alBd38 N x j‖ ^ 2
        + 3 * ((alArrA38 N x j * alFd38 N x j + 0 * alBd38 N x j) ^ 2).re
        + ‖alSample38 N x j * alFd38 N x j + alSample38 N x j * alBd38 N x j‖ ^ 2
        + ‖0 * alFd38 N x j + alArrC38 N x j * alBd38 N x j‖ ^ 2
        - ((0 * alFd38 N x j + alArrC38 N x j * alBd38 N x j) ^ 2).re) := by
  have hh := alh38_pos N
  have hd := alFd_sample38 N x j
  have hb := alBd_sample38 N x j
  have A := alP3A38 (alh38 N) hh (alSample38 N x (j + 1)) (alSample38 N x j) _ hd
  have B := alP3B38 (alh38 N) hh (alSample38 N x (j + 1)) (alSample38 N x j) (alSample38 N x (j - 1)) _ _ hd hb
  have C := alP3C38 (alh38 N) hh (alSample38 N x j) (alSample38 N x (j - 1)) _ hb
  simp only [zero_mul, add_zero, zero_add, alArrA38, alArrC38]
  simp only [zero_mul, add_zero, zero_add] at C
  unfold alR
  simp only []
  rw [A, B, C]
  ring

theorem alStar_apply38 (F : C(PhysicalCircle, ℂ)) (t : ℝ) :
    (star F) (t : PhysicalCircle) = (starRingEnd ℂ) (F (t : PhysicalCircle)) := rfl

section Close
variable (x : ℕ → SobolevHilbert 1) (u : SobolevHilbert 1) (hx : Tendsto x atTop (𝓝 u))
include hx

theorem alCloseQ38 (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ j : ZMod (2 * N + 1),
      ‖alSample38 N (x N) j - (physicalH1CanonicalContinuousRepresentativeCLM u)
        (alt38 N j : PhysicalCircle)‖ < ε := by
  filter_upwards [alUnif_close38 x u hx (fun _ => 0) tendsto_const_nhds ε hε] with N hN j
  have := hN (alt38 N j)
  simpa [alSample38, alCanon38] using this

theorem alCloseC38 (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ j : ZMod (2 * N + 1),
      ‖alArrC38 N (x N) j - (star (physicalH1CanonicalContinuousRepresentativeCLM u))
        (alt38 N j : PhysicalCircle)‖ < ε := by
  filter_upwards [alUnif_close38 x u hx (fun N => -alh38 N)
    (by simpa using alh_tendsto38.neg) ε hε] with N hN j
  have := hN (alt38 N j)
  rw [alArrC38, alSample_pred38, alStar_apply38, ← map_sub, Complex.norm_conj]
  simpa [sub_eq_add_neg, alCanon38] using this

theorem alCloseA38 (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ j : ZMod (2 * N + 1),
      ‖alArrA38 N (x N) j - (star (physicalH1CanonicalContinuousRepresentativeCLM u))
        (alt38 N j : PhysicalCircle)‖ < ε := by
  filter_upwards [alUnif_close38 x u hx alh38 alh_tendsto38 (ε) hε,
    alUnif_close38 x u hx (fun _ => 0) tendsto_const_nhds (ε) hε] with N h1 h2 j
  have a1 := h1 (alt38 N j)
  have a2 := h2 (alt38 N j)
  rw [alArrA38, alSample_succ38, alStar_apply38]
  have e : (starRingEnd ℂ) (alCanon38 (x N) (alt38 N j + alh38 N) + alSample38 N (x N) j) / 2
      - (starRingEnd ℂ) (physicalH1CanonicalContinuousRepresentativeCLM u (alt38 N j : PhysicalCircle))
      = (starRingEnd ℂ) (((alCanon38 (x N) (alt38 N j + alh38 N)
          - alCanon38 u (alt38 N j)) + (alCanon38 (x N) (alt38 N j) - alCanon38 u (alt38 N j)))) / 2 := by
    simp only [alSample38, alCanon38, map_add, map_sub]
    ring
  rw [e, norm_div, Complex.norm_conj]
  have : ‖(alCanon38 (x N) (alt38 N j + alh38 N) - alCanon38 u (alt38 N j))
      + (alCanon38 (x N) (alt38 N j) - alCanon38 u (alt38 N j))‖ < 2 * ε := by
    calc _ ≤ _ := norm_add_le _ _
      _ < ε + ε := add_lt_add (by simpa using a1) (by simpa using a2)
      _ = 2 * ε := by ring
  simp only [Complex.norm_ofNat]
  linarith

end Close

theorem alP3eq38 (β₂ : ℝ) (N : ℕ) (x : SobolevHilbert 1) :
    β₂ / alh38 N ^ 5 * ((3 / 2) * ∑ j : ZMod (2 * N + 1),
            (alR (fun j => (alh38 N : ℂ) * alSample38 N x j) (j + 1)
              - alR (fun j => (alh38 N : ℂ) * alSample38 N x j) j) ^ 2
          + ∑ j : ZMod (2 * N + 1), alR (fun j => (alh38 N : ℂ) * alSample38 N x j) j *
              ‖(alh38 N : ℂ) * alSample38 N x (j + 1) - (alh38 N : ℂ) * alSample38 N x (j - 1)‖ ^ 2
          + 2 * ∑ j : ZMod (2 * N + 1),
              (((alh38 N : ℂ) * alSample38 N x j * (starRingEnd ℂ)
                ((alh38 N : ℂ) * alSample38 N x (j - 1))).im) ^ 2)
    = β₂ * (3 * (alh38 N * ∑ j : ZMod (2 * N + 1),
            ‖alArrA38 N x j * alFd38 N x j + 0 * alBd38 N x j‖ ^ 2)
        + 3 * (((alh38 N : ℂ) * ∑ j : ZMod (2 * N + 1),
            (alArrA38 N x j * alFd38 N x j + 0 * alBd38 N x j) ^ 2).re)
        + alh38 N * ∑ j : ZMod (2 * N + 1),
            ‖alSample38 N x j * alFd38 N x j + alSample38 N x j * alBd38 N x j‖ ^ 2
        + alh38 N * ∑ j : ZMod (2 * N + 1),
            ‖0 * alFd38 N x j + alArrC38 N x j * alBd38 N x j‖ ^ 2
        - (((alh38 N : ℂ) * ∑ j : ZMod (2 * N + 1),
            (0 * alFd38 N x j + alArrC38 N x j * alBd38 N x j) ^ 2).re)) := by
  have hh := alh38_pos N
  have key : ((3 / 2) * ∑ j : ZMod (2 * N + 1),
            (alR (fun j => (alh38 N : ℂ) * alSample38 N x j) (j + 1)
              - alR (fun j => (alh38 N : ℂ) * alSample38 N x j) j) ^ 2
          + ∑ j : ZMod (2 * N + 1), alR (fun j => (alh38 N : ℂ) * alSample38 N x j) j *
              ‖(alh38 N : ℂ) * alSample38 N x (j + 1) - (alh38 N : ℂ) * alSample38 N x (j - 1)‖ ^ 2
          + 2 * ∑ j : ZMod (2 * N + 1),
              (((alh38 N : ℂ) * alSample38 N x j * (starRingEnd ℂ)
                ((alh38 N : ℂ) * alSample38 N x (j - 1))).im) ^ 2)
      = ∑ j : ZMod (2 * N + 1), alh38 N ^ 6 * (3 * ‖alArrA38 N x j * alFd38 N x j + 0 * alBd38 N x j‖ ^ 2
        + 3 * ((alArrA38 N x j * alFd38 N x j + 0 * alBd38 N x j) ^ 2).re
        + ‖alSample38 N x j * alFd38 N x j + alSample38 N x j * alBd38 N x j‖ ^ 2
        + ‖0 * alFd38 N x j + alArrC38 N x j * alBd38 N x j‖ ^ 2
        - ((0 * alFd38 N x j + alArrC38 N x j * alBd38 N x j) ^ 2).re) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => alP3j38 N x j
  rw [key, ← Finset.mul_sum]
  have hre : ∀ (f : ZMod (2 * N + 1) → ℂ),
      (((alh38 N : ℂ) * ∑ j, f j).re) = alh38 N * ∑ j, (f j).re := by
    intro f
    rw [Complex.re_ofReal_mul, Complex.re_sum]
  rw [hre, hre]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  field_simp

theorem alStarNorm38 (F : C(PhysicalCircle, ℂ)) (d : PhysicalL2) :
    ‖alMult38 (star F) d‖ ^ 2 = ‖alMult38 F d‖ ^ 2 := by
  rw [alMult_norm_sq38, alMult_norm_sq38]
  refine congrArg _ (funext fun y => ?_)
  simp [ContinuousMap.star_apply]

theorem alDoubleNorm38 (F : C(PhysicalCircle, ℂ)) (d : PhysicalL2) :
    ‖alMult38 (F + F) d‖ ^ 2 = 4 * ‖alMult38 F d‖ ^ 2 := by
  have : alMult38 (F + F) d = (2 : ℂ) • alMult38 F d := by
    rw [map_add, add_apply, two_smul]
  rw [this, norm_smul]
  simp only [Complex.norm_ofNat]
  ring

theorem alP3_38 (β₂ : ℝ) (x : ℕ → SobolevHilbert 1) (u : SobolevHilbert 1)
    (hF : ∀ N, alInF38 N (x N)) (hx : Tendsto x atTop (𝓝 u)) :
    Tendsto (fun N : ℕ => β₂ / alh38 N ^ 5 * ((3 / 2) * ∑ j : ZMod (2 * N + 1),
            (alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) (j + 1)
              - alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j) ^ 2
          + ∑ j : ZMod (2 * N + 1), alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j *
              ‖(alh38 N : ℂ) * alSample38 N (x N) (j + 1)
                - (alh38 N : ℂ) * alSample38 N (x N) (j - 1)‖ ^ 2
          + 2 * ∑ j : ZMod (2 * N + 1),
              (((alh38 N : ℂ) * alSample38 N (x N) j * (starRingEnd ℂ)
                ((alh38 N : ℂ) * alSample38 N (x N) (j - 1))).im) ^ 2)) atTop
      (𝓝 (β₂ * (8 * physicalH1WeightedDerivativeSquareAfterHolderInnerPrerequisites u
          + physicalH1Q4CrossPairingAfterCanonicalMultiplication u))) := by
  set F : C(PhysicalCircle, ℂ) := physicalH1CanonicalContinuousRepresentativeCLM u with hFdef
  have z0 : ∀ ε > 0, ∀ᶠ N in atTop, ∀ j : ZMod (2 * N + 1),
      ‖(0 : ℂ) - (0 : C(PhysicalCircle, ℂ)) (alt38 N j : PhysicalCircle)‖ < ε := by
    intro ε hε; exact Filter.Eventually.of_forall fun N j => by simpa using hε
  -- the four limits
  have L1 := alLim1_38 x u hF hx (star F) 0 (fun N j => alArrA38 N (x N) j) (fun N j => 0)
    (fun ε hε => alCloseA38 x u hx ε hε) z0
  have L1c := alLim2_38 x u hF hx (star F) 0 (fun N j => alArrA38 N (x N) j) (fun N j => 0)
    (fun ε hε => alCloseA38 x u hx ε hε) z0
  have L2 := alLim1_38 x u hF hx F F (fun N j => alSample38 N (x N) j) (fun N j => alSample38 N (x N) j)
    (fun ε hε => alCloseQ38 x u hx ε hε) (fun ε hε => alCloseQ38 x u hx ε hε)
  have L3 := alLim1_38 x u hF hx 0 (star F) (fun N j => 0) (fun N j => alArrC38 N (x N) j)
    z0 (fun ε hε => alCloseC38 x u hx ε hε)
  have L3c := alLim2_38 x u hF hx 0 (star F) (fun N j => 0) (fun N j => alArrC38 N (x N) j)
    z0 (fun ε hε => alCloseC38 x u hx ε hε)
  rw [add_zero] at L1 L1c
  rw [zero_add] at L3 L3c
  have R1 := (Complex.continuous_re.tendsto _).comp L1c
  have R3 := (Complex.continuous_re.tendsto _).comp L3c
  have comb := ((((L1.const_mul 3).add (R1.const_mul 3)).add L2).add L3).sub R3
  have comb2 := comb.const_mul β₂
  refine (comb2.congr (fun N => (alP3eq38 β₂ N (x N)).symm)).trans_eq ?_
  have e1 : ‖alMult38 (star F) (physicalH1DerivativeL2CLM u)‖ ^ 2
      = physicalH1WeightedDerivativeSquareAfterHolderInnerPrerequisites u := by
    rw [alStarNorm38]; rfl
  have e2 : ‖alMult38 (F + F) (physicalH1DerivativeL2CLM u)‖ ^ 2
      = 4 * physicalH1WeightedDerivativeSquareAfterHolderInnerPrerequisites u := by
    rw [alDoubleNorm38]; rfl
  have e3 : physicalH1Q4CrossPairingAfterCanonicalMultiplication u
      = 2 * (MeasureTheory.L1.integral (physicalL2ProductL1CLM
          (alMult38 (star F) (physicalH1DerivativeL2CLM u))
          (alMult38 (star F) (physicalH1DerivativeL2CLM u)))).re := rfl
  rw [e3, e1, e2]
  ring_nf
end Sec_c5

section Sec_c6
open Finset Filter Topology NlsGge.Pilot NlsGge.Analysis
open NlsGge.HierarchyRiccati.Core

/-- `V₂(u) = β₁ ∫|u|⁴ + β₂ ∫ [2|u|⁶ + 6|u|²|u'|² + ((|u|²)')²]` (`C:eq:V2positive`), built from the
continuous `H¹` pieces: quartic integral and the `Q₄` lower-order remainder
`cross + 8·weighted-derivative-square + 2·sixth-power` (see `alV2_eq_integral38`). -/
def alV2_38 (β₁ β₂ : ℝ) (u : SobolevHilbert 1) : ℝ :=
  β₁ * physicalH1QuarticIntegralAfterScalarL1Prerequisites
      (physicalH1CanonicalContinuousRepresentativeCLM u)
    + β₂ * physicalH1Q4LowerOrderRemainderAfterCanonicalComponents u

theorem alQuartic_eq38 (u : SobolevHilbert 1) :
    physicalH1QuarticIntegralAfterScalarL1Prerequisites
      (physicalH1CanonicalContinuousRepresentativeCLM u)
      = ∫ t in (0 : ℝ)..1, ‖alCanon38 u t‖ ^ 4 := by
  rw [physicalH1QuarticIntegralAfterScalarL1Prerequisites_eq_integral]
  exact (NlsGge.HierarchyRiccati.unitIntervalIntegral_lift_eq_spatialHaar
    (fun y : PhysicalCircle => ‖physicalH1CanonicalContinuousRepresentativeCLM u y‖ ^ 4)).symm

theorem alSixth_eq38 (u : SobolevHilbert 1) :
    physicalH1SixthPowerIntegralAfterCanonicalRepresentative u
      = ∫ t in (0 : ℝ)..1, ‖alCanon38 u t‖ ^ 6 := by
  rw [physicalH1SixthPowerIntegralAfterCanonicalRepresentative_eq_integral]
  exact (NlsGge.HierarchyRiccati.unitIntervalIntegral_lift_eq_spatialHaar
    (fun y : PhysicalCircle => ‖physicalH1CanonicalContinuousRepresentativeCLM u y‖ ^ 6)).symm

/-- `C:lem:sampling` (paper/v2.tex l.2143-2183). -/
theorem alSampling38 (β₀ β₁ β₂ : ℝ) (x : ℕ → SobolevHilbert 1) (u : SobolevHilbert 1)
    (hF : ∀ N, alInF38 N (x N)) (hx : Tendsto x atTop (𝓝 u)) :
    (∀ᶠ N in atTop, ∀ j : ZMod (2 * N + 1), alh38 N * ‖alSample38 N (x N) j‖ < 1)
    ∧ Tendsto (fun N : ℕ => alRh38 β₀ β₁ β₂ N (alSample38 N (x N))) atTop
        (𝓝 (alV2_38 β₁ β₂ u)) := by
  refine ⟨alDiskSample38 x u hx, ?_⟩
  have h12 := alP12_38 β₀ β₁ β₂ x u hx
  have h3 := alP3_38 β₂ x u hF hx
  have hsum := h12.add h3
  have hcongr : ∀ N, alRh38 β₀ β₁ β₂ N (alSample38 N (x N)) =
      (((β₀ - alh38 N) / alh38 N + 2 * β₁ / alh38 N ^ 3) * ∑ j : ZMod (2 * N + 1),
          alEll (alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j)
        + β₂ / alh38 N ^ 5 * (6 * ∑ j : ZMod (2 * N + 1),
              (-Real.log (1 - alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j)
                - alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j
                - (1 / 2) * alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j ^ 2)))
      + β₂ / alh38 N ^ 5 * ((3 / 2) * ∑ j : ZMod (2 * N + 1),
            (alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) (j + 1)
              - alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j) ^ 2
          + ∑ j : ZMod (2 * N + 1), alR (fun j => (alh38 N : ℂ) * alSample38 N (x N) j) j *
              ‖(alh38 N : ℂ) * alSample38 N (x N) (j + 1)
                - (alh38 N : ℂ) * alSample38 N (x N) (j - 1)‖ ^ 2
          + 2 * ∑ j : ZMod (2 * N + 1),
              (((alh38 N : ℂ) * alSample38 N (x N) j * (starRingEnd ℂ)
                ((alh38 N : ℂ) * alSample38 N (x N) (j - 1))).im) ^ 2) := by
    intro N
    rw [alRh_eq38 β₀ β₁ β₂ (hF N)]
    ring
  refine (hsum.congr (fun N => (hcongr N).symm)).trans_eq ?_
  unfold alV2_38 physicalH1Q4LowerOrderRemainderAfterCanonicalComponents
  rw [alQuartic_eq38, alSixth_eq38]
  ring_nf
end Sec_c6

end NlsGge.AblowitzLadik

end

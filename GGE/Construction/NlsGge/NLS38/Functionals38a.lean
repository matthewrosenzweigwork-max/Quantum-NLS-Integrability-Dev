import NlsGge.NLS38.SeqConv38
import NlsGge.Birkhoff.F01Determinant38

/-! # GWP piece A7a (part a): mass, kinetic energy, quartic charge, Hamiltonian

Plan: `campaign/GWP_PLAN.md` §7 Part A, piece A7a.  All Sobolev indices are casts of naturals
(§6.0): `seqSobolev38 ((1 : ℕ) : ℝ)`, `SobolevCarrier38 ((1 : ℕ) : ℝ)`.

* `mass x = Σ |x_n|²`, `kin x = Σ (2πn)² |x_n|²`, `quart x = Σ |(x*x)_n|²` (`= ∫|u|⁴`),
  `ham = kin + quart` (`= Q₂`, v2 l.60-62).  All four are totalised `tsum`s; summability on `h¹`
  is proved first (`summable_*_of_h1`), and the value identities are stated for `h¹` data.
* `hn_one_sq`, `quart_nonneg`, `quart_le`, `inner_nonlin_real`.
* Part b (`Functionals38`, the public entry point): the bounded bilinear map `convC38 : h¹ × h¹ → h⁰`, continuity of
  the functionals on `SobolevCarrier38 1` and the derivatives along `C¹` curves of the carrier.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open scoped ComplexConjugate

/-! ## Definitions -/

/-- `Q₀ = ∫|u|² = Σ |x_n|²`. -/
def mass (x : ℤ → ℂ) : ℝ := ∑' n, ‖x n‖ ^ 2

/-- `Σ (2πn)² |x_n|² = ∫|u'|²`. -/
def kin (x : ℤ → ℂ) : ℝ := ∑' n, disp n * ‖x n‖ ^ 2

/-- `Σ |(x*x)_n|² = ∫|u|⁴`. -/
def quart (x : ℤ → ℂ) : ℝ := ∑' n, ‖conv x x n‖ ^ 2

/-- `Q₂ = ∫(|u'|² + |u|⁴)`. -/
def ham (x : ℤ → ℂ) : ℝ := kin x + quart x

theorem ham_def (x : ℤ → ℂ) : ham x = kin x + quart x := rfl

/-! ## Summability on `h¹` -/

theorem sobolevModeWeight_cast_one (n : ℤ) :
    sobolevModeWeight ((1 : ℕ) : ℝ) n = 1 + (n : ℝ) ^ 2 := by
  rw [Nat.cast_one]; exact sobolevModeWeight_one_eq n

theorem japaneseBracket_sq_two_mul_one (n : ℤ) :
    japaneseBracket n ^ (2 * 1) = 1 + (n : ℝ) ^ 2 := by
  unfold japaneseBracket
  rw [mul_one, Real.sq_sqrt (by positivity)]

theorem disp_eq (n : ℤ) : disp n = 4 * Real.pi ^ 2 * (n : ℝ) ^ 2 := by
  unfold disp; ring

theorem disp_nonneg (n : ℤ) : 0 ≤ disp n := by
  rw [disp_eq]; positivity

section H1

variable {x : ℤ → ℂ}

theorem summable_w1_of_h1 (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    Summable fun n : ℤ => (1 + (n : ℝ) ^ 2) * ‖x n‖ ^ 2 := by
  have h := summable_hn_of_mem 1 x hx
  simpa only [japaneseBracket_sq_two_mul_one] using h

theorem summable_sq_of_h1 (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    Summable fun n : ℤ => ‖x n‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun n => by
      have : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
      nlinarith [sq_nonneg ‖x n‖])
    (summable_w1_of_h1 hx)

theorem summable_n2_of_h1 (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    Summable fun n : ℤ => (n : ℝ) ^ 2 * ‖x n‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => by nlinarith [sq_nonneg ‖x n‖])
    (summable_w1_of_h1 hx)

theorem summable_kin_of_h1 (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    Summable fun n : ℤ => disp n * ‖x n‖ ^ 2 := by
  refine ((summable_n2_of_h1 hx).mul_left (4 * Real.pi ^ 2)).congr fun n => ?_
  rw [disp_eq]; ring

theorem mass_nonneg (x : ℤ → ℂ) : 0 ≤ mass x := tsum_nonneg fun _ => sq_nonneg _

theorem kin_nonneg (x : ℤ → ℂ) : 0 ≤ kin x :=
  tsum_nonneg fun n => mul_nonneg (disp_nonneg n) (sq_nonneg _)

theorem hn_one_sq (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    hn 1 x ^ 2 = mass x + kin x / (4 * Real.pi ^ 2) := by
  rw [hn_sq]
  simp only [japaneseBracket_sq_two_mul_one]
  have hpi : (4 * Real.pi ^ 2) ≠ 0 := by positivity
  have hk : kin x / (4 * Real.pi ^ 2) = ∑' n : ℤ, (n : ℝ) ^ 2 * ‖x n‖ ^ 2 := by
    unfold kin
    rw [← tsum_div_const]
    refine tsum_congr fun n => ?_
    rw [disp_eq]; field_simp
  rw [hk, mass, ← (summable_sq_of_h1 hx).tsum_add (summable_n2_of_h1 hx)]
  exact tsum_congr fun n => by ring

theorem mass_le_hn_sq (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) : mass x ≤ hn 1 x ^ 2 := by
  rw [hn_one_sq hx]
  have : 0 ≤ kin x / (4 * Real.pi ^ 2) := div_nonneg (kin_nonneg x) (by positivity)
  linarith

theorem kin_le_hn_sq (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    kin x ≤ 4 * Real.pi ^ 2 * hn 1 x ^ 2 := by
  rw [hn_one_sq hx]
  have h0 := mass_nonneg x
  have hpi : (0 : ℝ) < 4 * Real.pi ^ 2 := by positivity
  rw [mul_add, mul_div_cancel₀ _ hpi.ne']
  nlinarith

/-! ## The quartic charge -/

theorem summable_quart_of_h1 (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    Summable fun n : ℤ => ‖conv x x n‖ ^ 2 :=
  (summable_sq_conv (isL1_of_hn_one x hx).1 (summable_sq_of_h1 hx)).1

theorem quart_nonneg (x : ℤ → ℂ) : 0 ≤ quart x := tsum_nonneg fun _ => sq_nonneg _

theorem quart_le_l1_mass (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    quart x ≤ l1 x ^ 2 * mass x :=
  (summable_sq_conv (isL1_of_hn_one x hx).1 (summable_sq_of_h1 hx)).2

/-- `∫|u|⁴ ≤ C ‖u‖_{h¹}⁴`, with `C = C₁²`. -/
theorem quart_le (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) : quart x ≤ C1 ^ 2 * hn 1 x ^ 4 := by
  obtain ⟨_, hl⟩ := isL1_of_hn_one x hx
  have hl0 : 0 ≤ l1 x := tsum_nonneg fun _ => norm_nonneg _
  have h1 : l1 x ^ 2 ≤ (C1 * hn 1 x) ^ 2 := pow_le_pow_left₀ hl0 hl 2
  have h2 := mass_le_hn_sq hx
  have h3 := quart_le_l1_mass hx
  have hm0 := mass_nonneg x
  calc quart x ≤ l1 x ^ 2 * mass x := h3
    _ ≤ (C1 * hn 1 x) ^ 2 * hn 1 x ^ 2 :=
        mul_le_mul h1 h2 hm0 (sq_nonneg _)
    _ = C1 ^ 2 * hn 1 x ^ 4 := by ring

theorem ham_nonneg (x : ℤ → ℂ) : 0 ≤ ham x := add_nonneg (kin_nonneg x) (quart_nonneg x)

/-! ## `⟨x, N(x)⟩` is real and equals `2 Q` -/

theorem inner_nonlin_real (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    (∑' n, conj (x n) * nonlin x n).im = 0 ∧ (∑' n, conj (x n) * nonlin x n).re = 2 * quart x := by
  obtain ⟨hL1, _⟩ := isL1_of_hn_one x hx
  have hs2 := summable_sq_of_h1 hx
  have hw : Summable fun n => ‖conv x x n‖ ^ 2 := summable_quart_of_h1 hx
  -- adjointness with f = x*x, g = y = x
  have hadj := inner_conv_cstar (f := conv x x) (g := x) (y := x) hw hL1 hs2
  have hq : ∑' n, conj (conv x x n) * conv x x n = ((quart x : ℝ) : ℂ) := by
    unfold quart
    push_cast
    refine tsum_congr fun n => ?_
    rw [Complex.conj_mul']
  rw [hq] at hadj
  have hN : ∑' n, conj (x n) * nonlin x n = 2 * ((quart x : ℝ) : ℂ) := by
    have e : ∀ n, conj (x n) * nonlin x n =
        2 * conj (conj (conv (conv x x) (cstar x) n) * x n) := fun n => by
      simp only [nonlin, map_mul, Complex.conj_conj]; ring
    simp only [e]
    rw [tsum_mul_left, ← Complex.conj_tsum, hadj]
    simp
  rw [hN]
  simp

end H1

/-! ## Regression probes (plane waves, kept as theorems) -/

section Probes

theorem single_mem_h1 (k : ℤ) (a : ℂ) : (Pi.single k a : ℤ → ℂ) ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
  finiteSupport_mem_seqSobolev38 _ _ ((Set.finite_singleton k).subset fun n hn => by
    by_contra h
    exact hn (by simp [(by simpa using h : n ≠ k)]))

theorem mass_single (k : ℤ) (a : ℂ) : mass (Pi.single k a) = ‖a‖ ^ 2 := by
  unfold mass
  rw [tsum_eq_single k (fun n hn => by simp [hn])]
  simp

theorem kin_single (k : ℤ) (a : ℂ) : kin (Pi.single k a) = disp k * ‖a‖ ^ 2 := by
  unfold kin
  rw [tsum_eq_single k (fun n hn => by simp [hn])]
  simp

theorem quart_single (k : ℤ) (a : ℂ) : quart (Pi.single k a) = ‖a‖ ^ 4 := by
  unfold quart
  rw [conv_single_single, tsum_eq_single (k + k) (fun n hn => by simp [hn])]
  simp; ring

/-- Plane wave: `Σ x̄_n N(x)_n = 2 ‖a‖⁴ = 2 Q(x)` (consistent with `inner_nonlin_real`). -/
theorem inner_nonlin_single (k : ℤ) (a : ℂ) :
    ∑' n, conj ((Pi.single k a : ℤ → ℂ) n) * nonlin (Pi.single k a) n =
      ((2 * ‖a‖ ^ 4 : ℝ) : ℂ) := by
  rw [tsum_eq_single k (fun n hn => by simp [hn]), nonlin_single]
  simp only [Pi.single_eq_same]
  have : conj a * (2 * ((‖a‖ ^ 2 : ℝ) : ℂ) * a) = ((2 * ‖a‖ ^ 4 : ℝ) : ℂ) := by
    have h := Complex.conj_mul' a
    calc conj a * (2 * ((‖a‖ ^ 2 : ℝ) : ℂ) * a) = 2 * ((‖a‖ ^ 2 : ℝ) : ℂ) * (conj a * a) := by ring
      _ = _ := by rw [h]; push_cast; ring
  exact this

theorem inner_nonlin_single_re (k : ℤ) (a : ℂ) :
    (∑' n, conj ((Pi.single k a : ℤ → ℂ) n) * nonlin (Pi.single k a) n).re =
      2 * quart (Pi.single k a) := by
  rw [inner_nonlin_single, quart_single, Complex.ofReal_re]

theorem hn_one_sq_single (k : ℤ) (a : ℂ) :
    hn 1 (Pi.single k a) ^ 2 = (1 + (k : ℝ) ^ 2) * ‖a‖ ^ 2 := by
  rw [hn_one_sq (single_mem_h1 k a), mass_single, kin_single, disp_eq]
  have : (4 * Real.pi ^ 2) ≠ 0 := by positivity
  field_simp

end Probes

end NlsGge.NLS38

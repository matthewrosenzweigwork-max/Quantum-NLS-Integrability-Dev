import NlsGge.Hierarchy.ALLaurentFourier38
import NlsGge.Hierarchy.ALC12Exact38
import NlsGge.Hierarchy.ALPositiveDecompositions38
import NlsGge.Hierarchy.ALTransferDefs38

/-! L01 (Batch 38): `D:prop:ALmoments` (paper/v2.tex l.1904-1929), positive discrete moments
`K_j = C(2j,j) M_d + 2 Σ_{k=1}^j (-1)^k C(2j,j-k) Re C_k` (`D:eq:Kj`) and
`K_j = (L/π) ∫_0^{2π} (2 - 2cos 2θ)^j κ(θ) dθ ≥ 0` (`D:eq:Kjpositive`). -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open Finset MeasureTheory

/-- Real summand of the cosine binomial expansion. -/
def cosBinTerm38 (j : ℕ) (θ : ℝ) (m : ℕ) : ℝ :=
  (-1 : ℝ) ^ (m + j) * (Nat.choose (2 * j) m : ℝ) * Real.cos (2 * ((m : ℝ) - j) * θ)

theorem cosBinTerm38_symm (j : ℕ) (θ : ℝ) {m : ℕ} (hm : m ≤ 2 * j) :
    cosBinTerm38 j θ (2 * j - m) = cosBinTerm38 j θ m := by
  unfold cosBinTerm38
  rw [Nat.choose_symm hm]
  have h1 : (-1 : ℝ) ^ (2 * j - m + j) = (-1 : ℝ) ^ (m + j) := by
    have : 2 * j - m + j + (m + j) = 4 * j := by omega
    have h2 : (-1 : ℝ) ^ (2 * j - m + j) * (-1 : ℝ) ^ (m + j) = 1 := by
      rw [← pow_add, this, pow_mul]; norm_num
    have h3 : ((-1 : ℝ) ^ (m + j)) * (-1 : ℝ) ^ (m + j) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    have h4 : (-1 : ℝ) ^ (m + j) ≠ 0 := by positivity
    exact mul_right_cancel₀ h4 (h2.trans h3.symm)
  rw [h1]
  congr 1
  have : (((2 * j - m : ℕ) : ℝ) - j) = -((m : ℝ) - j) := by
    rw [Nat.cast_sub hm]; push_cast; ring
  rw [this, show 2 * -((m : ℝ) - j) * θ = -(2 * ((m : ℝ) - j) * θ) by ring, Real.cos_neg]

theorem cos_binomial_full38 (j : ℕ) (θ : ℝ) :
    (2 - 2 * Real.cos (2 * θ)) ^ j = ∑ m ∈ range (2 * j + 1), cosBinTerm38 j θ m := by
  set e : ℂ := Complex.exp (θ * Complex.I) with he
  have hne : e ≠ 0 := Complex.exp_ne_zero _
  have hc : ((2 - 2 * Real.cos (2 * θ) : ℝ) : ℂ) = -((e + -e⁻¹) ^ 2) := by
    have h : (Real.cos (2 * θ) : ℂ) = (Complex.exp ((2*θ : ℝ) * Complex.I) +
        Complex.exp (-((2*θ : ℝ) * Complex.I)))/2 := by
      rw [Complex.ofReal_cos, Complex.cos]; congr 3; ring
    have h1 : e ^ 2 = Complex.exp ((2*θ : ℝ) * Complex.I) := by
      rw [he, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have h3 : (e⁻¹) ^ 2 = Complex.exp (-((2*θ : ℝ) * Complex.I)) := by
      rw [he, ← Complex.exp_neg, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have h4 : e * e⁻¹ = 1 := mul_inv_cancel₀ hne
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [h, ← h1, ← h3]
    linear_combination (-2) * h4
  have hmain : (((2 - 2 * Real.cos (2 * θ) : ℝ) ^ j : ℝ) : ℂ) =
      ∑ m ∈ range (2 * j + 1), (((-1 : ℂ) ^ j * ((Nat.choose (2 * j) m : ℂ) *
        (e ^ m * (-e⁻¹) ^ (2 * j - m))))) := by
    have A : (((2 - 2 * Real.cos (2 * θ) : ℝ) : ℂ)) ^ j = (-1 : ℂ) ^ j * (e + -e⁻¹) ^ (2 * j) := by
      rw [hc, neg_eq_neg_one_mul, mul_pow, ← pow_mul]
    rw [Complex.ofReal_pow, A, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    ring
  have hre := congrArg Complex.re hmain
  rw [Complex.ofReal_re, Complex.re_sum] at hre
  rw [hre]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ 2 * j := by simpa [Nat.lt_succ_iff] using hm
  have hterm : ((-1 : ℂ) ^ j * ((Nat.choose (2 * j) m : ℂ) * (e ^ m * (-e⁻¹) ^ (2 * j - m)))) =
      (((-1 : ℝ) ^ (m + j) * (Nat.choose (2 * j) m : ℝ) : ℝ) : ℂ) *
        Complex.exp (((2 * ((m : ℝ) - j) * θ : ℝ) : ℂ) * Complex.I) := by
    have hs : (-1 : ℂ) ^ (2 * j - m) = (-1 : ℂ) ^ m := by
      have h2 : (-1 : ℂ) ^ (2 * j - m) * (-1 : ℂ) ^ m = 1 := by
        rw [← pow_add, Nat.sub_add_cancel hm', pow_mul]; norm_num
      have h3 : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      exact mul_right_cancel₀ (pow_ne_zero m (by norm_num)) (h2.trans h3.symm)
    have hx : e ^ m * (e⁻¹) ^ (2 * j - m) = Complex.exp (((2 * ((m : ℝ) - j) * θ : ℝ) : ℂ) *
        Complex.I) := by
      rw [he, ← Complex.exp_nat_mul, ← Complex.exp_neg, ← Complex.exp_nat_mul,
        ← Complex.exp_add]
      congr 1
      rw [Nat.cast_sub hm']; push_cast; ring
    have hneg : (-e⁻¹) ^ (2 * j - m) = (-1 : ℂ) ^ (2 * j - m) * (e⁻¹) ^ (2 * j - m) := by
      rw [neg_eq_neg_one_mul, mul_pow]
    rw [hneg, hs]
    have hx' : e ^ m * ((-1 : ℂ) ^ m * (e⁻¹) ^ (2 * j - m)) =
        (-1 : ℂ) ^ m * Complex.exp (((2 * ((m : ℝ) - j) * θ : ℝ) : ℂ) * Complex.I) := by
      rw [← hx]; ring
    rw [hx']
    push_cast
    rw [pow_add]
    ring
  rw [hterm, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  unfold cosBinTerm38
  ring

theorem sum_range_symm_fold38 (j : ℕ) (f : ℕ → ℝ) (hf : ∀ m ≤ 2 * j, f (2 * j - m) = f m) :
    ∑ m ∈ range (2 * j + 1), f m = f j + 2 * ∑ k ∈ Icc 1 j, f (j + k) := by
  have e1 : 2 * j + 1 = (j + 1) + j := by omega
  rw [e1, Finset.sum_range_add, Finset.sum_range_succ]
  have e2 : ∑ m ∈ range j, f m = ∑ x ∈ range j, f (j + 1 + x) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.mp hx
    have : j - 1 - x = 2 * j - (j + 1 + x) := by omega
    rw [this, hf _ (by omega)]
  have e3 : ∑ k ∈ Icc 1 j, f (j + k) = ∑ x ∈ range j, f (j + 1 + x) := by
    have : Icc 1 j = Ico 1 (j + 1) := by ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [this, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun x _ => by rw [← add_assoc]
  rw [e3, e2]; ring

/-- `(2 - 2cos 2θ)^j = C(2j,j) + 2 Σ_{k=1}^j (-1)^k C(2j,j-k) cos 2kθ`. -/
theorem cos_binomial38 (j : ℕ) (θ : ℝ) :
    (2 - 2 * Real.cos (2 * θ)) ^ j = (Nat.choose (2 * j) j : ℝ) +
      2 * ∑ k ∈ Icc 1 j, (-1 : ℝ) ^ k * (Nat.choose (2 * j) (j - k) : ℝ) *
        Real.cos (2 * k * θ) := by
  rw [cos_binomial_full38, sum_range_symm_fold38 j _ (fun m hm => cosBinTerm38_symm j θ hm)]
  congr 1
  · unfold cosBinTerm38; simp
  · congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_Icc.mp hk
    unfold cosBinTerm38
    have h1 : (-1 : ℝ) ^ (j + k + j) = (-1 : ℝ) ^ k := by
      rw [show j + k + j = k + 2 * j by ring, pow_add, pow_mul]; norm_num
    have h2 : Nat.choose (2 * j) (j + k) = Nat.choose (2 * j) (j - k) := by
      rw [← Nat.choose_symm (show j + k ≤ 2 * j by omega)]; congr 1; omega
    rw [h1, h2]
    congr 2
    push_cast; ring_nf

/-- `K_j` (`D:eq:Kj`). -/
def alK38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (j : ℕ) : ℝ :=
  (Nat.choose (2 * j) j : ℝ) * alMass38 L α +
    2 * ∑ k ∈ Icc 1 j, (-1 : ℝ) ^ k * (Nat.choose (2 * j) (j - k) : ℝ) * (alC38 α k).re

/-- `D:eq:Kjpositive` (equality part): `K_j = (L/π) ∫_0^{2π} (2 - 2cos 2θ)^j κ(θ) dθ`. -/
theorem alK38_spectral {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) (j : ℕ) :
    alK38 α j = (L / Real.pi) *
      ∫ θ in (0:ℝ)..(2 * Real.pi), (2 - 2 * Real.cos (2 * θ)) ^ j * alKappa38 α θ := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hκ := continuous_alKappa38 hα
  set c : ℕ → ℝ := fun k => (-1 : ℝ) ^ k * (Nat.choose (2 * j) (j - k) : ℝ) with hc
  have hpt : ∀ θ : ℝ, (2 - 2 * Real.cos (2 * θ)) ^ j * alKappa38 α θ =
      (Nat.choose (2 * j) j : ℝ) * alKappa38 α θ +
        2 * ∑ k ∈ Icc 1 j, c k * (alKappa38 α θ * Real.cos (2 * k * θ)) := by
    intro θ
    have h2 : (2 * ∑ k ∈ Icc 1 j, (-1 : ℝ) ^ k * (Nat.choose (2 * j) (j - k) : ℝ) *
        Real.cos (2 * k * θ)) * alKappa38 α θ =
        2 * ∑ k ∈ Icc 1 j, c k * (alKappa38 α θ * Real.cos (2 * k * θ)) := by
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hc]; ring
    rw [cos_binomial38 j θ, add_mul, h2]
  have hint : ∀ k : ℕ, IntervalIntegrable (fun θ : ℝ => alKappa38 α θ * Real.cos (2 * k * θ))
      volume 0 (2 * Real.pi) := fun k =>
    (hκ.mul (by fun_prop)).intervalIntegrable _ _
  simp_rw [hpt]
  have hi1 : IntervalIntegrable (fun θ : ℝ => (Nat.choose (2 * j) j : ℝ) * alKappa38 α θ)
      volume 0 (2 * Real.pi) := (continuous_const.mul hκ).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1
      (by
        refine IntervalIntegrable.const_mul ?_ _
        exact (continuous_finsetSum _ fun k _ =>
          continuous_const.mul (hκ.mul (by fun_prop))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun k _ => (hint k).const_mul _), integral_alKappa38 hα]
  unfold alK38
  simp_rw [intervalIntegral.integral_const_mul]
  have this : ∀ k ∈ Icc 1 j, ∫ θ in (0:ℝ)..(2 * Real.pi), alKappa38 α θ * Real.cos (2 * k * θ) =
      Real.pi * (alC38 α k).re / L := fun k hk =>
    integral_alKappa38_cos hα (Finset.mem_Icc.mp hk).1
  have hs : ∑ i ∈ Icc 1 j, c i * ∫ θ in (0:ℝ)..(2 * Real.pi),
        alKappa38 α θ * Real.cos (2 * i * θ) =
      ∑ i ∈ Icc 1 j, c i * (Real.pi * (alC38 α i).re / L) :=
    Finset.sum_congr rfl fun k hk => by rw [this k hk]
  rw [hs, mul_add]
  congr 1
  · field_simp
  · rw [mul_left_comm, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hc]; field_simp

/-- `D:eq:Kjpositive` (positivity part): `K_j ≥ 0`. -/
theorem alK38_nonneg {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) (j : ℕ) :
    0 ≤ alK38 α j := by
  rw [alK38_spectral hα j]
  refine mul_nonneg (div_nonneg (Nat.cast_nonneg _) Real.pi_pos.le) ?_
  refine intervalIntegral.integral_nonneg (by positivity) fun θ _ => ?_
  have : 0 ≤ 2 - 2 * Real.cos (2 * θ) := by linarith [Real.cos_le_one (2 * θ)]
  exact mul_nonneg (pow_nonneg this j) (alKappa38_nonneg α θ)

theorem alK38_zero {L : ℕ} [NeZero L] (α : ZMod L → ℂ) : alK38 α 0 = alMass38 L α := by
  simp [alK38]

theorem alK38_one {L : ℕ} [NeZero L] (α : ZMod L → ℂ) :
    alK38 α 1 = 2 * alMass38 L α - 2 * (alC38 α 1).re := by
  simp [alK38, Nat.choose]
  ring

theorem alK38_two {L : ℕ} [NeZero L] (α : ZMod L → ℂ) :
    alK38 α 2 = 6 * alMass38 L α - 8 * (alC38 α 1).re + 2 * (alC38 α 2).re := by
  simp [alK38, Finset.sum_Icc_succ_top, Nat.choose]
  ring

/-- Agreement with `H_d` of `ALPositiveDecompositions38` (`L ≥ 3`). -/
theorem alK38_one_eq_alHd {L : ℕ} [NeZero L] (hL : 3 ≤ L) {α : ZMod L → ℂ}
    (hα : IsALField38 α) : alK38 α 1 = NlsGge.HierarchyRiccati.Core.alHd α := by
  rw [alK38_one, alC38_one38 hL hα]
  rfl

/-- Agreement with `K_d` of `ALPositiveDecompositions38` (`L ≥ 3`). -/
theorem alK38_two_eq_alKd {L : ℕ} [NeZero L] (hL : 3 ≤ L) {α : ZMod L → ℂ}
    (hα : IsALField38 α) : alK38 α 2 = NlsGge.HierarchyRiccati.Core.alKd α := by
  rw [alK38_two, alC38_one38 hL hα, alC38_two38 hL hα]
  rfl

/-- `M_d` of `ALPositiveDecompositions38` is `alMass38`. -/
theorem alMd_eq_alMass38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) :
    NlsGge.HierarchyRiccati.Core.alMd α = alMass38 L α := rfl

/-- Conservation of every `K_j`, conditional form: if the mass and all exterior Laurent
coefficients `C_k` agree at two configurations (e.g. two times of an AL orbit, by
isospectrality, E07-6b), then so does every `K_j`. -/
theorem alK38_eq_of_conserved {L : ℕ} [NeZero L] {α β : ZMod L → ℂ}
    (hM : alMass38 L α = alMass38 L β) (hC : ∀ k : ℕ, 1 ≤ k → alC38 α k = alC38 β k) (j : ℕ) :
    alK38 α j = alK38 β j := by
  unfold alK38
  rw [hM]
  congr 2
  exact Finset.sum_congr rfl fun k hk => by rw [hC k (Finset.mem_Icc.mp hk).1]

/-- Conservation along a flow, conditional on conservation of `alMass38` and `alC38`
(to be discharged from E07-6b). -/
theorem alK38_const_along38 {L : ℕ} [NeZero L] {ι : Type*} (γ : ι → ZMod L → ℂ)
    (hM : ∀ s t, alMass38 L (γ s) = alMass38 L (γ t))
    (hC : ∀ s t, ∀ k : ℕ, 1 ≤ k → alC38 (γ s) k = alC38 (γ t) k) (j : ℕ) (s t : ι) :
    alK38 (γ s) j = alK38 (γ t) j :=
  alK38_eq_of_conserved (hM s t) (hC s t) j

end NlsGge.AblowitzLadik
end

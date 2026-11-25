import NlsGge.Hierarchy.ALGaussianNormalizer38
import NlsGge.Hierarchy.ALPositiveDecompositions38
import NlsGge.Weights.Regularity

/-! L12: the exact lattice tilt `D:eq:ALtilt` (paper/v2.tex l.2376-2392).

`b(r) = 1 + r⁴`, `W̃ = W - δ b`.  In terms of the numerators `c_j` (`β_j = c_j/(j!)^4`):
`β̃_j = β_j - δ[j=0] - δ[j=2]`, i.e. `c̃_0 = c_0 - δ`, `c̃_2 = c_2 - 16 δ`, `c̃_j = c_j` otherwise.
For `0 < δ ≤ lo/64` the tilted numerators lie in `[3 lo/4, up]`, so `W̃` belongs to the class
`AdmittedCoefficients (3*lo/4) up`. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open Finset MeasureTheory Filter Topology

section Tilt

variable {lo up : ℝ} {c : ℕ → ℝ}

/-- Numerators of `W̃ = W - δ(1 + r⁴)`. -/
def alTiltCoeff38 (c : ℕ → ℝ) (δ : ℝ) (j : ℕ) : ℝ :=
  c j - (if j = 0 then δ else 0) - (if j = 2 then 16 * δ else 0)

theorem coefficient_tilt38 (c : ℕ → ℝ) (δ : ℝ) (j : ℕ) :
    NlsGge.coefficient (alTiltCoeff38 c δ) j =
      NlsGge.coefficient c j - (if j = 0 then δ else 0) - (if j = 2 then δ else 0) := by
  unfold NlsGge.coefficient alTiltCoeff38
  by_cases h0 : j = 0
  · subst h0; simp
  · by_cases h2 : j = 2
    · subst h2; simp [Nat.factorial]; ring
    · simp [h0, h2]

/-- The tilted numerators stay in the admitted class `[3 lo/4, up]` for `0 < δ ≤ lo/64`. -/
theorem alTiltCoeff_admitted38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ lo / 64) :
    NlsGge.Pilot.AdmittedCoefficients (3 * lo / 4) up (alTiltCoeff38 c δ) := by
  obtain ⟨hlo, hlu, hb⟩ := hc
  refine ⟨by positivity, by linarith, fun j => ?_⟩
  have := hb j
  unfold alTiltCoeff38
  by_cases h0 : j = 0
  · subst h0; simp; constructor <;> nlinarith [this.1, this.2]
  · by_cases h2 : j = 2
    · subst h2; simp; constructor <;> nlinarith [this.1, this.2]
    · simp [h0, h2]; constructor <;> nlinarith [this.1, this.2]

theorem hasSum_weight_tilt38 (c : ℕ → ℝ) (δ r : ℝ)
    (hs : Summable (NlsGge.weightTerm c r)) :
    HasSum (NlsGge.weightTerm (alTiltCoeff38 c δ) r)
      (NlsGge.Weights.weight c r - δ * (1 + r ^ 4)) := by
  have h0 : HasSum (fun j : ℕ => if j = 0 then δ else 0) δ := by
    simpa using hasSum_ite_eq (0 : ℕ) δ
  have h2 : HasSum (fun j : ℕ => if j = 2 then δ * r ^ 4 else 0) (δ * r ^ 4) := by
    simpa using hasSum_ite_eq (2 : ℕ) (δ * r ^ 4)
  have h := (hs.hasSum.sub h0).sub h2
  have e : NlsGge.weightTerm (alTiltCoeff38 c δ) r = fun j =>
      NlsGge.weightTerm c r j - (if j = 0 then δ else 0) - (if j = 2 then δ * r ^ 4 else 0) := by
    funext j
    unfold NlsGge.weightTerm
    rw [coefficient_tilt38]
    by_cases h0 : j = 0
    · subst h0; simp
    · by_cases h2 : j = 2
      · subst h2; simp; ring
      · simp [h0, h2]
  rw [e]
  convert h using 1
  unfold NlsGge.Weights.weight
  ring

/-- `W̃(r) = W(r) - δ(1 + r⁴)`. -/
theorem weight_tilt38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) (δ r : ℝ) :
    NlsGge.Weights.weight (alTiltCoeff38 c δ) r =
      NlsGge.Weights.weight c r - δ * (1 + r ^ 4) :=
  (hasSum_weight_tilt38 c δ r (NlsGge.Weights.weightTerm_summable lo up c hc.1
    (fun i => (hc.2.2 i).1) (fun i => (hc.2.2 i).2) r)).tsum_eq

/-- Rates of `W̃`: `ã_{h,ν} = a_{h,ν} - δ(1 + ω_{h,ν}⁴)`. -/
theorem alRate_tilt38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) (δ h : ℝ) (ν : ℤ) :
    alRate38 (alTiltCoeff38 c δ) h ν = alRate38 c h ν - δ * (1 + alOmega38 h ν ^ 4) := by
  unfold alRate38
  rw [weight_tilt38 hc]; ring

end Tilt

section Energy

variable {L : ℕ} [NeZero L] {lo up : ℝ} {c : ℕ → ℝ}

/-- `G_h = Q_{0,h} + Q_{4,h}`. -/
def alTiltG38 (h : ℝ) (α : ZMod L → ℂ) : ℝ := alQ38 h α 0 + alQ38 h α 2

/-- `E_{W̃,h} = E_{W,h} - δ G_h` on admissible fields. -/
theorem alEnergy_tilt38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ lo / 64) {α : ZMod L → ℂ} (hα : IsALField38 α) {h : ℝ}
    (hh : 0 < h) :
    alEnergy38 (alTiltCoeff38 c δ) h α = alEnergy38 c h α - δ * alTiltG38 h α := by
  have hc' := alTiltCoeff_admitted38 hc hδ0 hδ
  have hs := alEnergy38_summable hc hα hh
  have h0 : HasSum (fun j : ℕ => if j = 0 then δ * alQ38 h α 0 else 0) (δ * alQ38 h α 0) := by
    simpa using hasSum_ite_eq (0 : ℕ) (δ * alQ38 h α 0)
  have h2 : HasSum (fun j : ℕ => if j = 2 then δ * alQ38 h α 2 else 0) (δ * alQ38 h α 2) := by
    simpa using hasSum_ite_eq (2 : ℕ) (δ * alQ38 h α 2)
  have hsum := (hs.hasSum.sub h0).sub h2
  have e : alEnergyTerm38 (alTiltCoeff38 c δ) h α = fun j =>
      alEnergyTerm38 c h α j - (if j = 0 then δ * alQ38 h α 0 else 0)
        - (if j = 2 then δ * alQ38 h α 2 else 0) := by
    funext j
    unfold alEnergyTerm38
    rw [coefficient_tilt38]
    by_cases h0 : j = 0
    · subst h0; simp; ring
    · by_cases h2 : j = 2
      · subst h2; simp; ring
      · simp [h0, h2]
  unfold alEnergy38 alTiltG38
  rw [e, hsum.tsum_eq]
  ring

end Energy

section Partition

open Classical in
/-- `∫ e^{δ G_h} dη_h^W` with `dη_h^W = 𝒵_h(W)⁻¹ e^{-E_{W,h}} ∏_j (1-|α_j|²)⁻¹ d²α`
(`D:eq:ALfullmeasure`) on the open polydisk `𝔻^L`: the integral against the probability
measure given by this Lebesgue density. -/
def alTiltIntegral38 (L : ℕ) [NeZero L] (c : ℕ → ℝ) (h δ : ℝ) : ℝ :=
  (alPartition38 L c h)⁻¹ * ∫ α : ZMod L → ℂ, if IsALField38 α then
    Real.exp (δ * alTiltG38 h α) *
      (Real.exp (-alEnergy38 c h α) * ∏ j, (1 - ‖α j‖ ^ 2)⁻¹) else 0

/-- `D_{δ,h} = ∏_{|k|≤N} (1 - δ (1+ω_{h,k}⁴)/(W(ω_{h,k}) - h))`. -/
def alTiltD38 (c : ℕ → ℝ) (h δ : ℝ) (N : ℕ) : ℝ :=
  ∏ ν ∈ Finset.Icc (-(N : ℤ)) N,
    (1 - δ * (1 + alOmega38 h ν ^ 4) / (NlsGge.Weights.weight c (alOmega38 h ν) - h))

variable {lo up : ℝ} {c : ℕ → ℝ}

/-- Canonical partition function of `W̃` as the tilted Lebesgue integral. -/
theorem alTiltIntegral_eq_partition38 (L : ℕ) [NeZero L]
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {δ h : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ lo / 64) (hh : 0 < h) :
    alTiltIntegral38 L c h δ =
      (alPartition38 L c h)⁻¹ * alPartition38 L (alTiltCoeff38 c δ) h := by
  unfold alTiltIntegral38 alPartition38
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun α => ?_)
  by_cases hα : IsALField38 α
  · simp only [hα, ite_true]
    rw [alEnergy_tilt38 hc hδ0 hδ hα hh, ← mul_assoc, ← Real.exp_add]
    congr 2; ring
  · simp [hα]

/-- `D_{δ,h} = ∏ ã/a` (all `a_{h,k} > 0`). -/
theorem alTiltD_eq_prod38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) (δ h : ℝ) (N : ℕ)
    (ha : ∀ ν : ℤ, 0 < alRate38 c h ν) :
    alTiltD38 c h δ N =
      ∏ ν ∈ Finset.Icc (-(N : ℤ)) N, (alRate38 (alTiltCoeff38 c δ) h ν / alRate38 c h ν) := by
  unfold alTiltD38
  refine Finset.prod_congr rfl fun ν _ => ?_
  rw [alRate_tilt38 hc]
  have := (ha ν).ne'
  unfold alRate38 at this ⊢
  field_simp

/-- **`D:eq:ALtilt`.**  For `L = 2N+1`, `h = 1/L`, `0 ≤ δ ≤ lo/64`, and `(3lo/4)⁻¹ < L`:
`∫ e^{δG_h} dη_h^W = D_{δ,h}⁻¹ Z_h(W̃)/Z_h(W)` with the Gaussian-reweighted
`Z_h = ∫ f_h dγ_h`. -/
theorem alTilt_identity38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) (N : ℕ) {h δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ lo / 64) (hh : h = ((2 * N + 1 : ℕ) : ℝ)⁻¹)
    (hN : (3 * lo / 4)⁻¹ < ((2 * N + 1 : ℕ) : ℝ)) :
    alTiltIntegral38 (2 * N + 1) c h δ =
      (alTiltD38 c h δ N)⁻¹ *
        (alZ38 (L := 2 * N + 1) (alTiltCoeff38 c δ) h / alZ38 (L := 2 * N + 1) c h) := by
  have hc' := alTiltCoeff_admitted38 hc hδ0 hδ
  have hLpos : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  have hh0 : 0 < h := by rw [hh]; positivity
  have hlo' : lo⁻¹ < ((2 * N + 1 : ℕ) : ℝ) := by
    refine lt_of_le_of_lt ?_ hN
    have := hc.1
    exact inv_anti₀ (by positivity) (by linarith)
  have ha := alRate38_pos_of_mesh38 hc hh hlo'
  have ha' := alRate38_pos_of_mesh38 hc' hh hN
  rw [alTiltIntegral_eq_partition38 _ hc hδ0 hδ hh0, alTiltD_eq_prod38 hc δ h N ha,
    alGaussianNormalizer_Icc38 hc N hh hlo', alGaussianNormalizer_Icc38 hc' N hh hN,
    Finset.prod_div_distrib (s := Finset.Icc (-(N : ℤ)) N)
      (f := fun ν => alRate38 (alTiltCoeff38 c δ) h ν) (g := fun ν => alRate38 c h ν)]
  have hK : h ^ (2 * N + 1) ≠ 0 := by positivity
  have hP : ∏ ν ∈ Finset.Icc (-(N : ℤ)) N, Real.pi / alRate38 c h ν ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun ν _ => div_ne_zero Real.pi_ne_zero (ha ν).ne'
  have hP' : ∏ ν ∈ Finset.Icc (-(N : ℤ)) N, Real.pi / alRate38 (alTiltCoeff38 c δ) h ν ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun ν _ => div_ne_zero Real.pi_ne_zero (ha' ν).ne'
  have hr : ∏ ν ∈ Finset.Icc (-(N : ℤ)) N, Real.pi / alRate38 (alTiltCoeff38 c δ) h ν =
      (∏ ν ∈ Finset.Icc (-(N : ℤ)) N, Real.pi / alRate38 c h ν) *
        (∏ ν ∈ Finset.Icc (-(N : ℤ)) N, alRate38 c h ν) /
          (∏ ν ∈ Finset.Icc (-(N : ℤ)) N, alRate38 (alTiltCoeff38 c δ) h ν) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun ν _ => ?_
    have := (ha ν).ne'; have := (ha' ν).ne'
    field_simp
  rw [hr]
  have hA : ∏ ν ∈ Finset.Icc (-(N : ℤ)) N, alRate38 c h ν ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun ν _ => (ha ν).ne'
  have hA' : ∏ ν ∈ Finset.Icc (-(N : ℤ)) N, alRate38 (alTiltCoeff38 c δ) h ν ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun ν _ => (ha' ν).ne'
  generalize ∏ ν ∈ Finset.Icc (-(N : ℤ)) N, Real.pi / alRate38 c h ν = P at hP ⊢
  generalize ∏ ν ∈ Finset.Icc (-(N : ℤ)) N, alRate38 c h ν = A at hA ⊢
  generalize ∏ ν ∈ Finset.Icc (-(N : ℤ)) N, alRate38 (alTiltCoeff38 c δ) h ν = A' at hA' ⊢
  generalize h ^ (2 * N + 1) = K at hK ⊢
  field_simp

end Partition

/-! ### Positivity of the factors and the summable deficit bound -/

section Factors

variable {lo up : ℝ} {c : ℕ → ℝ}

/-- The `k`-th factor of `D_{δ,h}`: `1 - δ(1+ω⁴)/(W(ω) - h)`. -/
def alTiltFactor38 (c : ℕ → ℝ) (δ ω h : ℝ) : ℝ :=
  1 - δ * (1 + ω ^ 4) / (NlsGge.Weights.weight c ω - h)

theorem weight_ge_two38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) (ω : ℝ) :
    lo + lo / 16 * ω ^ 4 ≤ NlsGge.Weights.weight c ω := by
  have hs := NlsGge.Weights.weightTerm_summable lo up c hc.1
    (fun i => (hc.2.2 i).1) (fun i => (hc.2.2 i).2) ω
  have hn := NlsGge.Weights.weightTerm_nonneg lo c hc.1 (fun i => (hc.2.2 i).1) ω
  have this := hs.sum_le_tsum {0, 2} (fun j _ => hn j)
  have h02 : ∑ j ∈ ({0, 2} : Finset ℕ), NlsGge.weightTerm c ω j = c 0 + c 2 / 16 * ω ^ 4 := by
    simp [NlsGge.weightTerm, NlsGge.coefficient, Nat.factorial]
    norm_num
  rw [h02] at this
  have h0 := (hc.2.2 0).1
  have h2 := (hc.2.2 2).1
  have hω : 0 ≤ ω ^ 4 := by positivity
  show _ ≤ ∑' j, _
  nlinarith

theorem weight_ge_six38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) (ω : ℝ) :
    lo / 1296 * ω ^ 6 ≤ NlsGge.Weights.weight c ω := by
  have hs := NlsGge.Weights.weightTerm_summable lo up c hc.1
    (fun i => (hc.2.2 i).1) (fun i => (hc.2.2 i).2) ω
  have hn := NlsGge.Weights.weightTerm_nonneg lo c hc.1 (fun i => (hc.2.2 i).1) ω
  have := hs.le_tsum 3 (fun j _ => hn j)
  unfold NlsGge.Weights.weight
  have h3 := (hc.2.2 3).1
  simp [NlsGge.weightTerm, NlsGge.coefficient, Nat.factorial] at this
  have hω : 0 ≤ ω ^ 6 := by positivity
  refine le_trans ?_ this
  have : lo / 1296 * ω ^ 6 ≤ c 3 / 1296 * ω ^ 6 := by
    apply mul_le_mul_of_nonneg_right _ hω; linarith
  convert this using 2
  all_goals norm_num

/-- Uniformly, the deficit `δ(1+ω⁴)/(W(ω)-h)` is at most `1/4`. -/
theorem deficit_le_quarter38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {δ h : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ lo / 64) (hh : h ≤ lo / 2) (ω : ℝ) :
    0 ≤ δ * (1 + ω ^ 4) / (NlsGge.Weights.weight c ω - h) ∧
      δ * (1 + ω ^ 4) / (NlsGge.Weights.weight c ω - h) ≤ 1 / 4 := by
  have hlo := hc.1
  have hW := weight_ge_two38 hc ω
  have hω : 0 ≤ ω ^ 4 := by positivity
  have hpos : 0 < NlsGge.Weights.weight c ω - h := by nlinarith
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hpos]
  nlinarith [mul_nonneg hδ0 hω]

/-- Summable majorant of the deficits for `|ω| ≥ 4|ν|`, `ν ≠ 0`. -/
theorem deficit_le_bound38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {δ h : ℝ}
    (hδ0 : 0 ≤ δ) (hh : h ≤ lo / 2) {ν : ℤ} (hν : ν ≠ 0) {ω : ℝ}
    (hω : 4 * |(ν : ℝ)| ≤ |ω|) :
    δ * (1 + ω ^ 4) / (NlsGge.Weights.weight c ω - h) ≤ (324 * δ / lo) * (1 / (ν : ℝ) ^ 2) := by
  have hlo := hc.1
  have hW6 := weight_ge_six38 hc ω
  have hWl := NlsGge.Weights.weight_lower lo up c hc.1 (fun i => (hc.2.2 i).1) (fun i => (hc.2.2 i).2) ω
  have hn : (1 : ℝ) ≤ (ν : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ ν ^ 2 := by nlinarith [sq_pos_of_ne_zero hν]
    exact_mod_cast this
  have ht : 16 * (ν : ℝ) ^ 2 ≤ ω ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hω 2
    rw [mul_pow, sq_abs, sq_abs] at this; nlinarith
  set t := ω ^ 2 with htdef
  set n := (ν : ℝ) ^ 2 with hndef
  have h6 : ω ^ 6 = t ^ 3 := by rw [htdef]; ring
  have h4 : ω ^ 4 = t ^ 2 := by rw [htdef]; ring
  rw [h6] at hW6
  rw [h4]
  have hWh : NlsGge.Weights.weight c ω - h ≥ lo / 2592 * t ^ 3 := by
    nlinarith [hW6, hWl]
  have hpos : 0 < NlsGge.Weights.weight c ω - h := by
    have : 0 < lo / 2592 * t ^ 3 := by
      have : 0 < t := by nlinarith
      positivity
    linarith
  rw [div_le_iff₀ hpos]
  have ht1 : 16 ≤ t := by nlinarith
  have e : 324 * δ / lo * (1 / n) * (NlsGge.Weights.weight c ω - h) ≥
      324 * δ / lo * (1 / n) * (lo / 2592 * t ^ 3) :=
    mul_le_mul_of_nonneg_left hWh (by positivity)
  refine le_trans ?_ e
  have e2 : 324 * δ / lo * (1 / n) * (lo / 2592 * t ^ 3) = δ * t ^ 3 / (8 * n) := by
    field_simp; ring
  rw [e2, le_div_iff₀ (by positivity)]
  have key : (1 + t ^ 2) * (8 * n) ≤ t ^ 3 := by
    have h1 : 1 ≤ t ^ 2 := by nlinarith
    have h2 : (1 + t ^ 2) * (8 * n) ≤ 2 * t ^ 2 * (8 * n) := by nlinarith
    have h3 : 2 * t ^ 2 * (8 * n) ≤ t ^ 3 := by nlinarith [sq_nonneg t]
    linarith
  calc δ * (1 + t ^ 2) * (8 * n) = δ * ((1 + t ^ 2) * (8 * n)) := by ring
    _ ≤ δ * t ^ 3 := mul_le_mul_of_nonneg_left key hδ0

end Factors

section Convergence

variable {lo up : ℝ} {c : ℕ → ℝ}

/-- All factors of `D_{δ,h}` lie in `[3/4, 1]` once `h ≤ lo/2` and `0 ≤ δ ≤ lo/64`. -/
theorem alTiltFactor_bounds38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {δ h : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ lo / 64) (hh : h ≤ lo / 2) (ω : ℝ) :
    3 / 4 ≤ alTiltFactor38 c δ ω h ∧ alTiltFactor38 c δ ω h ≤ 1 := by
  have := deficit_le_quarter38 hc hδ0 hδ hh ω
  unfold alTiltFactor38
  constructor <;> linarith [this.1, this.2]

theorem abs_log_factor_le38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {δ h : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ lo / 64) (hh : h ≤ lo / 2) (ω : ℝ) :
    |Real.log (alTiltFactor38 c δ ω h)| ≤ 2 * (δ * (1 + ω ^ 4) / (NlsGge.Weights.weight c ω - h)) := by
  have hb := alTiltFactor_bounds38 hc hδ0 hδ hh ω
  have hd := deficit_le_quarter38 hc hδ0 hδ hh ω
  set d := δ * (1 + ω ^ 4) / (NlsGge.Weights.weight c ω - h) with hd'
  have hf : alTiltFactor38 c δ ω h = 1 - d := rfl
  rw [hf] at hb ⊢
  have hpos : 0 < 1 - d := by linarith [hd.2]
  have h1 : Real.log (1 - d) ≤ 0 := Real.log_nonpos hpos.le (by linarith [hd.1])
  have h2 := Real.one_sub_inv_le_log_of_pos hpos
  rw [abs_of_nonpos h1]
  have h3 : (1 - d)⁻¹ ≤ 1 + 4 / 3 * d := by
    rw [inv_le_iff_one_le_mul₀ hpos]; nlinarith [hd.1, hd.2]
  linarith [hd.1]

/-- `|k|h ≤ 1/2` gives `|ω_{h,k}| ≥ 4|k|` (the sine bound `|sin πx| ≥ 2|x|`). -/
theorem alOmega_abs_ge38 {h : ℝ} (hh : 0 < h) {ν : ℤ} (hν : |(ν : ℝ)| * h ≤ 1 / 2) :
    4 * |(ν : ℝ)| ≤ |alOmega38 h ν| := by
  have hx0 : 0 ≤ Real.pi * |(ν : ℝ)| * h := by positivity
  have hx1 : Real.pi * |(ν : ℝ)| * h ≤ Real.pi / 2 := by
    have := Real.pi_pos
    nlinarith
  have hs := Real.mul_le_sin hx0 hx1
  have e : 2 / Real.pi * (Real.pi * |(ν : ℝ)| * h) = 2 * |(ν : ℝ)| * h := by
    field_simp
  rw [e] at hs
  have hs0 : 0 ≤ Real.sin (Real.pi * |(ν : ℝ)| * h) := le_trans (by positivity) hs
  have habs : |Real.sin (Real.pi * ν * h)| = Real.sin (Real.pi * |(ν : ℝ)| * h) := by
    rcases le_total 0 (ν : ℝ) with hv | hv
    · rw [abs_of_nonneg hv] at hs0 ⊢
      exact abs_of_nonneg hs0
    · rw [abs_of_nonpos hv] at hs0 ⊢
      have : Real.pi * (-(ν : ℝ)) * h = -(Real.pi * ν * h) := by ring
      rw [this, Real.sin_neg] at hs0 ⊢
      rw [abs_of_nonpos (by linarith)]
  unfold alOmega38
  rw [abs_div, abs_mul, abs_of_pos hh, abs_two, habs, le_div_iff₀ hh]
  nlinarith

/-- The mesh sequence `h_N = 1/(2N+1)`. -/
def alMesh38 (N : ℕ) : ℝ := (((2 * N + 1 : ℕ) : ℝ))⁻¹

theorem alMesh_pos38 (N : ℕ) : 0 < alMesh38 N := by unfold alMesh38; positivity

theorem tendsto_alMesh38 : Tendsto alMesh38 atTop (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun N => (alMesh_pos38 N).ne'⟩
  unfold alMesh38
  refine tendsto_inv_atTop_zero.comp ?_
  exact tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun N => by simp only [id]; omega) tendsto_id)

theorem tendsto_alOmega38 (ν : ℤ) :
    Tendsto (fun N : ℕ => alOmega38 (alMesh38 N) ν) atTop (𝓝 (2 * Real.pi * ν)) := by
  have hd : HasDerivAt (fun x : ℝ => 2 * Real.sin (Real.pi * ν * x))
      (2 * Real.pi * ν) 0 := by
    have h1 : HasDerivAt (fun x : ℝ => Real.pi * ν * x) (Real.pi * ν) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (Real.pi * ν)
    have := (h1.sin).const_mul 2
    convert this using 1
    simp; ring
  have := (hasDerivAt_iff_tendsto_slope_zero.1 hd).comp tendsto_alMesh38
  refine this.congr fun N => ?_
  simp [alOmega38, smul_eq_mul]
  ring

theorem tendsto_alFactor38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) (δ : ℝ) (ν : ℤ) :
    Tendsto (fun N : ℕ => alTiltFactor38 c δ (alOmega38 (alMesh38 N) ν) (alMesh38 N)) atTop
      (𝓝 (alTiltFactor38 c δ (2 * Real.pi * ν) 0)) := by
  have hW := (NlsGge.Weights.weight_hasDerivAt lo up c hc.1 (fun i => (hc.2.2 i).1)
    (fun i => (hc.2.2 i).2) (2 * Real.pi * ν)).continuousAt.tendsto.comp (tendsto_alOmega38 ν)
  have hh : Tendsto alMesh38 atTop (𝓝 0) := tendsto_alMesh38.mono_right nhdsWithin_le_nhds
  have hden := hW.sub hh
  have hne : NlsGge.Weights.weight c (2 * Real.pi * ν) - 0 ≠ 0 := by
    rw [sub_zero]
    exact (NlsGge.Weights.weight_pos lo up c hc.1 (fun i => (hc.2.2 i).1)
      (fun i => (hc.2.2 i).2) _).ne'
  have hnum : Tendsto (fun N : ℕ => δ * (1 + alOmega38 (alMesh38 N) ν ^ 4)) atTop
      (𝓝 (δ * (1 + (2 * Real.pi * ν) ^ 4))) :=
    ((tendsto_alOmega38 ν).pow 4).const_add 1 |>.const_mul δ
  exact (hnum.div hden hne).const_sub 1

/-- Summable majorant of the deficits. -/
def alTiltMajorant38 (lo δ : ℝ) (ν : ℤ) : ℝ :=
  (if ν = 0 then 1 / 4 else 0) + (324 * δ / lo) * (1 / (ν : ℝ) ^ 2)

theorem summable_alTiltMajorant38 (lo δ : ℝ) : Summable (alTiltMajorant38 lo δ) := by
  unfold alTiltMajorant38
  refine Summable.add ?_ ?_
  · exact (hasSum_ite_eq (0 : ℤ) ((1 : ℝ) / 4)).summable
  · exact (Real.summable_one_div_int_pow.2 (by norm_num)).mul_left _

theorem deficit_le_majorant38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {δ h : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ lo / 64) (hh : h ≤ lo / 2) {ν : ℤ} {ω : ℝ}
    (hω : 4 * |(ν : ℝ)| ≤ |ω|) :
    δ * (1 + ω ^ 4) / (NlsGge.Weights.weight c ω - h) ≤ alTiltMajorant38 lo δ ν := by
  unfold alTiltMajorant38
  by_cases hν : ν = 0
  · subst hν
    have := (deficit_le_quarter38 hc hδ0 hδ hh ω).2
    simpa using this
  · have := deficit_le_bound38 hc hδ0 hh hν hω
    simpa [hν] using this

end Convergence

section Limit

variable {lo up : ℝ} {c : ℕ → ℝ}

open Classical in
/-- Windowed logarithms of the factors of `D_{δ,h_N}`. -/
def alTiltLogWindow38 (c : ℕ → ℝ) (δ : ℝ) (N : ℕ) (ν : ℤ) : ℝ :=
  if ν ∈ Finset.Icc (-(N : ℤ)) N then
    Real.log (alTiltFactor38 c δ (alOmega38 (alMesh38 N) ν) (alMesh38 N)) else 0

theorem alTiltD_eq_exp38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ lo / 64) {N : ℕ} (hN : alMesh38 N ≤ lo / 2) :
    alTiltD38 c (alMesh38 N) δ N = Real.exp (∑' ν : ℤ, alTiltLogWindow38 c δ N ν) := by
  classical
  rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) N) (fun ν hν => by
    simp [alTiltLogWindow38, hν]), Real.exp_sum]
  unfold alTiltD38
  refine Finset.prod_congr rfl fun ν hν => ?_
  have hb := alTiltFactor_bounds38 hc hδ0 hδ hN (alOmega38 (alMesh38 N) ν)
  simp only [alTiltLogWindow38, hν, ite_true]
  rw [Real.exp_log (by linarith [hb.1])]
  rfl

/-- **Convergence of `D_{δ,h}`** (mode: `h = 1/(2N+1) → 0` along the odd meshes; the limit is the
unconditionally convergent infinite product over `k ∈ ℤ`; real-number topology).
For `0 < δ ≤ lo/64` the limit `D_δ = ∏_{k∈ℤ}(1 - δ(1+(2πk)⁴)/a_k)`, `a_k = W(2πk)`, exists and
is positive, and `D_{δ,h_N} → D_δ`. -/
theorem alTiltD_tendsto38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ lo / 64) :
    ∃ Dδ : ℝ, 0 < Dδ ∧
      HasProd (fun k : ℤ => 1 - δ * (1 + (2 * Real.pi * k) ^ 4) /
        NlsGge.Weights.weight c (2 * Real.pi * k)) Dδ ∧
      Tendsto (fun N : ℕ => alTiltD38 c (alMesh38 N) δ N) atTop (𝓝 Dδ) := by
  classical
  have hlo := hc.1
  have hh0 : Tendsto alMesh38 atTop (𝓝 0) := tendsto_alMesh38.mono_right nhdsWithin_le_nhds
  have hev : ∀ᶠ N : ℕ in atTop, alMesh38 N ≤ lo / 2 :=
    hh0.eventually (Iic_mem_nhds (by positivity))
  set f0 : ℤ → ℝ := fun k => alTiltFactor38 c δ (2 * Real.pi * k) 0 with hf0
  have hf0pos : ∀ k, 0 < f0 k := fun k => by
    have := (alTiltFactor_bounds38 hc hδ0 hδ (h := 0) (by positivity) (2 * Real.pi * k)).1
    linarith
  -- bound on the log of the limit factors
  have hlim_bound : ∀ ν : ℤ, ‖Real.log (f0 ν)‖ ≤ 2 * alTiltMajorant38 lo δ ν := by
    intro ν
    have h1 := abs_log_factor_le38 hc hδ0 hδ (h := 0) (by positivity) (2 * Real.pi * ν)
    have h2 := deficit_le_majorant38 hc hδ0 hδ (h := 0) (by positivity) (ν := ν)
      (ω := 2 * Real.pi * ν) (by
        rw [abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos]
        have := Real.pi_gt_three
        nlinarith [abs_nonneg (ν : ℝ)])
    rw [Real.norm_eq_abs]
    exact h1.trans (by linarith)
  have hsumm : Summable fun ν => Real.log (f0 ν) :=
    Summable.of_norm_bounded ((summable_alTiltMajorant38 lo δ).mul_left 2) hlim_bound
  have hHas := Real.hasProd_of_hasSum_log hf0pos hsumm.hasSum
  refine ⟨Real.exp (∑' ν, Real.log (f0 ν)), Real.exp_pos _, ?_, ?_⟩
  · have e : f0 = fun k : ℤ => 1 - δ * (1 + (2 * Real.pi * k) ^ 4) /
        NlsGge.Weights.weight c (2 * Real.pi * k) := by
      funext k; simp [hf0, alTiltFactor38]
    rw [← e]; exact hHas
  · have hnn : ∀ ν, 0 ≤ alTiltMajorant38 lo δ ν := fun ν => by
      unfold alTiltMajorant38
      have : 0 ≤ 324 * δ / lo := by positivity
      have : 0 ≤ 1 / (ν : ℝ) ^ 2 := by positivity
      split_ifs <;> positivity
    have hab : ∀ ν : ℤ, Tendsto (fun N => alTiltLogWindow38 c δ N ν) atTop
        (𝓝 (Real.log (f0 ν))) := by
      intro ν
      have h1 := (tendsto_alFactor38 hc δ ν).log (hf0pos ν).ne'
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop ν.natAbs] with N hN
      have : ν ∈ Finset.Icc (-(N : ℤ)) N := by
        rw [Finset.mem_Icc]; omega
      simp [alTiltLogWindow38, this]
    have hbd : ∀ᶠ N : ℕ in atTop, ∀ ν : ℤ,
        ‖alTiltLogWindow38 c δ N ν‖ ≤ 2 * alTiltMajorant38 lo δ ν := by
      filter_upwards [hev] with N hN ν
      by_cases hν : ν ∈ Finset.Icc (-(N : ℤ)) N
      · simp only [alTiltLogWindow38, hν, ite_true]
        rw [Real.norm_eq_abs]
        have hmem := Finset.mem_Icc.1 hν
        have hνN : |(ν : ℝ)| * alMesh38 N ≤ 1 / 2 := by
          unfold alMesh38
          have hL : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
          rw [← div_eq_mul_inv, div_le_iff₀ hL]
          have : |ν| ≤ (N : ℤ) := abs_le.2 ⟨by omega, by omega⟩
          have h' : |(ν : ℝ)| ≤ N := by
            rw [← Int.cast_abs]; exact_mod_cast this
          push_cast; linarith
        have h1 := abs_log_factor_le38 hc hδ0 hδ hN (alOmega38 (alMesh38 N) ν)
        have h2 := deficit_le_majorant38 hc hδ0 hδ hN (ν := ν)
          (ω := alOmega38 (alMesh38 N) ν) (alOmega_abs_ge38 (alMesh_pos38 N) hνN)
        linarith
      · simp only [alTiltLogWindow38, hν, ite_false, norm_zero]
        linarith [hnn ν]
    have hT := tendsto_tsum_of_dominated_convergence
      ((summable_alTiltMajorant38 lo δ).mul_left 2) hab hbd
    refine (Real.continuous_exp.tendsto _ |>.comp hT).congr' ?_
    filter_upwards [hev] with N hN
    exact (alTiltD_eq_exp38 hc hδ0 hδ hN).symm

end Limit

section H2

variable {L : ℕ} [NeZero L]

/-- `‖𝓘_h(α/h)‖²_{H²} = Σ_{|k|≤N} (1+k²)² |û_k|²` for the trigonometric interpolant
`u = 𝓘_h(α/h)` with frequencies `-N..N` and Fourier coordinates `û = dft α` (so that
`α_j = h u(jh)`, `dft_symm_eq_interp38`); the sequence-space `h²` norm of the paper,
`⟨n⟩ = (1+n²)^{1/2}`. -/
def alH2Sq38 (α : ZMod L → ℂ) : ℝ :=
  ∑ k : ZMod L, (1 + ((k.valMinAbs : ℤ) : ℝ) ^ 2) ^ 2 * ‖ZMod.dft α k‖ ^ 2

theorem sum_shift_alDelta38 (α : ZMod L → ℂ) :
    ∑ i, ‖((alDelta38)^[2] α) i‖ ^ 2 =
      ∑ j, ‖α (j + 1) - 2 * α j + α (j - 1)‖ ^ 2 := by
  rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod L))]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id, alDelta38,
    Equiv.coe_addRight]
  congr 2; ring

/-- **`G_h ≥ c‖𝓘_h(α/h)‖²_{H²}`**, uniformly for `h = 1/L` (`L ≥ 3`) and all admissible
`α`, with `c = 1/2`: the mass dominates its quadratic part (`C:eq:Msplit`), `K_2` dominates the
squared second difference (`C:eq:Ksquares`), and `|ω_{h,k}| ≥ 4|k|`. -/
theorem alG_H2_lower38 (hL : 3 ≤ L) {α : ZMod L → ℂ} (hα : IsALField38 α) {h : ℝ}
    (hh : h = (L : ℝ)⁻¹) : (1 / 2) * alH2Sq38 α ≤ alTiltG38 h α := by
  open NlsGge.HierarchyRiccati.Core in
  have hLr : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh0 : 0 < h := by rw [hh]; positivity
  -- mass
  have hM : ∑ i, ‖α i‖ ^ 2 ≤ alMass38 L α := by
    rw [← alMd_eq_alMass38, alMd_split]
    have : 0 ≤ ∑ j, alEll (alR α j) :=
      Finset.sum_nonneg fun j _ => alEll_nonneg (by unfold alR; positivity)
        (alR_lt_one α hα j)
    have e : ∑ j, alR α j = ∑ i, ‖α i‖ ^ 2 := rfl
    linarith
  -- fourth order
  have hK : ∑ j, ‖α (j + 1) - 2 * α j + α (j - 1)‖ ^ 2 ≤ alK38 α 2 := by
    rw [alK38_two_eq_alKd hL hα, alKd_squares]
    have h1 : 0 ≤ ∑ j, (alR α (j + 1) - alR α j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have h2 : 0 ≤ ∑ j, alR α j * ‖α (j + 1) - α (j - 1)‖ ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (by unfold alR; positivity) (by positivity)
    have h4 : 0 ≤ ∑ j, (-Real.log (1 - alR α j) - alR α j - (1 / 2) * alR α j ^ 2) :=
      Finset.sum_nonneg fun j _ => alEll_sq_nonneg (by unfold alR; positivity)
        (alR_lt_one α hα j)
    refine le_add_of_le_of_nonneg (le_add_of_le_of_nonneg (le_add_of_le_of_nonneg
      (le_add_of_le_of_nonneg le_rfl ?_) ?_) ?_) ?_
    · exact mul_nonneg (by norm_num) h1
    · exact h2
    · positivity
    · exact mul_nonneg (by norm_num) h4
  -- Fourier side
  have hP := sum_norm_sq_eq_dft38 α hh
  have hD := alDelta_parseval38 2 α
  rw [sum_shift_alDelta38] at hD
  have hG : alTiltG38 h α = h⁻¹ * alMass38 L α + (h⁻¹) ^ 5 * alK38 α 2 := by
    unfold alTiltG38 alQ38
    rw [alMomentK38_eq_alK38, alMomentK38_eq_alK38, alK38_zero]; simp
  have hhL : (L : ℝ)⁻¹ = h := hh.symm
  have hlow : ∑ k : ZMod L, (1 + alOmega38 h k.valMinAbs ^ 4) * ‖ZMod.dft α k‖ ^ 2 ≤
      alTiltG38 h α := by
    rw [hG]
    have a1 : h⁻¹ * ∑ i, ‖α i‖ ^ 2 ≤ h⁻¹ * alMass38 L α :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    have a2 : (h⁻¹) ^ 5 * ∑ j, ‖α (j + 1) - 2 * α j + α (j - 1)‖ ^ 2 ≤
        (h⁻¹) ^ 5 * alK38 α 2 := mul_le_mul_of_nonneg_left hK (by positivity)
    have b1 : h⁻¹ * ∑ i, ‖α i‖ ^ 2 = ∑ k : ZMod L, ‖ZMod.dft α k‖ ^ 2 := by
      rw [hP]; field_simp
    have b2 : (h⁻¹) ^ 5 * ∑ j, ‖α (j + 1) - 2 * α j + α (j - 1)‖ ^ 2 =
        ∑ k : ZMod L, alOmega38 h k.valMinAbs ^ 4 * ‖ZMod.dft α k‖ ^ 2 := by
      rw [hD, hhL, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : Real.pi * (k.valMinAbs : ℝ) / L = Real.pi * k.valMinAbs * h := by rw [hh]; ring
      unfold alOmega38
      rw [this]
      have : h ≠ 0 := hh0.ne'
      field_simp
      ring
    have : ∑ k : ZMod L, (1 + alOmega38 h k.valMinAbs ^ 4) * ‖ZMod.dft α k‖ ^ 2 =
        ∑ k : ZMod L, ‖ZMod.dft α k‖ ^ 2 +
          ∑ k : ZMod L, alOmega38 h k.valMinAbs ^ 4 * ‖ZMod.dft α k‖ ^ 2 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    linarith
  refine le_trans ?_ hlow
  unfold alH2Sq38
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hk : |((k.valMinAbs : ℤ) : ℝ)| * h ≤ 1 / 2 := by
    have h1 := ZMod.natAbs_valMinAbs_le k
    have h2 : ((k.valMinAbs.natAbs : ℕ) : ℝ) ≤ (L : ℝ) / 2 := by
      have : (k.valMinAbs.natAbs : ℝ) * 2 ≤ L := by
        have := Nat.div_mul_le_self L 2
        exact_mod_cast le_trans (Nat.mul_le_mul_right 2 h1) this
      linarith
    have h3 : |((k.valMinAbs : ℤ) : ℝ)| = (k.valMinAbs.natAbs : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
    rw [h3, hh]
    rw [← div_eq_mul_inv, div_le_iff₀ hLr]; linarith
  have hω := alOmega_abs_ge38 hh0 hk
  set x : ℝ := ((k.valMinAbs : ℤ) : ℝ) with hx
  set ω := alOmega38 h k.valMinAbs with hωd
  have h4 : (4 * |x|) ^ 4 ≤ |ω| ^ 4 := pow_le_pow_left₀ (by positivity) hω 4
  have h5 : |x| ^ 4 = x ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
  have h6 : |ω| ^ 4 = ω ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
  rw [mul_pow, h5, h6] at h4
  have h7 : (1 + x ^ 2) ^ 2 ≤ 2 * (1 + ω ^ 4) := by nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg x]
  have : 0 ≤ ‖ZMod.dft α k‖ ^ 2 := by positivity
  nlinarith

/-- Uniform form: `∃ c > 0`, for every `L ≥ 3` and `h = 1/L`, every admissible `α`. -/
theorem alG_H2_lower_exists38 :
    ∃ c : ℝ, 0 < c ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ {α : ZMod L → ℂ}, IsALField38 α →
      ∀ {h : ℝ}, h = (L : ℝ)⁻¹ → c * alH2Sq38 α ≤ alTiltG38 h α :=
  ⟨1 / 2, by norm_num, fun L _ hL _ hα _ hh => alG_H2_lower38 hL hα hh⟩

end H2

end NlsGge.AblowitzLadik
end

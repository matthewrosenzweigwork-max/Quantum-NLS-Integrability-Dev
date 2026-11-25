import NlsGge.GK38.PairVolterraPower

/-!
# F2: the Volterra operator, the fundamental solution and the integral equation (plan section 6.2)

Source: Grébert-Kappeler book, Chapter I, section 1, Theorem 1.1 and its proof (GKP `(2)`):
the fundamental solution `M(t, λ, φ)` of `L(φ)M = λM`, `M(0) = Id`, is `(1 - 𝒱)⁻¹ E_λ`, where
`𝒱 N (t) = ∫₀ᵗ E_λ(t-s) Φ̃(s) N(s) ds` on `C([0,1], M₂(ℂ))`; `1 - 𝒱` is invertible by the Neumann
series because `‖𝒱ⁿ‖ ≤ e^{|Im λ|} ‖φ‖₁ⁿ / n!` (`norm_volterraP_pow_le`).

## Files

* `PairVolterraDefs.lean`: `freeE`, `freeFund`, `potCoeff38`, `ext38`, entry bounds;
* `PairVolterraOp.lean`: `volterraFun`, the bounded operator `volterraP` on the sup-norm space
  `PairCont38 = C(Icc, Fin 2 → Fin 2 → ℂ)`;
* `PairVolterraPower.lean`: the iterate estimate and the Neumann step;
* this file: the statements of plan 6.2 at the type `C(Icc, Matrix (Fin 2) (Fin 2) ℂ)`, the
  integral equation and uniqueness (`fundPair_integral_eq`, `fundCont_unique`), the entrywise bound
  `|M(t)_{ij}| ≤ exp(|Im z| t + ∫₀ᵗ (|φ₁| + |φ₂|))` (`norm_fundPair_entry_le`, by the truncated
  Neumann expansion `M = Σ_{k<n} 𝒱ᵏE + 𝒱ⁿM`, `fundCont_eq_sum`), and linearity/Lipschitz dependence
  of `𝒱_φ` on `φ` (`volterraP_sub`, `norm_volterraP_sub_le`, for F3);
* `PairVolterraProbe.lean`: probes (`φ = 0`, constant potential).

## Convention (binding instruction from the F1 review, finding N2)

`volterra` and hence `monodromyPair`, `fundPair` use F1's representatives `potRepFst38 φ`,
`potRepSnd38 φ`, i.e. the coefficient `potCoeff38 φ = [[0, iφ₁],[-iφ₂, 0]]` with
`zsCoeffPot38 φ z = -zR + potCoeff38 φ` (`zsCoeffPot38_eq`).  The Volterra integrals are integrals
of the scalar entries (`..) i j`); a matrix is the matrix of its entry integrals.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.GK38

noncomputable section

/-- The Volterra operator `(𝒱 N)(t) = ∫₀ᵗ E_z(t-s) [[0, iφ₁(s)],[-iφ₂(s), 0]] N(s) ds` (book `(1.2)`,
GKP `(2)`), with the representatives `potRepFst38 φ`, `potRepSnd38 φ` of F1.  Defined as the
bounded operator `volterraP` (`‖𝒱‖ ≤ e^{|Im z|} ‖φ‖₁`, `norm_volterraP_le`). -/
def volterra (φ : PotPair) (z : ℂ) :
    C(Set.Icc (0 : ℝ) 1, Matrix (Fin 2) (Fin 2) ℂ) →L[ℂ]
      C(Set.Icc (0 : ℝ) 1, Matrix (Fin 2) (Fin 2) ℂ) :=
  volterraP φ z

/-- Entrywise formula for `𝒱 N`, with `N` extended constantly beyond `[0,1]` (irrelevant: only
`s ∈ [0,t]` enters). -/
theorem volterra_apply (φ : PotPair) (z : ℂ) (N : C(Set.Icc (0 : ℝ) 1, Matrix (Fin 2) (Fin 2) ℂ))
    (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    volterra φ z N t i j =
      ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * Set.IccExtend zero_le_one N s) i j :=
  rfl

/-- `1 - 𝒱` is invertible: Neumann series, `‖𝒱ⁿ‖ ≤ e^{|Im z|} ‖φ‖₁ⁿ / n!` (book Theorem 1.1). -/
theorem isUnit_one_sub_volterra (φ : PotPair) (z : ℂ) : IsUnit (1 - volterra φ z) :=
  isUnit_one_sub_volterraP φ z

/-- The fundamental solution `(1 - 𝒱)⁻¹ E_z` as a continuous function on `[0,1]`. -/
def fundCont (φ : PotPair) (z : ℂ) : C(Set.Icc (0 : ℝ) 1, Matrix (Fin 2) (Fin 2) ℂ) :=
  Ring.inverse (1 - volterra φ z) (freeFund z)

/-- The monodromy matrix `M(1, z, φ)` of the unit-period problem (book Chapter I, section 1). -/
def monodromyPair (φ : PotPair) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Ring.inverse (1 - volterra φ z) (freeFund z)) ⟨1, by norm_num, le_rfl⟩

/-- The fundamental solution `M(t, z, φ)`, `t ∈ [0,1]` (rev. 4.1: the `t`-version). -/
def fundPair (φ : PotPair) (z : ℂ) (t : Set.Icc (0 : ℝ) 1) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Ring.inverse (1 - volterra φ z) (freeFund z)) t

theorem fundPair_eq (φ : PotPair) (z : ℂ) (t : Set.Icc (0 : ℝ) 1) :
    fundPair φ z t = fundCont φ z t := rfl

theorem monodromyPair_eq_fundPair (φ : PotPair) (z : ℂ) :
    monodromyPair φ z = fundPair φ z ⟨1, by norm_num, le_rfl⟩ := rfl

/-! ### The integral equation and uniqueness -/

theorem fundCont_sub_volterra (φ : PotPair) (z : ℂ) :
    fundCont φ z - volterra φ z (fundCont φ z) = freeFund z := by
  have hu := isUnit_one_sub_volterra φ z
  have h := congrArg (fun T => T (freeFund z)) (Ring.mul_inverse_cancel _ hu)
  simpa [fundCont, sub_apply] using h

/-- `M(t) = E_z(t) + ∫₀ᵗ E_z(t-s) Φ̃(s) M(s) ds` (book `(1.2)`, entrywise), `M = fundPair φ z`. -/
theorem fundPair_integral_eq (φ : PotPair) (z : ℂ) (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    fundPair φ z t i j = freeE z t i j +
      ∫ s in (0 : ℝ)..t,
        (freeE z (t - s) * potCoeff38 φ s *
          Set.IccExtend zero_le_one (fundPair φ z) s) i j := by
  have h := congrArg (fun F => F t i j) (fundCont_sub_volterra φ z)
  simp only [ContinuousMap.sub_apply, Matrix.sub_apply, freeFund_apply] at h
  rw [volterra_apply] at h
  have h3 : fundPair φ z = ⇑(fundCont φ z) := rfl
  rw [h3]
  linear_combination h

theorem monodromyPair_integral_eq (φ : PotPair) (z : ℂ) (i j : Fin 2) :
    monodromyPair φ z i j = freeE z 1 i j +
      ∫ s in (0 : ℝ)..1,
        (freeE z (1 - s) * potCoeff38 φ s *
          Set.IccExtend zero_le_one (fundPair φ z) s) i j :=
  fundPair_integral_eq φ z ⟨1, by norm_num, le_rfl⟩ i j

/-- `M(0) = Id`. -/
theorem fundPair_zero (φ : PotPair) (z : ℂ) : fundPair φ z ⟨0, le_rfl, zero_le_one⟩ = 1 := by
  ext i j
  rw [fundPair_integral_eq]
  simp [freeE_zero]

/-- Uniqueness: a continuous solution of the integral equation is `fundCont φ z`. -/
theorem fundCont_unique (φ : PotPair) (z : ℂ) (G : C(Set.Icc (0 : ℝ) 1, Matrix (Fin 2) (Fin 2) ℂ))
    (hG : ∀ (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2), G t i j = freeE z t i j +
      ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * Set.IccExtend zero_le_one G s) i j) :
    G = fundCont φ z := by
  have hu := isUnit_one_sub_volterra φ z
  have h1 : (1 - volterra φ z) G = freeFund z := by
    ext t i j
    show G t i j - volterra φ z G t i j = freeE z t i j
    rw [volterra_apply, hG t i j]
    ring
  calc G = (1 : C(Set.Icc (0 : ℝ) 1, Matrix (Fin 2) (Fin 2) ℂ) →L[ℂ]
        C(Set.Icc (0 : ℝ) 1, Matrix (Fin 2) (Fin 2) ℂ)) G := rfl
    _ = (Ring.inverse (1 - volterra φ z) * (1 - volterra φ z)) G := by
        rw [Ring.inverse_mul_cancel _ hu]
    _ = Ring.inverse (1 - volterra φ z) ((1 - volterra φ z) G) := rfl
    _ = fundCont φ z := by rw [h1]; rfl

/-- `fundCont φ z` at the (definitionally equal) normed type `PairCont38`. -/
def fundContP (φ : PotPair) (z : ℂ) : PairCont38 := fundCont φ z

/-- `freeFund z` at the normed type `PairCont38`. -/
def freeFundP (z : ℂ) : PairCont38 := freeFund z

/-! ### The bound `|M(t)_{ij}| ≤ exp(|Im z| t + ∫₀ᵗ (|φ₁| + |φ₂|))` (book Theorem 1.1, `L¹` form) -/

theorem fundCont_eq_add (φ : PotPair) (z : ℂ) :
    (fundContP φ z) = (freeFundP z) +
      volterraP φ z (fundContP φ z) := by
  ext t i j
  have h := congrArg (fun F => F t i j) (fundCont_sub_volterra φ z)
  simp only [ContinuousMap.sub_apply, Matrix.sub_apply, freeFund_apply] at h
  show fundCont φ z t i j = freeE z t i j + volterra φ z (fundCont φ z) t i j
  linear_combination h

/-- Truncated Neumann expansion `M = Σ_{k<n} 𝒱ᵏ E + 𝒱ⁿ M`. -/
theorem fundCont_eq_sum (φ : PotPair) (z : ℂ) (n : ℕ) :
    (fundContP φ z) = (∑ k ∈ Finset.range n, (volterraP φ z ^ k) (freeFundP z)) +
      (volterraP φ z ^ n) (fundContP φ z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (volterraP φ z ^ n) (fundContP φ z) =
        (volterraP φ z ^ n) (freeFundP z) +
          (volterraP φ z ^ (n + 1)) (fundContP φ z) := by
      conv_lhs => rw [fundCont_eq_add φ z]
      rw [map_add, pow_succ, mul_apply_eq_comp]
    rw [Finset.sum_range_succ, add_assoc, ← h1]
    exact ih

theorem norm_fundCont_entry_le (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (i j : Fin 2) :
    ‖fundCont φ z ⟨t, ht⟩ i j‖ ≤ Real.exp (|z.im| * t + potPrim38 φ t) := by
  set a : ℝ := |z.im|
  set W : ℝ := potPrim38 φ t with hW
  have hE : ∀ (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2),
      ‖(freeFundP z) ⟨s, hs⟩ i j‖ ≤ Real.exp (a * s) * 1 := fun s hs i j => by
    have := norm_freeE_entry_le z s i j
    rw [abs_of_nonneg hs.1] at this
    show ‖freeE z s i j‖ ≤ Real.exp (a * s) * 1
    rw [mul_one]; exact this
  have hbound : ∀ n : ℕ, ‖fundCont φ z ⟨t, ht⟩ i j‖ ≤
      Real.exp (a * t) * (∑ k ∈ Finset.range n, W ^ k / k.factorial) +
        Real.exp (a * t) * (W ^ n / n.factorial) * ‖(fundContP φ z)‖ := by
    intro n
    have h := congrArg (fun F : PairCont38 => F ⟨t, ht⟩ i j) (fundCont_eq_sum φ z n)
    simp only [ContinuousMap.add_apply, Pi.add_apply, ContinuousMap.coe_sum, Finset.sum_apply] at h
    have hfc : fundCont φ z ⟨t, ht⟩ i j = (∑ k ∈ Finset.range n,
        ((volterraP φ z ^ k) (freeFundP z)) ⟨t, ht⟩ i j) +
        ((volterraP φ z ^ n) (fundContP φ z)) ⟨t, ht⟩ i j := h
    rw [hfc]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      have := norm_volterra_pow_entry_le_weighted φ z k (freeFundP z) 1 hE ht i j
      simpa using this
    · exact norm_volterra_pow_entry_le φ z n (fundContP φ z) ht i j
  have hlim : Tendsto (fun n : ℕ => Real.exp (a * t) * (∑ k ∈ Finset.range n, W ^ k / k.factorial) +
        Real.exp (a * t) * (W ^ n / n.factorial) * ‖(fundContP φ z)‖) atTop
      (𝓝 (Real.exp (a * t) * Real.exp W + Real.exp (a * t) * 0 * ‖(fundContP φ z)‖)) := by
    have h1 := (NormedSpace.expSeries_div_hasSum_exp W).tendsto_sum_nat
    rw [← Real.exp_eq_exp_ℝ] at h1
    have h2 := FloorSemiring.tendsto_pow_div_factorial_atTop W
    exact (h1.const_mul _).add (((h2.const_mul _)).mul_const _)
  have := ge_of_tendsto' hlim hbound
  calc _ ≤ _ := this
    _ = Real.exp (a * t + W) := by rw [Real.exp_add]; ring

theorem norm_fundPair_entry_le (φ : PotPair) (z : ℂ) (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    ‖fundPair φ z t i j‖ ≤ Real.exp (|z.im| * t + potPrim38 φ t) :=
  norm_fundCont_entry_le φ z t.2 i j

/-- Book Theorem 1.1, `L¹` form, entrywise: `|M(1)_{ij}| ≤ exp(|Im z| + ‖φ‖₁)`. -/
theorem norm_monodromyPair_entry_le (φ : PotPair) (z : ℂ) (i j : Fin 2) :
    ‖monodromyPair φ z i j‖ ≤ Real.exp (|z.im| + potL1Norm38 φ) := by
  have := norm_fundPair_entry_le φ z ⟨1, by norm_num, le_rfl⟩ i j
  rw [monodromyPair_eq_fundPair]
  simpa [potPrim38_one] using this

open scoped Matrix.Norms.Elementwise in
/-- The same, for the entrywise sup norm of the matrix (book Theorem 1.1, `L¹` form).  (For the
`L^∞`-operator norm of `Matrix`, which is at most twice the entrywise one, F3 states its own form.) -/
theorem norm_monodromyPair_le_elementwise (φ : PotPair) (z : ℂ) :
    ‖monodromyPair φ z‖ ≤ Real.exp (|z.im| + potL1Norm38 φ) :=
  (Matrix.norm_le_iff (Real.exp_nonneg _)).2 fun i j => norm_monodromyPair_entry_le φ z i j

/-! ### Dependence on the potential (for F3: linearity and Lipschitz continuity in `φ`) -/

theorem potCoeff38_add_ae (φ ψ : PotPair) :
    ∀ᵐ s : ℝ, potCoeff38 (φ + ψ) s = potCoeff38 φ s + potCoeff38 ψ s := by
  filter_upwards [coverRep38_add_ae φ.1 ψ.1, coverRep38_add_ae φ.2 ψ.2] with s h1 h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [potCoeff38, potRepFst38, potRepSnd38, h1, h2, mul_add]
  ring

theorem potCoeff38_sub_ae (φ ψ : PotPair) :
    ∀ᵐ s : ℝ, potCoeff38 (φ - ψ) s = potCoeff38 φ s - potCoeff38 ψ s := by
  filter_upwards [coverRep38_sub_ae φ.1 ψ.1, coverRep38_sub_ae φ.2 ψ.2] with s h1 h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [potCoeff38, potRepFst38, potRepSnd38, h1, h2, mul_sub]
  ring

theorem potCoeff38_smul_ae (c : ℂ) (φ : PotPair) :
    ∀ᵐ s : ℝ, potCoeff38 (c • φ) s = c • potCoeff38 φ s := by
  filter_upwards [coverRep38_smul_ae c φ.1, coverRep38_smul_ae c φ.2] with s h1 h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [potCoeff38, potRepFst38, potRepSnd38, h1, h2]
  · ring
  · ring

theorem volterraFun_sub (φ ψ : PotPair) (z : ℂ) (N : PairCont38) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    volterraFun (φ - ψ) z N t i j = volterraFun φ z N t i j - volterraFun ψ z N t i j := by
  simp only [volterraFun_apply]
  have hK : Continuous fun s : ℝ => freeE z (t - s) := (continuous_freeE z).comp
    (continuous_const.sub continuous_id)
  rw [← intervalIntegral.integral_sub
    (intervalIntegrable_triple_entry_of_mem φ hK (continuous_ext38 N) ht i j)
    (intervalIntegrable_triple_entry_of_mem ψ hK (continuous_ext38 N) ht i j)]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [potCoeff38_sub_ae φ ψ] with s hs _
  rw [hs, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]

theorem volterraFun_smul_potential (c : ℂ) (φ : PotPair) (z : ℂ) (N : PairCont38) (t : ℝ)
    (i j : Fin 2) :
    volterraFun (c • φ) z N t i j = c * volterraFun φ z N t i j := by
  simp only [volterraFun_apply]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [potCoeff38_smul_ae c φ] with s hs _
  rw [hs, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

/-- `φ ↦ 𝒱_φ` is real-linear on the nose and additive: `𝒱_{φ-ψ} = 𝒱_φ - 𝒱_ψ` (a.e. linearity of the
representatives, F1). -/
theorem volterraP_sub (φ ψ : PotPair) (z : ℂ) :
    volterraP (φ - ψ) z = volterraP φ z - volterraP ψ z := by
  ext N t i j
  exact volterraFun_sub φ ψ z N t.2 i j

theorem volterraP_smul_potential (c : ℂ) (φ : PotPair) (z : ℂ) :
    volterraP (c • φ) z = c • volterraP φ z := by
  ext N t i j
  exact volterraFun_smul_potential c φ z N t i j

/-- Lipschitz dependence on the potential, in the `L²` norm: `‖𝒱_φ - 𝒱_ψ‖ ≤ e^{|Im z|} (‖φ₁ - ψ₁‖ +
‖φ₂ - ψ₂‖)` (F1: `potL1Norm38_le`). -/
theorem norm_volterraP_sub_le (φ ψ : PotPair) (z : ℂ) :
    ‖volterraP φ z - volterraP ψ z‖ ≤ Real.exp |z.im| * (‖φ.1 - ψ.1‖ + ‖φ.2 - ψ.2‖) := by
  rw [← volterraP_sub]
  exact (norm_volterraP_le (φ - ψ) z).trans
    (mul_le_mul_of_nonneg_left (potL1Norm38_le (φ - ψ)) (Real.exp_nonneg _))

theorem volterra_sub (φ ψ : PotPair) (z : ℂ) :
    volterra (φ - ψ) z = volterra φ z - volterra ψ z := volterraP_sub φ ψ z

theorem volterra_smul_potential (c : ℂ) (φ : PotPair) (z : ℂ) :
    volterra (c • φ) z = c • volterra φ z := volterraP_smul_potential c φ z

end

end NlsGge.GK38

import NlsGge.GK38.PairVolterraDefs

/-!
# F2 (part 2): the Volterra operator as a bounded operator on `C([0,1], M₂(ℂ))`

`(𝒱 N)(t) = ∫₀ᵗ E_z(t-s) Φ̃(s) N(s) ds` (book Chapter I, section 1, proof of Theorem 1.1),
with `Φ̃ = potCoeff38 φ` the coefficient of F1's representatives.  Entries are integrals of scalar
functions.  The operator is bounded on the sup norm with `‖𝒱‖ ≤ e^{|Im z|} ‖φ‖₁`
(`‖φ‖₁ = potL1Norm38 φ`): this is the `L¹ × C → C` packaging of the bilinear map
`(φ, N) ↦ ∫ E φ N` (the plan's risk note; the `L²` potential enters only through its `L¹` norm,
`potL1Norm38_le`).
-/

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.GK38

noncomputable section

/-! ### Entries of products and integrability -/

theorem mul3_apply (A B C : PairMat38) (i j : Fin 2) :
    (A * B * C) i j = ∑ l, ∑ k, A i k * B k l * C l j := by
  simp only [Matrix.mul_apply, Finset.sum_mul]

theorem freeE_mul_apply (z : ℂ) (t : ℝ) (X : PairMat38) (i j : Fin 2) :
    (freeE z t * X) i j = freeE z t i i * X i j := by
  fin_cases i <;> fin_cases j <;> simp [freeE, Matrix.mul_apply, Fin.sum_univ_two]

theorem uIcc_zero_subset {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Set.uIcc (0 : ℝ) t ⊆ Set.uIcc 0 1 := by
  rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]
  exact Set.Icc_subset_Icc le_rfl ht.2

theorem intervalIntegrable_fsum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ} {a b : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun x => ∑ i ∈ s, f i x) volume a b := by
  have := IntervalIntegrable.sum s h
  simpa [Finset.sum_fn] using this

/-- The entries of `K(s) Φ̃(s) N(s)` are interval integrable for continuous `K`, `N`. -/
theorem intervalIntegrable_triple_entry (φ : PotPair) {K N : ℝ → PairMat38} (hK : Continuous K)
    (hN : Continuous N) (i j : Fin 2) :
    IntervalIntegrable (fun s => (K s * potCoeff38 φ s * N s) i j) volume 0 1 := by
  simp_rw [mul3_apply]
  refine intervalIntegrable_fsum _ fun l _ => intervalIntegrable_fsum _ fun k _ => ?_
  have hK' : Continuous fun s => K s i k := (continuous_apply k).comp ((continuous_apply i).comp hK)
  have hN' : Continuous fun s => N s l j := (continuous_apply j).comp ((continuous_apply l).comp hN)
  exact (((intervalIntegrable_potCoeff38_entry φ k l).continuousOn_mul
    hK'.continuousOn).mul_continuousOn hN'.continuousOn)

theorem intervalIntegrable_triple_entry_of_mem (φ : PotPair) {K N : ℝ → PairMat38}
    (hK : Continuous K) (hN : Continuous N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    IntervalIntegrable (fun s => (K s * potCoeff38 φ s * N s) i j) volume 0 t :=
  (intervalIntegrable_triple_entry φ hK hN i j).mono_set (uIcc_zero_subset ht)

/-! ### The operator -/

/-- `(𝒱 N)(t) = ∫₀ᵗ E_z(t-s) Φ̃(s) N(s) ds`, entrywise. -/
def volterraFun (φ : PotPair) (z : ℂ) (N : PairCont38) (t : ℝ) : PairMat38 :=
  Matrix.of fun i j => ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * ext38 N s) i j

/-- The `t`-independent kernel integral `∫₀ᵗ E_z(-s) Φ̃(s) N(s) ds`. -/
def volterraKer (φ : PotPair) (z : ℂ) (N : PairCont38) (t : ℝ) : PairMat38 :=
  Matrix.of fun i j => ∫ s in (0 : ℝ)..t, (freeE z (-s) * potCoeff38 φ s * ext38 N s) i j

theorem volterraFun_apply (φ : PotPair) (z : ℂ) (N : PairCont38) (t : ℝ) (i j : Fin 2) :
    volterraFun φ z N t i j =
      ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * ext38 N s) i j := rfl

/-- Factorization `E_z(t-s) = E_z(t) E_z(-s)`. -/
theorem volterraFun_eq (φ : PotPair) (z : ℂ) (N : PairCont38) (t : ℝ) :
    volterraFun φ z N t = freeE z t * volterraKer φ z N t := by
  ext i j
  rw [freeE_mul_apply, volterraFun_apply]
  simp only [volterraKer, Matrix.of_apply]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [sub_eq_add_neg, freeE_add, mul_assoc, mul_assoc, ← mul_assoc (freeE z (-s)), freeE_mul_apply]

theorem norm_triple_entry_le (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (φ : PotPair) (s : ℝ) (N : PairMat38)
    {β : ℝ} (hβ : ∀ i j, ‖N i j‖ ≤ β) (i j : Fin 2) :
    ‖(freeE z r * potCoeff38 φ s * N) i j‖ ≤ Real.exp (|z.im| * r) * (potW38 φ s * β) := by
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ 0 0)
  have h1 := norm_nonneg (potRepFst38 φ s)
  have h2 := norm_nonneg (potRepSnd38 φ s)
  have hE : ∀ a b, ‖freeE z r a b‖ ≤ Real.exp (|z.im| * r) := fun a b => by
    simpa [abs_of_nonneg hr] using norm_freeE_entry_le z r a b
  have he : 0 ≤ Real.exp (|z.im| * r) := Real.exp_nonneg _
  have hw1 : ‖potRepFst38 φ s‖ ≤ potW38 φ s := by unfold potW38; linarith
  have hw2 : ‖potRepSnd38 φ s‖ ≤ potW38 φ s := by unfold potW38; linarith
  have hw0 : 0 ≤ potW38 φ s := potW38_nonneg φ s
  have hE0 : ‖Complex.exp (-(Complex.I * z * ↑r))‖ ≤ Real.exp (|z.im| * r) := by
    simpa [freeE] using hE 0 0
  have hE1 : ‖Complex.exp (Complex.I * z * ↑r)‖ ≤ Real.exp (|z.im| * r) := by
    simpa [freeE] using hE 1 1
  fin_cases i <;> fin_cases j <;>
    (rw [mul3_apply]; simp only [Fin.sum_univ_two]; simp [freeE, potCoeff38])
  · calc _ ≤ Real.exp (|z.im| * r) * potW38 φ s * β :=
          mul_le_mul (mul_le_mul hE0 hw1 (norm_nonneg _) he) (hβ 1 0) (norm_nonneg _)
            (mul_nonneg he hw0)
      _ = _ := by ring
  · calc _ ≤ Real.exp (|z.im| * r) * potW38 φ s * β :=
          mul_le_mul (mul_le_mul hE0 hw1 (norm_nonneg _) he) (hβ 1 1) (norm_nonneg _)
            (mul_nonneg he hw0)
      _ = _ := by ring
  · calc _ ≤ Real.exp (|z.im| * r) * potW38 φ s * β :=
          mul_le_mul (mul_le_mul hE1 hw2 (norm_nonneg _) he) (hβ 0 0) (norm_nonneg _)
            (mul_nonneg he hw0)
      _ = _ := by ring
  · calc _ ≤ Real.exp (|z.im| * r) * potW38 φ s * β :=
          mul_le_mul (mul_le_mul hE1 hw2 (norm_nonneg _) he) (hβ 0 1) (norm_nonneg _)
            (mul_nonneg he hw0)
      _ = _ := by ring

/-! ### Continuity of `𝒱 N` -/

theorem continuousOn_volterraKer_entry (φ : PotPair) (z : ℂ) (N : PairCont38) (i j : Fin 2) :
    ContinuousOn (fun t => volterraKer φ z N t i j) (Set.Icc (0 : ℝ) 1) := by
  have hKc : Continuous fun s : ℝ => freeE z (-s) := (continuous_freeE z).comp continuous_neg
  have hint := intervalIntegrable_triple_entry φ hKc (continuous_ext38 N) i j
  have h2 := (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hint
  have h3 := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := 1) (by
    rwa [Set.uIcc_of_le zero_le_one])
  rw [Set.uIcc_of_le zero_le_one] at h3
  exact h3

/-- `𝒱 N` as a continuous function on `[0,1]`. -/
def volterraMap (φ : PotPair) (z : ℂ) (N : PairCont38) : PairCont38 where
  toFun t := fun i j => volterraFun φ z N t i j
  continuous_toFun := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have hk := (continuousOn_volterraKer_entry φ z N i j).domRestrict
    have he : Continuous fun t : Set.Icc (0 : ℝ) 1 => freeE z t i i :=
      ((continuous_apply i).comp ((continuous_apply i).comp (continuous_freeE z))).comp
        continuous_subtype_val
    refine (he.mul hk).congr fun t => ?_
    show freeE z t i i * volterraKer φ z N t i j = volterraFun φ z N t i j
    rw [volterraFun_eq, freeE_mul_apply]

theorem volterraMap_apply (φ : PotPair) (z : ℂ) (N : PairCont38) (t : Set.Icc (0 : ℝ) 1)
    (i j : Fin 2) : volterraMap φ z N t i j = volterraFun φ z N t i j := rfl

theorem volterraMap_add (φ : PotPair) (z : ℂ) (N₁ N₂ : PairCont38) :
    volterraMap φ z (N₁ + N₂) = volterraMap φ z N₁ + volterraMap φ z N₂ := by
  ext t i j
  have hadd : ∀ s, ext38 (N₁ + N₂) s = ext38 N₁ s + ext38 N₂ s := fun s => rfl
  simp only [volterraMap_apply, ContinuousMap.add_apply, Pi.add_apply, volterraFun_apply, hadd,
    mul_add, Matrix.add_apply]
  exact intervalIntegral.integral_add
    (intervalIntegrable_triple_entry_of_mem φ ((continuous_freeE z).comp
      (continuous_const.sub continuous_id)) (continuous_ext38 N₁) t.2 i j)
    (intervalIntegrable_triple_entry_of_mem φ ((continuous_freeE z).comp
      (continuous_const.sub continuous_id)) (continuous_ext38 N₂) t.2 i j)

theorem volterraMap_smul (φ : PotPair) (z : ℂ) (c : ℂ) (N : PairCont38) :
    volterraMap φ z (c • N) = c • volterraMap φ z N := by
  ext t i j
  have hsmul : ∀ s, ext38 (c • N) s = c • ext38 N s := fun s => rfl
  simp only [volterraMap_apply, ContinuousMap.smul_apply, Pi.smul_apply, volterraFun_apply, hsmul,
    Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
  exact intervalIntegral.integral_const_mul c _

/-! ### The bound `‖𝒱 N (t)‖ ≤ ∫₀ᵗ e^{|Im z|(t-s)} |Φ̃(s)| β(s) ds` -/

theorem norm_volterraFun_entry_le (φ : PotPair) (z : ℂ) (N : PairCont38) (β : ℝ → ℝ)
    (hβ : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j, ‖ext38 N s i j‖ ≤ β s)
    (hint : IntervalIntegrable (fun s => potW38 φ s * β s) volume 0 1) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    ‖volterraFun φ z N t i j‖ ≤
      ∫ s in (0 : ℝ)..t, Real.exp (|z.im| * (t - s)) * (potW38 φ s * β s) := by
  rw [volterraFun_apply]
  refine intervalIntegral.norm_integral_le_of_norm_le ht.1 ?_ ?_
  · refine Filter.Eventually.of_forall fun s hs => ?_
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.trans ht.2⟩
    exact norm_triple_entry_le z (sub_nonneg.mpr hs.2) φ s (ext38 N s) (hβ s hs') i j
  · have hc : Continuous fun s : ℝ => Real.exp (|z.im| * (t - s)) := by fun_prop
    exact (hint.mono_set (uIcc_zero_subset ht)).continuousOn_mul hc.continuousOn

theorem norm_volterraFun_entry_le_const (φ : PotPair) (z : ℂ) (N : PairCont38) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    ‖volterraFun φ z N t i j‖ ≤ Real.exp |z.im| * potL1Norm38 φ * ‖N‖ := by
  have hint : IntervalIntegrable (fun s => potW38 φ s * ‖N‖) volume 0 1 :=
    (intervalIntegrable_potW38 φ).mul_const _
  refine (norm_volterraFun_entry_le φ z N (fun _ => ‖N‖)
    (fun s hs i j => norm_ext38_entry_le N hs i j) hint ht i j).trans ?_
  have hw : IntervalIntegrable (fun s => potW38 φ s) volume 0 t :=
    (intervalIntegrable_potW38 φ).mono_set (uIcc_zero_subset ht)
  have hc : Continuous fun s : ℝ => Real.exp (|z.im| * (t - s)) := by fun_prop
  calc ∫ s in (0 : ℝ)..t, Real.exp (|z.im| * (t - s)) * (potW38 φ s * ‖N‖)
      ≤ ∫ s in (0 : ℝ)..t, Real.exp |z.im| * (potW38 φ s * ‖N‖) := by
        refine intervalIntegral.integral_mono_on ht.1 ?_ ?_ fun s hs => ?_
        · exact (hw.mul_const _).continuousOn_mul hc.continuousOn
        · exact (hw.mul_const _).const_mul _
        · refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_)
            (mul_nonneg (potW38_nonneg φ s) (norm_nonneg N))
          have : 0 ≤ |z.im| := abs_nonneg _
          nlinarith [hs.1, hs.2, ht.2]
    _ = Real.exp |z.im| * ‖N‖ * ∫ s in (0 : ℝ)..t, potW38 φ s := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]; ring
    _ ≤ Real.exp |z.im| * ‖N‖ * ∫ s in (0 : ℝ)..1, potW38 φ s := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
          (Filter.Eventually.of_forall fun s => potW38_nonneg φ s) (intervalIntegrable_potW38 φ)
    _ = _ := by rw [potL1Norm38_eq_integral]; ring

/-! ### The bounded operator -/

/-- The Volterra operator on `PairCont38 = C([0,1], M₂(ℂ))` (sup norm). -/
def volterraP (φ : PotPair) (z : ℂ) : PairCont38 →L[ℂ] PairCont38 :=
  LinearMap.mkContinuous
    { toFun := volterraMap φ z
      map_add' := volterraMap_add φ z
      map_smul' := fun c N => by simpa using volterraMap_smul φ z c N }
    (Real.exp |z.im| * potL1Norm38 φ) fun N => by
      have hC : 0 ≤ Real.exp |z.im| * potL1Norm38 φ * ‖N‖ := by
        have := potL1Norm38_nonneg φ
        positivity
      refine ((ContinuousMap.norm_le _ hC).2 fun t => ?_)
      refine (pi_norm_le_iff_of_nonneg hC).2 fun i => (pi_norm_le_iff_of_nonneg hC).2 fun j => ?_
      exact norm_volterraFun_entry_le_const φ z N t.2 i j

theorem volterraP_apply (φ : PotPair) (z : ℂ) (N : PairCont38) (t : Set.Icc (0 : ℝ) 1)
    (i j : Fin 2) : volterraP φ z N t i j = volterraFun φ z N t i j := rfl

theorem norm_volterraP_le (φ : PotPair) (z : ℂ) :
    ‖volterraP φ z‖ ≤ Real.exp |z.im| * potL1Norm38 φ :=
  LinearMap.mkContinuous_norm_le _ (by have := potL1Norm38_nonneg φ; positivity) _

end

end NlsGge.GK38

import NlsGge.GK38.PairAnalytic

/-!
# F3 (part c): `det M = 1` (book Lemma 1.5 and Proposition 1.6)

Source: Grébert-Kappeler book, Chapter I, section 1 (Lemma 1.5, Proposition 1.6).

Write `M(t) = E_z(t) Q(t)`, `Q_{ij}(t) = δ_{ij} + ∫₀ᵗ g_{ij}`, `g = E_z(-s) Φ̃(s) M(s)`.  Since `Φ̃` is
off-diagonal, `g₀₀ = a Q₁₀`, `g₀₁ = a Q₁₁`, `g₁₀ = b Q₀₀`, `g₁₁ = b Q₀₁` (`a = E₀₀(-s)Φ̃₀₁E₁₁(s)`,
`b = E₁₁(-s)Φ̃₁₀E₀₀(s)`), so the absolutely continuous function `det Q` has a.e. derivative `0`
(the book's `i∂ₜ[g,h] = (μ-ν)(g₁h₂+g₂h₁)` at `μ = ν`).  `det E = 1`.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.GK38

noncomputable section

theorem absolutelyContinuousOnInterval_const38 (c : ℂ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
  (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval

/-- The primitive of an interval integrable complex function is absolutely continuous (Mathlib has
the real-valued statement; complex values follow from real and imaginary parts). -/
theorem ac_primitive38 {g : ℝ → ℂ} {a b c : ℝ} (hg : IntervalIntegrable g volume a b)
    (hc : c ∈ Set.uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ r in c..x, g r) a b := by
  have hre : IntervalIntegrable (fun r => (g r).re) volume a b :=
    intervalIntegrable_iff.2 ((intervalIntegrable_iff.1 hg).re)
  have him : IntervalIntegrable (fun r => (g r).im) volume a b :=
    intervalIntegrable_iff.2 ((intervalIntegrable_iff.1 hg).im)
  have h1 := (Complex.isometry_ofReal.lipschitzWith.comp_absolutelyContinuousOnInterval
    (hre.absolutelyContinuousOnInterval_intervalIntegral hc))
  have h2 := (Complex.isometry_ofReal.lipschitzWith.comp_absolutelyContinuousOnInterval
    (him.absolutelyContinuousOnInterval_intervalIntegral hc))
  have h3 := h1.add (h2.const_smul Complex.I)
  refine h3.congr fun x hx => ?_
  have hint : IntervalIntegrable g volume c x := hg.mono_set (Set.uIcc_subset_uIcc hc hx)
  have e1 := Complex.reCLM.intervalIntegral_comp_comm hint
  have e2 := Complex.imCLM.intervalIntegral_comp_comm hint
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at e1 e2
  simp only [Function.comp_apply, Pi.add_apply, smul_eq_mul]
  rw [e1, e2]
  apply Complex.ext <;> simp

/-- Abstract Liouville step: a `2 × 2` matrix of primitives `Q' = Ψ Q` with off-diagonal `Ψ` has
`det Q(1) = 1` (absolute continuity and a vanishing a.e. derivative). -/
theorem det_primitive_eq_one {a b g00 g01 g10 g11 : ℝ → ℂ}
    (i00 : IntervalIntegrable g00 volume 0 1) (i01 : IntervalIntegrable g01 volume 0 1)
    (i10 : IntervalIntegrable g10 volume 0 1) (i11 : IntervalIntegrable g11 volume 0 1)
    (h00 : ∀ s ∈ Set.Icc (0 : ℝ) 1, g00 s = a s * ∫ r in (0 : ℝ)..s, g10 r)
    (h01 : ∀ s ∈ Set.Icc (0 : ℝ) 1, g01 s = a s * (1 + ∫ r in (0 : ℝ)..s, g11 r))
    (h10 : ∀ s ∈ Set.Icc (0 : ℝ) 1, g10 s = b s * (1 + ∫ r in (0 : ℝ)..s, g00 r))
    (h11 : ∀ s ∈ Set.Icc (0 : ℝ) 1, g11 s = b s * ∫ r in (0 : ℝ)..s, g01 r) :
    (1 + ∫ r in (0 : ℝ)..1, g00 r) * (1 + ∫ r in (0 : ℝ)..1, g11 r) -
      (∫ r in (0 : ℝ)..1, g01 r) * (∫ r in (0 : ℝ)..1, g10 r) = 1 := by
  set q00 : ℝ → ℂ := fun s => 1 + ∫ r in (0 : ℝ)..s, g00 r with hq00
  set q11 : ℝ → ℂ := fun s => 1 + ∫ r in (0 : ℝ)..s, g11 r with hq11
  set q01 : ℝ → ℂ := fun s => ∫ r in (0 : ℝ)..s, g01 r with hq01
  set q10 : ℝ → ℂ := fun s => ∫ r in (0 : ℝ)..s, g10 r with hq10
  have h0 : (0 : ℝ) ∈ Set.uIcc 0 1 := Set.left_mem_uIcc
  have ac01 := ac_primitive38 i01 h0
  have ac10 := ac_primitive38 i10 h0
  have ac00 : AbsolutelyContinuousOnInterval q00 0 1 :=
    (absolutelyContinuousOnInterval_const38 1 0 1).add (ac_primitive38 i00 h0)
  have ac11 : AbsolutelyContinuousOnInterval q11 0 1 :=
    (absolutelyContinuousOnInterval_const38 1 0 1).add (ac_primitive38 i11 h0)
  set D : ℝ → ℂ := fun s => q00 s * q11 s - q01 s * q10 s with hD
  have acD : AbsolutelyContinuousOnInterval D 0 1 := (ac00.smul ac11).sub (ac01.smul ac10)
  have hderiv : ∀ᵐ x : ℝ, x ∈ Set.uIcc (0 : ℝ) 1 → HasDerivAt D 0 x := by
    filter_upwards [i00.ae_hasDerivAt_integral, i01.ae_hasDerivAt_integral,
      i10.ae_hasDerivAt_integral, i11.ae_hasDerivAt_integral] with x d00 d01 d10 d11 hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by rwa [Set.uIcc_of_le zero_le_one] at hx
    have e00 : HasDerivAt q00 (g00 x) x := (d00 hx 0 h0).const_add 1
    have e11 : HasDerivAt q11 (g11 x) x := (d11 hx 0 h0).const_add 1
    have e01 : HasDerivAt q01 (g01 x) x := d01 hx 0 h0
    have e10 : HasDerivAt q10 (g10 x) x := d10 hx 0 h0
    have := (e00.mul e11).sub (e01.mul e10)
    convert this using 1
    rw [h00 x hx', h01 x hx', h10 x hx', h11 x hx']
    ring
  obtain ⟨C, hC⟩ := acD.const_of_ae_hasDerivAt_zero hderiv
  have hD0 : D 0 = 1 := by simp [hD, hq00, hq11, hq01, hq10]
  have hD1 : D 1 = C := hC 1 Set.right_mem_uIcc
  have hD0' : D 0 = C := hC 0 h0
  have hD1' : D 1 = 1 := hD1.trans (hD0'.symm.trans hD0)
  exact hD1'

/-! ### Application to the fundamental solution -/

/-- The integrand `g_{ij}(s) = (E_z(-s) Φ̃(s) M(s))_{ij}` of the kernel integral. -/
def detKer38 (φ : PotPair) (z : ℂ) (i j : Fin 2) (s : ℝ) : ℂ :=
  (freeE z (-s) * potCoeff38 φ s * ext38 (fundContP φ z) s) i j

theorem intervalIntegrable_detKer38 (φ : PotPair) (z : ℂ) (i j : Fin 2) :
    IntervalIntegrable (detKer38 φ z i j) volume 0 1 :=
  intervalIntegrable_triple_entry φ ((continuous_freeE z).comp continuous_neg)
    (continuous_ext38 _) i j

/-- `M(t)_{ij} = E_z(t)_{ii} (δ_{ij} + ∫₀ᵗ g_{ij})`. -/
theorem fundContP_entry_eq (φ : PotPair) (z : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (i j : Fin 2) :
    fundContP φ z ⟨t, ht⟩ i j =
      freeE z t i i * ((if i = j then (1 : ℂ) else 0) + ∫ s in (0 : ℝ)..t, detKer38 φ z i j s) := by
  have h := congrArg (fun F => F ⟨t, ht⟩ i j) (fundCont_eq_add φ z)
  simp only [ContinuousMap.add_apply, Pi.add_apply] at h
  rw [h, volterraP_apply, volterraFun_eq, freeE_mul_apply]
  show freeE z t i j + freeE z t i i * volterraKer φ z (fundContP φ z) t i j = _
  have : freeE z t i j = freeE z t i i * (if i = j then (1 : ℂ) else 0) := by
    fin_cases i <;> fin_cases j <;> simp [freeE]
  rw [this, mul_add]
  rfl

theorem detKer38_zero_row (φ : PotPair) (z : ℂ) (j : Fin 2) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    detKer38 φ z 0 j s =
      (freeE z (-s) 0 0 * (Complex.I * potRepFst38 φ s) * freeE z s 1 1) *
        ((if (1 : Fin 2) = j then (1 : ℂ) else 0) + ∫ r in (0 : ℝ)..s, detKer38 φ z 1 j r) := by
  have hM := fundContP_entry_eq φ z hs 1 j
  have : detKer38 φ z 0 j s = freeE z (-s) 0 0 * (Complex.I * potRepFst38 φ s) *
      ext38 (fundContP φ z) s 1 j := by
    unfold detKer38
    rw [mul_assoc, freeE_mul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    simp [potCoeff38]
    ring
  rw [this, ext38_of_mem _ hs]
  show _ * (fundContP φ z ⟨s, hs⟩ 1 j) = _
  rw [hM]; ring

theorem detKer38_one_row (φ : PotPair) (z : ℂ) (j : Fin 2) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    detKer38 φ z 1 j s =
      (freeE z (-s) 1 1 * (-(Complex.I * potRepSnd38 φ s)) * freeE z s 0 0) *
        ((if (0 : Fin 2) = j then (1 : ℂ) else 0) + ∫ r in (0 : ℝ)..s, detKer38 φ z 0 j r) := by
  have hM := fundContP_entry_eq φ z hs 0 j
  have : detKer38 φ z 1 j s = freeE z (-s) 1 1 * (-(Complex.I * potRepSnd38 φ s)) *
      ext38 (fundContP φ z) s 0 j := by
    unfold detKer38
    rw [mul_assoc, freeE_mul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    simp [potCoeff38]
    ring
  rw [this, ext38_of_mem _ hs]
  show _ * (fundContP φ z ⟨s, hs⟩ 0 j) = _
  rw [hM]; ring

theorem freeE_diag_prod (z : ℂ) (t : ℝ) : freeE z t 0 0 * freeE z t 1 1 = 1 := by
  simp [freeE, ← Complex.exp_add]

/-- F3, Proposition 1.6: `det M(1, z, φ) = 1` (book Lemma 1.5 with `μ = ν`). -/
theorem det_monodromyPair (φ : PotPair) (z : ℂ) : (monodromyPair φ z).det = 1 := by
  have key := det_primitive_eq_one
    (a := fun s => freeE z (-s) 0 0 * (Complex.I * potRepFst38 φ s) * freeE z s 1 1)
    (b := fun s => freeE z (-s) 1 1 * (-(Complex.I * potRepSnd38 φ s)) * freeE z s 0 0)
    (intervalIntegrable_detKer38 φ z 0 0) (intervalIntegrable_detKer38 φ z 0 1)
    (intervalIntegrable_detKer38 φ z 1 0) (intervalIntegrable_detKer38 φ z 1 1)
    (fun s hs => by simpa using detKer38_zero_row φ z 0 hs)
    (fun s hs => by simpa using detKer38_zero_row φ z 1 hs)
    (fun s hs => by simpa using detKer38_one_row φ z 0 hs)
    (fun s hs => by simpa using detKer38_one_row φ z 1 hs)
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have e : ∀ i j, monodromyPair φ z i j = fundContP φ z ⟨1, h1⟩ i j := fun i j => rfl
  rw [Matrix.det_fin_two, e, e, e, e, fundContP_entry_eq φ z h1, fundContP_entry_eq φ z h1,
    fundContP_entry_eq φ z h1, fundContP_entry_eq φ z h1]
  have h2 := freeE_diag_prod z 1
  simp only [ite_true, show ¬ ((0 : Fin 2) = 1) from by decide, show ¬ ((1 : Fin 2) = 0) from by decide, ite_false]
  linear_combination (freeE z 1 0 0 * freeE z 1 1 1) * key + h2

end

end NlsGge.GK38

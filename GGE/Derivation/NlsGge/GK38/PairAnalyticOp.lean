import NlsGge.GK38.PairVolterra
import NlsGge.GK38.Lib.WeaklyAnalytic

/-!
# F3 (part a): analytic dependence of the Volterra operator on `(φ, z)`

Source: Grébert-Kappeler book, Chapter I, section 1 (equation `(1.2)`, Theorem 1.1 and its
analyticity statement).

The operator `𝒱_{φ,z} N (t) = ∫₀ᵗ E_z(t-s) Φ̃_φ(s) N(s) ds` of F2 (`volterraP`, at `PairCont38`)
factors as
`𝒱_{φ,z} = 𝓜_z ∘ 𝒱_{φ,0} ∘ 𝓜_z`,
where `𝓜_z N (t) = E_z(t) N(t)` is the left multiplication by the free solution.  The point is the
matrix identity `E_z(-s) Φ̃(s) = Φ̃(s) E_z(s)` (`Φ̃` is off-diagonal).  Hence

* `φ ↦ 𝒱_{φ,0}` is a bounded linear map `PotPair →L[ℂ] (PairCont38 →L[ℂ] PairCont38)` (F2:
  `volterraP_sub`, `volterraP_smul_potential`, `norm_volterraP_le`), and
* `z ↦ 𝓜_z` is entire as an `L(PairCont38)`-valued map, since `E_z(t)_{ii} = exp(z ∙ g_i)(t)` is the
  exponential of `z g_i` in the Banach algebra `C([0,1], ℂ)`.

So `(φ, z) ↦ 𝒱_{φ,z}` is a product of analytic maps in the Banach algebra `L(PairCont38)`.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.GK38

noncomputable section

/-! ### Left multiplication by a diagonal of scalar functions -/

/-- Continuous scalar functions on `[0,1]` (a commutative Banach algebra). -/
abbrev Scal38 : Type := C(Set.Icc (0 : ℝ) 1, ℂ)

/-- `(mulRowFun i a N)(t)_{i'j} = δ_{i'i} a(t) N(t)_{i'j}`: multiplication of row `i` of `N` by `a`. -/
def mulRowFun (i : Fin 2) (a : Scal38) (N : PairCont38) : PairCont38 where
  toFun t := fun i' j => if i' = i then a t * N t i' j else 0
  continuous_toFun := by
    refine continuous_pi fun i' => continuous_pi fun j => ?_
    by_cases h : i' = i
    · simp only [h, ite_true]
      exact a.continuous.mul ((continuous_apply j).comp ((continuous_apply i).comp N.continuous))
    · simp only [h, ite_false]; exact continuous_const

@[simp] theorem mulRowFun_apply (i : Fin 2) (a : Scal38) (N : PairCont38) (t : Set.Icc (0 : ℝ) 1)
    (i' j : Fin 2) : mulRowFun i a N t i' j = if i' = i then a t * N t i' j else 0 := rfl

theorem norm_mulRowFun_le (i : Fin 2) (a : Scal38) (N : PairCont38) :
    ‖mulRowFun i a N‖ ≤ ‖a‖ * ‖N‖ := by
  have hC : 0 ≤ ‖a‖ * ‖N‖ := by positivity
  refine (ContinuousMap.norm_le _ hC).2 fun t => ?_
  refine (pi_norm_le_iff_of_nonneg hC).2 fun i' => (pi_norm_le_iff_of_nonneg hC).2 fun j => ?_
  rw [mulRowFun_apply]
  split_ifs
  · rw [norm_mul]
    refine mul_le_mul (a.norm_coe_le_norm t) ?_ (norm_nonneg _) (norm_nonneg _)
    exact (norm_le_pi_norm (N t i') j).trans
      ((norm_le_pi_norm (N t) i').trans (N.norm_coe_le_norm t))
  · simpa using hC

/-- `a ↦ (N ↦ row `i` of `N` multiplied by `a`)` as a bounded bilinear map. -/
def mulRowL (i : Fin 2) : Scal38 →L[ℂ] PairCont38 →L[ℂ] PairCont38 :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (mulRowFun i)
      (fun a b N => by
        ext t i' j; by_cases h : i' = i <;> simp [h, add_mul])
      (fun c a N => by
        ext t i' j; by_cases h : i' = i <;> simp [h, mul_assoc])
      (fun a N M => by
        ext t i' j; by_cases h : i' = i <;> simp [h, mul_add])
      (fun c a N => by
        ext t i' j; by_cases h : i' = i
        · simp [h]; ring
        · simp [h]))
    1 (fun a N => by simpa using norm_mulRowFun_le i a N)

@[simp] theorem mulRowL_apply (i : Fin 2) (a : Scal38) (N : PairCont38) :
    mulRowL i a N = mulRowFun i a N := rfl

theorem analyticAt_mulRowL (i : Fin 2) (a : Scal38) :
    AnalyticAt ℂ (fun a : Scal38 => mulRowL i a) a :=
  ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := Scal38) (F := PairCont38 →L[ℂ] PairCont38)
    (mulRowL i) a

/-! ### The free solution as an exponential in `C([0,1], ℂ)` -/

/-- `sgn 0 = -1`, `sgn 1 = 1`: `E_z(t) = diag(e^{sgn₀ i z t}, e^{sgn₁ i z t})`. -/
def sgn38 (i : Fin 2) : ℂ := if i = 0 then -1 else 1

/-- The generator `g_i(t) = sgn_i · i · t` in `C([0,1], ℂ)`. -/
def gen38 (i : Fin 2) : Scal38 :=
  ⟨fun t => sgn38 i * Complex.I * (t : ℝ), by unfold sgn38; fun_prop⟩

/-- `E_z(t)_{ii} = exp(z g_i(t))`, as the exponential `exp(z • g_i)` in the Banach algebra. -/
def expGen38 (z : ℂ) (i : Fin 2) : Scal38 := NormedSpace.exp (z • gen38 i)
theorem expGen38_apply (z : ℂ) (i : Fin 2) (t : Set.Icc (0 : ℝ) 1) :
    expGen38 z i t = Complex.exp (z * (sgn38 i * Complex.I * (t : ℝ))) := by
  unfold expGen38
  have h := NormedSpace.map_exp (𝔸 := Scal38) (𝔹 := ℂ) (ContinuousMap.evalAlgHom ℂ ℂ t)
    (AddMonoidHomClass.continuous_of_bound _ 1 fun g => by
      simpa using g.norm_coe_le_norm t) (z • gen38 i)
  simp only [ContinuousMap.evalAlgHom_apply] at h
  rw [h, ← Complex.exp_eq_exp_ℂ]
  simp [gen38]

theorem freeE_diag (z : ℂ) (t : ℝ) (i : Fin 2) :
    freeE z t i i = Complex.exp (z * (sgn38 i * Complex.I * t)) := by
  fin_cases i <;> simp [freeE, sgn38] <;> ring_nf

theorem expGen38_eq_freeE (z : ℂ) (i : Fin 2) (t : Set.Icc (0 : ℝ) 1) :
    expGen38 z i t = freeE z t i i := by
  rw [expGen38_apply, freeE_diag]

theorem analyticOnNhd_expGen38 (i : Fin 2) : AnalyticOnNhd ℂ (fun z => expGen38 z i) Set.univ := by
  intro z _
  have h1 : AnalyticAt ℂ (fun w : ℂ => w • gen38 i) z :=
    ((ContinuousLinearMap.id ℂ ℂ).smulRight (gen38 i)).analyticAt z
  exact (NormedSpace.exp_analytic (𝕂 := ℂ) _).comp h1

/-- `𝓜_z N = diag(E_z) N`, left multiplication by the free solution. -/
def mulFree38 (z : ℂ) : PairCont38 →L[ℂ] PairCont38 :=
  mulRowL 0 (expGen38 z 0) + mulRowL 1 (expGen38 z 1)

/-- `z ↦ 𝓜_z` is entire. -/
theorem analyticOnNhd_mulFree38 : AnalyticOnNhd ℂ mulFree38 Set.univ := fun z hz =>
  ((analyticAt_mulRowL 0 _).comp (analyticOnNhd_expGen38 0 z hz)).add
    ((analyticAt_mulRowL 1 _).comp (analyticOnNhd_expGen38 1 z hz))

theorem mulFree38_apply (z : ℂ) (N : PairCont38) (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    mulFree38 z N t i j = freeE z t i i * N t i j := by
  fin_cases i <;> simp [mulFree38, expGen38_eq_freeE]

theorem ext38_mulFree38 (z : ℂ) (N : PairCont38) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ext38 (mulFree38 z N) s = freeE z s * ext38 N s := by
  ext i j
  rw [freeE_mul_apply, ext38_of_mem _ hs, ext38_of_mem _ hs]
  exact mulFree38_apply z N ⟨s, hs⟩ i j

/-! ### `E_z(-s) Φ̃(s) = Φ̃(s) E_z(s)` and the factorization `𝒱_{φ,z} = 𝓜_z 𝒱_{φ,0} 𝓜_z` -/

theorem freeE_neg_mul_potCoeff38 (z : ℂ) (φ : PotPair) (s : ℝ) :
    freeE z (-s) * potCoeff38 φ s = potCoeff38 φ s * freeE z s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [freeE, potCoeff38, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem freeE_zero_potential (r : ℝ) : freeE 0 r = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [freeE]

theorem volterraFun_factor (φ : PotPair) (z : ℂ) (N : PairCont38) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    volterraFun φ z N t i j =
      freeE z t i i * volterraFun φ 0 (mulFree38 z N) t i j := by
  simp only [volterraFun_apply, freeE_zero_potential, one_mul]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s hs => ?_
  have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le ht.1] at hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  show (freeE z (t - s) * potCoeff38 φ s * ext38 N s) i j =
    freeE z t i i * (potCoeff38 φ s * ext38 (mulFree38 z N) s) i j
  rw [ext38_mulFree38 z N hs', ← freeE_mul_apply, sub_eq_add_neg, freeE_add, mul_assoc,
    mul_assoc, ← mul_assoc (freeE z (-s)), freeE_neg_mul_potCoeff38, mul_assoc (potCoeff38 φ s)]

/-- `𝒱_{φ,z} = 𝓜_z ∘ 𝒱_{φ,0} ∘ 𝓜_z` (book `(1.2)`, with `E_z(-s)Φ̃ = Φ̃E_z(s)`). -/
theorem volterraP_eq_mul (φ : PotPair) (z : ℂ) :
    volterraP φ z = mulFree38 z * volterraP φ 0 * mulFree38 z := by
  ext N t i j
  rw [volterraP_apply, mul_apply_eq_comp, mul_apply_eq_comp,
    mulFree38_apply, volterraP_apply]
  exact volterraFun_factor φ z N t.2 i j

/-! ### `φ ↦ 𝒱_{φ,0}` is a bounded linear map -/

theorem volterraP_add (φ ψ : PotPair) (z : ℂ) :
    volterraP (φ + ψ) z = volterraP φ z + volterraP ψ z := by
  have h : φ + ψ = φ - (-1 : ℂ) • ψ := by simp [sub_eq_add_neg]
  have e : (-1 : ℂ) • volterraP ψ z = -volterraP ψ z := by ext N t i j; simp
  rw [h, volterraP_sub, volterraP_smul_potential, e]
  ext N t i j; simp

/-- `φ ↦ 𝒱_{φ,0}`, `(𝒱_{φ,0}N)(t) = ∫₀ᵗ Φ̃_φ(s) N(s) ds`. -/
def volterraZeroL : PotPair →L[ℂ] (PairCont38 →L[ℂ] PairCont38) :=
  LinearMap.mkContinuous
    { toFun := fun φ => volterraP φ 0
      map_add' := fun φ ψ => volterraP_add φ ψ 0
      map_smul' := fun c φ => by
        show volterraP (c • φ) 0 = c • volterraP φ 0
        exact volterraP_smul_potential c φ 0 }
    2 fun φ => by
      refine (norm_volterraP_le φ 0).trans ?_
      simpa using (potL1Norm38_le_two_mul φ)

@[simp] theorem volterraZeroL_apply (φ : PotPair) : volterraZeroL φ = volterraP φ 0 := rfl

theorem analyticAt_volterraZeroL (φ : PotPair) :
    AnalyticAt ℂ (fun φ : PotPair => volterraZeroL φ) φ :=
  ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := PotPair) (F := PairCont38 →L[ℂ] PairCont38)
    volterraZeroL φ

/-- Products of analytic `L(PairCont38)`-valued maps are analytic (the Banach algebra `L(X)`;
stated with `comp₂` of `analyticAt_mul` to keep the instances aligned). -/
theorem analyticAt_mul_op38 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : E → PairCont38 →L[ℂ] PairCont38} {p : E} (hf : AnalyticAt ℂ f p)
    (hg : AnalyticAt ℂ g p) : AnalyticAt ℂ (fun x => f x * g x) p :=
  (analyticAt_mul (𝕜 := ℂ) (A := PairCont38 →L[ℂ] PairCont38) (f p, g p)).comp₂ hf hg

/-- The Volterra operator is jointly analytic in `(φ, z)` (book Thm 1.1, analyticity), as an
`L(PairCont38)`-valued map. -/
theorem analyticOnNhd_volterraP :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => volterraP p.1 p.2) Set.univ := by
  intro p _
  have hz : AnalyticAt ℂ (fun p : PotPair × ℂ => mulFree38 p.2) p :=
    (analyticOnNhd_mulFree38 p.2 (Set.mem_univ _)).comp analyticAt_snd
  have hφ : AnalyticAt ℂ (fun p : PotPair × ℂ => volterraZeroL p.1) p :=
    (analyticAt_volterraZeroL p.1).comp analyticAt_fst
  have := analyticAt_mul_op38 (analyticAt_mul_op38 hz hφ) hz
  refine this.congr (Filter.Eventually.of_forall fun q => ?_)
  exact (volterraP_eq_mul q.1 q.2).symm

end

end NlsGge.GK38

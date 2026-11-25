import QuantumNLS.CountFunctionsS01Calc

/-!
# CountFunctionsS01Poisson: the classical Poisson bracket `{F,G}` of functions on `ℂ^J` and its Leibniz rules

PRINTED SOURCES
* `source-text/chapters/core/wick_calculus.tex:67-70` (bracket convention): "With the bracket convention in
  `eq:birkhoff`, `C_1(f,g) = S_1(f,g) + i{f,g}/2`", `C_1(f,g) = Σ_a ∂_{z_a}f ∂_{z̄_a}g`, i.e.
  `{f,g} = -i Σ_a (∂_{z_a}f ∂_{z̄_a}g - ∂_{z̄_a}f ∂_{z_a}g)`.
* `source-text/chapters/core/canonical_algebra.tex:23-27, 30`: "`{a_j,c_ab} = i(δ_ja-δ_jb)c_ab`,
  `{c_ab,c_cd} = i(δ_bc c_ad - δ_ad c_cb)`, `{c_ab, conj c_ab} = i(a_a - a_b)`" (the Leibniz rule and the bracket
  convention); "Thus the prefactor in (eq:dirac-main) is `N/i`".

`poisson F G z` is that bracket for `F G : ℂ^J → ℂ` real-differentiable at `z`, with Wirtinger derivatives defined
from the real Fréchet derivative (`wz F z j = (∂_x - i ∂_y)/2`, `wzb F z j = (∂_x + i ∂_y)/2`).  Proved here: the
bilinearity and Leibniz rules, antisymmetry, and the values on the generators `c_ab = z_a z̄_b` and on the count
functions `f(a_J)`, `a_j = |z_j|²` (for `f` differentiable at `a_J`), which reproduce the printed table.
No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open scoped InnerProductSpace ComplexConjugate

open QuantumNLS.CountFunctionsS01Ops

namespace QuantumNLS.CountFunctionsS01Poisson

variable {J : Finset ℤ}

/-- The coordinate space `ℂ^J`. -/
abbrev CPt (J : Finset ℤ) := ↥J → ℂ

/-- Wirtinger derivative `∂/∂z_j`. -/
def wz (F : CPt J → ℂ) (z : CPt J) (j : ↥J) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ F z (Pi.single j (1 : ℂ)) - Complex.I * fderiv ℝ F z (Pi.single j Complex.I))

/-- Wirtinger derivative `∂/∂z̄_j`. -/
def wzb (F : CPt J → ℂ) (z : CPt J) (j : ↥J) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ F z (Pi.single j (1 : ℂ)) + Complex.I * fderiv ℝ F z (Pi.single j Complex.I))

/-- The Poisson bracket `{F,G} = -i Σ_j (∂_{z_j}F ∂_{z̄_j}G - ∂_{z̄_j}F ∂_{z_j}G)`. -/
def poisson (F G : CPt J → ℂ) (z : CPt J) : ℂ :=
  -Complex.I * ∑ j : ↥J, (wz F z j * wzb G z j - wzb F z j * wz G z j)

/-! ### Rules -/

section Rules

variable {F G : CPt J → ℂ} {z : CPt J}

lemma fderiv_mul_apply (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) (v : CPt J) :
    fderiv ℝ (fun y => F y * G y) z v = F z * fderiv ℝ G z v + G z * fderiv ℝ F z v := by
  rw [fderiv_fun_mul hF hG]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

lemma fderiv_add_apply (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) (v : CPt J) :
    fderiv ℝ (fun y => F y + G y) z v = fderiv ℝ F z v + fderiv ℝ G z v := by
  rw [fderiv_fun_add hF hG]
  simp only [ContinuousLinearMap.add_apply]

lemma fderiv_const_mul_apply (hF : DifferentiableAt ℝ F z) (c : ℂ) (v : CPt J) :
    fderiv ℝ (fun y => c * F y) z v = c * fderiv ℝ F z v := by
  rw [fderiv_const_mul hF c]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

lemma wz_mul (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) (j : ↥J) :
    wz (fun y => F y * G y) z j = F z * wz G z j + G z * wz F z j := by
  unfold wz
  rw [fderiv_mul_apply hF hG, fderiv_mul_apply hF hG]
  ring

lemma wzb_mul (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) (j : ↥J) :
    wzb (fun y => F y * G y) z j = F z * wzb G z j + G z * wzb F z j := by
  unfold wzb
  rw [fderiv_mul_apply hF hG, fderiv_mul_apply hF hG]
  ring

lemma wz_add (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) (j : ↥J) :
    wz (fun y => F y + G y) z j = wz F z j + wz G z j := by
  unfold wz
  rw [fderiv_add_apply hF hG, fderiv_add_apply hF hG]
  ring

lemma wzb_add (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) (j : ↥J) :
    wzb (fun y => F y + G y) z j = wzb F z j + wzb G z j := by
  unfold wzb
  rw [fderiv_add_apply hF hG, fderiv_add_apply hF hG]
  ring

lemma wz_const_mul (hF : DifferentiableAt ℝ F z) (c : ℂ) (j : ↥J) :
    wz (fun y => c * F y) z j = c * wz F z j := by
  unfold wz
  rw [fderiv_const_mul_apply hF, fderiv_const_mul_apply hF]
  ring

lemma wzb_const_mul (hF : DifferentiableAt ℝ F z) (c : ℂ) (j : ↥J) :
    wzb (fun y => c * F y) z j = c * wzb F z j := by
  unfold wzb
  rw [fderiv_const_mul_apply hF, fderiv_const_mul_apply hF]
  ring

/-- Leibniz rule in the first slot. -/
theorem poisson_mul_left (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) (H : CPt J → ℂ) :
    poisson (fun y => F y * G y) H z = F z * poisson G H z + G z * poisson F H z := by
  unfold poisson
  simp only [wz_mul hF hG, wzb_mul hF hG]
  have h : ∀ j : ↥J, (F z * wz G z j + G z * wz F z j) * wzb H z j -
      (F z * wzb G z j + G z * wzb F z j) * wz H z j =
      F z * (wz G z j * wzb H z j - wzb G z j * wz H z j) +
        G z * (wz F z j * wzb H z j - wzb F z j * wz H z j) := fun j => by ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem poisson_add_left (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) (H : CPt J → ℂ) :
    poisson (fun y => F y + G y) H z = poisson F H z + poisson G H z := by
  unfold poisson
  simp only [wz_add hF hG, wzb_add hF hG]
  have h : ∀ j : ↥J, (wz F z j + wz G z j) * wzb H z j - (wzb F z j + wzb G z j) * wz H z j =
      (wz F z j * wzb H z j - wzb F z j * wz H z j) + (wz G z j * wzb H z j - wzb G z j * wz H z j) :=
    fun j => by ring
  simp only [h, Finset.sum_add_distrib]
  ring

theorem poisson_const_mul_left (hF : DifferentiableAt ℝ F z) (c : ℂ) (H : CPt J → ℂ) :
    poisson (fun y => c * F y) H z = c * poisson F H z := by
  unfold poisson
  simp only [wz_const_mul hF c, wzb_const_mul hF c]
  have h : ∀ j : ↥J, c * wz F z j * wzb H z j - c * wzb F z j * wz H z j =
      c * (wz F z j * wzb H z j - wzb F z j * wz H z j) := fun j => by ring
  simp only [h, ← Finset.mul_sum]
  ring

theorem poisson_antisymm (F G : CPt J → ℂ) (z : CPt J) : poisson F G z = - poisson G F z := by
  unfold poisson
  have h : ∀ j : ↥J, wz F z j * wzb G z j - wzb F z j * wz G z j =
      -(wz G z j * wzb F z j - wzb G z j * wz F z j) := fun j => by ring
  simp only [h, Finset.sum_neg_distrib]
  ring

end Rules


/-! ### The generators `c_ab = z_a z̄_b` -/

section Generators

variable {J : Finset ℤ}

/-- The classical generator `c_ab(z) = z_a conj(z_b)`. -/
def genF (a b : ↥J) : CPt J → ℂ := fun z => z a * conj (z b)

lemma hasFDerivAt_genF (a b : ↥J) (z : CPt J) :
    HasFDerivAt (genF a b)
      ((z a) • ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj b : CPt J →L[ℝ] ℂ)) +
        (conj (z b)) • (ContinuousLinearMap.proj a : CPt J →L[ℝ] ℂ)) z := by
  have h1 : HasFDerivAt (fun y : CPt J => y a) (ContinuousLinearMap.proj a : CPt J →L[ℝ] ℂ) z :=
    (ContinuousLinearMap.proj a : CPt J →L[ℝ] ℂ).hasFDerivAt
  have h2 : HasFDerivAt (fun y : CPt J => conj (y b))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj b : CPt J →L[ℝ] ℂ)) z :=
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj b : CPt J →L[ℝ] ℂ)).hasFDerivAt
  exact h1.mul h2

lemma fderiv_genF_apply (a b : ↥J) (z v : CPt J) :
    fderiv ℝ (genF a b) z v = z a * conj (v b) + conj (z b) * v a := by
  rw [(hasFDerivAt_genF a b z).fderiv]
  simp

lemma differentiableAt_genF (a b : ↥J) (z : CPt J) : DifferentiableAt ℝ (genF a b) z :=
  (hasFDerivAt_genF a b z).differentiableAt

lemma wz_genF (a b : ↥J) (z : CPt J) (j : ↥J) :
    wz (genF a b) z j = if a = j then conj (z b) else 0 := by
  unfold wz
  rw [fderiv_genF_apply, fderiv_genF_apply]
  by_cases ha : a = j <;> by_cases hb : b = j <;>
    simp [ha, hb, eq_comm] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

lemma wzb_genF (a b : ↥J) (z : CPt J) (j : ↥J) :
    wzb (genF a b) z j = if b = j then z a else 0 := by
  unfold wzb
  rw [fderiv_genF_apply, fderiv_genF_apply]
  by_cases ha : a = j <;> by_cases hb : b = j <;>
    simp [ha, hb, eq_comm] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

lemma sum_ite_ite (a d : ↥J) (x y : ℂ) :
    ∑ j : ↥J, (if a = j then x else 0) * (if d = j then y else 0) = if a = d then x * y else 0 := by
  by_cases h : a = d
  · subst h
    simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases haj : a = j
    · have : d ≠ j := fun hdj => h (haj.trans hdj.symm)
      simp [this]
    · simp [haj]

/-- **`{c_ab, c_cd} = i(δ_bc c_ad - δ_ad c_cb)`** (`canonical_algebra.tex:26-27`, eq:classical-algebra). -/
theorem poisson_genF_genF (a b c d : ↥J) (z : CPt J) :
    poisson (genF a b) (genF c d) z =
      Complex.I * ((if b = c then genF a d z else 0) - (if a = d then genF c b z else 0)) := by
  unfold poisson
  simp only [wz_genF, wzb_genF]
  have e : ∀ j : ↥J, (if a = j then conj (z b) else 0) * (if d = j then z c else 0) -
      (if b = j then z a else 0) * (if c = j then conj (z d) else 0) =
      (if a = j then conj (z b) else 0) * (if d = j then z c else 0) -
      (if b = j then z a else 0) * (if c = j then conj (z d) else 0) := fun _ => rfl
  rw [Finset.sum_sub_distrib, sum_ite_ite, sum_ite_ite]
  by_cases h1 : a = d <;> by_cases h2 : b = c <;> simp [genF, h1, h2] <;> ring

end Generators


/-! ### The count functions `f(a_J)`, `a_j = |z_j|²` -/

section Counts

variable {J : Finset ℤ}

/-- The classical count point `a_J(z) = (|z_j|²)_{j∈J}`. -/
def apt (z : CPt J) : ↥J → ℝ := fun j => ‖z j‖ ^ 2

/-- The classical count function `z ↦ f(a_J(z))`. -/
def cntF (f : (↥J → ℝ) → ℂ) : CPt J → ℂ := fun z => f (apt z)

/-- The real derivative of `a_J`. -/
def aptCLM (z : CPt J) : CPt J →L[ℝ] (↥J → ℝ) :=
  ContinuousLinearMap.pi fun j => (2 : ℝ) • ((innerSL ℝ (z j)).comp (ContinuousLinearMap.proj j))

lemma hasFDerivAt_apt (z : CPt J) : HasFDerivAt apt (aptCLM z) z := by
  rw [hasFDerivAt_pi']
  intro j
  have h1 := (hasStrictFDerivAt_norm_sq (z j)).hasFDerivAt
  have h2 : HasFDerivAt (fun y : CPt J => y j) (ContinuousLinearMap.proj j : CPt J →L[ℝ] ℂ) z :=
    (ContinuousLinearMap.proj j : CPt J →L[ℝ] ℂ).hasFDerivAt
  have h3 := h1.comp z h2
  have e : (ContinuousLinearMap.proj j : (↥J → ℝ) →L[ℝ] ℝ).comp (aptCLM z) =
      (2 • innerSL ℝ (z j)).comp (ContinuousLinearMap.proj j) := by
    ext v
    simp [aptCLM]
    ring
  rw [e]
  exact h3

lemma hasFDerivAt_cntF {f : (↥J → ℝ) → ℂ} {z : CPt J} (hf : DifferentiableAt ℝ f (apt z)) :
    HasFDerivAt (cntF f) ((fderiv ℝ f (apt z)).comp (aptCLM z)) z :=
  hf.hasFDerivAt.comp z (hasFDerivAt_apt z)

lemma differentiableAt_cntF {f : (↥J → ℝ) → ℂ} {z : CPt J} (hf : DifferentiableAt ℝ f (apt z)) :
    DifferentiableAt ℝ (cntF f) z :=
  (hasFDerivAt_cntF hf).differentiableAt

lemma aptCLM_single_one (z : CPt J) (j : ↥J) :
    aptCLM z (Pi.single j (1 : ℂ)) = Pi.single j (2 * (z j).re) := by
  ext i
  by_cases h : i = j
  · subst h
    simp [aptCLM, Complex.inner, mul_comm]
  · simp [aptCLM, h]

lemma aptCLM_single_I (z : CPt J) (j : ↥J) :
    aptCLM z (Pi.single j Complex.I) = Pi.single j (2 * (z j).im) := by
  ext i
  by_cases h : i = j
  · subst h
    simp [aptCLM, Complex.inner]
  · simp [aptCLM, h]

lemma pi_single_real (j : ↥J) (c : ℝ) : (Pi.single j c : ↥J → ℝ) = c • Pi.single j (1 : ℝ) := by
  ext i
  by_cases h : i = j
  · subst h; simp
  · simp [h]

lemma wz_cntF {f : (↥J → ℝ) → ℂ} {z : CPt J} (hf : DifferentiableAt ℝ f (apt z)) (j : ↥J) :
    wz (cntF f) z j = fderiv ℝ f (apt z) (Pi.single j (1 : ℝ)) * conj (z j) := by
  unfold wz
  rw [(hasFDerivAt_cntF hf).fderiv]
  simp only [ContinuousLinearMap.comp_apply, aptCLM_single_one, aptCLM_single_I]
  rw [pi_single_real j (2 * (z j).re), pi_single_real j (2 * (z j).im), map_smul, map_smul,
    Complex.real_smul, Complex.real_smul]
  have : conj (z j) = ((z j).re : ℂ) - Complex.I * ((z j).im : ℂ) := by
    apply Complex.ext <;> simp
  rw [this]
  push_cast
  ring_nf

lemma wzb_cntF {f : (↥J → ℝ) → ℂ} {z : CPt J} (hf : DifferentiableAt ℝ f (apt z)) (j : ↥J) :
    wzb (cntF f) z j = fderiv ℝ f (apt z) (Pi.single j (1 : ℝ)) * z j := by
  unfold wzb
  rw [(hasFDerivAt_cntF hf).fderiv]
  simp only [ContinuousLinearMap.comp_apply, aptCLM_single_one, aptCLM_single_I]
  rw [pi_single_real j (2 * (z j).re), pi_single_real j (2 * (z j).im), map_smul, map_smul,
    Complex.real_smul, Complex.real_smul]
  have : z j = ((z j).re : ℂ) + Complex.I * ((z j).im : ℂ) := (Complex.re_add_im (z j)).symm.trans (by ring)
  conv_rhs => rw [this]
  push_cast
  ring_nf

/-- `{f(a_J), g(a_J)} = 0`. -/
theorem poisson_cntF_cntF {f g : (↥J → ℝ) → ℂ} {z : CPt J} (hf : DifferentiableAt ℝ f (apt z))
    (hg : DifferentiableAt ℝ g (apt z)) : poisson (cntF f) (cntF g) z = 0 := by
  unfold poisson
  simp only [wz_cntF hf, wz_cntF hg, wzb_cntF hf, wzb_cntF hg]
  rw [Finset.sum_eq_zero, mul_zero]
  intro j _
  ring

lemma pi_single_one_sub (J : Finset ℤ) (a b : ↥J) :
    hvec J a b = Pi.single b (1 : ℝ) - Pi.single a (1 : ℝ) := by
  ext j
  simp only [hvec, Pi.sub_apply, Pi.single_apply]

/-- **`{f(a_J), c_ab} = -i (∂_h f)(a_J) c_ab`**, `h = e_b - e_a` (the bracket of a count function with a generator;
`canonical_algebra.tex:25`: `{a_j, c_ab} = i(δ_ja - δ_jb)c_ab`, Leibniz). -/
theorem poisson_cntF_genF {f : (↥J → ℝ) → ℂ} {z : CPt J} (hf : DifferentiableAt ℝ f (apt z)) (a b : ↥J) :
    poisson (cntF f) (genF a b) z =
      -Complex.I * (fderiv ℝ f (apt z) (hvec J a b) * (z a * conj (z b))) := by
  unfold poisson
  simp only [wz_cntF hf, wzb_genF, wzb_cntF hf, wz_genF]
  have e : ∀ j : ↥J, fderiv ℝ f (apt z) (Pi.single j (1 : ℝ)) * conj (z j) * (if b = j then z a else 0) -
      fderiv ℝ f (apt z) (Pi.single j (1 : ℝ)) * z j * (if a = j then conj (z b) else 0) =
      (if b = j then fderiv ℝ f (apt z) (Pi.single j (1 : ℝ)) * conj (z j) * z a else 0) -
      (if a = j then fderiv ℝ f (apt z) (Pi.single j (1 : ℝ)) * z j * conj (z b) else 0) := fun j => by
    by_cases hb : b = j <;> by_cases ha : a = j <;> simp [hb, ha]
  simp only [e, Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  rw [pi_single_one_sub, map_sub]
  ring

end Counts

end QuantumNLS.CountFunctionsS01Poisson

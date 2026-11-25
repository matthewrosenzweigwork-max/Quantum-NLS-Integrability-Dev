import QuantumNLS.Prop022GradientR118

/-! The exact second symmetric slot sum on diagonal directions, in the actual
completed tensor carriers. This is the pair part of the real Hessian. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace ComplexConjugate Topology ContDiff
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
namespace QuantumNLS.Prop022SecondSlotR118
open TensorCarrier PhysicalTensor BetheCoefficientTransform
open Prop022TensorCompressionR115 Prop022TensorCalculusR116 Prop022ClassicalTimeR116
open Prop022SymmetricSlotR117 Prop022GradientR118
variable {L : ℝ} [Fact (0 < L)]
local instance : AddCommGroup (L2T L) := (inferInstance : NormedAddCommGroup (L2T L)).toAddCommGroup
local instance (n : ℕ) : AddCommGroup (HilbertTensorPower ℂ (L2T L) n) :=
  (inferInstance : NormedAddCommGroup (HilbertTensorPower ℂ (L2T L) n)).toAddCommGroup

/-- Append one fixed vector and project to the symmetric sector. -/
def appendFixed (r : ℕ) (h : L2T L) :
    HilbertTensorPower ℂ (L2T L) r →L[ℂ] HN L (r+1) :=
  (physSector L (r+1)).orthogonalProjectionOnto ∘L
    (splitIsometry (𝕜 := ℂ) (E := L2T L) r 1).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (tensorLeft (E := HilbertTensorPower ℂ (L2T L) r)
      (F := HilbertTensorPower ℂ (L2T L) 1)).flip (htpow 1 h)

lemma appendFixed_power (r : ℕ) (u h : L2T L) :
    appendFixed r h (htpow r u) = insertion r 1 u (power 1 h) := rfl

lemma appendFixed_norm (r : ℕ) (h : L2T L)
    (x : HilbertTensorPower ℂ (L2T L) r) : ‖appendFixed r h x‖ ≤ ‖x‖ * ‖h‖ := by
  change ‖(physSector L (r+1)).orthogonalProjectionOnto
    ((splitIsometry r 1).symm (htmul x (htpow 1 h)))‖ ≤ _
  exact (Submodule.norm_orthogonalProjectionOnto_apply_le _ _).trans (by
    rw [LinearIsometryEquiv.norm_map, norm_htmul, norm_htpow, pow_one])

/-- The derivative in the base profile of its first power differential. -/
def powerDD (r : ℕ) (u h : L2T L) : L2T L →L[ℝ] HN L (r+1) :=
  ((r+1 : ℕ) : ℝ) • ((appendFixed r h).restrictScalars ℝ ∘L powerDifferential r u)

lemma powerD_hasFDerivAt (r : ℕ) (u h : L2T L) :
    HasFDerivAt (fun v => powerD (r+1) v h) (powerDD r u h) u := by
  have he : (fun v => powerD (r+1) v h) =
      (fun v => ((r+1 : ℕ) : ℝ) • appendFixed r h (htpow r v)) := by
    funext v
    rw [powerD_eq_insertion, appendFixed_power]
  rw [he]
  exact (((appendFixed r h).restrictScalars ℝ).hasFDerivAt.comp u
    (htpow_hasFDerivAt r u)).const_smul (((r+1 : ℕ) : ℝ))

lemma projected_two_slots_swap (n : ℕ) (u h k : L2T L) (i j f : Fin n)
    (hi : i ≠ f) (hj : j ≠ f) :
    (physSector L n).orthogonalProjectionOnto
      (tensorMultilinear n (Function.update (Function.update (fun _ => u) i k) f h)) =
    (physSector L n).orthogonalProjectionOnto
      (tensorMultilinear n (Function.update (Function.update (fun _ => u) j k) f h)) := by
  classical
  apply Subtype.ext
  rw [← Submodule.starProjection_apply, ← Submodule.starProjection_apply,
    ← symProj_eq_starProjection, tensorMultilinear_apply, tensorMultilinear_apply]
  have hf : (fun a => Function.update (Function.update (fun _ => u) i k) f h
        ((Equiv.swap i j).symm a)) =
      Function.update (Function.update (fun _ => u) j k) f h := by
    by_cases hij : i = j
    · subst j; simp only [Equiv.swap_self]; rfl
    funext a
    by_cases haf : a = f
    · subst a
      simp [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hi.symm hj.symm]
    · by_cases hai : a = i
      · subst a
        simp [Equiv.symm_swap, hi, hj, hij, Ne.symm hij]
      · by_cases haj : a = j
        · subst a
          simp [Equiv.symm_swap, hi, hj]
        · simp [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hai haj, haf, hai, haj]
  have hp := Ext006PairPowerWick.symProj_perm (E := L2T L) (Equiv.swap i j)
    ((ptprod (Function.update (Function.update (fun _ => u) i k) f h) :
      AlgTensorPower ℂ (L2T L) n) : HilbertTensorPower ℂ (L2T L) n)
  rw [permHilbertIsometry_coe, permLinearEquiv_ptprod, hf] at hp
  exact hp.symm

lemma append_update_one (n : ℕ) (u h : L2T L) (i : Fin n) :
    Fin.append (Function.update (fun _ => u) i h) (fun _ : Fin 1 => h) =
      Function.update (Function.update (fun _ : Fin (n+1) => u) (i.castAdd 1) h) (Fin.last n) h := by
  classical
  funext a
  refine Fin.addCases (fun j => ?_) (fun j => ?_) a
  · have hn : j.castAdd 1 ≠ Fin.last n := Fin.ne_of_val_ne (by change (j:ℕ) ≠ n; omega)
    simp [hn, Function.update_apply, Fin.castAdd_inj]
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have he : Fin.natAdd n (0 : Fin 1) = Fin.last n := by apply Fin.ext; simp
    rw [Fin.append_right, he, Function.update_self]

lemma append_two_constant (r : ℕ) (u h : L2T L) :
    Fin.append (fun _ : Fin r => u) (fun _ : Fin 2 => h) =
      Function.update (Function.update (fun _ : Fin (r+2) => u) ((Fin.last r).castAdd 1) h)
        (Fin.last (r+1)) h := by
  classical
  funext a
  refine Fin.addCases (fun j => ?_) (fun j => ?_) a
  · have h1 : j.castAdd 2 ≠ Fin.last (r+1) := Fin.ne_of_val_ne (by change (j:ℕ) ≠ r+1; omega)
    have h2 : j.castAdd 2 ≠ (Fin.last r).castAdd 1 := Fin.ne_of_val_ne (by change (j:ℕ) ≠ r; omega)
    simp [h1, h2]
  · fin_cases j
    · have h1 : Fin.natAdd r (0 : Fin 2) ≠ Fin.last (r+1) := by apply Fin.ne_of_val_ne; simp
      have h2 : Fin.natAdd r (0 : Fin 2) = (Fin.last r).castAdd 1 := by apply Fin.ext; simp
      rw [Fin.append_right]
      change h = Function.update (Function.update (fun _ => u) ((Fin.last r).castAdd 1) h) (Fin.last (r+1)) h (Fin.natAdd r (0 : Fin 2))
      rw [Function.update_of_ne h1, h2, Function.update_self]
    · have h1 : Fin.natAdd r (1 : Fin 2) = Fin.last (r+1) := by apply Fin.ext; simp
      rw [Fin.append_right]
      change h = Function.update (Function.update (fun _ => u) ((Fin.last r).castAdd 1) h) (Fin.last (r+1)) h (Fin.natAdd r (1 : Fin 2))
      rw [h1, Function.update_self]

lemma second_slot_eq (r : ℕ) (u h : L2T L) (i : Fin (r+1)) :
    appendFixed (r+1) h (tensorMultilinear (r+1) (Function.update (fun _ => u) i h)) =
      insertion r 2 u (power 2 h) := by
  classical
  change (physSector L (r+2)).orthogonalProjectionOnto
    ((splitIsometry (r+1) 1).symm
      (htmul (tensorMultilinear (r+1) (Function.update (fun _ => u) i h)) (htpow 1 h))) =
    (physSector L (r+2)).orthogonalProjectionOnto
      ((splitIsometry r 2).symm (htmul (htpow r u) (htpow 2 h)))
  rw [tensorMultilinear_apply, htpow, htpow, htpow,
    ← splitIsometry_ptprod_append, ← splitIsometry_ptprod_append,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply]
  change (physSector L (r+2)).orthogonalProjectionOnto
    (tensorMultilinear (r+2) (Fin.append (m := r+1) (n := 1) (Function.update (fun _ : Fin (r+1) => u) i h) (fun _ : Fin 1 => h))) =
    (physSector L (r+2)).orthogonalProjectionOnto
      (tensorMultilinear (r+2) (Fin.append (m := r) (n := 2) (fun _ : Fin r => u) (fun _ : Fin 2 => h)))
  rw [append_update_one, append_two_constant]
  apply projected_two_slots_swap
  · exact Fin.ne_of_val_ne (by change (i:ℕ) ≠ r+1; omega)
  · exact Fin.ne_of_val_ne (by simp)

/-- Exact m(m-1) factor for the second differential on a diagonal direction. -/
theorem powerDD_diagonal (r : ℕ) (u h : L2T L) :
    powerDD (r+1) u h h = (((r+2 : ℕ) : ℝ) * ((r+1 : ℕ) : ℝ)) •
      insertion r 2 u (power 2 h) := by
  classical
  change ((r+2 : ℕ) : ℝ) • appendFixed (r+1) h (powerDifferential (r+1) u h) = _
  rw [powerDifferential, sum_apply, map_sum]
  have he (i : Fin (r+1)) :
      appendFixed (r+1) h
        (((tensorMultilinear (L := L) (r+1)).restrictScalars ℝ).toContinuousLinearMap
          (fun _ => u) i h) = insertion r 2 u (power 2 h) := second_slot_eq r u h i
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ (r+1), smul_smul]

lemma powerDD_one (u h k : L2T L) : powerDD 0 u h k = 0 := by
  change ((0+1 : ℕ) : ℝ) • appendFixed 0 h (powerDifferential 0 u k) = 0
  rw [powerDifferential]
  simp

/-- Literal second differential of the rank polynomial. -/
def classicalHessian (B : ∀ m, HN L m →L[ℂ] HN L m) (m : ℕ) (u : L2T L) :
    L2T L →L[ℝ] L2T L →L[ℝ] ℝ := fderiv ℝ (classicalD B m) u

lemma classicalD_smooth (B : ∀ m, HN L m →L[ℂ] HN L m) (m : ℕ) :
    ContDiff ℝ 1 (classicalD B m) := by
  exact (classicalTerm_smooth B m 2).fderiv_right (by norm_num)

/-- No Hessian value is postulated: this is obtained by differentiating the
rank polynomial's proved first differential. -/
theorem classicalHessian_apply (B : ∀ m, HN L m →L[ℂ] HN L m)
    (r : ℕ) (u h k : L2T L) :
    classicalHessian B (r+1) u k h =
      (⟪powerD (r+1) u k, B (r+1) (powerD (r+1) u h)⟫_ℂ +
        ⟪power (r+1) u, B (r+1) (powerDD r u h k)⟫_ℂ +
        (⟪powerDD r u h k, B (r+1) (power (r+1) u)⟫_ℂ +
        ⟪powerD (r+1) u h, B (r+1) (powerD (r+1) u k)⟫_ℂ)).re := by
  have hp := power_hasFDerivAt (r+1) u
  have hd := powerD_hasFDerivAt r u h
  have h1 := hp.inner ℂ (((B (r+1)).restrictScalars ℝ).hasFDerivAt.comp u hd)
  have h2 := hd.inner ℂ (((B (r+1)).restrictScalars ℝ).hasFDerivAt.comp u hp)
  have hh := Complex.reCLM.hasFDerivAt.comp u (h1.add h2)
  have he : (fun v => classicalD B (r+1) v h) =
      fun v => classicalRate B (r+1) v h := by funext v; exact classicalD_apply B (r+1) v h
  have ha := (ContinuousLinearMap.apply ℝ ℝ h).hasFDerivAt.comp u
    ((classicalD_smooth B (r+1)).differentiable (by norm_num) u).hasFDerivAt
  change HasFDerivAt (fun v => classicalD B (r+1) v h) _ u at ha
  rw [he] at ha
  change HasFDerivAt (fun v => classicalRate B (r+1) v h) _ u at hh
  have heq := congrArg (fun T : L2T L →L[ℝ] ℝ => T k) (ha.unique hh)
  convert heq using 1
  · rfl
  · simp only [comp_apply, add_apply, fderivInnerCLM_apply, prod_apply,
      Complex.reCLM_apply, Complex.add_re]
    change
      (⟪powerD (r+1) u k, B (r+1) (powerD (r+1) u h)⟫_ℂ).re +
        (⟪power (r+1) u, B (r+1) (powerDD r u h k)⟫_ℂ).re +
        ((⟪powerDD r u h k, B (r+1) (power (r+1) u)⟫_ℂ).re +
        (⟪powerD (r+1) u h, B (r+1) (powerD (r+1) u k)⟫_ℂ).re) =
      (⟪power (r+1) u, B (r+1) (powerDD r u h k)⟫_ℂ).re +
        (⟪powerD (r+1) u k, B (r+1) (powerD (r+1) u h)⟫_ℂ).re +
        ((⟪powerD (r+1) u h, B (r+1) (powerD (r+1) u k)⟫_ℂ).re +
        (⟪powerDD r u h k, B (r+1) (power (r+1) u)⟫_ℂ).re)
    ring

/-- The pair and mixed contractions are the two diagonal Hessian blocks,
with the physical factor two and the exact rank factors. -/
theorem classicalHessian_diagonal (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (r : ℕ) (u h : L2T L) :
    classicalHessian B (r+2) u h h =
      2 * (⟪power 1 h, mixedTerm B u (r+1) (power 1 h)⟫_ℂ).re +
      2 * (⟪power 2 h, pairTerm B u r⟫_ℂ).re := by
  rw [classicalHessian_apply]
  have hb : (⟪power (r+2) u, B (r+2) (powerDD (r+1) u h h)⟫_ℂ).re =
      (⟪powerDD (r+1) u h h, B (r+2) (power (r+2) u)⟫_ℂ).re := by
    rw [← adjoint_inner_left, hs]
    exact inner_re_symm (𝕜 := ℂ) _ _
  simp only [Complex.add_re]
  rw [hb, powerDD_diagonal, inner_smul_left_real, pairTerm_matrix,
    powerD_eq_insertion]
  have hmap (m : ℕ) (c : ℝ) (x : HN L m) : B m (c • x) = c • B m x :=
    ((B m).restrictScalars ℝ).map_smul c x
  have hir {m : ℕ} (x y : HN L m) (c : ℝ) : ⟪x,c • y⟫_ℂ = c • ⟪x,y⟫_ℂ := by
    change ⟪x,(c:ℂ) • y⟫_ℂ = (c:ℂ) * ⟪x,y⟫_ℂ
    rw [inner_smul_right]
  simp only [mixedTerm, FunLike.coe_smul, Pi.smul_apply, comp_apply, inner_smul_right,
    adjoint_inner_right, hmap, inner_smul_left_real, hir, Complex.real_smul, pow_two,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re,
    Complex.natCast_im, zero_mul, mul_zero, sub_zero]
  push_cast
  simp
  ring

end QuantumNLS.Prop022SecondSlotR118
#print axioms QuantumNLS.Prop022SecondSlotR118.powerDD_diagonal
#print axioms QuantumNLS.Prop022SecondSlotR118.classicalHessian_apply
#print axioms QuantumNLS.Prop022SecondSlotR118.classicalHessian_diagonal

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022SecondSlotR118." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022SecondSlotR118." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R118 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."

import QuantumNLS.Prop024WConstant
import QuantumNLS.Prop021RemainderInputR131
import QuantumNLS.Prop022PrintedCoefficientsR124

/-! PROP-024 step (1), identification of the linear term (Prop024WLinear).

The degree-one Wick cells `linVec` of `Prop024WSeries` are identified with the PROP-021 linear piece
`√N · linearHamiltonian (gradient B u)` of `Prop021RemainderInputR131.lowOrders`
(source `fluctuations.tex:274-276`: the `j = 1` terms are `√N{a*(∇F(u)) + a(∇F(u))}`).

* `eq_rk_one_zero`, `eq_rk_zero_one`: every kernel `HN 0 → HN 1`, `HN 1 → HN 0` is a rank-one power kernel
  (the first power embedding `oneEmbedding` is an isometry onto `HN 1`, `oneEmbedding_surj`).
* `wickFock_one_zero`, `wickFock_zero_one`: `𝒲_{1,0}(C) = a*(g_C)`, `𝒲_{0,1}(C) = a(g_{C†})` on the smooth domain.
* `gradientTerm_eq`: the `r`-th gradient term of `Prop022GradientR118` is `(r+1)` times the `ck`-vector.
* `cellDeg_one_eq`, `linVec_eq_linearHamiltonian`: `linVec N B u x = √N • linearHamiltonian (gradient B u) x hx`.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace ComplexConjugate Topology
namespace QuantumNLS.Prop024WLinear
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors Ext006PhysFockCoord
open Prop024WWeylPhysical Prop022TensorCompressionR115 Prop022ACoherent
open Prop024WBlock Prop024WSector Prop024WWords Prop024WOrder Prop024WSeries Prop024WConstant
open Prop024ContractionsR54 Prop022FactorialCoefficientsR115 Prop022PrintedCoefficientsR124
open Ext006ModeDomainR33a
variable {L : ℝ} [Fact (0 < L)]

/-! ### The first-sector embedding is onto -/

lemma inner_oneEmbedding (g h : L2T L) :
    ⟪oneEmbedding g, oneEmbedding h⟫_ℂ = ⟪g, h⟫_ℂ := by
  rw [oneEmbedding_apply, oneEmbedding_apply, inner_power, pow_one]

lemma oneEmbedding_surj (z : HN L 1) :
    oneEmbedding ((oneEmbedding (L := L)).adjoint z) = z := by
  apply sub_eq_zero.mp
  apply powers_total 1
  intro g
  rw [inner_sub_right, ← oneEmbedding_apply g, inner_oneEmbedding,
    ContinuousLinearMap.adjoint_inner_right, sub_self]

lemma power_zero_eq (u v : L2T L) : (power 0 u : HN L 0) = power 0 v := by
  apply (PhysicalPlacements.physZeroSectorIso L).injective
  rw [physZero_power, physZero_power]

lemma inner_power_zero (u v : L2T L) : ⟪(power 0 u : HN L 0), power 0 v⟫_ℂ = 1 := by
  rw [inner_power, pow_zero]

/-! ### Kernels between the zero and the one-particle sector are rank-one power kernels -/

lemma eq_rk_one_zero (C : HN L 0 →L[ℂ] HN L 1) (f : L2T L) :
    C = rk 1 0 ((oneEmbedding (L := L)).adjoint (C (power 0 f))) f := by
  apply clm_ext_powers
  intro g' h'
  rw [power_zero_eq h' f, rk_apply, inner_smul_right, inner_power_zero, one_mul, inner_power, pow_one,
    ContinuousLinearMap.adjoint_inner_right, oneEmbedding_apply]

lemma eq_rk_zero_one (C : HN L 1 →L[ℂ] HN L 0) (g : L2T L) :
    C = rk 0 1 g ((oneEmbedding (L := L)).adjoint (C.adjoint (power 0 g))) := by
  apply clm_ext_powers
  intro g' h'
  have key : ⟪power 1 ((oneEmbedding (L := L)).adjoint (C.adjoint (power 0 g))), power 1 h'⟫_ℂ =
      ⟪(power 0 g : HN L 0), C (power 1 h')⟫_ℂ := by
    rw [inner_power, pow_one, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left, oneEmbedding_apply]
  rw [power_zero_eq g' g, rk_apply, inner_smul_right, key, inner_power_zero, mul_one]

/-! ### The Wick operators `𝒲_{1,0}` and `𝒲_{0,1}` are creation and annihilation -/

lemma wickFock_one_zero (C : HN L 0 →L[ℂ] HN L 1) (f : L2T L) (y : physSmooth L) :
    wickFock 1 0 C y.1 = (creP ((oneEmbedding (L := L)).adjoint (C (power 0 f))) y).1 := by
  have h : wickFock 1 0 C y.1 =
      wickFock 1 0 (rk 1 0 ((oneEmbedding (L := L)).adjoint (C (power 0 f))) f) y.1 :=
    congrArg (fun K : HN L 0 →L[ℂ] HN L 1 => wickFock 1 0 K y.1) (eq_rk_one_zero C f)
  rw [h, wickFock_rk]
  simp

lemma wickFock_zero_one (C : HN L 1 →L[ℂ] HN L 0) (g : L2T L) (y : physSmooth L) :
    wickFock 0 1 C y.1 =
      (annP ((oneEmbedding (L := L)).adjoint (C.adjoint (power 0 g))) y).1 := by
  have h : wickFock 0 1 C y.1 =
      wickFock 0 1 (rk 0 1 g ((oneEmbedding (L := L)).adjoint (C.adjoint (power 0 g)))) y.1 :=
    congrArg (fun K : HN L 1 →L[ℂ] HN L 0 => wickFock 0 1 K y.1) (eq_rk_zero_one C g)
  rw [h, wickFock_rk]
  simp

/-! ### The contracted kernels of degree one and the gradient -/

lemma ck_adjoint {m a b : ℕ} (ha : a ≤ m) (hb : b ≤ m) (Bm : HN L m →L[ℂ] HN L m)
    (hs : Bm.adjoint = Bm) (u : L2T L) :
    (ck m a b ha hb Bm u).adjoint = ck m b a hb ha Bm u := by
  unfold ck
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, hs,
    ContinuousLinearMap.comp_assoc]

lemma ck_vec (m a : ℕ) (ha : a ≤ m) (Bm : HN L m →L[ℂ] HN L m) (u : L2T L) :
    ck m a 0 ha (Nat.zero_le m) Bm u (power 0 u) = (insertSector m a ha u).adjoint (Bm (power m u)) := by
  unfold ck
  simp only [ContinuousLinearMap.comp_apply]
  rw [insertSector_power_zero]

/-- The vector in `L2T` representing the `m = r+1` contraction of `B_m u^{⊗m}` against `u^{⊗(m-1)}`. -/
def gradVec (B : ∀ m, HN L m →L[ℂ] HN L m) (r : ℕ) (u : L2T L) : L2T L :=
  (oneEmbedding (L := L)).adjoint
    ((insertSector (r+1) 1 (Nat.le_add_left 1 r) u).adjoint (B (r+1) (power (r+1) u)))

lemma insertion_one_eq_first (r : ℕ) (u h : L2T L) :
    insertion r 1 u (power 1 h) =
      (physSector L (r+1)).orthogonalProjectionOnto (Ext025A8.insertFirst r u h) := by
  have h1 := Prop022SymmetricSlotR117.powerD_eq_insertion r u h
  have h2 := Prop022GradientR118.powerD_eq_first r u h
  rw [h1] at h2
  first
  | exact smul_right_injective _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero r)) h2
  | exact (smul_right_inj (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero r))).mp h2

lemma insertSector_one_power (r : ℕ) (u h : L2T L) :
    insertSector (r+1) 1 (Nat.le_add_left 1 r) u (power 1 h) =
      (physSector L (r+1)).orthogonalProjectionOnto (Ext025A8.insertFirst r u h) :=
  (Subtype.ext (insertSector_coe r 1 (Nat.le_add_left 1 r) u (power 1 h))).trans
    (insertion_one_eq_first r u h)

/-- The source gradient term is `m = r+1` times the contracted vector. -/
lemma gradientTerm_eq (B : ∀ m, HN L m →L[ℂ] HN L m) (r : ℕ) (u : L2T L) :
    Prop022GradientR118.gradientTerm B r u = ((r+1 : ℕ) : ℂ) • gradVec B r u := by
  apply ext_inner_left ℂ
  intro h
  rw [Prop022GradientR118.gradientTerm_pairing, inner_smul_right]
  unfold gradVec
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    oneEmbedding_apply, insertSector_one_power]

lemma div_sqrt_self (N : ℕ) : (N : ℝ) / Real.sqrt (N : ℝ) = Real.sqrt (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have h : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
    rw [div_eq_iff h.ne']
    exact (Real.mul_self_sqrt (Nat.cast_nonneg N)).symm

lemma cellCoeff_one_zero (N m : ℕ) : cellCoeff N m 1 0 = Real.sqrt (N : ℝ) * (m : ℝ) := by
  unfold cellCoeff
  simp only [Nat.add_zero, pow_one, Nat.choose_one_right, Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [div_sqrt_self]

lemma cellCoeff_zero_one (N m : ℕ) : cellCoeff N m 0 1 = Real.sqrt (N : ℝ) * (m : ℝ) := by
  unfold cellCoeff
  simp only [Nat.zero_add, pow_one, Nat.choose_one_right, Nat.choose_zero_right, Nat.cast_one, mul_one,
    one_mul]
  rw [div_sqrt_self]

lemma cellVec_one_zero (N r : ℕ) (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) (y : physSmooth L) :
    cellVec N (r+1) 1 0 (B (r+1)) u y.1 =
      ((Real.sqrt (N : ℝ) * ((r+1 : ℕ) : ℝ) : ℝ) : ℂ) • (creP (gradVec B r u) y).1 := by
  unfold cellVec
  rw [dif_pos ⟨Nat.le_add_left 1 r, Nat.zero_le _⟩, cellCoeff_one_zero, wickFock_one_zero _ u y, ck_vec]
  all_goals rfl

lemma cellVec_zero_one (N r : ℕ) (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (u : L2T L) (y : physSmooth L) :
    cellVec N (r+1) 0 1 (B (r+1)) u y.1 =
      ((Real.sqrt (N : ℝ) * ((r+1 : ℕ) : ℝ) : ℝ) : ℂ) • (annP (gradVec B r u) y).1 := by
  unfold cellVec
  rw [dif_pos ⟨Nat.zero_le _, Nat.le_add_left 1 r⟩, cellCoeff_zero_one, wickFock_zero_one _ u y,
    ck_adjoint (Nat.zero_le _) (Nat.le_add_left 1 r) (B (r+1)) (hs (r+1)) u, ck_vec]
  all_goals rfl

/-! ### Continuity of the linear Hamiltonian in its coefficient -/

lemma annP_add (g g' : L2T L) : annP (g + g') = annP g + annP g' := by
  unfold annP
  rw [map_add, Ext006StrongFieldR41a.A_add_smear, map_add]

lemma creP_add (g g' : L2T L) : creP (g + g') = creP g + creP g' := by
  unfold creP
  rw [map_add, Ext006StrongFieldR41a.C_add_smear, map_add]

lemma le_mul_sqrt_of_sq_le {x h c : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) (hc : 0 ≤ c)
    (H : x ^ 2 ≤ h ^ 2 * c) : x ≤ h * Real.sqrt c := by
  have h1 : x ^ 2 ≤ (h * Real.sqrt c) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc]; exact H
  have h2 : 0 ≤ h * Real.sqrt c := by positivity
  by_contra hlt
  push_neg at hlt
  nlinarith [h1, h2, hlt]

/-- The particle-number mass of a smooth vector. -/
def smoothMass (y : physSmooth L) : ℝ :=
  ∑' m : Occupation.Occ, (Occupation.total m : ℝ) * ‖(physToD y).1 m‖ ^ 2

lemma smoothMass_nonneg (y : physSmooth L) : 0 ≤ smoothMass y :=
  tsum_nonneg (fun m => by positivity)

lemma norm_annP_le (g : L2T L) (y : physSmooth L) :
    ‖(annP g y).1‖ ≤ ‖g‖ * Real.sqrt (smoothMass y) := by
  have h1 : ‖(annP g y).1‖ =
      ‖(Ext006SmoothOperatorsR34a.A ((Ext006KernelHilbertSchmidt.physicalBasis L).repr g)
        (physToD y)).1‖ := by
    unfold annP
    rw [transport_coe, LinearIsometryEquiv.norm_map]
  have hn : ‖(Ext006KernelHilbertSchmidt.physicalBasis L).repr g‖ = ‖g‖ :=
    LinearIsometryEquiv.norm_map _ _
  rw [h1, ← hn]
  exact le_mul_sqrt_of_sq_le (norm_nonneg _) (norm_nonneg _) (smoothMass_nonneg y)
    (Ext006FieldBoundsR42a.A_norm_sq_le_mass _ _)

lemma norm_creP_le (g : L2T L) (y : physSmooth L) :
    ‖(creP g y).1‖ ≤ ‖g‖ * Real.sqrt (smoothMass y + ‖y.1‖ ^ 2) := by
  have h1 : ‖(creP g y).1‖ =
      ‖(Ext006SmoothOperatorsR34a.C ((Ext006KernelHilbertSchmidt.physicalBasis L).repr g)
        (physToD y)).1‖ := by
    unfold creP
    rw [transport_coe, LinearIsometryEquiv.norm_map]
  have hn : ‖(Ext006KernelHilbertSchmidt.physicalBasis L).repr g‖ = ‖g‖ :=
    LinearIsometryEquiv.norm_map _ _
  have hy : ‖(physToD y).1‖ = ‖y.1‖ := by
    rw [physToD_coe, LinearIsometryEquiv.norm_map]
  rw [h1, ← hn]
  apply le_mul_sqrt_of_sq_le (norm_nonneg _) (norm_nonneg _) (add_nonneg (smoothMass_nonneg y) (sq_nonneg _))
  rw [Ext006FieldBoundsR42a.C_norm_sq, hy]
  have h2 := Ext006FieldBoundsR42a.A_norm_sq_le_mass
    ((Ext006KernelHilbertSchmidt.physicalBasis L).repr g) (physToD y)
  have h3 : ∑' m : Occupation.Occ, (Occupation.total m : ℝ) * ‖(physToD y).1 m‖ ^ 2 = smoothMass y := rfl
  rw [h3] at h2
  nlinarith [h2]

/-- The linear Hamiltonian at a fixed smooth vector, as an additive map in its coefficient. -/
def linHom (y : physSmooth L) : L2T L →+ Fock L :=
  AddMonoidHom.mk' (fun g => (annP g y).1 + (creP g y).1) (by
    intro g g'
    show (annP (g+g') y).1 + (creP (g+g') y).1 =
      ((annP g y).1 + (creP g y).1) + ((annP g' y).1 + (creP g' y).1)
    rw [annP_add, creP_add]
    simp only [LinearMap.add_apply, Submodule.coe_add]
    abel)

lemma linHom_apply (y : physSmooth L) (g : L2T L) :
    linHom y g = (annP g y).1 + (creP g y).1 := rfl

lemma continuous_linHom (y : physSmooth L) : Continuous (linHom y) := by
  apply AddMonoidHomClass.continuous_of_bound (linHom y)
    (Real.sqrt (smoothMass y) + Real.sqrt (smoothMass y + ‖y.1‖ ^ 2))
  intro g
  rw [linHom_apply]
  calc ‖(annP g y).1 + (creP g y).1‖ ≤ ‖(annP g y).1‖ + ‖(creP g y).1‖ := norm_add_le _ _
    _ ≤ ‖g‖ * Real.sqrt (smoothMass y) + ‖g‖ * Real.sqrt (smoothMass y + ‖y.1‖ ^ 2) :=
        add_le_add (norm_annP_le g y) (norm_creP_le g y)
    _ = (Real.sqrt (smoothMass y) + Real.sqrt (smoothMass y + ‖y.1‖ ^ 2)) * ‖g‖ := by ring

/-- The smoothness certificate in the form used by `linearHamiltonian`. -/
lemma smoothOf (y : physSmooth L) : Smooth (Ext006PhysicalVacuum.coefficient y.1) :=
  (Prop021DisplacementR129.common_domain y.1).2 ((mem_physSmooth_iff_moments y.1).1 y.2)

/-- The PROP-021 linear Hamiltonian is `a(g) + a*(g)` on the smooth domain. -/
lemma linearHamiltonian_eq (g : L2T L) (y : physSmooth L)
    (hy : Smooth (Ext006PhysicalVacuum.coefficient y.1)) :
    Prop021PhaseR130.linearHamiltonian g y.1 hy = linHom y g := by
  unfold Prop021PhaseR130.linearHamiltonian
  rw [linHom_apply]
  unfold annP creP
  rw [transport_coe, transport_coe, ← map_add]
  rfl

/-! ### The degree-one cell of order `m = r+1` -/

lemma cellDeg_one_eq (N r : ℕ) (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (u : L2T L) (y : physSmooth L) :
    cellDeg N (r+1) 1 (B (r+1)) u y.1 =
      (Real.sqrt (N : ℝ) : ℂ) • linHom y (Prop022GradientR118.gradientTerm B r u) := by
  have e1 : linHom y (Prop022GradientR118.gradientTerm B r u) =
      ((r+1 : ℕ) : ℂ) • linHom y (gradVec B r u) := by
    rw [gradientTerm_eq, Nat.cast_smul_eq_nsmul ℂ (r+1) (gradVec B r u), map_nsmul,
      ← Nat.cast_smul_eq_nsmul ℂ (r+1) (linHom y (gradVec B r u))]
  unfold cellDeg
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.sub_zero, Nat.sub_self]
  rw [cellVec_zero_one N r B hs u y, cellVec_one_zero N r B u y, e1, linHom_apply, ← smul_add,
    smul_smul]
  congr 1
  first
  | (push_cast; ring)
  | push_cast
  | simp

/-- **The linear term.**  `linVec` is `√N` times the actual PROP-021 linear Hamiltonian with the source
gradient `∇F(u)`, as a vector of `Fock L`, for self-adjoint factorial kernels and unit `u`. -/
theorem linVec_eq_linHom (N : ℕ) (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (M Aa : ℝ) (hA : 0 ≤ Aa) (hB : FactorialBound B M Aa)
    (u : L2T L) (hu : ‖u‖ = 1) (y : physSmooth L) :
    linVec N B u y.1 = (Real.sqrt (N : ℝ) : ℂ) • linHom y (Prop022GradientR118.gradient B u) := by
  have hsum : HasSum (fun r => Prop022GradientR118.gradientTerm B r u)
      (Prop022GradientR118.gradient B u) :=
    (Prop022GradientR118.gradient_summable B M Aa 1 hA hB le_rfl u hu.le).hasSum
  have hmap := hsum.map (linHom y) (continuous_linHom y)
  unfold linVec
  rw [tsum_congr (fun r => cellDeg_one_eq N r B hs u y)]
  exact (hmap.const_smul (Real.sqrt (N : ℝ) : ℂ)).tsum_eq

/-- **The linear term, in PROP-021 form** (`Prop021RemainderInputR131.lowOrders`, second summand):
`linVec N B u x = √N • linearHamiltonian (gradient B u) x hx`. -/
theorem linVec_eq_linearHamiltonian (N : ℕ) (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (M Aa : ℝ) (hA : 0 ≤ Aa) (hB : FactorialBound B M Aa)
    (u : L2T L) (hu : ‖u‖ = 1) (y : physSmooth L)
    (hy : Smooth (Ext006PhysicalVacuum.coefficient y.1)) :
    linVec N B u y.1 =
      (Real.sqrt (N : ℝ) : ℂ) • Prop021PhaseR130.linearHamiltonian (Prop022GradientR118.gradient B u) y.1 hy := by
  rw [linearHamiltonian_eq _ y hy]
  exact linVec_eq_linHom N B hs M Aa hA hB u hu y

end QuantumNLS.Prop024WLinear

#print axioms QuantumNLS.Prop024WLinear.oneEmbedding_surj
#print axioms QuantumNLS.Prop024WLinear.wickFock_one_zero
#print axioms QuantumNLS.Prop024WLinear.wickFock_zero_one
#print axioms QuantumNLS.Prop024WLinear.gradientTerm_eq
#print axioms QuantumNLS.Prop024WLinear.cellDeg_one_eq
#print axioms QuantumNLS.Prop024WLinear.linVec_eq_linHom
#print axioms QuantumNLS.Prop024WLinear.linVec_eq_linearHamiltonian

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WLinear." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WLinear." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
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
  Lean.logInfo m!"Prop024WLinear aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard axioms only."

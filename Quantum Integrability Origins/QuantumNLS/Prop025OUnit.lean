import QuantumNLS.Prop025OTarget
import QuantumNLS.ActualModelQuantumR52a
import QuantumNLS.Prop001RseventeenZero
import QuantumNLS.Prop001RthirteenDerivative
import QuantumNLS.RootMeasureContinuity

/-! PROP-025 (thm:MP-mixed, mixed_propagation.tex sha256 24ab083b...), stage O5c:
**the joint spectral unitary is the printed product `U_N(t)V_N(θ)`** (source lines 52-66, 244-420), and the
elementary trace-norm facts used by the final assembly.

"`V_N(θ) = exp(−i Σ_{n∈I} θ_n M_{N,n})`, `U_N(t) = exp(−i Σ_{r∈R} t_r Q_{N,r})` ... Every unitary used below is defined on
the entire `N`-particle Hilbert space by this resolution.  Both families strongly commute."

* `evolution_add_symbol`: the spectral evolution of a sum of symbols is the composition;
* `physBasis_succ`: at positive particle number `N+1` the frozen O3f basis `physBasis` IS the DEF-044 basis
  `Def044D1SpectralR51a.basis` (the R52a basis of `chargeUnitary`/`countUnitary`);
* `mixedEv_eq`: the O3f joint eigenvalue at `N+1`, with labels `enum I` and angles `θ ∘ enum I`, is
  `chargeSymbol + countSymbol` of `ActualModelQuantumR52a` (orders: the same `eigenvalue` at `κ/(N+1)`; counts: the
  corrected occupation `m_n = (marrArr (N+1) m).1 n = m.1 n`);
* **`unitary_eq`**: `evolution(physBasis)(mixedEv)(1) = chargeUnitary ∘ countUnitary` (`N+1` particle convention);
* `rdN_add`: `γ^{(k)}` of DEF-030 at `N = k + q` is `reducedDensityPower k q`;
* `rank_zero_marginal`: the rank-zero marginal of every normalized vector is the `0`-fold projector (both are the
  scalar `1`);
* `htpow_sub_le`, `tensorProj_sub_le`: Lipschitz bound of the `k`-fold projector on the ball of radius `2`;
* `norm_Tact`, `norm_traj`: the product torus preserves the `L²` norm, hence so does every trajectory of the field
  of a torus-invariant differentiable function.
No hypothesis is added; all inherited modules are read-only.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped Topology NNReal ENNReal InnerProductSpace
open MeasureTheory Filter Set

namespace QuantumNLS.Prop025OUnit
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.BetheCoefficientTransform (HN marrArr)
open QuantumNLS.BetheSpectralCharges (evolution evolution_coord eigenvalue)
open QuantumNLS.BulkResponseActual (physBasis)
open QuantumNLS.TensorCarrier (HilbertTensorPower htpow reducedDensityPower ptprod norm_ptprod norm_htpow
  AlgTensorPower)
open QuantumNLS.TraceClass (traceNorm)
open QuantumNLS.Prop025OTarget (enum sum_enum)
open QuantumNLS.RF535Final (Tact GlobalStatement)
open QuantumNLS.SymplecticBracket (hamField)
open QuantumNLS.Ext025B6TorusCoordinates (Torus)
open QuantumNLS.RootMassInvolutionR8 (mass)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-! ### 1. The joint spectral unitary -/

/-- The spectral evolution of a sum of symbols is the composition of the two evolutions. -/
theorem evolution_add_symbol {N : ℕ} (b : BetheCoefficientTransform.BetheBasis L N) (e1 e2 : MArr N → ℝ)
    (ψ : HN L N) :
    evolution b (fun m => e1 m + e2 m) 1 ψ = evolution b e1 1 (evolution b e2 1 ψ) := by
  apply b.repr.injective
  ext m
  simp only [HilbertBasis.repr_apply_apply, evolution_coord]
  have hp : DiagonalMultiplier.phase (fun m => e1 m + e2 m) 1 m =
      DiagonalMultiplier.phase e1 1 m * DiagonalMultiplier.phase e2 1 m := by
    unfold DiagonalMultiplier.phase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hp, mul_assoc]

/-- At positive particle number the O3f basis is the DEF-044 basis. -/
theorem physBasis_succ (hκ : 0 < κ) (N : ℕ) :
    physBasis L hκ (N + 1) = Def044D1SpectralR51a.basis (L := L) hκ N := by
  unfold physBasis
  exact dif_pos (by omega)

/-- The O3f joint eigenvalue at `N+1` is `chargeSymbol + countSymbol`. -/
theorem mixedEv_eq (I : Finset ℤ) (R : Finset ℕ) (t : ℕ → ℝ) (θ : ℤ → ℝ) (N : ℕ) :
    Prop025OPhase.mixedEv L κ R t (enum I) (fun i => θ (enum I i)) (N + 1) =
      fun m => ActualModelQuantumR52a.chargeSymbol (L := L) (κ := κ) R t N m +
        ActualModelQuantumR52a.countSymbol I θ N m := by
  funext m
  unfold Prop025OPhase.mixedEv ActualModelQuantumR52a.chargeSymbol ActualModelQuantumR52a.countSymbol
  congr 1
  · simp only [Nat.cast_add, Nat.cast_one]
  · exact sum_enum I (fun n => θ n * ((m.1 n : ℕ) : ℝ))

/-- **O5c: `evolution(physBasis)(mixedEv)(1) = U_N(t) V_N(θ)`** (the printed product, `N+1` particles). -/
theorem unitary_eq (hκ : 0 < κ) (I : Finset ℤ) (R : Finset ℕ) (t : ℕ → ℝ) (θ : ℤ → ℝ) (N : ℕ)
    (ψ : HN L (N + 1)) :
    evolution (physBasis L hκ (N + 1))
        (Prop025OPhase.mixedEv L κ R t (enum I) (fun i => θ (enum I i)) (N + 1)) 1 ψ =
      ActualModelQuantumR52a.chargeUnitary hκ R t N (ActualModelQuantumR52a.countUnitary hκ I θ N ψ) := by
  rw [physBasis_succ, mixedEv_eq, evolution_add_symbol]
  rfl

/-! ### 2. Marginals -/

/-- DEF-030 at `N = k + q`. -/
theorem rdN_add (k q : ℕ) (hk : k ≤ k + q) (x : HilbertTensorPower ℂ (L2T L) (k + q)) :
    PhysicalTensor.reducedDensityN (k + q) k hk x = reducedDensityPower k q x := by
  unfold PhysicalTensor.reducedDensityN
  have key : ∀ (m : ℕ) (e : m = q) (p : k + q = k + m),
      reducedDensityPower k m (PhysicalTensor.castHTP p x) = reducedDensityPower k q x := by
    intro m e p
    subst e
    rfl
  exact key _ (by omega) _

/-- **Rank zero**: the `0`-marginal of a normalized vector and the `0`-fold projector are both the scalar `1`. -/
theorem rank_zero_marginal (N : ℕ) (hk : 0 ≤ N) (ψ : HilbertTensorPower ℂ (L2T L) N) (hψ : ‖ψ‖ = 1)
    (u : L2T L) :
    PhysicalTensor.reducedDensityN N 0 hk ψ = Prop025OInputs.tensorProj 0 u := by
  unfold Prop025OInputs.tensorProj
  apply Prop001RseventeenZero.unit_density_eq (PhysicalTensor.zeroSectorIso (𝕜 := ℂ) (E := L2T L))
    (htpow 0 u) (PhysicalTensor.zeroSectorIso_htpow u)
  · exact PhysicalTensor.reducedDensityN_isPositive N 0 hk ψ
  · exact PhysicalTensor.traceIn_reducedDensityN_eq_one N 0 hk _ ψ hψ

/-- Telescoping for tensor powers on the ball of radius `B`. -/
theorem htpow_sub_le (n : ℕ) (u v : L2T L) {B : ℝ} (hB : 0 ≤ B) (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B) :
    ‖(htpow n u : HilbertTensorPower ℂ (L2T L) n) - htpow n v‖ ≤ n * B ^ (n - 1) * ‖u - v‖ := by
  set f := QuantumNLS.RootOverlapLimit.htpowML (H := L2T L) n with hf
  have hnorm : ‖f‖ ≤ 1 := by
    refine ContinuousMultilinearMap.opNorm_le_bound zero_le_one (fun m => ?_)
    have e : f m = ((ptprod m : AlgTensorPower ℂ (L2T L) n) : HilbertTensorPower ℂ (L2T L) n) :=
      QuantumNLS.RootOverlapLimit.htpowML_apply n m
    rw [one_mul]
    exact (calc ‖f m‖ = ‖((ptprod m : AlgTensorPower ℂ (L2T L) n) : HilbertTensorPower ℂ (L2T L) n)‖ :=
        congrArg _ e
      _ = ∏ i, ‖m i‖ := by rw [UniformSpace.Completion.norm_coe, norm_ptprod]).le
  have h := f.norm_image_sub_le (fun _ => u) (fun _ => v)
  have e1 : f (fun _ => u) = htpow n u := QuantumNLS.RootOverlapLimit.htpowML_apply n _
  have e2 : f (fun _ => v) = htpow n v := QuantumNLS.RootOverlapLimit.htpowML_apply n _
  have hh : ‖(htpow n u : HilbertTensorPower ℂ (L2T L) n) - htpow n v‖ =
      ‖f (fun _ => u) - f (fun _ => v)‖ := by rw [e1, e2]
  have h1 : ‖(fun _ : Fin n => u)‖ ≤ B := (pi_norm_le_iff_of_nonneg hB).2 (fun _ => hu)
  have h2 : ‖(fun _ : Fin n => v)‖ ≤ B := (pi_norm_le_iff_of_nonneg hB).2 (fun _ => hv)
  have h3 : ‖(fun _ : Fin n => u) - (fun _ : Fin n => v)‖ ≤ ‖u - v‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun _ => le_rfl)
  have h4 : max ‖(fun _ : Fin n => u)‖ ‖(fun _ : Fin n => v)‖ ^ (n - 1) ≤ B ^ (n - 1) :=
    pow_le_pow_left₀ (le_max_iff.2 (Or.inl (norm_nonneg _))) (max_le h1 h2) _
  refine hh.le.trans (h.trans ?_)
  rw [Fintype.card_fin]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc ‖f‖ * (n : ℝ) * max ‖(fun _ : Fin n => u)‖ ‖(fun _ : Fin n => v)‖ ^ (n - 1) *
        ‖(fun _ : Fin n => u) - (fun _ : Fin n => v)‖ ≤ 1 * (n : ℝ) * B ^ (n - 1) * ‖u - v‖ := by
        gcongr
    _ = n * B ^ (n - 1) * ‖u - v‖ := by ring

/-- The constant of the projector bound on the ball of radius `2`. -/
def cproj (k : ℕ) : ℝ := 2 * 2 ^ k * ((k : ℝ) * 2 ^ (k - 1))

theorem cproj_nonneg (k : ℕ) : 0 ≤ cproj k := by unfold cproj; positivity

/-- **Projector bound**: `‖P_k(u) − P_k(v)‖₁ ≤ c_k ‖u − v‖` for `‖u‖, ‖v‖ ≤ 2`. -/
theorem tensorProj_sub_le (k : ℕ) (u v : L2T L) (hu : ‖u‖ ≤ 2) (hv : ‖v‖ ≤ 2) :
    traceNorm (Prop025OInputs.tensorProj k u - Prop025OInputs.tensorProj k v) ≤
      ENNReal.ofReal (cproj k * ‖u - v‖) := by
  set x : HilbertTensorPower ℂ (L2T L) k := htpow k u with hx
  set y : HilbertTensorPower ℂ (L2T L) k := htpow k v with hy
  have hxn : ‖x‖ ≤ 2 ^ k := by rw [hx, norm_htpow]; exact pow_le_pow_left₀ (norm_nonneg _) hu k
  have hyn : ‖y‖ ≤ 2 ^ k := by rw [hy, norm_htpow]; exact pow_le_pow_left₀ (norm_nonneg _) hv k
  have hd : ‖x - y‖ ≤ k * 2 ^ (k - 1) * ‖u - v‖ := htpow_sub_le k u v (by norm_num) hu hv
  have h := Prop001RthirteenDerivative.traceNorm_rankOne_difference x x y y
  change traceNorm (InnerProductSpace.rankOne ℂ x x - InnerProductSpace.rankOne ℂ y y) ≤ _
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hD0 : 0 ≤ (k : ℝ) * 2 ^ (k - 1) * ‖u - v‖ := by positivity
  have e1 : ‖x - y‖ * ‖x‖ ≤ ((k : ℝ) * 2 ^ (k - 1) * ‖u - v‖) * 2 ^ k :=
    mul_le_mul hd hxn (norm_nonneg _) hD0
  have e2 : ‖y‖ * ‖x - y‖ ≤ 2 ^ k * ((k : ℝ) * 2 ^ (k - 1) * ‖u - v‖) :=
    mul_le_mul hyn hd (norm_nonneg _) (by positivity)
  have e3 : cproj k * ‖u - v‖ = ((k : ℝ) * 2 ^ (k - 1) * ‖u - v‖) * 2 ^ k +
      2 ^ k * ((k : ℝ) * 2 ^ (k - 1) * ‖u - v‖) := by unfold cproj; ring
  rw [e3]
  linarith

/-! ### 3. Norm conservation on the phase torus -/

/-- The product torus preserves the `L²` norm (`‖Φ v‖ = ‖v‖`, `Φ T_ψ = rot_{ψ⁻¹} Φ`). -/
theorem norm_Tact (hκ : 0 < κ) {d : ℝ} {Φl : L2T L → QuantumNLS.D01LocalPrimitive.K}
    {Ψl : QuantumNLS.D01LocalPrimitive.K → L2T L} (hG : GlobalStatement L κ hκ d Φl Ψl) (ψ : Torus)
    (v : L2T L) : ‖Tact (L := L) hκ ψ v‖ = ‖v‖ := by
  obtain ⟨-, -, Φ, Ψ, -, -, -, -, -, -, -, -, -, -, -, -, hnorm, -, -, -, -, -, -, hrotψ, -, -, -⟩ := hG.2
  have h1 := hnorm (Tact (L := L) hκ ψ v)
  rw [hrotψ, Prop025OPhys.norm_rotate, hnorm] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1.symm

/-- A trajectory of the field of a torus-invariant differentiable function from a unit vector stays on the unit
sphere (it stays on the phase torus of its datum). -/
theorem norm_traj (hκ : 0 < κ) {d : ℝ} {Φl : L2T L → QuantumNLS.D01LocalPrimitive.K}
    {Ψl : QuantumNLS.D01LocalPrimitive.K → L2T L} (hG : GlobalStatement L κ hκ d Φl Ψl) {F : L2T L → ℝ}
    (hF : ∀ ψ v, F (Tact (L := L) hκ ψ v) = F v) (hFd : Differentiable ℝ F) {u : L2T L} (hu : ‖u‖ = 1)
    (γ : ℝ → L2T L) (hγ0 : γ 0 = u) (hγ : ∀ τ, HasDerivAt γ (hamField F (γ τ)) τ) (τ : ℝ) :
    ‖γ τ‖ = 1 := by
  obtain ⟨ψ, hψ⟩ := Prop025OTorus.on_torus hκ hG (u := u) (v := γ τ) (fun n => by
    rw [Prop025OTorus.mass_conserved hκ hG hF hFd γ hγ n τ, hγ0])
  rw [hψ, norm_Tact hκ hG, hu]

end QuantumNLS.Prop025OUnit

#print axioms QuantumNLS.Prop025OUnit.evolution_add_symbol
#print axioms QuantumNLS.Prop025OUnit.unitary_eq
#print axioms QuantumNLS.Prop025OUnit.rdN_add
#print axioms QuantumNLS.Prop025OUnit.rank_zero_marginal
#print axioms QuantumNLS.Prop025OUnit.tensorProj_sub_le
#print axioms QuantumNLS.Prop025OUnit.norm_traj
-- Recursive type/value audit of every own declaration: standard axioms only, and no held
-- identifier (HeldGP14Tonelli, the superseded pre-D1 `RegularCut`) in the transitive closure.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop025OUnit." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        throwError "Held dependency: {n}"
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
  Lean.logInfo m!"Prop025OUnit aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only, no held identifiers."

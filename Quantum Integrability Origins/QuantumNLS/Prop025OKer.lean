import QuantumNLS.Prop025OPhase
import QuantumNLS.Prop025OInputs
import QuantumNLS.R52CFLinear
import QuantumNLS.R52CFOrbit

/-! PROP-025 (thm:MP-mixed, mixed_propagation.tex sha256 24ab083b...), stage O4a:
**the summed factorial kernels and the exact quantization of `N L_N`** (source lines 420-444).

"The real classical functional associated with eq:MP-L is `F_{a,t,θ}(v) = -(2πκ)⁻¹ Re(∮_{Γ_a} p_t s_κ(z;v)/D dz +
Σ_n θ_n ∮_{Γ_n} s_κ(z;v)/D dz)`.  All denominators are frozen at the original profile `u`.  After removal of its
scalar term, its kernels are `B_j = -(2πκ)⁻¹ Re(∮_{Γ_a} p_t κ^j K_{j,z}/D dz + Σ_n θ_n ∮_{Γ_n} κ^j K_{j,z}/D dz)`.
They are self-adjoint, and the exact `N`-particle quantization is
`N L_N = N ℓ_0 1 + N Σ_{j=1}^N (N)_j/N^j 𝒰_{N,j}(B_j)`."

* `mixD`, `mixK`, `mixScal`: the frozen weight `D(z_θ)⁻¹` (NOT masked), the summed kernels `B_{j+1}` on the frozen
  stage-O3f family `mixedPieces` (window rectangle with weight `p_t`, fixed rectangles with weights `θ_i`), the
  scalar `ℓ_0`;
* `ae_good_mixed`, `LmixOp_eq`: the masked operator `LmixOp` of stage O3f equals the unmasked one;
* **`N_LmixOp`**: `N L_N = (N ℓ_0) 1 + Prop001.generator B N` (the literal falling-factorial placement series);
* `sector_eq`: the literal PROP-021 sector `N Σ_m N^{-m}(n)_m 𝒰_{n,m}(B_m)` at `n = N` is that generator;
* **`marginal_eq`**: the marginal of `e^{-iN L_N} ψ` equals the marginal of the PROP-021 evolution
  `nEvolution (positiveExtension B) N 1 ψ` ("The scalar term changes no reduced projector");
* **`coh_inv`**: the coherent energy of any frozen-contour kernel family with a continuous weight is invariant under
  the full product-torus action `T_ψ` of the accepted global chart ("By the explicit interface, every scalar transfer
  is invariant under all coordinatewise phase rotations") — finitely supported angles by the accepted bracket
  invariance (`R52CFOrbit.symbol_invariant`), all angles by density and continuity of the torus action.
No hypothesis is added; all inherited modules are read-only.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped ComplexConjugate Topology NNReal ENNReal InnerProductSpace
open MeasureTheory Filter Set

namespace QuantumNLS.Prop025OKer
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.Extrapolation (Gfull)
open QuantumNLS.PeriodReconstructionCore
open QuantumNLS.MPContour (Piece ThetaSpace nu zθ uθ rectPieces polyT continuous_polyT continuous_zθ continuous_uθ)
open QuantumNLS.MPFamily (good)
open QuantumNLS.Prop026Uniform (rectFamily rectFamily_props)
open QuantumNLS.Prop025OPhase (mixedPieces xmS xpS LmixOp)
open QuantumNLS.R52CFKernels (kerA scal physK)
open QuantumNLS.FunctionalLinearization (evol)
open QuantumNLS.TensorCarrier (SymSector HilbertTensorPower reducedDensityPower)
open QuantumNLS.Prop022PositiveDataR126 (positiveExtension)
open QuantumNLS.ProductTorusGenerator (Linf)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-! ### 1. The objects -/

/-- The frozen denominator weight `D(z_θ)⁻¹`, `D = Df L κ (Gfull μ)` (no mask). -/
def mixD (hκ : 0 < κ) (u : L2T L) (μ : Measure ℝ) (h a : ℝ) (ords : Finset ℕ) (t : ℕ → ℝ) {nI : ℕ}
    (n : Fin nI → ℤ) (θf : Fin nI → ℝ) : ThetaSpace (6 + nI * 6) → ℂ :=
  fun θ => (Df L κ (Gfull μ) (zθ (mixedPieces hκ u h a ords t n θf) θ))⁻¹

/-- **The summed kernels** `B_{j+1}` (eq:MP-summed-kernels). -/
def mixK (hκ : 0 < κ) (u : L2T L) (μ : Measure ℝ) (h a : ℝ) (ords : Finset ℕ) (t : ℕ → ℝ) {nI : ℕ}
    (n : Fin nI → ℤ) (θf : Fin nI → ℝ) : ∀ j : ℕ, HN L (j + 1) →L[ℂ] HN L (j + 1) :=
  kerA (nu (6 + nI * 6)) κ
    (fun θ => uθ κ (mixedPieces hκ u h a ords t n θf) θ * mixD hκ u μ h a ords t n θf θ)
    (physK (L := L) (zθ (mixedPieces hκ u h a ords t n θf)))

/-- The scalar term `ℓ_0`. -/
def mixScal (hκ : 0 < κ) (u : L2T L) (μ : Measure ℝ) (h a : ℝ) (ords : Finset ℕ) (t : ℕ → ℝ) {nI : ℕ}
    (n : Fin nI → ℤ) (θf : Fin nI → ℝ) : ℝ :=
  scal (nu (6 + nI * 6))
    (fun θ => uθ κ (mixedPieces hκ u h a ords t n θf) θ * mixD hκ u μ h a ords t n θf θ)
    (fun θ => 1 + Complex.exp (Complex.I * zθ (mixedPieces hκ u h a ords t n θf) θ * L))

theorem mixK_selfAdjoint (hκ : 0 < κ) (u : L2T L) (μ : Measure ℝ) (h a : ℝ) (ords : Finset ℕ) (t : ℕ → ℝ)
    {nI : ℕ} (n : Fin nI → ℤ) (θf : Fin nI → ℝ) (j : ℕ) :
    (mixK (L := L) hκ u μ h a ords t n θf j).adjoint = mixK hκ u μ h a ords t n θf j := by
  have hs := R52CFKernels.kerA_selfAdjoint (nu (6 + nI * 6)) κ
    (fun θ => uθ κ (mixedPieces hκ u h a ords t n θf) θ * mixD hκ u μ h a ords t n θf θ)
    (physK (L := L) (zθ (mixedPieces hκ u h a ords t n θf))) j
  unfold mixK
  rw [← ContinuousLinearMap.star_eq_adjoint]
  exact hs.star_eq

/-! ### 2. The mask is immaterial -/

theorem ae_good_mixed (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (_μ : Measure ℝ) {h : ℝ} (hh : 0 < h) (a : ℝ)
    (ords : Finset ℕ) (t : ℕ → ℝ) {nI : ℕ} (n : Fin nI → ℤ) (θf : Fin nI → ℝ) :
    ∀ᵐ θ ∂(nu (6 + nI * 6)), good (mixedPieces hκ u h a ords t n θf) θ := by
  have hlt : ∀ i, xmS hκ u n i < xpS hκ u n i := fun i =>
    (QuantumNLS.Prop025OCount.separator_brackets L hκ u hu (n i)).2.2.1
  have hfam := (rectFamily_props (xmS hκ u n) (xpS hκ u n) (fun _ => h) θf (fun i => |θf i|) hlt
    (fun _ => hh) (fun i => le_rfl)).2.2
  have hpiece : ∀ i, ∀ τ ∈ Ioo (0 : ℝ) 1, (((mixedPieces hκ u h a ords t n θf) i).γ τ).im ≠ 0 := by
    intro i τ hτ
    unfold mixedPieces
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      exact QuantumNLS.Prop019Linearization.rect_im_ne hh _ _ i hτ
    · rw [Fin.append_right]
      exact hfam j τ hτ
  rw [ae_iff]
  refine measure_mono_null
    (t := (Set.univ : Set (Fin (6 + nI * 6))) ×ˢ {τ : unitInterval | (τ : ℝ) = 0 ∨ (τ : ℝ) = 1}) ?_ ?_
  · intro θ' hθ'
    refine Set.mem_prod.2 ⟨Set.mem_univ _, ?_⟩
    show ((θ'.2 : ℝ) = 0 ∨ (θ'.2 : ℝ) = 1)
    by_contra hne
    rw [not_or] at hne
    exact absurd (hpiece θ'.1 θ'.2
      ⟨lt_of_le_of_ne θ'.2.2.1 (Ne.symm hne.1), lt_of_le_of_ne θ'.2.2.2 hne.2⟩) hθ'
  · unfold nu
    rw [Measure.prod_prod, QuantumNLS.Prop020Link.vol01, mul_zero]

open Classical in
theorem LmixOp_eq (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (μ : Measure ℝ) {h : ℝ} (hh : 0 < h) (a : ℝ)
    (ords : Finset ℕ) (t : ℕ → ℝ) {nI : ℕ} (n : Fin nI → ℤ) (θf : Fin nI → ℝ) (N : ℕ) :
    LmixOp hκ u μ h a ords t n θf N =
      MPOps.Lop (nu (6 + nI * 6))
        (fun θ => NormalizedTransfer.normalizedTransfer L κ N (zθ (mixedPieces hκ u h a ords t n θf) θ))
        (uθ κ (mixedPieces hκ u h a ords t n θf)) (mixD hκ u μ h a ords t n θf) := by
  unfold LmixOp MPOps.Lop
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_good_mixed hκ u hu μ hh a ords t n θf] with θ hθ
  simp only [mixD, if_pos hθ]

/-! ### 3. The exact quantization -/

/-- **`N L_N = (N ℓ_0) 1 + N Σ_j (N)_j/N^j 𝒰_{N,j}(B_j)`**, for a continuous frozen weight. -/
theorem N_LmixOp (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (μ : Measure ℝ) {h : ℝ} (hh : 0 < h) (a : ℝ)
    (ords : Finset ℕ) (t : ℕ → ℝ) {nI : ℕ} (n : Fin nI → ℤ) (θf : Fin nI → ℝ) (N : ℕ)
    (hd : Continuous (mixD (L := L) hκ u μ h a ords t n θf)) :
    ((N : ℕ) : ℂ) • LmixOp hκ u μ h a ords t n θf N =
      ((((N : ℕ) : ℝ) * mixScal hκ u μ h a ords t n θf : ℝ) : ℂ) •
          (1 : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N) +
        Prop001.generator (mixK hκ u μ h a ords t n θf) N := by
  rw [LmixOp_eq hκ u hu μ hh a ords t n θf N]
  exact R52CFKernels.N_Lop_eq (L := L) (nu (6 + nI * 6)) κ N (zθ (mixedPieces hκ u h a ords t n θf))
    (uθ κ (mixedPieces hκ u h a ords t n θf)) (mixD hκ u μ h a ords t n θf)
    (continuous_zθ _) (continuous_uθ κ _) hd

/-- The literal PROP-021 sector at `n = N` is the PROP-001 generator. -/
theorem sector_eq (K : ∀ j : ℕ, HN L (j + 1) →L[ℂ] HN L (j + 1)) (N : ℕ) :
    Prop021ManyBodyR129.sector (positiveExtension K) N N = Prop001.generator K N := by
  unfold Prop021ManyBodyR129.sector Prop001.generator
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  unfold Prop001.theta
  rw [inv_pow, div_eq_inv_mul]

/-- **The scalar term changes no reduced density**: the marginal of `e^{-iN L_N}ψ` is that of the PROP-021
`N`-sector evolution of the summed kernels. -/
theorem marginal_eq (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (μ : Measure ℝ) {h : ℝ} (hh : 0 < h) (a : ℝ)
    (ords : Finset ℕ) (t : ℕ → ℝ) {nI : ℕ} (n : Fin nI → ℤ) (θf : Fin nI → ℝ) (k q : ℕ)
    (hd : Continuous (mixD (L := L) hκ u μ h a ords t n θf)) (ψ : SymSector ℂ (L2T L) (k + q)) :
    reducedDensityPower k q
        ((evol ((((k + q : ℕ) : ℝ) : ℂ) • LmixOp hκ u μ h a ords t n θf (k + q)) 1 ψ :
          SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q)) =
      PhysicalTensor.reducedDensityN (k + q) k (Nat.le_add_right k q)
        ((Prop025OInputs.nEvolution (positiveExtension (mixK hκ u μ h a ords t n θf)) (k + q) 1 ψ :
          HN L (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q)) := by
  have hc : ((((k + q : ℕ) : ℝ) : ℂ)) = (((k + q : ℕ) : ℂ)) := by push_cast; rfl
  rw [hc, N_LmixOp hκ u hu μ hh a ords t n θf (k + q) hd, R52CFLinear.evol_scalar_add,
    R52CFLinear.rdN_add]
  unfold Prop025OInputs.nEvolution
  rw [sector_eq]
  have hph : ‖Complex.exp (-Complex.I * (((((k + q : ℕ) : ℝ) *
      mixScal hκ u μ h a ords t n θf : ℝ)) : ℂ))‖ = 1 := by
    rw [show -Complex.I * (((((k + q : ℕ) : ℝ) * mixScal hκ u μ h a ords t n θf : ℝ)) : ℂ) =
      ((-(((k + q : ℕ) : ℝ) * mixScal hκ u μ h a ords t n θf) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [Submodule.coe_smul, QuantumNLS.Prop020Diag.reducedDensityPower_phase k q _ hph]

/-! ### 4. Product-torus invariance of the frozen coherent energy -/

/-- A finitely supported angle vector with the given circle values on `F`. -/
def angF (ψ : ℤ → Circle) (F : Finset ℤ) : Linf :=
  ⟨fun n => if n ∈ F then Complex.arg (ψ n : ℂ) else 0, memℓp_infty ⟨Real.pi, by
    rintro x ⟨n, rfl⟩
    show ‖(if n ∈ F then Complex.arg (ψ n : ℂ) else 0)‖ ≤ Real.pi
    split_ifs
    · rw [Real.norm_eq_abs]; exact Complex.abs_arg_le_pi _
    · simp [Real.pi_pos.le]⟩⟩

theorem angF_apply (ψ : ℤ → Circle) (F : Finset ℤ) (n : ℤ) :
    angF ψ F n = if n ∈ F then Complex.arg (ψ n : ℂ) else 0 := rfl

theorem symbol_torus_invariant (hκ : 0 < κ) {d : ℝ} {Φl : L2T L → QuantumNLS.D01LocalPrimitive.K}
    {Ψl : QuantumNLS.D01LocalPrimitive.K → L2T L} (hG : RF535Final.GlobalStatement L κ hκ d Φl Ψl)
    (ψ : ℤ → Circle) (v : L2T L) (w : ℂ) :
    NormalizedTransfer.productSymbol L κ (RF535Final.Tact (L := L) hκ ψ v) w =
      NormalizedTransfer.productSymbol L κ v w := by
  -- the finitely supported truncations
  set ψF : Finset ℤ → (ℤ → Circle) := fun F n => Circle.exp (angF ψ F n) with hψF
  have hfin : ∀ F : Finset ℤ, NormalizedTransfer.productSymbol L κ (RF535Final.Tact (L := L) hκ (ψF F) v) w =
      NormalizedTransfer.productSymbol L κ v w := by
    intro F
    have h1 := hG.1.2.1 (angF ψ F) v
    have h2 := QuantumNLS.R52CFOrbit.symbol_invariant hκ hG F (angF ψ F)
      (fun n hn => by rw [angF_apply, if_neg hn]) v w
    simp only [hψF]
    rw [h1]
    exact h2
  have hlim : Tendsto ψF atTop (𝓝 ψ) := by
    rw [tendsto_pi_nhds]
    intro n
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({n} : Finset ℤ)] with F hF
    have hn : n ∈ F := hF (Finset.mem_singleton_self n)
    simp only [hψF, angF_apply, if_pos hn]
    exact (Circle.exp_arg (ψ n)).symm
  have hcont : Continuous (fun p : (ℤ → Circle) × L2T L => RF535Final.Tact (L := L) hκ p.1 p.2) :=
    hG.1.2.2.2.2.1
  have hT : Tendsto (fun F => RF535Final.Tact (L := L) hκ (ψF F) v) atTop
      (𝓝 (RF535Final.Tact (L := L) hκ ψ v)) :=
    (hcont.tendsto (ψ, v)).comp (hlim.prodMk_nhds tendsto_const_nhds)
  have hsc : Continuous (fun x : L2T L => NormalizedTransfer.productSymbol L κ x w) :=
    continuous_iff_continuousAt.mpr fun x =>
      (QuantumNLS.Prop010ClassicalR10.analyticAt_symbol hκ x w).continuousAt
  have hS := (hsc.tendsto _).comp hT
  have hS' : Tendsto (fun F => NormalizedTransfer.productSymbol L κ (RF535Final.Tact (L := L) hκ (ψF F) v) w)
      atTop (𝓝 (NormalizedTransfer.productSymbol L κ v w)) := by
    simp only [hfin]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hS hS'

/-- **Invariance of the frozen coherent energy** under the full product torus. -/
theorem coh_inv (hκ : 0 < κ) {d : ℝ} {Φl : L2T L → QuantumNLS.D01LocalPrimitive.K}
    {Ψl : QuantumNLS.D01LocalPrimitive.K → L2T L} (hG : RF535Final.GlobalStatement L κ hκ d Φl Ψl)
    {m : ℕ} (g z : ThetaSpace m → ℂ) (hg : Continuous g) (hz : Continuous z) {hb W : ℝ}
    (hzh : ∀ θ, |(z θ).im| ≤ hb) (hgW : ∀ θ, ‖g θ‖ ≤ W) (ψ : ℤ → Circle) (v : L2T L) :
    R52CFHartree.coh (kerA (nu m) κ g (physK (L := L) z)) (RF535Final.Tact (L := L) hκ ψ v) =
      R52CFHartree.coh (kerA (nu m) κ g (physK (L := L) z)) v := by
  rw [R52CFCoh.coh_eq (nu m) κ g z hg hz hzh hgW, R52CFCoh.coh_eq (nu m) κ g z hg hz hzh hgW]
  simp_rw [symbol_torus_invariant hκ hG ψ v]

end QuantumNLS.Prop025OKer

#print axioms QuantumNLS.Prop025OKer.N_LmixOp
#print axioms QuantumNLS.Prop025OKer.sector_eq
#print axioms QuantumNLS.Prop025OKer.marginal_eq
#print axioms QuantumNLS.Prop025OKer.symbol_torus_invariant
#print axioms QuantumNLS.Prop025OKer.coh_inv
#print axioms QuantumNLS.Prop025OKer.mixK_selfAdjoint

-- Recursive type/value audit of every own declaration: standard axioms only, and no held
-- identifier (HeldGP14Tonelli, the superseded pre-D1 `RegularCut`) in the transitive closure.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop025OKer." then
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
  Lean.logInfo m!"Prop025OKer aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only, no held identifiers."

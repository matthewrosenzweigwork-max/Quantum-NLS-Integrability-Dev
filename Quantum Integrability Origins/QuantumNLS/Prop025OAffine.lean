import QuantumNLS.Prop025OFact
import QuantumNLS.Prop025OPhys

/-! PROP-025 (thm:MP-mixed, mixed_propagation.tex sha256 24ab083b...), stage O5a:
**eq:MP-affine-propagation** (source lines 589-606): "Thus the parameter called `Q` in the physical fluctuation
theorem is at most `CW_a⁴` ... For `N ≥ CW_a⁴` it gives
`sup_{t,θ} ‖γ^{(k)}_{e^{-iNL_N}u^{⊗N}} - |v_{a,t,θ}^{⊗k}⟩⟨v_{a,t,θ}^{⊗k}|‖₁ ≤ C_k N^{-1/4} W_a^7`, where `v_{a,t,θ}` is the
auxiliary-time-one flow of `F_{a,t,θ}` from `u`.  We have applied the arbitrary factorial-kernel theorem once, to
the summed kernels eq:MP-summed-kernels."

The named input `Prop025OInputs.Prop021Input` (PROP-021, Q7B:thm:main at `H = L²(𝕋_L)`) is applied ONCE, with
* the summed kernels `B = mixK` (stage O4a), `A = κL`, `M = max(1, C_f W_a)` (stage O4b `factorial_bound`),
* `P = max(1, C_p(1 + 2M))` from eq:MP-physical-P (stage O4d `phys_P`, with the product-torus invariance of the
  frozen coherent energy, stage O4a `coh_inv`, and the accepted global chart `RF535Final.global_actual_chart`),
* auxiliary time box `T = 1`, the exact product preparation `u^{⊗N}`;
the scalar term is removed by stage O4a `marginal_eq`, and `N ≥ c_A Q` holds eventually by the frozen O1
`large_N` (`Q ≤ c W_a⁴`).  The classical endpoint is the time-one value of a solution `γ` of the frozen affine
equation `γ' = X_{F_{a,t,θ}}(γ)`, `γ(0) = u` (the ambient flow `classicalFlow`).
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped ComplexConjugate Topology NNReal ENNReal InnerProductSpace
open MeasureTheory Filter Set

namespace QuantumNLS.Prop025OAffine
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.MPContour (ThetaSpace nu zθ uθ continuous_zθ continuous_uθ)
open QuantumNLS.Prop025OPhase (mixedPieces LmixOp)
open QuantumNLS.Prop025OKer (mixD mixK marginal_eq coh_inv mixK_selfAdjoint)
open QuantumNLS.Prop025OFinal (W)
open QuantumNLS.Prop025OParams (alpha alpha_pos large_N)
open QuantumNLS.PROP018Probability (cutN cut_bounds)
open QuantumNLS.Prop017Physical (RootSpectralInputs)
open QuantumNLS.Prop017Quantum (eta0)
open QuantumNLS.BulkResponseActual (IsLimitingRapidityMeasure)
open QuantumNLS.FunctionalLinearization (evol)
open QuantumNLS.TensorCarrier (SymSector HilbertTensorPower reducedDensityPower)
open QuantumNLS.TraceClass (traceNorm)
open QuantumNLS.HighMomentsOps (wvec)
open QuantumNLS.Prop022PositiveDataR126 (positiveExtension positiveExtension_bound positiveExtension_selfAdjoint)
open QuantumNLS.Prop022ClassicalFlowR126 (classicalFlow classicalFlow_spec classicalFlow_eq_profile)
open QuantumNLS.Prop022ActualProfileR117 (velocity)
open QuantumNLS.Prop022FactorialMajorantR115 (pairMajorant)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

theorem rpow_three_halves_le {Q c W : ℝ} (hQ : 0 ≤ Q) (hc : 0 ≤ c) (hW : 0 ≤ W) (h : Q ≤ c * W ^ 4) :
    Q ^ ((3 : ℝ) / 2) ≤ c ^ ((3 : ℝ) / 2) * W ^ 6 := by
  have h1 : Q ^ ((3 : ℝ) / 2) ≤ (c * W ^ 4) ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow hQ h (by norm_num)
  rw [Real.mul_rpow hc (by positivity)] at h1
  have h2 : (W ^ 4) ^ ((3 : ℝ) / 2) = W ^ 6 := by
    rw [← Real.rpow_natCast W 4, ← Real.rpow_mul hW, ← Real.rpow_natCast W 6]
    norm_num
  rwa [h2] at h1

theorem sqrt_le_of {Q c W : ℝ} (hc : 0 ≤ c) (hW : 1 ≤ W) (h : Q ≤ c * W ^ 4) :
    Real.sqrt Q ≤ Real.sqrt c * W ^ 7 := by
  have hW0 : 0 ≤ W := by linarith
  calc Real.sqrt Q ≤ Real.sqrt (c * W ^ 4) := Real.sqrt_le_sqrt h
    _ = Real.sqrt c * W ^ 2 := by
        rw [Real.sqrt_mul hc, show W ^ 4 = (W ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    _ ≤ Real.sqrt c * W ^ 7 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hW (by norm_num)) (Real.sqrt_nonneg _)

set_option maxHeartbeats 64000000 in
/-- **eq:MP-affine-propagation**, from the named PROP-021 input applied once to the summed kernels. -/
theorem affine_propagation (H21 : Prop025OInputs.Prop021Input (L := L)) (hκ : 0 < κ) (u : L2T L)
    (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (d : ℕ) (hd : 2 ≤ d) (ords : Finset ℕ) (hords : ords ⊆ Finset.range (d + 1)) (T : ℕ → ℝ)
    {nI : ℕ} (n : Fin nI → ℤ) (Θ : Fin nI → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ q : ℕ in atTop, ∀ t : ℕ → ℝ, (∀ r ∈ ords, |t r| ≤ T r) →
      ∀ θf : Fin nI → ℝ, (∀ i, |θf i| ≤ Θ i) →
      ∃ γ : ℝ → L2T L, γ 0 = u ∧
        (∀ τ, HasDerivAt γ (velocity (positiveExtension
          (mixK (L := L) hκ u (μ : Measure ℝ) h (cutN L (alpha d) (k + q)) ords t n θf)) (γ τ)) τ) ∧
        traceNorm (reducedDensityPower k q
            ((evol ((((k + q : ℕ) : ℝ) : ℂ) •
                LmixOp hκ u (μ : Measure ℝ) h (cutN L (alpha d) (k + q)) ords t n θf (k + q)) 1
              (wvec (k + q) u) : SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q)) -
          Prop025OInputs.tensorProj k (γ 1)) ≤
        ENNReal.ofReal (C * ((k + q : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) * W d (cutN L (alpha d) (k + q)) ^ 7) := by
  have hL : 0 < L := Fact.out
  -- the global chart and the physical bound eq:MP-physical-P
  obtain ⟨⟨dl, CL, hdl, hCL, Φloc, Ψloc, hloc⟩, hglob⟩ := RF535Final.global_actual_chart L
  have hG := hglob dl CL Φloc Ψloc hdl hCL hloc κ hκ
  set A : ℝ := κ * L with hAdef
  have hA : 0 < A := mul_pos hκ hL
  obtain ⟨Cp, hCp0, hP⟩ := Prop025OPhys.phys_P hκ hG u hu A hA.le
  -- the factorial constant
  obtain ⟨Cf, hCf0, hevF⟩ := Prop025OFact.factorial_bound hκ u hu hμ hηh hδ hd0 hin d hd ords hords T n Θ
  set Mc : ℝ := (nu (6 + nI * 6)).real univ * Cf * 2 * Real.exp (L * h) with hMcdef
  have hMc0 : 0 ≤ Mc := by rw [hMcdef]; have := (measureReal_nonneg : 0 ≤ (nu (6 + nI * 6)).real univ); positivity
  -- PROP-021, applied once
  obtain ⟨cA, hcA⟩ := H21 A hA
  obtain ⟨CAT, hCAT⟩ := hcA 1 one_pos
  set cP : ℝ := 1 + Cp * (1 + 2 * (1 + Mc)) with hcPdef
  have hcP0 : 0 ≤ cP := by rw [hcPdef]; positivity
  set cQ : ℝ := 1 + pairMajorant A ^ 2 * (1 + Mc) ^ 2 * cP ^ 2 with hcQdef
  have hcQ0 : 0 ≤ cQ := by rw [hcQdef]; positivity
  obtain ⟨N₀, hN₀1, hlarge⟩ := large_N d hd (3 * Real.pi / L) (max cA 0 * cQ) (by positivity) (by positivity)
  set CA : ℝ := max CAT 0 with hCAdef
  refine ⟨CA * Real.sqrt k * ((1 + Mc) * cQ ^ ((3 : ℝ) / 2) + Real.sqrt cQ), by positivity, ?_⟩
  have hNlim : ∀ᶠ q : ℕ in atTop, N₀ ≤ ((k + q : ℕ) : ℝ) := by
    obtain ⟨m, hm⟩ := exists_nat_ge N₀
    filter_upwards [eventually_ge_atTop m] with q hq
    exact hm.trans (by exact_mod_cast (show m ≤ k + q by omega))
  obtain ⟨NF, hNF⟩ := Filter.eventually_atTop.mp hevF
  filter_upwards [eventually_ge_atTop NF, hNlim, eventually_ge_atTop 1] with q hqF hNq hq1
  intro t ht θf hθf
  have hF := hNF (k + q) (by omega)
  set N : ℕ := k + q with hNdef
  have hN1 : 1 ≤ N := by omega
  set a : ℝ := cutN L (alpha d) N with hadef
  obtain ⟨hcut1, hcut2, -⟩ := cut_bounds (θ := alpha d) hL N
  have ha0 : 0 ≤ a := le_trans (by positivity) hcut1
  have hW1 : 1 ≤ W d a := by unfold W; exact one_le_pow₀ (by linarith)
  have hW0 : 0 ≤ W d a := by linarith
  obtain ⟨hcont, hw, him, hfac⟩ := hF t ht θf hθf
  set K := mixK (L := L) hκ u (μ : Measure ℝ) h a ords t n θf with hKdef
  set M : ℝ := max 1 (Mc * W d a) with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMW : M ≤ (1 + Mc) * W d a := by
    rw [hMdef]; apply max_le <;> nlinarith
  have hK : ∀ j, ‖K j‖ ≤ M * A ^ (j + 1) / Real.sqrt ((2 * (j + 1)).factorial : ℝ) := by
    intro j
    refine (hfac j).trans ?_
    rw [hMcdef] at hMdef
    have h1 : (nu (6 + nI * 6)).real univ * Cf * 2 * Real.exp (L * h) * W d a ≤ M := by
      rw [hMdef, ← hMcdef]; exact le_max_right _ _
    gcongr
  have hsK : ∀ j, (K j).adjoint = K j := fun j => mixK_selfAdjoint hκ u _ h a ords t n θf j
  -- the invariance of the frozen coherent energy
  have hinv : ∀ (ψ : ℤ → Circle) (v : L2T L), R52CFHartree.coh K (RF535Final.Tact (L := L) hκ ψ v) =
      R52CFHartree.coh K v :=
    coh_inv hκ hG _ _ ((continuous_uθ κ _).mul hcont) (continuous_zθ _) him hw
  set P : ℝ := max 1 (Cp * (1 + 2 * M)) with hPdef
  have hP1 : 1 ≤ P := le_max_left _ _
  have hPW : P ≤ cP * W d a := by
    rw [hPdef, hcPdef]
    apply max_le
    · nlinarith [mul_nonneg hCp0 (by linarith : (0 : ℝ) ≤ 1 + 2 * M)]
    · have : Cp * (1 + 2 * M) ≤ Cp * ((1 + 2 * (1 + Mc)) * W d a) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hCp0
      nlinarith
  set u₀ : Prop001.Sphere (L2T L) := ⟨u, hu⟩ with hu₀
  have hS : ∀ s t : ℝ, |s| ≤ 1 → |t| ≤ 1 →
      ‖fderiv ℝ (classicalFlow (positiveExtension K) M A hA.le (positiveExtension_bound K M A hK)
          (positiveExtension_selfAdjoint K hsK) (t - s))
        (Prop022ActualProfileR117.profile (positiveExtension K) M A hA.le (positiveExtension_bound K M A hK)
          (positiveExtension_selfAdjoint K hsK) u₀ s)‖ ≤ P := by
    intro s t' hs ht'
    rw [← classicalFlow_eq_profile]
    refine (hP K M (by linarith) hK hsK hinv (t' - s) s).trans ?_
    have hts : |t' - s| ≤ 2 := by
      have := abs_sub (t') s; linarith
    calc Cp * (1 + |t' - s| * M) ≤ Cp * (1 + 2 * M) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hCp0
      _ ≤ P := le_max_right _ _
  -- `Q ≤ cQ W_a⁴` and `N ≥ c_A Q`
  have hQ : Prop025OInputs.Qpar A 1 M P ≤ cQ * W d a ^ 4 := by
    unfold Prop025OInputs.Qpar
    rw [hcQdef]
    have hMP : M * P ≤ ((1 + Mc) * cP) * W d a ^ 2 := by
      calc M * P ≤ ((1 + Mc) * W d a) * (cP * W d a) := mul_le_mul hMW hPW (by linarith) (by positivity)
        _ = _ := by ring
    have hMP2 : (M * P) ^ 2 ≤ (((1 + Mc) * cP) * W d a ^ 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hMP 2
    have hW4 : 1 ≤ W d a ^ 4 := one_le_pow₀ hW1
    have e : pairMajorant A ^ 2 * 1 ^ 2 * M ^ 2 * P ^ 2 = pairMajorant A ^ 2 * (M * P) ^ 2 := by ring
    rw [e]
    have : pairMajorant A ^ 2 * (M * P) ^ 2 ≤ pairMajorant A ^ 2 * (((1 + Mc) * cP) * W d a ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hMP2 (sq_nonneg _)
    nlinarith
  have hQ0 : 0 ≤ Prop025OInputs.Qpar A 1 M P := by unfold Prop025OInputs.Qpar; positivity
  have hNQ : cA * Prop025OInputs.Qpar A 1 M P ≤ (N : ℝ) := by
    have hl := hlarge (N : ℝ) hNq a hcut1 hcut2
    calc cA * Prop025OInputs.Qpar A 1 M P ≤ max cA 0 * Prop025OInputs.Qpar A 1 M P :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hQ0
      _ ≤ max cA 0 * (cQ * W d a ^ 4) := mul_le_mul_of_nonneg_left hQ (le_max_right _ _)
      _ = max cA 0 * cQ * ((1 + a) ^ (d + 1)) ^ 4 := by unfold W; ring
      _ ≤ N := hl
  have hres := (hCAT K M hM1 hK hsK u₀ P hP1 hS N hN1 hNQ).2.2 k hk (Nat.le_add_right k q)
    (wvec N u) (QuantumNLS.Prop020Main.norm_wvec N u hu) 1 (by norm_num)
  rw [sub_self, norm_zero, mul_zero, add_zero] at hres
  set γ : ℝ → L2T L := fun τ => classicalFlow (positiveExtension K) M A hA.le (positiveExtension_bound K M A hK)
    (positiveExtension_selfAdjoint K hsK) τ u with hγdef
  have hspec := classicalFlow_spec (positiveExtension K) M A hA.le (positiveExtension_bound K M A hK)
    (positiveExtension_selfAdjoint K hsK) u
  refine ⟨γ, hspec.1, fun τ => (hspec.2 τ).1, ?_⟩
  have hγ1 : γ 1 = Prop022ActualProfileR117.profile (positiveExtension K) M A hA.le
      (positiveExtension_bound K M A hK) (positiveExtension_selfAdjoint K hsK) u₀ 1 :=
    classicalFlow_eq_profile _ _ _ _ _ _ u₀ 1
  have hh : 0 < h := lt_trans (QuantumNLS.Prop017Quantum.eta0_pos hκ) hηh
  rw [marginal_eq hκ u hu (μ : Measure ℝ) hh a ords t n θf k q hcont, hγ1]
  refine hres.trans (ENNReal.ofReal_le_ofReal ?_)
  -- `CAT √k N^{-1/4} (M Q^{3/2} + √Q) ≤ C N^{-1/4} W^7`
  have hNr : 0 ≤ (N : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h32 := rpow_three_halves_le hQ0 hcQ0 hW0 hQ
  have hsq := sqrt_le_of hcQ0 hW1 hQ
  have hbr : M * Prop025OInputs.Qpar A 1 M P ^ ((3 : ℝ) / 2) + Real.sqrt (Prop025OInputs.Qpar A 1 M P) ≤
      ((1 + Mc) * cQ ^ ((3 : ℝ) / 2) + Real.sqrt cQ) * W d a ^ 7 := by
    have e1 : M * Prop025OInputs.Qpar A 1 M P ^ ((3 : ℝ) / 2) ≤
        ((1 + Mc) * W d a) * (cQ ^ ((3 : ℝ) / 2) * W d a ^ 6) :=
      mul_le_mul hMW h32 (by positivity) (by positivity)
    have e2 : ((1 + Mc) * W d a) * (cQ ^ ((3 : ℝ) / 2) * W d a ^ 6) =
        (1 + Mc) * cQ ^ ((3 : ℝ) / 2) * W d a ^ 7 := by ring
    nlinarith
  have hbr0 : 0 ≤ M * Prop025OInputs.Qpar A 1 M P ^ ((3 : ℝ) / 2) + Real.sqrt (Prop025OInputs.Qpar A 1 M P) := by
    positivity
  calc CAT * Real.sqrt k * (N : ℝ) ^ (-(1 / 4 : ℝ)) *
        (M * Prop025OInputs.Qpar A 1 M P ^ ((3 : ℝ) / 2) + Real.sqrt (Prop025OInputs.Qpar A 1 M P))
      ≤ CA * Real.sqrt k * (N : ℝ) ^ (-(1 / 4 : ℝ)) *
        (M * Prop025OInputs.Qpar A 1 M P ^ ((3 : ℝ) / 2) + Real.sqrt (Prop025OInputs.Qpar A 1 M P)) := by
        gcongr
        exact le_max_left _ _
    _ ≤ CA * Real.sqrt k * (N : ℝ) ^ (-(1 / 4 : ℝ)) * (((1 + Mc) * cQ ^ ((3 : ℝ) / 2) + Real.sqrt cQ) * W d a ^ 7) := by
        gcongr
    _ = CA * Real.sqrt k * ((1 + Mc) * cQ ^ ((3 : ℝ) / 2) + Real.sqrt cQ) * (N : ℝ) ^ (-(1 / 4 : ℝ)) *
        W d a ^ 7 := by ring

end QuantumNLS.Prop025OAffine

#print axioms QuantumNLS.Prop025OAffine.affine_propagation

-- Recursive type/value audit of every own declaration: standard axioms only, and no held
-- identifier (HeldGP14Tonelli, the superseded pre-D1 `RegularCut`) in the transitive closure.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop025OAffine." then
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
  Lean.logInfo m!"Prop025OAffine aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only, no held identifiers."

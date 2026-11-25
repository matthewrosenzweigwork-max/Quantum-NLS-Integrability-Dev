import QuantumNLS.LOCAL009R23TransferSpectrum

/-! The source inverse is applied by the usual CFC to the actual transfer.
All spectral margins and operator-norm differentiability are proved here. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
noncomputable section
open Complex Set Metric
open scoped InnerProductSpace
namespace QuantumNLS.LOCAL009R23PhysicalInverse
open QuantumNLS.BetheLabels QuantumNLS.LOCAL009R22LiteralScalar
  QuantumNLS.LOCAL009R22Geometry QuantumNLS.LOCAL009R22OperatorSupport
  QuantumNLS.LOCAL009R23DiagonalAnalytic QuantumNLS.LOCAL009R23TransferSpectrum
  QuantumNLS.Ext025A7 QuantumNLS.LOCAL009R22Derivative
  QuantumNLS.LOCAL009R22Margin QuantumNLS.TransferProductCorrection

variable {L κ M ε : ℝ} [Fact (0 < L)] {N : ℕ}

abbrev Sector (L : ℝ) [Fact (0 < L)] (N : ℕ) := QuantumNLS.BetheCoefficientTransform.HN L N

def transfer (L κ ε : ℝ) [Fact (0 < L)] (N : ℕ) (z : ℂ) : Sector L N →L[ℂ] Sector L N :=
  QuantumNLS.NormalizedTransfer.normalizedTransfer L (κ*ε*N) N z

def radius (L M : ℝ) : ℝ := 2*M/(halfWidth L/2)

def normalCalc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f : ℂ → ℂ) (S : H →L[ℂ] H) : H →L[ℂ] H := cfc (p := IsStarNormal) f S

def inverseOp (L κ M ε : ℝ) [Fact (0 < L)] (N : ℕ) (z : ℂ) : Sector L N →L[ℂ] Sector L N :=
  normalCalc (spectralInverse κ L (radius L M) z) (transfer L κ ε N z)

abbrev basis (hκ : 0 < κ) (hε : 0 < ε) (hN : 0 < N) :=
  QuantumNLS.LOCAL009Round50Diagonalization.physicalBetheBasis
    (L := L) (show 0 < κ*ε*(N : ℝ) by positivity) hN

/-- Entire transfer eigenvalue, evaluated away from every actual root. -/
theorem transfer_eigen (hκ : 0 < κ) (hε : 0 < ε) (hN : 0 < N)
    (m : MArr N) {z : ℂ} (hz : ∀ j, z ≠ (arrRoots L (κ*ε) m j : ℂ)) :
    transfer L κ ε N z (basis hκ hε hN m) =
      transferS (κ*ε) L (arrRoots L (κ*ε) m) z • basis hκ hε hN m := by
  have hc : (κ*ε*(N : ℝ))/(N : ℝ) = κ*ε := fixed_coupling_parameter hN
  have hp := QuantumNLS.UnconditionalBetheBasis.transfer_physicalBasis
    (L := L) (show 0 < κ*ε*(N : ℝ) by positivity) hN z m
  change transfer L κ ε N z (basis hκ hε hN m) = _ at hp
  rw [hp]
  congr 1
  unfold QuantumNLS.NormalityBridge.eigen
  have hroot (i : Fin N) : QuantumNLS.BetheSmooth.sourceRoots L
      (QuantumNLS.NormalityBridge.label m).1 (κ*ε*(N : ℝ)/(N : ℝ)) i =
      arrRoots L (κ*ε) m (Fin.rev i) := by
    rw [hc, QuantumNLS.RootMeasureTransfer.label_val]
    exact QuantumNLS.BetheLabels.sourceRoots_eq_roots_rev (Fact.out : 0 < L) (mul_pos hκ hε) _ i
  rw [QuantumNLS.BetheSpectralContinuity.spectralValue_nonpole L
    (QuantumNLS.NormalityBridge.cpos (show 0 < κ*ε*(N : ℝ) by positivity) hN)
    (QuantumNLS.NormalityBridge.label m).2 z (fun j => by rw [hroot]; exact hz _)]
  unfold QuantumNLS.TransferSeparation.sFun transferS
  simp only [hroot]
  rw [hc]
  have p1 := Equiv.prod_comp Fin.revPerm
    (fun j => (1 + I * ((κ*ε : ℝ) : ℂ) / (z-(arrRoots L (κ*ε) m j : ℂ))))
  have p2 := Equiv.prod_comp Fin.revPerm
    (fun j => (1 - I * ((κ*ε : ℝ) : ℂ) / (z-(arrRoots L (κ*ε) m j : ℂ))))
  simp only [Fin.revPerm_apply] at p1 p2
  rw [p1,p2]
  congr 2
  ring

theorem source_small (hsmall : κ*L*M ≤ 1/1000000) :
    κ*M/(halfWidth L/2) ≤ 1/10000 := by
  have hL : 0 < L := Fact.out
  have heq : κ*M/(halfWidth L/2) = 4*(κ*L*M)/Real.pi := by
    unfold halfWidth
    field_simp
    ring
  rw [heq]
  apply (div_le_iff₀ Real.pi_pos).mpr
  nlinarith [Real.pi_gt_three]

theorem actual_band_separation (hκ : 0 < κ) (hε : 0 < ε) (hN : 0 < N)
    (hsmall : κ*L*M ≤ 1/1000000) (hbudget : ε*N ≤ M)
    (n : ℤ) (m : MArr N) {z : ℂ} (hz : z ∈ band (momentum L n) (halfWidth L)) (j : Fin N) :
    halfWidth L/2 ≤ ‖z-(arrRoots L (κ*ε) m j : ℂ)‖ := by
  have hL : 0 < L := Fact.out
  have ha : 0 < halfWidth L := by unfold halfWidth; positivity
  apply band_root_separation ha (hq := ⟨correctedInt (labelsEquivArr.symm m) j-n, ?_⟩) hz
  have heq : momentum L n + 4*halfWidth L*(correctedInt (labelsEquivArr.symm m) j-n : ℤ) =
      momentum L (correctedInt (labelsEquivArr.symm m) j) := by
    unfold momentum halfWidth
    push_cast
    field_simp
    ring
  rw [heq]
  exact actual_root_confinement hκ (Fact.out : 0 < L) hsmall hN hε hbudget m j

/-- Both the ordinary CFC and its full operator-norm derivative have the
printed inverse scalar entries, throughout the open contour band. -/
theorem inverseOp_spec (hκ : 0 < κ) (hM : 0 < M) (hsmall : κ*L*M ≤ 1/1000000)
    (hN : 0 < N) (hε : 0 < ε) (hεM : ε ≤ M) (hbudget : ε*N ≤ M)
    (n : ℤ) {z : ℂ} (hz : z ∈ band (momentum L n) (halfWidth L)) :
    (∀ m, inverseOp L κ M ε N z (basis hκ hε hN m) =
      inverseTransfer κ L (radius L M) ε (arrRoots L (κ*ε) m) z • basis hκ hε hN m) ∧
    DifferentiableAt ℂ (inverseOp L κ M ε N) z ∧
    (∀ m, deriv (inverseOp L κ M ε N) z (basis hκ hε hN m) =
      deriv (inverseTransfer κ L (radius L M) ε (arrRoots L (κ*ε) m)) z • basis hκ hε hN m) ∧
    ‖inverseOp L κ M ε N z‖ ≤ radius L M := by
  have hL : 0 < L := Fact.out
  let U := band (momentum L n) (halfWidth L)
  let d := halfWidth L/2
  have hd : 0 < d := by dsimp [d,halfWidth]; positivity
  have hR : 0 < radius L M := by unfold radius halfWidth; positivity
  have hs : κ*M/d ≤ 1/10000 := source_small hsmall
  have hr : κ*radius L M ≤ 1/1000 := by
    calc
      κ*radius L M = 2*(κ*M/d) := by unfold radius; dsimp [d]; ring
      _ ≤ 1/1000 := by linarith
  have hU : IsOpen U := band_open _ _
  have hexp : ∀ z ∈ U, ‖Complex.exp (I*z*L)‖ ≤ 8 :=
    fun z hz => source_phase_bound (Fact.out : 0 < L) n hz
  have hgap : ∀ z ∈ U, 1/2 ≤ ‖1-Complex.exp (I*z*L)‖ :=
    fun z hz => source_gap_bound (Fact.out : 0 < L) n hz
  have hsep : ∀ (m : MArr N) z, z ∈ U → ∀ j, d ≤ ‖z-(arrRoots L (κ*ε) m j : ℂ)‖ :=
    fun m z hz j => actual_band_separation hκ hε hN hsmall hbudget n m hz j
  have hne : ∀ (m : MArr N) z, z ∈ U → ∀ j, z ≠ (arrRoots L (κ*ε) m j : ℂ) := by
    intro m z hz j he
    have := hsep m z hz j
    rw [he,sub_self,norm_zero] at this
    linarith
  have htarget : ∀ (m : MArr N) z, z ∈ U → ‖transferS (κ*ε) L (arrRoots L (κ*ε) m) z-spectralMap κ L z 0‖ <
      3/4*‖spectralLinear κ L z‖*radius L M := by
    intro m z hz
    exact transfer_target_margin hκ hM hd hs hN hε.le hεM hbudget _ (hsep m z hz) (hexp z hz) (hgap z hz)
  have he : ∀ z ∈ U, ∀ m, inverseOp L κ M ε N z (basis hκ hε hN m) =
      inverseTransfer κ L (radius L M) ε (arrRoots L (κ*ε) m) z • basis hκ hε hN m := by
    intro z hz m
    exact inverse_cfc_eigen (basis hκ hε hN) (transfer L κ ε N z)
      (fun m => transferS (κ*ε) L (arrRoots L (κ*ε) m) z)
      (fun m => transfer_eigen hκ hε hN m (hne m z hz)) hκ hR hr hU hexp hgap hz
      (fun m => (transfer_strict_spectral_margin hκ hM hd hs hN hε.le hεM hbudget _
        (hsep m z hz) (hexp z hz) (hgap z hz)).le) m
  have hb : ∀ (m : MArr N) z, z ∈ U → ‖inverseTransfer κ L (radius L M) ε (arrRoots L (κ*ε) m) z‖ ≤ radius L M := by
    intro m z hz
    exact (mem_ball_zero_iff.mp
      (local009_application κ L hκ hR hr hU hexp hgap hz (htarget m z hz)).1).le
  have ha : ∀ (m : MArr N) z, z ∈ U → AnalyticAt ℂ (inverseTransfer κ L (radius L M) ε (arrRoots L (κ*ε) m)) z :=
    fun m z hz => inverseTransfer_analyticAt hκ hR hr hU hexp hgap _ hz (hne m z hz) (htarget m z hz)
  have hl := analytic_lift (basis hκ hε hN) (inverseOp L κ M ε N)
    (fun m => inverseTransfer κ L (radius L M) ε (arrRoots L (κ*ε) m)) hU hR.le he ha hb hz
  exact ⟨he z hz,hl.1,hl.2,norm_le_of_eigen (basis hκ hε hN) _ _ (he z hz) hR.le (fun m => hb m z hz)⟩

end QuantumNLS.LOCAL009R23PhysicalInverse

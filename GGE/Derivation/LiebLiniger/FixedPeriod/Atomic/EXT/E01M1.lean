import LiebLiniger.FixedPeriod.Atomic.EXT.FlowRotationC1
import NlsGge.Birkhoff.S01Equivariance38

/-! # The actual NLS Hamiltonian depends on the actions on H¹

Equal actions give equal Hamiltonians on each finite Birkhoff plane.
Symmetric Birkhoff truncations converge in h¹; continuity of the same actual
inverse and of the literal physical Hamiltonian passes that equality to H¹.
The minus-reflected Fourier convention is retained by `reflIso38`.
-/

set_option autoImplicit false
noncomputable section
namespace LiebLiniger.FixedPeriod.EXT

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
open scoped Topology

local notation "B0" => NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38

/-- Equal actions on a finite plane give equal literal Hamiltonians. Polar
transitivity includes zero coordinates and the empty plane. -/
private theorem e01m1_HLambda_eq (Λ : Finset ℤ) (w v : Λ → ℂ)
    (h : ∀ i, ‖w i‖ ^ 2 = ‖v i‖ ^ 2) : HΛ Λ w = HΛ Λ v := by
  have ht := finitePlane_phase_transitive38 Λ w v h
  have hh := HLambda_phaseInvariant38 Λ w (fun i => (v i).arg - (w i).arg)
  change HΛ Λ (finitePlanePhase38 Λ (fun i => (v i).arg - (w i).arg) w) = HΛ Λ w at hh
  rw [ht] at hh
  exact hh.symm

/-- Inserting the restricted coordinates is exactly the existing symmetric
h¹ truncation, with its proved norm convergence. -/
private theorem e01m1_insert_trunc (N : ℕ) (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    finitePlaneInsert38 (symmetricModes N) (fun i => carrierCoe38 ((1 : ℕ) : ℝ) z i) =
      truncC38 ((1 : ℕ) : ℝ) N z := by
  classical
  apply carrierExt38
  funext n
  rw [finitePlaneInsert38_coe, carrierCoe38_truncC38]
  by_cases hn : n ∈ symmetricModes N
  · simp only [extZero38_apply_of_mem _ hn, hn, ↓reduceIte]
  · simp only [extZero38_apply_of_not_mem _ hn, hn, ↓reduceIte]

/-- The finite-plane energies of a physical H¹ field's Birkhoff truncations
converge to its actual physical energy. All maps act on the genuine h¹ carrier. -/
private theorem e01m1_tendsto_HLambda (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Filter.Tendsto (fun N : ℕ => HΛ (symmetricModes N) (fun i => (B0).Φ u i))
      Filter.atTop (𝓝 (ham (physicalFourier u))) := by
  let x : SobolevCarrier38 ((1 : ℕ) : ℝ) :=
    carrierMk38 ((1 : ℕ) : ℝ) (fourierSeq38 u) ((fourierSeq38_mem_iff _ u).2 (by simpa only [Nat.cast_one] using hu))
  let z : SobolevCarrier38 ((1 : ℕ) : ℝ) := (B0).TC 1 x
  have hz : carrierCoe38 ((1 : ℕ) : ℝ) z = (B0).Φ u := rfl
  have hi : (B0).TinvC 1 z = x := (B0).TinvC_TC 1 x
  have hr : carrierCoe38 ((1 : ℕ) : ℝ) (reflIso38 ((1 : ℕ) : ℝ) x) = physicalFourier u := by
    funext n
    change -fourierSeq38 u (-n) = physicalFourier u n
    rw [fourierSeq38_apply, neg_neg, neg_neg]
  have hc : Continuous (fun a : SobolevCarrier38 ((1 : ℕ) : ℝ) =>
      ham (carrierCoe38 ((1 : ℕ) : ℝ) (reflIso38 ((1 : ℕ) : ℝ) ((B0).TinvC 1 a)))) :=
    continuous_ham_coe.comp ((reflIso38 ((1 : ℕ) : ℝ)).continuous.comp ((B0).continuous_TinvC 1))
  have ht := (hc.tendsto z).comp (tendsto_truncC38 ((1 : ℕ) : ℝ) z)
  rw [hi, hr] at ht
  have he (N : ℕ) : HΛ (symmetricModes N) (fun i => (B0).Φ u i) =
      ham (carrierCoe38 ((1 : ℕ) : ℝ) (reflIso38 ((1 : ℕ) : ℝ) ((B0).TinvC 1 (truncC38 ((1 : ℕ) : ℝ) N z)))) := by
    rw [HΛ_eq_inverseCarrier38, ← hz, e01m1_insert_trunc,
      NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38_top]
  exact ht.congr (fun N => (he N).symm)

/-- For any two physical L² fields with H¹ Fourier coefficients, equality of
every actual Birkhoff action implies equality of their literal NLS Hamiltonians.
There are no finite-support, nonzero-coordinate, or extra regularity premises. -/
theorem actual_hamiltonian_eq_of_actions_H1_38 :
    ∀ (u v : NlsGge.Pilot.PhysicalL2),
      NlsGge.Pilot.SobolevSquareSummable 1 (NlsGge.Pilot.physicalFourier u) →
      NlsGge.Pilot.SobolevSquareSummable 1 (NlsGge.Pilot.physicalFourier v) →
      (∀ n : ℤ,
        ‖NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38.Φ u n‖ ^ 2 =
        ‖NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38.Φ v n‖ ^ 2) →
      NlsGge.NLS38.ham (NlsGge.Pilot.physicalFourier u) =
        NlsGge.NLS38.ham (NlsGge.Pilot.physicalFourier v) := by
  intro u v hu hv h
  exact tendsto_nhds_unique_of_forall (e01m1_tendsto_HLambda u hu)
    (e01m1_tendsto_HLambda v hv)
    (fun N => e01m1_HLambda_eq (symmetricModes N) _ _ (fun i => h i))

end LiebLiniger.FixedPeriod.EXT

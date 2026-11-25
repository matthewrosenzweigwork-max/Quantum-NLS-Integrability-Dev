import QuantumNLS.REF88SH1Endpoint
import QuantumNLS.VarFinal

/-! R-EF8C2837 item (iv), physical_cubic.tex:316–330: the H¹ limit passage.
`pair_identification_of_approximants` is an explicit reduction from the finite physical
pair identity of item (iii). It proves the target H¹ identification; the finite identity
is required only at the approximants, never at the target. It is not asserted proved here.
All hη, hW2, varying-coupling bounds and donor conditions are derived.
Author sol_multi round23; independent reviewer terra_review. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace QuantumNLS.REF88SH1Identification
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Sobolev
open QuantumNLS.ActualGapDataR26 (Data)
open QuantumNLS.F04SelBand (Mu II)
open QuantumNLS.RootIndexedMasses (masses)
open QuantumNLS.ActionTorus (PosL1)
open QuantumNLS.BetheLabels (arrRoots)
variable {L κ : ℝ} [Fact (0 < L)]

/-- The full printed limit argument, with the finite item-(iii) identity explicit.
The H¹ approximating sequence is supplied by H1_approximationInput. The conclusion
holds for every target response datum, in particular the datum in the actual-law theorem. -/
theorem pair_identification_of_approximants (hκ : 0 < κ) (ν : ℤ → PosL1 → ℝ)
    (hν : ∀ n, ContinuousOn (ν n) {a : PosL1 | 0 < a.1 n})
    (v : ℕ → H02 L 1) (u : H02 L 1) (hv : Tendsto v atTop (𝓝 u))
    {a b : ℤ} (hab : b < a) (ha : 0 < II hκ u.val a) (hb : 0 < II hκ u.val b)
    (hav : ∀ j, 0 < II hκ (v j).val a) (hbv : ∀ j, 0 < II hκ (v j).val b)
    (finite_pair : ∀ (j : ℕ) (hKj : 0 < κ * ‖(v j).val‖ ^ 2)
      (D : Data hKj (FullMass.unitDir (v j).val)),
      ν a (masses hκ (v j).val) - ν b (masses hκ (v j).val) = D.omega a b)
    (hK : 0 < κ * ‖u.val‖ ^ 2) (D0 : Data hK (FullMass.unitDir u.val)) :
    ν a (masses hκ u.val) - ν b (masses hκ u.val) = D0.omega a b := by
  have hu := REF88SH1Approximation.nonzero_of_active hκ ha
  have hv0 : ∀ j, (v j).val ≠ 0 := fun j => REF88SH1Approximation.nonzero_of_active hκ (hav j)
  -- Select actual gaps with donor b and receiver a; minus that gap is receiver-minus-donor.
  obtain ⟨hK',hKs,D,k,η,hmono,hk,hcoupling,hocc,hη,hW,hgap⟩ :=
    REF88SH1Endpoint.H1_actual_endpoint hκ v u hv hu hv0 (ne_of_lt hab) hbv hav
  have hL2 := ((H02.toL2 (L := L) (by norm_num : (0 : ℝ) ≤ 1)).continuous.tendsto u).comp hv
  have hmasses : Tendsto (fun j => masses hκ (v j).val) atTop (𝓝 (masses hκ u.val)) :=
    (DEF014Continuity.continuous_physical_masses hκ).tendsto u.val |>.comp hL2
  have hfa : Tendsto (fun j => ν a (masses hκ (v j).val)) atTop (𝓝 (ν a (masses hκ u.val))) := by
    apply ((hν a) _ ha).tendsto.comp
    exact tendsto_nhdsWithin_iff.2 ⟨hmasses,Eventually.of_forall fun j => hav j⟩
  have hfb : Tendsto (fun j => ν b (masses hκ (v j).val)) atTop (𝓝 (ν b (masses hκ u.val))) := by
    apply ((hν b) _ hb).tendsto.comp
    exact tendsto_nhdsWithin_iff.2 ⟨hmasses,Eventually.of_forall fun j => hbv j⟩
  let p0 := ν a (masses hκ u.val) - ν b (masses hκ u.val)
  have homega : Tendsto (fun n => (D (k n)).omega b a) atTop (𝓝 (-p0)) := by
    have he : ∀ n, (D (k n)).omega b a =
        -(ν a (masses hκ (v (k n)).val) - ν b (masses hκ (v (k n)).val)) := by
      intro n
      rw [REF88QuantumDef.omega_swap, ← finite_pair (k n) (hKs (k n)) (D (k n))]
    simpa only [he,p0,Function.comp_def] using ((hfa.sub hfb).comp hk).neg
  have hg : Tendsto (fun n => F02Tightness.gap L (κ * ‖(v (k n)).val‖ ^ 2) b a (η n))
      atTop (𝓝 (-p0)) := by
    simpa only [sub_add_cancel,zero_add] using hgap.add homega
  have htarget_b : 0 < II hK (FullMass.unitDir u.val) b := by
    have hi := REF88QuantumDef.II_unitDir hκ hu hK b
    have hp : 0 < ‖u.val‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.2 hu)
    nlinarith
  have htarget_a : 0 < II hK (FullMass.unitDir u.val) a := by
    have hi := REF88QuantumDef.II_unitDir hκ hu hK a
    have hp : 0 < ‖u.val‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.2 hu)
    nlinarith
  obtain ⟨η',hdonor,heq⟩ := REF88SH1Endpoint.patch_donor hK (FullMass.unitDir u.val) η hη htarget_b
  have hη' : Tendsto (fun n => ∑' m : ℤ, |(((η' n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) -
      II hK (FullMass.unitDir u.val) m|) atTop (𝓝 0) :=
    hη.congr' (heq.mono fun n hn => by dsimp only; rw [hn])
  have hW' : Tendsto (fun n => QuantileTransport.W2 (QuantileTransport.empirical (n + 1)
      (arrRoots L ((κ * ‖(v (k n)).val‖ ^ 2) / ((n : ℝ) + 1)) (η' n)))
        (Mu hK (FullMass.unitDir u.val))) atTop (𝓝 0) :=
    hW.congr' (heq.mono fun n hn => by dsimp only; rw [hn])
  have hg' : Tendsto (fun n => F02Tightness.gap L (κ * ‖(v (k n)).val‖ ^ 2) b a (η' n))
      atTop (𝓝 (-p0)) := hg.congr' (heq.mono fun n hn => by dsimp only; rw [hn])
  let Ks : ℕ → ℝ := fun n => κ * ‖(v (k n)).val‖ ^ 2
  let K : ℝ := κ * ‖u.val‖ ^ 2
  have hbd : ∀ᶠ n : ℕ in atTop, K / 2 ≤ Ks n ∧ Ks n ≤ 2 * K := by
    filter_upwards [hcoupling.eventually (lt_mem_nhds (show K / 2 < K by dsimp [K]; linarith)),
      hcoupling.eventually (gt_mem_nhds (show K < 2 * K by dsimp [K]; linarith))] with n h1 h2
    exact ⟨h1.le,h2.le⟩
  have hactual := VarFinal.variable_coupling hK (FullMass.unitDir u.val) (FullMass.norm_unitDir hu)
    D0.bulk hcoupling (κm := K / 2) (κp := 2 * K) (by dsimp [K]; linarith) hbd
    hab htarget_b htarget_a η' hdonor hη' (Or.inl hW')
    D0.response D0.fm D0.pull D0.xl (fun _ _ _ _ _ _ => D0.phase _)
  have hforward : Tendsto (fun n => ∑ i, arrRoots L (Ks n / ((n : ℝ) + 1))
        (AdjacentResponse.transfer (η' n) (hdonor n) a) i ^ 2 -
      ∑ i, arrRoots L (Ks n / ((n : ℝ) + 1)) (η' n) i ^ 2) atTop (𝓝 p0) := by
    have hh := hg'.neg
    simp only [neg_neg] at hh
    refine hh.congr fun n => ?_
    simp only [F02Tightness.gap,dif_pos (hdonor n),F02Tightness.Q2,Nat.cast_add,Nat.cast_one]
    ring
  exact tendsto_nhds_unique hforward hactual.2

#print axioms pair_identification_of_approximants
end QuantumNLS.REF88SH1Identification

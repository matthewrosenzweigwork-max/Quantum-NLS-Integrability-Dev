import QuantumNLS.RiccatiODEConverse
/-! integrator-authored trusted spec for R-3FEAD88B values:prop:riccati, uniqueness clause (review record r36 FULL support): headline statement(s) copied verbatim from RiccatiODEConverse (QuantumNLS.RiccatiODEConverse). -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.R3FEASpecU
open QuantumNLS.RiccatiODEConverse
open Set
open QuantumNLS.RiccatiPointwiseCoef
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPicardBall
open QuantumNLS.RiccatiPointwiseDisc QuantumNLS.RiccatiPointwiseRep
open QuantumNLS.RiccatiClassical QuantumNLS.RiccatiChargeIdent
open QuantumNLS.RiccatiExpansions QuantumNLS.RiccatiRemainder
open QuantumNLS.RiccatiChargeLevels QuantumNLS.RiccatiDerivative
open QuantumNLS.SmoothScalarMomentsPrerequisite

set_option maxHeartbeats 8000000 in
theorem represented_periodic_ode_unique_spec {L a S δ : ℝ} [Fact (0 < L)] {M : ℕ}
    {K : Set ℝ} {f : ℝ → ℂ} {hL : 0 < L} {ha : 1 / 2 < a}
    (out : LocalOutput L f M a S δ K hL ha)
    {κ : ℝ} (hκ : κ ∈ K) {z : ℂ} (hR : out.R ≤ ‖z‖)
    (hsec : δ * ‖z‖ ≤ z.im) (hz : 0 < z.im) {p : Ell2 × Ell2} (hp : p ∈ out.V)
    (r : ℝ → ℂ) (q : Ell2) (hrep : physRep L a q = r)
    (hsmall : ‖q‖ ≤ out.C / z.im)
    (hr : ∀ t, HasDerivAt r
      (Complex.I * z * r t + physRep L a (lowT L a S p.1) t
        - (κ : ℂ) * physRep L a (lowT L a S p.2) t * r t ^ 2) t) :
    riccatiT hL ha hz (κ / L) (lowT L a S p.1) (lowT L a S p.2) q = q ∧
    q = out.rf κ z p ∧ r = physRep L a (out.rf κ z p) := by
  exact QuantumNLS.RiccatiODEConverse.represented_periodic_ode_unique out hκ hR hsec hz hp r q hrep hsmall hr

end QuantumNLS.R3FEASpecU
#print axioms QuantumNLS.R3FEASpecU.represented_periodic_ode_unique_spec

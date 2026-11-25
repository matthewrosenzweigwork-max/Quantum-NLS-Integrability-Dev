import NlsGge.GK38.GradFundamentalDefs

/- G1-067 HOST (proof development, AUTHOR; not reviewed). Target module NlsGge/ThirdConsultation/G1/G1WronskianHost.lean.
   Hosts the design names wedge, symmetricPair, bilinearPair. Bodies are DEFINITIONS/G1.lean.md lines 286-288
   of root/gpt6pro_followup5/handoff/definitions_design_20261027, copied byte-identically.
   Shared host: G1-067 and G1-068 import this module and must not redeclare these names. -/
set_option autoImplicit false

open NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def wedge (a b : PairVec38) : ℂ := a 0*b 1-a 1*b 0
def symmetricPair (a b : PairVec38) : ℂ := a 0*b 1+a 1*b 0
def bilinearPair (a b : PairVec38) : ℂ := a 0*b 0+a 1*b 1

end
end NlsGge.GKDefinitionDesign

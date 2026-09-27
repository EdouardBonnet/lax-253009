import Lax253009.RandomizedContainments
import Lax253009Proofs.RegisteredBridge.RandomizedContainments

namespace Lax253009Proofs

/--
---
conclusion: Lax253009.RandomizedContainments.RP_subset_NP
---
The certificate is a complete random tape. Its verifier parses the registered
pair encoding, checks the tape length, and simulates the registered procedure.
-/
theorem rp_subset_np :
    Lax666725.OneSidedError.RP ⊆ Lax434930.NondeterministicPolynomialTime.NP :=
  RegisteredBridge.registered_RP_subset_NP

/--
---
conclusion: Lax253009.RandomizedContainments.ZPP_subset_NP
---
Turning failure into rejection gives RP membership; the explicit random-tape
verifier then supplies an NP certificate.
-/
theorem zpp_subset_np :
    Lax666725.ZeroError.ZPP ⊆ Lax434930.NondeterministicPolynomialTime.NP :=
  RegisteredBridge.registered_ZPP_subset_NP

end Lax253009Proofs

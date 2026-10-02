import Lax323828.RandomizedContainments
import Lax323828Proofs.RegisteredBridge.RandomizedContainments
import Lax666725.ZPPSubsetOneSided

namespace Lax323828Proofs

/--
---
conclusion: Lax323828.RandomizedContainments.RP_subset_NP
---
The certificate is a complete random tape. Its verifier parses the registered
pair encoding, checks the tape length, and simulates the registered procedure.
-/
theorem rp_subset_np :
    Lax666725.OneSidedError.RP ⊆ Lax434930.NondeterministicPolynomialTime.NP :=
  RegisteredBridge.registered_RP_subset_NP

/--
---
conclusion: Lax323828.RandomizedContainments.ZPP_subset_NP
---
Turning failure into rejection gives RP membership; the explicit random-tape
verifier then supplies an NP certificate.
-/
theorem zpp_subset_np :
    Lax666725.ZeroError.ZPP ⊆ Lax434930.NondeterministicPolynomialTime.NP :=
  fun _ hL ↦ Lax323828.RandomizedContainments.RP_subset_NP
    (Lax666725.ZPPSubsetOneSided.ZPP_subset_RP_inter_coRP hL).1

end Lax323828Proofs

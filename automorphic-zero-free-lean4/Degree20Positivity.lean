import Degree20LeafLLL
import Degree20LeafLLRL
import Degree20LeafLLRR
import Degree20LeafLRLL
import Degree20LeafLRLR
import Degree20LeafLRRL
import Degree20LeafLRRR

namespace EllipticBernstein.SmoothDegree20
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
theorem hpLLR : Degree20.positiveOn NLLR :=
  Degree20.glueY NLLR hpLLRL hpLLRR
theorem hpLRL : Degree20.positiveOn NLRL :=
  Degree20.glueY NLRL hpLRLL hpLRLR
theorem hpLRR : Degree20.positiveOn NLRR :=
  Degree20.glueY NLRR hpLRRL hpLRRR
theorem hpLL : Degree20.positiveOn NLL :=
  Degree20.glueX NLL hpLLL hpLLR
theorem hpLR : Degree20.positiveOn NLR :=
  Degree20.glueX NLR hpLRL hpLRR
theorem hpL : Degree20.positiveOn NL :=
  Degree20.glueY NL hpLL hpLR
end EllipticBernstein.SmoothDegree20

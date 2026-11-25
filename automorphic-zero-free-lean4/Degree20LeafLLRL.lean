import Degree20Cuts

namespace EllipticBernstein.SmoothDegree20
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem hpLLRL : Degree20.positiveOn NLLRL :=
  Degree20.cert_sound 8 true _ (by decide +kernel)
end EllipticBernstein.SmoothDegree20

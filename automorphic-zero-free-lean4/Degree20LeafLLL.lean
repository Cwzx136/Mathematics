import Degree20Cuts

namespace EllipticBernstein.SmoothDegree20
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem hpLLL : Degree20.positiveOn NLLL :=
  Degree20.cert_sound 9 false _ (by decide +kernel)
end EllipticBernstein.SmoothDegree20

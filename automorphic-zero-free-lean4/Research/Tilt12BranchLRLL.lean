import Research.Tilt12Cuts

namespace EllipticBernstein.Tilt12
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

theorem hpLRLL : Degree12.positiveOn NLRLL := Degree12.cert_sound 0 true _ (by decide +kernel)
end EllipticBernstein.Tilt12

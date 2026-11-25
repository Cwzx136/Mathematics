import Research.Tilt12BranchLL
import Research.Tilt12BranchLRLL
import Research.Tilt12BranchLRLR
import Research.Tilt12BranchLRRL
import Research.Tilt12BranchLRRR

namespace EllipticBernstein.Tilt12
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

theorem hpLRL : Degree12.positiveOn NLRL := Degree12.glueY _ hpLRLL hpLRLR
theorem hpLRR : Degree12.positiveOn NLRR := Degree12.glueY _ hpLRRL hpLRRR
theorem hpLR : Degree12.positiveOn NLR := Degree12.glueX _ hpLRL hpLRR
theorem hpL : Degree12.positiveOn NL := Degree12.glueY _ hpLL hpLR
end EllipticBernstein.Tilt12

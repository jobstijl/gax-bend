# The rounding-error theorem's bound, k u absev (proofs/err.bend), and the
# tracked bound (Err.track, api/track.bend) hold for F32 on sampled inputs: 20000 per kernel, PGA3D products and CGA3D
# distances far from the origin. The control shows the check can fail:
# the worst case comes within a factor 4 of the bound. The bench files
# print the full figures.
import Base
import ../bench/measure_pga3d.bend as P
import ../bench/measure_cga3d.bend as C

# within t of the theorem's bound, and within the tracked bound
# (api/track.bend, from computed quantities only)
def okp(+t: F32, a: P.Acc) -> Bool:
  match a:
    case P.Acc{mx, sum, n, grow, trk}:
      Bool.and(F32.is_le(mx, t), F32.is_le(trk, 1.0))

def okc(a: C.Acc) -> Bool:
  match a:
    case C.Acc{bound, rel, kappa}:
      F32.is_le(bound, 1.0)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("Motor.transform.Point within bound: " ++ Bool.show(okp(1.0, P.run.mtp(20000n, 7, P.mtp.k(), P.acc0()))))
    IO.print("Motor.gp.Motor within bound: " ++ Bool.show(okp(1.0, P.run.mm(20000n, 7, P.mm.k(), P.acc0()))))
    IO.print("Point.vee.Point within bound: " ++ Bool.show(okp(1.0, P.run.pvp(20000n, 7, P.pvp.k(), P.acc0()))))
    IO.print("CGA3D Vector.dot.Vector at R = 1e4 within bound: " ++ Bool.show(okc(C.run(20000n, 10000.0, 7, C.k(), C.Acc{0.0, 0.0, 0.0}))))
    IO.print("control, Point.vee.Point within a quarter of the bound: " ++ Bool.show(okp(0.25, P.run.pvp(20000n, 7, P.pvp.k(), P.acc0()))))
#|Motor.transform.Point within bound: True
#|Motor.gp.Motor within bound: True
#|Point.vee.Point within bound: True
#|CGA3D Vector.dot.Vector at R = 1e4 within bound: True
#|control, Point.vee.Point within a quarter of the bound: False

# Four pixels of demos/raytrace.bend, as packed 0xRRGGBB colours: the sky
# (top left), the red ball lit (centre), the floor (bottom left) and the
# red ball's underside, which the light does not reach (ambient only). The demo itself prints a timing, so
# the gate checks it through these.
import Base
import ../demos/raytrace.bend as R

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(U32.show(R.pack(R.pixel(256.0, 0.0, 0.0))))
    IO.print(U32.show(R.pack(R.pixel(256.0, 128.0, 128.0))))
    IO.print(U32.show(R.pack(R.pixel(256.0, 0.0, 250.0))))
    IO.print(U32.show(R.pack(R.pixel(256.0, 128.0, 196.0))))
#|13362674
#|10693924
#|8882045
#|2230535

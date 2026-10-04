# A CGA3D ray tracer, drawn into Bend's quadtree Image and written as a PPM.
#   bend demos/raytrace.bend demos/raytrace.ppm
#
# The rule (brief §2a.9): geometry through the library, no raw trig or
# square roots here. A ray is the line through the eye and a pixel's point
# (p ^ q ^ ei); it meets a sphere in a point pair (s ⌋ l) and the ground
# in a flat point; brightness is a dot product of directions. Floats appear
# only at the boundary: pixel coordinates in, colour channels out. What the
# library had to gain for this is in docs/friction.md.
import Base
import ../api/cga3d.bend as C
import ../algebras/cga3d/kinds.bend as K

# Scene
# -----

def eye() -> K.Vector<F32>:
  C.Point.xyz(0.0, 0.6, 3.5)

def light() -> K.Vector<F32>:
  C.Direction.unit(C.Direction.xyz(F32.neg(1.0), 1.6, 1.2))

def floor() -> K.Vector<F32>:
  C.Plane.normal(0.0, 1.0, 0.0, F32.neg(0.6))

# a ball: a sphere and a colour (a direction: r, g, b)
type Ball is Data:
  Ball{s: K.Vector<F32>, c: K.Vector<F32>}

def balls() -> List<&2, Ball>:
  [ Ball{C.Sphere.at(0.0, 0.4, 0.0, 1.0), C.Direction.xyz(0.9, 0.25, 0.2)},
    Ball{C.Sphere.at(F32.neg(1.9), 0.0, F32.neg(0.9), 0.6), C.Direction.xyz(0.2, 0.8, 0.3)},
    Ball{C.Sphere.at(1.8, 0.1, F32.neg(1.2), 0.7), C.Direction.xyz(0.25, 0.4, 0.95)} ]

# Hits
# ----

# a hit: squared distance from the eye, point, normal, colour
type Hit is Data:
  Hit{d: F32, p: K.Vector<F32>, n: K.Vector<F32>, c: K.Vector<F32>}

def Hit.none() -> Hit:
  Hit{1.0e30, C.Point.xyz(0.0, 0.0, 0.0), C.Direction.xyz(0.0, 1.0, 0.0), C.Direction.xyz(0.0, 0.0, 0.0)}

def Hit.d(h: Hit) -> F32:
  match h:
    case Hit{d, p, n, c}:
      d

def Hit.nearer(+a: Hit, +b: Hit) -> Hit:
  Bool.pick(Hit, F32.is_lt(Hit.d(a), Hit.d(b)), a, b)

# whether q lies ahead of the eye along the ray direction r
def ahead(+o: K.Vector<F32>, +r: K.Vector<F32>, q: K.Vector<F32>) -> Bool:
  F32.is_lt(0.0, C.Direction.dot(C.Direction.between(o, q), r))

# the hit at point q of the ball b, if q is ahead
def Hit.at(+o: K.Vector<F32>, +r: K.Vector<F32>, +s: K.Vector<F32>, +c: K.Vector<F32>, +q: K.Vector<F32>) -> Hit:
  Bool.pick(Hit, ahead(o, r, q), Hit{C.Point.distance2(o, q), q, C.Direction.between(C.Sphere.center(s), q), c}, Hit.none())

def Hit.pair(+o: K.Vector<F32>, +r: K.Vector<F32>, +s: K.Vector<F32>, +c: K.Vector<F32>, pq: K.Vector<F32> & K.Vector<F32>) -> Hit:
  match pq:
    case (p, q):
      Hit.nearer(Hit.at(o, r, s, c, p), Hit.at(o, r, s, c, q))

def Hit.ball(+o: K.Vector<F32>, +r: K.Vector<F32>, +l: K.Trivector<F32>, b: Ball) -> Hit:
  match b:
    case Ball{+s, +c}:
      +pp = C.Line.meet(s, l)
      Bool.pick(Hit, C.PointPair.real(pp), Hit.pair(o, r, s, c, C.PointPair.points(pp)), Hit.none())

def Hit.balls(+o: K.Vector<F32>, +r: K.Vector<F32>, +l: K.Trivector<F32>, bs: List<&2, Ball>, acc: Hit) -> Hit:
  match bs:
    case Nil{}:
      acc
    case b <> t:
      Hit.balls(o, r, l, t, Hit.nearer(Hit.ball(o, r, l, b), acc))

def Hit.floor(+o: K.Vector<F32>, +r: K.Vector<F32>, +l: K.Trivector<F32>) -> Hit:
  +q = C.FlatPoint.point(C.Line.meet(floor(), l))
  Bool.pick(Hit, ahead(o, r, q), Hit{C.Point.distance2(o, q), q, C.Direction.xyz(0.0, 1.0, 0.0), C.Direction.xyz(0.7, 0.7, 0.65)}, Hit.none())

# whether the light is blocked from q: some ball meets the ray from q to
# the light ahead of q
def blocked.ball(+q: K.Vector<F32>, +l: K.Trivector<F32>, b: Ball) -> Bool:
  match b:
    case Ball{s, c}:
      Bool.pick(Bool, F32.is_lt(Hit.d(Hit.ball(q, light(), l, Ball{s, c})), 1.0e29), True{}, False{})

def blocked(+q: K.Vector<F32>, +l: K.Trivector<F32>, bs: List<&2, Ball>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case b <> t:
      Bool.or(blocked.ball(q, l, b), blocked(q, l, t))

# Shading
# -------

def sky(+v: F32) -> K.Vector<F32>:
  C.Direction.xyz((0.55 + 0.25 * v : F32), (0.7 + 0.2 * v : F32), 0.95)

def shade(+h: Hit, +v: F32) -> K.Vector<F32>:
  match h:
    case Hit{+d, +p, +n, +c}:
      +q = C.Point.moved(p, C.Direction.scaled(0.001, n))
      +lit = Bool.pick(F32, blocked(q, C.Line.through(q, C.Point.moved(q, light())), balls()), 0.0, F32.max(0.0, C.Direction.dot(n, light())))
      Bool.pick(K.Vector<F32>, F32.is_lt(d, 1.0e29), C.Direction.scaled((0.15 + 0.85 * lit : F32), c), sky(v))

# the colour seen through pixel (x, y) of an n by n image
def pixel(+n: F32, +x: F32, +y: F32) -> K.Vector<F32>:
  +u = ((x + 0.5) / n * 2.0 - 1.0 : F32)
  +v = (1.0 - (y + 0.5) / n * 2.0 : F32)
  +o = eye()
  +q = C.Point.xyz(u, (0.6 + v : F32), 2.0)
  +l = C.Line.through(o, q)
  +r = C.Direction.between(o, q)
  shade(Hit.nearer(Hit.balls(o, r, l, balls(), Hit.none()), Hit.floor(o, r, l)), v)

# The image
# ---------

def channel(+c: F32) -> U32:
  F32.to_u32(F32.min(255.0, F32.max(0.0, (c * 255.0 : F32))))

def pack(c: K.Vector<F32>) -> U32:
  match c:
    case K.Vector{r, g, b, o, i}:
      ((channel(r) * 65536 + channel(g) * 256) + channel(b) : U32)

# the image of the square at (x, y) with side 2^k, as a quadtree
def render(+n: F32, +k: Nat, +x: U32, +y: U32) -> Image:
  match k:
    case 0n:
      Pix{pack(pixel(n, U32.to_f32(x), U32.to_f32(y)))}
    case 1n+j:
      +h = U32.shln(1, j)
      a b c d = render(n, j, x, y) render(n, j, (x + h : U32), y) render(n, j, x, (y + h : U32)) render(n, j, (x + h : U32), (y + h : U32))
      Qua{a, b, c, d}

# the quadrant holding (x, y): left or right, top or bottom
def Image.quad(l: Bool, t: Bool, a: Image, b: Image, c: Image, d: Image) -> Image:
  match l t:
    case True{} True{}:
      a
    case False{} True{}:
      b
    case True{} False{}:
      c
    case False{} False{}:
      d

def Image.sub(img: Image, +x: U32, +y: U32, +h: U32) -> Image:
  match img:
    case Pix{c}:
      Pix{c}
    case Qua{a, b, c, d}:
      Image.quad(U32.is_lt(x, h), U32.is_lt(y, h), a, b, c, d)

# the colour at (x, y) in a quadtree of side 2^k
def Image.at(+k: Nat, img: Image, +x: U32, +y: U32) -> U32:
  match k:
    case 0n:
      match img:
        case Pix{c}:
          c
        case Qua{a, b, c, d}:
          0
    case 1n+j:
      +h = U32.shln(1, j)
      Image.at(j, Image.sub(img, x, y, h), Bool.pick(U32, U32.is_lt(x, h), x, (x - h : U32)), Bool.pick(U32, U32.is_lt(y, h), y, (y - h : U32)))

def rgb(+c: U32) -> String:
  Nat.show(U32.to_nat(U32.shrn(c, 16n))) ++ " " ++ Nat.show(U32.to_nat((U32.shrn(c, 8n) .&. 255 : U32))) ++ " " ++ Nat.show(U32.to_nat((c .&. 255 : U32))) ++ "\n"

# the pixels p, p - 1, .., 0 (row-major) in front of acc
def Ppm.go(f: Nat, +p: U32, +img: Image, +k: Nat, +n: U32, acc: String) -> String:
  match f:
    case 0n:
      acc
    case 1n+g:
      Ppm.go(g, (p - 1 : U32), img, k, n, rgb(Image.at(k, img, (p % n : U32), (p / n : U32))) ++ acc)

def Ppm.text(+img: Image, +k: Nat) -> String:
  +n = U32.shln(1, k)
  +s = U32.to_nat(n)
  "P3\n" ++ Nat.show(s) ++ " " ++ Nat.show(s) ++ "\n255\n" ++ Ppm.go(Nat.mul(s, s), (n * n - 1 : U32), img, k, n, "")

def put.fin(r: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (f, res) = r
  File.close(f)

def put(path: String, text: String) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path, "w"))
    r : File & Result<&1, &1, U32 & String, Unit> <- File.write(f, text)
    put.fin(r)

def outpath.go(args: List<String>) -> String:
  match args:
    case Nil{}:
      "demos/raytrace.ppm"
    case a <> t:
      a

# the first argument after the program's name
def outpath(args: List<String>) -> String:
  match args:
    case Nil{}:
      "demos/raytrace.ppm"
    case p <> t:
      outpath.go(t)

# 256 by 256: depth 8, one fork per quadrant at every level
def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +t0 : Nat <- IO.now()
    +img : Image = render!(256.0, 8n, 0, 0)
    +t1 : Nat <- IO.now()
    put(outpath(args), Ppm.text(img, 8n))
    IO.print("rendered 256x256 in " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms")

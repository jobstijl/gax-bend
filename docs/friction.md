# Friction log

The brief (§2a.9): examples get no raw trig or square roots. Lengths are
join norms, angles come from directions, colours are points. Every place
an example reached for raw float math goes here, with the library fix.

## `demos/raytrace.bend` (CGA3D ray tracer), 2026-10-04

| wanted | first reached for | library fix (`api/cga3d.bend`) |
|---|---|---|
| a ray through the eye and a pixel | coordinates and a parameter t | `Line.through(p, q)` = p ∧ q ∧ e∞ |
| where a ray meets a sphere | the quadratic \|o + t d − c\|² = r² | `Line.meet(s, l)` = s ⌋ l, a point pair; `PointPair.real` |
| the hit points | the quadratic formula | `PointPair.points(b)` = (b ∓ √b²)(e∞ ⌋ b); the square root lives here |
| where a ray meets the floor | solving for t | `Line.meet(plane, l)`, a flat point; `FlatPoint.point` |
| a ball's centre, for its normal | the sphere's fields divided by its weight | `Sphere.center` |
| a normal, a light direction | subtracting coordinates and normalising | `Direction.between(p, q)`, `Direction.unit`, `Direction.dot` |
| starting a shadow ray just off the surface | adding 0.001·n to coordinates | `Point.moved(p, d)`: the translation along d |
| dimming a colour | multiplying three channels | `Direction.scaled(k, c)`: colours are directions (r, g, b) |
| which hit is nearest | Euclidean distances | `Point.distance2` = −2 P·Q |

What stays as floats, at the boundary: the pixel's coordinates (u, v) in,
the sky's gradient, and the channel packing out.

## About Bend

- `Bool.pick` computes both arms in compiled code. So shading computes a
  shadow ray even for pixels that hit nothing. A branch on a computed
  `Bool` needs a helper def that matches it.
- `IO.args()` includes the program's name. The demo first wrote its image
  over its own binary ("Text file busy").
- Base has a quadtree `Image` and a window, but no image file writer. The
  demo walks the quadtree into a PPM (`Image.at`, `Ppm.text`).

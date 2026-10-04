# The algebras, as Bend data (ADR-002): the content of gax's .gax spec
# files. Blades are lists of generator indices in the written order, so
# e032 is [0, 3, 2] and is stored as -e023.

import Base
import ../src/spec.bend as S
import ./gen.bend as G

# PGA3D (gax crates/gax/specs/pga3d.gax): e0 squares to 0, e1 e2 e3 to 1
def PGA3D() -> G.GSpec:
  G.GSpec{"PGA3D", "PGA3", 4n, ["0", "1", "2", "3"],
    S.Gen{S.QZ{}, S.Gen{S.QP{}, S.Gen{S.QP{}, S.Gen{S.QP{}, S.SigEnd{}}}}},
    [ G.GKind{"Scalar", True{}, [[]]},
      G.GKind{"Plane", True{}, [[1n], [2n], [3n], [0n]]},
      G.GKind{"Line", True{}, [[2n, 3n], [3n, 1n], [1n, 2n], [0n, 1n], [0n, 2n], [0n, 3n]]},
      G.GKind{"Point", True{}, [[0n, 3n, 2n], [0n, 1n, 3n], [0n, 2n, 1n], [1n, 2n, 3n]]},
      G.GKind{"Direction", False{}, [[0n, 3n, 2n], [0n, 1n, 3n], [0n, 2n, 1n]]},
      G.GKind{"Pseudoscalar", True{}, [[0n, 1n, 2n, 3n]]},
      G.GKind{"Rotor", True{}, [[], [2n, 3n], [3n, 1n], [1n, 2n]]},
      G.GKind{"Translator", True{}, [[], [0n, 1n], [0n, 2n], [0n, 3n]]},
      G.GKind{"Motor", True{}, [[], [2n, 3n], [3n, 1n], [1n, 2n], [0n, 1n], [0n, 2n], [0n, 3n], [0n, 1n, 2n, 3n]]},
      G.GKind{"Flector", True{}, [[1n], [2n], [3n], [0n], [0n, 3n, 2n], [0n, 1n, 3n], [0n, 2n, 1n], [1n, 2n, 3n]]},
      G.GKind{"Multivector", True{}, [[], [0n], [1n], [2n], [3n], [0n, 1n], [0n, 2n], [0n, 3n], [1n, 2n], [3n, 1n], [2n, 3n],
        [0n, 2n, 1n], [0n, 1n, 3n], [0n, 3n, 2n], [1n, 2n, 3n], [0n, 1n, 2n, 3n]]} ]}

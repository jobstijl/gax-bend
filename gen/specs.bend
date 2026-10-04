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
        [0n, 2n, 1n], [0n, 1n, 3n], [0n, 3n, 2n], [1n, 2n, 3n], [0n, 1n, 2n, 3n]]} ],
    ["Plane", "Line", "Point", "Rotor", "Translator", "Motor", "Flector"]}

# VGA2D (gax vga2d.gax): e1 e2 square to 1
def VGA2D() -> G.GSpec:
  G.GSpec{"VGA2D", "VGA2", 2n, ["1", "2"],
    S.Gen{S.QP{}, S.Gen{S.QP{}, S.SigEnd{}}},
    [ G.GKind{"Scalar", True{}, [[]]},
      G.GKind{"Vector", True{}, [[0n], [1n]]},
      G.GKind{"Pseudoscalar", True{}, [[0n, 1n]]},
      G.GKind{"Rotor", True{}, [[], [0n, 1n]]},
      G.GKind{"Multivector", True{}, [[], [0n], [1n], [0n, 1n]]} ],
    ["Vector", "Rotor"]}

# VGA3D (gax vga3d.gax): e1 e2 e3 square to 1
def VGA3D() -> G.GSpec:
  G.GSpec{"VGA3D", "VGA3", 3n, ["1", "2", "3"],
    S.Gen{S.QP{}, S.Gen{S.QP{}, S.Gen{S.QP{}, S.SigEnd{}}}},
    [ G.GKind{"Scalar", True{}, [[]]},
      G.GKind{"Vector", True{}, [[0n], [1n], [2n]]},
      G.GKind{"Bivector", True{}, [[1n, 2n], [2n, 0n], [0n, 1n]]},
      G.GKind{"Pseudoscalar", True{}, [[0n, 1n, 2n]]},
      G.GKind{"Paravector", False{}, [[], [0n], [1n], [2n]]},
      G.GKind{"Rotor", True{}, [[], [1n, 2n], [2n, 0n], [0n, 1n]]},
      G.GKind{"Odd", True{}, [[0n], [1n], [2n], [0n, 1n, 2n]]},
      G.GKind{"Multivector", True{}, [[], [0n], [1n], [2n], [1n, 2n], [2n, 0n], [0n, 1n], [0n, 1n, 2n]]} ],
    ["Vector", "Rotor", "Odd"]}

# PGA2D (gax pga2d.gax): e0 squares to 0, e1 e2 to 1
def PGA2D() -> G.GSpec:
  G.GSpec{"PGA2D", "PGA2", 3n, ["0", "1", "2"],
    S.Gen{S.QZ{}, S.Gen{S.QP{}, S.Gen{S.QP{}, S.SigEnd{}}}},
    [ G.GKind{"Scalar", True{}, [[]]},
      G.GKind{"Line", True{}, [[1n], [2n], [0n]]},
      G.GKind{"Point", True{}, [[2n, 0n], [0n, 1n], [1n, 2n]]},
      G.GKind{"Direction", False{}, [[2n, 0n], [0n, 1n]]},
      G.GKind{"Pseudoscalar", True{}, [[0n, 1n, 2n]]},
      G.GKind{"Rotor", True{}, [[], [1n, 2n]]},
      G.GKind{"Translator", True{}, [[], [2n, 0n], [0n, 1n]]},
      G.GKind{"Motor", True{}, [[], [1n, 2n], [2n, 0n], [0n, 1n]]},
      G.GKind{"Flector", True{}, [[1n], [2n], [0n], [0n, 1n, 2n]]},
      G.GKind{"Multivector", True{}, [[], [0n], [1n], [2n], [0n, 1n], [2n, 0n], [1n, 2n], [0n, 1n, 2n]]} ],
    ["Line", "Point", "Rotor", "Translator", "Motor", "Flector"]}

# STA (gax sta.gax): e0 squares to 1, e1 e2 e3 to -1
def STA() -> G.GSpec:
  G.GSpec{"STA", "STA", 4n, ["0", "1", "2", "3"],
    S.Gen{S.QP{}, S.Gen{S.QN{}, S.Gen{S.QN{}, S.Gen{S.QN{}, S.SigEnd{}}}}},
    [ G.GKind{"Scalar", True{}, [[]]},
      G.GKind{"Vector", True{}, [[0n], [1n], [2n], [3n]]},
      G.GKind{"Bivector", True{}, [[1n, 0n], [2n, 0n], [3n, 0n], [2n, 3n], [3n, 1n], [1n, 2n]]},
      G.GKind{"Trivector", True{}, [[1n, 2n, 3n], [0n, 3n, 2n], [0n, 1n, 3n], [0n, 2n, 1n]]},
      G.GKind{"Pseudoscalar", True{}, [[0n, 1n, 2n, 3n]]},
      G.GKind{"Phasor", True{}, [[], [0n, 1n, 2n, 3n]]},
      G.GKind{"Even", True{}, [[], [1n, 0n], [2n, 0n], [3n, 0n], [2n, 3n], [3n, 1n], [1n, 2n], [0n, 1n, 2n, 3n]]},
      G.GKind{"Odd", True{}, [[0n], [1n], [2n], [3n], [1n, 2n, 3n], [0n, 3n, 2n], [0n, 1n, 3n], [0n, 2n, 1n]]},
      G.GKind{"Multivector", True{}, [[], [0n], [1n], [2n], [3n], [1n, 0n], [2n, 0n], [3n, 0n], [2n, 3n], [3n, 1n], [1n, 2n],
        [1n, 2n, 3n], [0n, 3n, 2n], [0n, 1n, 3n], [0n, 2n, 1n], [0n, 1n, 2n, 3n]]} ],
    ["Vector", "Even", "Odd"]}

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
    ["Plane", "Line", "Point", "Rotor", "Translator", "Motor", "Flector"], G.NoNul{}}

# VGA2D (gax vga2d.gax): e1 e2 square to 1
def VGA2D() -> G.GSpec:
  G.GSpec{"VGA2D", "VGA2", 2n, ["1", "2"],
    S.Gen{S.QP{}, S.Gen{S.QP{}, S.SigEnd{}}},
    [ G.GKind{"Scalar", True{}, [[]]},
      G.GKind{"Vector", True{}, [[0n], [1n]]},
      G.GKind{"Pseudoscalar", True{}, [[0n, 1n]]},
      G.GKind{"Rotor", True{}, [[], [0n, 1n]]},
      G.GKind{"Multivector", True{}, [[], [0n], [1n], [0n, 1n]]} ],
    ["Vector", "Rotor"], G.NoNul{}}

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
    ["Vector", "Rotor", "Odd"], G.NoNul{}}

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
    ["Line", "Point", "Rotor", "Translator", "Motor", "Flector"], G.NoNul{}}

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
    ["Vector", "Even", "Odd"], G.NoNul{}}

# CGA3D (gax cga3d.gax): R(4,1) in the null basis e1 e2 e3 eo ei, eo . ei =
# -1. The tree runs on e+ (generator 3) and e- (4), eo = (e- - e+)/2 and
# ei = e- + e+; blades are written with eo as 5 and ei as 6.
def CGA3D() -> G.GSpec:
  G.GSpec{"CGA3D", "CGA3", 5n, ["1", "2", "3", "p", "m", "o", "i"],
    S.Gen{S.QP{}, S.Gen{S.QP{}, S.Gen{S.QP{}, S.Gen{S.QP{}, S.Gen{S.QN{}, S.SigEnd{}}}}}},
    [ G.GKind{"Scalar", True{}, [[]]},
      G.GKind{"Vector", True{}, [[0n], [1n], [2n], [5n], [6n]]},
      G.GKind{"Twist", True{}, [[1n, 2n], [2n, 0n], [0n, 1n], [0n, 6n], [1n, 6n], [2n, 6n]]},
      G.GKind{"Bivector", True{}, [[1n, 2n], [2n, 0n], [0n, 1n], [0n, 5n], [1n, 5n], [2n, 5n], [0n, 6n], [1n, 6n], [2n, 6n], [5n, 6n]]},
      G.GKind{"Trivector", True{}, [[1n, 2n, 5n], [2n, 0n, 5n], [0n, 1n, 5n], [1n, 2n, 6n], [2n, 0n, 6n], [0n, 1n, 6n], [0n, 5n, 6n], [1n, 5n, 6n], [2n, 5n, 6n], [0n, 1n, 2n]]},
      G.GKind{"Quadvector", True{}, [[1n, 2n, 5n, 6n], [2n, 0n, 5n, 6n], [0n, 1n, 5n, 6n], [0n, 1n, 2n, 5n], [0n, 1n, 2n, 6n]]},
      G.GKind{"Pseudoscalar", True{}, [[0n, 1n, 2n, 5n, 6n]]},
      G.GKind{"Motor", True{}, [[], [1n, 2n], [2n, 0n], [0n, 1n], [0n, 6n], [1n, 6n], [2n, 6n], [0n, 1n, 2n, 6n]]},
      G.GKind{"Even", True{}, [[], [1n, 2n], [2n, 0n], [0n, 1n], [0n, 5n], [1n, 5n], [2n, 5n], [0n, 6n], [1n, 6n], [2n, 6n], [5n, 6n],
        [1n, 2n, 5n, 6n], [2n, 0n, 5n, 6n], [0n, 1n, 5n, 6n], [0n, 1n, 2n, 5n], [0n, 1n, 2n, 6n]]},
      G.GKind{"Odd", True{}, [[0n], [1n], [2n], [5n], [6n], [1n, 2n, 5n], [2n, 0n, 5n], [0n, 1n, 5n], [1n, 2n, 6n], [2n, 0n, 6n], [0n, 1n, 6n],
        [0n, 5n, 6n], [1n, 5n, 6n], [2n, 5n, 6n], [0n, 1n, 2n], [0n, 1n, 2n, 5n, 6n]]},
      G.GKind{"Multivector", True{}, [[], [0n], [1n], [2n], [5n], [6n], [1n, 2n], [2n, 0n], [0n, 1n], [0n, 5n], [1n, 5n], [2n, 5n],
        [0n, 6n], [1n, 6n], [2n, 6n], [5n, 6n], [1n, 2n, 5n], [2n, 0n, 5n], [0n, 1n, 5n], [1n, 2n, 6n], [2n, 0n, 6n], [0n, 1n, 6n],
        [0n, 5n, 6n], [1n, 5n, 6n], [2n, 5n, 6n], [0n, 1n, 2n], [1n, 2n, 5n, 6n], [2n, 0n, 5n, 6n], [0n, 1n, 5n, 6n], [0n, 1n, 2n, 5n],
        [0n, 1n, 2n, 6n], [0n, 1n, 2n, 5n, 6n]]} ],
    ["Vector", "Motor", "Even", "Odd"], G.Nul{3n, 4n}}

# STAP (gax stap.gax): projective spacetime R(3,1,1), e0 degenerate, e1 e2 e3 square to 1, e4 (time) to -1
def STAP() -> G.GSpec:
  G.GSpec{"STAP", "STAP", 5n, ["0", "1", "2", "3", "4"],
    S.Gen{S.QZ{}, S.Gen{S.QP{}, S.Gen{S.QP{}, S.Gen{S.QP{}, S.Gen{S.QN{}, S.SigEnd{}}}}}},
    [ G.GKind{"Scalar", True{}, [[]]},
      G.GKind{"Vector", True{}, [[0n], [1n], [2n], [3n], [4n]]},
      G.GKind{"Bivector", True{}, [[0n, 1n], [0n, 2n], [0n, 3n], [0n, 4n], [2n, 3n], [3n, 1n], [1n, 2n], [4n, 1n], [4n, 2n], [4n, 3n]]},
      G.GKind{"Trivector", True{}, [[0n, 2n, 3n], [0n, 3n, 1n], [0n, 1n, 2n], [0n, 1n, 4n], [0n, 2n, 4n], [0n, 3n, 4n], [1n, 2n, 3n], [2n, 3n, 4n], [3n, 1n, 4n], [1n, 2n, 4n]]},
      G.GKind{"Quadvector", True{}, [[0n, 3n, 2n, 4n], [0n, 1n, 3n, 4n], [0n, 2n, 1n, 4n], [0n, 1n, 2n, 3n], [1n, 2n, 3n, 4n]]},
      G.GKind{"Pseudoscalar", True{}, [[0n, 1n, 2n, 3n, 4n]]},
      G.GKind{"Motor", True{}, [[], [0n, 1n], [0n, 2n], [0n, 3n], [0n, 4n], [2n, 3n], [3n, 1n], [1n, 2n], [4n, 1n], [4n, 2n], [4n, 3n], [0n, 3n, 2n, 4n], [0n, 1n, 3n, 4n], [0n, 2n, 1n, 4n], [0n, 1n, 2n, 3n], [1n, 2n, 3n, 4n]]},
      G.GKind{"Odd", True{}, [[0n], [1n], [2n], [3n], [4n], [0n, 2n, 3n], [0n, 3n, 1n], [0n, 1n, 2n], [0n, 1n, 4n], [0n, 2n, 4n], [0n, 3n, 4n], [1n, 2n, 3n], [2n, 3n, 4n], [3n, 1n, 4n], [1n, 2n, 4n], [0n, 1n, 2n, 3n, 4n]]},
      G.GKind{"Multivector", True{}, [[], [0n], [1n], [2n], [3n], [4n], [0n, 1n], [0n, 2n], [0n, 3n], [0n, 4n], [2n, 3n], [3n, 1n], [1n, 2n], [4n, 1n], [4n, 2n], [4n, 3n], [0n, 2n, 3n], [0n, 3n, 1n], [0n, 1n, 2n], [0n, 1n, 4n], [0n, 2n, 4n], [0n, 3n, 4n], [1n, 2n, 3n], [2n, 3n, 4n], [3n, 1n, 4n], [1n, 2n, 4n], [0n, 3n, 2n, 4n], [0n, 1n, 3n, 4n], [0n, 2n, 1n, 4n], [0n, 1n, 2n, 3n], [1n, 2n, 3n, 4n], [0n, 1n, 2n, 3n, 4n]]} ],
    ["Vector", "Motor", "Odd"], G.NoNul{}}

# CSTA (gax csta.gax): conformal spacetime R(4,2) in the null basis e1 e2 e3 e4 eo ei; the tree
# runs on e+ (generator 4) and e- (5); blades are written with eo as 6 and ei as 7
def CSTA() -> G.GSpec:
  G.GSpec{"CSTA", "CSTA", 6n, ["1", "2", "3", "4", "p", "m", "o", "i"],
    S.Gen{S.QP{}, S.Gen{S.QP{}, S.Gen{S.QP{}, S.Gen{S.QN{}, S.Gen{S.QP{}, S.Gen{S.QN{}, S.SigEnd{}}}}}}},
    [ G.GKind{"Scalar", True{}, [[]]},
      G.GKind{"Vector", True{}, [[0n], [1n], [2n], [3n], [6n], [7n]]},
      G.GKind{"Twist", True{}, [[1n, 2n], [2n, 0n], [0n, 1n], [3n, 0n], [3n, 1n], [3n, 2n], [0n, 7n], [1n, 7n], [2n, 7n], [3n, 7n]]},
      G.GKind{"Bivector", True{}, [[1n, 2n], [2n, 0n], [0n, 1n], [3n, 0n], [3n, 1n], [3n, 2n], [0n, 6n], [1n, 6n], [2n, 6n], [3n, 6n], [0n, 7n], [1n, 7n], [2n, 7n], [3n, 7n], [6n, 7n]]},
      G.GKind{"Trivector", True{}, [[1n, 2n, 3n], [2n, 0n, 3n], [0n, 1n, 3n], [0n, 1n, 2n], [1n, 2n, 6n], [2n, 0n, 6n], [0n, 1n, 6n], [3n, 0n, 6n], [3n, 1n, 6n], [3n, 2n, 6n], [1n, 2n, 7n], [2n, 0n, 7n], [0n, 1n, 7n], [3n, 0n, 7n], [3n, 1n, 7n], [3n, 2n, 7n], [0n, 6n, 7n], [1n, 6n, 7n], [2n, 6n, 7n], [3n, 6n, 7n]]},
      G.GKind{"Quadvector", True{}, [[0n, 1n, 2n, 3n], [1n, 2n, 3n, 6n], [2n, 0n, 3n, 6n], [0n, 1n, 3n, 6n], [0n, 1n, 2n, 6n], [1n, 2n, 3n, 7n], [2n, 0n, 3n, 7n], [0n, 1n, 3n, 7n], [0n, 1n, 2n, 7n], [1n, 2n, 6n, 7n], [2n, 0n, 6n, 7n], [0n, 1n, 6n, 7n], [3n, 0n, 6n, 7n], [3n, 1n, 6n, 7n], [3n, 2n, 6n, 7n]]},
      G.GKind{"Quintvector", True{}, [[1n, 2n, 3n, 6n, 7n], [2n, 0n, 3n, 6n, 7n], [0n, 1n, 3n, 6n, 7n], [0n, 1n, 2n, 6n, 7n], [0n, 1n, 2n, 3n, 6n], [0n, 1n, 2n, 3n, 7n]]},
      G.GKind{"Pseudoscalar", True{}, [[0n, 1n, 2n, 3n, 6n, 7n]]},
      G.GKind{"Motor", True{}, [[], [1n, 2n], [2n, 0n], [0n, 1n], [3n, 0n], [3n, 1n], [3n, 2n], [0n, 7n], [1n, 7n], [2n, 7n], [3n, 7n], [1n, 2n, 3n, 7n], [2n, 0n, 3n, 7n], [0n, 1n, 3n, 7n], [0n, 1n, 2n, 7n], [0n, 1n, 2n, 3n]]},
      G.GKind{"Even", True{}, [[], [1n, 2n], [2n, 0n], [0n, 1n], [3n, 0n], [3n, 1n], [3n, 2n], [0n, 6n], [1n, 6n], [2n, 6n], [3n, 6n], [0n, 7n], [1n, 7n], [2n, 7n], [3n, 7n], [6n, 7n], [0n, 1n, 2n, 3n], [1n, 2n, 3n, 6n], [2n, 0n, 3n, 6n], [0n, 1n, 3n, 6n], [0n, 1n, 2n, 6n], [1n, 2n, 3n, 7n], [2n, 0n, 3n, 7n], [0n, 1n, 3n, 7n], [0n, 1n, 2n, 7n], [1n, 2n, 6n, 7n], [2n, 0n, 6n, 7n], [0n, 1n, 6n, 7n], [3n, 0n, 6n, 7n], [3n, 1n, 6n, 7n], [3n, 2n, 6n, 7n], [0n, 1n, 2n, 3n, 6n, 7n]]},
      G.GKind{"Odd", True{}, [[0n], [1n], [2n], [3n], [6n], [7n], [1n, 2n, 3n], [2n, 0n, 3n], [0n, 1n, 3n], [0n, 1n, 2n], [1n, 2n, 6n], [2n, 0n, 6n], [0n, 1n, 6n], [3n, 0n, 6n], [3n, 1n, 6n], [3n, 2n, 6n], [1n, 2n, 7n], [2n, 0n, 7n], [0n, 1n, 7n], [3n, 0n, 7n], [3n, 1n, 7n], [3n, 2n, 7n], [0n, 6n, 7n], [1n, 6n, 7n], [2n, 6n, 7n], [3n, 6n, 7n], [1n, 2n, 3n, 6n, 7n], [2n, 0n, 3n, 6n, 7n], [0n, 1n, 3n, 6n, 7n], [0n, 1n, 2n, 6n, 7n], [0n, 1n, 2n, 3n, 6n], [0n, 1n, 2n, 3n, 7n]]},
      G.GKind{"Multivector", True{}, [[], [0n], [1n], [2n], [3n], [6n], [7n], [1n, 2n], [2n, 0n], [0n, 1n], [3n, 0n], [3n, 1n], [3n, 2n], [0n, 6n], [1n, 6n], [2n, 6n], [3n, 6n], [0n, 7n], [1n, 7n], [2n, 7n], [3n, 7n], [6n, 7n], [1n, 2n, 3n], [2n, 0n, 3n], [0n, 1n, 3n], [0n, 1n, 2n], [1n, 2n, 6n], [2n, 0n, 6n], [0n, 1n, 6n], [3n, 0n, 6n], [3n, 1n, 6n], [3n, 2n, 6n], [1n, 2n, 7n], [2n, 0n, 7n], [0n, 1n, 7n], [3n, 0n, 7n], [3n, 1n, 7n], [3n, 2n, 7n], [0n, 6n, 7n], [1n, 6n, 7n], [2n, 6n, 7n], [3n, 6n, 7n], [0n, 1n, 2n, 3n], [1n, 2n, 3n, 6n], [2n, 0n, 3n, 6n], [0n, 1n, 3n, 6n], [0n, 1n, 2n, 6n], [1n, 2n, 3n, 7n], [2n, 0n, 3n, 7n], [0n, 1n, 3n, 7n], [0n, 1n, 2n, 7n], [1n, 2n, 6n, 7n], [2n, 0n, 6n, 7n], [0n, 1n, 6n, 7n], [3n, 0n, 6n, 7n], [3n, 1n, 6n, 7n], [3n, 2n, 6n, 7n], [1n, 2n, 3n, 6n, 7n], [2n, 0n, 3n, 6n, 7n], [0n, 1n, 3n, 6n, 7n], [0n, 1n, 2n, 6n, 7n], [0n, 1n, 2n, 3n, 6n], [0n, 1n, 2n, 3n, 7n], [0n, 1n, 2n, 3n, 6n, 7n]]} ],
    ["Vector", "Motor"], G.Nul{4n, 5n}}

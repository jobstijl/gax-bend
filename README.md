# gax-blend

A geometric algebra library for [Bend 2](https://github.com/bendlang/bend):
fast on Bend's CPU and GPU backends, with its algebra proven in Bend's own
type theory instead of tested. gax ([github.com/jobstijl/gax](https://github.com/jobstijl/gax))
is the semantic reference.

## Status

| layer | what | state |
|---|---|---|
| S, the spec | a multivector tree over any dimension, any diagonal signature, any scalar ring | **22 laws proven** ([docs/laws.md](docs/laws.md)); `LAWS.bend` is a draft under review |
| K, kernels | flat per-kind records with straight-line kernels, each proven equal to the spec | next (Phase 2) |
| A, the API | PGA2D/3D, VGA3D, CGA3D, STA with geometric nouns and batch APIs | later |
| numbers | exact `Int` (done); dyadics, SoftF32, double-F32, posits | Phase 3 |

The Phase 0 measurements behind the design (checker cost, kernel speed
against C, GPU) are in [docs/bend-facts.md](docs/bend-facts.md), and the
decisions in [docs/design.md](docs/design.md).

## Running it

```sh
. tools/env.sh          # bend 2.0.35 and the project's clang on PATH
tools/gate.sh           # proofs, example tests, negative controls
bend tests/spec_pga3d.bend
```

`tools/gate.sh` passes only when:
- `bend PROOF.bend` prints ALL PROOFS CHECK;
- every `tests/*.bend` prints the `#|` lines it ends with;
- every negative control in `tests/neg/` fails.

GPU runs use the upstream `hip` branch: `. tools/env-hip.sh`, then `bend-hip`.
See bend-facts, "Pins".

## Layout

```
LAWS.bend         the laws (owned by the human once approved)
PROOF.bend        fills every law; the gate
src/spec.bend     Layer S: MV(T, d), Sig(d), products, signs, complements, grades
src/ring.bend     the ring laws a theorem may assume
src/int.bend      exact integers
src/show.bend     printing multivectors as blade sums
proofs/           the lemmas behind PROOF.bend
tests/            example tests (`#|` expected output) and negative controls
bench/            benchmarks (Bend against C)
spikes/           Phase 0 experiments, kept as evidence for bend-facts
tools/            env, the 16 GB cap, the gate
docs/             facts, design (ADRs), laws, upstream notes
```

## Conventions

Basis, orientation and signs follow gax (ADR-009 there):
- PGA puts e0 first;
- the join sign is e123 ∨ e032 = +e23;
- `J_R` is the right complement, with a ∧ J_R(a) = I;
- the regressive product is J_L(J_R a ∧ J_R b).

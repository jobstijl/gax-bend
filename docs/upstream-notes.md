# Upstream notes

These are the places where Bend itself limits this project. Per the 2026-10-04 decision, **none are filed upstream**. Each entry gives a repro in this repository, the related upstream issue if one exists, and what the project does about it.

## 1. `--verdict` has no model for unital structures

- **Repro:** `upstream/verdict_ring_hypotheses.bend`.
- **Bend:** 2.0.35, commit `2bfc83fd`.
- **What happens:** bend2 prints ALL PROOFS CHECK. `--verdict` prints SOME PROOFS FAIL with the generic "mismatch" text. `-o x.bendtt` gives the real reason: `no model for sum3~unit`.
- **Cause:** the kernel checks a template once, with each `~` constant replaced by a model. Models are chosen greedily: T ↦ Unit, operations ↦ `λx y. Unit{}`.
  - Every equation between operation applications holds under that model.
  - `add(x, zero) == x` does not, because the kernel has no eta.
  - Even a backtracking search (PR #1263, open) finds nothing: with T = Unit, commutativity forces a constant `add`, and the unit law then needs `Unit{} == x` for a variable `x`.
  - Every unital structure is therefore affected: monoids, rings, fields, and the scalar ring of a geometric algebra.
- **Related:** #1182 (same root cause, higher-order `~` laws), PR #1263.
- **What we do:** since 2026-10-04 there is no `--verdict` on this machine (see ADR-001, amendment 2), so this does not block the gate. Proofs are kept free of needless bare-variable hypotheses anyway, so they stay kernel-friendly if `--verdict` returns.

## 2. A `∀` hypothesis about native F32 has no model

- **Repro:** `spikes/q09b_native_hyp.bend`.
- **Message:** `no model for native_add_bits~ieee`.
- **Same cause** as note 1.
- **Related:** WONTFIX lists bit-level F32 in the checker as SOON (#1017).
- **What we do:** laws over native F32 are conditional bend2 theorems with `~` hypotheses (ADR-001, amendment 2).

## 3. The kernel runs out of fuel on large closed computations

- **Repro:** `spikes/q04c_assoc_ZPPP.bend` under `--verdict` gave `out of fuel` (400 M steps). bend2 checks it in 5.6 s.
- **WONTFIX** #993 / #1075 covers this in general ("keep large constants and depths abstract").
- **What we do:** nothing needed while bend2 is the gate.

## 4. GPU lanes: Metal and CUDA only on main

- **WONTFIX #811.** The AMD lane exists only on the unmerged `hip` branch: Bend 2.0.24, 147 commits behind main.
- **What we do:** GPU numbers come from that branch, built with Bun, with ROCm 7.2.4 unpacked in `.vendor/rocm` (bend-facts: pins). Library code targets main (2.0.35). Every file benchmarked on the GPU must also check on 2.0.24; so far all have.

## 5. Hypotheses cannot be reused unless they are `~`

- **Issue #848**, closed "by design, for now".
- A function-typed hypothesis is affine. Passing it as `+h` is refused: `+unit can be used many times, so its type must be Data`.
- **What we do:** ring laws are `~` parameters.

## 6. Smaller ergonomic limits that shape generated code

These are design choices upstream and are recorded in bend-facts under "Language facts":
- only parameters and pattern variables can be matched or destructured;
- defs are ordered, with no mutual recursion;
- `A & B` is `Type`;
- there is no CSE (#812).

# Integral closedness of broad Siegel E-values

A Lean 4 formalization of the integral closedness proof for the ring of broad
Siegel E-values. The value ring comes from
[Broad Siegel E-values](https://github.com/Niklas-Fraccaro/wide-e-values-lean).

## Main theorem

The verified descent theorem is
[`isIntegrallyClosed_valueSubring_of_broadArithmeticFrames_and_division`](WideEIntegralClosed/RamifiedDescent.lean).

```lean
∀ (_ : BroadArithmeticFrameExistence) (_ : HasWideDivisionAtOne),
  IsIntegrallyClosed WideE.valueSubring
```

The arithmetic Frobenius input supplies rational exponents and broad
E-function amplitudes for any finite family. Lean verifies the construction
of a common frame from individual frames by block diagonals. The proof of
individual frame existence is in progress. The paper derives this input from
[Lepetit, Proposition 16 and Theorem 7](https://nwejm.univ-lille.fr/index.php/nwejm/article/view/23).

The proof specializes a ramified Picard–Vessiot algebra at the ordinary point
`(1, 0)` of the Laurent–logarithm base. Evaluation selects a normal component
of the fiber. Division by `z - 1` lifts finite relations. Normality in the
selected component gives integral closedness by descent.

## Proof modules

| Paper section | Lean module |
| --- | --- |
| Fundamental matrix and constants | `FrameAssembly`, `BroadFrobenius`, `ArithmeticRealization` |
| Inverse determinant values | `Determinant` |
| Picard–Vessiot fiber and normal components | `PicardVessiotFiber`, `HopfNormality`, `Normalization` |
| Finite relations and factorization | `Specialization`, `Factorization` |
| Integral closedness and the polynomial corollary | `AlgebraicDescent`, `RamifiedDescent` |

## Reproducibility

Requires Git and elan. The project pins Lean 4.19.0, Mathlib, WideE, and the
strict E-value dependency in `lake-manifest.json`.

```sh
git clone https://github.com/Niklas-Fraccaro/wide-e-values-integral-closedness-lean.git
cd wide-e-values-integral-closedness-lean
lake exe cache get
./build.sh build WideEIntegralClosed +WideEIntegralClosed.Audit
```

On Windows, run the same sequential elaboration settings with PowerShell.

```powershell
lake exe cache get
.\build.ps1 build WideEIntegralClosed +WideEIntegralClosed.Audit
```

The optional entry point `WideEIntegralClosed.Main` imports the division
proof from the pinned WideE library and leaves the Frobenius input as a
hypothesis.

## Verification

[![Lean verification](https://github.com/Niklas-Fraccaro/wide-e-values-integral-closedness-lean/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/Niklas-Fraccaro/wide-e-values-integral-closedness-lean/actions/workflows/lean.yml)

The workflow builds the library and checks that the audited declarations
depend only on `propext`, `Classical.choice`, and `Quot.sound`.
See [the axiom audit](WideEIntegralClosed/Audit.lean).

## Attribution

The project reuses WideE and adapts constructions from the pinned
[strict E-unit formalization](https://github.com/Hatsuwr/strict-e-unit-classification/tree/340c7435608e0f1aa1d9b08a0100721a4fd23005).
The strict project's [license](third_party/strict-e-unit-classification/LICENSE)
and [notice](third_party/strict-e-unit-classification/NOTICE) accompany those
adaptations.

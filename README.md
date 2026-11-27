# Integral closedness of broad Siegel E-values

This Lean library proves that the ring of broad Siegel E-values is integrally
closed in its fraction field.

## Main theorem

The main theorem is [`WideEIntegralClosed.isIntegrallyClosed_valueSubring`](WideEIntegralClosed/IntegralClosedness.lean).

```lean
IsIntegrallyClosed WideE.valueSubring
```

The proof specializes a ramified Picard–Vessiot algebra at the ordinary point
`(1, 0)` and descends normality from the selected component of the fiber.
[Proof note (German, PDF)](Ganzabgeschlossenheit_E_Wertring.pdf)

The corollaries give smooth normal factorization for maps from finitely
presented algebras and polynomial and positive-power membership criteria for
the value ring. [Lean corollaries](WideEIntegralClosed/IntegralClosedness.lean#L14)

## Reproducibility

Requires Git and elan. The project pins Lean 4.19.0, Mathlib, WideE, and
Hatsuwr's strict E-unit formalization. [WideE](https://github.com/Niklas-Fraccaro/wide-e-values-lean) ·
[Pinned strict E-unit source](https://github.com/Hatsuwr/strict-e-unit-classification/tree/340c7435608e0f1aa1d9b08a0100721a4fd23005)

```sh
git clone https://github.com/Niklas-Fraccaro/wide-e-values-integral-closedness-lean.git
cd wide-e-values-integral-closedness-lean
lake exe cache get
./build.sh build WideEIntegralClosed +WideEIntegralClosed.Audit +WideEIntegralClosed.FullAudit
```

The final command builds the library and checks that the audited declarations
depend only on `propext`, `Classical.choice`, and `Quot.sound`.
[Descent audit](WideEIntegralClosed/Audit.lean) · [Full audit](WideEIntegralClosed/FullAudit.lean)

## Verification

[![Lean verification](https://github.com/Niklas-Fraccaro/wide-e-values-integral-closedness-lean/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/Niklas-Fraccaro/wide-e-values-integral-closedness-lean/actions/workflows/lean.yml)

The workflow starts from a fresh Linux checkout and uses the Mathlib cache.
It builds the library and runs both axiom audits.

The strict E-unit license and notice accompany the adapted constructions.
[License](third_party/strict-e-unit-classification/LICENSE) · [Notice](third_party/strict-e-unit-classification/NOTICE)

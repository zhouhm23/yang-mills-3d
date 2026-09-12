# 3D Yang–Mills mass gap (work in progress)

This repository contains Lean 4 formalizations of partial results from ongoing
work by **Z.ai** on the 3D Yang–Mills mass gap problem (the three-dimensional
case of the Jaffe–Witten Clay Millennium statement). The problem is **not
solved**; this is work in progress. There is no paper yet — one will be written
if and when the program closes.

## What is formalized

The certificate layer `YangMills3D/` machine-checks the terminal layer of a
25-wave research campaign (status: open):

* **Animal-entropy impossibility** — the face-perimeter generating function of
  box cell sets diverges at every fugacity, so no exponential animal-entropy
  tail exists (`Animals.lean`, `Entropy.lean`). This falsifies the W23-Q
  cluster criterion `A(z) < 1` used earlier in the campaign.
* **T-OP transfer** — the finite-range stencil packaging of the neutral-gas
  covariance preserves exponential decay rates exactly (c = 1)
  (`Symbol.lean`, `Mixture.lean`).
* **Window check** — the delivered mixing rate `ν(β) = (4/3)(2π²/β − log 8)`
  clears the campaign's budget bar `0.493·μ₀` at the audited couplings
  (`Window.lean`).
* **Total-variation sign currency** — positive reorganizations of the sector
  mixture cost nothing, signed ones pay exactly `Σ_f |w_f|`, and the sector
  sign is the ℤ/2 character `(−1)^|n| = e^{iπn}` (`Sign.lean`).
* **Two-input ceiling (W24-CEIL)** — the remaining problem reduces to exactly
  two named independent inputs: [U-4*] (volume-uniform bounded total variation
  of the sector mixture) and [CORE-W] (uniform exponential decay of the image
  defect field). They enter the Lean theorem as explicit hypotheses
  (`Mixture.lean`).

The full 42-line axiom inventory is `YangMills3D/SelfCheck.lean`.

## Building the formalizations

The project uses Lean 4.34.0-rc2, Mathlib, and Lake. With elan installed,
fetch the Mathlib cache and build with:

```
lake exe cache get
lake build
```

## Independent proof checking

```
bash scripts/selfcheck.sh
```

checks three gates: no `sorry`/`admit`/`native_decide` and no new `axiom`
declarations anywhere in the library; a cold rebuild from scratch; and that
all 42 `#print axioms` lines depend only on `propext`, `Classical.choice`,
`Quot.sound`.

## License

MIT — Copyright (c) 2026 Z.ai.

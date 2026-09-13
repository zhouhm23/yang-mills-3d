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
* **Kernel convexity (W28T-CONV)** — the uniform-decay class is closed under
  convex combination at the same rate `ν` (constant `Σ α_i K_i`): the uniform
  decay survives every positive disorder resolution (`Decay.lean`).
* **Shadow-projection floor (W29-FLOOR)** — a cell configuration meeting `e`
  distinct x-layers has at least `4e + 2` exposed faces (tight: the tube), and
  boundary additivity over non-contacting components
  `|∂W| = Σ_i |∂C_i|` (W29-DEC) (`Floor.lean`).
* **Pairing/parity layer (W26-PAR, W26-CANCEL)** — sign-pure orbit merges
  conserve TV exactly, and the even/odd split obeys `2·Z_even = Z⁺ + Z` with
  cancellation factor `Z_even = (Z⁺ + |Z|)/2` (`Coarsen.lean`).
* **Diameter–perimeter floor (W30-FLOOR2)** — a vertex-connected cell set
  with ℓ₁-diameter `r` has at least `2r + 6` exposed faces; TIGHT at the
  corner chain `(i,i,i)`, `i = 0..m`, whose perimeter is exactly
  `6(m+1) = 2·(3m) + 6` (`Fan.lean`).  Formalized in the vertex-connected
  form the chain unions satisfy: the campaign's connectivity-free version
  is falsified by the two-point set `{0, (r,0,0)}` (perimeter `12 < 2r+6`
  for `r ≥ 4`) — see the module docstring for the correction.
* **Doubled connecting rate (W30-RATE) and W30-FORM germ** — a
  vertex-connected cell set reaching within halo distance 1 of both anchors
  has perimeter ≥ `2d + 2` at anchor separation `d`, so the W29-EF rate
  `κ_c − ln F₀ − ε` DOUBLES to `ν = 2(κ_c − ln F₀ − ε)`; at the window
  bottom `β = 6.618` the [W30-MISS] fan price `F₀ ≤ 6.093` clears the
  ascent bar `0.493·2.40` (theorem-floor `ν > 1.8002`, machine 2.3510).
  Includes the exact intra/inter-cluster split
  `W_p·star(W_p) = Σ_a W_a·star(W_a) + Σ_{a≠b} W_a·star(W_b)` of w30-charge
  (`Fan.lean`).

* **Wave-31 walk-counting layer (W31, toward W31-FAN)** — the abstract
  walk vocabulary over a finite vertex set (`wEdges`, `WalkOn`, `Simple`
  via Pairwise over up-to-swap edge pairs, `ClosedAt`, `Covers`),
  used/unused neighborhood bookkeeping, and the COUNTING BRIDGE
  `card_usedNbrs_eq_incCount`: for a simple walk, the used neighbors of
  a vertex `s` number exactly the edges of the walk incident to `s`
  (simplicity makes the "other endpoint" map injective on the incident
  edges) — the wave-31 analogue of the wave-29 shadow-projection
  pigeonhole.  `card_usedNbrs_of_X_eq` extends the bridge to a walk
  plus an extra pair set with pairwise UndEq-distinct pairs
  (`Euler.lean`).
* **Wave-31 manifold/pinched split and the [W31-MISS] reduction** —
  `Reach`/`ManifoldSurf`/`AdjClosed` package the manifold-surface
  predicate (anchor membership, 4-regularity per W31-REG,
  connectivity), and `tailFan_split` is the [W31-MISS] reduction: a
  tail-fan for the full polymer family at ((8/3) + A) · (max 3 F)ⁿ
  follows from the DONE manifold half (W31-FAN at F₀ = 3, all n) plus
  ANY tail-fan for the pinched subclass at (A, F); with a pinched fan
  at F₀ <= 6.093 this closes [W30-MISS]/[CORE-W] on [6.618, 8.2319)
  via W29-EF + W30-RATE (`Manifold.lean`).  Still pending in Lean: the
  endpoint-parity lemma, Euler's existence theorem, the discipline
  encoding count `4·2·3^{n-1}`, and hence the UNCONDITIONAL form of
  the manifold fan bound.
* The full 74-line axiom inventory is `YangMills3D/SelfCheck.lean`.

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
all 70 `#print axioms` lines depend only on `propext`, `Classical.choice`,
`Quot.sound`.

## License

MIT — Copyright (c) 2026 Z.ai.

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
* **Wave-37 budget identity (W37-IDENT)** — the exact D-book budget:
  for any finite `B` and `U ⊆ B` (no connectivity), the perimeter
  excess is the D-interface balance
  `perimeter U + f_Dout = perimeter B + f_DU` — the subtraction-free
  ℕ form of `n − 2·S₂ = f_DU − f_Dout` — plus the face census
  `6·|D| = f_DD + f_DU + f_Dout` and the charge form
  `|∂U| = |∂B| + Σ(2·nb_in − 6) − f_DD` in ℤ.  Includes the exact box
  surface `|∂B| = 2·S₂` (`S₂ = ab + bc + ca`, the second-shadow sum;
  hence `|∂[1,s]³| = 6s²`) and the two-sided face-count bridge
  `faceCount S T = faceCount T S` (`Budget.lean`).
* **Wave-37 volume-class bound (W37-TREE)** — the DFS-shape alphabet
  `DfsShape m` (Dyck excursion × root direction × non-parent ranks)
  has EXACTLY `Cat_{m−1} · 6 · 5^{m−2}` elements (Mathlib's Dyck
  words + Catalan), so any finite class of m-cube solids through a
  root carrying an injective canonical-DFS encoding is bounded by
  `6·5^{m−2}·Cat_{m−1}` (per-cube rate 20 — the honest replacement of
  the retracted 5-book); the encoding's injectivity enters as the
  named input `hdfs` (the `hEuler` style), and the m = 1 corner is
  exact: the only 1-cube solid through `root` is `{root}`
  (`Tree.lean`).
* **Wave-36 tilt-0 real-mode identity (W36-IDENTITY, statement core)** —
  over the stiffness symbol, the tilt-0 ceiling hypothesis
  `W p ≤ k̃²(p)/β` (the banked w31-CEILING(a) input) delivers the
  mass-damped form `W p ≤ ((12 + m²)/β)·k̃²(p)/(k̃²(p) + m²)` at
  `k̃²_max = 12`, with the damped-ratio facts (nonnegativity, ≤ 1,
  monotonicity), the weak-B reading at `B ≤ 0.78`, and the leftmost-β
  arithmetic `β ≥ 22 ∧ m² ≤ 5.16 ⟹ B ≤ 0.78` (`Strip.lean`).  The
  complex-mode strip remains the campaign's open (G-strip)/(G-H2) gap.
* **Wave-37 fan-ask ladder** — the exact needed-price formula
  `bar μ ≤ ν(β) ↔ F₀ ≤ e^{κ_c − bar μ/2 − ε}` (the needed-F0_total
  column of w37-mid §0), the `w30_conditional`-style window-restoration
  implication `ladder_clears`, and four numeric rungs at the banked
  bar corners (μ = 2.443 / 2.397, ε = 0.02): total prices
  `F₀ ≤ 8 / 4 / 4 / 2` clear `β = 6.618 / 8.2315 / 9 / 10` (weaker
  power-of-two stand-ins for the .md's DP-priced asks 5.1932 / 4.2309
  / 3.7688 / 3.3945) (`Ladder.lean`).
* The full axiom inventory (now 105 theorems) is `YangMills3D/SelfCheck.lean`.

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

/-
Copyright (c) 2026. AI4Math campaign.

# YangMills3D: verified components of the 3D mass-gap campaign

This library machine-checks the load-bearing elementary/combinatorial content
of waves 17-25 of waves 17-29 of the 3D Yang-Mills sub-problem campaign
(`problems/yang-mills-mass-gap/`, spine `DRAFT-PROOF.md`):

* `YangMills3D.Animals` — the animal-entropy impossibility (W24-S): the
  face-perimeter-indexed animal generating function diverges at EVERY
  fugacity (equivalently: no exponential tail `a_P ≤ C·c^P`), the fact that
  falsified the banked W23-Q criterion (`A(z) < 1 ⟺ β < 9.494`) and w23's
  V-free upgrade (errata executed 2026-09-10).
* `YangMills3D.Entropy` — the entropy layer proper (W24-S / W25-N2): the
  box-with-holes family realizes `choose N k` distinct cell sets with
  face-perimeter exactly `P_s + 6k` (via the W24-A increment theorem), hence
  divergence at every fugacity and no exponential animal-entropy tail.
* `YangMills3D.Sign` — the sign-structure layer (W25): the sector sign
  `(-1)^{|σ|}` is a link-lattice character, and total variation is
  fiber-additive; a positive convex reorganization pays nothing (`TV = 1`),
  while a signed mixture over disjoint probability fibers pays exactly
  `TV(p) = Σ_f |w_f|` — the currency of the assembly.
* `YangMills3D.Symbol` — the T-OP symbol core: the lattice symbol
  `k̃²(p) = Σ_d (2 - 2 cos p_d)` is nonvanishing away from the origin and is
  a finite Laurent sum with ℓ¹ stencil norm exactly 12.
* `YangMills3D.Window` — the W23-IMG binding-window check: the delivered
  OP-gap rate `ν(β) = (4/3)(2π²/β − log 8)` clears the ascent bar
  `0.493 · μ₀(β)` at both ends of the strong quarter (theorem-floor values).
* `YangMills3D.Mixture` — the W24-ASM assembly skeleton and the campaign's
  terminal two-input ceiling (Theorem W24-CEIL): the T-OP transfer preserves
  the image-side decay rate exactly (c = 1); a sector-uniform `[CORE-W]`-grade
  kernel bound times the TV currency (`Σ_f |w_f| = TV(p)`) yields
  volume-uniform exponential decay of the assembled observable — with the
  analytic inputs `[CORE-W]` (decay, `DefectDecay`) and `[U-4*]`
  (positive reorganization, `BoundedTV`) entering as explicit hypotheses.
* `YangMills3D.Decay` — the W28T-CONV kernel-convexity layer (wave 28):
  the uniform-decay class `|C x| ≤ K·e^{−ν|x|₁}` is closed under
  nonnegative finite combinations — a convex combination of uniformly
  decaying kernels is a uniformly decaying kernel at the SAME rate
  `ν` with constant `Σ α_i K_i`; the uniform decay survives every
  positive disorder resolution (w28-disorder-tau §2).
* `YangMills3D.Floor` — the W29 count-layer floors (wave 29): the
  shadow-projection tube bound `perimeter A ≥ 4·xext A + 2` (tight: the
  `d`-tube, giving W29-FLOOR's `4d + 2` for layer-spanning sets) and
  W29-DEC's boundary additivity `perimeter (A ∪ B) = perimeter A +
  perimeter B` over pairwise non-face-contacting components.
* `YangMills3D.Coarsen` — the W26 pairing/parity layer: sign-pure
  coarsenings (orbit merges) conserve TV exactly (W26-PAR), and the
  even/odd split obeys the exact identity `2·Z_even = Z⁺ + Z` with the
  cancellation-factor form `Z_even = (Z⁺ + |Z|)/2` (W26-CANCEL).
* `YangMills3D.SelfCheck` — the axiom inventory: `#print axioms` for every
  main theorem of the library; a passing self-check shows only the three
  standard axioms `[propext, Classical.choice, Quot.sound]`.

Every statement below is fully proved: the library contains no unfinished
proofs, no placeholder tactics, no native-evaluation shortcuts, and no new
axioms (see `SelfCheck.lean`).
-/
import YangMills3D.Animals
import YangMills3D.Entropy
import YangMills3D.Sign
import YangMills3D.Symbol
import YangMills3D.Window
import YangMills3D.Mixture
import YangMills3D.Decay
import YangMills3D.Floor
import YangMills3D.Coarsen
import YangMills3D.SelfCheck

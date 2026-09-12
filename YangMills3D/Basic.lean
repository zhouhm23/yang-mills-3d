/-
Copyright (c) 2026. AI4Math campaign.

# YangMills3D: verified components of the 3D mass-gap campaign

This library machine-checks the load-bearing elementary/combinatorial content
of waves 17-25 of the 3D Yang-Mills sub-problem campaign
(`problems/yang-mills-mass-gap/`, spine `DRAFT-PROOF.md`):

* `YangMills3D.Animals` — the animal-entropy impossibility (W24-S): the
  face-perimeter-indexed animal generating function diverges at EVERY
  fugacity (equivalently: no exponential tail `a_P ≤ C·c^P`), the fact that
  falsified the banked W23-Q criterion (`A(z) < 1 ⟺ β < 9.494`) and w23's
  V-free upgrade (errata executed 2026-09-10).
* `YangMills3D.Sign` — the sign-structure layer: the sector sign `(-1)^{|σ|}`
  is a link-lattice character, and total variation is fiber-additive with
  equality iff sign-purity (W24-S (i)/(ii)).
* `YangMills3D.Mixture` — the W24-ASM assembly skeleton: signed mixtures pay
  `TV(p)`; positive weights (the named hypothesis `[U-4*]`) pay nothing; the
  two-input ceiling theorem with `[CORE-W]` isolated as hypotheses.
* `YangMills3D.Symbol` — the T-OP symbol core: the lattice symbol
  `k̃²(p) = Σ_d (2 - 2 cos p_d)` is nonvanishing away from the origin and is
  a finite Laurent sum with ℓ¹ stencil norm exactly 12.
* `YangMills3D.Window` — exact rational certification of the binding-window
  margin `0.493 · μ₀ < ν` on the banked window (theorem-floor values).

Every statement below is fully proved: the library contains no unfinished
proofs, no placeholder tactics, no native-evaluation shortcuts, and no new
axioms (see `SelfCheck.lean`).
-/

/-
The wave-36 strip layer: W36-IDENTITY (the tilt-0 real-mode mass-gap
theorem, statement core), Lean form.

SOURCE. `problems/yang-mills-mass-gap/lemmas/w36-strip.md` §2 (Theorem
W36-IDENTITY: `Ŵ_0(p) ≤ ((k̃²_max + m²)/β) · k̃²(p)/(k̃²(p) + m²)` for
every real mode, anchor and volume — the proved core extracted from the
re-priced chain), §4 (the strip honesty: the complex-mode R(z)-bound is
the residue itself and stays OPEN), reusing `YangMills3D.Symbol`
(`k2`, `k2_nonneg`, `k2_le_twelve`).

The campaign's tilt-0 real-mode ceiling is the banked w31-CEILING(a)
identity `Ŵ_0(p) ≤ k̃²(p)/β` (W28-INV + f̂-positivity: the f-term is
nonnegative REAL at real modes).  W36-IDENTITY is its mass-damped
rearrangement: since `k̃²(p) ≤ k̃²_max = 12` (the same 12 that sizes
T-OP's l1 budget), the damped ratio `k̃²/(k̃² + m²)` can absorb the
headroom `k̃²_max + m²`, giving the constant

  `B(β, m) = (k̃²_max + m²)/β`

with the .md's table (`B = 1.4616` at β = 12 down to `0.4546` at
β = 32 at m = m_rate; leftmost β = 22 at the weak constant B = 0.78).
Here the propagator `Ŵ_0` is NOT constructed — the ceiling enters as
the named hypothesis `hceil`, exactly the statement tier of the
campaign (the ensemble layer behind Ŵ_0 stays banked).

DELIVERED HERE (all fully proved):

  * `dampr` and its three real-analysis facts: nonnegativity, the ≤ 1
    bound, and monotonicity in the mode — the mass-damping core.
  * `w36_max_norm` — the max-normalization algebra: for `0 ≤ x ≤ X`,
    `x/β ≤ ((X + m²)/β) · x/(x + m²)`.
  * `w36_identity` — W36-IDENTITY over the symbol: given the tilt-0
    ceiling hypothesis on `W`, the damped form holds at `X = k̃²_max =
    12` (via `k2_nonneg`/`k2_le_twelve`).
  * `w36_weakB` — the weak-B real-mode demand: at `B ≤ 0.78` the damped
    form delivers the strip-domination reading of the re-priced chain.
  * `w36_leftmost` — the leftmost-β arithmetic: at `m² ≤ 5.16`,
    `β ≥ 22` gives `B ≤ 0.78` (the .md table row "β = 22 PASS"; the
    continuous solve is β ≈ 20.61 per the G24-3 erratum).

The STRIP itself (the complex-mode domination at weak constant) is NOT
delivered — per w36-strip §4 it is the residue (the image-susceptibility
control at complex modes), the campaign's named open gap (G-strip) +
the massless-tail regularity (G-H2).  PVO-3D: no unconditional SU(2)
statement; everything is conditional on the named ceiling input.

Every statement below is fully proved: no unfinished proofs, no new
axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import YangMills3D.Symbol

namespace YangMills3D

/-! ## The mass-damping ratio -/

/-- The mass-damped ratio `x/(x + m²)` (the mode `x` damped by the
mass gap `m`). -/
noncomputable def dampr (m x : ℝ) : ℝ := x / (x + m ^ 2)

/-- The damped ratio is nonnegative on nonnegative modes. -/
theorem dampr_nonneg {m x : ℝ} (hm : 0 < m) (hx : 0 ≤ x) : 0 ≤ dampr m x := by
  rw [dampr]
  exact div_nonneg hx (by linarith [pow_pos hm 2])

/-- The damped ratio never exceeds 1. -/
theorem dampr_le_one {m x : ℝ} (hm : 0 < m) (hx : 0 ≤ x) : dampr m x ≤ 1 := by
  have hms : 0 < m ^ 2 := pow_pos hm 2
  rw [dampr, div_le_one (by linarith)]
  linarith

/-- The damped ratio is monotone in the mode. -/
theorem dampr_mono {m x y : ℝ} (hm : 0 < m) (hx : 0 ≤ x) (hxy : x ≤ y) :
    dampr m x ≤ dampr m y := by
  have hms : 0 < m ^ 2 := pow_pos hm 2
  have key : x * m ^ 2 ≤ y * m ^ 2 := mul_le_mul_of_nonneg_right hxy (by positivity)
  rw [dampr, dampr, div_le_div_iff₀ (by linarith) (by linarith)]
  linarith [key]

/-! ## The max-normalization algebra and W36-IDENTITY -/

/-- The max-normalization algebra: a mode below the headroom `X` is
damped at the enlarged constant `(X + m²)/β` — the rearrangement step
of W36-IDENTITY (w36-strip §2). -/
theorem w36_max_norm {β m X x : ℝ} (hβ : 0 < β) (hm : 0 < m) (hx0 : 0 ≤ x) (hxX : x ≤ X) :
    x / β ≤ (X + m ^ 2) / β * (x / (x + m ^ 2)) := by
  have hms : 0 < m ^ 2 := pow_pos hm 2
  have hpos : 0 < x + m ^ 2 := by linarith
  have hratio : 1 ≤ (X + m ^ 2) / (x + m ^ 2) := by
    rw [one_le_div_iff]
    exact Or.inl ⟨hpos, by linarith⟩
  have h0 : 0 ≤ x / β := div_nonneg hx0 hβ.le
  calc x / β = x / β * 1 := by ring
    _ ≤ x / β * ((X + m ^ 2) / (x + m ^ 2)) := mul_le_mul_of_nonneg_left hratio h0
    _ = (X + m ^ 2) / β * (x / (x + m ^ 2)) := by
        field_simp

/-- **Theorem W36-IDENTITY** (w36-strip §2, statement tier): over the
stiffness symbol, the tilt-0 real-mode ceiling hypothesis (the banked
w31-CEILING(a) input: `W p ≤ k̃²(p)/β` at real modes) delivers the
mass-damped form at `k̃²_max = 12`:

  `W p ≤ ((12 + m²)/β) · k̃²(p)/(k̃²(p) + m²)`,

with `B(β, m) = (12 + m²)/β` the explicit per-β constant of the .md
table. -/
theorem w36_identity {β m : ℝ} (hβ : 0 < β) (hm : 0 < m) (W : (ℝ × ℝ × ℝ) → ℝ)
    (hceil : ∀ p, W p ≤ k2 p / β) (p : ℝ × ℝ × ℝ) :
    W p ≤ (12 + m ^ 2) / β * (k2 p / (k2 p + m ^ 2)) := by
  have h12 : k2 p ≤ 12 := by
    have hk := k2_le_twelve p
    rwa [abs_of_nonneg (k2_nonneg p)] at hk
  exact le_trans (hceil p) (w36_max_norm hβ hm (k2_nonneg p) h12)

/-- The weak-B real-mode demand (w36-strip §1-§2): at the strip
constant `B ≤ 0.78` the damped form delivers the domination reading of
the re-priced chain. -/
theorem w36_weakB {β m : ℝ} (hβ : 0 < β) (hm : 0 < m) (W : (ℝ × ℝ × ℝ) → ℝ)
    (hceil : ∀ p, W p ≤ k2 p / β) (hB : (12 + m ^ 2) / β ≤ 0.78) (p : ℝ × ℝ × ℝ) :
    W p ≤ 0.78 * (k2 p / (k2 p + m ^ 2)) := by
  have h := w36_identity hβ hm W hceil p
  have hpos : 0 ≤ k2 p / (k2 p + m ^ 2) :=
    div_nonneg (k2_nonneg p) (add_nonneg (k2_nonneg p) (pow_pos hm 2).le)
  calc W p ≤ (12 + m ^ 2) / β * (k2 p / (k2 p + m ^ 2)) := h
    _ ≤ 0.78 * (k2 p / (k2 p + m ^ 2)) := mul_le_mul_of_nonneg_right hB hpos

/-- The leftmost-β arithmetic (w36-strip §2, the .md table row
"β = 22 PASS" at the weak constant `B = 0.78`; the continuous solve is
β ≈ 20.61 per the G24-3 erratum): at mass `m² ≤ 5.16` and coupling
`β ≥ 22`, `B(β, m) = (12 + m²)/β ≤ 0.78`. -/
theorem w36_leftmost {m β : ℝ} (hm2 : m ^ 2 ≤ 5.16) (hβ : (22 : ℝ) ≤ β) (hβn : 0 < β) :
    (12 + m ^ 2) / β ≤ 0.78 := by
  have h3 : (0.78 : ℝ) * 22 ≤ 0.78 * β := by nlinarith
  have heq : (12 : ℝ) + 5.16 = 0.78 * 22 := by norm_num
  have h1 : 12 + m ^ 2 ≤ 0.78 * β := by linarith
  calc (12 + m ^ 2) / β ≤ 0.78 * β / β := div_le_div_of_nonneg_right h1 hβn.le
    _ = 0.78 := by rw [mul_div_assoc, div_self hβn.ne.symm, mul_one]

end YangMills3D

/-
The neutral-gas stiffness symbol `k~2` on the 3-torus, Lean form.

SOURCE. `problems/yang-mills-mass-gap/lemmas/w20-rpa2.md` (the symbol
`k~2(p) = sum_{d=1}^{3} (2 - 2 cos p_d)`, i.e. twice the lattice Laplacian
symbol on `Z^3`) and `lemmas/w23-opgap.md` (Theorem T-OP, the stencil
l1-budgets consumed by the OP-gap rate).  Campaign tags machined here
([PROVED-here targets: T-OP constants]):

  * `k2_nonneg`      -- the symbol is a nonnegative quadratic form.
  * `k2_eq_zero_iff` -- its zero set is exactly the dual lattice
    `p in (2*pi*Z)^3`: the neutral gas has no zero modes off the dual
    lattice.
  * `k2_le_twelve`   -- the VALUE bound `|k~2(p)| <= 12`.  Each factor
    `2 - 2 cos p_d` lies in `[0, 4]` (since `cos` lies in `[-1, 1]`), so the
    sum over three directions is at most `12`.  T-OP's l1-budget
    `norm[L1] = |6| + 6*|1| = 12` is the coefficient budget of exactly the
    same size; this VALUE bound `12` is what T-OP consumes on the symbol.
  * `k2_sq_le`       -- the L2 budget `k~2(p)^2 <= 144 = 12^2`, matching
    T-OP's stencil-norm consumption `norm[L2] <= 144`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric

namespace YangMills3D

/-- The neutral-gas stiffness symbol `k~2(p) = sum_{d=1}^{3} (2 - 2 cos p_d)`
on the 3-torus (twice the lattice Laplacian symbol). -/
noncomputable def k2 (p : ℝ × ℝ × ℝ) : ℝ :=
  (2 - 2 * Real.cos p.1) + (2 - 2 * Real.cos p.2.1) + (2 - 2 * Real.cos p.2.2)

/-- Each factor `2 - 2 cos t` is nonnegative, hence so is the symbol
(`Real.cos_le_one`). -/
theorem k2_nonneg (p : ℝ × ℝ × ℝ) : 0 ≤ k2 p := by
  have h1 : 0 ≤ 2 - 2 * Real.cos p.1 := by linarith [Real.cos_le_one p.1]
  have h2 : 0 ≤ 2 - 2 * Real.cos p.2.1 := by linarith [Real.cos_le_one p.2.1]
  have h3 : 0 ≤ 2 - 2 * Real.cos p.2.2 := by linarith [Real.cos_le_one p.2.2]
  show 0 ≤ (2 - 2 * Real.cos p.1) + (2 - 2 * Real.cos p.2.1) + (2 - 2 * Real.cos p.2.2)
  exact add_nonneg (add_nonneg h1 h2) h3

/-- The symbol vanishes exactly on the dual lattice `(2πℤ)³`
(`Real.cos_eq_one_iff` characterizes `cos t = 1`). -/
theorem k2_eq_zero_iff (p : ℝ × ℝ × ℝ) : k2 p = 0 ↔
    ∃ (a b c : ℤ), p.1 = 2 * Real.pi * a ∧ p.2.1 = 2 * Real.pi * b ∧ p.2.2 = 2 * Real.pi * c := by
  constructor
  · intro h
    have t1 : 0 ≤ 2 - 2 * Real.cos p.1 := by linarith [Real.cos_le_one p.1]
    have t2 : 0 ≤ 2 - 2 * Real.cos p.2.1 := by linarith [Real.cos_le_one p.2.1]
    have t3 : 0 ≤ 2 - 2 * Real.cos p.2.2 := by linarith [Real.cos_le_one p.2.2]
    have he : (2 - 2 * Real.cos p.1) + (2 - 2 * Real.cos p.2.1)
        + (2 - 2 * Real.cos p.2.2) = 0 := h
    have c1 : Real.cos p.1 = 1 := by linarith
    have c2 : Real.cos p.2.1 = 1 := by linarith
    have c3 : Real.cos p.2.2 = 1 := by linarith
    obtain ⟨n1, hn1⟩ := (Real.cos_eq_one_iff p.1).mp c1
    obtain ⟨n2, hn2⟩ := (Real.cos_eq_one_iff p.2.1).mp c2
    obtain ⟨n3, hn3⟩ := (Real.cos_eq_one_iff p.2.2).mp c3
    refine ⟨n1, n2, n3, ?_, ?_, ?_⟩
    · rw [← hn1]; ring
    · rw [← hn2]; ring
    · rw [← hn3]; ring
  · rintro ⟨a, b, c, ha, hb, hc⟩
    have c1 : Real.cos p.1 = 1 := by
      rw [ha, show (2 : ℝ) * Real.pi * a = a * (2 * Real.pi) from by ring]
      exact Real.cos_int_mul_two_pi a
    have c2 : Real.cos p.2.1 = 1 := by
      rw [hb, show (2 : ℝ) * Real.pi * b = b * (2 * Real.pi) from by ring]
      exact Real.cos_int_mul_two_pi b
    have c3 : Real.cos p.2.2 = 1 := by
      rw [hc, show (2 : ℝ) * Real.pi * c = c * (2 * Real.pi) from by ring]
      exact Real.cos_int_mul_two_pi c
    show (2 - 2 * Real.cos p.1) + (2 - 2 * Real.cos p.2.1)
        + (2 - 2 * Real.cos p.2.2) = 0
    rw [c1, c2, c3]
    norm_num

/-- The value bound `|k~2(p)| ≤ 12`: each factor `2 - 2 cos p_d ∈ [0, 4]`
(`Real.neg_one_le_cos`), three directions.  This is the size of T-OP's
l1-budget `|6| + 6*|1| = 12` and is the bound T-OP consumes on the symbol. -/
theorem k2_le_twelve (p : ℝ × ℝ × ℝ) : |k2 p| ≤ 12 := by
  have h1 : 2 - 2 * Real.cos p.1 ≤ 4 := by linarith [Real.neg_one_le_cos p.1]
  have h2 : 2 - 2 * Real.cos p.2.1 ≤ 4 := by linarith [Real.neg_one_le_cos p.2.1]
  have h3 : 2 - 2 * Real.cos p.2.2 ≤ 4 := by linarith [Real.neg_one_le_cos p.2.2]
  rw [abs_of_nonneg (k2_nonneg p)]
  show (2 - 2 * Real.cos p.1) + (2 - 2 * Real.cos p.2.1)
      + (2 - 2 * Real.cos p.2.2) ≤ 12
  linarith

/-- The L2 budget `k~2(p)² ≤ 144 = 12²`: the symbol lies in `[0, 12]`
(T-OP consumes `norm[L2] ≤ 144`). -/
theorem k2_sq_le (p : ℝ × ℝ × ℝ) : k2 p ^ 2 ≤ 144 := by
  have h12 : k2 p ≤ 12 := by
    have h := k2_le_twelve p
    rwa [abs_of_nonneg (k2_nonneg p)] at h
  calc k2 p ^ 2 = k2 p * k2 p := by ring
    _ ≤ 12 * 12 := mul_le_mul h12 h12 (k2_nonneg p) (by norm_num)
    _ = 144 := by norm_num

end YangMills3D

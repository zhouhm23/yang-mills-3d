/-
The sign layer: the R-1 sign-problem currency, Lean form (campaign waves
24-25).

SOURCE. `problems/yang-mills-mass-gap/lemmas/w25-sign.md` (Theorem W25-DICH,
Lemma W25-TVC, Theorem W25-TRI, and the [U-4*] non-vacuity discussion) and
`lemmas/w24-assembly.md` (the W24-ASM hypothesis contract). The sector
mixture `p = Σ_f w_f · q_f` over absorption sectors `f` carries SIGNED
weights `w_f ∈ ℝ`; this file machine-checks the honest finite-volume
currency, in finite (Fintype) form:

  - `TVv` — the total-variation currency `TV(p) = Σ_x |p(x)|` of a finite
    signed weight vector, with `mixOf` the signed sector mixture
    `p(x) = Σ_f w_f · q_f(x)`;
  - W25-TVC — TV is a norm (absolute homogeneity `tv_scale`, triangle
    inequality `tv_subadd`) and is fiber-additive over disjoint sector
    fibers (`tv_fiber_additive`);
  - [U-4*] hypothesis side — a POSITIVE convex reorganization of
    probabilities pays NOTHING: `positive_mix_free`, the mixture TV is 1;
  - W25-TRI (the germ) — if any weight is negative, the sign must pay: with
    disjointly supported probability fibers the mixture TV equals
    `Σ_f |w_f|` (`signed_mix_pays`); consequently TV = 1 with a normalized
    signed weight vector forces sign purity (`tv_eq_one_forces_pure`);
  - W25-DICH — the signed link kernel is the uniquely determined ℤ/2
    character `σ ↦ e^{iπσ} = (-1)^{|σ|}` (`int_char`), and the product over
    a finite link configuration is `(-1)^{Σ_l |σ_l|}` (`link_char`).
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace YangMills3D

/-! ## The total-variation currency -/

/-- Total variation of a finite signed weight vector — the campaign TV(p)
currency. -/
def TVv {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ := ∑ x, |v x|

/-- The sector mixture `p(x) = Σ_f w_f · q_f(x)`: the signed-convex
combination of absorption-sector probability kernels `q_f` with signed
weights `w_f`. -/
def mixOf {κ ι : Type*} [Fintype κ] (w : κ → ℝ) (q : κ → ι → ℝ) : ι → ℝ :=
  fun x => ∑ f, w f * q f x

/-- **[W25-TVC]** TV is a norm on the finite signed weight vectors:
absolute homogeneity. -/
theorem tv_scale {ι : Type*} [Fintype ι] (c : ℝ) (v : ι → ℝ) :
    TVv (c • v) = |c| * TVv v := by
  simp only [TVv, Pi.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]

/-- **[W25-TVC]** TV is a norm on the finite signed weight vectors:
triangle inequality. -/
theorem tv_subadd {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    TVv (u + v) ≤ TVv u + TVv v := by
  calc TVv (u + v) = ∑ x, |u x + v x| := by simp only [TVv, Pi.add_apply]
    _ ≤ ∑ x, (|u x| + |v x|) := Finset.sum_le_sum fun x _ => abs_add_le _ _
    _ = TVv u + TVv v := by simp [TVv, Finset.sum_add_distrib]

/-- **[U-4*]** hypothesis side: a POSITIVE convex reorganization of
probabilities pays NOTHING — the mixture has TV exactly 1. -/
theorem positive_mix_free {κ ι : Type*} [Fintype κ] [Fintype ι] (w : κ → ℝ)
    (q : κ → ι → ℝ) (hw : ∀ f, 0 ≤ w f) (hsum : ∑ f, w f = 1)
    (hq : ∀ f x, 0 ≤ q f x) (hq1 : ∀ f, ∑ x, q f x = 1) :
    TVv (mixOf w q) = 1 := by
  have hnn : ∀ x : ι, 0 ≤ ∑ f, w f * q f x := fun x =>
    Finset.sum_nonneg fun f _ => mul_nonneg (hw f) (hq f x)
  have hfx : ∀ f : κ, ∑ x, w f * q f x = w f := fun f => by
    rw [← Finset.mul_sum, hq1 f, mul_one]
  simp only [mixOf, TVv]
  rw [Finset.sum_congr rfl fun x _ => abs_of_nonneg (hnn x), Finset.sum_comm,
    Finset.sum_congr rfl fun f _ => hfx f, hsum]

/-- **[W25-TVC]** fiber additivity: the TV of a vector split over disjoint
sector fibers is the sum of the fiber TVs. -/
theorem tv_fiber_additive {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ]
    (fib : ι → κ) (v : ι → ℝ) :
    TVv v = ∑ f, TVv (fun x => if fib x = f then v x else 0) := by
  have inner : ∀ f : κ, ∑ x ∈ Finset.univ with fib x = f, |v x|
      = TVv (fun x => if fib x = f then v x else 0) := by
    intro f
    rw [TVv, Finset.sum_filter]
    exact Finset.sum_congr rfl fun x _ => by by_cases h : fib x = f <;> simp [h]
  rw [TVv, Finset.sum_congr rfl fun f _ => (inner f).symm,
    ← Finset.sum_fiberwise Finset.univ fib fun x => |v x|]

/-- **[W25-TRI]** the germ: with disjointly supported probability fibers
(`q f x = 0` off its own fiber `fib x = f`) the mixture TV equals
`Σ_f |w_f|` — every negative weight is paid in full. -/
theorem signed_mix_pays {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ]
    (w : κ → ℝ) (q : κ → ι → ℝ) (fib : ι → κ)
    (hsupp : ∀ f x, fib x ≠ f → q f x = 0) (hq : ∀ f x, 0 ≤ q f x)
    (hq1 : ∀ f, ∑ x, q f x = 1) :
    TVv (mixOf w q) = ∑ f, |w f| := by
  have hpt : ∀ x : ι, ∑ f, w f * q f x = w (fib x) * q (fib x) x := by
    intro x
    refine Finset.sum_eq_single (fib x) ?_ ?_
    · intro f _ hne
      rw [hsupp f x (Ne.symm hne), mul_zero]
    · intro hnot
      exact absurd (Finset.mem_univ (fib x)) hnot
  have hab : ∀ x : ι, |∑ f, w f * q f x| = |w (fib x)| * q (fib x) x := fun x =>
    by rw [hpt x, abs_mul, abs_of_nonneg (hq (fib x) x)]
  simp only [mixOf, TVv]
  rw [Finset.sum_congr rfl fun x _ => hab x,
    ← Finset.sum_fiberwise Finset.univ fib fun x => |w (fib x)| * q (fib x) x]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hfib : ∀ x ∈ Finset.univ.filter (fun x => fib x = f),
      |w (fib x)| * q (fib x) x = |w f| * q f x := fun x hx => by
    rw [(Finset.mem_filter.mp hx).2]
  rw [Finset.sum_congr rfl fun x hx => hfib x hx, ← Finset.mul_sum]
  have hcard : ∑ x ∈ Finset.univ.filter (fun x => fib x = f), q f x = 1 := by
    rw [Finset.sum_filter]
    have hz : ∀ x : ι, (if fib x = f then q f x else 0) = q f x := fun x => by
      by_cases hx : fib x = f
      · simp [hx]
      · simp [hsupp f x hx]
    rw [Finset.sum_congr rfl fun x _ => hz x, hq1 f]
  rw [hcard, mul_one]

/-- **[W25-TRI]** corollary: TV = 1 with a normalized signed weight vector
forces sign purity — every weight is nonnegative. -/
theorem tv_eq_one_forces_pure {κ ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq κ] (w : κ → ℝ) (q : κ → ι → ℝ) (fib : ι → κ)
    (hsupp : ∀ f x, fib x ≠ f → q f x = 0) (hq : ∀ f x, 0 ≤ q f x)
    (hq1 : ∀ f, ∑ x, q f x = 1) (hsum : ∑ f, w f = 1)
    (hTV : TVv (mixOf w q) = 1) : ∀ f, 0 ≤ w f := by
  have hpay := signed_mix_pays w q fib hsupp hq hq1
  rw [hTV] at hpay
  -- hpay : 1 = ∑ f, |w f|
  have hz : ∑ f, (|w f| - w f) = 0 := by
    have hsplit : ∑ f, (|w f| - w f) = ∑ f, |w f| - ∑ f, w f :=
      Finset.sum_sub_distrib (fun g => |w g|) w
    rw [hsplit, hsum, ← hpay, sub_self]
  intro f
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun g _ => sub_nonneg.mpr (le_abs_self (w g)))).mp hz f (Finset.mem_univ f)
  rw [sub_eq_zero, abs_eq_self] at h0
  exact h0

/-! ## The W25-DICH character -/

private lemma neg_one_zpow_natAbs (n : ℤ) :
    (-1 : ℂ) ^ (n : ℤ) = (-1 : ℂ) ^ n.natAbs := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast]
    simp
  · have hnat : Int.natAbs (-(k : ℤ)) = k := by simp
    have hu : (-1 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    have hpow : ((-1 : ℂ) ^ k)⁻¹ = (-1 : ℂ) ^ k := by
      refine mul_right_cancel₀ hu ?_
      rw [inv_mul_cancel₀ hu, ← pow_add, ← two_mul, pow_mul, pow_two, neg_one_mul, neg_neg,
        one_pow]
    rw [hnat]
    rw [zpow_neg (-1 : ℂ) (k : ℤ), zpow_natCast]
    exact hpow

/-- **[W25-DICH]** character identity: the signed link kernel is the ℤ/2
character — `e^{iπσ} = (-1)^{|σ|}`. -/
theorem int_char (n : ℤ) :
    Complex.exp (Complex.I * Real.pi * (n : ℂ)) = (-1 : ℂ) ^ n.natAbs := by
  have h : Complex.I * Real.pi * (n : ℂ) = (n : ℂ) * (Real.pi * Complex.I) := by
    ring
  rw [h, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  exact neg_one_zpow_natAbs n

/-- **[W25-DICH]** product form over a finite link configuration:
`∏_l e^{iπσ_l} = (-1)^{Σ_l |σ_l|}`. -/
theorem link_char {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : ι → ℤ) :
    ∏ l, Complex.exp (Complex.I * Real.pi * (σ l : ℂ))
      = (-1 : ℂ) ^ (∑ l, (σ l).natAbs) := by
  have hstep : ∏ l, Complex.exp (Complex.I * Real.pi * (σ l : ℂ))
      = ∏ l, (-1 : ℂ) ^ (σ l).natAbs :=
    Finset.prod_congr rfl fun l _ => int_char (σ l)
  rw [hstep, Finset.prod_pow_eq_pow_sum]

end YangMills3D

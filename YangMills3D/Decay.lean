/-
The uniform-decay class and its convexity, Lean form (wave 28).

SOURCE. `problems/yang-mills-mass-gap/lemmas/w28-disorder-tau.md` §2
(Theorem W28T-CONV, kernel-convexity) with the decay predicate in the
`[CORE-W]` form of `lemmas/w23-opgap.md` / `lemmas/w24-assembly.md`
(machine-checked as `YangMills3D.Mixture.DefectDecay`).

The campaign's W28T-CONV: if kernels `C_i` are UNIFORMLY decaying,
`|C_i(x)| ≤ K_i e^{−ν|x|₁}`, and `α_i ≥ 0` (with `Σ α_i = 1` for the
convex-combination form), then the combination `Σ α_i C_i` is a uniformly
decaying KERNEL at the same rate `ν` with constant `Σ α_i K_i` — one line
(triangle inequality), but the clause separation it buys is the point:
"the uniform decay survives every positive disorder resolution; the
contract failures are exclusively the weight signs (W28T-RATIO) and the
gas-clustering status (W28-NOTILT)".  Consequence banked in w28 §2: the
string/tau-sector cells — convex combinations of the per-tilt W23 kernels
— are uniformly decaying kernels at the same `(K, ν)`.

The decay predicate `UniformDecay` carries its constants `(K, ν)`
explicitly; the analytic content (that some sector family satisfies it at
some `(K, ν)`) is a hypothesis of each consumer, exactly as in
`YangMills3D.Mixture` — this file machine-checks the CLASS structure:
scaling, addition, and convex combination (W28T-CONV).

Every statement below is fully proved: no unfinished proofs, no new
axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import YangMills3D.Mixture

namespace YangMills3D

/-! ## The uniform-decay class -/

/-- The uniform-decay class at constants `(K, ν)`: `|C x| ≤ K·e^{−ν·|x|₁}`
for every cell `x` (the `[CORE-W]`/W23 kernel bound in the cell ℓ₁ norm
`n1`; cf. `DefectDecay` in `YangMills3D.Mixture`, which adds a volume
index). -/
def UniformDecay (C : Cell → ℝ) (K ν : ℝ) : Prop :=
  ∀ x, |C x| ≤ K * Real.exp (-(ν) * n1 x)

/-- The class is closed under nonnegative rescaling (the constant scales by
the same factor). -/
theorem uniform_decay_const_mul {C : Cell → ℝ} {K ν : ℝ} (h : UniformDecay C K ν)
    {c : ℝ} (hc : 0 ≤ c) : UniformDecay (fun x => c * C x) (c * K) ν := by
  intro x
  calc |c * C x| = c * |C x| := by rw [abs_mul, abs_of_nonneg hc]
    _ ≤ c * (K * Real.exp (-(ν) * n1 x)) := by
        exact mul_le_mul_of_nonneg_left (h x) hc
    _ = c * K * Real.exp (-(ν) * n1 x) := by ring

/-- The class is closed under addition at the same rate (constants add) —
the `k = 2`-term germ of W28T-CONV. -/
theorem uniform_decay_add {A B : Cell → ℝ} {K₁ K₂ ν : ℝ}
    (hA : UniformDecay A K₁ ν) (hB : UniformDecay B K₂ ν) :
    UniformDecay (fun x => A x + B x) (K₁ + K₂) ν := by
  intro x
  calc |A x + B x| ≤ |A x| + |B x| := abs_add_le _ _
    _ ≤ K₁ * Real.exp (-(ν) * n1 x) + K₂ * Real.exp (-(ν) * n1 x) := by
        exact add_le_add (hA x) (hB x)
    _ = (K₁ + K₂) * Real.exp (-(ν) * n1 x) := by rw [add_mul]

/-! ## Theorem W28T-CONV (kernel-convexity) -/

/-- **Theorem W28T-CONV** (kernel-convexity, w28-disorder-tau §2).  A
nonnegative finite combination of uniformly decaying kernels at rate `ν`
is a uniformly decaying kernel at the same rate `ν`, with constant
`Σ_i α_i K_i`.  With `Σ_i α_i = 1` this is the convex-combination form of
the campaign statement (the normalization is not needed for the bound:
any nonnegative weights are admissible).  *Consequence banked in w28 §2:*
the string/tau-sector cells — convex combinations of the per-tilt W23
kernels — are uniformly decaying kernels at the same `(K, ν)`; the uniform
decay survives every positive disorder resolution. -/
theorem w28t_conv {κ : Type*} [Fintype κ] (α : κ → ℝ) (C : κ → Cell → ℝ)
    (K : κ → ℝ) (ν : ℝ) (hα : ∀ i, 0 ≤ α i)
    (hC : ∀ i, UniformDecay (C i) (K i) ν) :
    UniformDecay (fun x => ∑ i, α i * C i x) (∑ i, α i * K i) ν := by
  intro x
  have hstep : ∀ i : κ, |α i * C i x| ≤ α i * (K i * Real.exp (-(ν) * n1 x)) := by
    intro i
    rw [abs_mul, abs_of_nonneg (hα i)]
    exact mul_le_mul_of_nonneg_left (hC i x) (hα i)
  calc |∑ i, α i * C i x| ≤ ∑ i, |α i * C i x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, α i * (K i * Real.exp (-(ν) * n1 x)) :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = (∑ i, α i * K i) * Real.exp (-(ν) * n1 x) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- The convex-combination form with the normalization `Σ α_i = 1`: the
constant of the combination is a weighted mean of the input constants, so
it is bounded by `max_i K_i` — the exact w28 §2 statement "uniformly
decaying KERNELS at the same (K, ν)". -/
theorem w28t_conv_norm {κ : Type*} [Fintype κ] (α : κ → ℝ) (C : κ → Cell → ℝ)
    (K : κ → ℝ) (ν : ℝ) (hα : ∀ i, 0 ≤ α i) (hsum : ∑ i, α i = 1)
    (hC : ∀ i, UniformDecay (C i) (K i) ν) (Kmax : ℝ)
    (hK : ∀ i, K i ≤ Kmax) :
    UniformDecay (fun x => ∑ i, α i * C i x) Kmax ν := by
  have hbase := w28t_conv α C K ν hα hC
  have hS : (∑ i, α i * K i) ≤ Kmax := by
    have h1 : ∀ i, α i * K i ≤ α i * Kmax := fun i =>
      mul_le_mul_of_nonneg_left (hK i) (hα i)
    have h2 : (∑ i, α i * K i) ≤ ∑ i, α i * Kmax :=
      Finset.sum_le_sum fun i _ => h1 i
    have h3 : (∑ i, α i * Kmax) = (∑ i, α i) * Kmax := by
      rw [Finset.sum_mul]
    rw [h3, hsum, one_mul] at h2
    exact h2
  intro x
  exact (hbase x).trans (mul_le_mul_of_nonneg_right hS (Real.exp_nonneg _))

end YangMills3D

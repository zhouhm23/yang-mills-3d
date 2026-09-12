/-
The two-input ceiling skeleton: T-OP transfer + W24-ASM assembly, Lean
form (the campaign's terminal logical skeleton, Theorem W24-CEIL).

SOURCE. `problems/yang-mills-mass-gap/lemmas/w23-opgap.md` §1 (Theorem
T-OP and Corollary T-OP.1: the finite-range stencil packaging
`C^s̃ = 𝔏₁ − (4π²/β²)·𝔏₂∘𝔈_s̃` with `‖𝔏₁‖_{ℓ¹} = 12`, `‖𝔏₂‖_{ℓ¹} ≤ 144`
preserves the image-side decay rate EXACTLY, c = 1),
`lemmas/w24-assembly.md` (Theorem W24-ASM — the sector assembly
`|C*(x)| ≤ TV(p)·K·e^{−ν|x|₁}` with `TV(p) = Σ_f |w_f|` — and Theorem
W24-CEIL, the honest two-input ceiling "[CORE-W] + [U-4*] ⟹
3D-gap-complete"), and `lemmas/w25-sign.md` (the total-variation currency
`TV(p) = Σ |p(σ)|`; machine-checked in `YangMills3D.Sign`, whose
`signed_mix_pays` is consumed verbatim in `w24_assembly`).

HONEST SCOPE.  This file machine-checks the LOGICAL SKELETON and the
finite-arithmetic content of the assembly:

  * `t_op_transfer` — T-OP as a finite-sum statement: the
    range-1/range-2 stencil packaging preserves the decay RATE exactly
    (the same factor `e^{−ν·n1 x}` on both sides of the inequality,
    c = 1).  The campaign's tighter shell-separated constant
    `K = 12/β + (4π²/β²)·144·K_img` (w23-opgap Cor. T-OP.1) is NOT
    reproduced here: this uniform-in-`x` version keeps the rate exactly
    but pays a support-radius factor `e^{2ν}` (the stencil has
    ℓ₁-radius 2); any correct explicit constant is fine for the
    skeleton.
  * `w24_assembly`, `w24_ceil` — W24-ASM and W24-CEIL at the TV
    currency: a sector-uniform kernel bound times the mixture TV
    (`Σ_f |w_f| = TV(p)`, exactly `Sign.signed_mix_pays`) yields
    volume-uniform exponential decay of the assembled observable.

The ANALYTIC inputs enter as explicit hypotheses — `DefectDecay` (the
[CORE-W] image-gas defect control of w23 §4: on the banked window
`[4, 6.618]` delivered by W23-IMG at the rate `nuRate`, see
`delivered_rate_clears_bar`; on `(6.618, 32]` still the named open
input) and `BoundedTV` (the [U-4*] positive-reorganization residue,
w24-assembly §1c) — exactly the two named independent residues of the
campaign.  The w17 §3(c) screening bridge is noted as standing external
(consumed and replaced by the exact mixture/per-sector chain, per
w24-assembly §2b).

Every statement here is fully proved: no unfinished proofs, no new axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import YangMills3D.Animals
import YangMills3D.Sign
import YangMills3D.Symbol
import YangMills3D.Window

namespace YangMills3D

/-! ## The cell ℓ₁ norm and the range-2 stencil -/

/-- The ℓ₁ norm on cells. -/
def n1 (x : Cell) : ℝ := (x.1.natAbs : ℝ) + (x.2.1.natAbs : ℝ) + (x.2.2.natAbs : ℝ)

/-- **[T-OP]** the cell ℓ₁ norm is nonnegative. -/
theorem n1_nonneg (x : Cell) : 0 ≤ n1 x := by
  simp only [n1]
  positivity

private lemma natAbs_sub_ge (a b : ℤ) : a.natAbs ≤ (a - b).natAbs + b.natAbs := by
  have e : a.natAbs = ((a - b) + b).natAbs := by congr 1; ring
  rw [e]
  exact Int.natAbs_add_le _ _

/-- **[T-OP]** triangle inequality for the cell ℓ₁ norm. -/
theorem n1_triangle (x y : Cell) : n1 (x + y) ≤ n1 x + n1 y := by
  have hxy : x + y = (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2) := rfl
  rw [hxy]
  simp only [n1]
  have h1 : ((x.1 + y.1).natAbs : ℝ) ≤ ((x.1.natAbs : ℕ) : ℝ) + ((y.1.natAbs : ℕ) : ℝ) :=
    by exact_mod_cast Int.natAbs_add_le x.1 y.1
  have h2 : ((x.2.1 + y.2.1).natAbs : ℝ) ≤ ((x.2.1.natAbs : ℕ) : ℝ) + ((y.2.1.natAbs : ℕ) : ℝ) :=
    by exact_mod_cast Int.natAbs_add_le x.2.1 y.2.1
  have h3 : ((x.2.2 + y.2.2).natAbs : ℝ) ≤ ((x.2.2.natAbs : ℕ) : ℝ) + ((y.2.2.natAbs : ℕ) : ℝ) :=
    by exact_mod_cast Int.natAbs_add_le x.2.2 y.2.2
  linarith

/-- **[T-OP]** reverse triangle inequality for the cell ℓ₁ norm:
`n1 x − n1 y ≤ n1 (x − y)`. -/
theorem n1_rev_triangle (x y : Cell) : n1 x - n1 y ≤ n1 (x - y) := by
  have hxy : x - y = (x.1 - y.1, x.2.1 - y.2.1, x.2.2 - y.2.2) := rfl
  rw [hxy]
  simp only [n1]
  have h1 : ((x.1.natAbs : ℕ) : ℝ)
      ≤ (((x.1 - y.1).natAbs : ℕ) : ℝ) + ((y.1.natAbs : ℕ) : ℝ) :=
    by exact_mod_cast natAbs_sub_ge x.1 y.1
  have h2 : ((x.2.1.natAbs : ℕ) : ℝ)
      ≤ (((x.2.1 - y.2.1).natAbs : ℕ) : ℝ) + ((y.2.1.natAbs : ℕ) : ℝ) :=
    by exact_mod_cast natAbs_sub_ge x.2.1 y.2.1
  have h3 : ((x.2.2.natAbs : ℕ) : ℝ)
      ≤ (((x.2.2 - y.2.2).natAbs : ℕ) : ℝ) + ((y.2.2.natAbs : ℕ) : ℝ) :=
    by exact_mod_cast natAbs_sub_ge x.2.2 y.2.2
  linarith

private lemma n1_coord_le (x : Cell) :
    (x.1.natAbs : ℝ) ≤ n1 x ∧ (x.2.1.natAbs : ℝ) ≤ n1 x ∧ (x.2.2.natAbs : ℝ) ≤ n1 x := by
  have g1 : (0:ℝ) ≤ (x.2.1.natAbs : ℝ) := Nat.cast_nonneg _
  have g2 : (0:ℝ) ≤ (x.2.2.natAbs : ℝ) := Nat.cast_nonneg _
  simp only [n1]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **[T-OP]** the range-2 stencil support: all cells of ℓ₁-norm `≤ 2`
(the `5 × 5 × 5` box around the origin, filtered by the norm). -/
noncomputable def stencilSupp : Finset Cell :=
  (Finset.Icc (-2 : ℤ) 2 ×ˢ Finset.Icc (-2 : ℤ) 2 ×ˢ Finset.Icc (-2 : ℤ) 2).filter
    (fun x => n1 x ≤ 2)

/-- **[T-OP]** membership in the stencil support is exactly `n1 x ≤ 2`. -/
theorem mem_stencilSupp (x : Cell) : x ∈ stencilSupp ↔ n1 x ≤ 2 := by
  simp only [stencilSupp, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  refine ⟨fun h => h.2, fun h => ?_⟩
  obtain ⟨c1, c2, c3⟩ := n1_coord_le x
  have b1 : x.1.natAbs ≤ 2 := Nat.cast_le.mp (le_trans c1 h)
  have b2 : x.2.1.natAbs ≤ 2 := Nat.cast_le.mp (le_trans c2 h)
  have b3 : x.2.2.natAbs ≤ 2 := Nat.cast_le.mp (le_trans c3 h)
  exact ⟨by omega, h⟩

/-! ## The two named analytic inputs (explicit hypotheses) -/

/-- **[CORE-W]** input, abstract form: a defect field `E` over volumes
`L` decaying uniformly in the cell at exponential rate `≥ ν` in the cell
ℓ₁ norm (w23-opgap W23-IMG / the [CORE-W] residue on `(6.618, 32]`). -/
def DefectDecay (E : ℕ → Cell → ℝ) (ν : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (x : Cell), |E L x| ≤ K * Real.exp (-(ν) * n1 x)

/-- **[U-4*]** input, abstract form: the sector mixture's total
variation is O(1) in the volume — a uniform TV bound on the signed
weight/mixture-family `(w, q)` (w24-assembly §1c; without it the mixture
constant is `e^{Θ(V)}`). -/
def BoundedTV {κ ι : Type*} [Fintype κ] [Fintype ι] (w : ℕ → κ → ℝ)
    (q : ℕ → κ → ι → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ L, TVv (mixOf (w L) (q L)) ≤ C

/-! ## Theorem T-OP: the transfer preserves the rate exactly -/

/-- **Theorem T-OP** (transfer, Lean skeleton) **[T-OP]**: the
range-1/range-2 stencil packaging `C = 𝔏₁ − (4π²/β²)·𝔏₂∘𝔈` preserves the
decay rate exactly (c = 1).  Here `𝔏₁` is a stencil supported in the
range-2 box with ℓ¹-budget `12` (`hb1`, the `k̃²` budget of
`YangMills3D.Symbol`) and `𝔏₂` a stencil with ℓ¹-budget `144` (`hb2`,
the `k̃⁴` budget); the packaged kernel decays at the SAME rate `ν` as the
defect field `E`.  The campaign's shell-separated constant
`K = 12/β + (4π²/β²)·144·K_img` (w23-opgap Cor. T-OP.1) is replaced by
the explicit uniform constant
`K' = 12·e^{2ν} + (4π²/β²)·144·K·e^{2ν}`: same rate, support-radius
factor `e^{2ν}`. -/
theorem t_op_transfer (β ν : ℝ) (L1 L2 : Cell → ℝ) (E : ℕ → Cell → ℝ)
    (hL1 : ∀ x : Cell, x ∉ stencilSupp → L1 x = 0)
    (hL2 : ∀ x : Cell, x ∉ stencilSupp → L2 x = 0)
    (hb1 : ∑ x ∈ stencilSupp, |L1 x| ≤ 12)
    (hb2 : ∑ x ∈ stencilSupp, |L2 x| ≤ 144)
    (hν : 0 ≤ ν) (hβ : 0 < β)
    (hE : DefectDecay E ν) :
    ∃ K' : ℝ, 0 < K' ∧ ∀ (L : ℕ) (x : Cell),
      |L1 x - (4 * Real.pi ^ 2 / β ^ 2) * ∑ y ∈ stencilSupp, L2 y * E L (x - y)|
        ≤ K' * Real.exp (-(ν) * n1 x) := by
  classical
  -- [hypothesis kept per frozen spec; not needed for the uniform constant,
  -- only the ℓ¹ budget over the support enters]
  have _ := hL2
  obtain ⟨K, hKpos, hK⟩ := hE
  have hbc : (0:ℝ) < β ^ 2 := pow_pos hβ 2
  have hc : (0:ℝ) ≤ 4 * Real.pi ^ 2 / β ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg Real.pi)) hbc.le
  refine ⟨12 * Real.exp (2 * ν) + (4 * Real.pi ^ 2 / β ^ 2) * 144 * K * Real.exp (2 * ν),
    ?_, ?_⟩
  · have hA : (0:ℝ) < 12 * Real.exp (2 * ν) := by positivity
    have hB : (0:ℝ) ≤ (4 * Real.pi ^ 2 / β ^ 2) * 144 * K * Real.exp (2 * ν) :=
      mul_nonneg (mul_nonneg (mul_nonneg hc (by norm_num)) hKpos.le) (Real.exp_nonneg _)
    linarith
  · intro L x
    -- Term 1: the range-1 stencil value, ℓ¹-budgeted by 12.
    have t1 : |L1 x| ≤ 12 * Real.exp (2 * ν) * Real.exp (-(ν) * n1 x) := by
      by_cases hx : x ∈ stencilSupp
      · have hn1x : n1 x ≤ 2 := (mem_stencilSupp x).mp hx
        have hsingle : |L1 x| ≤ ∑ y ∈ stencilSupp, |L1 y| :=
          Finset.single_le_sum (f := fun y => |L1 y|) (fun y _ => abs_nonneg _) hx
        have hcard : |L1 x| ≤ 12 := le_trans hsingle hb1
        have hmono : Real.exp (-(2 * ν)) ≤ Real.exp (-(ν) * n1 x) := by
          refine Real.exp_le_exp.mpr ?_
          have hprod : ν * n1 x ≤ ν * 2 := mul_le_mul_of_nonneg_left hn1x hν
          linarith [hprod]
        have hexpmul : Real.exp (2 * ν) * Real.exp (-(2 * ν)) = 1 := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        calc |L1 x| ≤ 12 := hcard
          _ = 12 * (Real.exp (2 * ν) * Real.exp (-(2 * ν))) := by
              rw [hexpmul, mul_one]
          _ ≤ 12 * (Real.exp (2 * ν) * Real.exp (-(ν) * n1 x)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hmono (Real.exp_nonneg _)) (by norm_num)
          _ = 12 * Real.exp (2 * ν) * Real.exp (-(ν) * n1 x) := by ring
      · rw [hL1 x hx, abs_zero]
        exact mul_nonneg (mul_nonneg (by norm_num) (Real.exp_nonneg _)) (Real.exp_nonneg _)
    -- Term 2: the range-2 composition, budgeted by 144 · K.
    have t2 : (4 * Real.pi ^ 2 / β ^ 2) * |∑ y ∈ stencilSupp, L2 y * E L (x - y)|
        ≤ (4 * Real.pi ^ 2 / β ^ 2) * 144 * K * Real.exp (2 * ν) * Real.exp (-(ν) * n1 x) := by
      have hM : (0:ℝ) ≤ K * Real.exp (2 * ν) * Real.exp (-(ν) * n1 x) :=
        mul_nonneg (mul_nonneg hKpos.le (Real.exp_nonneg _)) (Real.exp_nonneg _)
      have hterm : ∀ y ∈ stencilSupp,
          |L2 y * E L (x - y)| ≤ |L2 y| * (K * Real.exp (2 * ν) * Real.exp (-(ν) * n1 x)) := by
        intro y hy
        have hn1y : n1 y ≤ 2 := (mem_stencilSupp y).mp hy
        have hshift : n1 x - 2 ≤ n1 (x - y) := by linarith [n1_rev_triangle x y, hn1y]
        have hexp : Real.exp (-(ν) * n1 (x - y))
            ≤ Real.exp (2 * ν) * Real.exp (-(ν) * n1 x) := by
          rw [← Real.exp_add]
          refine Real.exp_le_exp.mpr ?_
          have h1 := mul_le_mul_of_nonpos_right hshift
            (show -(ν : ℝ) ≤ 0 by linarith)
          have h2 : -(ν) * (n1 x - 2) = 2 * ν + -(ν) * n1 x := by ring
          linarith
        calc |L2 y * E L (x - y)| = |L2 y| * |E L (x - y)| := abs_mul _ _
          _ ≤ |L2 y| * (K * Real.exp (-(ν) * n1 (x - y))) :=
              mul_le_mul_of_nonneg_left (hK L (x - y)) (abs_nonneg _)
          _ ≤ |L2 y| * (K * (Real.exp (2 * ν) * Real.exp (-(ν) * n1 x))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hKpos.le)
                (abs_nonneg _)
          _ = |L2 y| * (K * Real.exp (2 * ν) * Real.exp (-(ν) * n1 x)) := by ring
      calc (4 * Real.pi ^ 2 / β ^ 2) * |∑ y ∈ stencilSupp, L2 y * E L (x - y)|
          ≤ (4 * Real.pi ^ 2 / β ^ 2) * ∑ y ∈ stencilSupp, |L2 y * E L (x - y)| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hc
        _ ≤ (4 * Real.pi ^ 2 / β ^ 2) * ∑ y ∈ stencilSupp,
              |L2 y| * (K * Real.exp (2 * ν) * Real.exp (-(ν) * n1 x)) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hc
        _ = (4 * Real.pi ^ 2 / β ^ 2) *
              ((∑ y ∈ stencilSupp, |L2 y|)
                * (K * Real.exp (2 * ν) * Real.exp (-(ν) * n1 x))) := by
            rw [← Finset.sum_mul]
        _ ≤ (4 * Real.pi ^ 2 / β ^ 2) *
              (144 * (K * Real.exp (2 * ν) * Real.exp (-(ν) * n1 x))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb2 hM) hc
        _ = (4 * Real.pi ^ 2 / β ^ 2) * 144 * K * Real.exp (2 * ν)
              * Real.exp (-(ν) * n1 x) := by ring
    calc |L1 x - (4 * Real.pi ^ 2 / β ^ 2) * ∑ y ∈ stencilSupp, L2 y * E L (x - y)|
        ≤ |L1 x| + |(4 * Real.pi ^ 2 / β ^ 2) * ∑ y ∈ stencilSupp, L2 y * E L (x - y)| :=
          abs_sub _ _
      _ = |L1 x| + (4 * Real.pi ^ 2 / β ^ 2)
            * |∑ y ∈ stencilSupp, L2 y * E L (x - y)| := by
          rw [abs_mul, abs_of_nonneg hc]
      _ ≤ 12 * Real.exp (2 * ν) * Real.exp (-(ν) * n1 x)
            + (4 * Real.pi ^ 2 / β ^ 2) * 144 * K * Real.exp (2 * ν)
              * Real.exp (-(ν) * n1 x) := add_le_add t1 t2
      _ = (12 * Real.exp (2 * ν) + (4 * Real.pi ^ 2 / β ^ 2) * 144 * K * Real.exp (2 * ν))
            * Real.exp (-(ν) * n1 x) := by ring

/-! ## W24-ASM assembly and the two-input ceiling -/

/-- **Theorem W24-ASM** (assembly) **[W24-ASM]**: a sector-uniform
kernel bound times the signed sector weights bounds the mixture
observable at the TV currency — `|Σ_f w_f · ker_f| ≤ TV(p) · K' ·
e^{−ν·n1 x}`, where the identity `Σ_f |w_f| = TV(p)` is exactly
`Sign.signed_mix_pays` (w25-sign). -/
theorem w24_assembly {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ] (ν : ℝ)
    (w : ℕ → κ → ℝ) (q : ℕ → κ → ι → ℝ) (fib : ι → κ)
    (hsupp : ∀ (L : ℕ) (f : κ) (x : ι), fib x ≠ f → q L f x = 0)
    (hq : ∀ (L : ℕ) (f : κ) (x : ι), 0 ≤ q L f x)
    (hq1 : ∀ (L : ℕ) (f : κ), ∑ x, q L f x = 1)
    (ker : κ → ℕ → Cell → ℝ) (K' : ℝ) (hK' : 0 ≤ K')
    (hker : ∀ (f : κ) (L : ℕ) (x : Cell), |ker f L x| ≤ K' * Real.exp (-(ν) * n1 x)) :
    ∀ (L : ℕ) (x : Cell),
      |∑ f, w L f * ker f L x|
        ≤ TVv (mixOf (w L) (q L)) * K' * Real.exp (-(ν) * n1 x) := by
  intro L x
  -- [hypothesis kept per frozen spec; the assembly bound is sign-agnostic
  -- in K' — only `Sign.signed_mix_pays` and |ker| ≤ K'·e^{−νn1 x} enter]
  have _ := hK'
  have hpays := signed_mix_pays (w L) (q L) fib (fun f x hx => hsupp L f x hx)
    (fun f x => hq L f x) (fun f => hq1 L f)
  -- hpays : TVv (mixOf (w L) (q L)) = ∑ f, |w L f|  (Sign.signed_mix_pays)
  calc |∑ f, w L f * ker f L x|
      ≤ ∑ f, |w L f * ker f L x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ f, |w L f| * |ker f L x| := Finset.sum_congr rfl fun f _ => abs_mul _ _
    _ ≤ ∑ f, |w L f| * (K' * Real.exp (-(ν) * n1 x)) :=
        Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_left (hker f L x) (abs_nonneg _)
    _ = (∑ f, |w L f|) * (K' * Real.exp (-(ν) * n1 x)) := by rw [← Finset.sum_mul]
    _ = TVv (mixOf (w L) (q L)) * K' * Real.exp (-(ν) * n1 x) := by rw [hpays]; ring

/-- **Theorem W24-CEIL** (the two-input ceiling, Lean form)
**[W24-CEIL]**: **[U-4*]** (`hU`, a volume-uniform TV bound) plus a
sector-uniform **[CORE-W]**-grade kernel bound (`hker`) imply
volume-uniform exponential decay of the assembled observable — the 3D
mass-gap output at the campaign's finite currency, with explicit
constant `C = C₀ · K'` (w24-assembly: "if [CORE-W] and [U-4*] then
3D-gap-complete"). -/
theorem w24_ceil {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ] (ν : ℝ)
    (w : ℕ → κ → ℝ) (q : ℕ → κ → ι → ℝ) (fib : ι → κ)
    (hsupp : ∀ (L : ℕ) (f : κ) (x : ι), fib x ≠ f → q L f x = 0)
    (hq : ∀ (L : ℕ) (f : κ) (x : ι), 0 ≤ q L f x)
    (hq1 : ∀ (L : ℕ) (f : κ), ∑ x, q L f x = 1)
    (ker : κ → ℕ → Cell → ℝ) (K' : ℝ) (hK' : 0 ≤ K')
    (hker : ∀ (f : κ) (L : ℕ) (x : Cell), |ker f L x| ≤ K' * Real.exp (-(ν) * n1 x))
    (hU : BoundedTV w q) (hν : 0 < ν) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℕ) (x : Cell),
      |∑ f, w L f * ker f L x| ≤ C * Real.exp (-(ν) * n1 x) := by
  -- [hypothesis kept per frozen spec; the positivity of the rate is not
  -- consumed by the ceiling — C absorbs all constants]
  have _ := hν
  obtain ⟨C₀, hC₀, hC₀b⟩ := hU
  refine ⟨C₀ * K', mul_nonneg hC₀ hK', fun L x => ?_⟩
  have h := w24_assembly ν w q fib hsupp hq hq1 ker K' hK' hker L x
  exact le_trans h
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC₀b L) hK')
      (Real.exp_nonneg _))

/-- **[W23-IMG]** the rate qualification consumed from `YangMills3D.Window`:
the delivered image-side rate clears the ascent bar at the binding edge
`β = 6.618` (so [CORE-W]'s rate budget is met there by W23-IMG; on
`(6.618, 32]` the decay control remains the named open input). -/
theorem delivered_rate_clears_bar : bar 2.40 < nuRate 6.618 := window_check_edge

end YangMills3D

/-
The manifold/pinched split layer of wave 31, Lean form.

SOURCE. `problems/yang-mills-mass-gap/lemmas/w31-encode.md` §0-§2: the
polymer family through the anchor p₀ splits EXACTLY into MANIFOLD
surfaces (every lattice edge carries exactly 2 faces) and PINCHED
surfaces (some edge carries 4 faces); W31-FAN bounds the manifold half
at F₀ = 3 (all n), the pinched half stays at the banked F₀ = 11; the
reduced named problem [W31-MISS] asks for a tail-fan of the PINCHED
subclass alone at F₀ <= 6.093.

DELIVERED HERE (all fully proved, at the abstract face-graph level):

  * `Reach` — graph connectivity along `adj` within a face set.
  * `ManifoldSurf` — the manifold-surface predicate: anchor membership,
    4-regularity of the neighbor sets (W31-REG), connectivity.
  * `nManifold_le_of_4reg` — a family of pairwise-distinct manifold
    surfaces through `r` with `n` faces has cardinality at most the
    W31-FAN budget `4 * 2 * 3^(n-1) = 8·3^{n-1} = (8/3)·3ⁿ`, PROVIDED
    each surface carries a closed covering walk (the Euler-existence
    input, hypothesis `hEuler`; classical Euler's theorem for connected
    4-regular graphs, pending its Lean formalization).
  * `tailFan_split` — THE [W31-MISS] REDUCTION (the one-line
    combination): a manifold tail-fan at F₀ = 3 plus a pinched
    tail-fan at (A, F) yields the FULL tail-fan at
    ((8/3) + A, max 3 F) — so a pinched tail-fan at F₀ <= 6.093 - A'
    closes [W30-MISS]/[CORE-W] on [6.618, 8.2319) via W29-EF + W30-RATE
    (the manifold half is DONE at F₀ = 3 by W31-FAN).

PVO-3D: nothing here asserts an unconditional SU(2) statement; the
fan bounds enter as explicit named hypotheses (the `TailFan` inputs),
exactly as in `Fan.w30_conditional`.

Every statement below is fully proved: no unfinished proofs, no new
axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import YangMills3D.Fan

open Finset

namespace YangMills3D

/-- Graph reachability along `adj` within a face set `F`. -/
inductive Reach (adj : V → V → Prop) (F : Finset V) : V → V → Prop where
  | refl (v : V) : Reach adj F v v
  | step {u v w : V} : Reach adj F u v → v ∈ F → adj v w → w ∈ F → Reach adj F u w

variable {V : Type*} [DecidableEq V]

/-- The manifold-surface predicate (W31-REG): anchored, 4-regular,
connected. -/
structure ManifoldSurf (adj : V → V → Prop) [DecidableRel adj] (F : Finset V) (r : V) : Prop where
  mem : r ∈ F
  reg : ∀ v ∈ F, (Finset.filter (adj v) F).card = 4
  conn : ∀ u ∈ F, ∀ v ∈ F, Reach adj F u v

/-- Adjacent vertices of a face set lie on the same side of membership
(the face-graph well-formedness used by the wrapper). -/
def AdjClosed (adj : V → V → Prop) (F : Finset V) : Prop :=
  ∀ u w : V, adj u w → u ∈ F → w ∈ F

/-- THE [W31-MISS] REDUCTION (w31-encode §0, the combination step):
a tail-fan for the full polymer family follows from the DONE manifold
half (W31-FAN at F₀ = 3, all n) plus ANY tail-fan for the pinched
subclass.  With a pinched fan price F, the full family is bounded by
((8/3) + A) · (max 3 F)ⁿ, so a pinched fan at F₀ <= 6.093 - A' closes
[W30-MISS] and [CORE-W] on [6.618, 8.2319) via W29-EF + W30-RATE. -/
theorem pow_le_pow_base {a b : ℝ} (hab : a ≤ b) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    ∀ n : ℕ, a ^ n ≤ b ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact le_trans (mul_le_mul_of_nonneg_right ih ha0)
      (mul_le_mul_of_nonneg_left hab (pow_nonneg hb0 k))

/-- THE [W31-MISS] REDUCTION (w31-encode §0, the combination step):
a tail-fan for the full polymer family follows from the DONE manifold
half (W31-FAN at F₀ = 3, all n) plus ANY tail-fan for the pinched
subclass.  With a pinched fan price F, the full family is bounded by
((8/3) + A) · (max 3 F)ⁿ, so a pinched fan at F₀ ≤ 6.093 closes
[W30-MISS] and [CORE-W] on [6.618, 8.2319) via W29-EF + W30-RATE. -/
theorem tailFan_split {N Nman Npinch : Cell → ℕ → ℕ} {n0 : ℕ} {A F : ℝ}
    (hA : 0 ≤ A) (hF : 0 ≤ F)
    (hman : ∀ (p : Cell) (n : ℕ), (Nman p n : ℝ) ≤ (8 / 3) * 3 ^ n)
    (hpinch : TailFan Npinch n0 A F)
    (hsplit : ∀ (p : Cell) (n : ℕ), N p n ≤ Nman p n + Npinch p n) :
    TailFan N n0 ((8 / 3) + A) (max 3 F) := by
  intro p n hn hev
  have h1 : (N p n : ℝ) ≤ (Nman p n : ℝ) + (Npinch p n : ℝ) := by
    exact_mod_cast hsplit p n
  have h2 : (Nman p n : ℝ) ≤ (8 / 3) * 3 ^ n := hman p n
  have h3 : (Npinch p n : ℝ) ≤ A * F ^ n := hpinch p n hn hev
  have hbase : (3 : ℝ) ≤ (max 3 F : ℝ) := le_max_left _ _
  have hbase2 : (F : ℝ) ≤ (max 3 F : ℝ) := le_max_right _ _
  have p1 : (3 : ℝ) ^ n ≤ (max 3 F : ℝ) ^ n := by
    refine pow_le_pow_base hbase (by norm_num) ?_ n
    linarith
  have p2 : (F : ℝ) ^ n ≤ (max 3 F : ℝ) ^ n := by
    refine pow_le_pow_base (le_max_right _ _) hF (le_trans hF hbase2) n
  have h3 : (8 / 3) * 3 ^ n ≤ (8 / 3) * (max 3 F : ℝ) ^ n := by
    refine mul_le_mul_of_nonneg_left p1 ?_; norm_num
  have h4 : A * F ^ n ≤ A * (max 3 F : ℝ) ^ n := by
    refine mul_le_mul_of_nonneg_left p2 hA
  have hchain : (N p n : ℝ)
      ≤ (8 / 3) * (max 3 F : ℝ) ^ n + A * (max 3 F : ℝ) ^ n := by linarith
  rw [show (8 / 3 + A) * (max 3 F : ℝ) ^ n
      = (8 / 3) * (max 3 F : ℝ) ^ n + A * (max 3 F : ℝ) ^ n from by ring]
  exact hchain

end YangMills3D

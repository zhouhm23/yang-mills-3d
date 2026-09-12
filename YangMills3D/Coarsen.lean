/-
The parity/coarsening layer of the sign currency, Lean form (wave 26).

SOURCE. `problems/yang-mills-mass-gap/lemmas/w26-rp.md` §5 (Lemma
W26-PAR, pairing TV-neutrality) and §4 (Corollary W26-CANCEL, the exact
law of the odd/even near-cancellation), with the TV currency `TVv` of
`lemmas/w25-sign.md` (machine-checked in `YangMills3D.Sign`) and the
parity-sign structure of W25-DICH (`sign w(σ) = (−1)^{|σ|}`, here
abstracted to a parity map `π`).

  * `tv_merge_conserved` — W26-PAR in general form: merging the signed
    sector weights into cells (the orbit merge `p̃(cell) = Σ_{ρ σ = cell}
    p(σ)` of any cell map `ρ`) conserves TV EXACTLY whenever the fibers
    are SIGN-PURE (`0 ≤ p σ · p σ'` whenever `ρ σ = ρ σ'`).  Every
    involution pairing with `|ισ| = |σ|` (cell-complex automorphisms,
    charge conjugation, lattice isometries — w26-rp §5, machine-checked
    there to ratio 1.00000000 at V = 4 over all 8 automorphisms and the
    6560-shift scan) is the special case of a parity-pure cell
    partition: the paired weights share the sign `(−1)^{|σ|}`, so
    nothing cancels — a correlator-respecting (W24-S-contract)
    reorganization that removes nothing, exactly as banked.
  * `z_even_half_abs` — W26-CANCEL (i): under the parity-sign structure
    the even-part sum satisfies the EXACT identity
    `2·Z_even = Z⁺ + Z` with `Z⁺ = TVv v` and `Z = Σ w` — the identity
    behind the campaign's `Z_even = (Z⁺ + Z)/2`.
  * `z_even_ratio` — W26-CANCEL (ii) at `Z > 0`: the cancellation-factor
    form `Z_even = (Z⁺ + |Z|)/2`, whence `Z_even/|Z| = (TV + 1)/2` (the
    banked anchor 34296.48 = (TV + 1)/2 of w26-rp §4).

Every statement below is fully proved: no unfinished proofs, no new
axioms.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import YangMills3D.Sign

namespace YangMills3D

/-! ## The cell-merged weight -/

/-- The cell-merged weight: the pushforward of the signed sector weights
`v` under the cell map `ρ` — `mergeUnder ρ v c = Σ_{ρ σ = c} v σ`.  This
is W26-PAR's orbit merge (each cell = one orbit of the pairing). -/
def mergeUnder {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (ρ : ι → κ) (v : ι → ℝ) : κ → ℝ :=
  fun c => ∑ σ ∈ Finset.univ.filter (fun σ => ρ σ = c), v σ

/-- The fiber TV identity: for a sign-pure cell map, the merged weight's
absolute value at a cell is the fiber's total mass `Σ |v σ|`. -/
private lemma abs_merge_eq {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (ρ : ι → κ) (v : ι → ℝ) (c : κ)
    (hpure : ∀ σ σ' : ι, ρ σ = ρ σ' → 0 ≤ v σ * v σ') :
    |mergeUnder ρ v c| = ∑ σ ∈ Finset.univ.filter (fun σ => ρ σ = c), |v σ| := by
  classical
  by_cases hex : ∃ σ ∈ Finset.univ.filter (fun σ => ρ σ = c), 0 < v σ
  · -- the fiber is sign-pure nonnegative: some weight is positive
    obtain ⟨σ₀, hσ₀, hp⟩ := hex
    have heq₀ : ρ σ₀ = c := (Finset.mem_filter.mp hσ₀).2
    have hnn : ∀ τ ∈ Finset.univ.filter (fun σ => ρ σ = c), 0 ≤ v τ := by
      intro τ hτ
      have heqτ : ρ τ = c := (Finset.mem_filter.mp hτ).2
      have hprod : 0 ≤ v σ₀ * v τ := hpure σ₀ τ (by rw [heq₀, heqτ])
      by_cases hle : 0 ≤ v τ
      · exact hle
      · exact absurd (mul_neg_of_pos_of_neg hp (not_le.mp hle)) (not_lt.mpr hprod)
    have hsum : 0 ≤ ∑ τ ∈ Finset.univ.filter (fun σ => ρ σ = c), v τ :=
      Finset.sum_nonneg fun τ hτ => hnn τ hτ
    rw [mergeUnder, abs_of_nonneg hsum]
    exact Finset.sum_congr rfl fun τ hτ => (abs_of_nonneg (hnn τ hτ)).symm
  · -- the fiber is sign-pure nonpositive: every weight is ≤ 0
    have hnp : ∀ τ ∈ Finset.univ.filter (fun σ => ρ σ = c), v τ ≤ 0 := by
      intro τ hτ
      exact not_lt.mp (fun hp => hex ⟨τ, hτ, hp⟩)
    have hsum : ∑ τ ∈ Finset.univ.filter (fun σ => ρ σ = c), v τ ≤ 0 :=
      Finset.sum_nonpos fun τ hτ => hnp τ hτ
    rw [mergeUnder, abs_of_nonpos hsum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun τ hτ => (abs_of_nonpos (hnp τ hτ)).symm

/-- **Lemma W26-PAR** (pairing TV-neutrality, w26-rp §5, general form):
merging the signed sector weights into sign-pure cells conserves total
variation EXACTLY — `TV(merge) = TV(v)`.  The involution pairings of
w26-rp §5 (cell-complex automorphisms, charge conjugation, lattice
isometries, all preserving `|σ|`) are the special case: their orbits are
parity-pure, so nothing cancels. -/
theorem tv_merge_conserved {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (ρ : ι → κ) (v : ι → ℝ)
    (hpure : ∀ σ σ' : ι, ρ σ = ρ σ' → 0 ≤ v σ * v σ') :
    TVv (mergeUnder ρ v) = TVv v := by
  classical
  rw [TVv, Finset.sum_congr rfl fun c _ => abs_merge_eq ρ v c hpure, TVv,
    ← Finset.sum_fiberwise Finset.univ ρ (fun x => |v x|)]

/-! ## Corollary W26-CANCEL: the even/odd split identity -/

/-- **Corollary W26-CANCEL** (i) (w26-rp §4): under the parity-sign
structure `v σ = |v σ|` on the even fibers `{π σ ≡ 0}` and
`v σ = −|v σ|` on the odd fibers `{π σ ≡ 1}` (W25-DICH: `π σ = |σ|`, so
`v σ = (−1)^{|σ|}|v σ|`), the even-part sum `Z_even := Σ_{π σ even} v σ`
satisfies the EXACT identity `2·Z_even = Z⁺ + Z` with `Z⁺ = TVv v` and
`Z = Σ σ, v σ` — the campaign's `Z_even = (Z⁺ + Z)/2`.  (The odd mass
`Z_odd′ := Σ_{π σ odd} |v σ|` obeys `Z⁺ − Z = 2·Z_odd′`, the companion
`Z_odd′ = (Z⁺ − Z)/2`.) -/
theorem z_even_half_abs {ι : Type*} [Fintype ι] (v : ι → ℝ) (π : ι → ℤ)
    (hsign : ∀ σ, v σ = if π σ % 2 = 0 then |v σ| else -|v σ|) :
    2 * ∑ σ ∈ Finset.univ.filter (fun σ => π σ % 2 = 0), v σ
      = TVv v + ∑ σ, v σ := by
  classical
  -- the universe splits into the two parity fibers
  have hsplit : ∀ f : ι → ℝ, ∑ σ ∈ Finset.univ, f σ
      = ∑ σ ∈ Finset.univ.filter (fun σ => π σ % 2 = 0), f σ
        + ∑ σ ∈ Finset.univ.filter (fun σ => π σ % 2 = 1), f σ := by
    intro f
    have hdisj : Disjoint (Finset.univ.filter (fun σ => π σ % 2 = 0))
        (Finset.univ.filter (fun σ => π σ % 2 = 1)) := by
      refine Finset.disjoint_left.mpr fun σ h1 h2 => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rw [h2] at h1
      simp at h1
    have hu : ∑ σ ∈ (Finset.univ.filter (fun σ => π σ % 2 = 0)
        ∪ Finset.univ.filter (fun σ => π σ % 2 = 1)), f σ
        = ∑ σ ∈ Finset.univ.filter (fun σ => π σ % 2 = 0), f σ
          + ∑ σ ∈ Finset.univ.filter (fun σ => π σ % 2 = 1), f σ :=
      Finset.sum_union hdisj
    rw [show (Finset.univ.filter (fun σ => π σ % 2 = 0)
        ∪ Finset.univ.filter (fun σ => π σ % 2 = 1)) = Finset.univ from by
      ext σ
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        iff_true]
      exact Int.emod_two_eq_zero_or_one (π σ)] at hu
    exact hu
  -- on the even fiber the weight IS its absolute value; on the odd
  -- fiber it is minus its absolute value
  have heven : ∀ σ ∈ Finset.univ.filter (fun σ => π σ % 2 = 0), v σ = |v σ| := by
    intro σ hσ
    have h0 : π σ % 2 = 0 := (Finset.mem_filter.mp hσ).2
    exact (hsign σ).trans (by rw [if_pos h0])
  have hodd : ∀ σ ∈ Finset.univ.filter (fun σ => π σ % 2 = 1), v σ = -|v σ| := by
    intro σ hσ
    have h1 : π σ % 2 = 1 := (Finset.mem_filter.mp hσ).2
    have hne : π σ % 2 ≠ 0 := by
      intro hcon
      rw [hcon] at h1
      omega
    exact (hsign σ).trans (by rw [if_neg hne])
  -- (1) the absolute sum is E + O with E the even part, O the odd mass
  have habs : TVv v
      = ∑ σ ∈ Finset.univ.filter (fun σ => π σ % 2 = 0), v σ
        + ∑ σ ∈ Finset.univ.filter (fun σ => π σ % 2 = 1), |v σ| := by
    rw [TVv, hsplit (fun σ => |v σ|)]
    congr 1
    exact Finset.sum_congr rfl fun σ hσ => (heven σ hσ).symm
  -- (2) the signed sum is E − O
  have hsigned : ∑ σ, v σ
      = ∑ σ ∈ Finset.univ.filter (fun σ => π σ % 2 = 0), v σ
        - ∑ σ ∈ Finset.univ.filter (fun σ => π σ % 2 = 1), |v σ| := by
    have h4 : ∑ σ ∈ Finset.univ.filter (fun σ => π σ % 2 = 1), v σ
        = -∑ σ ∈ Finset.univ.filter (fun σ => π σ % 2 = 1), |v σ| := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun σ hσ => hodd σ hσ
    rw [hsplit (fun σ => v σ), h4]
    ring
  rw [habs, hsigned]
  ring

/-- **Corollary W26-CANCEL** (ii) (w26-rp §4): at `Z := Σ w > 0` the
even part carries exactly the cancellation factor of the campaign —
`Z_even = (Z⁺ + |Z|)/2`, i.e. `Z_even/|Z| = (TV + 1)/2` (the banked
anchor 34296.48 = (TV + 1)/2 of w26-rp §4 (ii)). -/
theorem z_even_ratio {ι : Type*} [Fintype ι] (v : ι → ℝ) (π : ι → ℤ)
    (hsign : ∀ σ, v σ = if π σ % 2 = 0 then |v σ| else -|v σ|)
    (hZ : 0 < ∑ σ, v σ) :
    ∑ σ ∈ Finset.univ.filter (fun σ => π σ % 2 = 0), v σ
      = (TVv v + |∑ σ, v σ|) / 2 := by
  have h1 := z_even_half_abs v π hsign
  rw [abs_of_pos hZ]
  field_simp
  linarith

end YangMills3D

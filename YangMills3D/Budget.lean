/-
The wave-37 budget-identity layer: [W37-IDENT], Lean form.

SOURCE. `problems/yang-mills-mass-gap/lemmas/w37-mid.md` §3 (Lemma
W37-IDENT, machine-certified there on 20000 random (bbox, U) pairs plus
the single-removal cost book and the census formula), reusing
`YangMills3D.Animals` (`Cell`, `dirs`, `addDir`, `negDir`, `perimeter`,
`box`).

The campaign's D-book budget: for a box `B`, a removed-cube set
`D ⊆ B` and `U = B ∖ D`, the perimeter excess of `U` over the box
surface is EXACTLY the count of `U`-facing `D`-faces minus the count of
outside-facing `D`-faces — the clean form

  `n − 2·S₂ = f_DU − f_Dout`

with `n = |∂U|`, `S₂ = ab + bc + ca` the SECOND-SHADOW SUM of the box
extents (so `|∂B| = 2·S₂`), `f_DU` = the shared `D`-`U` face count and
`f_Dout` = the `D`-faces leaving `B`.  The equivalent charge form proved
in the campaign is `|∂U| = |∂B| + Σ_{d∈D}(2·nb_in(d) − 6) − 2·f_DD`
(`nb_in` = in-box neighbours, `f_DD` = shared `D`-`D` faces); the
per-cell charge depends only on the bbox position of `d`
(corner/edge/face/interior).  This identity is the correct costing of
the removed set — the W36 compact-book cost bound that omitted the D-D
rebate is false by exactly this term (w37-mid §3).

DELIVERED HERE (all fully proved; no connectivity hypotheses on `U` —
the identity holds for ANY finite `U ⊆ B`):

  * `faceCount` / `faceOut` / `nbIn` — the interface face counts
    (double indicator sums in the `perimeter` style).
  * `faceCount_swap` — the two-sided double-counting bridge: the
    `S`-faces landing in `T` are exactly as many as the `T`-faces
    landing in `S` (the "other endpoint" map `(x, d) ↦ (x + d, −d)` is
    a bijection on face pairs; the wave-37 analogue of the wave-29/31
    counting bridges).
  * `w37_ident` — the clean-form budget identity for arbitrary finite
    `B` and `U ⊆ B`, in subtraction-free ℕ form
    `perimeter U + f_Dout = perimeter B + f_DU`.
  * `face_census` — the face census of the removed set
    `6·|D| = f_DD + f_DU + f_Dout` in the ORDERED D-D count (each
    shared D-D face from both endpoints — exactly the campaign's
    `2·f_DD` display).
  * `w37_ident_charge` — the campaign's charge identity in ℤ.
  * `genBox` / `secondShadow` — the `a×b×c` box and the second-shadow
    sum `S₂ = ab + bc + ca`; `perimeter_genBox` — the exact box surface
    `|∂B| = 2·S₂` (hence `perimeter_box_eq : |∂[1,s]³| = 6s²`, the
    exact value the campaign states and `Animals.perimeter_box_le` only
    bounds), and `w37_ident_genBox` / `w37_ident_genBox_int` — the
    clean identity in the literal `n − 2·S₂ = f_DU − f_Dout` reading.

Every statement below is fully proved: no unfinished proofs, no new
axioms.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import YangMills3D.Animals

namespace YangMills3D

/-! ## The six directions, spelled out -/

/-- The six directions of `dirs`, spelled out (a private copy of the
`Floor.lean` expansion, for use in this module). -/
private theorem dirs_explicit {β : Type*} [AddCommMonoid β] (f : Cell → β) :
    ∑ d ∈ dirs, f d
      = f (-1, 0, 0) + (f (1, 0, 0) + (f (0, -1, 0) + (f (0, 1, 0)
        + (f (0, 0, -1) + f (0, 0, 1))))) := by
  rw [dirs, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]

/-- The double negation of a direction is the direction. -/
theorem negDir_negDir (d : Cell) : negDir (negDir d) = d := by
  obtain ⟨a, b, c⟩ := d
  simp [negDir]

/-- The cardinality of the side interval `[1, n]`. -/
private theorem card_Icc_side (n : ℕ) : (Finset.Icc (1 : ℤ) n).card = n := by
  rw [Int.card_Icc]
  omega

/-- Summing over `dirs` a quantity evaluated at the reflected direction
is the same sum (`negDir` permutes the six directions), indicator form:
the atomic reindexing behind `faceCount_swap`. -/
private theorem dirs_negDir_sum_ite (S : Finset Cell) (y : Cell) :
    ∑ d ∈ dirs, (if addDir y (negDir d) ∈ S then (1:ℕ) else 0)
      = ∑ d ∈ dirs, (if addDir y d ∈ S then 1 else 0) := by
  have hL : ∑ d ∈ dirs, (if addDir y (negDir d) ∈ S then (1:ℕ) else 0)
      = (if addDir y (1, 0, 0) ∈ S then (1:ℕ) else 0)
        + ((if addDir y (-1, 0, 0) ∈ S then 1 else 0)
        + ((if addDir y (0, 1, 0) ∈ S then 1 else 0)
        + ((if addDir y (0, -1, 0) ∈ S then 1 else 0)
        + ((if addDir y (0, 0, 1) ∈ S then 1 else 0)
        + (if addDir y (0, 0, -1) ∈ S then 1 else 0))))) :=
    dirs_explicit (fun d => (if addDir y (negDir d) ∈ S then (1:ℕ) else 0))
  have hR : ∑ d ∈ dirs, (if addDir y d ∈ S then (1:ℕ) else 0)
      = (if addDir y (-1, 0, 0) ∈ S then (1:ℕ) else 0)
        + ((if addDir y (1, 0, 0) ∈ S then 1 else 0)
        + ((if addDir y (0, -1, 0) ∈ S then 1 else 0)
        + ((if addDir y (0, 1, 0) ∈ S then 1 else 0)
        + ((if addDir y (0, 0, -1) ∈ S then 1 else 0)
        + (if addDir y (0, 0, 1) ∈ S then 1 else 0))))) :=
    dirs_explicit (fun d => (if addDir y d ∈ S then (1:ℕ) else 0))
  rw [hL, hR]
  ring

/-! ## Interface face counts -/

/-- The number of faces of the cells of `S` whose outer neighbour lies
in `T` (each shared `S`-`T` face counted once from the `S` side). -/
def faceCount (S T : Finset Cell) : ℕ :=
  ∑ x ∈ S, ∑ d ∈ dirs, (if addDir x d ∈ T then 1 else 0)

/-- The number of faces of the cells of `S` whose outer neighbour lies
OUTSIDE `B` (the faces of `S` exposed relative to `B`). -/
def faceOut (S B : Finset Cell) : ℕ :=
  ∑ x ∈ S, ∑ d ∈ dirs, (if addDir x d ∈ B then 0 else 1)

/-- The number of in-`B` neighbours of a cell (`nb_in` of w37-mid §3;
the per-cell bbox charge is a function of this count alone:
corner/edge/face/interior). -/
def nbIn (B : Finset Cell) (x : Cell) : ℕ :=
  ∑ d ∈ dirs, (if addDir x d ∈ B then 1 else 0)

/-- The perimeter is the self-exposed face count: `perimeter S` is
exactly `faceOut S S`. -/
theorem perimeter_eq_faceOut (S : Finset Cell) : perimeter S = faceOut S S := rfl

/-- The exposed-face partition: every face of `S` either leaves `B` or
lands in `B`. -/
theorem faceOut_add_faceCount (S B : Finset Cell) :
    faceOut S B + faceCount S B = 6 * S.card := by
  classical
  have hpt : ∀ x ∈ S, ∑ d ∈ dirs,
      ((if addDir x d ∈ B then (0:ℕ) else 1) + (if addDir x d ∈ B then 1 else 0))
      = 6 := by
    intro x _
    have hdir : ∀ d ∈ dirs, (if addDir x d ∈ B then (0:ℕ) else 1)
        + (if addDir x d ∈ B then 1 else 0) = 1 := by
      intro d hd
      by_cases h : addDir x d ∈ B <;> simp [h]
    rw [Finset.sum_congr rfl (fun d hd => hdir d hd), dirs_explicit]
    omega
  calc faceOut S B + faceCount S B
      = ∑ x ∈ S, ∑ d ∈ dirs,
          ((if addDir x d ∈ B then (0:ℕ) else 1) + (if addDir x d ∈ B then 1 else 0)) := by
        simp only [faceOut, faceCount, ← Finset.sum_add_distrib]
    _ = ∑ _x ∈ S, 6 := Finset.sum_congr rfl (fun x hx => hpt x hx)
    _ = 6 * S.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- The double-counting bridge: the `S`-faces whose outer neighbour
lies in `T` are exactly as many as the `T`-faces whose outer neighbour
lies in `S` (the map `(x, d) ↦ (x + d, −d)` is a bijection on face
pairs, by `addDir_eq_iff`). -/
theorem faceCount_swap (S T : Finset Cell) : faceCount S T = faceCount T S := by
  classical
  have expand : ∀ x ∈ S, ∑ d ∈ dirs, (if addDir x d ∈ T then (1:ℕ) else 0)
      = ∑ y ∈ T, ∑ d ∈ dirs, (if addDir x d = y then 1 else 0) := by
    intro x _
    have hterm : ∀ d ∈ dirs, (if addDir x d ∈ T then (1:ℕ) else 0)
        = ∑ y ∈ T, (if addDir x d = y then 1 else 0) := by
      intro d _
      by_cases hx : addDir x d ∈ T
      · rw [if_pos hx]
        have hsingle : ∑ y ∈ T, (if addDir x d = y then (1:ℕ) else 0) = 1 := by
          rw [Finset.sum_eq_single (addDir x d)]
          · simp
          · intro b _ hb; exact if_neg (fun he => hb he.symm)
          · intro hn; exact absurd hx hn
        rw [hsingle]
      · rw [if_neg hx]
        refine (Finset.sum_eq_zero fun y hy => ?_).symm
        exact if_neg (fun he => hx (by rw [he]; exact hy))
    rw [Finset.sum_congr rfl (fun d hd => hterm d hd), Finset.sum_comm]
  simp only [faceCount]
  rw [Finset.sum_congr rfl (fun x hx => expand x hx), Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hstep : ∀ d ∈ dirs,
      ∑ x ∈ S, (if addDir x d = y then (1:ℕ) else 0)
        = (if addDir y (negDir d) ∈ S then 1 else 0) := by
    intro d _
    rw [Finset.sum_congr rfl (fun x _ => if_congr (addDir_eq_iff x d y) rfl rfl),
      Finset.sum_ite_eq']
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun d hd => hstep d hd),
    dirs_negDir_sum_ite]

/-! ## The clean-form budget identity (W37-IDENT, arbitrary finite sets) -/

/-- Pointwise trichotomy: for `x ∈ U ⊆ B` and any direction, the
`U`-exposure indicator splits into the `B`-exposure indicator plus the
interface indicator toward `B ∖ U`. -/
private theorem ite_split_U (B U : Finset Cell) (hU : U ⊆ B) (x d : Cell) :
    (if addDir x d ∈ U then (0:ℕ) else 1)
      = (if addDir x d ∈ B then 0 else 1)
        + (if addDir x d ∈ B \ U then 1 else 0) := by
  by_cases h1 : addDir x d ∈ U
  · have h2 : addDir x d ∈ B := hU h1
    have h3 : ¬ (addDir x d ∈ B \ U) := fun hh => (Finset.mem_sdiff.mp hh).2 h1
    simp [h1, h2, h3]
  · by_cases h2 : addDir x d ∈ B
    · have h3 : addDir x d ∈ B \ U := Finset.mem_sdiff.mpr ⟨h2, h1⟩
      simp [h1, h2, h3]
    · simp [h1, h2]

/-- **Lemma W37-IDENT, clean form** (w37-mid §3), subtraction-free ℕ
form, for ARBITRARY finite `B` and `U ⊆ B` (no connectivity, no box
structure needed): `perimeter U + f_Dout = perimeter B + f_DU` — the
perimeter excess `|∂U| − |∂B|` equals the count of `U`-facing `D`-faces
minus the count of `D`-faces leaving `B`, where `D = B ∖ U`. -/
theorem w37_ident (B U : Finset Cell) (hU : U ⊆ B) :
    perimeter U + faceOut (B \ U) B = perimeter B + faceCount (B \ U) U := by
  classical
  have hd : Disjoint U (B \ U) := Finset.disjoint_left.mpr
    (fun a ha hb => (Finset.mem_sdiff.mp hb).2 ha)
  have hunion : U ∪ (B \ U) = B := by
    ext x
    by_cases hx : x ∈ U
    · simp [hx, hU hx]
    · by_cases hxb : x ∈ B
      · simp [hx, hxb]
      · simp [hx, hxb]
  have hsplitB : perimeter B
      = (∑ x ∈ U, ∑ d ∈ dirs, (if addDir x d ∈ B then (0:ℕ) else 1))
        + faceOut (B \ U) B := by
    rw [perimeter]
    have h2 : ∑ x ∈ U ∪ (B \ U), ∑ d ∈ dirs, (if addDir x d ∈ B then (0:ℕ) else 1)
        = (∑ x ∈ U, ∑ d ∈ dirs, (if addDir x d ∈ B then 0 else 1))
          + ∑ x ∈ B \ U, ∑ d ∈ dirs, (if addDir x d ∈ B then 0 else 1) :=
      Finset.sum_union hd
    rw [hunion] at h2
    exact h2
  have hu : ∀ x ∈ U, ∑ d ∈ dirs, (if addDir x d ∈ U then (0:ℕ) else 1)
      = (∑ d ∈ dirs, (if addDir x d ∈ B then 0 else 1))
        + ∑ d ∈ dirs, (if addDir x d ∈ B \ U then 1 else 0) := by
    intro x hx
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ => ite_split_U B U hU x d
  have hpU : perimeter U
      = (∑ x ∈ U, ∑ d ∈ dirs, (if addDir x d ∈ B then (0:ℕ) else 1))
        + faceCount U (B \ U) := by
    rw [perimeter, Finset.sum_congr rfl (fun x hx => hu x hx), Finset.sum_add_distrib]
    rfl
  rw [hpU, hsplitB, faceCount_swap U (B \ U)]
  omega

/-! ## The face census and the charge identity -/

/-- **The face census of the removed set** (w37-mid §3's proof step
`6·|D| = 2·f_DD + f_DU + f_Dout`): with `D = B ∖ U` and the ORDERED D-D
count `faceCount D D` (each shared D-D face from both endpoints — the
campaign's `2·f_DD`), every face of `D` either meets `U`, meets `D`, or
leaves `B`. -/
theorem face_census (B U : Finset Cell) (hU : U ⊆ B) :
    6 * (B \ U).card
      = faceCount (B \ U) (B \ U) + faceCount (B \ U) U + faceOut (B \ U) B := by
  classical
  have hpt : ∀ x ∈ B \ U, ∑ d ∈ dirs,
      ((if addDir x d ∈ B \ U then (1:ℕ) else 0)
        + (if addDir x d ∈ U then 1 else 0)
        + (if addDir x d ∈ B then 0 else 1)) = 6 := by
    intro x hx
    obtain ⟨_hxB, _hxU⟩ := Finset.mem_sdiff.mp hx
    have hdir : ∀ d ∈ dirs,
        ((if addDir x d ∈ B \ U then (1:ℕ) else 0)
          + (if addDir x d ∈ U then 1 else 0)
          + (if addDir x d ∈ B then 0 else 1)) = 1 := by
      intro d hd
      by_cases h1 : addDir x d ∈ U
      · have h2 : addDir x d ∈ B := hU h1
        have h3 : ¬ (addDir x d ∈ B \ U) := fun hh => (Finset.mem_sdiff.mp hh).2 h1
        simp [h1, h2, h3]
      · by_cases h2 : addDir x d ∈ B
        · have h4 : addDir x d ∈ B \ U := Finset.mem_sdiff.mpr ⟨h2, h1⟩
          simp [h1, h2, h4]
        · simp [h1, h2]
    rw [Finset.sum_congr rfl (fun d hd => hdir d hd), dirs_explicit]
    omega
  have hsplit : ∑ x ∈ B \ U, ∑ d ∈ dirs,
      ((if addDir x d ∈ B \ U then (1:ℕ) else 0)
        + (if addDir x d ∈ U then 1 else 0)
        + (if addDir x d ∈ B then 0 else 1))
      = faceCount (B \ U) (B \ U) + faceCount (B \ U) U + faceOut (B \ U) B := by
    simp only [Finset.sum_add_distrib]
    rfl
  calc 6 * (B \ U).card = ∑ _x ∈ B \ U, (6:ℕ) := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ = ∑ x ∈ B \ U, ∑ d ∈ dirs,
          ((if addDir x d ∈ B \ U then (1:ℕ) else 0)
            + (if addDir x d ∈ U then 1 else 0)
            + (if addDir x d ∈ B then 0 else 1)) :=
        Finset.sum_congr rfl (fun x hx => (hpt x hx).symm)
    _ = faceCount (B \ U) (B \ U) + faceCount (B \ U) U + faceOut (B \ U) B := hsplit

/-- The in-`B` neighbourhood count of the removed set splits into the
`U`-facing and `D`-facing parts (w37-mid §3's
`Σ nb_in = f_DU + 2·f_DD`, in the ordered count). -/
theorem sum_nbIn (B U : Finset Cell) (hU : U ⊆ B) :
    ∑ x ∈ B \ U, nbIn B x = faceCount (B \ U) U + faceCount (B \ U) (B \ U) := by
  classical
  have hpt : ∀ x ∈ B \ U, nbIn B x
      = (∑ d ∈ dirs, (if addDir x d ∈ U then (1:ℕ) else 0))
        + ∑ d ∈ dirs, (if addDir x d ∈ B \ U then 1 else 0) := by
    intro x hx
    obtain ⟨hxB, _hxU⟩ := Finset.mem_sdiff.mp hx
    rw [nbIn, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases h1 : addDir x d ∈ U
    · have h2 : addDir x d ∈ B := hU h1
      have h3 : ¬ (addDir x d ∈ B \ U) := fun hh => (Finset.mem_sdiff.mp hh).2 h1
      simp [h1, h2, h3]
    · by_cases h2 : addDir x d ∈ B
      · have h4 : addDir x d ∈ B \ U := Finset.mem_sdiff.mpr ⟨h2, h1⟩
        simp [h1, h2, h4]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun x hx => hpt x hx), Finset.sum_add_distrib]
  rfl

/-- **Lemma W37-IDENT, charge form** (w37-mid §3's
`|∂U| = |∂B| + Σ_{d∈D}(2·nb_in(d) − 6) − 2·f_DD`), for arbitrary finite
`B` and `U ⊆ B`, in ℤ currency with the ORDERED D-D count (the
campaign's `2·f_DD` is exactly `faceCount D D`).  The proof combines
the clean form with the census:
`Σ(2·nb_in − 6) − f_DD^{ord} = f_DU − f_Dout`. -/
theorem w37_ident_charge (B U : Finset Cell) (hU : U ⊆ B) :
    (perimeter U : ℤ) = (perimeter B : ℤ)
      + ∑ x ∈ B \ U, (2 * ((nbIn B x : ℕ) : ℤ) - 6)
      - ((faceCount (B \ U) (B \ U) : ℕ) : ℤ) := by
  classical
  have e1 := w37_ident B U hU
  have e2 := face_census B U hU
  have e3 := sum_nbIn B U hU
  have h2s : ∑ x ∈ B \ U, (2 * ((nbIn B x : ℕ) : ℤ))
      = 2 * (((∑ x ∈ B \ U, nbIn B x : ℕ) : ℤ)) := by
    have h1 : ∑ x ∈ B \ U, (2 * ((nbIn B x : ℕ) : ℤ))
        = (∑ x ∈ B \ U, ((nbIn B x : ℕ) : ℤ)) * 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [h1, Nat.cast_sum]
    ring
  have h6 : ∑ _x ∈ B \ U, (6:ℤ) = 6 * (((B \ U).card : ℕ) : ℤ) := by
    rw [Finset.sum_const]
    ring
  have e4 : ∑ x ∈ B \ U, (2 * ((nbIn B x : ℕ) : ℤ) - 6)
      = 2 * (((∑ x ∈ B \ U, nbIn B x : ℕ) : ℤ)) - 6 * (((B \ U).card : ℕ) : ℤ) := by
    rw [Finset.sum_sub_distrib, h2s, h6]
  rw [e4]
  omega

/-! ## Boxes and the second-shadow sum -/

/-- A general `a × b × c` box: the product of the coordinate intervals
`[1, a]`, `[1, b]`, `[1, c]` (the campaign's bbox; `Animals.box` is the
cube case `genBox s s s`). -/
def genBox (a b c : ℕ) : Finset Cell :=
  Finset.Icc (1 : ℤ) a ×ˢ (Finset.Icc (1 : ℤ) b ×ˢ Finset.Icc (1 : ℤ) c)

/-- The SECOND-SHADOW SUM `S₂ = ab + bc + ca` of an `a×b×c` box
(w37-mid §3 / the `bbox_census` of w37_lib: the sum of the three
pairwise products of the box extents; twice it is the box surface
`|∂B|`). -/
def secondShadow (a b c : ℕ) : ℕ := a * b + b * c + c * a

theorem mem_genBox_iff {a b c : ℕ} {x : Cell} :
    x ∈ genBox a b c ↔ 1 ≤ x.1 ∧ x.1 ≤ (a : ℤ) ∧ 1 ≤ x.2.1 ∧ x.2.1 ≤ (b : ℤ)
      ∧ 1 ≤ x.2.2 ∧ x.2.2 ≤ (c : ℤ) := by
  simp only [genBox, Finset.mem_product, Finset.mem_Icc]
  tauto

theorem card_genBox (a b c : ℕ) : (genBox a b c).card = a * b * c := by
  have hc : (Finset.Icc (1 : ℤ) c).card = c := by rw [Int.card_Icc]; omega
  have hb : (Finset.Icc (1 : ℤ) b).card = b := by rw [Int.card_Icc]; omega
  have ha : (Finset.Icc (1 : ℤ) a).card = a := by rw [Int.card_Icc]; omega
  rw [genBox, Finset.card_product, Finset.card_product, ha, hb, hc]
  ring

/-- Directional indicator sums over the box: the `x.1`-fiber of level
`j` has size `b·c` when `j ∈ [1, a]` (and is empty otherwise). -/
private lemma genBox_sum_ite_x1 (a b c : ℕ) (j : ℤ) :
    ∑ x ∈ genBox a b c, (if x.1 = j then (1:ℕ) else 0)
      = b * c * (if j ∈ Finset.Icc (1:ℤ) a then 1 else 0) := by
  rw [genBox]
  simp only [Finset.sum_product]
  have hrc : ∀ t : ℤ, ∑ r ∈ Finset.Icc (1:ℤ) c, (if t = j then (1:ℕ) else 0)
      = c * (if t = j then 1 else 0) := by
    intro t; rw [Finset.sum_const, smul_eq_mul, card_Icc_side]
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun _q _ => hrc p))]
  have hqb : ∀ t : ℤ, ∑ q ∈ Finset.Icc (1:ℤ) b, c * (if t = j then (1:ℕ) else 0)
      = b * (c * (if t = j then 1 else 0)) := by
    intro t; rw [Finset.sum_const, smul_eq_mul, card_Icc_side]
  rw [Finset.sum_congr rfl (fun p _ => hqb p)]
  have harr : ∀ p : ℤ, b * (c * (if p = j then (1:ℕ) else 0))
      = (if p = j then 1 else 0) * (b * c) := by
    intro p; by_cases hp : p = j <;> simp [hp]
  rw [Finset.sum_congr rfl (fun p _ => harr p), ← Finset.sum_mul, Finset.sum_ite_eq']
  by_cases hj : j ∈ Finset.Icc (1:ℤ) a
  · rw [if_pos hj, Nat.one_mul, Nat.mul_one]
  · rw [if_neg hj, Nat.zero_mul, Nat.mul_zero]

/-- Directional indicator sums over the box: the `x.2.1`-fiber. -/
private lemma genBox_sum_ite_x2 (a b c : ℕ) (j : ℤ) :
    ∑ x ∈ genBox a b c, (if x.2.1 = j then (1:ℕ) else 0)
      = a * c * (if j ∈ Finset.Icc (1:ℤ) b then 1 else 0) := by
  rw [genBox]
  simp only [Finset.sum_product]
  have hrc : ∀ q : ℤ, ∑ r ∈ Finset.Icc (1:ℤ) c, (if q = j then (1:ℕ) else 0)
      = c * (if q = j then 1 else 0) := by
    intro q; rw [Finset.sum_const, smul_eq_mul, card_Icc_side]
  rw [Finset.sum_congr rfl (fun _p _ => Finset.sum_congr rfl (fun q _ => hrc q))]
  have hqb : ∑ q ∈ Finset.Icc (1:ℤ) b, c * (if q = j then (1:ℕ) else 0)
      = c * (if j ∈ Finset.Icc (1:ℤ) b then 1 else 0) := by
    rw [← Finset.mul_sum, Finset.sum_ite_eq']
  rw [Finset.sum_congr rfl (fun p _ => hqb)]
  rw [Finset.sum_const, smul_eq_mul, card_Icc_side]
  ring

/-- Directional indicator sums over the box: the `x.2.2`-fiber. -/
private lemma genBox_sum_ite_x3 (a b c : ℕ) (j : ℤ) :
    ∑ x ∈ genBox a b c, (if x.2.2 = j then (1:ℕ) else 0)
      = a * b * (if j ∈ Finset.Icc (1:ℤ) c then 1 else 0) := by
  rw [genBox]
  simp only [Finset.sum_product]
  have hin : ∀ p q : ℤ, ∑ r ∈ Finset.Icc (1:ℤ) c, (if r = j then (1:ℕ) else 0)
      = if j ∈ Finset.Icc (1:ℤ) c then 1 else 0 := by
    intro p q; rw [Finset.sum_ite_eq']
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hin p q))]
  rw [Finset.sum_const, smul_eq_mul, card_Icc_side]
  rw [Finset.sum_const, smul_eq_mul, card_Icc_side]
  ring

/-! ## The exact box surface: `|∂B| = 2·S₂` -/

/-- Component projections of a step in direction `(-1, 0, 0)`. -/
private lemma addDir_negx (x : Cell) : addDir x (-1, 0, 0) = (x.1 + -1, x.2.1, x.2.2) := by
  simp [addDir]

/-- Component projections of a step in direction `(1, 0, 0)`. -/
private lemma addDir_posx (x : Cell) : addDir x (1, 0, 0) = (x.1 + 1, x.2.1, x.2.2) := by
  simp [addDir]

/-- Component projections of a step in direction `(0, -1, 0)`. -/
private lemma addDir_negy (x : Cell) : addDir x (0, -1, 0) = (x.1, x.2.1 + -1, x.2.2) := by
  simp [addDir]

/-- Component projections of a step in direction `(0, 1, 0)`. -/
private lemma addDir_posy (x : Cell) : addDir x (0, 1, 0) = (x.1, x.2.1 + 1, x.2.2) := by
  simp [addDir]

/-- Component projections of a step in direction `(0, 0, -1)`. -/
private lemma addDir_negz (x : Cell) : addDir x (0, 0, -1) = (x.1, x.2.1, x.2.2 + -1) := by
  simp [addDir]

/-- Component projections of a step in direction `(0, 0, 1)`. -/
private lemma addDir_posz (x : Cell) : addDir x (0, 0, 1) = (x.1, x.2.1, x.2.2 + 1) := by
  simp [addDir]

/-- The `-x`-exposed faces of a box: exactly the `x.1 = 1` cells,
`b·c` of them. -/
private lemma genBox_out_negx (a b c : ℕ) (ha : 1 ≤ a) :
    ∑ x ∈ genBox a b c, (if addDir x (-1, 0, 0) ∈ genBox a b c then (0:ℕ) else 1)
      = b * c := by
  have hpt : ∀ x ∈ genBox a b c,
      (if addDir x (-1, 0, 0) ∈ genBox a b c then (0:ℕ) else 1)
        = (if x.1 = 1 then (1:ℕ) else 0) := by
    intro x hx
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mem_genBox_iff.mp hx
    by_cases hx1 : x.1 = 1
    · have hout : ¬ (addDir x (-1, 0, 0) ∈ genBox a b c) := by
        intro hmem
        obtain ⟨k1, _k2, _k3, _k4, _k5, _k6⟩ := mem_genBox_iff.mp hmem
        simp only [addDir_negx] at k1
        omega
      rw [if_neg hout, if_pos hx1]
    · have hin : addDir x (-1, 0, 0) ∈ genBox a b c := by
        rw [mem_genBox_iff]
        simp only [addDir_negx]
        refine ⟨?_, ?_, h3, h4, h5, h6⟩ <;> omega
      rw [if_pos hin, if_neg hx1]
  rw [Finset.sum_congr rfl (fun x hx => hpt x hx), genBox_sum_ite_x1,
    if_pos (Finset.mem_Icc.mpr ⟨le_refl (1 : ℤ), by exact_mod_cast ha⟩), Nat.mul_one]

/-- The `+x`-exposed faces of a box: exactly the `x.1 = a` cells. -/
private lemma genBox_out_posx (a b c : ℕ) (ha : 1 ≤ a) :
    ∑ x ∈ genBox a b c, (if addDir x (1, 0, 0) ∈ genBox a b c then (0:ℕ) else 1)
      = b * c := by
  have hpt : ∀ x ∈ genBox a b c,
      (if addDir x (1, 0, 0) ∈ genBox a b c then (0:ℕ) else 1)
        = (if x.1 = (a : ℤ) then (1:ℕ) else 0) := by
    intro x hx
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mem_genBox_iff.mp hx
    by_cases hx1 : x.1 = a
    · have hout : ¬ (addDir x (1, 0, 0) ∈ genBox a b c) := by
        intro hmem
        obtain ⟨_k1, k2, _k3, _k4, _k5, _k6⟩ := mem_genBox_iff.mp hmem
        simp only [addDir_posx] at k2
        omega
      rw [if_neg hout, if_pos hx1]
    · have hin : addDir x (1, 0, 0) ∈ genBox a b c := by
        rw [mem_genBox_iff]
        simp only [addDir_posx]
        refine ⟨?_, ?_, h3, h4, h5, h6⟩ <;> omega
      rw [if_pos hin, if_neg hx1]
  rw [Finset.sum_congr rfl (fun x hx => hpt x hx), genBox_sum_ite_x1,
    if_pos (Finset.mem_Icc.mpr ⟨by omega, le_refl (a : ℤ)⟩), Nat.mul_one]

/-- The `-y`-exposed faces of a box: exactly the `x.2.1 = 1` cells. -/
private lemma genBox_out_negy (a b c : ℕ) (hb : 1 ≤ b) :
    ∑ x ∈ genBox a b c, (if addDir x (0, -1, 0) ∈ genBox a b c then (0:ℕ) else 1)
      = a * c := by
  have hpt : ∀ x ∈ genBox a b c,
      (if addDir x (0, -1, 0) ∈ genBox a b c then (0:ℕ) else 1)
        = (if x.2.1 = 1 then (1:ℕ) else 0) := by
    intro x hx
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mem_genBox_iff.mp hx
    by_cases hx1 : x.2.1 = 1
    · have hout : ¬ (addDir x (0, -1, 0) ∈ genBox a b c) := by
        intro hmem
        obtain ⟨_k1, _k2, k3, _k4, _k5, _k6⟩ := mem_genBox_iff.mp hmem
        simp only [addDir_negy] at k3
        omega
      rw [if_neg hout, if_pos hx1]
    · have hin : addDir x (0, -1, 0) ∈ genBox a b c := by
        rw [mem_genBox_iff]
        simp only [addDir_negy]
        refine ⟨h1, h2, ?_, ?_, h5, h6⟩ <;> omega
      rw [if_pos hin, if_neg hx1]
  rw [Finset.sum_congr rfl (fun x hx => hpt x hx), genBox_sum_ite_x2,
    if_pos (Finset.mem_Icc.mpr ⟨le_refl (1 : ℤ), by exact_mod_cast hb⟩), Nat.mul_one]

/-- The `+y`-exposed faces of a box: exactly the `x.2.1 = b` cells. -/
private lemma genBox_out_posy (a b c : ℕ) (hb : 1 ≤ b) :
    ∑ x ∈ genBox a b c, (if addDir x (0, 1, 0) ∈ genBox a b c then (0:ℕ) else 1)
      = a * c := by
  have hpt : ∀ x ∈ genBox a b c,
      (if addDir x (0, 1, 0) ∈ genBox a b c then (0:ℕ) else 1)
        = (if x.2.1 = (b : ℤ) then (1:ℕ) else 0) := by
    intro x hx
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mem_genBox_iff.mp hx
    by_cases hx1 : x.2.1 = b
    · have hout : ¬ (addDir x (0, 1, 0) ∈ genBox a b c) := by
        intro hmem
        obtain ⟨_k1, _k2, _k3, k4, _k5, _k6⟩ := mem_genBox_iff.mp hmem
        simp only [addDir_posy] at k4
        omega
      rw [if_neg hout, if_pos hx1]
    · have hin : addDir x (0, 1, 0) ∈ genBox a b c := by
        rw [mem_genBox_iff]
        simp only [addDir_posy]
        refine ⟨h1, h2, ?_, ?_, h5, h6⟩ <;> omega
      rw [if_pos hin, if_neg hx1]
  rw [Finset.sum_congr rfl (fun x hx => hpt x hx), genBox_sum_ite_x2,
    if_pos (Finset.mem_Icc.mpr ⟨by omega, le_refl (b : ℤ)⟩), Nat.mul_one]

/-- The `-z`-exposed faces of a box: exactly the `x.2.2 = 1` cells. -/
private lemma genBox_out_negz (a b c : ℕ) (hc : 1 ≤ c) :
    ∑ x ∈ genBox a b c, (if addDir x (0, 0, -1) ∈ genBox a b c then (0:ℕ) else 1)
      = a * b := by
  have hpt : ∀ x ∈ genBox a b c,
      (if addDir x (0, 0, -1) ∈ genBox a b c then (0:ℕ) else 1)
        = (if x.2.2 = 1 then (1:ℕ) else 0) := by
    intro x hx
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mem_genBox_iff.mp hx
    by_cases hx1 : x.2.2 = 1
    · have hout : ¬ (addDir x (0, 0, -1) ∈ genBox a b c) := by
        intro hmem
        obtain ⟨_k1, _k2, _k3, _k4, k5, _k6⟩ := mem_genBox_iff.mp hmem
        simp only [addDir_negz] at k5
        omega
      rw [if_neg hout, if_pos hx1]
    · have hin : addDir x (0, 0, -1) ∈ genBox a b c := by
        rw [mem_genBox_iff]
        simp only [addDir_negz]
        refine ⟨h1, h2, h3, h4, ?_, ?_⟩ <;> omega
      rw [if_pos hin, if_neg hx1]
  rw [Finset.sum_congr rfl (fun x hx => hpt x hx), genBox_sum_ite_x3,
    if_pos (Finset.mem_Icc.mpr ⟨le_refl (1 : ℤ), by exact_mod_cast hc⟩), Nat.mul_one]

/-- The `+z`-exposed faces of a box: exactly the `x.2.2 = c` cells. -/
private lemma genBox_out_posz (a b c : ℕ) (hc : 1 ≤ c) :
    ∑ x ∈ genBox a b c, (if addDir x (0, 0, 1) ∈ genBox a b c then (0:ℕ) else 1)
      = a * b := by
  have hpt : ∀ x ∈ genBox a b c,
      (if addDir x (0, 0, 1) ∈ genBox a b c then (0:ℕ) else 1)
        = (if x.2.2 = (c : ℤ) then (1:ℕ) else 0) := by
    intro x hx
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mem_genBox_iff.mp hx
    by_cases hx1 : x.2.2 = c
    · have hout : ¬ (addDir x (0, 0, 1) ∈ genBox a b c) := by
        intro hmem
        obtain ⟨_k1, _k2, _k3, _k4, _k5, k6⟩ := mem_genBox_iff.mp hmem
        simp only [addDir_posz] at k6
        omega
      rw [if_neg hout, if_pos hx1]
    · have hin : addDir x (0, 0, 1) ∈ genBox a b c := by
        rw [mem_genBox_iff]
        simp only [addDir_posz]
        refine ⟨h1, h2, h3, h4, ?_, ?_⟩ <;> omega
      rw [if_pos hin, if_neg hx1]
  rw [Finset.sum_congr rfl (fun x hx => hpt x hx), genBox_sum_ite_x3,
    if_pos (Finset.mem_Icc.mpr ⟨by omega, le_refl (c : ℤ)⟩), Nat.mul_one]

/-- **The exact box surface** (w37-mid §3, the `|∂B| = 2·S₂` reading):
the exposed-face count of the `a×b×c` box is exactly twice the
second-shadow sum `S₂ = ab + bc + ca`. -/
theorem perimeter_genBox (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    perimeter (genBox a b c) = 2 * secondShadow a b c := by
  rw [perimeter, Finset.sum_comm, dirs_explicit]
  rw [genBox_out_negx a b c ha, genBox_out_posx a b c ha,
    genBox_out_negy a b c hb, genBox_out_posy a b c hb,
    genBox_out_negz a b c hc, genBox_out_posz a b c hc]
  simp only [secondShadow]
  ring

/-- **The exact cube-box perimeter** (the campaign's
`|∂[1,s]³| = 6·s²`, stated in `w24-cold`/`w25-cluster` and used
throughout; `Animals.perimeter_box_le` only bounds it). -/
theorem perimeter_box_eq (s : ℕ) (hs : 1 ≤ s) : perimeter (box s) = 6 * s * s := by
  have h : perimeter (genBox s s s) = 2 * secondShadow s s s :=
    perimeter_genBox s s s hs hs hs
  rw [show genBox s s s = box s from rfl, secondShadow] at h
  rw [h]
  ring

/-! ## The boxed clean identity: `n − 2·S₂ = f_DU − f_Dout` -/

/-- **Lemma W37-IDENT** (w37-mid §3, clean form over a box), ℕ form: for
`D ⊆ B` the removed set of the `a×b×c` box `B` and `U = B ∖ D`,
`perimeter U + f_Dout = 2·S₂ + f_DU` — the subtraction-free reading of
the campaign's budget identity `n − 2·S₂ = f_DU − f_Dout`. -/
theorem w37_ident_genBox (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (D : Finset Cell) (hD : D ⊆ genBox a b c) :
    perimeter (genBox a b c \ D) + faceOut D (genBox a b c)
      = 2 * secondShadow a b c + faceCount D (genBox a b c \ D) := by
  have hBD : genBox a b c \ (genBox a b c \ D) = D := by
    ext x
    by_cases hxD : x ∈ D
    · simp [hxD, hD hxD]
    · by_cases hxg : x ∈ genBox a b c
      · simp [hxD, hxg]
      · simp [hxD, hxg]
  have h := w37_ident (genBox a b c) (genBox a b c \ D) (fun x hx => (Finset.mem_sdiff.mp hx).1)
  rw [perimeter_genBox a b c ha hb hc, hBD] at h
  exact h

/-- **Lemma W37-IDENT** (w37-mid §3, clean form over a box), the
LITERAL `n − 2·S₂ = f_DU − f_Dout` reading in ℤ currency: with
`n = |∂U|` the perimeter of `U = B ∖ D`, `S₂ = ab + bc + ca` the
second-shadow sum, `f_DU` the `U`-facing `D`-faces and `f_Dout` the
`D`-faces leaving `B`. -/
theorem w37_ident_genBox_int (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (D : Finset Cell) (hD : D ⊆ genBox a b c) :
    (perimeter (genBox a b c \ D) : ℤ) - 2 * (secondShadow a b c : ℤ)
      = (faceCount D (genBox a b c \ D) : ℤ) - (faceOut D (genBox a b c) : ℤ) := by
  have h := w37_ident_genBox a b c ha hb hc D hD
  omega

end YangMills3D

/-
The wave-39/42 layer-identity layer: [W39-ID] (the coarea identity
`|∂U| = H + V` per axis) and [G28-ID] (the min-axis identity
`Σ_a V_a = 2·|∂U|`), Lean form.

SOURCE. `problems/yang-mills-mass-gap/lemmas/w39-dense.md` §1 (Lemma
[W39-ID]: the layered decomposition of the perimeter along ANY axis,
machine-certified there on 10196/10196 connected solids — Gate-27
exhaustively re-confirmed, including the G27-1 erratum's own checks),
and `lemmas/w42-adjudicate.md` §1 ([G28-ID]: the axis-triple identity
`Σ_a V_a = 2·|∂U|` — each face has a normal `±e_a` for exactly one `a`
and is a "wall" for exactly the other two axes, so it is counted in
exactly two of the three `V_a`; Gate-29 exhaustively re-confirmed the
identity and the min-axis consequence on 27,622 classes after
retracting the W42-LAYER book constant), reusing
`YangMills3D.Animals` (`Cell`, `dirs`, `addDir`, `perimeter`) —
a SIBLING IDENTITY to `YangMills3D.Budget`'s `w37_ident`: there the
perimeter excess is carried by the removed-set D-book
(`faceCount`/`faceOut` interface counts); here it is carried by the
axis-layering book (the slice `P2`-sums and the cap-face counts).

THE CAMPAIGN'S STATEMENTS, Lean form (U any finite cell set — no
connectivity is needed; the identities hold for ANY finite `U`, which
makes them STRONGER than the campaign's solid statements):

  * Per axis `a ∈ {x, y, z}`: the slice family `S_j = {cells at
    coordinate level `j` along the axis}`, the wall-face count
    `V = Σ_j P2(S_j)` (the exposed faces with normal ⊥ the axis; for
    the no-gap columns the `P2`-sum is the height-TV `Σ|Δh|`) and the
    cap-face count `H` (the exposed faces with normal ∥ the axis).
  * [W39-ID] `|∂U| = H + V` per axis (`coareaX/Y/Z`), with the
    slice-sum form `V = Σ_j P2(S_j)` exact
    (`wallX_eq_sliceP2_sum` etc.) and the cap budget
    `H + 2·Σ_z|S_z ∩ S_{z+1}| = 2·|U|` — the campaign's
    `H = 2v − 2Σ_z|S_z ∩ S_{z+1}|` in subtraction-free ℕ form, with
    `Σ_z|S_z ∩ S_{z+1}|` read as the ORDERED double count
    `capInternal` (each vertical adjacency counted from both ends;
    `capX_add_capInternalX` etc.).
  * [G28-ID] `V_x + V_y + V_z = 2·|∂U|`
    (`sum_wall_eq_twice_perimeter`) and the min-axis corollary
    `min_a V_a ≤ 2·|∂U|/3` (`wall_min_axis` — the exact input the
    min-axis layered book [W42-LAYER] consumes; per the Gate-29
    retraction the BOOK did not bank, the identity did).  The mirror
    identities `H_x + H_y + H_z = |∂U|` (`sum_cap_eq_perimeter`) and
    `min_a H_a ≤ |∂U|/3` (`cap_min_axis`) complete the face census:
    every exposed face is counted ONCE in the cap book (its own axis)
    and TWICE in the wall book (the other two axes).

Every statement below is fully proved: no unfinished proofs, no new
axioms.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import YangMills3D.Animals

namespace YangMills3D

/-! ## The per-axis direction families -/

/-- The four in-plane ("wall") directions of the x-axis layering: the
exposed faces with these normals are the `V_x` walls. -/
def dirsWallX : Finset Cell := ({(0, -1, 0), (0, 1, 0), (0, 0, -1), (0, 0, 1)} : Finset Cell)

/-- The four in-plane ("wall") directions of the y-axis layering. -/
def dirsWallY : Finset Cell := ({(-1, 0, 0), (1, 0, 0), (0, 0, -1), (0, 0, 1)} : Finset Cell)

/-- The four in-plane ("wall") directions of the z-axis layering. -/
def dirsWallZ : Finset Cell := ({(-1, 0, 0), (1, 0, 0), (0, -1, 0), (0, 1, 0)} : Finset Cell)

/-- The two axis ("cap") directions `±e_x`: the exposed faces with
these normals are the `H_x` caps. -/
def dirsCapX : Finset Cell := ({(-1, 0, 0), (1, 0, 0)} : Finset Cell)

/-- The two axis ("cap") directions `±e_y`. -/
def dirsCapY : Finset Cell := ({(0, -1, 0), (0, 1, 0)} : Finset Cell)

/-- The two axis ("cap") directions `±e_z`. -/
def dirsCapZ : Finset Cell := ({(0, 0, -1), (0, 0, 1)} : Finset Cell)

/-- The six directions, spelled out (a private copy of the
`Budget.lean` expansion, for use in this module). -/
private theorem dirs_six {β : Type*} [AddCommMonoid β] (f : Cell → β) :
    ∑ d ∈ dirs, f d
      = f (-1, 0, 0) + (f (1, 0, 0) + (f (0, -1, 0) + (f (0, 1, 0)
        + (f (0, 0, -1) + f (0, 0, 1))))) := by
  rw [dirs, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]

/-- The x-wall quadruple, spelled out. -/
private theorem sum_dirsWallX {β : Type*} [AddCommMonoid β] (f : Cell → β) :
    ∑ d ∈ dirsWallX, f d
      = f (0, -1, 0) + (f (0, 1, 0) + (f (0, 0, -1) + f (0, 0, 1))) := by
  rw [dirsWallX, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]

/-- The y-wall quadruple, spelled out. -/
private theorem sum_dirsWallY {β : Type*} [AddCommMonoid β] (f : Cell → β) :
    ∑ d ∈ dirsWallY, f d
      = f (-1, 0, 0) + (f (1, 0, 0) + (f (0, 0, -1) + f (0, 0, 1))) := by
  rw [dirsWallY, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]

/-- The z-wall quadruple, spelled out. -/
private theorem sum_dirsWallZ {β : Type*} [AddCommMonoid β] (f : Cell → β) :
    ∑ d ∈ dirsWallZ, f d
      = f (-1, 0, 0) + (f (1, 0, 0) + (f (0, -1, 0) + f (0, 1, 0))) := by
  rw [dirsWallZ, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]

/-- The x-cap pair, spelled out. -/
private theorem sum_dirsCapX {β : Type*} [AddCommMonoid β] (f : Cell → β) :
    ∑ d ∈ dirsCapX, f d = f (-1, 0, 0) + f (1, 0, 0) := by
  rw [dirsCapX, Finset.sum_insert (by decide), Finset.sum_singleton]

/-- The y-cap pair, spelled out. -/
private theorem sum_dirsCapY {β : Type*} [AddCommMonoid β] (f : Cell → β) :
    ∑ d ∈ dirsCapY, f d = f (0, -1, 0) + f (0, 1, 0) := by
  rw [dirsCapY, Finset.sum_insert (by decide), Finset.sum_singleton]

/-- The z-cap pair, spelled out. -/
private theorem sum_dirsCapZ {β : Type*} [AddCommMonoid β] (f : Cell → β) :
    ∑ d ∈ dirsCapZ, f d = f (0, 0, -1) + f (0, 0, 1) := by
  rw [dirsCapZ, Finset.sum_insert (by decide), Finset.sum_singleton]

/-! ## The wall/cap face counts per axis -/

/-- `V_x`: the wall-face count of the x-axis layering — the exposed
faces with normal ⊥ `e_x` (w39-dense §1's `V = Σ_z P2(S_z)`; the
slice-sum form is `wallX_eq_sliceP2_sum`). -/
def wallX (U : Finset Cell) : ℕ :=
  ∑ x ∈ U, ∑ d ∈ dirsWallX, (if addDir x d ∈ U then 0 else 1)

/-- `V_y`: the wall-face count of the y-axis layering. -/
def wallY (U : Finset Cell) : ℕ :=
  ∑ x ∈ U, ∑ d ∈ dirsWallY, (if addDir x d ∈ U then 0 else 1)

/-- `V_z`: the wall-face count of the z-axis layering. -/
def wallZ (U : Finset Cell) : ℕ :=
  ∑ x ∈ U, ∑ d ∈ dirsWallZ, (if addDir x d ∈ U then 0 else 1)

/-- `H_x`: the cap-face count of the x-axis layering — the exposed
faces with normal ∥ `±e_x` (w39-dense §1's `H`; the campaign's
`Σ_z(|S_z ∖ S_{z+1}| + |S_z ∖ S_{z−1}|)`). -/
def capX (U : Finset Cell) : ℕ :=
  ∑ x ∈ U, ∑ d ∈ dirsCapX, (if addDir x d ∈ U then 0 else 1)

/-- `H_y`: the cap-face count of the y-axis layering. -/
def capY (U : Finset Cell) : ℕ :=
  ∑ x ∈ U, ∑ d ∈ dirsCapY, (if addDir x d ∈ U then 0 else 1)

/-- `H_z`: the cap-face count of the z-axis layering. -/
def capZ (U : Finset Cell) : ℕ :=
  ∑ x ∈ U, ∑ d ∈ dirsCapZ, (if addDir x d ∈ U then 0 else 1)

/-- The ordered internal x-axis faces of `U`: the pairs `(x, ±e_x)`
with both endpoints in `U` — the ORDERED double count of the
campaign's `Σ_z |S_z ∩ S_{z+1}|` (each vertical adjacency counted
from both endpoints), so that `capX + capInternalX = 2·|U|` is the
subtraction-free form of `H = 2v − 2Σ_z|S_z ∩ S_{z+1}|`. -/
def capInternalX (U : Finset Cell) : ℕ :=
  ∑ x ∈ U, ∑ d ∈ dirsCapX, (if addDir x d ∈ U then 1 else 0)

/-- The ordered internal y-axis faces of `U`. -/
def capInternalY (U : Finset Cell) : ℕ :=
  ∑ x ∈ U, ∑ d ∈ dirsCapY, (if addDir x d ∈ U then 1 else 0)

/-- The ordered internal z-axis faces of `U`. -/
def capInternalZ (U : Finset Cell) : ℕ :=
  ∑ x ∈ U, ∑ d ∈ dirsCapZ, (if addDir x d ∈ U then 1 else 0)

/-! ## [W39-ID], the coarea identity: `|∂U| = H + V` per axis -/

/-- Pointwise: the six exposed-face indicators split into the x-cap
pair plus the x-wall quadruple. -/
private theorem coarea_ptX (U : Finset Cell) (x : Cell) :
    ∑ d ∈ dirs, (if addDir x d ∈ U then (0:ℕ) else 1)
      = (∑ d ∈ dirsCapX, (if addDir x d ∈ U then 0 else 1))
        + ∑ d ∈ dirsWallX, (if addDir x d ∈ U then 0 else 1) := by
  rw [dirs_six, sum_dirsCapX, sum_dirsWallX]
  by_cases h1 : addDir x (-1, 0, 0) ∈ U <;> by_cases h2 : addDir x (1, 0, 0) ∈ U <;>
    by_cases h3 : addDir x (0, -1, 0) ∈ U <;> by_cases h4 : addDir x (0, 1, 0) ∈ U <;>
    by_cases h5 : addDir x (0, 0, -1) ∈ U <;> by_cases h6 : addDir x (0, 0, 1) ∈ U <;>
    simp only [h1, h2, h3, h4, h5, h6] <;> omega

/-- Pointwise: the six exposed-face indicators split into the y-cap
pair plus the y-wall quadruple. -/
private theorem coarea_ptY (U : Finset Cell) (x : Cell) :
    ∑ d ∈ dirs, (if addDir x d ∈ U then (0:ℕ) else 1)
      = (∑ d ∈ dirsCapY, (if addDir x d ∈ U then 0 else 1))
        + ∑ d ∈ dirsWallY, (if addDir x d ∈ U then 0 else 1) := by
  rw [dirs_six, sum_dirsCapY, sum_dirsWallY]
  by_cases h1 : addDir x (-1, 0, 0) ∈ U <;> by_cases h2 : addDir x (1, 0, 0) ∈ U <;>
    by_cases h3 : addDir x (0, -1, 0) ∈ U <;> by_cases h4 : addDir x (0, 1, 0) ∈ U <;>
    by_cases h5 : addDir x (0, 0, -1) ∈ U <;> by_cases h6 : addDir x (0, 0, 1) ∈ U <;>
    simp only [h1, h2, h3, h4, h5, h6] <;> omega

/-- Pointwise: the six exposed-face indicators split into the z-cap
pair plus the z-wall quadruple. -/
private theorem coarea_ptZ (U : Finset Cell) (x : Cell) :
    ∑ d ∈ dirs, (if addDir x d ∈ U then (0:ℕ) else 1)
      = (∑ d ∈ dirsCapZ, (if addDir x d ∈ U then 0 else 1))
        + ∑ d ∈ dirsWallZ, (if addDir x d ∈ U then 0 else 1) := by
  rw [dirs_six, sum_dirsCapZ, sum_dirsWallZ]
  by_cases h1 : addDir x (-1, 0, 0) ∈ U <;> by_cases h2 : addDir x (1, 0, 0) ∈ U <;>
    by_cases h3 : addDir x (0, -1, 0) ∈ U <;> by_cases h4 : addDir x (0, 1, 0) ∈ U <;>
    by_cases h5 : addDir x (0, 0, -1) ∈ U <;> by_cases h6 : addDir x (0, 0, 1) ∈ U <;>
    simp only [h1, h2, h3, h4, h5, h6] <;> omega

/-- **Lemma [W39-ID], x-axis** (w39-dense §1): the coarea identity
`|∂U| = H_x + V_x` — the perimeter splits exactly into the cap faces
(normal `±e_x`) and the wall faces (normal ⊥ `e_x`).  Holds for ANY
finite `U` (no connectivity; stronger than the campaign's solid
statement). -/
theorem coareaX (U : Finset Cell) : perimeter U = capX U + wallX U := by
  rw [perimeter, Finset.sum_congr rfl (fun x _ => coarea_ptX U x),
    Finset.sum_add_distrib]
  rfl

/-- **Lemma [W39-ID], y-axis** (w39-dense §1): `|∂U| = H_y + V_y`. -/
theorem coareaY (U : Finset Cell) : perimeter U = capY U + wallY U := by
  rw [perimeter, Finset.sum_congr rfl (fun x _ => coarea_ptY U x),
    Finset.sum_add_distrib]
  rfl

/-- **Lemma [W39-ID], z-axis** (w39-dense §1): `|∂U| = H_z + V_z`. -/
theorem coareaZ (U : Finset Cell) : perimeter U = capZ U + wallZ U := by
  rw [perimeter, Finset.sum_congr rfl (fun x _ => coarea_ptZ U x),
    Finset.sum_add_distrib]
  rfl

/-! ## The slices and `V = Σ_z P2(S_z)` -/

/-- The `j`-slice of the x-axis layering: `S^x_j = {x ∈ U : x.1 = j}`. -/
def sliceX (U : Finset Cell) (j : ℤ) : Finset Cell := U.filter (fun x => x.1 = j)

/-- The `j`-slice of the y-axis layering. -/
def sliceY (U : Finset Cell) (j : ℤ) : Finset Cell := U.filter (fun x => x.2.1 = j)

/-- The `j`-slice of the z-axis layering. -/
def sliceZ (U : Finset Cell) (j : ℤ) : Finset Cell := U.filter (fun x => x.2.2 = j)

theorem mem_sliceX_iff {U : Finset Cell} {y : Cell} {j : ℤ} :
    y ∈ sliceX U j ↔ y ∈ U ∧ y.1 = j := by simp [sliceX]

theorem mem_sliceY_iff {U : Finset Cell} {y : Cell} {j : ℤ} :
    y ∈ sliceY U j ↔ y ∈ U ∧ y.2.1 = j := by simp [sliceY]

theorem mem_sliceZ_iff {U : Finset Cell} {y : Cell} {j : ℤ} :
    y ∈ sliceZ U j ↔ y ∈ U ∧ y.2.2 = j := by simp [sliceZ]

/-- `P2(S^x_j)`: the 2D in-plane perimeter of the `j`-slice (the
wall-face count of the slice in the four in-plane directions). -/
def sliceP2X (U : Finset Cell) (j : ℤ) : ℕ :=
  ∑ x ∈ sliceX U j, ∑ d ∈ dirsWallX, (if addDir x d ∈ sliceX U j then 0 else 1)

/-- `P2(S^y_j)`: the 2D in-plane perimeter of the `j`-slice. -/
def sliceP2Y (U : Finset Cell) (j : ℤ) : ℕ :=
  ∑ x ∈ sliceY U j, ∑ d ∈ dirsWallY, (if addDir x d ∈ sliceY U j then 0 else 1)

/-- `P2(S^z_j)`: the 2D in-plane perimeter of the `j`-slice. -/
def sliceP2Z (U : Finset Cell) (j : ℤ) : ℕ :=
  ∑ x ∈ sliceZ U j, ∑ d ∈ dirsWallZ, (if addDir x d ∈ sliceZ U j then 0 else 1)

private theorem dirsWallX_fst_zero {d : Cell} (hd : d ∈ dirsWallX) : d.1 = 0 := by
  simp only [dirsWallX, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> rfl

private theorem dirsWallY_mid_zero {d : Cell} (hd : d ∈ dirsWallY) : d.2.1 = 0 := by
  simp only [dirsWallY, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> rfl

private theorem dirsWallZ_lst_zero {d : Cell} (hd : d ∈ dirsWallZ) : d.2.2 = 0 := by
  simp only [dirsWallZ, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> rfl

/-- The slice-sum form of `P2(S^x_j)`: summing over the slice is
summing over `U` conditioned on `x.1 = j`, and inside the slice the
in-plane exposure reads in `U` (an in-plane step preserves the level). -/
private theorem sliceP2X_eq (U : Finset Cell) (j : ℤ) :
    sliceP2X U j
      = ∑ x ∈ U, (if x.1 = j then ∑ d ∈ dirsWallX, (if addDir x d ∈ U then (0:ℕ) else 1)
          else 0) := by
  classical
  rw [sliceP2X, sliceX, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hxj : x.1 = j
  · simp only [hxj, ite_true]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hcoord : (addDir x d).1 = j := by
      simp only [addDir, dirsWallX_fst_zero hd]
      omega
    simp only [Finset.mem_filter, hcoord, and_true]
  · simp only [hxj, ite_false]

/-- The slice-sum form of `P2(S^y_j)`. -/
private theorem sliceP2Y_eq (U : Finset Cell) (j : ℤ) :
    sliceP2Y U j
      = ∑ x ∈ U, (if x.2.1 = j then ∑ d ∈ dirsWallY, (if addDir x d ∈ U then (0:ℕ) else 1)
          else 0) := by
  classical
  rw [sliceP2Y, sliceY, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hxj : x.2.1 = j
  · simp only [hxj, ite_true]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hcoord : (addDir x d).2.1 = j := by
      simp only [addDir, dirsWallY_mid_zero hd]
      omega
    simp only [Finset.mem_filter, hcoord, and_true]
  · simp only [hxj, ite_false]

/-- The slice-sum form of `P2(S^z_j)`. -/
private theorem sliceP2Z_eq (U : Finset Cell) (j : ℤ) :
    sliceP2Z U j
      = ∑ x ∈ U, (if x.2.2 = j then ∑ d ∈ dirsWallZ, (if addDir x d ∈ U then (0:ℕ) else 1)
          else 0) := by
  classical
  rw [sliceP2Z, sliceZ, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hxj : x.2.2 = j
  · simp only [hxj, ite_true]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hcoord : (addDir x d).2.2 = j := by
      simp only [addDir, dirsWallZ_lst_zero hd]
      omega
    simp only [Finset.mem_filter, hcoord, and_true]
  · simp only [hxj, ite_false]

/-- The slice-sum recombination: summing a per-cell budget over `U`
equals summing, per level, the level-conditioned budget (the exact
bookkeeping behind `V = Σ_z P2(S_z)`). -/
private theorem sum_recombineX (U : Finset Cell) (W : Cell → ℕ) :
    ∑ j ∈ U.image (fun y => y.1), ∑ x ∈ U, (if x.1 = j then W x else 0)
      = ∑ x ∈ U, W x := by
  classical
  refine Eq.trans Finset.sum_comm ?_
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.sum_eq_single_of_mem x.1 (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    (fun j _ hj => by simp [hj.symm])]
  simp

private theorem sum_recombineY (U : Finset Cell) (W : Cell → ℕ) :
    ∑ j ∈ U.image (fun y => y.2.1), ∑ x ∈ U, (if x.2.1 = j then W x else 0)
      = ∑ x ∈ U, W x := by
  classical
  refine Eq.trans Finset.sum_comm ?_
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.sum_eq_single_of_mem x.2.1 (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    (fun j _ hj => by simp [hj.symm])]
  simp

private theorem sum_recombineZ (U : Finset Cell) (W : Cell → ℕ) :
    ∑ j ∈ U.image (fun y => y.2.2), ∑ x ∈ U, (if x.2.2 = j then W x else 0)
      = ∑ x ∈ U, W x := by
  classical
  refine Eq.trans Finset.sum_comm ?_
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.sum_eq_single_of_mem x.2.2 (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    (fun j _ hj => by simp [hj.symm])]
  simp

/-- **Lemma [W39-ID], slice-sum form, x-axis** (w39-dense §1): the
wall count IS the slice-`P2` sum, `V_x = Σ_j P2(S^x_j)` — the sum
running over the level set of `U` (a slice at a level `U` does not
meet is empty and contributes `0`).  Each slice's `P2` reads in `U`
because an in-plane step preserves the level. -/
theorem wallX_eq_sliceP2_sum (U : Finset Cell) :
    wallX U = ∑ j ∈ U.image (fun y => y.1), sliceP2X U j := by
  classical
  rw [wallX]
  refine Eq.trans ?_ (Eq.symm (Finset.sum_congr rfl fun j _ => sliceP2X_eq U j))
  exact Eq.symm (sum_recombineX U
    (fun x => ∑ d ∈ dirsWallX, (if addDir x d ∈ U then (0:ℕ) else 1)))

/-- **Lemma [W39-ID], slice-sum form, y-axis** (w39-dense §1):
`V_y = Σ_j P2(S^y_j)`. -/
theorem wallY_eq_sliceP2_sum (U : Finset Cell) :
    wallY U = ∑ j ∈ U.image (fun y => y.2.1), sliceP2Y U j := by
  classical
  rw [wallY]
  refine Eq.trans ?_ (Eq.symm (Finset.sum_congr rfl fun j _ => sliceP2Y_eq U j))
  exact Eq.symm (sum_recombineY U
    (fun x => ∑ d ∈ dirsWallY, (if addDir x d ∈ U then (0:ℕ) else 1)))

/-- **Lemma [W39-ID], slice-sum form, z-axis** (w39-dense §1):
`V_z = Σ_j P2(S^z_j)`. -/
theorem wallZ_eq_sliceP2_sum (U : Finset Cell) :
    wallZ U = ∑ j ∈ U.image (fun y => y.2.2), sliceP2Z U j := by
  classical
  rw [wallZ]
  refine Eq.trans ?_ (Eq.symm (Finset.sum_congr rfl fun j _ => sliceP2Z_eq U j))
  exact Eq.symm (sum_recombineZ U
    (fun x => ∑ d ∈ dirsWallZ, (if addDir x d ∈ U then (0:ℕ) else 1)))

/-! ## The cap budget: `H = 2v − 2Σ_z|S_z ∩ S_{z+1}|`, subtraction-free -/

/-- **The x-cap budget** (w39-dense §1's `H = 2v − 2Σ_z|S_z ∩ S_{z+1}|`
in subtraction-free ℕ form, with `Σ_z|S_z ∩ S_{z+1}|` the ORDERED
double count `capInternalX`): every cell's two axis faces are either
exposed (caps) or internal (a vertical adjacency merging one top face
with one bottom face), so `H_x + capInternalX = 2·|U|`. -/
theorem capX_add_capInternalX (U : Finset Cell) :
    capX U + capInternalX U = 2 * U.card := by
  classical
  have hpt : ∀ x ∈ U, (∑ d ∈ dirsCapX, (if addDir x d ∈ U then (0:ℕ) else 1))
      + ∑ d ∈ dirsCapX, (if addDir x d ∈ U then 1 else 0) = 2 := by
    intro x _
    rw [sum_dirsCapX, sum_dirsCapX]
    by_cases h1 : addDir x (-1, 0, 0) ∈ U <;> by_cases h2 : addDir x (1, 0, 0) ∈ U <;>
      simp [h1, h2]
  rw [capX, capInternalX, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl (fun x hx => hpt x hx), Finset.sum_const, smul_eq_mul,
    Nat.mul_comm]

/-- **The y-cap budget**: `H_y + capInternalY = 2·|U|`. -/
theorem capY_add_capInternalY (U : Finset Cell) :
    capY U + capInternalY U = 2 * U.card := by
  classical
  have hpt : ∀ x ∈ U, (∑ d ∈ dirsCapY, (if addDir x d ∈ U then (0:ℕ) else 1))
      + ∑ d ∈ dirsCapY, (if addDir x d ∈ U then 1 else 0) = 2 := by
    intro x _
    rw [sum_dirsCapY, sum_dirsCapY]
    by_cases h1 : addDir x (0, -1, 0) ∈ U <;> by_cases h2 : addDir x (0, 1, 0) ∈ U <;>
      simp [h1, h2]
  rw [capY, capInternalY, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl (fun x hx => hpt x hx), Finset.sum_const, smul_eq_mul,
    Nat.mul_comm]

/-- **The z-cap budget**: `H_z + capInternalZ = 2·|U|`. -/
theorem capZ_add_capInternalZ (U : Finset Cell) :
    capZ U + capInternalZ U = 2 * U.card := by
  classical
  have hpt : ∀ x ∈ U, (∑ d ∈ dirsCapZ, (if addDir x d ∈ U then (0:ℕ) else 1))
      + ∑ d ∈ dirsCapZ, (if addDir x d ∈ U then 1 else 0) = 2 := by
    intro x _
    rw [sum_dirsCapZ, sum_dirsCapZ]
    by_cases h1 : addDir x (0, 0, -1) ∈ U <;> by_cases h2 : addDir x (0, 0, 1) ∈ U <;>
      simp [h1, h2]
  rw [capZ, capInternalZ, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl (fun x hx => hpt x hx), Finset.sum_const, smul_eq_mul,
    Nat.mul_comm]

/-! ## [G28-ID]: the axis-triple identity and the min-axis bound -/

/-- Pointwise: each exposed face is a wall for exactly TWO of the
three layerings (its normal is ⊥ exactly two of the three axes). -/
private theorem wall_triple_pt (U : Finset Cell) (x : Cell) :
    (∑ d ∈ dirsWallX, (if addDir x d ∈ U then (0:ℕ) else 1))
      + (∑ d ∈ dirsWallY, (if addDir x d ∈ U then 0 else 1))
      + (∑ d ∈ dirsWallZ, (if addDir x d ∈ U then 0 else 1))
      = 2 * ∑ d ∈ dirs, (if addDir x d ∈ U then 0 else 1) := by
  rw [sum_dirsWallX, sum_dirsWallY, sum_dirsWallZ, dirs_six]
  by_cases h1 : addDir x (-1, 0, 0) ∈ U <;> by_cases h2 : addDir x (1, 0, 0) ∈ U <;>
    by_cases h3 : addDir x (0, -1, 0) ∈ U <;> by_cases h4 : addDir x (0, 1, 0) ∈ U <;>
    by_cases h5 : addDir x (0, 0, -1) ∈ U <;> by_cases h6 : addDir x (0, 0, 1) ∈ U <;>
    simp only [h1, h2, h3, h4, h5, h6] <;> omega

/-- **Lemma [G28-ID]** (w42-adjudicate §1): the axis-triple identity
`V_x + V_y + V_z = 2·|∂U|` — every face has a normal `±e_a` for
exactly one axis `a` and is a wall for exactly the other two axes, so
it is counted in exactly two of the three wall counts.  Gate-29
exhaustively confirmed on 27,622 classes. -/
theorem sum_wall_eq_twice_perimeter (U : Finset Cell) :
    wallX U + wallY U + wallZ U = 2 * perimeter U := by
  classical
  calc wallX U + wallY U + wallZ U
      = (∑ x ∈ U, ∑ d ∈ dirsWallX, (if addDir x d ∈ U then (0:ℕ) else 1))
        + (∑ x ∈ U, ∑ d ∈ dirsWallY, (if addDir x d ∈ U then 0 else 1))
        + (∑ x ∈ U, ∑ d ∈ dirsWallZ, (if addDir x d ∈ U then 0 else 1)) := rfl
    _ = ∑ x ∈ U, ((∑ d ∈ dirsWallX, (if addDir x d ∈ U then 0 else 1))
        + (∑ d ∈ dirsWallY, (if addDir x d ∈ U then 0 else 1))
        + (∑ d ∈ dirsWallZ, (if addDir x d ∈ U then 0 else 1))) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    _ = ∑ x ∈ U, (2 * ∑ d ∈ dirs, (if addDir x d ∈ U then 0 else 1)) :=
        Finset.sum_congr rfl (fun x _ => wall_triple_pt U x)
    _ = perimeter U + perimeter U := by
        rw [Finset.sum_congr rfl (fun x _ => Nat.two_mul
          (∑ d ∈ dirs, (if addDir x d ∈ U then (0:ℕ) else 1))),
          Finset.sum_add_distrib, perimeter]
    _ = 2 * perimeter U := (Nat.two_mul _).symm

/-- **Lemma [G28-ID], min-axis form** (w42-adjudicate §1): some axis
has `3·V_a ≤ 2·|∂U|` — every finite cell set has an axis-layering
with wall count at most `2/3·|∂U|` (the min-axis layering; the
"deep-wall region" `{V_a > 2·|∂U|/3 for all a}` is empty).  This is
the exact input the min-axis layered book [W42-LAYER] consumes; per
the Gate-29 retraction the BOOK did not bank, this identity did. -/
theorem wall_min_axis (U : Finset Cell) :
    3 * wallX U ≤ 2 * perimeter U ∨ 3 * wallY U ≤ 2 * perimeter U
      ∨ 3 * wallZ U ≤ 2 * perimeter U := by
  by_cases h1 : 3 * wallX U ≤ 2 * perimeter U
  · exact Or.inl h1
  by_cases h2 : 3 * wallY U ≤ 2 * perimeter U
  · exact Or.inr (Or.inl h2)
  refine Or.inr (Or.inr ?_)
  have hsum := sum_wall_eq_twice_perimeter U
  omega

/-- Pointwise: each exposed face is a cap for exactly ONE layering
(its normal is ∥ exactly one axis). -/
private theorem cap_triple_pt (U : Finset Cell) (x : Cell) :
    (∑ d ∈ dirsCapX, (if addDir x d ∈ U then (0:ℕ) else 1))
      + (∑ d ∈ dirsCapY, (if addDir x d ∈ U then 0 else 1))
      + (∑ d ∈ dirsCapZ, (if addDir x d ∈ U then 0 else 1))
      = ∑ d ∈ dirs, (if addDir x d ∈ U then 0 else 1) := by
  rw [sum_dirsCapX, sum_dirsCapY, sum_dirsCapZ, dirs_six]
  by_cases h1 : addDir x (-1, 0, 0) ∈ U <;> by_cases h2 : addDir x (1, 0, 0) ∈ U <;>
    by_cases h3 : addDir x (0, -1, 0) ∈ U <;> by_cases h4 : addDir x (0, 1, 0) ∈ U <;>
    by_cases h5 : addDir x (0, 0, -1) ∈ U <;> by_cases h6 : addDir x (0, 0, 1) ∈ U <;>
    simp only [h1, h2, h3, h4, h5, h6] <;> omega

/-- **The cap-census mirror of [G28-ID]**: `H_x + H_y + H_z = |∂U|` —
every exposed face has a normal `±e_a` for exactly one axis, so it is
counted in exactly one of the three cap counts (together with
`sum_wall_eq_twice_perimeter` and the three coarea identities this
exhausts the face census). -/
theorem sum_cap_eq_perimeter (U : Finset Cell) :
    capX U + capY U + capZ U = perimeter U := by
  classical
  calc capX U + capY U + capZ U
      = (∑ x ∈ U, ∑ d ∈ dirsCapX, (if addDir x d ∈ U then (0:ℕ) else 1))
        + (∑ x ∈ U, ∑ d ∈ dirsCapY, (if addDir x d ∈ U then 0 else 1))
        + (∑ x ∈ U, ∑ d ∈ dirsCapZ, (if addDir x d ∈ U then 0 else 1)) := rfl
    _ = ∑ x ∈ U, ((∑ d ∈ dirsCapX, (if addDir x d ∈ U then 0 else 1))
        + (∑ d ∈ dirsCapY, (if addDir x d ∈ U then 0 else 1))
        + (∑ d ∈ dirsCapZ, (if addDir x d ∈ U then 0 else 1))) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    _ = ∑ x ∈ U, ∑ d ∈ dirs, (if addDir x d ∈ U then 0 else 1) :=
        Finset.sum_congr rfl (fun x _ => cap_triple_pt U x)
    _ = perimeter U := rfl

/-- **The min-cap bound**: some axis has `3·H_a ≤ |∂U|` (the mirror of
`wall_min_axis` over the cap census). -/
theorem cap_min_axis (U : Finset Cell) :
    3 * capX U ≤ perimeter U ∨ 3 * capY U ≤ perimeter U
      ∨ 3 * capZ U ≤ perimeter U := by
  by_cases h1 : 3 * capX U ≤ perimeter U
  · exact Or.inl h1
  by_cases h2 : 3 * capY U ≤ perimeter U
  · exact Or.inr (Or.inl h2)
  refine Or.inr (Or.inr ?_)
  have hsum := sum_cap_eq_perimeter U
  omega

end YangMills3D

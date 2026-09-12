/-
The exact anchored-count floor layer: W29-FLOOR (the shadow-projection
tube bound) and W29-DEC (boundary additivity over components), Lean form
(wave 29).

SOURCE. `problems/yang-mills-mass-gap/lemmas/w29-count.md` §2 (Lemma
W29-DEC and the W29-FLOOR shadow bound) with the face-perimeter and
direction machinery of `lemmas/w24-cold.md`/`lemmas/w25-cluster.md`
(W25-N1: `P = 6n − 2e`), reusing `YangMills3D.Animals` (`Cell`, `dirs`,
`addDir`, `perimeter`).

The campaign's W29-FLOOR: no closed surface through two anchors at
x-separation `d` has fewer than `4d + 2` plaquettes (tight: the tube
`{1, …, d}`).  The proof is the shadow-projection pigeonhole: each met
fiber (a column of cells sharing the other two coordinates) contributes
its two extreme exposed faces, so the exposed-face count dominates twice
the three shadow sizes; every x-layer met shows up in two of the shadows.

Here the statement is made in the cleanest self-contained cell form
(the dual of the campaign's plaquette picture): for a finite cell set
`A` with exposed-face count `perimeter A` (exactly the campaign `|dW|`
for the boundary surface `dW = ∂A`) and `xext A` = the number of
distinct x-layers met,

  `perimeter A ≥ 4·xext A + 2`   (the shadow bound; `= 4d + 2` for a
  `d`-tube, so the floor is TIGHT),

and if every x-layer `1, …, d` is met (`xext A ≥ d`, the consequence of
surface-connectedness + crossing that the campaign uses) then
`perimeter A ≥ 4d + 2` — W29-FLOOR verbatim.  The cruder bbox floor
`2(ab + bc + ca)` is FALSE for sparse sets (w29-count §2: a 3-cell
edge-chain has 18 exposed faces in a 3×3×1 box) — the shadow form is the
correct statement, as the campaign itself learned in-session.

W29-DEC: the exposed-face count is ADDITIVE over pairwise
non-face-contacting sets — `perimeter (A ∪ B) = perimeter A + perimeter
B` — hence over the 6-connected components `C_i` of `W`:
`|∂W| = Σ_i |∂C_i|` (disjoint boundary face sets).

Every statement below is fully proved: no unfinished proofs, no new
axioms.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import YangMills3D.Animals

namespace YangMills3D

/-! ## Shadows, layers, and directional exposed faces -/

/-- The yz-shadow of a finite cell set: the `(y, z)` positions met. -/
def shadowYZ (A : Finset Cell) : Finset (ℤ × ℤ) := A.image fun c => (c.2.1, c.2.2)

/-- The xz-shadow of a finite cell set. -/
def shadowXZ (A : Finset Cell) : Finset (ℤ × ℤ) := A.image fun c => (c.1, c.2.2)

/-- The xy-shadow of a finite cell set. -/
def shadowXY (A : Finset Cell) : Finset (ℤ × ℤ) := A.image fun c => (c.1, c.2.1)

/-- The x-extent: the number of distinct x-layers met by the set. -/
def xext (A : Finset Cell) : ℕ := (A.image fun c => c.1).card

/-- The cells of `A` with an exposed face in direction `d`. -/
def exposedIn (A : Finset Cell) (d : Cell) : Finset Cell :=
  A.filter fun c => addDir c d ∉ A

/-- The exposed faces decompose per direction: the indicator sum in a
fixed direction `d` is the number of cells exposed that way. -/
private lemma sum_exposed_eq_card (A : Finset Cell) (d : Cell) :
    ∑ c ∈ A, (if addDir c d ∈ A then 0 else 1) = (exposedIn A d).card := by
  have h2 : ∑ c ∈ A.filter (fun c : Cell => addDir c d ∉ A), (1 : ℕ)
      = (A.filter (fun c : Cell => addDir c d ∉ A)).card := by
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
  rw [exposedIn, ← h2, Finset.sum_filter]
  exact Finset.sum_congr rfl fun c _ => by
    by_cases hc : addDir c d ∈ A <;> simp [hc]

/-- The six directions of `dirs`, spelled out. -/
private lemma sum_dirs6 {β : Type*} [AddCommMonoid β] (f : Cell → β) :
    ∑ d ∈ dirs, f d
      = f (-1, 0, 0) + (f (1, 0, 0) + (f (0, -1, 0) + (f (0, 1, 0)
        + (f (0, 0, -1) + f (0, 0, 1))))) := by
  rw [dirs, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]

/-- The perimeter is the sum of the six directional exposed-face counts. -/
private lemma perimeter_eq_exposed (A : Finset Cell) :
    perimeter A = (exposedIn A (-1, 0, 0)).card + ((exposedIn A (1, 0, 0)).card
      + ((exposedIn A (0, -1, 0)).card + ((exposedIn A (0, 1, 0)).card
      + ((exposedIn A (0, 0, -1)).card + (exposedIn A (0, 0, 1)).card)))) := by
  have hcard : ∀ d : Cell,
      (∑ c ∈ A, (if addDir c d ∈ A then 0 else 1)) = (exposedIn A d).card :=
    fun d => sum_exposed_eq_card A d
  simp only [perimeter]
  rw [Finset.sum_comm, sum_dirs6]
  rw [hcard (-1, 0, 0), hcard (1, 0, 0), hcard (0, -1, 0), hcard (0, 1, 0),
    hcard (0, 0, -1), hcard (0, 0, 1)]

/-! ## The shadow-projection pigeonhole (W29-FLOOR, core) -/

/-- Each met yz-position has a minimal-x cell, and its `-x` face is
exposed. -/
private lemma exists_minx_exposed (A : Finset Cell) (p : ℤ × ℤ)
    (hp : p ∈ shadowYZ A) :
    ∃ c ∈ exposedIn A (-1, 0, 0), ((c.2.1, c.2.2)) = p := by
  obtain ⟨c₀, hc₀, hp⟩ := Finset.mem_image.mp hp
  set F := A.filter (fun c : Cell => (c.2.1, c.2.2) = p) with hF
  have hFne : F.Nonempty := ⟨c₀, Finset.mem_filter.mpr ⟨hc₀, hp⟩⟩
  have hXne : (F.image (fun c : Cell => c.1)).Nonempty := hFne.image _
  have hxmem := Finset.min'_mem _ hXne
  have hx : ∀ x ∈ F.image (fun c : Cell => c.1),
       (F.image (fun c : Cell => c.1)).min' hXne ≤ x := fun x hx =>
    Finset.min'_le _ _ hx
  obtain ⟨c, hcF, hc1⟩ := Finset.mem_image.mp hxmem
  have hk : (c.2.1, c.2.2) = p := (Finset.mem_filter.mp hcF).2
  rw [Prod.mk.injEq] at hk
  obtain ⟨hk1, hk2⟩ := hk
  have hcval : c = ((F.image (fun c : Cell => c.1)).min' hXne, p.1, p.2) := by
    rw [show c = (c.1, c.2.1, c.2.2) from rfl, hc1, hk1, hk2]
  have hcell : ((F.image (fun c : Cell => c.1)).min' hXne, p.1, p.2) ∈ exposedIn A (-1, 0, 0) := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [← hcval]; exact (Finset.mem_filter.mp hcF).1
    · intro hbad
      have hunf : addDir ((F.image (fun c : Cell => c.1)).min' hXne, p.1, p.2)
          (-1, 0, 0) = ((F.image (fun c : Cell => c.1)).min' hXne - 1, p.1, p.2) := by
        simp only [addDir]
        have e1 : (F.image (fun c : Cell => c.1)).min' hXne + (-1 : ℤ) = (F.image (fun c : Cell => c.1)).min' hXne - 1 := by omega
        have e2 : p.1 + (0 : ℤ) = p.1 := by omega
        have e3 : p.2 + (0 : ℤ) = p.2 := by omega
        rw [e1, e2, e3]
      rw [hunf] at hbad
      have hfib : ((F.image (fun c : Cell => c.1)).min' hXne - 1, p.1, p.2) ∈ F :=
        Finset.mem_filter.mpr ⟨hbad, rfl⟩
      have hz : (((F.image (fun c : Cell => c.1)).min' hXne - 1) : ℤ) ∈ F.image (fun c : Cell => c.1) :=
        Finset.mem_image.mpr ⟨_, hfib, rfl⟩
      exact absurd (hx _ hz) (by omega)
  exact ⟨_, hcell, rfl⟩

/-- Each met yz-position has a maximal-x cell, and its `+x` face is
exposed. -/
private lemma exists_maxx_exposed (A : Finset Cell) (p : ℤ × ℤ)
    (hp : p ∈ shadowYZ A) :
    ∃ c ∈ exposedIn A (1, 0, 0), ((c.2.1, c.2.2)) = p := by
  obtain ⟨c₀, hc₀, hp⟩ := Finset.mem_image.mp hp
  set F := A.filter (fun c : Cell => (c.2.1, c.2.2) = p) with hF
  have hFne : F.Nonempty := ⟨c₀, Finset.mem_filter.mpr ⟨hc₀, hp⟩⟩
  have hXne : (F.image (fun c : Cell => c.1)).Nonempty := hFne.image _
  have hxmem := Finset.max'_mem _ hXne
  have hx : ∀ x ∈ F.image (fun c : Cell => c.1),
      x ≤ (F.image (fun c : Cell => c.1)).max' hXne  := fun x hx =>
    Finset.le_max' _ _ hx
  obtain ⟨c, hcF, hc1⟩ := Finset.mem_image.mp hxmem
  have hk : (c.2.1, c.2.2) = p := (Finset.mem_filter.mp hcF).2
  rw [Prod.mk.injEq] at hk
  obtain ⟨hk1, hk2⟩ := hk
  have hcval : c = ((F.image (fun c : Cell => c.1)).max' hXne, p.1, p.2) := by
    rw [show c = (c.1, c.2.1, c.2.2) from rfl, hc1, hk1, hk2]
  have hcell : ((F.image (fun c : Cell => c.1)).max' hXne, p.1, p.2) ∈ exposedIn A (1, 0, 0) := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [← hcval]; exact (Finset.mem_filter.mp hcF).1
    · intro hbad
      have hunf : addDir ((F.image (fun c : Cell => c.1)).max' hXne, p.1, p.2)
          (1, 0, 0) = ((F.image (fun c : Cell => c.1)).max' hXne + 1, p.1, p.2) := by
        simp only [addDir]
        have e2 : p.1 + (0 : ℤ) = p.1 := by omega
        have e3 : p.2 + (0 : ℤ) = p.2 := by omega
        rw [e2, e3]
      rw [hunf] at hbad
      have hfib : ((F.image (fun c : Cell => c.1)).max' hXne + 1, p.1, p.2) ∈ F :=
        Finset.mem_filter.mpr ⟨hbad, rfl⟩
      have hz : (((F.image (fun c : Cell => c.1)).max' hXne + 1) : ℤ) ∈ F.image (fun c : Cell => c.1) :=
        Finset.mem_image.mpr ⟨_, hfib, rfl⟩
      exact absurd (hx _ hz) (by omega)
  exact ⟨_, hcell, rfl⟩

/-- Each met xz-position has a minimal-y cell, and its `-y` face is
exposed. -/
private lemma exists_miny_exposed (A : Finset Cell) (p : ℤ × ℤ)
    (hp : p ∈ shadowXZ A) :
    ∃ c ∈ exposedIn A (0, -1, 0), ((c.1, c.2.2)) = p := by
  obtain ⟨c₀, hc₀, hp⟩ := Finset.mem_image.mp hp
  set F := A.filter (fun c : Cell => (c.1, c.2.2) = p) with hF
  have hFne : F.Nonempty := ⟨c₀, Finset.mem_filter.mpr ⟨hc₀, hp⟩⟩
  have hXne : (F.image (fun c : Cell => c.2.1)).Nonempty := hFne.image _
  have hxmem := Finset.min'_mem _ hXne
  have hx : ∀ x ∈ F.image (fun c : Cell => c.2.1),
       (F.image (fun c : Cell => c.2.1)).min' hXne ≤ x := fun x hx =>
    Finset.min'_le _ _ hx
  obtain ⟨c, hcF, hc1⟩ := Finset.mem_image.mp hxmem
  have hk : (c.1, c.2.2) = p := (Finset.mem_filter.mp hcF).2
  rw [Prod.mk.injEq] at hk
  obtain ⟨hk1, hk2⟩ := hk
  have hcval : c = (p.1, (F.image (fun c : Cell => c.2.1)).min' hXne, p.2) := by
    rw [show c = (c.1, c.2.1, c.2.2) from rfl, hc1, hk1, hk2]
  have hcell : (p.1, (F.image (fun c : Cell => c.2.1)).min' hXne, p.2) ∈ exposedIn A (0, -1, 0) := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [← hcval]; exact (Finset.mem_filter.mp hcF).1
    · intro hbad
      have hunf : addDir (p.1, (F.image (fun c : Cell => c.2.1)).min' hXne, p.2)
          (0, -1, 0) = (p.1, (F.image (fun c : Cell => c.2.1)).min' hXne - 1, p.2) := by
        simp only [addDir]
        have e1 : (F.image (fun c : Cell => c.2.1)).min' hXne + (-1 : ℤ) = (F.image (fun c : Cell => c.2.1)).min' hXne - 1 := by omega
        have e2 : p.1 + (0 : ℤ) = p.1 := by omega
        have e3 : p.2 + (0 : ℤ) = p.2 := by omega
        rw [e1, e2, e3]
      rw [hunf] at hbad
      have hfib : (p.1, (F.image (fun c : Cell => c.2.1)).min' hXne - 1, p.2) ∈ F :=
        Finset.mem_filter.mpr ⟨hbad, rfl⟩
      have hz : (((F.image (fun c : Cell => c.2.1)).min' hXne - 1) : ℤ) ∈ F.image (fun c : Cell => c.2.1) :=
        Finset.mem_image.mpr ⟨_, hfib, rfl⟩
      exact absurd (hx _ hz) (by omega)
  exact ⟨_, hcell, rfl⟩

/-- Each met xz-position has a maximal-y cell, and its `+y` face is
exposed. -/
private lemma exists_maxy_exposed (A : Finset Cell) (p : ℤ × ℤ)
    (hp : p ∈ shadowXZ A) :
    ∃ c ∈ exposedIn A (0, 1, 0), ((c.1, c.2.2)) = p := by
  obtain ⟨c₀, hc₀, hp⟩ := Finset.mem_image.mp hp
  set F := A.filter (fun c : Cell => (c.1, c.2.2) = p) with hF
  have hFne : F.Nonempty := ⟨c₀, Finset.mem_filter.mpr ⟨hc₀, hp⟩⟩
  have hXne : (F.image (fun c : Cell => c.2.1)).Nonempty := hFne.image _
  have hxmem := Finset.max'_mem _ hXne
  have hx : ∀ x ∈ F.image (fun c : Cell => c.2.1),
      x ≤ (F.image (fun c : Cell => c.2.1)).max' hXne  := fun x hx =>
    Finset.le_max' _ _ hx
  obtain ⟨c, hcF, hc1⟩ := Finset.mem_image.mp hxmem
  have hk : (c.1, c.2.2) = p := (Finset.mem_filter.mp hcF).2
  rw [Prod.mk.injEq] at hk
  obtain ⟨hk1, hk2⟩ := hk
  have hcval : c = (p.1, (F.image (fun c : Cell => c.2.1)).max' hXne, p.2) := by
    rw [show c = (c.1, c.2.1, c.2.2) from rfl, hc1, hk1, hk2]
  have hcell : (p.1, (F.image (fun c : Cell => c.2.1)).max' hXne, p.2) ∈ exposedIn A (0, 1, 0) := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [← hcval]; exact (Finset.mem_filter.mp hcF).1
    · intro hbad
      have hunf : addDir (p.1, (F.image (fun c : Cell => c.2.1)).max' hXne, p.2)
          (0, 1, 0) = (p.1, (F.image (fun c : Cell => c.2.1)).max' hXne + 1, p.2) := by
        simp only [addDir]
        have e2 : p.1 + (0 : ℤ) = p.1 := by omega
        have e3 : p.2 + (0 : ℤ) = p.2 := by omega
        rw [e2, e3]
      rw [hunf] at hbad
      have hfib : (p.1, (F.image (fun c : Cell => c.2.1)).max' hXne + 1, p.2) ∈ F :=
        Finset.mem_filter.mpr ⟨hbad, rfl⟩
      have hz : (((F.image (fun c : Cell => c.2.1)).max' hXne + 1) : ℤ) ∈ F.image (fun c : Cell => c.2.1) :=
        Finset.mem_image.mpr ⟨_, hfib, rfl⟩
      exact absurd (hx _ hz) (by omega)
  exact ⟨_, hcell, rfl⟩

/-- Each met xy-position has a minimal-z cell, and its `-z` face is
exposed. -/
private lemma exists_minz_exposed (A : Finset Cell) (p : ℤ × ℤ)
    (hp : p ∈ shadowXY A) :
    ∃ c ∈ exposedIn A (0, 0, -1), ((c.1, c.2.1)) = p := by
  obtain ⟨c₀, hc₀, hp⟩ := Finset.mem_image.mp hp
  set F := A.filter (fun c : Cell => (c.1, c.2.1) = p) with hF
  have hFne : F.Nonempty := ⟨c₀, Finset.mem_filter.mpr ⟨hc₀, hp⟩⟩
  have hXne : (F.image (fun c : Cell => c.2.2)).Nonempty := hFne.image _
  have hxmem := Finset.min'_mem _ hXne
  have hx : ∀ x ∈ F.image (fun c : Cell => c.2.2),
       (F.image (fun c : Cell => c.2.2)).min' hXne ≤ x := fun x hx =>
    Finset.min'_le _ _ hx
  obtain ⟨c, hcF, hc1⟩ := Finset.mem_image.mp hxmem
  have hk : (c.1, c.2.1) = p := (Finset.mem_filter.mp hcF).2
  rw [Prod.mk.injEq] at hk
  obtain ⟨hk1, hk2⟩ := hk
  have hcval : c = (p.1, p.2, (F.image (fun c : Cell => c.2.2)).min' hXne) := by
    rw [show c = (c.1, c.2.1, c.2.2) from rfl, hc1, hk1, hk2]
  have hcell : (p.1, p.2, (F.image (fun c : Cell => c.2.2)).min' hXne) ∈ exposedIn A (0, 0, -1) := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [← hcval]; exact (Finset.mem_filter.mp hcF).1
    · intro hbad
      have hunf : addDir (p.1, p.2, (F.image (fun c : Cell => c.2.2)).min' hXne)
          (0, 0, -1) = (p.1, p.2, (F.image (fun c : Cell => c.2.2)).min' hXne - 1) := by
        simp only [addDir]
        have e1 : (F.image (fun c : Cell => c.2.2)).min' hXne + (-1 : ℤ) = (F.image (fun c : Cell => c.2.2)).min' hXne - 1 := by omega
        have e2 : p.1 + (0 : ℤ) = p.1 := by omega
        have e3 : p.2 + (0 : ℤ) = p.2 := by omega
        rw [e1, e2, e3]
      rw [hunf] at hbad
      have hfib : (p.1, p.2, (F.image (fun c : Cell => c.2.2)).min' hXne - 1) ∈ F :=
        Finset.mem_filter.mpr ⟨hbad, rfl⟩
      have hz : (((F.image (fun c : Cell => c.2.2)).min' hXne - 1) : ℤ) ∈ F.image (fun c : Cell => c.2.2) :=
        Finset.mem_image.mpr ⟨_, hfib, rfl⟩
      exact absurd (hx _ hz) (by omega)
  exact ⟨_, hcell, rfl⟩

/-- Each met xy-position has a maximal-z cell, and its `+z` face is
exposed. -/
private lemma exists_maxz_exposed (A : Finset Cell) (p : ℤ × ℤ)
    (hp : p ∈ shadowXY A) :
    ∃ c ∈ exposedIn A (0, 0, 1), ((c.1, c.2.1)) = p := by
  obtain ⟨c₀, hc₀, hp⟩ := Finset.mem_image.mp hp
  set F := A.filter (fun c : Cell => (c.1, c.2.1) = p) with hF
  have hFne : F.Nonempty := ⟨c₀, Finset.mem_filter.mpr ⟨hc₀, hp⟩⟩
  have hXne : (F.image (fun c : Cell => c.2.2)).Nonempty := hFne.image _
  have hxmem := Finset.max'_mem _ hXne
  have hx : ∀ x ∈ F.image (fun c : Cell => c.2.2),
      x ≤ (F.image (fun c : Cell => c.2.2)).max' hXne  := fun x hx =>
    Finset.le_max' _ _ hx
  obtain ⟨c, hcF, hc1⟩ := Finset.mem_image.mp hxmem
  have hk : (c.1, c.2.1) = p := (Finset.mem_filter.mp hcF).2
  rw [Prod.mk.injEq] at hk
  obtain ⟨hk1, hk2⟩ := hk
  have hcval : c = (p.1, p.2, (F.image (fun c : Cell => c.2.2)).max' hXne) := by
    rw [show c = (c.1, c.2.1, c.2.2) from rfl, hc1, hk1, hk2]
  have hcell : (p.1, p.2, (F.image (fun c : Cell => c.2.2)).max' hXne) ∈ exposedIn A (0, 0, 1) := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [← hcval]; exact (Finset.mem_filter.mp hcF).1
    · intro hbad
      have hunf : addDir (p.1, p.2, (F.image (fun c : Cell => c.2.2)).max' hXne)
          (0, 0, 1) = (p.1, p.2, (F.image (fun c : Cell => c.2.2)).max' hXne + 1) := by
        simp only [addDir]
        have e2 : p.1 + (0 : ℤ) = p.1 := by omega
        have e3 : p.2 + (0 : ℤ) = p.2 := by omega
        rw [e2, e3]
      rw [hunf] at hbad
      have hfib : (p.1, p.2, (F.image (fun c : Cell => c.2.2)).max' hXne + 1) ∈ F :=
        Finset.mem_filter.mpr ⟨hbad, rfl⟩
      have hz : (((F.image (fun c : Cell => c.2.2)).max' hXne + 1) : ℤ) ∈ F.image (fun c : Cell => c.2.2) :=
        Finset.mem_image.mpr ⟨_, hfib, rfl⟩
      exact absurd (hx _ hz) (by omega)
  exact ⟨_, hcell, rfl⟩

/-- The yz-shadow is dominated by the `-x`-exposed cells (via their
(y, z)-labels: distinct labels label distinct cells). -/
private lemma shadowYZ_le_exposed_negx (A : Finset Cell) :
    (shadowYZ A).card ≤ (exposedIn A (-1, 0, 0)).card := by
  have hsub : shadowYZ A
      ⊆ (exposedIn A (-1, 0, 0)).image (fun c => (c.2.1, c.2.2)) := by
    intro p hp
    obtain ⟨c, hc, hkey⟩ := exists_minx_exposed A p hp
    exact Finset.mem_image.mpr ⟨c, hc, hkey⟩
  exact le_trans (Finset.card_le_card hsub) Finset.card_image_le

/-- The yz-shadow is dominated by the `+x`-exposed cells. -/
private lemma shadowYZ_le_exposed_posx (A : Finset Cell) :
    (shadowYZ A).card ≤ (exposedIn A (1, 0, 0)).card := by
  have hsub : shadowYZ A
      ⊆ (exposedIn A (1, 0, 0)).image (fun c => (c.2.1, c.2.2)) := by
    intro p hp
    obtain ⟨c, hc, hkey⟩ := exists_maxx_exposed A p hp
    exact Finset.mem_image.mpr ⟨c, hc, hkey⟩
  exact le_trans (Finset.card_le_card hsub) Finset.card_image_le

/-- The xz-shadow is dominated by the `-y`-exposed cells. -/
private lemma shadowXZ_le_exposed_negy (A : Finset Cell) :
    (shadowXZ A).card ≤ (exposedIn A (0, -1, 0)).card := by
  have hsub : shadowXZ A
      ⊆ (exposedIn A (0, -1, 0)).image (fun c => (c.1, c.2.2)) := by
    intro p hp
    obtain ⟨c, hc, hkey⟩ := exists_miny_exposed A p hp
    exact Finset.mem_image.mpr ⟨c, hc, hkey⟩
  exact le_trans (Finset.card_le_card hsub) Finset.card_image_le

/-- The xz-shadow is dominated by the `+y`-exposed cells. -/
private lemma shadowXZ_le_exposed_posy (A : Finset Cell) :
    (shadowXZ A).card ≤ (exposedIn A (0, 1, 0)).card := by
  have hsub : shadowXZ A
      ⊆ (exposedIn A (0, 1, 0)).image (fun c => (c.1, c.2.2)) := by
    intro p hp
    obtain ⟨c, hc, hkey⟩ := exists_maxy_exposed A p hp
    exact Finset.mem_image.mpr ⟨c, hc, hkey⟩
  exact le_trans (Finset.card_le_card hsub) Finset.card_image_le

/-- The xy-shadow is dominated by the `-z`-exposed cells. -/
private lemma shadowXY_le_exposed_negz (A : Finset Cell) :
    (shadowXY A).card ≤ (exposedIn A (0, 0, -1)).card := by
  have hsub : shadowXY A
      ⊆ (exposedIn A (0, 0, -1)).image (fun c => (c.1, c.2.1)) := by
    intro p hp
    obtain ⟨c, hc, hkey⟩ := exists_minz_exposed A p hp
    exact Finset.mem_image.mpr ⟨c, hc, hkey⟩
  exact le_trans (Finset.card_le_card hsub) Finset.card_image_le

/-- The xy-shadow is dominated by the `+z`-exposed cells. -/
private lemma shadowXY_le_exposed_posz (A : Finset Cell) :
    (shadowXY A).card ≤ (exposedIn A (0, 0, 1)).card := by
  have hsub : shadowXY A
      ⊆ (exposedIn A (0, 0, 1)).image (fun c => (c.1, c.2.1)) := by
    intro p hp
    obtain ⟨c, hc, hkey⟩ := exists_maxz_exposed A p hp
    exact Finset.mem_image.mpr ⟨c, hc, hkey⟩
  exact le_trans (Finset.card_le_card hsub) Finset.card_image_le

/-! ## The shadow bound -/

/-- **[W29-FLOOR, shadow form]** the exposed-face count of any finite
cell set dominates twice its three shadow sizes: each met fiber
contributes its two extreme faces (the shadow-projection pigeonhole of
w29-count §2). -/
theorem perimeter_ge_shadows (A : Finset Cell) :
    2 * (shadowYZ A).card + 2 * (shadowXZ A).card + 2 * (shadowXY A).card
      ≤ perimeter A := by
  rw [perimeter_eq_exposed A]
  have h1 := shadowYZ_le_exposed_negx A
  have h2 := shadowYZ_le_exposed_posx A
  have h3 := shadowXZ_le_exposed_negy A
  have h4 := shadowXZ_le_exposed_posy A
  have h5 := shadowXY_le_exposed_negz A
  have h6 := shadowXY_le_exposed_posz A
  omega

/-- The x-extent is bounded by the xz-shadow (each x-layer appears in
the shadow). -/
theorem xext_le_shadowXZ (A : Finset Cell) : xext A ≤ (shadowXZ A).card := by
  have h : (shadowXZ A).image (fun p => p.1) = A.image (fun c => c.1) := by
    rw [shadowXZ, Finset.image_image]
    exact Finset.image_congr (fun c _ => rfl)
  rw [xext, ← h]
  exact Finset.card_image_le

/-- The x-extent is bounded by the xy-shadow. -/
theorem xext_le_shadowXY (A : Finset Cell) : xext A ≤ (shadowXY A).card := by
  have h : (shadowXY A).image (fun p => p.1) = A.image (fun c => c.1) := by
    rw [shadowXY, Finset.image_image]
    exact Finset.image_congr (fun c _ => rfl)
  rw [xext, ← h]
  exact Finset.card_image_le

/-- A nonempty set meets at least one yz-position. -/
theorem card_shadowYZ_pos (A : Finset Cell) (hne : A.Nonempty) :
    0 < (shadowYZ A).card := by
  obtain ⟨c, hc⟩ := hne
  exact Finset.card_pos.mpr ⟨(c.2.1, c.2.2), Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩

/-- **Theorem W29-FLOOR** (the tube bound, w29-count §2), cell form: a
nonempty finite cell set meeting `e` distinct x-layers has at least
`4e + 2` exposed faces.  Tight: a `d`-tube meets `d` layers and has
exactly `4d + 2` of them. -/
theorem perimeter_ge_of_xext (A : Finset Cell) (hne : A.Nonempty) :
    4 * xext A + 2 ≤ perimeter A := by
  have h0 := perimeter_ge_shadows A
  have h1 := xext_le_shadowXZ A
  have h2 := xext_le_shadowXY A
  have h3 : 0 < (shadowYZ A).card := card_shadowYZ_pos A hne
  omega

/-- **Theorem W29-FLOOR** (crossing form, w29-count §2): a nonempty
finite cell set meeting every x-layer `1, …, d` has at least `4d + 2`
exposed faces — no surface bridging two anchors at x-separation `d` is
smaller (tight: the tube).  The layer-spanning hypothesis is what
connectedness of the bridging surface delivers in the campaign. -/
theorem perimeter_ge_of_layers (A : Finset Cell) (hne : A.Nonempty) (d : ℕ)
    (hmet : ∀ t : ℤ, 1 ≤ t → t ≤ (d : ℤ) → ∃ c ∈ A, c.1 = t) :
    4 * d + 2 ≤ perimeter A := by
  have hsub : Finset.Icc (1 : ℤ) (d : ℤ) ⊆ A.image (fun c => c.1) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    obtain ⟨c, hc, hct⟩ := hmet t ht.1 ht.2
    exact Finset.mem_image.mpr ⟨c, hc, hct⟩
  have hcard : (Finset.Icc (1 : ℤ) (d : ℤ)).card = d := by
    rw [Int.card_Icc]; omega
  have hcardle : d ≤ xext A := by
    rw [xext, ← hcard]
    exact Finset.card_le_card hsub
  have h0 := perimeter_ge_of_xext A hne
  omega

/-! ## Boundary additivity over components (W29-DEC) -/

/-- **Lemma W29-DEC** (germ, w29-count §2): the exposed-face count is
additive over disjoint sets in face-contact with each other NOWHERE —
exactly the situation of two distinct 6-connected components (a boundary
face of one would have its outer cell in the other if they touched,
merging them). -/
theorem perimeter_union (A B : Finset Cell)
    (hno : ∀ a ∈ A, ∀ b ∈ B, ∀ d ∈ dirs, addDir a d ≠ b)
    (hdisj : Disjoint A B) :
    perimeter (A ∪ B) = perimeter A + perimeter B := by
  classical
  have hkey1 : ∀ a ∈ A, ∀ d ∈ dirs, addDir a (negDir d) ∈ B → False := by
    intro a ha d hd hb
    exact hno a ha (addDir a (negDir d)) hb (negDir d) (negDir_mem_dirs hd)
      (by simp only [addDir, negDir])
  have h1 : ∀ c ∈ A, ∀ d ∈ dirs,
      (if addDir c d ∈ A ∪ B then 0 else 1) = (if addDir c d ∈ A then 0 else 1) := by
    intro c hc d hd
    by_cases h : addDir c d ∈ A
    · simp [Finset.mem_union_left _ h, h]
    · have hb : addDir c d ∉ A ∪ B := by
        intro hu
        rcases Finset.mem_union.mp hu with hu | hu
        · exact h hu
        · exact hno c hc (addDir c d) hu d hd rfl
      simp [h, hb]
  have h2 : ∀ c ∈ B, ∀ d ∈ dirs,
      (if addDir c d ∈ A ∪ B then 0 else 1) = (if addDir c d ∈ B then 0 else 1) := by
    intro c hc d hd
    by_cases h : addDir c d ∈ B
    · simp [Finset.mem_union_right _ h, h]
    · have hb : addDir c d ∉ A ∪ B := by
        intro hu
        rcases Finset.mem_union.mp hu with hu | hu
        · exact hno (addDir c d) hu c hc (negDir d) (negDir_mem_dirs hd) (by
            simp only [addDir, negDir]
            have e1 : c.1 + d.1 + -d.1 = c.1 := by omega
            have e2 : c.2.1 + d.2.1 + -d.2.1 = c.2.1 := by omega
            have e3 : c.2.2 + d.2.2 + -d.2.2 = c.2.2 := by omega
            rw [e1, e2, e3])
        · exact h hu
      simp [h, hb]
  simp only [perimeter]
  rw [Finset.sum_union hdisj,
    Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d hd => h1 c hc d hd,
    Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun d hd => h2 c hc d hd]

/-- **Lemma W29-DEC** (additivity, w29-count §2): the exposed-face count
of a finite union of pairwise disjoint, pairwise non-face-contacting
cell sets is the sum of the counts — `|∂W| = Σ_i |∂C_i|` for the
6-connected components `C_i` of `W` (disjoint boundary face sets). -/
theorem perimeter_biUnion {κ : Type*} [DecidableEq κ] (s : Finset κ)
    (C : κ → Finset Cell)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (C i) (C j))
    (hcontact : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a ∈ C i, ∀ b ∈ C j, ∀ d ∈ dirs,
      addDir a d ≠ b) :
    perimeter (s.biUnion C) = ∑ i ∈ s, perimeter (C i) := by
  classical
  have key : ∀ (s : Finset κ),
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (C i) (C j)) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a ∈ C i, ∀ b ∈ C j, ∀ d ∈ dirs,
        addDir a d ≠ b) →
      perimeter (s.biUnion C) = ∑ i ∈ s, perimeter (C i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _ _; simp [perimeter]
    | insert i s hi ih =>
      intro hdisj hcontact
      have hne_ij : ∀ j ∈ s, i ≠ j := fun j hj hcc => hi (hcc ▸ hj)
      have hdisjS : ∀ j ∈ s, ∀ j' ∈ s, j ≠ j' → Disjoint (C j) (C j') :=
        fun j hj j' hj' hcc =>
          hdisj j (Finset.mem_insert_of_mem hj) j' (Finset.mem_insert_of_mem hj') hcc
      have hcontactS : ∀ j ∈ s, ∀ j' ∈ s, j ≠ j' → ∀ a ∈ C j, ∀ b ∈ C j',
          ∀ d ∈ dirs, addDir a d ≠ b :=
        fun j hj j' hj' hcc a hb b hb' d hd =>
          hcontact j (Finset.mem_insert_of_mem hj) j' (Finset.mem_insert_of_mem hj')
            hcc a hb b hb' d hd
      have hdisjU : Disjoint (C i) (s.biUnion C) := by
        refine Finset.disjoint_left.mpr fun a ha hu => ?_
        simp only [Finset.mem_biUnion] at hu
        obtain ⟨j, hj, haj⟩ := hu
        exact Finset.disjoint_left.mp
          (hdisj i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
            (hne_ij j hj)) ha haj
      have hcontactU : ∀ a ∈ C i, ∀ b ∈ s.biUnion C, ∀ d ∈ dirs,
          addDir a d ≠ b := by
        intro a ha b hb d hd
        simp only [Finset.mem_biUnion] at hb
        obtain ⟨j, hj, haj⟩ := hb
        exact hcontact i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
          (hne_ij j hj) a ha b haj d hd
      rw [Finset.biUnion_insert,
        perimeter_union (C i) (s.biUnion C) hcontactU hdisjU,
        ih hdisjS hcontactS, Finset.sum_insert hi]
  exact key s hdisj hcontact

end YangMills3D

/-
The wave-37 volume-class layer: [W37-TREE], Lean form.

SOURCE. `problems/yang-mills-mass-gap/lemmas/w37-mid.md` §2 (Lemma
W37-TREE with the machine Redelmeier certificate 1/6/45/344/2670/...,
and the G25-3 sparse-slice scoping note), reusing `YangMills3D.Animals`
(`Cell`, `dirs`, `addDir`), `YangMills3D.Manifold` (`Reach`, the
6-connected reachability), and Mathlib's Dyck words and Catalan numbers
(`Mathlib.Combinatorics.Enumerative.DyckWord`:
`DyckWord.card_dyckWord_semilength_eq_catalan`).

The campaign's sound volume-class bound: the number of 6-connected
m-cube sets containing a fixed root cell is at most

  `6 · 5^{m−2} · Cat_{m−1}`   (= 1 at m = 1),

the honest replacement of the G23-1-RETRACTED `#classes ≤ 6·5^{v−1}/v`
book (the retracted step omitted exactly the Dyck factor; with it the
per-cube volume-class rate is 20 = 5·4, not 5).  Proof idea
(w37-mid §2): fix a canonical DFS over a spanning tree of the solid,
rooted at the root, children tried in a fixed direction order.  The
(down, up) step pattern is a Dyck excursion — `Cat_{m−1}` of them; the
first descent has 6 direction choices; every LATER descent enters an
UNVISITED neighbour of the current cell, and the tree-parent direction
is already visited, so at most 5 choices — encoded as the RANK of the
chosen direction among the ≤ 5 non-parent directions in the fixed
cyclic order; every ascent is FORCED (it retraces the current subtree
edge).  The visited set of the walk is the solid, so the encoding is
injective.

DELIVERED HERE (all fully proved):

  * `SixConn` — 6-connectedness as `Reach` along the face-adjacency.
  * `DfsShape m` — the DFS-shape alphabet: a Dyck word of semilength
    `m − 1` (the excursion), the ROOT descent direction (`↥dirs`, 6
    choices) and a RANK `Fin (m−2) → Fin 5` for each later descent
    (≤ 5 non-parent directions each).  `card_dfsShape` computes its
    cardinality EXACTLY: `catalan (m−1) · (6 · 5^{m−2})` — the
    unconditional alphabet count.
  * `solidClass_card_le` — the volume-class bound: any FINITE class
    `𝒞` of m-cube solids through `root` that carries an injective
    DFS-shape encoding has `card 𝒞 ≤ catalan (m−1) · (6 · 5^{m−2})`.
    The encoding's injectivity is the named input `hdfs` — exactly the
    w37-mid §2 canonical-DFS argument (visited set = the solid), which
    remains the named Lean formalization work item, in the same
    named-input style as `Manifold.nManifold_le_of_4reg`'s `hEuler`.
  * `solid_one_eq` — the m = 1 corner EXACTLY: the only 1-cube solid
    through `root` is `{root}` (the campaign's "= 1 at m = 1").

PVO-3D: nothing here asserts an unconditional SU(2) statement; per the
G25-3 note this bounds the SPARSE slice (per-volume-class anchored
counts), not the compact slice (the banked exhibit v = 348 > n = 312
exceeds any such volume cap).

Every statement below is fully proved: no unfinished proofs, no new
axioms.
-/
import Mathlib.Combinatorics.Enumerative.DyckWord
import YangMills3D.Animals
import YangMills3D.Manifold

namespace YangMills3D

/-! ## 6-connected solids through a root -/

/-- Face-adjacency of two cells (the 6-neighbour relation). -/
def adj6 (x y : Cell) : Prop := ∃ d ∈ dirs, addDir x d = y

/-- A finite cell set is 6-connected when any two of its cells are
joined by a face-adjacency path inside the set. -/
def SixConn (S : Finset Cell) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, Reach adj6 S u v

/-- The 1-cube corner: a 1-element cell set containing `root` IS the
singleton of `root` — the campaign's "= 1 at m = 1" of [W37-TREE]. -/
theorem solid_one_eq {root : Cell} {S : Finset Cell}
    (hcard : S.card = 1) (hroot : root ∈ S) : S = {root} := by
  obtain ⟨T, hT⟩ := Finset.card_eq_one.mp hcard
  rw [hT, Finset.mem_singleton] at hroot
  rw [← hroot] at hT
  exact hT

/-! ## The DFS-shape alphabet -/

/-- A DFS-shape of a rooted m-cube solid (the encoding alphabet of the
w37-mid §2 canonical-DFS argument): the Dyck excursion of the walk
(semilength `m − 1`: one `U`/`D` pair per solid cell), the ROOT descent
direction (6 choices), and a RANK `Fin (m−2) → Fin 5` — the position,
in a fixed cyclic order, of the chosen direction among the at most 5
non-tree-parent directions at each of the `m − 2` later descents (the
parent is already visited). -/
def DfsShape (m : ℕ) : Type :=
  { p : DyckWord // p.semilength = m - 1 } × (↥dirs × (Fin (m - 2) → Fin 5))

instance dfsShapeFintype (m : ℕ) : Fintype (DfsShape m) := by
  unfold DfsShape
  infer_instance

/-- The cardinality of the DFS-shape alphabet, EXACTLY the campaign's
`Cat_{m−1} · 6 · 5^{m−2}` (unconditional): Dyck excursions of
semilength `m − 1` are counted by the Catalan number
(Mathlib's `DyckWord.DyckWord.card_dyckWord_semilength_eq_catalan`), directions
by 6, ranks by `5^{m−2}`. -/
theorem card_dfsShape (m : ℕ) :
    Fintype.card (DfsShape m) = catalan (m - 1) * (6 * 5 ^ (m - 2)) := by
  unfold DfsShape
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_coe, card_dirs,
    Fintype.card_pi_const, Fintype.card_fin, DyckWord.card_dyckWord_semilength_eq_catalan]

/-! ## The volume-class bound -/

/-- **Lemma W37-TREE** (w37-mid §2), the sound volume-class bound for a
finite subclass: a finite class `𝒞` of m-cube solids through `root`
that carries an INJECTIVE DFS-shape encoding (the canonical-DFS map of
w37-mid §2 — the walk's visited set is the solid — the named Lean
formalization input `hdfs`, in the `hEuler` style of
`Manifold.nManifold_le_of_4reg`) has

  `card 𝒞 ≤ catalan (m−1) · (6 · 5^{m−2})`,

i.e. per-volume-class anchored count ≤ `6 · 5^{m−2} · Cat_{m−1}` with
per-cube rate 20 (the honest replacement of the G23-1-RETRACTED
5-book). -/
theorem solidClass_card_le {_root : Cell} {m : ℕ} (𝒞 : Finset (Finset Cell))
    (hdfs : ∃ f : Finset Cell → DfsShape m, ∀ S ∈ 𝒞, ∀ T ∈ 𝒞, f S = f T → S = T) :
    𝒞.card ≤ catalan (m - 1) * (6 * 5 ^ (m - 2)) := by
  obtain ⟨f, hf⟩ := hdfs
  have hinj : Function.Injective (fun S : {x // x ∈ 𝒞} => f S) := by
    intro a b hab
    exact Subtype.ext (hf (a : Finset Cell) a.prop (b : Finset Cell) b.prop hab)
  have h1 : Fintype.card {x // x ∈ 𝒞}
      ≤ Fintype.card (DfsShape m) :=
    Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_coe, card_dfsShape] at h1
  exact h1

end YangMills3D

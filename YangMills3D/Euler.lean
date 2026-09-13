/-
The abstract walk-counting layer of wave 31: infrastructure toward
W31-FAN (the manifold-surface fan), Lean form.

SOURCE. `problems/yang-mills-mass-gap/lemmas/w31-encode.md` §1 (Lemma
W31-REG: the face graph of a manifold polymer is connected and
4-regular, hence Eulerian; Theorem W31-FAN: every rooted directed
Euler circuit is determined by <= 4 · 2 · 3^{n-1} discipline choices).

DELIVERED HERE (all fully proved):

  * `wEdges`, `WalkOn`, `Simple`, `ClosedAt`, `Covers` — the walk
    vocabulary.  Edges are the consecutive pairs of a vertex list,
    compared UP TO SWAP (`UndEq`); simplicity is List.Pairwise over the
    traversed pairs; walk-ness carries the F-membership and the
    edge-level adjacency/nondegeneracy.
  * `incCount s D` — the number of edges of a pair list incident to
    `s`, with the cons-recursion `incCount_cons`.
  * `card_usedNbrs_eq_incCount` — the COUNTING BRIDGE: for a simple
    walk, the used neighbors of a vertex `s` number exactly the edges
    of the walk incident to `s` (simplicity makes the "other endpoint"
    map injective on the incident edges) — the wave-31 analogue of the
    wave-29 shadow-projection pigeonhole.
  * `card_usedNbrs_of_X_eq` — the bridge for a walk plus an extra pair
    set `X` with pairwise UndEq-distinct pairs (the input shape of the
    splice step of Euler's existence argument).
  * `mem_usedNbrs_union`, `card_used_add_unused` — used/unused
    neighborhood bookkeeping over unions.

STILL PENDING (the remainder of W31-FAN, not formalized here): the
endpoint-parity lemma (for a closed edge-simple walk, incCount = 2
per vertex; blocks the proof that a stuck walk is closed), Euler's
existence theorem (maximality + splice on the parity lemma), the
discipline encoding `Enc = nbrs r × Fin 2 × (F \ {r} → Fin 3)` with
its greedy decode/reproduction, the count
`#closed simple walks ≤ 4 · 2 · 3^{n-1}`, and the manifold-side
wrapper deriving N_manifold(p₀, n) ≤ (8/3)·3ⁿ unconditionally.

Every statement below is fully proved: no unfinished proofs, no new
axioms.
-/import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic

namespace YangMills3D

/-! ## Undirected edges -/

/-- Undirected equality of two traversed pairs: same edge, either
orientation. -/
def UndEq {V : Type*} (e e' : V × V) : Prop :=
  (e.1 = e'.1 ∧ e.2 = e'.2) ∨ (e.1 = e'.2 ∧ e.2 = e'.1)

theorem UndEq_refl {V : Type*} (e : V × V) : UndEq e e :=
  Or.inl ⟨rfl, rfl⟩

theorem UndEq_symm {V : Type*} {e e' : V × V} (h : UndEq e e') : UndEq e' e := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h2.symm, h1.symm⟩

theorem UndEq_symm_iff {V : Type*} {e e' : V × V} : UndEq e e' ↔ UndEq e' e :=
  ⟨UndEq_symm, UndEq_symm⟩

/-- An undirected edge is determined by its two endpoints in order. -/
theorem UndEq_of_eq {V : Type*} {e e' : V × V} (h1 : e.1 = e'.1) (h2 : e.2 = e'.2) :
    UndEq e e' :=
  Or.inl ⟨h1, h2⟩

/-! ## Walks over a finite vertex set with an adjacency -/

section Graph
variable {V : Type*} [DecidableEq V] (adj : V → V → Prop) [DecidableRel adj] (F : Finset V)

/-- Traversed-pair list of a walk: the consecutive pairs. -/
def wEdges (l : List V) : List (V × V) := l.zip l.tail

theorem wEdges_cons_cons (a b : V) (t : List V) :
    wEdges (a :: b :: t) = (a, b) :: wEdges (b :: t) := rfl

theorem wEdges_length (l : List V) (hl : l ≠ []) :
    (wEdges l).length + 1 = l.length := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a t ih =>
    match t with
    | [] => simp [wEdges]
    | b :: t' =>
      have h1 := ih (by simp)
      rw [wEdges_cons_cons, List.length_cons, List.length_cons]
      omega

theorem wEdges_length_eq (l : List V) (hl : l ≠ []) :
    (wEdges l).length = l.length - 1 := by
  have := wEdges_length l hl
  omega

/-- Index validity inside `wEdges`. -/
theorem wEdges_index_valid {l : List V} {i : ℕ} (hi : i + 1 < l.length) :
    i < (wEdges l).length := by
  have h1 := wEdges_length l (fun h => by rw [h] at hi; simp at hi)
  have h2 : (l.zip l.tail).length + 1 = l.length := h1
  simp only [List.length_zip, List.length_tail] at h2
  omega

/-- The edge at position `i` of a walk is the pair of consecutive
vertices. -/
theorem wEdges_getElem {l : List V} {i : ℕ} (hi : i + 1 < l.length) :
    (wEdges l)[i]'(wEdges_index_valid hi) = (l[i]'(by omega), l[i + 1]'(by omega)) := by
  have hidx : i < (l.zip l.tail).length := wEdges_index_valid hi
  have h1 : (l.zip l.tail)[i]'hidx
      = (l[i]'(by omega), (l.tail)[i]'(by simp only [List.length_tail]; omega)) :=
    List.getElem_zip (h := hidx)
  refine h1.trans ?_
  congr 1
  exact List.getElem_tail (by simp only [List.length_tail]; omega)

theorem wEdges_length_pos {l : List V} (h1 : 1 < l.length) : 0 < (wEdges l).length := by
  have h := wEdges_length l (fun h => by rw [h] at h1; simp at h1)
  omega

/-- The vertices of the edge list are the walk's vertices. -/
theorem wEdges_fst_snd_mem : ∀ (l : List V) {e : V × V}, e ∈ wEdges l → e.1 ∈ l ∧ e.2 ∈ l := by
  intro l
  induction l with
  | nil => intro e he; cases he
  | cons a t ih =>
    match t with
    | [] => intro e he; simp [wEdges] at he
    | b :: t' =>
      intro e he
      rw [wEdges_cons_cons, List.mem_cons] at he
      rcases he with rfl | he'
      · exact ⟨by simp, by simp⟩
      · obtain ⟨h1, h2⟩ := ih he'
        exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

theorem wEdges_fst_mem {l : List V} {e : V × V} (he : e ∈ wEdges l) : e.1 ∈ l ∧ e.2 ∈ l :=
  wEdges_fst_snd_mem l he

/-- Walk on `F`: a nonempty vertex list staying in `F` whose consecutive
pairs (the edges of `wEdges`) are adjacent, in `F`, and nondegenerate. -/
def WalkOn (l : List V) : Prop :=
  l ≠ [] ∧ (∀ x ∈ l, x ∈ F) ∧
    ∀ e ∈ wEdges l, e.1 ∈ F ∧ e.2 ∈ F ∧ adj e.1 e.2 ∧ e.1 ≠ e.2

/-- The head of a walk lies in the walk. -/
theorem head_mem_of_ne {l : List V} (hl : l ≠ []) : l.head (hl) ∈ l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => simp

/-- The last vertex of a walk lies in the walk. -/
theorem getLast_mem_of_ne {l : List V} (hl : l ≠ []) : l.getLast hl ∈ l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => simp

/-- Every edge of a walk has distinct endpoints (via irreflexivity). -/
theorem walk_edge_ne {l : List V} (hirrefl : ∀ v : V, ¬ adj v v)
    (h : WalkOn adj F l) {e : V × V} (he : e ∈ wEdges l) : e.1 ≠ e.2 := by
  have hb := h.2.2 e he
  intro hcon
  rw [hcon] at hb
  exact hirrefl _ hb.2.2.1

/-- Closed walk based at `r`. -/
def ClosedAt (r : V) (l : List V) : Prop := l.head? = some r ∧ l.getLast? = some r

theorem head?_mem {l : List V} {r : V} (h : l.head? = some r) : r ∈ l := by
  cases l with
  | nil => simp at h
  | cons a t =>
    have h2 : a = r := by simpa using h
    simp [h2]

theorem getLast?_mem : ∀ (l : List V) {r : V}, l.getLast? = some r → r ∈ l := by
  intro l
  induction l with
  | nil => intro r h; simp at h
  | cons a t ih =>
    intro r h
    match t with
    | [] =>
      have h2 : a = r := by simpa using h
      simp [h2]
    | b :: t' => exact List.mem_cons_of_mem _ (ih h)

theorem ClosedAt.mem_head {r : V} {l : List V} (h : ClosedAt r l) : r ∈ l :=
  head?_mem h.1

theorem ClosedAt.mem_getLast {r : V} {l : List V} (h : ClosedAt r l) : r ∈ l :=
  getLast?_mem l h.2

/-- The walk covers every undirected edge of `F` (pair-membership form;
no index proofs). -/
def Covers (l : List V) : Prop :=
  ∀ u w : V, u ∈ F → adj u w → ∃ e ∈ wEdges l, e = (u, w) ∨ e = (w, u)

/-- Membership of a traversed pair in the used-edge set, up to swap. -/
def isUsed (U : Finset (V × V)) (v w : V) : Prop := (v, w) ∈ U ∨ (w, v) ∈ U

/-- Simple walk: no undirected edge traversed twice (Pairwise over the
traversed pairs). -/
def Simple (l : List V) : Prop := (wEdges l).Pairwise (fun e e' => ¬ UndEq e e')

/-- Simplicity in value form: any two traversed pairs that are
undirected-equal coincide. -/
theorem simple_values : ∀ (l : List V), Simple l →
    ∀ e ∈ wEdges l, ∀ e' ∈ wEdges l, UndEq e e' → e = e' := by
  intro l
  induction l with
  | nil => intro _ e he; simp [wEdges] at he
  | cons a t ih =>
    match t with
    | [] => intro _ e he; simp [wEdges] at he
    | b :: t' =>
      intro h e he e' he' hUnd
      rw [wEdges_cons_cons] at he he'
      rw [Simple, wEdges_cons_cons, List.pairwise_cons] at h
      rcases List.mem_cons.mp he with rfl | hed
      · rcases List.mem_cons.mp he' with rfl | hed'
        · rfl
        · exact absurd hUnd (h.1 e' hed')
      · rcases List.mem_cons.mp he' with rfl | hed'
        · exact absurd (UndEq_symm hUnd) (h.1 e hed)
        · exact ih h.2 e hed e' hed' hUnd

/-- The head of a nonempty prefix is the head of the list. -/
theorem take_head? (t : List V) (k : ℕ) (hk : 0 < k) :
    (t.take k).head? = t.head? := by
  cases k with
  | zero => omega
  | succ y =>
    cases t with
    | nil => simp
    | cons x xs => rfl

/-- Edges of the tail are edges of the full walk. -/
theorem wEdges_cons_mem {a : V} {t : List V} (ht : t ≠ []) {e : V × V}
    (he : e ∈ wEdges t) : e ∈ wEdges (a :: t) := by
  cases t with
  | nil => exact absurd rfl ht
  | cons x xs =>
    rw [wEdges_cons_cons, List.mem_cons]
    exact Or.inr he


/-- Edges of a prefix are edges of the walk. -/
theorem wEdges_take_mem : ∀ (l : List V) (k : ℕ) {e : V × V},
    e ∈ wEdges (l.take k) → e ∈ wEdges l := by
  intro l
  induction l with
  | nil => intro k e he; simp [wEdges] at he
  | cons a t ih =>
    intro k e he
    match k with
    | 0 => simp [wEdges] at he
    | k' + 1 =>
      rw [show (a :: t).take (k' + 1) = a :: t.take k' from rfl] at he
      cases ht : t.take k' with
      | nil => rw [ht] at he; simp [wEdges] at he
      | cons c s =>
        rw [ht] at he
        rw [wEdges_cons_cons, List.mem_cons] at he
        rcases he with heq | he'
        · -- e = (a, c); c is the head of t
          rw [heq]
          have htne' : t ≠ [] := fun hcon => by rw [hcon] at ht; simp at ht
          have hk' : 0 < k' := by
            cases k' with
            | zero => exact absurd ht (by simp [List.take_zero])
            | succ m => omega
          have h1 : (t.take k').head? = some c := by rw [ht]; simp
          have h2 := take_head? t k' hk'
          rw [h1] at h2
          cases t with
          | nil => exact absurd htne' (by simp)
          | cons x xs =>
            have h3 : c = x := by simpa using h2
            rw [wEdges_cons_cons, List.mem_cons]
            exact Or.inl (by simpa using h3)
        · rw [← ht] at he'
          have htne' : t ≠ [] := fun hcon => by rw [hcon] at ht; simp at ht
          exact wEdges_cons_mem htne' (ih k' he')

/-- Simplicity passes to prefixes. -/
theorem Simple.take : ∀ (l : List V) (k : ℕ), Simple l → Simple (l.take k) := by
  intro l
  induction l with
  | nil => intro k _; simp [Simple, wEdges]
  | cons a t ih =>
    intro k h
    match k with
    | 0 => simp [Simple, wEdges]
    | k' + 1 =>
      rw [show (a :: t).take (k' + 1) = a :: t.take k' from rfl]
      match t with
      | [] => rw [List.take_nil]; exact h
      | b :: t' =>
        rw [Simple, wEdges_cons_cons, List.pairwise_cons] at h
        cases ht' : (b :: t').take k' with
        | nil =>
          simp [Simple, wEdges]
        | cons c s =>
          have hbc : c = b := by
            have h1 : ((b :: t').take k').head? = some c := by rw [ht']; simp
            have h2 := take_head? (b :: t') k' (by
              cases k' with
              | zero => rw [List.take_zero] at ht'; simp at ht'
              | succ m => omega)
            rw [h1] at h2
            simpa using h2
          rw [Simple, wEdges_cons_cons, List.pairwise_cons]
          refine ⟨fun e he => ?_, ?_⟩
          · rw [← ht'] at he
            have he' := wEdges_take_mem (b :: t') k' he
            have hne := h.1 e he'
            rw [← hbc] at hne
            exact hne
          · have hs := ih k' h.2
            rwa [ht'] at hs

theorem mem_wEdges_getElem {l : List V} {i : ℕ} (hi : i + 1 < l.length) :
    (l[i], l[i + 1]) ∈ wEdges l := by
  rw [show (l[i], l[i + 1]) = (wEdges l)[i]'(wEdges_index_valid hi) from
    (wEdges_getElem hi).symm]
  exact List.getElem_mem (wEdges_index_valid hi)

/-- The neighbors of `v` inside `F` (the degree-4 sets of W31-REG). -/
def nbrs (v : V) : Finset V := F.filter (adj v)

theorem mem_nbrs {v w : V} : w ∈ nbrs adj F v ↔ w ∈ F ∧ adj v w := by
  simp [nbrs]

instance isUsed_decidable (U : Finset (V × V)) (v w : V) :
    Decidable (isUsed U v w) :=
  inferInstanceAs (Decidable ((v, w) ∈ U ∨ (w, v) ∈ U))

/-- The already-used neighbors of `v`. -/
def usedNbrs (U : Finset (V × V)) (v : V) : Finset V :=
  (nbrs adj F v).filter (fun w => isUsed U v w)

/-- The not-yet-used neighbors of `v`. -/
def unusedNbrs (U : Finset (V × V)) (v : V) : Finset V :=
  (nbrs adj F v).filter (fun w => ¬ isUsed U v w)

theorem mem_unusedNbrs {U : Finset (V × V)} {v w : V} :
    w ∈ unusedNbrs adj F U v ↔ (w ∈ F ∧ adj v w) ∧ ¬ isUsed U v w := by
  constructor
  · intro hw
    have h1 : w ∈ nbrs adj F v ∧ ¬ isUsed U v w := Finset.mem_filter.mp hw
    have h2 := Iff.mp (mem_nbrs adj F) h1.1
    exact ⟨h2, h1.2⟩
  · rintro ⟨hpair, hne⟩
    have h2 := Iff.mpr (mem_nbrs adj F) hpair
    exact Finset.mem_filter.mpr ⟨h2, hne⟩

theorem mem_usedNbrs {U : Finset (V × V)} {v w : V} :
    w ∈ usedNbrs adj F U v ↔ (w ∈ F ∧ adj v w) ∧ isUsed U v w := by
  constructor
  · intro hw
    have h1 : w ∈ nbrs adj F v ∧ isUsed U v w := Finset.mem_filter.mp hw
    have h2 := Iff.mp (mem_nbrs adj F) h1.1
    exact ⟨h2, h1.2⟩
  · rintro ⟨hpair, hne⟩
    have h2 := Iff.mpr (mem_nbrs adj F) hpair
    exact Finset.mem_filter.mpr ⟨h2, hne⟩

/-- The used and unused neighbors of `v` partition `nbrs v`. -/
theorem card_used_add_unused (U : Finset (V × V)) (v : V) :
    (usedNbrs adj F U v).card + (unusedNbrs adj F U v).card = (nbrs adj F v).card := by
  have hd : Disjoint (usedNbrs adj F U v) (unusedNbrs adj F U v) := by
    refine Finset.disjoint_left.mpr fun w hw hw' => ?_
    simp only [usedNbrs, Finset.mem_filter] at hw
    simp only [unusedNbrs, Finset.mem_filter] at hw'
    exact hw'.2 hw.2
  have hu : usedNbrs adj F U v ∪ unusedNbrs adj F U v = nbrs adj F v := by
    ext w
    simp only [Finset.mem_union, usedNbrs, Finset.mem_filter, unusedNbrs]
    by_cases h : isUsed U v w <;> simp [h]
  rw [← hu, Finset.card_union_of_disjoint hd]

/-! ## The counting bridge: used neighbors vs incident edge positions -/

/-- The number of edges of the pair list `D` incident to `s`. -/
def incCount (s : V) (D : List (V × V)) : ℕ :=
  (D.filter (fun e => s = e.1 ∨ s = e.2)).length

theorem incCount_cons (s : V) (e : V × V) (D : List (V × V)) :
    incCount s (e :: D)
      = (if s = e.1 ∨ s = e.2 then 1 else 0) + incCount s D := by
  classical
  simp only [incCount, List.filter_cons]
  split
  · rw [List.length_cons]
    split
    · omega
    · simp_all
  · split
    · simp_all
    · omega

theorem incCount_nil (s : V) : incCount s ([] : List (V × V)) = 0 := rfl

/-- The tail of a walk is a walk. -/
theorem WalkOn.tail {a : V} {l : List V} (h : WalkOn adj F (a :: l)) (hl : l ≠ []) :
    WalkOn adj F l := by
  refine ⟨hl, fun x hx => h.2.1 x (List.mem_cons_of_mem _ hx), ?_⟩
  intro e he
  exact h.2.2 e (by
    cases l with
    | nil => exact absurd rfl hl
    | cons b t' => rw [wEdges_cons_cons, List.mem_cons]; exact Or.inr he)

/-- The edge list of a simple walk has no repeated pairs. -/
theorem wEdges_nodup {l : List V} (hsimple : Simple l) : (wEdges l).Nodup := by
  have h := hsimple
  refine List.Pairwise.imp ?_ h
  intro x y hne hcon
  rw [hcon] at hne
  exact hne (UndEq_refl y)

/-- **Counting bridge**: the used neighbors of `s` number exactly the
edges of a simple walk incident to `s` (simplicity makes the
"other endpoint" map injective on the incident edges). -/
theorem card_usedNbrs_eq_incCount {l : List V} (hwalk : WalkOn adj F l)
    (hsimple : Simple l) (hsymm : ∀ x y : V, adj x y → adj y x) (s : V) :
    (usedNbrs adj F (wEdges l).toFinset s).card = incCount s (wEdges l) := by
  classical
  have hset : usedNbrs adj F (wEdges l).toFinset s
      = (((wEdges l).filter (fun (e : V × V) => s = e.1 ∨ s = e.2)).map
          (fun (e : V × V) => if s = e.1 then e.2 else e.1)).toFinset := by
    ext w
    constructor
    · intro hw
      rcases Iff.mp (mem_usedNbrs adj F) hw with ⟨⟨hF, hadj⟩, hused⟩
      have h2 : (s, w) ∈ (wEdges l).toFinset ∨ (w, s) ∈ (wEdges l).toFinset := hused
      rcases h2 with h | h
      · have hDmem : (s, w) ∈ wEdges l := List.mem_toFinset.mp h
        refine List.mem_toFinset.mpr ?_
        rw [List.mem_map]
        refine ⟨(s, w), List.mem_filter.mpr ⟨hDmem, by simp⟩, ?_⟩
        show (if s = (s, w).1 then (s, w).2 else (s, w).1) = w
        rw [if_pos rfl]
      · have hDmem : (w, s) ∈ wEdges l := List.mem_toFinset.mp h
        have hne : w ≠ s := by
          have hwE := hwalk.2.2 (w, s) hDmem
          exact fun hcon => hwE.2.2.2 hcon
        refine List.mem_toFinset.mpr ?_
        rw [List.mem_map]
        refine ⟨(w, s), List.mem_filter.mpr ⟨hDmem, by simp⟩, ?_⟩
        show (if s = (w, s).1 then (w, s).2 else (w, s).1) = w
        rw [if_neg (fun hcon => hne hcon.symm)]
    · intro hw
      have hw' := List.mem_toFinset.mp hw
      rw [List.mem_map] at hw'
      obtain ⟨e, heO, hfe⟩ := hw'
      rw [List.mem_filter] at heO
      obtain ⟨heD, hor⟩ := heO
      simp at hor
      obtain ⟨hF1, hF2, hadj, hneE⟩ := hwalk.2.2 e heD
      have hfe' : (if s = e.1 then e.2 else e.1) = w := hfe
      rcases hor with hor | hor
      · subst hor
        rw [if_pos rfl] at hfe'
        have hwE : w = e.2 := hfe'.symm
        subst hwE
        exact Iff.mpr (mem_usedNbrs adj F) ⟨⟨hF2, hadj⟩, Or.inl (List.mem_toFinset.mpr heD)⟩
      · have hne1 : ¬ (s = e.1) := fun hc => hneE (hc.symm.trans hor)
        rw [if_neg hne1] at hfe'
        have hwE : w = e.1 := hfe'.symm
        subst hwE
        subst hor
        exact Iff.mpr (mem_usedNbrs adj F) ⟨⟨hF1, hsymm e.1 e.2 hadj⟩, Or.inr (List.mem_toFinset.mpr heD)⟩
  have hDnodup : (wEdges l).Nodup := wEdges_nodup hsimple
  have hOnodup : ((wEdges l).filter (fun e => s = e.1 ∨ s = e.2)).Nodup :=
    List.Nodup.filter _ hDnodup
  have hOmap : (((wEdges l).filter (fun e => s = e.1 ∨ s = e.2)).map
      (fun e => if s = e.1 then e.2 else e.1)).Nodup := by
    refine List.Nodup.map_on ?_ hOnodup
    intro x hx y hy hfeq
    have hxD : x ∈ wEdges l := List.mem_of_mem_filter hx
    have hyD : y ∈ wEdges l := List.mem_of_mem_filter hy
    have hneX : x.1 ≠ x.2 := (hwalk.2.2 x hxD).2.2.2
    have hneY : y.1 ≠ y.2 := (hwalk.2.2 y hyD).2.2.2
    by_cases hcon : x = y
    · exact hcon
    · exfalso
      have horx : s = x.1 ∨ s = x.2 := by
        have hb := (List.mem_filter.mp hx).2
        simp at hb
        exact hb
      have hory : s = y.1 ∨ s = y.2 := by
        have hb := (List.mem_filter.mp hy).2
        simp at hb
        exact hb
      rcases horx with horx | horx
      · rcases hory with hory | hory
        · rw [if_pos horx, if_pos hory] at hfeq
          exact hcon (simple_values l hsimple x hxD y hyD
            (UndEq_of_eq (horx.symm.trans hory) hfeq))
        · rw [if_pos horx, if_neg (fun hc => hneY (hc.symm.trans hory))] at hfeq
          exact hcon (simple_values l hsimple x hxD y hyD
            (Or.inr ⟨horx.symm.trans hory, hfeq⟩))
      · rcases hory with hory | hory
        · rw [if_neg (fun hc => hneX (hc.symm.trans horx)), if_pos hory] at hfeq
          exact hcon (simple_values l hsimple x hxD y hyD
            (Or.inr ⟨hfeq, horx.symm.trans hory⟩))
        · rw [if_neg (fun hc => hneX (hc.symm.trans horx)),
            if_neg (fun hc => hneY (hc.symm.trans hory))] at hfeq
          exact hcon (simple_values l hsimple x hxD y hyD
            (UndEq_of_eq hfeq (horx.symm.trans hory)))
  have hnod : (((wEdges l).filter (fun (e : V × V) => s = e.1 ∨ s = e.2)).map
      (fun (e : V × V) => if s = e.1 then e.2 else e.1)).Nodup := hOmap
  have hcard : (((wEdges l).filter (fun (e : V × V) => s = e.1 ∨ s = e.2)).map
      (fun (e : V × V) => if s = e.1 then e.2 else e.1)).toFinset.card
      = (((wEdges l).filter (fun (e : V × V) => s = e.1 ∨ s = e.2)).map
      (fun (e : V × V) => if s = e.1 then e.2 else e.1)).length := by
    exact List.toFinset_card_of_nodup hnod
  rw [hset, hcard, List.length_map]
  rfl

/-! ## Endpoint parity: a stuck walk is closed -/

/-- Membership in the used neighbors of a union splits. -/
theorem mem_usedNbrs_union {U X : Finset (V × V)} {v w : V} :
    w ∈ usedNbrs adj F (U ∪ X) v ↔ w ∈ usedNbrs adj F U v ∨ w ∈ usedNbrs adj F X v := by
  rw [mem_usedNbrs, mem_usedNbrs, mem_usedNbrs]
  simp only [Finset.mem_union, isUsed]
  tauto

/-- The used neighbors of `s` w.r.t. a pair set `X` number exactly the
edges of `X` incident to `s` (for `X` whose pairs are pairwise
UndEq-distinct). -/
theorem card_usedNbrs_of_X_eq {X : Finset (V × V)} (s : V)
    (hsymm : ∀ x y : V, adj x y → adj y x)
    (hXmem : ∀ e ∈ X, e.1 ∈ F ∧ e.2 ∈ F ∧ adj e.1 e.2) :
    (usedNbrs adj F X s).card
      = ((X.filter (fun (e : V × V) => s = e.1 ∨ s = e.2)).image
          (fun (e : V × V) => if s = e.1 then e.2 else e.1)).card := by
  classical
  have hset : usedNbrs adj F X s
      = (X.filter (fun (e : V × V) => s = e.1 ∨ s = e.2)).image
          (fun (e : V × V) => if s = e.1 then e.2 else e.1) := by
    ext w
    constructor
    · intro hw
      have hw' : (w ∈ F ∧ adj s w) ∧ isUsed X s w := Iff.mp (mem_usedNbrs adj F) hw
      obtain ⟨hF, hadj⟩ := hw'.1
      have h2 : (s, w) ∈ X ∨ (w, s) ∈ X := hw'.2
      rcases h2 with h | h
      · refine Finset.mem_image.mpr ⟨(s, w), Finset.mem_filter.mpr ⟨h, ?_⟩, ?_⟩
        · simp
        · show (if s = (s, w).1 then (s, w).2 else (s, w).1) = w
          rw [if_pos rfl]
      · refine Finset.mem_image.mpr ⟨(w, s), Finset.mem_filter.mpr ⟨h, ?_⟩, ?_⟩
        · simp
        · show (if s = (w, s).1 then (w, s).2 else (w, s).1) = w
          by_cases hsw : s = w
          · subst hsw
            simp
          · rw [if_neg hsw]
    · intro hw
      obtain ⟨e, heX, hfe⟩ := Finset.mem_image.mp hw
      obtain ⟨heXin, hor⟩ := Finset.mem_filter.mp heX
      obtain ⟨hF1, hF2, hadj⟩ := hXmem e heXin
      have hfe' : (if s = e.1 then e.2 else e.1) = w := hfe
      rcases hor with hor | hor
      · rw [if_pos hor] at hfe'
        have hwE : w = e.2 := hfe'.symm
        subst hwE
        have hadj' : adj s e.2 := by rw [hor]; exact hadj
        have hmem' : (s, e.2) ∈ X := by rw [hor]; exact heXin
        exact Iff.mpr (mem_usedNbrs adj F) ⟨⟨hF2, hadj'⟩, Or.inl hmem'⟩
      · split at hfe'
        · rename_i hs1
          have hwE : w = e.2 := hfe'.symm
          subst hwE
          have hadj' : adj s e.2 := by rw [hs1]; exact hadj
          have hmem' : (s, e.2) ∈ X := by rw [hs1]; exact heXin
          refine Iff.mpr (mem_usedNbrs adj F) ⟨⟨hF2, hadj'⟩, Or.inl hmem'⟩
        · rename_i hs1
          have hwE : w = e.1 := hfe'.symm
          subst hwE
          have hadj' : adj s e.1 := by rw [hor]; exact hsymm e.1 e.2 hadj
          have hmem' : (e.1, s) ∈ X := by rw [hor]; exact heXin
          refine Iff.mpr (mem_usedNbrs adj F) ⟨⟨hF1, hadj'⟩, Or.inr hmem'⟩
  rw [hset]
/-- The visit count of `s` in a vertex list. -/
def occ (s : V) (l : List V) : ℕ := (l.filter (fun x => x = s)).length

theorem occ_nil (s : V) : occ s ([] : List V) = 0 := rfl

theorem occ_cons (s a : V) (l : List V) :
    occ s (a :: l) = (if a = s then 1 else 0) + occ s l := by
  classical
  simp only [occ, List.filter_cons]
  split
  · rw [List.length_cons]
    split
    · omega
    · simp_all
  · split
    · simp_all
    · omega

end Graph

end YangMills3D

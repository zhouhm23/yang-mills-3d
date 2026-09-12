/-
The animal-entropy layer: W24-S (the wave-24 impossibility), Lean form.

SOURCE. `problems/yang-mills-mass-gap/lemmas/w24-cold.md` §1 (the hole
construction) and `lemmas/w25-cluster.md` (W25-N2). The campaign's W23-Q
criterion `A(z) = Σ_P a_P z^P < 1` (an exponential animal-entropy tail
`a_P ≤ C·c^P`) was falsified by the box-with-holes construction; this file
machine-checks that construction for the FACE-perimeter index:

  an `s`-box minus `k` holes (an arbitrary subset of the even-parity
  interior core — pairwise non-adjacency is automatic by parity) has
  face-perimeter EXACTLY `perimeter (box s) + 6·k`, with the exact value
  `perimeter (box s) = 6·s²` computed in the campaign (only the quadratic
  bound `≤ 12·s²` is needed and proved here).

Counts in `Entropy.lean` are over ALL finite cell subsets of the box (a
superset of the connected solid animals), which makes the impossibility
results STRONGER than the campaign's statement.
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace YangMills3D

/-! ## Lattice data -/

/-- Cells of the cubic lattice as integer triples. -/
abbrev Cell := ℤ × ℤ × ℤ

/-- The six unit directions of the cubic lattice. -/
def dirs : Finset Cell :=
  ({(-1, 0, 0), (1, 0, 0), (0, -1, 0), (0, 1, 0), (0, 0, -1), (0, 0, 1)} : Finset Cell)

theorem card_dirs : dirs.card = 6 := by
  simp only [dirs]
  decide

theorem dirs_cases {d : Cell} (hd : d ∈ dirs) :
    d = (-1, 0, 0) ∨ d = (1, 0, 0) ∨ d = (0, -1, 0) ∨ d = (0, 1, 0)
      ∨ d = (0, 0, -1) ∨ d = (0, 0, 1) := by
  simp only [dirs, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem dirs_bdd {d : Cell} (hd : d ∈ dirs) :
    (d.1 = -1 ∨ d.1 = 0 ∨ d.1 = 1) ∧ (d.2.1 = -1 ∨ d.2.1 = 0 ∨ d.2.1 = 1)
      ∧ (d.2.2 = -1 ∨ d.2.2 = 0 ∨ d.2.2 = 1) := by
  rcases dirs_cases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem dirs_axis {d : Cell} (hd : d ∈ dirs) :
    (d.1 ≠ 0 ∧ d.2.1 = 0 ∧ d.2.2 = 0) ∨ (d.2.1 ≠ 0 ∧ d.1 = 0 ∧ d.2.2 = 0)
      ∨ (d.2.2 ≠ 0 ∧ d.1 = 0 ∧ d.2.1 = 0) := by
  rcases dirs_cases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- Componentwise negation of a direction. -/
def negDir (d : Cell) : Cell := (-d.1, -d.2.1, -d.2.2)

theorem negDir_mem_dirs {d : Cell} (hd : d ∈ dirs) : negDir d ∈ dirs := by
  rcases dirs_cases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [negDir, dirs]

/-- Componentwise translation of a cell by a direction. -/
def addDir (x d : Cell) : Cell := (x.1 + d.1, x.2.1 + d.2.1, x.2.2 + d.2.2)

theorem addDir_eq_iff (x d h : Cell) : addDir x d = h ↔ x = addDir h (negDir d) := by
  simp only [addDir, negDir, Prod.ext_iff]
  constructor <;> intro hh <;> omega

/-! ## Face-perimeter -/

/-- The face-perimeter of a finite cell set: the number of exposed faces,
`#{(x, d) : x ∈ A, d ∈ dirs, x + d ∉ A}` (the face form of W25-N1's
`P = 6n - 2e`). A double indicator sum, decidable by construction. -/
def perimeter (A : Finset Cell) : ℕ :=
  ∑ x ∈ A, ∑ d ∈ dirs, (if addDir x d ∈ A then 0 else 1)

theorem perimeter_le (A : Finset Cell) : perimeter A ≤ 6 * A.card := by
  have h : ∀ x ∈ A, ∑ d ∈ dirs, (if addDir x d ∈ A then 0 else 1) ≤ 6 := by
    intro x _
    calc ∑ d ∈ dirs, (if addDir x d ∈ A then 0 else 1)
        ≤ ∑ d ∈ dirs, 1 := Finset.sum_le_sum (fun d _ => by split <;> omega)
      _ = 6 := by simp [Finset.sum_const, card_dirs]
  calc perimeter A = ∑ x ∈ A, ∑ d ∈ dirs, (if addDir x d ∈ A then 0 else 1) := rfl
    _ ≤ ∑ x ∈ A, 6 := Finset.sum_le_sum (fun x hx => h x hx)
    _ = 6 * A.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-! ## Boxes and the even core -/

/-- The `s`-box `[1,s]³` as a finite set of cells. -/
def box (s : ℕ) : Finset Cell :=
  Finset.Icc (1 : ℤ) s ×ˢ Finset.Icc (1 : ℤ) s ×ˢ Finset.Icc (1 : ℤ) s

theorem mem_box_iff {s : ℕ} {x : Cell} :
    x ∈ box s ↔ 1 ≤ x.1 ∧ x.1 ≤ (s : ℤ) ∧ 1 ≤ x.2.1 ∧ x.2.1 ≤ (s : ℤ)
      ∧ 1 ≤ x.2.2 ∧ x.2.2 ≤ (s : ℤ) := by
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  tauto

theorem card_box (s : ℕ) : (box s).card = s * s * s := by
  have hc : (Finset.Icc (1 : ℤ) s).card = s := by rw [Int.card_Icc]; omega
  rw [box, Finset.card_product, Finset.card_product, hc]
  ring

/-- Even elements of `[2, s-1]`. -/
def evens (s : ℕ) : Finset ℤ := (Finset.Icc (2 : ℤ) (s - 1)).filter (fun a => a % 2 = 0)

/-- The even-parity interior core of the `s`-box; any two of its cells are
non-adjacent (a unit step flips a coordinate parity). -/
def evenCore (s : ℕ) : Finset Cell := evens s ×ˢ evens s ×ˢ evens s

theorem evenCore_subset_box (s : ℕ) : evenCore s ⊆ box s := by
  intro x hx
  simp only [evenCore, Finset.mem_product, evens, Finset.mem_filter, Finset.mem_Icc] at hx
  simp only [mem_box_iff]
  omega

theorem core_step_mem_box {s : ℕ} {h : Cell} {d : Cell}
    (hh : h ∈ evenCore s) (hd : d ∈ dirs) : addDir h d ∈ box s := by
  obtain ⟨t1, t2, t3⟩ := dirs_bdd hd
  simp only [evenCore, Finset.mem_product, evens, Finset.mem_filter, Finset.mem_Icc] at hh
  obtain ⟨⟨h1, h1e⟩, ⟨h2, h2e⟩, ⟨h3, h3e⟩⟩ := hh
  simp only [addDir, mem_box_iff]
  omega

theorem core_step_not_mem_core {s : ℕ} {h : Cell} {d : Cell}
    (hh : h ∈ evenCore s) (hd : d ∈ dirs) : addDir h d ∉ evenCore s := by
  intro hmem
  simp only [evenCore, Finset.mem_product, evens, Finset.mem_filter, Finset.mem_Icc] at hh hmem
  obtain ⟨⟨h1, h1e⟩, ⟨h2, h2e⟩, ⟨h3, h3e⟩⟩ := hh
  obtain ⟨⟨g1, g1e⟩, ⟨g2, g2e⟩, ⟨g3, g3e⟩⟩ := hmem
  simp only [addDir] at g1e g2e g3e
  obtain ⟨t1, t2, t3⟩ := dirs_bdd hd
  rcases dirs_axis hd with e1 | e2 | e3
  all_goals
    rcases t1 with h1' | h1' | h1' <;> rcases t2 with h2' | h2' | h2' <;>
      rcases t3 with h3' | h3' | h3' <;> omega

/-! ## The box-with-holes perimeter identity -/

/-- **The increment theorem** (W24-A's "perimeter exactly `6s² + 6k`",
Lean form). Removing `k` holes — an arbitrary subset of the even-parity
core — from the `s`-box raises the face-perimeter by exactly `6·k`. -/
theorem perimeter_box_sdiff {s : ℕ} {H : Finset Cell} (hH : H ⊆ evenCore s) :
    perimeter (box s \ H) = perimeter (box s) + 6 * H.card := by
  classical
  have hHbox : H ⊆ box s := Finset.Subset.trans hH (evenCore_subset_box s)
  have hunion : (box s \ H) ∪ H = box s := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    by_cases hxH : x ∈ H
    · simp [hxH, hHbox hxH]
    · by_cases hxb : x ∈ box s
      · simp [hxb, hxH]
      · simp [hxH, hxb]
  have hdisj : Disjoint (box s \ H) H := by
    apply Finset.disjoint_left.mpr
    rintro x hx hxH'
    exact (Finset.mem_sdiff.mp hx).2 hxH'
  have hrowsH : ∑ x ∈ H, ∑ d ∈ dirs, (if addDir x d ∈ box s then 0 else 1) = 0 := by
    refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun d hd => ?_
    have hmem : addDir x d ∈ box s := core_step_mem_box (hH hx) hd
    simp [hmem]
  have hsplit :
      ∑ x ∈ box s, ∑ d ∈ dirs, (if addDir x d ∈ box s then 0 else 1)
        = (∑ x ∈ box s \ H, ∑ d ∈ dirs, (if addDir x d ∈ box s then 0 else 1))
          + ∑ x ∈ H, ∑ d ∈ dirs, (if addDir x d ∈ box s then 0 else 1) := by
    rw [← Finset.sum_union hdisj, hunion]
  simp only [perimeter]
  rw [hsplit, hrowsH, add_zero]
  have hterm : ∀ x ∈ box s \ H, ∀ d ∈ dirs,
      (if addDir x d ∈ box s \ H then 0 else 1)
        = (if addDir x d ∈ box s then 0 else 1) + (if addDir x d ∈ H then 1 else 0) := by
    intro x hx d _
    rcases Finset.mem_sdiff.mp hx with ⟨hxb, hxH⟩
    by_cases h1 : addDir x d ∈ H
    · have hnA : addDir x d ∉ box s \ H := fun hc => (Finset.mem_sdiff.mp hc).2 h1
      have hbx : addDir x d ∈ box s := hHbox h1
      simp [h1, hnA, hbx]
    · by_cases h2 : addDir x d ∈ box s
      · have hA' : addDir x d ∈ box s \ H := Finset.mem_sdiff.mpr ⟨h2, h1⟩
        simp [h1, h2, hA']
      · have hnA : addDir x d ∉ box s \ H := fun hc => h2 (Finset.mem_sdiff.mp hc).1
        simp [h1, h2, hnA]
  rw [Finset.sum_congr rfl (fun x hx =>
    Finset.sum_congr rfl (fun d hd => hterm x hx d hd))]
  simp only [Finset.sum_add_distrib]
  have hfiber : ∑ x ∈ box s \ H, ∑ d ∈ dirs, (if addDir x d ∈ H then 1 else 0)
      = 6 * H.card := by
    have hper : ∀ d ∈ dirs,
        ∑ x ∈ box s \ H, (if addDir x d ∈ H then 1 else 0) = H.card := by
      intro d hd
      have hexp : ∀ x ∈ box s \ H,
          (if addDir x d ∈ H then (1:ℕ) else 0)
            = ∑ h ∈ H, (if addDir x d = h then 1 else 0) := by
        intro x _
        by_cases hx : addDir x d ∈ H
        · rw [if_pos hx]
          have hsingle : ∑ h ∈ H, (if addDir x d = h then (1:ℕ) else 0) = 1 := by
            rw [Finset.sum_eq_single (addDir x d)]
            · simp
            · intro b _ hb; exact if_neg (fun he => hb he.symm)
            · intro hn; exact absurd hx hn
          rw [hsingle]
        · rw [if_neg hx]
          refine Eq.symm (Finset.sum_eq_zero fun h hh => ?_)
          refine if_neg (fun he => hx (by rw [he]; exact hh))
      have hfib1 : ∀ h ∈ H,
          ∑ x ∈ box s \ H, (if addDir x d = h then (1:ℕ) else 0) = 1 := by
        intro h hh
        rw [Finset.sum_congr rfl
          (fun x _ => if_congr (addDir_eq_iff x d h) rfl rfl)]
        have hmem : addDir h (negDir d) ∈ box s \ H := by
          refine Finset.mem_sdiff.mpr ⟨core_step_mem_box (hH hh) (negDir_mem_dirs hd), ?_⟩
          intro hc
          exact core_step_not_mem_core (hH hh) (negDir_mem_dirs hd) (hH hc)
        rw [Finset.sum_ite_eq', if_pos hmem]
      calc ∑ x ∈ box s \ H, (if addDir x d ∈ H then (1:ℕ) else 0)
          = ∑ h ∈ H, ∑ x ∈ box s \ H, (if addDir x d = h then (1:ℕ) else 0) := by
            rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
        _ = ∑ h ∈ H, 1 := Finset.sum_congr rfl hfib1
        _ = H.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
    calc ∑ x ∈ box s \ H, ∑ d ∈ dirs, (if addDir x d ∈ H then 1 else 0)
        = ∑ d ∈ dirs, ∑ x ∈ box s \ H, (if addDir x d ∈ H then 1 else 0) := Finset.sum_comm
      _ = ∑ d ∈ dirs, H.card := Finset.sum_congr rfl hper
      _ = dirs.card * H.card := by rw [Finset.sum_const, smul_eq_mul]
      _ = 6 * H.card := by rw [card_dirs]
  rw [hfiber]

/-! ## A quadratic perimeter bound for the box -/

private lemma box_sum_ite_le1 (s : ℕ) (j : ℤ) :
    ∑ x ∈ box s, (if x.1 = j then (1:ℕ) else 0) ≤ s * s := by
  have hc : (Finset.Icc (1 : ℤ) s).card = s := by rw [Int.card_Icc]; omega
  rw [box]
  simp only [Finset.sum_product]
  have hbc : ∀ a : ℤ, ∑ c ∈ Finset.Icc (1:ℤ) s, (if a = j then (1:ℕ) else 0)
      = s * (if a = j then 1 else 0) := by
    intro a; rw [Finset.sum_const, smul_eq_mul, hc]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hbc a))]
  have hbb : ∀ a : ℤ, ∑ b ∈ Finset.Icc (1:ℤ) s, (s * (if a = j then (1:ℕ) else 0))
      = s * (s * (if a = j then 1 else 0)) := by
    intro a; rw [Finset.sum_const, smul_eq_mul, hc]
  rw [Finset.sum_congr rfl (fun a _ => hbb a)]
  have harr : ∀ a : ℤ, s * (s * (if a = j then (1:ℕ) else 0))
      = (if a = j then 1 else 0) * (s * s) := by
    intro a; by_cases ha : a = j <;> simp [ha]
  rw [Finset.sum_congr rfl (fun a _ => harr a), ← Finset.sum_mul, Finset.sum_ite_eq']
  by_cases hj : j ∈ Finset.Icc (1:ℤ) s
  · rw [if_pos hj, Nat.one_mul]
  · rw [if_neg hj, Nat.zero_mul]
    exact Nat.zero_le _

private lemma box_sum_ite_le2 (s : ℕ) (j : ℤ) :
    ∑ x ∈ box s, (if x.2.1 = j then (1:ℕ) else 0) ≤ s * s := by
  have hc : (Finset.Icc (1 : ℤ) s).card = s := by rw [Int.card_Icc]; omega
  rw [box]
  simp only [Finset.sum_product]
  have hin : ∀ a b : ℤ, ∑ c ∈ Finset.Icc (1:ℤ) s, (if b = j then (1:ℕ) else 0)
      = s * (if b = j then 1 else 0) := by
    intro a b; rw [Finset.sum_const, smul_eq_mul, hc]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hin a b))]
  have hbb : ∑ b ∈ Finset.Icc (1:ℤ) s, (s * (if b = j then (1:ℕ) else 0))
      = s * (if j ∈ Finset.Icc (1:ℤ) s then 1 else 0) := by
    rw [← Finset.mul_sum, Finset.sum_ite_eq']
  rw [Finset.sum_congr rfl (fun a _ => by rw [hbb])]
  by_cases hj : j ∈ Finset.Icc (1:ℤ) s
  · have hfin : ∀ a : ℤ, (s * (if j ∈ Finset.Icc (1:ℤ) s then (1:ℕ) else 0)) = s := by
      intro a; rw [if_pos hj]; omega
    rw [Finset.sum_congr rfl (fun a _ => hfin a), Finset.sum_const, smul_eq_mul, hc]
  · have hfin : ∀ a : ℤ, (s * (if j ∈ Finset.Icc (1:ℤ) s then (1:ℕ) else 0)) = 0 := by
      intro a; rw [if_neg hj]; omega
    rw [Finset.sum_congr rfl (fun a _ => hfin a)]
    simp

private lemma box_sum_ite_le3 (s : ℕ) (j : ℤ) :
    ∑ x ∈ box s, (if x.2.2 = j then (1:ℕ) else 0) ≤ s * s := by
  have hc : (Finset.Icc (1 : ℤ) s).card = s := by rw [Int.card_Icc]; omega
  rw [box]
  simp only [Finset.sum_product]
  have hin : ∀ a b : ℤ, ∑ c ∈ Finset.Icc (1:ℤ) s, (if c = j then (1:ℕ) else 0)
      = if j ∈ Finset.Icc (1:ℤ) s then 1 else 0 := by
    intro a b; rw [Finset.sum_ite_eq']
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hin a b))]
  by_cases hj : j ∈ Finset.Icc (1:ℤ) s
  · have hval : (if j ∈ Finset.Icc (1:ℤ) s then (1:ℕ) else 0) = 1 := if_pos hj
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hval))]
    rw [Finset.sum_const, smul_eq_mul, hc]
    rw [Finset.sum_const, smul_eq_mul, hc]
    rw [Nat.mul_one]
  · have hval : (if j ∈ Finset.Icc (1:ℤ) s then (1:ℕ) else 0) = 0 := if_neg hj
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hval))]
    simp

/-- Quadratic perimeter bound for the box (the exact value is `6·s²`; only
the quadratic order is consumed by `Entropy.lean`). -/
theorem perimeter_box_le (s : ℕ) (hs : 1 ≤ s) : perimeter (box s) ≤ 12 * s * s := by
  have hface1 : ∀ d ∈ ({(-1, 0, 0), (1, 0, 0)} : Finset Cell),
      ∑ x ∈ box s, (if addDir x d ∈ box s then (0:ℕ) else 1) ≤ 2 * s * s := by
    intro d hd
    have hpt : ∀ x ∈ box s, (if addDir x d ∈ box s then (0:ℕ) else 1)
        ≤ (if x.1 = 1 then (1:ℕ) else 0) + (if x.1 = (s:ℤ) then 1 else 0) := by
      intro x hx
      simp only [addDir, mem_box_iff] at hx ⊢
      rcases Finset.mem_insert.mp hd with rfl | hd2
      · by_cases hx1 : x.1 = 1
        · simp [hx1]
        · rw [if_pos (by simp only [Int.add_zero, Int.zero_add]; omega)]
          omega
      · rw [Finset.mem_singleton.mp hd2]
        by_cases hx1 : x.1 = (s:ℤ)
        · simp [hx1]
        · rw [if_pos (by simp only [Int.add_zero, Int.zero_add]; omega)]
          omega
    calc ∑ x ∈ box s, (if addDir x d ∈ box s then (0:ℕ) else 1)
        ≤ ∑ x ∈ box s, ((if x.1 = 1 then 1 else 0) + (if x.1 = (s:ℤ) then 1 else 0)) :=
          Finset.sum_le_sum hpt
      _ = ∑ x ∈ box s, (if x.1 = 1 then (1:ℕ) else 0)
            + ∑ x ∈ box s, (if x.1 = (s:ℤ) then 1 else 0) := Finset.sum_add_distrib
      _ ≤ s * s + s * s := Nat.add_le_add (box_sum_ite_le1 s 1) (box_sum_ite_le1 s s)
      _ ≤ 2 * s * s := by rw [Nat.two_mul, Nat.add_mul]
  have hface2 : ∀ d ∈ ({(0, -1, 0), (0, 1, 0)} : Finset Cell),
      ∑ x ∈ box s, (if addDir x d ∈ box s then (0:ℕ) else 1) ≤ 2 * s * s := by
    intro d hd
    have hpt : ∀ x ∈ box s, (if addDir x d ∈ box s then (0:ℕ) else 1)
        ≤ (if x.2.1 = 1 then (1:ℕ) else 0) + (if x.2.1 = (s:ℤ) then 1 else 0) := by
      intro x hx
      simp only [addDir, mem_box_iff] at hx ⊢
      rcases Finset.mem_insert.mp hd with rfl | hd2
      · by_cases hx1 : x.2.1 = 1
        · simp [hx1]
        · rw [if_pos (by simp only [Int.add_zero, Int.zero_add]; omega)]
          omega
      · rw [Finset.mem_singleton.mp hd2]
        by_cases hx1 : x.2.1 = (s:ℤ)
        · simp [hx1]
        · rw [if_pos (by simp only [Int.add_zero, Int.zero_add]; omega)]
          omega
    calc ∑ x ∈ box s, (if addDir x d ∈ box s then (0:ℕ) else 1)
        ≤ ∑ x ∈ box s, ((if x.2.1 = 1 then 1 else 0) + (if x.2.1 = (s:ℤ) then 1 else 0)) :=
          Finset.sum_le_sum hpt
      _ = ∑ x ∈ box s, (if x.2.1 = 1 then (1:ℕ) else 0)
            + ∑ x ∈ box s, (if x.2.1 = (s:ℤ) then 1 else 0) := Finset.sum_add_distrib
      _ ≤ s * s + s * s := Nat.add_le_add (box_sum_ite_le2 s 1) (box_sum_ite_le2 s s)
      _ ≤ 2 * s * s := by rw [Nat.two_mul, Nat.add_mul]
  have hface3 : ∀ d ∈ ({(0, 0, -1), (0, 0, 1)} : Finset Cell),
      ∑ x ∈ box s, (if addDir x d ∈ box s then (0:ℕ) else 1) ≤ 2 * s * s := by
    intro d hd
    have hpt : ∀ x ∈ box s, (if addDir x d ∈ box s then (0:ℕ) else 1)
        ≤ (if x.2.2 = 1 then (1:ℕ) else 0) + (if x.2.2 = (s:ℤ) then 1 else 0) := by
      intro x hx
      simp only [addDir, mem_box_iff] at hx ⊢
      rcases Finset.mem_insert.mp hd with rfl | hd2
      · by_cases hx1 : x.2.2 = 1
        · simp [hx1]
        · rw [if_pos (by simp only [Int.add_zero, Int.zero_add]; omega)]
          omega
      · rw [Finset.mem_singleton.mp hd2]
        by_cases hx1 : x.2.2 = (s:ℤ)
        · simp [hx1]
        · rw [if_pos (by simp only [Int.add_zero, Int.zero_add]; omega)]
          omega
    calc ∑ x ∈ box s, (if addDir x d ∈ box s then (0:ℕ) else 1)
        ≤ ∑ x ∈ box s, ((if x.2.2 = 1 then 1 else 0) + (if x.2.2 = (s:ℤ) then 1 else 0)) :=
          Finset.sum_le_sum hpt
      _ = ∑ x ∈ box s, (if x.2.2 = 1 then (1:ℕ) else 0)
            + ∑ x ∈ box s, (if x.2.2 = (s:ℤ) then 1 else 0) := Finset.sum_add_distrib
      _ ≤ s * s + s * s := Nat.add_le_add (box_sum_ite_le3 s 1) (box_sum_ite_le3 s s)
      _ ≤ 2 * s * s := by rw [Nat.two_mul, Nat.add_mul]
  have hpd : ∀ d ∈ dirs,
      ∑ x ∈ box s, (if addDir x d ∈ box s then (0:ℕ) else 1) ≤ 2 * s * s := by
    intro d hd
    rcases dirs_cases hd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hface1 _ (Finset.mem_insert.mpr (Or.inl rfl))
    · exact hface1 _ (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))
    · exact hface2 _ (Finset.mem_insert.mpr (Or.inl rfl))
    · exact hface2 _ (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))
    · exact hface3 _ (Finset.mem_insert.mpr (Or.inl rfl))
    · exact hface3 _ (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))
  calc perimeter (box s)
      = ∑ d ∈ dirs, ∑ x ∈ box s, (if addDir x d ∈ box s then (0:ℕ) else 1) := Finset.sum_comm
    _ ≤ ∑ d ∈ dirs, 2 * s * s := Finset.sum_le_sum hpd
    _ = dirs.card * (2 * s * s) := by rw [Finset.sum_const, smul_eq_mul]
    _ = 12 * s * s := by rw [card_dirs]; ring

end YangMills3D

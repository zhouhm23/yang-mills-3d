/-
The wave-30 theorem layer: W30-FLOOR2 (the diameter-perimeter floor),
W30-RATE (the doubled connecting rate: geometric core + rate law), and
the W30-FORM covariance-split germ, Lean form.

SOURCE. `problems/yang-mills-mass-gap/lemmas/w30-fan.md` §1 (Lemma
W30-FLOOR2 and Theorem W30-RATE), `lemmas/w29-count.md` §1 (the W29-EF
effective-fan criterion whose rate W30-RATE doubles) and
`lemmas/w30-charge.md` §1 (Proposition W30-FORM), reusing
`YangMills3D.Animals` (`Cell`, `dirs`, `addDir`, `perimeter`),
`YangMills3D.Floor` (the shadows, `xext`, and the shadow-projection
bound `perimeter_ge_shadows`), and `YangMills3D.Mixture`/`Window`
(`n1`, `bar`).

  * W30-FLOOR2 [`perimeter_ge_two_r`] — a finite VERTEX-PATH-CONNECTED
    cell set with ℓ₁-diameter `r` has at least `2r + 6` exposed faces
    (TIGHT: the corner chain `(i,i,i)`, `i = 0..m`, formalized as
    `diagChain` with perimeter exactly `6(m+1)` and diameter exactly
    `3m`, `w30_floor2_tight`).  The proof is the three-axis shadow
    bound: `p_xy ≥ xext`, `p_yz ≥ yext`, `p_xz ≥ zext` (each met fiber
    contributes its extreme faces — `Floor.perimeter_ge_shadows`),
    plus the coordinate-span IVT along vertex paths (one vertex step
    changes each coordinate by at most 1), giving `xext ≥ a + 1`,
    `yext ≥ b + 1`, `zext ≥ c + 1` for any two cells of the set.

    HONEST CORRECTION.  w30-fan.md §1 states W30-FLOOR2 for ARBITRARY
    finite `A ⊂ Z³` ("the bound needs NO connectivity of A"); that
    unrestricted statement is FALSE: the two-point set
    `{(0,0,0), (r,0,0)}` has perimeter `12 < 2r + 6` for every `r ≥ 4`
    (its shadow sum is only `1 + 2 + 2 = 5`, and the campaign's step
    `p_xy ≥ max(a,b) + 1` fails — the shadow contains the two projected
    cells, not the interpolated segment).  What the proof actually uses
    is interval-filling of the coordinate projections, which holds for
    vertex-connected sets — exactly the chain unions W30-RATE consumes
    (consecutive Mayer-chain polymers are vertex-incompatible, the
    mission's 18-adjacency, so their union of enclosed cells is
    vertex-connected).  The connected form is what is proved here; the
    machine sweep of w30-fan (20000 random sets, 0 violations) evidently
    sampled connected animals and missed the two-point counterexample.

  * W30-RATE [`connecting_perimeter_floor`] — the geometric core of the
    doubling law.  A vertex-path-connected cell set `W` that reaches
    within halo distance 1 of both anchors (the spanning attachment of
    a connecting Mayer-chain union: a face of `x`'s cell in `∂W` forces
    a cell `x'` of `W` at ℓ₁-distance ≤ 1 from `x`) has perimeter at
    least `2d + 2` at `d = |x − y|₁`: `diam W ≥ d − 2` and W30-FLOOR2
    gives `≥ 2(d − 2) + 6 = 2d + 2`.  Hence the W29-EF rate
    `κ_c − ln F₀ − ε` DOUBLES: the rate law is
    `nu2 κc F0 ε = 2(κc − ln F0 − ε)`, and at the window bottom
    `β = 6.618` the [W30-MISS] fan price `F₀ ≤ 6.093` clears the ascent
    bar `0.493·2.40` [`w30_rate_clears_bar`, `w30_conditional`].  The
    analytic passage (Mayer-chain domination and KP summability,
    w29-count §1 / w30-fan §1) remains the standing banked input —
    PVO-3D: nothing here asserts an unconditional SU(2) statement.

  * W30-FORM [`cov_split`] — the exact intra/inter-cluster split of a
    squared amplitude over a finite family (w30-charge §1: with
    `W_p = Σ_a W_a(p)` the cluster decomposition, `|W_p|² = Σ_a |W_a|² +
    Σ_{a≠b} W_a conj(W_b)`: the walk part is the diagonal, the ENTIRE
    mass content is the inter-cluster charging term).  This is the
    statement-level germ; the ensemble layer (expectations over the
    k-gas, the W28-DICT substitution) needs the campaign's gas
    machinery and is NOT formalized here.

Every statement below is fully proved: no unfinished proofs, no new
axioms.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import YangMills3D.Animals
import YangMills3D.Floor
import YangMills3D.Mixture

namespace YangMills3D

/-! ## The ℓ₁ norm on cells (natural-number currency) -/

/-- The ℓ₁ norm of a cell, natural-number currency (the `n1` of
`YangMills3D.Mixture` without the cast). -/
def n1n (x : Cell) : ℕ := x.1.natAbs + x.2.1.natAbs + x.2.2.natAbs

/-- **[T-OP]** the cell ℓ₁ norm satisfies the triangle inequality (ℕ
form of `Mixture.n1_triangle`). -/
theorem n1n_triangle (x y : Cell) : n1n (x + y) ≤ n1n x + n1n y := by
  have hxy : x + y = (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2) := rfl
  rw [hxy]
  simp only [n1n]
  have h1 := Int.natAbs_add_le x.1 y.1
  have h2 := Int.natAbs_add_le x.2.1 y.2.1
  have h3 := Int.natAbs_add_le x.2.2 y.2.2
  omega

private lemma n1n_add3 (a b c : Cell) : n1n (a + b + c) ≤ n1n a + n1n b + n1n c := by
  have h1 : n1n (a + b + c) ≤ n1n (a + b) + n1n c := n1n_triangle _ _
  have h2 : n1n (a + b) ≤ n1n a + n1n b := n1n_triangle a b
  omega

/-- The ℓ₁ norm is symmetric under swapping the endpoints. -/
private lemma n1n_sub_comm (x y : Cell) : n1n (x - y) = n1n (y - x) := by
  have hxy : x - y = (x.1 - y.1, x.2.1 - y.2.1, x.2.2 - y.2.2) := rfl
  have hyx : y - x = (y.1 - x.1, y.2.1 - x.2.1, y.2.2 - x.2.2) := rfl
  have habs : ∀ a b : ℤ, (a - b).natAbs = (b - a).natAbs := fun a b => by
    rw [show b - a = -(a - b) from by ring, Int.natAbs_neg]
  rw [hxy, hyx]
  simp only [n1n, habs]

/-- The ℝ-currency bridge: `n1` is the cast of `n1n`. -/
theorem n1_eq_n1n (x : Cell) : n1 x = (n1n x : ℝ) := by
  simp only [n1, n1n, Nat.cast_add]

/-! ## The ℓ₁-diameter -/

/-- The ℓ₁-diameter of a finite cell set: the largest pairwise ℓ₁
distance of its cells (`0` for the empty set). -/
def l1diam (A : Finset Cell) : ℕ := A.sup fun u => A.sup fun v => n1n (u - v)

/-- The diameter is dominated by any uniform pairwise bound. -/
theorem l1diam_le_of_forall (A : Finset Cell) (k : ℕ)
    (h : ∀ u ∈ A, ∀ v ∈ A, n1n (u - v) ≤ k) : l1diam A ≤ k :=
  Finset.sup_le fun u hu => Finset.sup_le fun v hv => h u hu v hv

/-- Any pair of cells realizes a distance below the diameter. -/
theorem le_l1diam_of_mem {A : Finset Cell} {u v : Cell} (hu : u ∈ A) (hv : v ∈ A) :
    n1n (u - v) ≤ l1diam A := by
  have h1 : n1n (u - v) ≤ A.sup (fun w => n1n (u - w)) :=
    Finset.le_sup (f := fun w => n1n (u - w)) hv
  have h2 : A.sup (fun w => n1n (u - w)) ≤ l1diam A :=
    Finset.le_sup (f := fun w => A.sup fun w' => n1n (w - w')) hu
  exact le_trans h1 h2

/-! ## Vertex paths and the coordinate-span IVT -/

/-- Vertex-adjacency (26-adjacency) of two cells: every coordinate
differs by at most 1. -/
def vtxAdj (x y : Cell) : Prop :=
  |x.1 - y.1| ≤ 1 ∧ |x.2.1 - y.2.1| ≤ 1 ∧ |x.2.2 - y.2.2| ≤ 1

/-- A vertex path in `A` from `u` to `v`: a discrete walk `w 0 = u, …,
w k = v` staying in `A` with vertex-adjacent consecutive cells — the
26-connectedness of the campaign's chain unions (consecutive Mayer-chain
polymers are vertex-incompatible, w30-fan §1). -/
def VtxPath (A : Finset Cell) (u v : Cell) : Prop :=
  ∃ (k : ℕ) (w : ℕ → Cell), w 0 = u ∧ w k = v
    ∧ (∀ i, i ≤ k → w i ∈ A) ∧ (∀ i, i < k → vtxAdj (w i) (w (i + 1)))

/-- Discrete IVT: a coordinate walk with steps of size at most `1`
running from layer `f (w 0)` up to layer `f (w k)` hits every
intermediate lattice layer (this is what makes the coordinate
projections of a vertex-connected set interval-filling). -/
private lemma ivt_image (A : Finset Cell) (f : Cell → ℤ) :
    ∀ (k : ℕ) (w : ℕ → Cell),
      (∀ i, i ≤ k → w i ∈ A) →
      (∀ i, i < k → |f (w i) - f (w (i + 1))| ≤ 1) →
      f (w 0) ≤ f (w k) →
      Finset.Icc (f (w 0)) (f (w k)) ⊆ A.image f := by
  intro k
  induction k with
  | zero =>
    intro w hA _ _ t ht
    rw [Finset.mem_Icc] at ht
    rw [le_antisymm ht.2 ht.1]
    exact Finset.mem_image.mpr ⟨w 0, hA 0 (Nat.zero_le _), rfl⟩
  | succ k ih =>
    intro w hA hstep hle t ht
    rw [Finset.mem_Icc] at ht
    rcases lt_or_ge t (f (w k)) with hlt | hge1
    · -- `t < f (w k)`: the length-`k` prefix already reaches the layer
      have hle' : f (w 0) ≤ f (w k) := le_trans ht.1 (le_of_lt hlt)
      have htk : t ∈ Finset.Icc (f (w 0)) (f (w k)) :=
        Finset.mem_Icc.mpr ⟨ht.1, le_of_lt hlt⟩
      have hsub := ih w (fun i hi => hA i (le_trans hi (Nat.le_succ k)))
        (fun i hi => hstep i (Nat.lt_succ_of_lt hi)) hle'
      exact hsub htk
    · -- `f (w k) ≤ t ≤ f (w (k+1)) ≤ f (w k) + 1`: `t` is one of the two
      -- endpoint layers, both realized by cells of `A`
      obtain ⟨h1, h2⟩ := abs_le.mp (hstep k (Nat.lt_succ_self k))
      have hcase : t = f (w k) ∨ t = f (w (k + 1)) := by omega
      rcases hcase with heq | heq
      · rw [heq]
        exact Finset.mem_image.mpr ⟨w k, hA k (by omega), rfl⟩
      · rw [heq]
        exact Finset.mem_image.mpr ⟨w (k + 1), hA _ (Nat.le_refl _), rfl⟩

/-- The coordinate-span bound: two cells joined by a vertex path in `A`
have their `f`-coordinate span (`|f u − f v| + 1` lattice layers) fully
represented in the `f`-projection profile of `A`.  The hypothesis `hf`
extracts the per-coordinate step bound from the vertex-adjacency of the
path. -/
theorem span_le_card_image {A : Finset Cell} {u v : Cell} (hp : VtxPath A u v)
    (f : Cell → ℤ)
    (hf : ∀ (k : ℕ) (w : ℕ → Cell),
      (∀ i, i < k → vtxAdj (w i) (w (i + 1))) →
      ∀ i, i < k → |f (w i) - f (w (i + 1))| ≤ 1) :
    (f u - f v).natAbs + 1 ≤ (A.image f).card := by
  obtain ⟨k, w, h0, hk, hA, hstep⟩ := hp
  rcases le_total (f u) (f v) with hle | hge
  · have hsub := ivt_image A f k w hA (hf k w hstep) (by rw [h0, hk]; exact hle)
    rw [h0, hk] at hsub
    have hcard : (Finset.Icc (f u) (f v)).card = (f u - f v).natAbs + 1 := by
      rw [Int.card_Icc]; omega
    have hcle := Finset.card_le_card hsub
    rwa [hcard] at hcle
  · -- reverse the path
    have hstep' : ∀ i, i < k → |f (w (k - i)) - f (w (k - (i + 1)))| ≤ 1 := by
      intro i hi
      have h := hf k w hstep (k - i - 1) (by omega)
      rw [show k - i - 1 + 1 = k - i from by omega] at h
      rw [show k - (i + 1) = k - i - 1 from by omega, abs_sub_comm]
      exact h
    have hv0 : w (k - 0) = v := by rw [Nat.sub_zero, hk]
    have hvk : w (k - k) = u := by rw [Nat.sub_self, h0]
    have hsub := ivt_image A f k (fun i => w (k - i))
      (fun i hi => hA _ (Nat.sub_le _ _)) hstep' (by rw [hv0, hvk]; exact hge)
    rw [hv0, hvk] at hsub
    have hcard : (Finset.Icc (f v) (f u)).card = (f u - f v).natAbs + 1 := by
      rw [Int.card_Icc]; omega
    have hcle := Finset.card_le_card hsub
    rwa [hcard] at hcle

/-- A unit step changes a clamped coordinate by at most 1. -/
private lemma min_step (a b : ℤ) : |min a b - min (a + 1) b| ≤ 1 := by
  rcases le_total b a with h | h
  · rw [min_eq_right h, min_eq_right (by linarith)]
    simp
  · rcases le_total (a + 1) b with h2 | h2
    · rw [min_eq_left h, min_eq_left h2]
      simp
    · rw [min_eq_left h, min_eq_right h2]
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩

/-- A unit step changes a clamped coordinate by at most 1. -/
private lemma max_step (a b : ℤ) : |max a b - max (a - 1) b| ≤ 1 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]
    simp
  · rcases le_total b (a - 1) with h2 | h2
    · rw [max_eq_left h, max_eq_left h2]
      simp
    · rw [max_eq_left h, max_eq_right h2]
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩

/-- The y-extent: the number of distinct y-layers met by the set. -/
def yext (A : Finset Cell) : ℕ := (A.image fun c => c.2.1).card

/-- The z-extent: the number of distinct z-layers met by the set. -/
def zext (A : Finset Cell) : ℕ := (A.image fun c => c.2.2).card

/-- The x-span of a vertex path is dominated by the x-layer profile. -/
theorem xext_ge_span {A : Finset Cell} {u v : Cell} (hp : VtxPath A u v) :
    (u.1 - v.1).natAbs + 1 ≤ xext A :=
  span_le_card_image hp (fun c => c.1) (fun _ _ hstep i hi => (hstep i hi).1)

/-- The y-span of a vertex path is dominated by the y-layer profile. -/
theorem yext_ge_span {A : Finset Cell} {u v : Cell} (hp : VtxPath A u v) :
    (u.2.1 - v.2.1).natAbs + 1 ≤ yext A :=
  span_le_card_image hp (fun c => c.2.1) (fun _ _ hstep i hi => (hstep i hi).2.1)

/-- The z-span of a vertex path is dominated by the z-layer profile. -/
theorem zext_ge_span {A : Finset Cell} {u v : Cell} (hp : VtxPath A u v) :
    (u.2.2 - v.2.2).natAbs + 1 ≤ zext A :=
  span_le_card_image hp (fun c => c.2.2) (fun _ _ hstep i hi => (hstep i hi).2.2)

/-! ## The three-axis shadow domination -/

/-- The number of distinct y-layers is dominated by the yz-shadow. -/
theorem yext_le_shadowYZ (A : Finset Cell) : yext A ≤ (shadowYZ A).card := by
  have h : (shadowYZ A).image (fun p => p.1) = A.image (fun c => c.2.1) := by
    rw [shadowYZ, Finset.image_image]
    exact Finset.image_congr (fun c _ => rfl)
  rw [yext, ← h]
  exact Finset.card_image_le

/-- The number of distinct z-layers is dominated by the xz-shadow. -/
theorem zext_le_shadowXZ (A : Finset Cell) : zext A ≤ (shadowXZ A).card := by
  have h : (shadowXZ A).image (fun p => p.2) = A.image (fun c => c.2.2) := by
    rw [shadowXZ, Finset.image_image]
    exact Finset.image_congr (fun c _ => rfl)
  rw [zext, ← h]
  exact Finset.card_image_le

/-! ## Theorem W30-FLOOR2: perimeter ≥ 2·diameter + 6 -/

/-- **Lemma W30-FLOOR2** (w30-fan §1, vertex-connected form) **[W30-FLOOR2]**:
a nonempty finite cell set in which any two cells are joined by a vertex
path (26-connectedness; the campaign's chain unions are exactly of this
kind) and with ℓ₁-diameter `r = l1diam A` has at least `2r + 6` exposed
faces.  TIGHT: the corner chain `diagChain m` (`(i,i,i)`, `i = 0..m`)
has diameter `3m` and perimeter exactly `6(m+1) = 2·(3m) + 6`
(`w30_floor2_tight`).  Strengthens the banked W23-P floor `((4/3)r + 4)`
for every `r`; supersedes `Floor.perimeter_ge_of_xext`'s `4·xext + 2`
(tube form) by the three-axis version.

PROOF (w30-fan §1, corrected): the shadow bound
`Floor.perimeter_ge_shadows` gives `perimeter A ≥ 2(p_xy + p_xz + p_yz)`;
the coordinate-span IVT gives `xext ≥ a + 1`, `yext ≥ b + 1`,
`zext ≥ c + 1` for the componentwise coordinate gaps `a, b, c` of any
pair; the shadows dominate the layer counts `xext, yext, zext`
respectively; summing, `p_xy + p_xz + p_yz ≥ a + b + c + 3 = r + 3`.
See the module docstring for the honest correction of the campaign's
unrestricted (connectivity-free) form. -/
theorem perimeter_ge_two_r (A : Finset Cell) (hne : A.Nonempty)
    (hconn : ∀ u ∈ A, ∀ v ∈ A, VtxPath A u v) :
    2 * l1diam A + 6 ≤ perimeter A := by
  have hpairs : ∀ u ∈ A, ∀ v ∈ A, 2 * n1n (u - v) + 6 ≤ perimeter A := by
    intro u hu v hv
    have h1' := xext_ge_span (hconn u hu v hv)
    have h2' := yext_ge_span (hconn u hu v hv)
    have h3' := zext_ge_span (hconn u hu v hv)
    have he1 := xext_le_shadowXY A
    have he2 := yext_le_shadowYZ A
    have he3 := zext_le_shadowXZ A
    have hs := perimeter_ge_shadows A
    have hn : n1n (u - v) = (u.1 - v.1).natAbs + (u.2.1 - v.2.1).natAbs
        + (u.2.2 - v.2.2).natAbs := rfl
    omega
  have hP6 : 6 ≤ perimeter A := by
    obtain ⟨u, hu⟩ := hne
    have h := hpairs u hu u hu
    omega
  have hsup : l1diam A ≤ (perimeter A - 6) / 2 :=
    l1diam_le_of_forall A _ fun u hu v hv =>
      Nat.le_div_iff_mul_le (by norm_num) |>.2 (by
        have h := hpairs u hu v hv
        omega)
  have hdm : (perimeter A - 6) / 2 * 2 ≤ perimeter A - 6 := Nat.div_mul_le_self _ _
  omega

/-! ## Tightness: the corner chain (the W30-FLOOR2 exhibit) -/

/-- The corner chain `{(i, i, i) : i ≤ m}` — vertex-connected, ℓ₁-diameter
exactly `3m`, perimeter exactly `6(m+1)`: the W30-FLOOR2 bound is TIGHT
(the machine-exact exhibit of w30-fan §1). -/
def diagChain (m : ℕ) : Finset Cell :=
  (Finset.range (m + 1)).image fun i : ℕ => ((i : ℤ), (i : ℤ), (i : ℤ))

/-- Membership in the corner chain. -/
theorem mem_diagChain {m : ℕ} {c : Cell} :
    c ∈ diagChain m ↔ ∃ j : ℕ, c = ((j : ℤ), (j : ℤ), (j : ℤ)) ∧ j ≤ m := by
  simp only [diagChain, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, _, rfl⟩
    exact ⟨j, rfl, by omega⟩
  · rintro ⟨j, rfl, hj⟩
    exact ⟨j, by omega, rfl⟩

/-- The corner chain is vertex-path-connected: the diagonal walk. -/
theorem vtxConnected_diagChain (m : ℕ) :
    ∀ u ∈ diagChain m, ∀ v ∈ diagChain m, VtxPath (diagChain m) u v := by
  intro u hu v hv
  obtain ⟨i, rfl, hi⟩ := mem_diagChain.mp hu
  obtain ⟨j, rfl, hj⟩ := mem_diagChain.mp hv
  rcases Nat.le_total i j with hle | hge
  · -- the up-walk `(min (i + t) j, …)`
    have hle' : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hle
    refine ⟨j - i, fun t => ((min ((i : ℤ) + (t : ℤ)) ((j : ℤ))), min ((i : ℤ) + (t : ℤ))
      ((j : ℤ)), min ((i : ℤ) + (t : ℤ)) ((j : ℤ))), ?_, ?_, ?_, ?_⟩
    · simp [min_eq_left hle']
    · have hsub : (((j - i : ℕ) : ℤ)) = (j : ℤ) - (i : ℤ) := Nat.cast_sub hle
      have hsum : ((i : ℤ) + ((j - i : ℕ) : ℤ)) = ((j : ℤ)) := by
        rw [hsub]; linarith
      have hm : min ((i : ℤ) + ((j - i : ℕ) : ℤ)) ((j : ℤ)) = (j : ℤ) := by
        rw [hsum]; exact min_eq_left le_rfl
      simpa using hm
    · intro t ht
      refine mem_diagChain.mpr
        ⟨(min ((i : ℤ) + (t : ℤ)) ((j : ℤ))).toNat, ?_, ?_⟩
      · simp only [Int.toNat_of_nonneg
          (show (0 : ℤ) ≤ min ((i : ℤ) + (t : ℤ)) ((j : ℤ)) by omega)]
      · omega
    · intro t ht
      have hcast : ((i : ℤ) + ((t + 1 : ℕ) : ℤ))
          = ((i : ℤ) + (t : ℤ)) + 1 := by push_cast; ring
      show vtxAdj _ _
      simp only []
      rw [hcast]
      exact ⟨min_step _ _, min_step _ _, min_step _ _⟩
  · -- the down-walk `(max (i - t) j, …)`
    have hge' : (j : ℤ) ≤ (i : ℤ) := by exact_mod_cast hge
    refine ⟨i - j, fun t => ((max ((i : ℤ) - (t : ℤ)) ((j : ℤ))), max ((i : ℤ) - (t : ℤ))
      ((j : ℤ)), max ((i : ℤ) - (t : ℤ)) ((j : ℤ))), ?_, ?_, ?_, ?_⟩
    · simp [max_eq_left hge']
    · have hsub : (((i - j : ℕ) : ℤ)) = (i : ℤ) - (j : ℤ) := Nat.cast_sub hge
      have hsum : ((i : ℤ) - ((i - j : ℕ) : ℤ)) = ((j : ℤ)) := by
        rw [hsub]; linarith
      have hm : max ((i : ℤ) - ((i - j : ℕ) : ℤ)) ((j : ℤ)) = (j : ℤ) := by
        rw [hsum]; exact max_eq_right le_rfl
      simpa using hm
    · intro t ht
      refine mem_diagChain.mpr
        ⟨(max ((i : ℤ) - (t : ℤ)) ((j : ℤ))).toNat, ?_, ?_⟩
      · simp only [Int.toNat_of_nonneg
          (show (0 : ℤ) ≤ max ((i : ℤ) - (t : ℤ)) ((j : ℤ)) by omega)]
      · omega
    · intro t ht
      have hcast : ((i : ℤ) - ((t + 1 : ℕ) : ℤ))
          = ((i : ℤ) - (t : ℤ)) - 1 := by push_cast; ring
      show vtxAdj _ _
      simp only []
      rw [hcast]
      exact ⟨max_step _ _, max_step _ _, max_step _ _⟩

/-- The corner chain has exactly `m + 1` cells. -/
theorem card_diagChain (m : ℕ) : (diagChain m).card = m + 1 := by
  rw [diagChain, Finset.card_image_of_injective _ (fun j k h => by
    simp only [Prod.mk.injEq] at h
    exact Nat.cast_injective h.1), Finset.card_range]

/-- Every cell of the corner chain is isolated (diagonal neighbors share
no face), so the chain's perimeter is EXACTLY `6(m+1)`. -/
theorem perimeter_diagChain (m : ℕ) : perimeter (diagChain m) = 6 * (m + 1) := by
  classical
  have hexcl : ∀ (j : ℕ) (d : Cell), d ∈ dirs →
      addDir ((j : ℤ), (j : ℤ), (j : ℤ)) d ∉ diagChain m := by
    intro j d hd hmem
    obtain ⟨j', heq, -⟩ := mem_diagChain.mp hmem
    simp only [addDir, Prod.mk.injEq] at heq
    obtain ⟨t1, t2, t3⟩ := dirs_bdd hd
    obtain ⟨e1, e2, e3⟩ := heq
    rcases dirs_axis hd with h | h | h
    · omega
    · omega
    · omega
  have hcell : ∀ c ∈ diagChain m,
      ∑ d ∈ dirs, (if addDir c d ∈ diagChain m then 0 else 1) = 6 := by
    intro c hc
    obtain ⟨j, rfl, hj⟩ := mem_diagChain.mp hc
    have hall : ∀ d ∈ dirs,
        (if addDir ((j : ℤ), (j : ℤ), (j : ℤ)) d ∈ diagChain m then 0 else 1) = 1 :=
      fun d hd => by simp [hexcl j d hd]
    rw [Finset.sum_congr rfl (fun d hd => hall d hd), Finset.sum_const,
      smul_eq_mul, card_dirs]
  calc perimeter (diagChain m)
      = ∑ c ∈ diagChain m,
          ∑ d ∈ dirs, (if addDir c d ∈ diagChain m then 0 else 1) := rfl
    _ = ∑ _c ∈ diagChain m, 6 := Finset.sum_congr rfl (fun c hc => hcell c hc)
    _ = 6 * (diagChain m).card := by
        rw [Finset.sum_const, smul_eq_mul]; ring
    _ = 6 * (m + 1) := by rw [card_diagChain]

/-- The ℓ₁-diameter of the corner chain is exactly `3m`. -/
theorem l1diam_diagChain (m : ℕ) : l1diam (diagChain m) = 3 * m := by
  have hle : l1diam (diagChain m) ≤ 3 * m := by
    refine l1diam_le_of_forall _ _ (fun u hu v hv => ?_)
    obtain ⟨i, rfl, hi⟩ := mem_diagChain.mp hu
    obtain ⟨j, rfl, hj⟩ := mem_diagChain.mp hv
    have hsub : ((i : ℤ), (i : ℤ), (i : ℤ)) - ((j : ℤ), (j : ℤ), (j : ℤ))
        = ((i - j : ℤ), (i - j : ℤ), (i - j : ℤ)) := rfl
    rw [hsub]
    simp only [n1n]
    omega
  have hge : 3 * m ≤ l1diam (diagChain m) := by
    have h0 : ((0 : ℤ), (0 : ℤ), (0 : ℤ)) ∈ diagChain m := by
      rw [mem_diagChain]; exact ⟨0, rfl, Nat.zero_le _⟩
    have hm : ((m : ℤ), (m : ℤ), (m : ℤ)) ∈ diagChain m := by
      rw [mem_diagChain]; exact ⟨m, rfl, Nat.le_refl _⟩
    have h1 := le_l1diam_of_mem (A := diagChain m) h0 hm
    have h2 : n1n (((0 : ℤ), (0 : ℤ), (0 : ℤ)) - ((m : ℤ), (m : ℤ), (m : ℤ))) = 3 * m := by
      have hz : ((0 : ℤ), (0 : ℤ), (0 : ℤ)) - ((m : ℤ), (m : ℤ), (m : ℤ))
          = (0 - (m : ℤ), 0 - (m : ℤ), 0 - (m : ℤ)) := rfl
      rw [hz]
      simp only [n1n]
      omega
    rw [h2] at h1
    omega
  omega

/-- **W30-FLOOR2 tightness** (w30-fan §1): the corner chain `(i,i,i)`,
`i = 0..m`, is a legitimate vertex-connected cell set with
`perimeter = 2·l1diam + 6` EXACTLY — no uniform improvement of the
W30-FLOOR2 floor (in particular no exponent multiplier above `2` for the
connecting rate) is achievable. -/
theorem w30_floor2_tight (m : ℕ) :
    perimeter (diagChain m) = 2 * l1diam (diagChain m) + 6 := by
  rw [perimeter_diagChain, l1diam_diagChain]; ring

/-! ## Theorem W30-RATE: the doubled connecting floor -/

/-- **Theorem W30-RATE** (geometric core, w30-fan §1) **[W30-RATE]**:
a vertex-path-connected cell set `W` that reaches within halo distance
`1` of both anchors — `x'`, `y' ∈ W` with `n1n (x − x') ≤ 1`,
`n1n (y − y') ≤ 1`, exactly the spanning attachment of a connecting
Mayer-chain union (a face of `x`'s cell in `∂W` forces a cell of `W` at
ℓ₁-distance 1) — has perimeter at least `2d + 2` at `d = |x − y|₁`:
`diam W ≥ d − 2` (triangle inequality through the two halo cells) and
W30-FLOOR2 gives `≥ 2(d − 2) + 6 = 2d + 2`.  This is the floor that
DOUBLES the W29-EF connecting rate; the campaign's corner-chain exhibit
(`w30_floor2_tight`) shows the multiplier `2` cannot be improved for
off-axis pairs. -/
theorem connecting_perimeter_floor (W : Finset Cell) (hne : W.Nonempty)
    (hconn : ∀ u ∈ W, ∀ v ∈ W, VtxPath W u v)
    (x y x' y' : Cell) (hx' : x' ∈ W) (hy' : y' ∈ W)
    (hx : n1n (x - x') ≤ 1) (hy : n1n (y - y') ≤ 1) :
    2 * n1n (x - y) + 2 ≤ perimeter W := by
  have hspan : n1n (x - y)
      ≤ n1n (x - x') + n1n (x' - y') + n1n (y' - y) := by
    have h : x - y = (x - x') + (x' - y') + (y' - y) := by
      ext <;> simp
    rw [h]
    exact n1n_add3 _ _ _
  have hsym : n1n (y' - y) = n1n (y - y') := n1n_sub_comm _ _
  have hchain := le_l1diam_of_mem (A := W) hx' hy'
  have hfloor := perimeter_ge_two_r W hne hconn
  omega

/-- The connecting floor at the ℝ currency (`Mixture.n1`). -/
theorem connecting_perimeter_floor_real (W : Finset Cell) (hne : W.Nonempty)
    (hconn : ∀ u ∈ W, ∀ v ∈ W, VtxPath W u v)
    (x y x' y' : Cell) (hx' : x' ∈ W) (hy' : y' ∈ W)
    (hx : n1 (x - x') ≤ 1) (hy : n1 (y - y') ≤ 1) :
    2 * n1 (x - y) + 2 ≤ (perimeter W : ℝ) := by
  have hxn : n1n (x - x') ≤ 1 := by
    have h1 := n1_eq_n1n (x - x')
    rw [h1] at hx
    exact_mod_cast hx
  have hyn : n1n (y - y') ≤ 1 := by
    have h1 := n1_eq_n1n (y - y')
    rw [h1] at hy
    exact_mod_cast hy
  have h := connecting_perimeter_floor W hne hconn x y x' y' hx' hy' hxn hyn
  rw [n1_eq_n1n]
  exact_mod_cast h

/-! ## The doubled rate law and the [W30-MISS] window arithmetic -/

/-- The W29-EF single rate (w29-count §1): `ν₁ = κ_c − ln F − ε`, the
per-anchor entropy offset of the effective-fan criterion. -/
noncomputable def nuEff (κc F ε : ℝ) : ℝ := κc - Real.log F - ε

/-- The W30-RATE doubled rate law (w30-fan §1):
`ν = 2(κ_c − ln F₀ − ε)` — exactly TWICE the W29-EF rate: every
connecting Mayer-chain union contains the two halo cells, so its
perimeter obeys the W30-FLOOR2 diameter bound at `d − 2`, doubling the
price of `d` in the exponent. -/
noncomputable def nu2 (κc F0 ε : ℝ) : ℝ := 2 * (κc - Real.log F0 - ε)

/-- The doubling identity: `ν = 2·ν₁`. -/
theorem nu2_eq_twice (κc F ε : ℝ) : nu2 κc F ε = 2 * nuEff κc F ε := by
  unfold nu2 nuEff
  ring

/-- The rate is antitone in the fan price `F₀` (a stronger fan can only
raise the rate). -/
theorem nu2_le_of_F0_le {F0 F0' : ℝ} (hpos : 0 < F0) (hle : F0 ≤ F0')
    (κc ε : ℝ) : nu2 κc F0' ε ≤ nu2 κc F0 ε := by
  have hlog : Real.log F0 ≤ Real.log F0' := Real.log_le_log hpos hle
  simp only [nu2]
  linarith

/-- **[W30-MISS] input, abstract form** (the named residue of w30-fan
§4): a tail-fan bound `N(p, n) ≤ A₀ F₀ⁿ` uniform in the anchor `p`, for
every even `n ≥ n₀`, at ANY fixed head `n₀` (the head `n < n₀` is
machine-exact to `n = 30` or fan-tailed into the K constant). -/
def TailFan (N : Cell → ℕ → ℕ) (n0 : ℕ) (A0 F0 : ℝ) : Prop :=
  ∀ (p : Cell) (n : ℕ), n0 ≤ n → Even n → (N p n : ℝ) ≤ A0 * F0 ^ n

/-- Auxiliary: `log 8 < 2.0796` (as in `Window.log_eight_lt`), from
Mathlib's `Real.log_two_lt_d9`. -/
private theorem fan_log_eight_lt : Real.log 8 < 2.0796 := by
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 from by norm_num, Real.log_pow]
    norm_num
  rw [h8]
  linarith

/-- Auxiliary: `2π² > 19.7192` (as in `Window.two_pi_sq_gt`), from
Mathlib's `Real.pi_gt_d2`. -/
private theorem fan_two_pi_sq_gt : (19.7192 : ℝ) < 2 * Real.pi ^ 2 := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hp2 : (3.14 : ℝ) ^ 2 < Real.pi ^ 2 := by nlinarith [Real.pi_pos, hpi]
  nlinarith

/-- **[W30-MISS] bottom-point window check** (w30-fan §3): at the window
bottom `β = 6.618` the doubled rate law `ν = 2(κ_c − ln F₀)`, `κ_c =
2π²/β`, at the fan price `F₀ = 6.093` clears the ascent bar
`0.493·2.40 = 1.1832`: theorem-floor value `ν > 1.8002` (machine value
2.3510).  The banked fan `F₀ = 11` stays sub-bar under the SAME law
(machine: 1.1695, margin −0.0349) — the doubling alone does not close
the window; the tight point of the priced window `[6.618, 8.2319)` is
its top (machine: ν = 1.1815 vs bar 1.1817), which this floor-level
check does not address. -/
theorem w30_rate_clears_bar :
    bar 2.40 < nu2 (2 * Real.pi ^ 2 / 6.618) 6.093 0 := by
  have hlog8 := fan_log_eight_lt
  have hpi2 := fan_two_pi_sq_gt
  have hlogF : Real.log 6.093 < Real.log 8 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hkey : (19.7192 : ℝ) / 6.618 - 2.0796
      < 2 * Real.pi ^ 2 / 6.618 - Real.log 6.093 := by
    have d1 : (19.7192 : ℝ) / 6.618 < 2 * Real.pi ^ 2 / 6.618 :=
      div_lt_div_iff_of_pos_right (by norm_num) |>.mpr hpi2
    linarith
  have e2 : (0.493 : ℝ) * 2.40 < 2 * (19.7192 / 6.618 - 2.0796) := by norm_num
  simp only [bar, nu2]
  rw [sub_zero]
  linarith [mul_lt_mul_of_pos_left hkey (by norm_num : (0 : ℝ) < 2)]

/-- **Theorem W30-MISS-gate** (the conditional assembly, statement tier,
in the `Mixture.w24_ceil` named-input style): IF the anchored-surface
family carries a tail-fan bound at price `F₀ ≤ 6.093` (the [W30-MISS]
ask; ANY head `n₀`), THEN the doubled rate law `ν = 2(κ_c − ln F₀)`
clears the ascent bar `0.493·2.40` at the window bottom `β = 6.618` —
so the analytic passage W29-EF + W30-RATE + banked W28-ASM legs + T-OP
(w29-count §1 / w30-fan §4), which converts the fan into the two-point
decay at exactly this rate, would close the bottom point.  The fan
hypothesis enters as the named conditioning input only; the arithmetic
gate consumes the price alone (the analytic passage itself is the
standing banked step, NOT reproved here — PVO-3D: this is a statement
about the banked-form abelianized image gas consumed by the standing
conditional doors, not an unconditional SU(2) statement). -/
theorem w30_conditional {N : Cell → ℕ → ℕ} {n0 : ℕ} {A0 F0 : ℝ}
    (_hfan : TailFan N n0 A0 F0) (hprice : F0 ≤ 6.093) (hpos : 0 < F0) :
    bar 2.40 < nu2 (2 * Real.pi ^ 2 / 6.618) F0 0 := by
  have hmono := nu2_le_of_F0_le hpos hprice (2 * Real.pi ^ 2 / 6.618) 0
  exact lt_of_lt_of_le w30_rate_clears_bar hmono

/-! ## The W30-FORM germ: the intra/inter-cluster covariance split -/

/-- **Proposition W30-FORM** (statement germ, w30-charge §1) **[W30-FORM]**:
the exact intra/inter-cluster split of a squared amplitude.  For any
finite family of complex amplitudes `W a` with total `W_p = Σ_a W a`
(the support-connected cluster decomposition of the k-gas),
`W_p · star(W_p) = Σ_a W_a star(W_a) + Σ_{a≠b} W_a star(W_b)` (with
`star` the complex conjugation): the DIAGONAL is the walk part `Ŵ_walk`
(the neutrality-stripped profile, zero-mass by w29-T3) and the ENTIRE
mass content of the mid-mode floor is the off-diagonal inter-cluster
charging term `Ŵ_ch`.  (The ensemble layer — `E[·]` over the k-gas and
the W28-DICT substitution — is the campaign's gas machinery and is not
reproduced here.) -/
theorem cov_split {κ : Type*} [Fintype κ] [DecidableEq κ] (W : κ → ℂ) :
    (∑ a, W a) * ∑ b, star (W b)
      = ∑ a, W a * star (W a)
        + ∑ a, ∑ b ∈ Finset.univ.erase a, W a * star (W b) := by
  classical
  have key : ∀ a : κ, ∑ b ∈ Finset.univ, W a * star (W b)
      = W a * star (W a)
        + ∑ b ∈ Finset.univ.erase a, W a * star (W b) := by
    intro a
    have h := Finset.add_sum_erase (s := (Finset.univ : Finset κ))
      (f := fun b => W a * star (W b)) (Finset.mem_univ a)
    exact h.symm
  rw [Finset.sum_mul_sum,
    Finset.sum_congr rfl (fun a _ => key a), Finset.sum_add_distrib]

end YangMills3D

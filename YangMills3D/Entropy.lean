/-
The entropy-impossibility layer (W24-S / W25-N2, Lean form).

SOURCE. `problems/yang-mills-mass-gap/lemmas/w24-cold.md` §1 and the
Gate-16 audit (G16-1: the connected-count over-counted; counting ALL
subsets of the box, as done here, is a superset and is immune). Main
results:

* `animal_family_card`: the box-with-holes family realizes `choose N_s k`
  distinct cell sets with face-perimeter exactly `P_s + 6k`.
* `generating_diverges`: for EVERY `κ > 0` (every fugacity `exp(-κ)`) the
  face-perimeter generating function of the box animals is unbounded.
* `no_exponential_animal_tail`: no uniform exponential entropy tail
  `animalCount s P ≤ C · c^P` — the falsifier of the campaign's W23-Q
  criterion `A(z) < 1` and of w23's V-free upgrade (errata 2026-09-10).
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import YangMills3D.Animals

namespace YangMills3D

/-! ## The even core size -/

theorem card_evens_ge (s : ℕ) : (s - 2) / 2 ≤ (evens s).card := by
  have hsub : (Finset.Icc (1 : ℤ) ((s - 2) / 2)).image (fun m : ℤ => 2 * m) ⊆ evens s := by
    intro a ha
    simp only [Finset.mem_image, Finset.mem_Icc] at ha
    obtain ⟨m, hm, rfl⟩ := ha
    simp only [evens, Finset.mem_filter, Finset.mem_Icc]
    have hq := Nat.div_add_mod (s - 2) 2
    have hr : (s - 2) % 2 < 2 := by omega
    refine ⟨?_, by omega⟩
    omega
  have hinj : Set.InjOn (fun m : ℤ => 2 * m) (Finset.Icc (1 : ℤ) ((s - 2) / 2)) := by
    intro a _ b _ hab
    have hab' : (fun m : ℤ => 2 * m) a = (fun m : ℤ => 2 * m) b := hab
    simp only at hab'
    omega
  have hcard : ((Finset.Icc (1 : ℤ) ((s - 2) / 2)).image (fun m : ℤ => 2 * m)).card
      = (Finset.Icc (1 : ℤ) ((s - 2) / 2)).card := Finset.card_image_of_injOn hinj
  have hicc : (Finset.Icc (1 : ℤ) ((s - 2) / 2)).card = (s - 2) / 2 := by
    rw [Int.card_Icc]; omega
  rw [← hicc, ← hcard]
  exact Finset.card_le_card hsub

theorem card_evenCore_ge (s : ℕ) : ((s - 2) / 2)^3 ≤ (evenCore s).card := by
  have h := card_evens_ge s
  have h3 : ((s - 2) / 2)^3 ≤ (evens s).card * (evens s).card * (evens s).card := by
    have hp := Nat.pow_le_pow_left h
    calc ((s - 2) / 2)^3 ≤ ((evens s).card)^3 := hp 3
      _ = (evens s).card * (evens s).card * (evens s).card := by ring
  calc ((s - 2) / 2)^3 ≤ (evens s).card * (evens s).card * (evens s).card := h3
    _ = (evenCore s).card := by
        rw [evenCore, Finset.card_product, Finset.card_product]
        ring

/-! ## The family count -/

/-- Number of finite cell subsets of the `s`-box with face-perimeter `P`
(a SUPERSET of the connected solid animals: no connectivity required,
which by Gate-16 G16-1 only strengthens the impossibility results). -/
def animalCount (s P : ℕ) : ℕ := ((box s).powerset.filter (fun A => perimeter A = P)).card

private lemma sdiff_recover {s H : Finset Cell} (hH : H ⊆ s) : s \ (s \ H) = H := by
  ext x
  simp only [Finset.mem_sdiff]
  by_cases hx : x ∈ H
  · simp [hx, hH hx]
  · simp [hx]

private lemma family_inj (s k : ℕ) :
    Set.InjOn (fun H : Finset Cell => box s \ H) (↑((evenCore s).powersetCard k)) := by
  intro H₁ hH₁ H₂ hH₂ hhe
  have hhe' : box s \ H₁ = box s \ H₂ := hhe
  obtain ⟨h₁, -⟩ := Finset.mem_powersetCard.mp (Finset.mem_coe.mp hH₁)
  obtain ⟨h₂, -⟩ := Finset.mem_powersetCard.mp (Finset.mem_coe.mp hH₂)
  have hb1 : H₁ ⊆ box s := Finset.Subset.trans h₁ (evenCore_subset_box s)
  have hb2 : H₂ ⊆ box s := Finset.Subset.trans h₂ (evenCore_subset_box s)
  calc H₁ = box s \ (box s \ H₁) := (sdiff_recover hb1).symm
    _ = box s \ (box s \ H₂) := by rw [hhe']
    _ = H₂ := sdiff_recover hb2

/-- **The family count bound** (W24-A's binomial lower bound, Lean form). -/
theorem animal_family_card (s k : ℕ) :
    Nat.choose (evenCore s).card k ≤ animalCount s (perimeter (box s) + 6 * k) := by
  classical
  have hmem : ∀ H ∈ (evenCore s).powersetCard k,
      box s \ H ∈ (box s).powerset.filter (fun A => perimeter A = perimeter (box s) + 6 * k) := by
    intro H hH
    obtain ⟨hHsub, hHcard⟩ := Finset.mem_powersetCard.mp hH
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    rw [perimeter_box_sdiff hHsub, hHcard]
  have h0 : Nat.choose (evenCore s).card k = ((evenCore s).powersetCard k).card :=
    (Finset.card_powersetCard k (evenCore s)).symm
  calc Nat.choose (evenCore s).card k = ((evenCore s).powersetCard k).card := h0
    _ = (((evenCore s).powersetCard k).image (fun H => box s \ H)).card :=
        (Finset.card_image_of_injOn (family_inj s k)).symm
    _ ≤ ((box s).powerset.filter (fun A => perimeter A = perimeter (box s) + 6 * k)).card :=
        Finset.card_le_card
          (Finset.image_subset_iff.mpr (fun H hH => hmem H hH))
    _ = animalCount s (perimeter (box s) + 6 * k) := rfl

/-! ## Exponential and geometric helpers -/

private lemma exp_pow (a : ℝ) (n : ℕ) : Real.exp a ^ n = Real.exp ((n:ℝ) * a) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← Real.exp_add]; congr 1; push_cast; ring

private lemma pow_eq_exp_log {x : ℝ} (hx : 0 < x) (n : ℕ) :
    x^n = Real.exp ((n:ℝ) * Real.log x) := by
  have h1 : x^n = (Real.exp (Real.log x))^n := by rw [Real.exp_log hx]
  rw [h1, exp_pow]

private lemma cube_ge_self {s : ℝ} (hs : 1 ≤ s) : s ≤ s^3 := by
  have hr : s^3 - s = s * ((s - 1) * (s + 1)) := by ring
  have hnn : (0:ℝ) ≤ s * ((s - 1) * (s + 1)) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  linarith

private lemma cubic_dom (L : ℝ) (hL : 0 < L) (κ B : ℝ) :
    ∃ S : ℕ, ∀ s : ℕ, S ≤ s →
      B + 12 * κ * (s:ℝ)^2 ≤ (s:ℝ)^3 * L / 64 := by
  obtain ⟨S₁, hS₁⟩ := exists_nat_gt (max 1 (128 * B / L))
  obtain ⟨S₂, hS₂⟩ := exists_nat_gt (max 1 (1536 * κ / L))
  refine ⟨max S₁ S₂, fun s hs => ?_⟩
  have hS₁s : (S₁ : ℝ) ≤ (s:ℝ) := by
    have h1 : ((S₁ : ℕ):ℝ) ≤ ((max S₁ S₂ : ℕ):ℝ) := by
      exact_mod_cast (Nat.le_max_left S₁ S₂)
    have h2 : ((max S₁ S₂ : ℕ):ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
    linarith
  have hS₂s : (S₂ : ℝ) ≤ (s:ℝ) := by
    have h1 : ((S₂ : ℕ):ℝ) ≤ ((max S₁ S₂ : ℕ):ℝ) := by
      exact_mod_cast (Nat.le_max_right S₁ S₂)
    have h2 : ((max S₁ S₂ : ℕ):ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
    linarith
  have hmax1 : (max 1 (128 * B / L) : ℝ) < (s:ℝ) := by
    have h1 : (max 1 (128 * B / L) : ℝ) < ((S₁ : ℕ):ℝ) := by exact_mod_cast hS₁
    linarith
  have hmax2 : (max 1 (1536 * κ / L) : ℝ) < (s:ℝ) := by
    have h1 : (max 1 (1536 * κ / L) : ℝ) < ((S₂ : ℕ):ℝ) := by exact_mod_cast hS₂
    linarith
  have hs1 : (1:ℝ) ≤ (s:ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hmax1)
  have hge : (s:ℝ) ≤ (s:ℝ)^3 := cube_ge_self hs1
  have hstep2 : (s:ℝ) * L / 128 ≤ (s:ℝ)^3 * L / 128 := by
    have hd : (0:ℝ) ≤ (s:ℝ)^3 - (s:ℝ) := sub_nonneg.mpr hge
    have hp : (0:ℝ) ≤ ((s:ℝ)^3 - (s:ℝ)) * (L / 128) :=
      mul_nonneg hd (div_nonneg hL.le (by norm_num : (0:ℝ) ≤ 128))
    have he : ((s:ℝ)^3 - (s:ℝ)) * (L / 128)
        = (s:ℝ)^3 * L / 128 - (s:ℝ) * L / 128 := by ring
    linarith
  have hB : B ≤ (s:ℝ)^3 * L / 128 := by
    have hpos : (0:ℝ) ≤ (s:ℝ)^3 * L / 128 := by positivity
    rcases lt_trichotomy B 0 with hB0 | hB0 | hB0
    · linarith
    · have hle : (128 * B / L) ≤ (s:ℝ) := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hmax1)
      have hB' : B ≤ (s:ℝ) * L / 128 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 128)]
        linarith [(div_le_iff₀ hL).mp hle]
      exact le_trans hB' hstep2
    · have hle : (128 * B / L) ≤ (s:ℝ) := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hmax1)
      have hB' : B ≤ (s:ℝ) * L / 128 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 128)]
        linarith [(div_le_iff₀ hL).mp hle]
      exact le_trans hB' hstep2
  have hκ : 12 * κ * (s:ℝ)^2 ≤ (s:ℝ)^3 * L / 128 := by
    have hpos : (0:ℝ) ≤ (s:ℝ)^3 * L / 128 := by positivity
    rcases lt_trichotomy κ 0 with hκ0 | hκ0 | hκ0
    · have h12 : (12:ℝ) * κ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num) hκ0.le
      have hle0 : 12 * κ * (s:ℝ)^2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h12 (sq_nonneg (s:ℝ))
      linarith
    · rw [hκ0, mul_zero, zero_mul]
      exact hpos
    · have hle : (1536 * κ / L) ≤ (s:ℝ) := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hmax2)
      have h12 : (12:ℝ) * κ ≤ (s:ℝ) * L / 128 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 128)]
        linarith [(div_le_iff₀ hL).mp hle]
      linarith [mul_le_mul_of_nonneg_right h12 (sq_nonneg (s:ℝ))]
  have hsum := add_le_add hB hκ
  have hfin : (s:ℝ)^3 * L / 128 + (s:ℝ)^3 * L / 128 = (s:ℝ)^3 * L / 64 := by ring
  linarith

private lemma geom_sum_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, r^i ≤ 1 / (1 - r) := by
  induction n with
  | zero =>
    rw [Finset.sum_range_zero]
    exact div_nonneg zero_le_one (by linarith)
  | succ n ih =>
    rw [Finset.sum_range_succ', pow_zero]
    have hterm : ∑ i ∈ Finset.range n, r^(i+1) = r * ∑ i ∈ Finset.range n, r^i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => (pow_succ r i).trans (mul_comm (r^i) r)
    rw [hterm]
    have hmul := mul_le_mul_of_nonneg_left ih hr0
    have hcalc : (1:ℝ) + r * (1 / (1 - r)) = 1 / (1 - r) := by
      have hne : (1:ℝ) - r ≠ 0 := by intro h; linarith
      field_simp
      ring
    linarith

/-! ## The binomial-family lower bound -/

/-- The generating function of the box animals dominates the binomial sum
over the even-core hole family. -/
theorem box_gen_ge_binomial (κ : ℝ) (s : ℕ) :
    ∑ i ∈ Finset.range ((evenCore s).card + 1),
        (Nat.choose (evenCore s).card i : ℝ) * Real.exp (-κ * ((perimeter (box s) + 6*i : ℕ):ℝ))
      ≤ ∑ A ∈ (box s).powerset, Real.exp (-(κ:ℝ) * (perimeter A : ℝ)) := by
  classical
  set N := (evenCore s).card with hN
  have hval : ∀ k : ℕ, ∀ A ∈ ((evenCore s).powersetCard k).image (fun H => box s \ H),
      perimeter A = perimeter (box s) + 6 * k := by
    intro k A hA
    simp only [Finset.mem_image] at hA
    obtain ⟨H, hH, rfl⟩ := hA
    obtain ⟨hHsub, hHcard⟩ := Finset.mem_powersetCard.mp hH
    rw [perimeter_box_sdiff hHsub, hHcard]
  have himg : ∀ k ∈ Finset.range (N + 1),
      ∀ A ∈ ((evenCore s).powersetCard k).image (fun H => box s \ H), A ∈ (box s).powerset := by
    intro k _ A hA
    simp only [Finset.mem_image] at hA
    obtain ⟨H, hH, rfl⟩ := hA
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  have hdisj : ∀ k₁ ∈ Finset.range (N + 1), ∀ k₂ ∈ Finset.range (N + 1), k₁ ≠ k₂ →
      Disjoint (((evenCore s).powersetCard k₁).image (fun H => box s \ H))
        (((evenCore s).powersetCard k₂).image (fun H => box s \ H)) := by
    intro k₁ hk₁ k₂ hk₂ hne
    refine Finset.disjoint_left.mpr fun A hA₁ hA₂ => ?_
    have e₁ := hval k₁ A hA₁
    have e₂ := hval k₂ A hA₂
    exact hne (by omega)
  have hperk : ∀ k ∈ Finset.range (N + 1),
      ∑ A ∈ ((evenCore s).powersetCard k).image (fun H => box s \ H),
          Real.exp (-(κ:ℝ) * (perimeter A : ℝ))
        = (Nat.choose N k : ℝ) * Real.exp (-κ * ((perimeter (box s) + 6*k : ℕ):ℝ)) := by
    intro k _
    have hcard : (((evenCore s).powersetCard k).image (fun H => box s \ H)).card
        = Nat.choose N k := by
      rw [hN, Finset.card_image_of_injOn (family_inj s k), Finset.card_powersetCard]
    have hconst : ∀ A ∈ ((evenCore s).powersetCard k).image (fun H => box s \ H),
        Real.exp (-(κ:ℝ) * (perimeter A : ℝ))
          = Real.exp (-κ * ((perimeter (box s) + 6*k : ℕ):ℝ)) := by
      intro A hA
      rw [hval k A hA]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, hcard]
  have hpw : Set.PairwiseDisjoint (↑(Finset.range (N + 1)) : Set ℕ)
      (fun k => ((evenCore s).powersetCard k).image (fun H => box s \ H)) :=
    fun a ha b hb hab => hdisj a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab
  have hbunion := Finset.sum_biUnion (s := Finset.range (N + 1))
    (t := fun k => ((evenCore s).powersetCard k).image (fun H => box s \ H))
    (f := fun A => Real.exp (-(κ:ℝ) * (perimeter A : ℝ))) hpw
  have hsub : (Finset.range (N + 1)).biUnion
      (fun k => ((evenCore s).powersetCard k).image (fun H => box s \ H)) ⊆ (box s).powerset := by
    intro A hA
    simp only [Finset.mem_biUnion] at hA
    obtain ⟨k, hk, hAk⟩ := hA
    exact himg k hk A hAk
  calc ∑ i ∈ Finset.range (N + 1),
        (Nat.choose N i : ℝ) * Real.exp (-κ * ((perimeter (box s) + 6*i : ℕ):ℝ))
      = ∑ k ∈ Finset.range (N + 1),
          ∑ A ∈ ((evenCore s).powersetCard k).image (fun H => box s \ H),
            Real.exp (-(κ:ℝ) * (perimeter A : ℝ)) :=
        Finset.sum_congr rfl fun k hk => (hperk k hk).symm
    _ = ∑ A ∈ (Finset.range (N + 1)).biUnion
          (fun k => ((evenCore s).powersetCard k).image (fun H => box s \ H)),
            Real.exp (-(κ:ℝ) * (perimeter A : ℝ)) := hbunion.symm
    _ ≤ ∑ A ∈ (box s).powerset, Real.exp (-(κ:ℝ) * (perimeter A : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun A _ _ => Real.exp_nonneg _

/-! ## Divergence at every fugacity -/

private lemma evenCore_cast_ge (s : ℕ) (hs : 12 ≤ s) :
    (s:ℝ)^3 / 64 ≤ ((evenCore s).card : ℝ) := by
  have h1 : s / 3 ≤ (s - 2) / 2 := by omega
  have h2 : (s / 3)^3 ≤ ((s - 2) / 2)^3 := Nat.pow_le_pow_left h1 3
  have h3 : ((s - 2) / 2)^3 ≤ (evenCore s).card := card_evenCore_ge s
  have hnat : (s / 3)^3 ≤ (evenCore s).card := le_trans h2 h3
  have hq1 : s % 3 < 3 := Nat.mod_lt s (by omega)
  have hdm : 3 * (s / 3) + s % 3 = s := Nat.div_add_mod s 3
  have h4 : (s:ℝ)/3 ≤ ((s / 3 : ℕ):ℝ) + 1 := by
    have hc : (3:ℝ) * ((s/3:ℕ):ℝ) + ((s%3:ℕ):ℝ) = (s:ℝ) := by exact_mod_cast hdm
    have hr3 : ((s%3:ℕ):ℝ) < 3 := by exact_mod_cast hq1
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 3)]
    linarith
  have h5 : (s:ℝ)/4 ≤ (s:ℝ)/3 - 1 := by
    have hsR : (s:ℝ) ≥ 12 := by exact_mod_cast hs
    linarith
  have h6 : ((s:ℝ)/4)^3 ≤ ((s / 3 : ℕ):ℝ)^3 := by
    have hz : (0:ℝ) ≤ (s:ℝ)/3 - 1 := by linarith
    calc ((s:ℝ)/4)^3 ≤ ((s:ℝ)/3 - 1)^3 := pow_le_pow_left₀ (by linarith) h5 3
      _ ≤ ((s / 3 : ℕ):ℝ)^3 := pow_le_pow_left₀ hz (by linarith) 3
  have h7 : ((s:ℝ)/4)^3 = (s:ℝ)^3 / 64 := by rw [div_pow]; norm_num
  calc (s:ℝ)^3 / 64 = ((s:ℝ)/4)^3 := h7.symm
    _ ≤ ((s / 3 : ℕ):ℝ)^3 := h6
    _ ≤ ((evenCore s).card : ℝ) := by exact_mod_cast hnat

/-- **Divergence at every fugacity** (σ₃ = +∞, Lean form): for every
`κ > 0` the face-perimeter generating function of the box animals is
unbounded in the box size. -/
theorem generating_diverges (κ : ℝ) (hκ : 0 < κ) (M : ℝ) :
    ∃ s : ℕ, M < ∑ A ∈ (box s).powerset, Real.exp (-(κ:ℝ) * (perimeter A : ℝ)) := by
  classical
  rcases le_or_gt M 0 with hM | hM
  · refine ⟨1, ?_⟩
    have hsingle : (1:ℝ) ≤ ∑ A ∈ (box 1).powerset, Real.exp (-(κ:ℝ) * (perimeter A : ℝ)) := by
      have hsub : ({∅} : Finset (Finset Cell)) ⊆ (box 1).powerset := by
        intro A hA
        simp only [Finset.mem_singleton] at hA
        rw [hA]
        exact Finset.mem_powerset.mpr (Finset.empty_subset _)
      have hval : Real.exp (-(κ:ℝ) * (perimeter (∅ : Finset Cell) : ℝ)) = 1 := by
        have h0 : perimeter (∅ : Finset Cell) = 0 := by simp [perimeter]
        rw [h0, Nat.cast_zero, mul_zero, Real.exp_zero]
      have hsum : ∑ A ∈ ({∅} : Finset (Finset Cell)),
          Real.exp (-(κ:ℝ) * (perimeter A : ℝ)) = 1 := by
        rw [Finset.sum_singleton, hval]
      calc (1:ℝ) = ∑ A ∈ ({∅} : Finset (Finset Cell)),
            Real.exp (-(κ:ℝ) * (perimeter A : ℝ)) := hsum.symm
        _ ≤ ∑ A ∈ (box 1).powerset, Real.exp (-(κ:ℝ) * (perimeter A : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun A _ _ => Real.exp_nonneg _
    linarith
  set y := Real.exp (6 * -κ) with hy
  have hy0 : (0:ℝ) < y := Real.exp_pos _
  have hL : (0:ℝ) < Real.log (1 + y) := by
    apply Real.log_pos
    have : (1:ℝ) < 1 + y := by linarith
    linarith
  obtain ⟨S, hS⟩ := cubic_dom (Real.log (1 + y)) hL κ (Real.log M + 1)
  obtain ⟨T, hT⟩ := exists_nat_gt (max 12 S)
  have hT12 : (12:ℕ) ≤ T := le_trans (Nat.le_max_left 12 S) hT.le
  have hT1 : (1:ℕ) ≤ T := by omega
  have hTS : (S:ℕ) ≤ T := le_trans (Nat.le_max_right 12 S) hT.le
  refine ⟨T, ?_⟩
  have hbin : ∑ i ∈ Finset.range (((evenCore T).card : ℕ) + 1),
        ((Nat.choose ((evenCore T).card) i : ℝ) * y^i)
      = (1 + y)^(evenCore T).card := by
    have hflip : (1:ℝ) + y = y + 1 := by ring
    rw [hflip, add_pow]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [one_pow, mul_one]
    exact mul_comm _ _
  have hterm : ∀ i : ℕ,
      Real.exp (-κ * ((perimeter (box T) + 6*i : ℕ) : ℝ))
        = Real.exp (-κ * ((perimeter (box T) : ℝ))) * y^i := by
    intro i
    have hc : ((perimeter (box T) + 6*i : ℕ) : ℝ) = ((perimeter (box T) : ℝ) + 6*i) := by
      push_cast
      ring
    rw [hc]
    have hsplit : (-κ:ℝ) * ((perimeter (box T) : ℝ) + 6*i)
        = (-κ) * ((perimeter (box T) : ℝ)) + (i:ℝ) * (6 * -κ) := by ring
    rw [hsplit, Real.exp_add, ← exp_pow (6 * -κ) i, ← hy]
  have hconv : ∑ i ∈ Finset.range (((evenCore T).card : ℕ) + 1),
        ((Nat.choose ((evenCore T).card) i : ℝ)
          * Real.exp (-κ * ((perimeter (box T) + 6*i : ℕ) : ℝ)))
      = Real.exp (-κ * ((perimeter (box T) : ℝ))) * (1 + y)^(evenCore T).card := by
    have hstep : ∀ i ∈ Finset.range (((evenCore T).card : ℕ) + 1),
        (Nat.choose ((evenCore T).card) i : ℝ)
            * Real.exp (-κ * ((perimeter (box T) + 6*i : ℕ) : ℝ))
          = Real.exp (-κ * ((perimeter (box T) : ℝ)))
              * ((Nat.choose ((evenCore T).card) i : ℝ) * y^i) := by
      intro i _
      rw [hterm i]
      ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, hbin]
  have hlow1 : (1 + y)^(evenCore T).card * Real.exp (-κ * ((perimeter (box T) : ℝ)))
      ≤ ∑ A ∈ (box T).powerset, Real.exp (-(κ:ℝ) * (perimeter A : ℝ)) := by
    rw [mul_comm, ← hconv]
    exact box_gen_ge_binomial κ T
  have hNlow := evenCore_cast_ge T hT12
  have hNcast : ((T:ℝ)^3 * Real.log (1 + y) / 64)
      ≤ ((evenCore T).card : ℝ) * Real.log (1 + y) := by
    nlinarith [hNlow, hL]
  have hexp1 : Real.exp ((T:ℝ)^3 * Real.log (1 + y) / 64) ≤ (1 + y)^(evenCore T).card := by
    rw [pow_eq_exp_log (by linarith : (0:ℝ) < 1 + y)]
    exact Real.exp_le_exp.mpr hNcast
  have hPle : (perimeter (box T) : ℝ) ≤ 12 * (T:ℝ)^2 := by
    have hPcast : (perimeter (box T) : ℝ) ≤ ((12 * T * T : ℕ) : ℝ) :=
      by exact_mod_cast perimeter_box_le T hT1
    have hc : ((12 * T * T : ℕ):ℝ) = 12 * (T:ℝ)^2 := by push_cast; ring
    rw [hc] at hPcast
    exact hPcast
  have hexp2 : Real.exp (-12 * κ * (T:ℝ)^2)
      ≤ Real.exp (-κ * ((perimeter (box T) : ℝ))) := by
    refine Real.exp_le_exp.mpr ?_
    have hκnn : (0:ℝ) ≤ κ := le_of_lt hκ
    have hPm : (perimeter (box T) : ℝ) * κ ≤ 12 * (T:ℝ)^2 * κ :=
      mul_le_mul_of_nonneg_right hPle hκnn
    nlinarith
  have hfinal := hS T hTS
  have hMexp : Real.exp (Real.log M + 1) = M * Real.exp 1 := by
    rw [Real.exp_add, Real.exp_log hM]
  calc M = M * 1 := by ring
    _ < M * Real.exp 1 := by
        apply mul_lt_mul_of_pos_left _ hM
        exact Real.one_lt_exp_iff.mpr (by norm_num)
    _ = Real.exp (Real.log M + 1) := hMexp.symm
    _ ≤ Real.exp ((T:ℝ)^3 * Real.log (1 + y) / 64 - 12 * κ * (T:ℝ)^2) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp ((T:ℝ)^3 * Real.log (1 + y) / 64) * Real.exp (-12 * κ * (T:ℝ)^2) := by
        rw [← Real.exp_add, sub_eq_add_neg]
        congr 1
        ring
    _ ≤ (1 + y)^(evenCore T).card * Real.exp (-κ * ((perimeter (box T) : ℝ))) :=
        mul_le_mul hexp1 hexp2 (Real.exp_nonneg _) (pow_nonneg (by linarith) _)
    _ ≤ ∑ A ∈ (box T).powerset, Real.exp (-(κ:ℝ) * (perimeter A : ℝ)) := hlow1

/-- **No exponential animal-entropy tail** — the Lean form of the
falsification of the campaign's W23-Q criterion: there are no constants
`C > 0`, `c > 1` with `animalCount s P ≤ C · c^P` for all boxes `s` and
perimeters `P`. -/
theorem no_exponential_animal_tail :
    ¬ ∃ C c : ℝ, 0 < C ∧ 1 < c ∧ ∀ s P : ℕ, (animalCount s P : ℝ) ≤ C * c ^ P := by
  rintro ⟨C, c, hC, hc, hbound⟩
  have hcpos : (0:ℝ) < c := by linarith
  set κ := Real.log c + 1 with hκdef
  have hκ : (0:ℝ) < κ := by
    have hlog := Real.log_pos hc
    linarith
  have hunit : c * Real.exp (-κ) < 1 := by
    have h1 : Real.exp (-κ) * c = Real.exp (-1) := by
      rw [hκdef, neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hcpos,
        mul_comm (c⁻¹) (Real.exp (-1)), inv_mul_cancel_right₀ (ne_of_gt hcpos)]
    have h2 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    rw [mul_comm, h1]
    exact h2
  have hupper : ∀ s : ℕ, ∑ A ∈ (box s).powerset, Real.exp (-(κ:ℝ) * (perimeter A : ℝ))
      ≤ C / (1 - c * Real.exp (-κ)) := by
    intro s
    have hfib : ∑ A ∈ (box s).powerset, Real.exp (-(κ:ℝ) * (perimeter A : ℝ))
        = ∑ P ∈ ((box s).powerset.image perimeter),
            ∑ A ∈ ((box s).powerset.filter (fun B => perimeter B = P)),
              Real.exp (-(κ:ℝ) * (perimeter A : ℝ)) :=
      (Finset.sum_fiberwise_of_maps_to (fun A hA => Finset.mem_image_of_mem perimeter hA)
        (fun A => Real.exp (-(κ:ℝ) * (perimeter A : ℝ)))).symm
    rw [hfib]
    have hconst : ∀ P ∈ ((box s).powerset.image perimeter),
        ∑ A ∈ ((box s).powerset.filter (fun B => perimeter B = P)),
            Real.exp (-(κ:ℝ) * (perimeter A : ℝ))
          = (animalCount s P : ℝ) * Real.exp (-(κ:ℝ) * (P:ℝ)) := by
      intro P _
      have hpoint : ∀ A ∈ ((box s).powerset.filter (fun B => perimeter B = P)),
          Real.exp (-(κ:ℝ) * (perimeter A : ℝ)) = Real.exp (-(κ:ℝ) * (P:ℝ)) := by
        intro A hA
        simp only [Finset.mem_filter] at hA
        rw [hA.2]
      rw [Finset.sum_congr rfl hpoint, Finset.sum_const, nsmul_eq_mul]
      rfl
    rw [Finset.sum_congr rfl hconst]
    have hsplit : ∀ P : ℕ, c^P * Real.exp (-(κ:ℝ) * (P:ℝ))
        = (c * Real.exp (-(κ:ℝ)))^P := by
      intro P
      rw [mul_pow]
      congr 1
      symm
      rw [exp_pow (-(κ:ℝ)) P]
      congr 1
      ring
    have hper : ∀ P ∈ ((box s).powerset.image perimeter),
        (animalCount s P : ℝ) * Real.exp (-(κ:ℝ) * (P:ℝ))
          ≤ C * (c * Real.exp (-(κ:ℝ)))^P := by
      intro P _
      have hb := hbound s P
      calc (animalCount s P : ℝ) * Real.exp (-(κ:ℝ) * (P:ℝ))
          ≤ C * c^P * Real.exp (-(κ:ℝ) * (P:ℝ)) :=
            mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
        _ = C * (c^P * Real.exp (-(κ:ℝ) * (P:ℝ))) := by ring
        _ ≤ C * ((c * Real.exp (-(κ:ℝ)))^P) :=
            mul_le_mul_of_nonneg_left (le_of_eq (hsplit P)) hC.le
    have hPle : ∀ P ∈ ((box s).powerset.image perimeter), P ≤ 6 * (s * s * s) := by
      intro P hP
      simp only [Finset.mem_image] at hP
      obtain ⟨A, hA, hPA⟩ := hP
      have hAcard : A ⊆ box s := Finset.mem_powerset.mp hA
      have h1 := perimeter_le A
      have h2 := Finset.card_le_card hAcard
      have h3 : (box s).card = s * s * s := card_box s
      omega
    have himg : ((box s).powerset.image perimeter) ⊆ Finset.range (6 * (s * s * s) + 1) := by
      intro P hP
      simp only [Finset.mem_range]
      have := hPle P hP
      omega
    calc ∑ P ∈ ((box s).powerset.image perimeter),
            (animalCount s P : ℝ) * Real.exp (-(κ:ℝ) * (P:ℝ))
        ≤ ∑ P ∈ ((box s).powerset.image perimeter), C * (c * Real.exp (-(κ:ℝ)))^P :=
          Finset.sum_le_sum hper
      _ ≤ ∑ P ∈ Finset.range (6 * (s * s * s) + 1), C * (c * Real.exp (-(κ:ℝ)))^P :=
          Finset.sum_le_sum_of_subset_of_nonneg himg
            fun P _ _ =>
              mul_nonneg hC.le (pow_nonneg (mul_nonneg hcpos.le (Real.exp_nonneg _)) P)
      _ = C * ∑ P ∈ Finset.range (6 * (s * s * s) + 1), (c * Real.exp (-(κ:ℝ)))^P := by
          rw [Finset.mul_sum]
      _ ≤ C * (1 / (1 - c * Real.exp (-κ))) := by
          apply mul_le_mul_of_nonneg_left
          · exact geom_sum_le (c * Real.exp (-κ))
              (mul_nonneg hcpos.le (Real.exp_nonneg _)) hunit _
          · linarith
      _ ≤ C / (1 - c * Real.exp (-κ)) := le_of_eq (by rw [mul_one_div])
  obtain ⟨s, hs⟩ := generating_diverges κ hκ (C / (1 - c * Real.exp (-κ)))
  have hupp := hupper s
  have hbound' : (0:ℝ) ≤ C / (1 - c * Real.exp (-κ)) :=
    div_nonneg hC.le (by linarith)
  linarith

end YangMills3D


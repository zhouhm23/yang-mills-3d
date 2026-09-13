/-
The wave-37 fan-ask ladder layer: the needed-price formula and the
window-restoration rungs, Lean form.

SOURCE. `problems/yang-mills-mass-gap/lemmas/w37-mid.md` §0 (the
needed-F0_total table: `needed(β) = e^{κ_c − bar/2 − ε}`) and §4 (the
fan-ask ladder: `F0H ≤ 5.1932` restores `[6.618, 8.2315]`, `≤ 4.2309`
closes to 9, `≤ 3.7688` to 9.5, `≤ 3.3945` to 10; the G25-4 erratum:
the architecture ceiling is `β* = 10.53`–`10.60` and an ask EXISTS at
10.5), reusing `YangMills3D.Fan` (`TailFan`, `nu2`,
`nu2_le_of_F0_le`, the `w30_conditional` pattern) and
`YangMills3D.Window` (`bar`, the ascent budget `0.493·μ` with the
banked corner table: μ = 2.443 at the bottom 6.618, μ = 2.397 on and
past 8.2315).

The ladder is the two-sided price of the standing named obstruction
[W34-MISS]: the k=1-PINCHED tail fan, at machine-measured growth
1.348^n.  The asks are DP-bisected numbers of the W34-MASTER DP (the
campaign's machine step that combines the pinched fan with the banked
manifold branch); the DP is NOT formalized here — its OUTPUT price
enters as the named hypothesis, exactly the `w30_conditional` pattern.

DELIVERED HERE (all fully proved):

  * `nu2_needed_iff` — the EXACT ladder-threshold formula: at the
    doubled rate law the bar is met iff the total fan price is at most
    `exp(κ_c − bar μ / 2 − ε)` (no numerics — the definition of the
    needed-F0_total column of w37-mid §0).
  * `ladder_clears` — the named-input implication: a `TailFan` at a
    price clearing the needed constant delivers `bar μ ≤ ν(β)` at the
    named coupling (window restoration, statement tier).
  * `rung_bottom`, `rung_82315`, `rung_9`, `rung_10` — four numeric
    rungs at ε = 0.02 and rounded POWER-OF-TWO total prices
    8 / 4 / 4 / 2: weaker-but-true stand-ins for the .md's DP-priced
    thresholds (asks `5.1932 / 4.2309 / 3.7688 / 3.3945` on the
    pinched fan, DP totals `5.972 / 4.8665 / 4.3360 / 3.9081`); the
    exact thresholds are machine-priced in w37-mid §4, the implication
    FORM is what is formalized, and any smaller price clears a
    fortiori by `nu2_le_of_F0_le`.

PVO-3D: no unconditional SU(2) statement; the fan is the named
conditioning input on the banked-form image gas.

Every statement below is fully proved: no unfinished proofs, no new
axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import YangMills3D.Fan
import YangMills3D.Window

namespace YangMills3D

/-! ## The exact needed-price formula -/

/-- **The ladder-threshold formula** (w37-mid §0, the needed-F0_total
column, exactly): at the W30-RATE doubled rate law
`ν = 2(κ_c − ln F₀ − ε)` against the ascent bar `bar μ = 0.493·μ`, the
bar is met iff the total fan price is at most the threshold
`e^{κ_c − bar μ/2 − ε}`. -/
theorem nu2_needed_iff {F0 μ κc ε : ℝ} (hF : 0 < F0) :
    bar μ ≤ nu2 κc F0 ε ↔ F0 ≤ Real.exp (κc - bar μ / 2 - ε) := by
  constructor
  · intro h
    simp only [bar, nu2] at h
    simp only [bar]
    rw [← Real.log_le_iff_le_exp hF]
    linarith
  · intro h
    rw [← Real.log_le_iff_le_exp hF] at h
    simp only [bar] at h
    simp only [bar, nu2]
    linarith

/-- **The fan-ask ladder, statement tier** (w37-mid §4, the
`w30_conditional` pattern): a total tail-fan at a price clearing the
needed constant `e^{κ_c − bar μ/2 − ε}` delivers the window restoration
`bar μ ≤ ν(β)` at the named coupling. -/
theorem ladder_clears {N : Cell → ℕ → ℕ} {n0 : ℕ} {A0 F0 μ β ε : ℝ}
    (_hfan : TailFan N n0 A0 F0) (hpos : 0 < F0)
    (hneed : F0 ≤ Real.exp (2 * Real.pi ^ 2 / β - bar μ / 2 - ε)) :
    bar μ ≤ nu2 (2 * Real.pi ^ 2 / β) F0 ε :=
  (nu2_needed_iff hpos).mpr hneed

/-! ## The numeric rungs (banked corners, ε = 0.02, power-of-two prices) -/

/-- `2π² ≥ 19.7391`, from Mathlib's `Real.pi_gt_d20`
(3.14159265358979323846 < π). -/
private theorem two_pi_sq_ge : (19.7391 : ℝ) ≤ 2 * Real.pi ^ 2 := by
  have hp := Real.pi_gt_d20
  nlinarith [Real.pi_pos, hp]

private theorem log_eight_le : Real.log 8 ≤ 2.0795 := by
  have h2 : Real.log 2 ≤ 0.6931471808 := Real.log_two_lt_d9.le
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 from by norm_num, Real.log_pow]
    norm_num
  rw [h8]
  linarith

private theorem log_four_le : Real.log 4 ≤ 1.3863 := by
  have h2 : Real.log 2 ≤ 0.6931471808 := Real.log_two_lt_d9.le
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
    norm_num
  rw [h4]
  linarith

private theorem log_two_le : Real.log 2 ≤ 0.6932 := by
  have h2 : Real.log 2 ≤ 0.6931471808 := Real.log_two_lt_d9.le
  linarith

/-- The rung engine (w37-mid §4): at coupling `β` with `2π² ≥ 19.7391`,
if the price-`P` tail fan satisfies the bar at the LOWER floor
`2·(D − L − 0.02)` with `D ≤ 19.7391/β` a certified κ_c floor and
`L ≥ log P` the certified log ceiling, then the bar holds at ANY price
`F₀ ≤ P` (monotonicity of the rate in the price,
`nu2_le_of_F0_le`). -/
private theorem bar_le_nu2_of {μ β F0 P L D : ℝ} (hpos : 0 < F0) (hprice : F0 ≤ P)
    (hL : Real.log P ≤ L) (hkey : bar μ ≤ 2 * (D - L - 0.02))
    (hD : D ≤ (19.7391 : ℝ) / β)
    (_hposβ : 0 < β) (hdiv : (19.7391 : ℝ) / β ≤ 2 * Real.pi ^ 2 / β) :
    bar μ ≤ nu2 (2 * Real.pi ^ 2 / β) F0 0.02 := by
  have hmono := nu2_le_of_F0_le hpos hprice (2 * Real.pi ^ 2 / β) 0.02
  have hP : bar μ ≤ nu2 (2 * Real.pi ^ 2 / β) P 0.02 := by
    have hkey2 : (0.493 : ℝ) * μ ≤ 2 * (2 * Real.pi ^ 2 / β - Real.log P - 0.02) := by
      have h1 : bar μ ≤ 2 * (D - L - 0.02) := hkey
      simp only [bar] at h1
      linarith
    simp only [bar, nu2]
    exact hkey2
  exact hP.trans hmono

/-- **Rung, the window bottom** (w37-mid §4, "restores [6.618, 8.2315]";
μ = 2.443, the banked bottom corner): a total tail-fan at price `F₀ ≤ 8`
delivers `bar 2.443 ≤ ν` at `β = 6.618`, ε = 0.02.  The .md's exact
DP-priced ask is the pinched-fan price `F0H ≤ 5.1932` (DP total
≤ 5.972); any total price ≤ 8 clears a fortiori. -/
theorem rung_bottom {F0 : ℝ} (hpos : 0 < F0) (hprice : F0 ≤ 8) :
    bar 2.443 ≤ nu2 (2 * Real.pi ^ 2 / 6.618) F0 0.02 :=
  bar_le_nu2_of (μ := 2.443) (β := 6.618) (P := 8) (L := 2.0795) (D := 2.9826)
    hpos hprice log_eight_le (by simp only [bar]; norm_num) (by norm_num)
    (by norm_num) (div_le_div_iff_of_pos_right (by norm_num) |>.mpr two_pi_sq_ge)

/-- **Rung, 8.2315** (w37-mid §4, the ladder top; μ = 2.397, the banked
plateau corner): a total tail-fan at price `F₀ ≤ 4` delivers
`bar 2.397 ≤ ν` at `β = 8.2315`, ε = 0.02.  The .md's exact ask is the
pinched-fan price `F0H ≤ 5.1932` (DP total ≤ 5.972). -/
theorem rung_82315 {F0 : ℝ} (hpos : 0 < F0) (hprice : F0 ≤ 4) :
    bar 2.397 ≤ nu2 (2 * Real.pi ^ 2 / 8.2315) F0 0.02 :=
  bar_le_nu2_of (μ := 2.397) (β := 8.2315) (P := 4) (L := 1.3863) (D := 2.3979)
    hpos hprice log_four_le (by simp only [bar]; norm_num) (by norm_num)
    (by norm_num) (div_le_div_iff_of_pos_right (by norm_num) |>.mpr two_pi_sq_ge)

/-- **Rung, 9** (w37-mid §4, "closes [6.618, 9]"; μ = 2.397): a total
tail-fan at price `F₀ ≤ 4` delivers `bar 2.397 ≤ ν` at `β = 9`,
ε = 0.02.  The .md's exact ask is the pinched-fan price
`F0H ≤ 4.2309` (DP total ≤ 4.8665). -/
theorem rung_9 {F0 : ℝ} (hpos : 0 < F0) (hprice : F0 ≤ 4) :
    bar 2.397 ≤ nu2 (2 * Real.pi ^ 2 / 9) F0 0.02 :=
  bar_le_nu2_of (μ := 2.397) (β := 9) (P := 4) (L := 1.3863) (D := 2.1932)
    hpos hprice log_four_le (by simp only [bar]; norm_num) (by norm_num)
    (by norm_num) (div_le_div_iff_of_pos_right (by norm_num) |>.mpr two_pi_sq_ge)

/-- **Rung, 10** (w37-mid §4, "closes [6.618, 10]"; μ = 2.397): a total
tail-fan at price `F₀ ≤ 2` delivers `bar 2.397 ≤ ν` at `β = 10`,
ε = 0.02.  The .md's exact ask is the pinched-fan price
`F0H ≤ 3.3945` (DP total ≤ 3.9081). -/
theorem rung_10 {F0 : ℝ} (hpos : 0 < F0) (hprice : F0 ≤ 2) :
    bar 2.397 ≤ nu2 (2 * Real.pi ^ 2 / 10) F0 0.02 :=
  bar_le_nu2_of (μ := 2.397) (β := 10) (P := 2) (L := 0.6932) (D := 1.9739)
    hpos hprice log_two_le (by simp only [bar]; norm_num) (by norm_num)
    (by norm_num) (div_le_div_iff_of_pos_right (by norm_num) |>.mpr two_pi_sq_ge)

end YangMills3D

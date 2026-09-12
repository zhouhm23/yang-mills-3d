/-
The W23-IMG binding-window check, Lean form: the delivered OP-gap rate
`nu(beta) = (4/3) (2*pi^2/beta - log 8)` clears the ascent budget bar
`0.493 * mu_0(beta)` at the two ends of the strong quarter.

SOURCE. `problems/yang-mills-mass-gap/lemmas/w23-opgap.md` (the delivered
rate `nu`, tag W23-IMG), `lemmas/w22-ascent.md` section 5 (the bar
`0.493 * mu_0`), `lemmas/w21-rebase.md` (the mu_0 table:
mu_0(4) = 2.44, mu_0(6.618) = 2.40, mu_0(8) = 2.39, mu_0(16) = 2.42,
mu_0(32) = 1.81), and `lemmas/w20-rpa2.md` (the symbol whose constant
budget feeds T-OP; see `YangMills3D.Symbol`).
[PROVED-here targets: W23-IMG window check.]

RECORDED NUMBERS (binding edge `beta = 6.618`).  The bar is
`0.493 * 2.40 = 1.1832`.  The campaign machine value of the rate is
`nu(6.618) = 1.2044` (w23_opgap.py).  Lean certifies the weaker but fully
machine-checked floor `nu(6.618) > (4/3) * (19.7192/6.618 - 2.0796)`
`> 1.2000`: it uses only `Real.pi_gt_d2 : 3.14 < pi` (so `2*pi^2 > 19.7192`)
and `Real.log_two_lt_d9 : log 2 < 0.6931471808` (so `log 8 < 2.0796`).
Both the floor `1.2000` and the machine value `1.2044` clear the bar
`1.1832`, with a safe margin of about `0.017` even at the floor.

Strong end `beta = 4`: bar `0.493 * 2.44 = 1.20292` (about `1.203`), machine
value `nu(4) = 3.807`; the Lean-verified floor is
`(4/3) * (19.7192/4 - 2.0796) > 3.8002` — a huge margin.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

namespace YangMills3D

/-- The delivered OP-gap rate `nu(beta) = (4/3) (2*pi^2/beta - log 8)`
[w23-opgap, tag W23-IMG]. -/
noncomputable def nuRate (b : ℝ) : ℝ := (4 / 3) * (2 * Real.pi ^ 2 / b - Real.log 8)

/-- The ascent budget bar `0.493 * mu_0` [w22-ascent §5; mu_0 table
w21-rebase]. -/
noncomputable def bar (mu : ℝ) : ℝ := 0.493 * mu

/-- Auxiliary: `log 8 < 2.0796`, from `log 8 = 3 * log 2` and Mathlib's
`Real.log_two_lt_d9 : log 2 < 0.6931471808`. -/
private theorem log_eight_lt : Real.log 8 < 2.0796 := by
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 from by norm_num, Real.log_pow]
    norm_num
  rw [h8]
  linarith

/-- Auxiliary: `2 * pi² > 19.7192`, from Mathlib's `Real.pi_gt_d2 :
3.14 < pi`. -/
private theorem two_pi_sq_gt : (19.7192 : ℝ) < 2 * Real.pi ^ 2 := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hp2 : (3.14 : ℝ) ^ 2 < Real.pi ^ 2 := by nlinarith [Real.pi_pos, hpi]
  nlinarith

/-- **Binding-edge window check** (W23-IMG).  At the strong-quarter edge
`beta = 6.618` the delivered OP-gap rate clears the ascent budget bar:
`0.493 * 2.40 = 1.1832 < nu(6.618)`.  The Lean-verified floor of
`nu(6.618)` here is `(4/3) * (19.7192/6.618 - 2.0796) > 1.2000`; the
campaign machine value is `1.2044` (w23_opgap.py). -/
theorem window_check_edge : bar 2.40 < nuRate 6.618 := by
  have hlog := log_eight_lt
  have hpi2 := two_pi_sq_gt
  have key : (19.7192 : ℝ) / 6.618 - 2.0796 < 2 * Real.pi ^ 2 / 6.618 - Real.log 8 := by
    have d1 : (19.7192 : ℝ) / 6.618 < 2 * Real.pi ^ 2 / 6.618 := by
      field_simp
      exact hpi2
    linarith
  have e2 : (0.493 : ℝ) * 2.40 < (4 / 3) * (19.7192 / 6.618 - 2.0796) := by norm_num
  exact lt_trans e2 (mul_lt_mul_of_pos_left key (by norm_num))

/-- **Strong-end window check** (W23-IMG).  At the strong end `beta = 4`
the delivered OP-gap rate clears the ascent budget bar by a huge margin:
`0.493 * 2.44 = 1.20292 < nu(4)` (machine value `3.807`; Lean-verified
floor `(4/3) * (19.7192/4 - 2.0796) > 3.8002`). -/
theorem window_check_strong : bar 2.44 < nuRate 4 := by
  have hlog := log_eight_lt
  have hpi2 := two_pi_sq_gt
  have key : (19.7192 : ℝ) / 4 - 2.0796 < 2 * Real.pi ^ 2 / 4 - Real.log 8 := by
    have d1 : (19.7192 : ℝ) / 4 < 2 * Real.pi ^ 2 / 4 := by
      field_simp
      exact hpi2
    linarith
  have e2 : (0.493 : ℝ) * 2.44 < (4 / 3) * (19.7192 / 4 - 2.0796) := by norm_num
  exact lt_trans e2 (mul_lt_mul_of_pos_left key (by norm_num))

end YangMills3D

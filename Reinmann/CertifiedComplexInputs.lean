/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.CertifiedTaylorModel
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-! Kernel - checked scalar inputs for complex Taylor models. Series remainders
come from Mathlib; all endpoint comparisons are rational arithmetic. -/
noncomputable section
namespace Reinmann.CertifiedComplexInputs
open Finset CertifiedTaylorModel

/-- The rapidly convergent atanh expansion after positive - real scaling. -/
def logPartial (q : ℚ) (n : ℕ) : ℚ :=
  2 * ∑ i ∈ range n, ((q - 1) / (q + 1)) ^ (2 * i + 1) / (2 * i + 1)

def logError (q : ℚ) (n : ℕ) : ℚ :=
  2 * |(q - 1) / (q + 1)|^(2 * n + 1) / (1 - ((q - 1) / (q + 1)) ^ 2)

theorem log_partial_bound {q : ℚ} (hq : 0 < q) (n : ℕ) :
    |Real.log (q : ℝ) - (logPartial q n : ℝ)| ≤ (logError q n : ℝ) := by
  let x : ℝ := ((q : ℝ) - 1) / ((q : ℝ) + 1)
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hx : |x| < 1 := by
    rw [abs_lt]
    dsimp [x]
    constructor <;> field_simp <;> nlinarith
  have heq : (1 + x) / (1 - x) = (q : ℝ) := by dsimp [x]; field_simp; ring
  have h := Real.sum_range_sub_log_div_le hx n
  rw [heq] at h
  have he : |Real.log (q : ℝ) - 2*∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1)| =
      2*|1 / 2 * Real.log (q : ℝ) - ∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1)| := by
    calc
      _ = |2 * (1 / 2 * Real.log (q : ℝ) - ∑ i ∈ range n, x ^ (2 * i + 1) / (2 * i + 1))| := by
        congr 1
        ring
      _ = _ := by rw [abs_mul]; norm_num
  have h' := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [logPartial, logError, Rat.cast_mul, Rat.cast_sum, Rat.cast_div,
    Rat.cast_pow, Rat.cast_sub, Rat.cast_add, Rat.cast_one, Rat.cast_ofNat,
    Rat.cast_abs, Rat.cast_natCast, ← he, mul_div_assoc, x] using! h'

/-- A short rational series proof can be rounded to any convenient rational centre. -/
theorem log_enclosure {q a e : ℚ} (hq : 0 < q) (n : ℕ)
    (h : logError q n + |logPartial q n - a| ≤ e) :
    |Real.log (q : ℝ) - (a : ℝ)| ≤ (e : ℝ) := by
  calc
    _ = |(Real.log (q : ℝ) - (logPartial q n : ℝ))+
        ((logPartial q n : ℝ) - (a : ℝ))| := by congr 1; ring
    _ ≤ |Real.log (q : ℝ) - (logPartial q n : ℝ)|+
        |(logPartial q n : ℝ) - (a : ℝ)| := abs_add_le _ _
    _ ≤ (logError q n : ℝ)+|(logPartial q n : ℝ) - (a : ℝ)| :=
      add_le_add (log_partial_bound hq n) le_rfl
    _ ≤ _ := by exact_mod_cast h

/-- Scaling by a positive rational uses no complex - log branch assumptions. -/
theorem log_mul_enclosure {q r a b e f : ℚ} (hq : 0 < q) (hr : 0 < r)
    (hqa : |Real.log (q : ℝ) - (a : ℝ)| ≤ (e : ℝ))
    (hrb : |Real.log (r : ℝ) - (b : ℝ)| ≤ (f : ℝ)) :
    |Real.log ((q * r : ℚ) : ℝ) - ((a + b : ℚ) : ℝ)| ≤ ((e + f : ℚ) : ℝ) := by
  have hq' : (q : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hq)
  have hr' : (r : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr)
  push_cast
  rw [Real.log_mul hq' hr']
  calc
    _ = |(Real.log (q : ℝ) - (a : ℝ)) + (Real.log (r : ℝ) - (b : ℝ))| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add hqa hrb

theorem log_pow_enclosure {q a e : ℚ} (k : ℕ)
    (h : |Real.log (q : ℝ) - (a : ℝ)| ≤ (e : ℝ)) :
    |Real.log ((q ^ k : ℚ) : ℝ) - ((k * a : ℚ) : ℝ)| ≤ ((k * e : ℚ) : ℝ) := by
  push_cast
  rw [Real.log_pow, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg k)

theorem log_recenter {x : ℝ} {a b e f : ℚ}
    (h : |Real.log x - (a : ℝ)| ≤ (e : ℝ)) (hr : e+|a - b| ≤ f) :
    |Real.log x - (b : ℝ)| ≤ (f : ℝ) := by
  calc
    _ = |(Real.log x - (a : ℝ)) + ((a : ℝ) - (b : ℝ))| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ (e : ℝ)+|(a : ℝ) - (b : ℝ)| := add_le_add h le_rfl
    _ ≤ _ := by exact_mod_cast hr

/-- Scaled arguments lie in [1, 2], so twenty atanh terms suffice. -/
theorem log_scaled_enclosure {q a b : ℚ} (k : ℕ) (hq : 0 < q)
    (htwo : |Real.log (2 : ℝ) - (a : ℝ)| ≤ (1 / 10 ^ 15 : ℝ))
    (hsmall : logError q 20+|logPartial q 20 - b| ≤ (1 / 10 ^ 15 : ℚ)) :
    |Real.log (((2:ℚ) ^ k * q : ℚ) : ℝ) - ((k * a + b : ℚ) : ℝ)| ≤
      ((k * (1 / 10 ^ 15) + 1 / 10 ^ 15 : ℚ) : ℝ) := by
  have ht : |Real.log ((2 : ℚ) : ℝ) - (a : ℝ)| ≤ ((1 / 10 ^ 15 : ℚ) : ℝ) := by
    convert htwo using 1 <;> norm_num
  exact log_mul_enclosure (pow_pos (by norm_num : (0:ℚ)<2) k) hq
    (log_pow_enclosure k ht) (log_enclosure hq 20 hsmall)

/-- The constant jet of n^{-s}, including its phase, has explicit ordinary coefficients. -/
theorem exponential_coefficient (a c : ℂ) (n : ℕ) :
    coefficient (fun s => Complex.exp (a * s)) c n =
      a ^ n * Complex.exp (a * c) / (n.factorial : ℂ) := by
  simp only [coefficient, iteratedDeriv_cexp_const_mul]

/-- Twenty terms suffice for the scalar exponential after range reduction. -/
theorem exp_series_error {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z-∑ j ∈ range 20, z ^ j / (j.factorial : ℂ)‖ ≤ (1 / 10 ^ 18 : ℝ) := by
  calc
    _ ≤ ‖z‖^20 * ((21 : ℝ) * ((20 : ℕ).factorial * 20 : ℝ)⁻¹) :=
      Complex.exp_bound hz (by norm_num)
    _ ≤ 1 ^ 20 * ((21 : ℝ) * ((20 : ℕ).factorial * 20 : ℝ)⁻¹) := by gcongr
    _ ≤ _ := by norm_num [Nat.factorial]

/-- Attach the proved transcendental remainder to a rational polynomial enclosure. -/
theorem exp_series_contains {z : ℂ} {a : Disk} (hz : ‖z‖ ≤ 1)
    (ha : Contains a (∑ j ∈ range 20, z ^ j / (j.factorial : ℂ))) :
    Contains (inflate a (1 / 10 ^ 18) (by norm_num)) (Complex.exp z) :=
  contains_inflate (by norm_num) ha (by
    convert exp_series_error hz using 1 <;> norm_num)

/-- Forty - eight log terms suffice on the half - unit disk. -/
theorem log_series_error {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log (1 + z) - Complex.logTaylor 48 z‖ ≤ (1 / 10 ^ 15 : ℝ) := by
  have hlt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  have hi : (1-‖z‖)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_comm₀ (by linarith : 0 < 1-‖z‖) (by norm_num : (0 : ℝ)<2)]
    norm_num
    linarith
  calc
    _ ≤ ‖z‖^48 * (1-‖z‖)⁻¹ / 48 := by
      convert Complex.norm_log_sub_logTaylor_le 47 hlt using 1 <;> norm_num
    _ ≤ (1 / 2 : ℝ) ^ 48 * 2 / 48 := by gcongr
    _ ≤ _ := by norm_num

theorem log_series_contains {z : ℂ} {a : Disk} (hz : ‖z‖ ≤ 1 / 2)
    (ha : Contains a (Complex.logTaylor 48 z)) :
    Contains (inflate a (1 / 10 ^ 15) (by norm_num)) (Complex.log (1 + z)) :=
  contains_inflate (by norm_num) ha (by
    convert log_series_error hz using 1 <;> norm_num)

/-- Exact periodic reduction; numerical pi bounds only enter its enclosure. -/
theorem exp_phase_reduce (t : ℝ) (k : ℤ) :
    Complex.exp (((t - (k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((t : ℂ) * Complex.I) := by
  convert Complex.exp_periodic.sub_int_mul_eq (x := (t : ℂ) * Complex.I) k using 1
  all_goals try rfl
  congr 1
  push_cast
  ring

/-- Gamma's shifted centre admits a principal - log series without branch ambiguity. -/
theorem gamma_log_centre_reduce :
    Complex.log ((49 / 4 : ℂ) + 7 * Complex.I) =
      (Real.log (16 : ℝ) : ℂ) + Complex.log (1 + ((-15 / 64 : ℂ) + (7 / 16) * Complex.I)) := by
  have hx : (1 : ℂ) + ((-15 / 64 : ℂ) + (7 / 16) * Complex.I) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  have hw : (49 / 4 : ℂ) + 7 * Complex.I =
      ((16 : ℝ) : ℂ) * (1 + ((-15 / 64 : ℂ) + (7 / 16) * Complex.I)) := by
    norm_num
    ring
  rw [hw, Complex.log_ofReal_mul (by norm_num : (0 : ℝ)<16) hx]

theorem gamma_log_centre_norm : ‖(-15 / 64 : ℂ) + (7 / 16) * Complex.I‖ ≤ (1 / 2 : ℝ) := by
  have h := Complex.sq_norm ((-15 / 64 : ℂ) + (7 / 16) * Complex.I)
  norm_num [Complex.normSq_apply] at h
  nlinarith [norm_nonneg ((-15 / 64 : ℂ) + (7 / 16) * Complex.I)]

end Reinmann.CertifiedComplexInputs

/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.StirlingCell
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-! Order-twelve Euler--Maclaurin summation for `∑ Log (w + j)`, with the
actual periodic Bernoulli remainder and its explicit bound on `(0, ∞)`. -/
noncomputable section
namespace Reinmann.StirlingSum
open MeasureTheory Set Finset Filter Topology
open scoped Interval
open StirlingCell

/-- Endpoint Bernoulli corrections. -/
def corr (w : ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ range 11, (-1 : ℂ)^(k+1) * BernoulliQuadrature.kernel (k+2) 0 * logChain w (k+1) x

/-- The periodic order-twelve remainder integrand. -/
def tailIntegrand (w : ℂ) (t : ℝ) : ℂ :=
  (EulerMaclaurinTail.periodicTwelve t : ℂ) / ((12 : ℕ).factorial : ℂ) * logChain w 12 t

def cellTail (w : ℂ) (x : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..1, BernoulliQuadrature.kernel 12 u * logChain w 12 (x+u)

theorem one_cell (w : ℂ) {x : ℝ} (hw : 0 < w.re) (hx : 0 ≤ x) :
    logChain w 0 x = (∫ u in (0 : ℝ)..1, logChain w 0 (x+u)) +
      (logChain w 0 x - logChain w 0 (x+1))/2 + corr w x - corr w (x+1) - cellTail w x := by
  have h := log_cell w hw hx 12
  rw [sum_range_succ'] at h
  have hsum : (∑ k ∈ range 11, (-1 : ℂ)^(k+1) *
      (BernoulliQuadrature.kernel (k+1+1) 1 * logChain w (k+1) (x+1) -
       BernoulliQuadrature.kernel (k+1+1) 0 * logChain w (k+1) x)) =
      corr w (x+1) - corr w x := by
    rw [corr, corr, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    rw [show k+1+1 = k+2 by omega, BernoulliQuadrature.kernel_at_one _ (by omega)]
    ring
  rw [hsum] at h
  norm_num only [BernoulliQuadrature.kernel_one, Complex.ofReal_zero,
    Complex.ofReal_one, pow_zero, one_mul] at h
  dsimp [cellTail]
  linear_combination -h

theorem cellTail_eq (w : ℂ) (j : ℕ) :
    cellTail w j = ∫ t in (j : ℝ)..(j : ℝ)+1, tailIntegrand w t := by
  rw [cellTail]
  have h : (∫ u in (0 : ℝ)..1, BernoulliQuadrature.kernel 12 u * logChain w 12 ((j : ℝ)+u)) =
      ∫ u in (0 : ℝ)..1, tailIntegrand w ((j : ℝ)+u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    dsimp only
    rw [EulerMaclaurinFinite.kernel_periodic_twelve j hu, tailIntegrand]
  rw [h, intervalIntegral.integral_comp_add_left]
  simp only [add_zero]

theorem logChain_zero_continuousOn (w : ℂ) (hw : 0 < w.re) :
    ContinuousOn (logChain w 0) (Ici 0) := by
  intro t ht
  have hre : 0 < (w + (t : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [show (0 : ℝ) ≤ t from ht]
  exact (logChain_hasDerivAt w 0 hre).continuousAt.continuousWithinAt

theorem logChain_zero_intervalIntegrable (w : ℂ) (hw : 0 < w.re) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) : IntervalIntegrable (logChain w 0) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (logChain_zero_continuousOn w hw).mono
  intro t ht
  rcases mem_uIcc.mp ht with h | h
  · exact le_trans ha h.1
  · exact le_trans hb h.1

/-- Pointwise majorant of the remainder integrand. -/
theorem tailIntegrand_norm_le (w : ℂ) (hw : 0 < w.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖tailIntegrand w t‖ ≤ (6112/15015 : ℝ)/12 * (1/(w.re+t)^12) := by
  have hpos : 0 < w.re + t := by linarith
  have hre : (w + (t : ℂ)).re = w.re + t := by simp
  have hnorm : w.re + t ≤ ‖w + (t : ℂ)‖ := by
    rw [← hre]; exact Complex.re_le_norm _
  have hne : w + (t : ℂ) ≠ 0 := add_ne_zero_of_re_pos (by rw [hre]; exact hpos)
  have hz : ‖(w + (t : ℂ))^(-(((11 : ℕ) : ℤ)+1))‖ ≤ 1/(w.re+t)^12 := by
    rw [norm_zpow]
    have he : (-(((11 : ℕ) : ℤ)+1)) = -12 := by norm_num
    rw [he, zpow_neg, zpow_ofNat, one_div]
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ hpos.le hnorm 12
  simp only [tailIntegrand, logChain, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
  have hp := EulerMaclaurinTail.periodicTwelve_abs_le t
  have hf : ((12 : ℕ).factorial : ℝ) = 12 * (11 : ℕ).factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hf]
  have h11 : (0 : ℝ) < (11 : ℕ).factorial := by exact_mod_cast Nat.factorial_pos 11
  calc |EulerMaclaurinTail.periodicTwelve t| / (12 * ((11 : ℕ).factorial : ℝ)) *
        (((11 : ℕ).factorial : ℝ) * ‖(w + (t : ℂ))^(-(((11 : ℕ) : ℤ)+1))‖)
      = |EulerMaclaurinTail.periodicTwelve t| / 12 * ‖(w + (t : ℂ))^(-(((11 : ℕ) : ℤ)+1))‖ := by
        field_simp
    _ ≤ (6112/15015 : ℝ)/12 * (1/(w.re+t)^12) := by
        apply mul_le_mul (by linarith) hz (norm_nonneg _) (by norm_num)

theorem tailIntegrand_measurable (w : ℂ) : AEStronglyMeasurable (tailIntegrand w) volume := by
  apply AEStronglyMeasurable.mul
  · exact ((Complex.continuous_ofReal.measurable.comp
      EulerMaclaurinTail.periodicTwelve_measurable).div_const _).aestronglyMeasurable
  · have : Measurable (fun t : ℝ => (w + (t : ℂ))^(-(((11 : ℕ) : ℤ)+1))) :=
      (measurable_const.add Complex.continuous_ofReal.measurable).pow_const _
    exact ((measurable_const.mul this)).aestronglyMeasurable

/-- The majorant `1/(a+t)^12` is integrable on `(0,∞)` with integral `a^(-11)/11`. -/
theorem majorant_integral {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => 1/(a+t)^12) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), 1/(a+t)^12 = 1/(11*a^11) := by
  let F : ℝ → ℝ := fun t => -(1/11 : ℝ) * (a+t)^(-11 : ℤ)
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt F (1/(a+t)^12) t := by
    intro t ht
    have hpos : 0 < a + t := by linarith [show (0 : ℝ) < t from ht]
    have h := ((hasDerivAt_zpow (-11) (a+t) (Or.inl hpos.ne')).comp t
      ((hasDerivAt_id t).const_add a)).const_mul (-(1/11 : ℝ))
    convert h using 1
    · rfl
    have he : ((-11 : ℤ) - 1) = -12 := by norm_num
    simp only [mul_one, he, zpow_neg, zpow_ofNat]
    push_cast
    field_simp
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt
    have h := ((hasDerivAt_zpow (-11) (a+0) (Or.inl (by linarith))).comp (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).const_add a)).const_mul (-(1/11 : ℝ))
    exact h.continuousAt
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ 1/(a+t)^12 := by
    intro t ht
    have : 0 < a + t := by linarith [show (0 : ℝ) < t from ht]
    positivity
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => a + t) atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_id
    have h2 := (tendsto_zpow_atTop_zero (by norm_num : (-11 : ℤ) < 0)).comp h1
    have h3 := h2.const_mul (-(1/11 : ℝ))
    simpa [F] using! h3
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos hlim]
  simp only [F, add_zero, zpow_neg, zpow_ofNat]
  field_simp
  ring

theorem tailIntegrand_integrableOn (w : ℂ) (hw : 0 < w.re) :
    IntegrableOn (tailIntegrand w) (Ioi 0) := by
  have hm := (majorant_integral hw).1.const_mul ((6112/15015 : ℝ)/12)
  apply hm.mono' (tailIntegrand_measurable w).restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact tailIntegrand_norm_le w hw (le_of_lt ht)

/-- The infinite remainder and its explicit bound. -/
def tail (w : ℂ) : ℂ := ∫ t in Ioi (0 : ℝ), tailIntegrand w t

theorem tail_norm_le (w : ℂ) (hw : 0 < w.re) :
    ‖tail w‖ ≤ (6112/15015 : ℝ)/12 * (1/(11*w.re^11)) := by
  have hm := (majorant_integral hw).1.const_mul ((6112/15015 : ℝ)/12)
  have h := norm_integral_le_of_norm_le hm (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact tailIntegrand_norm_le w hw (le_of_lt ht))
  rw [integral_const_mul, (majorant_integral hw).2] at h
  exact h

theorem tailIntegrand_intervalIntegrable (w : ℂ) (hw : 0 < w.re) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable (tailIntegrand w) volume a b := by
  rw [intervalIntegrable_iff, uIoc_of_le hab]
  by_cases ha0 : a = 0
  · subst ha0
    exact (tailIntegrand_integrableOn w hw).mono_set Ioc_subset_Ioi_self
  · exact (tailIntegrand_integrableOn w hw).mono_set (by
      intro t ht; exact (show (0 : ℝ) < t by
        have : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0); linarith [ht.1]))

/-- Order-twelve summation of `∑_{j<n} Log (w + j)`. -/
theorem finite_sum (w : ℂ) (hw : 0 < w.re) (n : ℕ) :
    (∑ j ∈ range n, logChain w 0 j) =
      (∫ t in (0 : ℝ)..(n : ℝ), logChain w 0 t) +
      (logChain w 0 0 - logChain w 0 n)/2 + corr w 0 - corr w n -
      ∫ t in (0 : ℝ)..(n : ℝ), tailIntegrand w t := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hcell := one_cell w hw hn
    rw [cellTail_eq] at hcell
    have hshift : (∫ u in (0 : ℝ)..1, logChain w 0 ((n : ℝ)+u)) =
        ∫ t in (n : ℝ)..(n : ℝ)+1, logChain w 0 t := by
      simpa only [add_zero, add_comm (1 : ℝ)] using!
        intervalIntegral.integral_comp_add_left (a := 0) (b := 1) (logChain w 0) (n : ℝ)
    rw [hshift] at hcell
    have hp := intervalIntegral.integral_add_adjacent_intervals
      (logChain_zero_intervalIntegrable w hw (le_refl 0) hn)
      (logChain_zero_intervalIntegrable w hw hn (by linarith : (0 : ℝ) ≤ (n : ℝ)+1))
    have hr := intervalIntegral.integral_add_adjacent_intervals
      (tailIntegrand_intervalIntegrable w hw (le_refl 0) hn)
      (tailIntegrand_intervalIntegrable w hw hn (by linarith : (n : ℝ) ≤ (n : ℝ)+1))
    rw [sum_range_succ, ih]
    push_cast
    linear_combination hcell + hp - hr

end Reinmann.StirlingSum

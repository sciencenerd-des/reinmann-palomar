/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.BernoulliBernsteinBounds
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! A proved improper-integral bound for the actual twelfth Bernoulli
Euler--Maclaurin tail. Identifying zeta minus its finite model with this integral
is a separate obligation and is not assumed or asserted here. -/
noncomputable section
namespace Reinmann.EulerMaclaurinTail
open MeasureTheory Set Polynomial

def periodicTwelve (t : ℝ) : ℝ :=
  aeval (Int.fract t) (Polynomial.bernoulli 12)

theorem periodicTwelve_measurable : Measurable periodicTwelve :=
  (Polynomial.bernoulli 12).continuous_aeval.measurable.comp measurable_fract

theorem periodicTwelve_abs_le (t : ℝ) :
    |periodicTwelve t| ≤ (6112/15015 : ℝ) :=
  BernoulliBernsteinBounds.bernoulli_twelve_periodic_abs_le t

def integrand (s : ℂ) (t : ℝ) : ℂ :=
  (periodicTwelve t : ℂ)*(t : ℂ)^(-s-12)

theorem integrand_norm_le (s : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖integrand s t‖ ≤ (6112/15015 : ℝ)*t^(-s.re-12) := by
  rw [integrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos ht]
  norm_num [Complex.sub_re, Complex.neg_re]
  exact mul_le_mul_of_nonneg_right (periodicTwelve_abs_le t)
    (Real.rpow_nonneg ht.le _)

theorem integrand_integrable {s : ℂ} (hs : -11 < s.re) {N : ℝ} (hN : 0 < N) :
    IntegrableOn (integrand s) (Ioi N) := by
  have hp : -s.re-12 < -1 := by linarith
  have hbound := (integrableOn_Ioi_rpow_of_lt hp hN).const_mul (6112/15015 : ℝ)
  have hpower := integrableOn_Ioi_cpow_of_lt (a := -s-12)
    (by norm_num [Complex.sub_re, Complex.neg_re]; linarith) hN
  have hmeas : AEStronglyMeasurable (integrand s) (volume.restrict (Ioi N)) :=
    (Complex.continuous_ofReal.measurable.comp periodicTwelve_measurable).aestronglyMeasurable.mul
      hpower.aestronglyMeasurable
  apply hbound.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact integrand_norm_le s (hN.trans ht)

/-- The factorial-normalized periodic integral occurring in order-12 EM. -/
def remainder (s : ℂ) (N : ℝ) : ℂ :=
  -((ascPochhammer ℂ 12).eval s)/((12 : ℕ).factorial : ℂ) *
    ∫ t in Ioi N, integrand s t

theorem integral_norm_le {s : ℂ} (hs : -11 < s.re) {N : ℝ} (hN : 0 < N) :
    ‖∫ t in Ioi N, integrand s t‖ ≤
      (6112/15015 : ℝ)*N^(-s.re-11)/(s.re+11) := by
  have hp : -s.re-12 < -1 := by linarith
  have hbound := (integrableOn_Ioi_rpow_of_lt hp hN).const_mul (6112/15015 : ℝ)
  have h := norm_integral_le_of_norm_le hbound (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact integrand_norm_le s (hN.trans ht))
  rw [integral_const_mul, integral_Ioi_rpow_of_lt hp hN] at h
  have he : -s.re-12+1 = -s.re-11 := by ring
  rw [he] at h
  have hd : s.re+11 ≠ 0 := by linarith
  apply h.trans_eq
  have hn : -s.re-11 = -(s.re+11) := by ring
  rw [hn]
  simp only [neg_div_neg_eq]
  ring

/-- No unknown Bernoulli or remainder constant appears in this bound. -/
theorem remainder_norm_le {s : ℂ} (hs : -11 < s.re) {N : ℝ} (hN : 0 < N) :
    ‖remainder s N‖ ≤
      ‖(ascPochhammer ℂ 12).eval s‖/((12 : ℕ).factorial : ℝ) *
        ((6112/15015 : ℝ)*N^(-s.re-11)/(s.re+11)) := by
  rw [remainder, norm_mul, norm_div, norm_neg, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (integral_norm_le hs hN)
    (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))

end Reinmann.EulerMaclaurinTail

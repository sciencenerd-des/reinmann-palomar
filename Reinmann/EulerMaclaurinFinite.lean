/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.EulerMaclaurinCell
public import Reinmann.EulerMaclaurinTail
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Exact finite Euler--Maclaurin summation at order twelve. -/
noncomputable section
namespace Reinmann.EulerMaclaurinFinite
open Polynomial MeasureTheory Set Finset
open scoped Interval

/-- The spatial derivative with its alternating sign removed. -/
def power (s : ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  (ascPochhammer ℂ k).eval s * (x : ℂ)^(-s-(k : ℂ))

def correction (s : ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ range 11, BernoulliQuadrature.kernel (k+2) 0 * power s (k+1) x

def cellTail (s : ℂ) (N : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, BernoulliQuadrature.kernel 12 t * power s 12 (N+t)

theorem power_zero (s : ℂ) (x : ℝ) : power s 0 x = (x : ℂ)^(-s) := by
  simp [power]

theorem signed_powerDerivative (s : ℂ) (N : ℝ) (k : ℕ) (t : ℝ) :
    (-1 : ℂ)^k * EulerMaclaurinCell.powerDerivative s N k t = power s k (N+t) := by
  simp only [EulerMaclaurinCell.powerDerivative, power, Complex.ofReal_add]
  have hsign : (-1 : ℂ)^k * (-1 : ℂ)^k = 1 := by rw [← mul_pow]; simp
  rw [← mul_assoc, ← mul_assoc, hsign, one_mul, add_comm (t : ℂ)]

theorem normalized_cell (s : ℂ) {N : ℝ} (hN : 0 < N) (m : ℕ) :
    (∫ t in (0 : ℝ)..1, power s 0 (N+t)) =
      (∑ k ∈ range m,
        (BernoulliQuadrature.kernel (k+1) 1 * power s k (N+1) -
         BernoulliQuadrature.kernel (k+1) 0 * power s k N)) +
      (∫ t in (0 : ℝ)..1, BernoulliQuadrature.kernel m t * power s m (N+t)) := by
  have h := EulerMaclaurinCell.finite_cell s hN m
  have hsum : (∑ k ∈ range m, (-1 : ℂ)^k *
        (BernoulliQuadrature.kernel (k+1) 1 * EulerMaclaurinCell.powerDerivative s N k 1 -
         BernoulliQuadrature.kernel (k+1) 0 * EulerMaclaurinCell.powerDerivative s N k 0)) =
      ∑ k ∈ range m,
        (BernoulliQuadrature.kernel (k+1) 1 * power s k (N+1) -
         BernoulliQuadrature.kernel (k+1) 0 * power s k N) := by
    apply sum_congr rfl
    intro k _
    rw [mul_sub, mul_left_comm _ _ (EulerMaclaurinCell.powerDerivative s N k 1),
      mul_left_comm _ _ (EulerMaclaurinCell.powerDerivative s N k 0),
      signed_powerDerivative, signed_powerDerivative, add_zero]
  rw [hsum, ← intervalIntegral.integral_const_mul] at h
  convert h using 1
  all_goals try rfl
  · simp only [power_zero, Complex.ofReal_add, add_comm]
  · congr 2
    funext t
    rw [mul_left_comm, signed_powerDerivative]

/-- An actual power sum on one cell, including its integral remainder. -/
theorem one_cell (s : ℂ) {N : ℝ} (hN : 0 < N) :
    power s 0 N = (∫ t in (0 : ℝ)..1, power s 0 (N+t)) +
      (power s 0 N - power s 0 (N+1))/2 + correction s N - correction s (N+1) -
      cellTail s N := by
  have h := normalized_cell s hN 12
  rw [sum_range_succ'] at h
  have hsum : (∑ k ∈ range 11,
      (BernoulliQuadrature.kernel (k+1+1) 1 * power s (k+1) (N+1) -
       BernoulliQuadrature.kernel (k+1+1) 0 * power s (k+1) N)) =
      correction s (N+1) - correction s N := by
    rw [correction, correction, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    rw [show k+1+1 = k+2 by omega, BernoulliQuadrature.kernel_at_one _ (by omega)]
  rw [hsum] at h
  norm_num only [BernoulliQuadrature.kernel_one, Complex.ofReal_zero,
    Complex.ofReal_one] at h
  dsimp [cellTail]
  linear_combination -h

/-- The periodic kernel agrees on the closed unit cell, including its endpoint. -/
theorem kernel_fract (n : ℕ) (hn : n ≠ 1) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    BernoulliQuadrature.kernel n (Int.fract t) = BernoulliQuadrature.kernel n t := by
  by_cases h : t = 1
  · subst t
    simp only [Int.fract_one]
    exact (BernoulliQuadrature.kernel_at_one n hn).symm
  · rw [Int.fract_eq_self.mpr ⟨ht.1, lt_of_le_of_ne ht.2 h⟩]

theorem kernel_periodic_twelve (N : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    BernoulliQuadrature.kernel 12 t =
      (EulerMaclaurinTail.periodicTwelve ((N : ℝ)+t) : ℂ) /
        ((12 : ℕ).factorial : ℂ) := by
  have heval := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℚ ℝ ℂ)
    (Int.fract t) (Polynomial.bernoulli 12)
  rw [← kernel_fract 12 (by norm_num) ht, BernoulliQuadrature.kernel]
  simp only [EulerMaclaurinTail.periodicTwelve, Int.fract_natCast_add]
  exact congrArg (fun z : ℂ => z / ((12 : ℕ).factorial : ℂ)) heval

/-- The cell remainder is the actual periodic Bernoulli integral on that cell. -/
theorem cellTail_eq (s : ℂ) (N : ℕ) :
    cellTail s N = (ascPochhammer ℂ 12).eval s / ((12 : ℕ).factorial : ℂ) *
      ∫ t in (N : ℝ)..(N : ℝ)+1, EulerMaclaurinTail.integrand s t := by
  rw [cellTail]
  have h : (∫ t in (0 : ℝ)..1,
      BernoulliQuadrature.kernel 12 t * power s 12 ((N : ℝ)+t)) =
      ∫ t in (0 : ℝ)..1, ((ascPochhammer ℂ 12).eval s /
        ((12 : ℕ).factorial : ℂ)) * EulerMaclaurinTail.integrand s ((N : ℝ)+t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    dsimp only
    rw [kernel_periodic_twelve N ht]
    simp only [power, EulerMaclaurinTail.integrand, Nat.cast_ofNat]
    ring
  rw [h, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_left]
  simp only [add_zero]

theorem power_intervalIntegrable (s : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (power s 0) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have htpos : 0 < t := by
    rcases mem_uIcc.mp ht with h | h <;> linarith [h.1, h.2]
  have he : power s 0 = fun x : ℝ => (x : ℂ)^(-s) := funext (power_zero s)
  rw [he]
  exact (Complex.continuousAt_ofReal_cpow_const t (-s) (Or.inr htpos.ne')).continuousWithinAt

theorem tail_intervalIntegrable {s : ℂ} (hs : -11 < s.re) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (EulerMaclaurinTail.integrand s) volume a b := by
  rw [intervalIntegrable_iff, uIoc_of_le hab]
  exact (EulerMaclaurinTail.integrand_integrable hs (by linarith : 0 < a/2)).mono_set
    (by intro t ht; exact (by linarith [ht.1] : a/2 < t))

/-- Order-twelve summation for the actual powers on a finite integer interval. -/
theorem finite_sum (s : ℂ) (N M : ℕ) (hN : 0 < N) (hs : -11 < s.re) :
    (∑ j ∈ range M, power s 0 ((N+j : ℕ) : ℝ)) =
      (∫ t in (N : ℝ)..((N+M : ℕ) : ℝ), power s 0 t) +
      (power s 0 N - power s 0 (N+M))/2 + correction s N - correction s (N+M) -
      (ascPochhammer ℂ 12).eval s / ((12 : ℕ).factorial : ℂ) *
        ∫ t in (N : ℝ)..((N+M : ℕ) : ℝ), EulerMaclaurinTail.integrand s t := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  induction M with
  | zero => simp
  | succ M ih =>
    have hM : 0 < ((N+M : ℕ) : ℝ) := by positivity
    have hcell := one_cell s hM
    rw [cellTail_eq] at hcell
    have hshift : (∫ t in (0 : ℝ)..1, power s 0 (((N+M : ℕ) : ℝ)+t)) =
        ∫ t in ((N+M : ℕ) : ℝ)..((N+M : ℕ) : ℝ)+1, power s 0 t := by
      simpa only [add_zero, add_comm (1 : ℝ)] using!
        intervalIntegral.integral_comp_add_left (a := 0) (b := 1) (power s 0)
          ((N+M : ℕ) : ℝ)
    rw [hshift] at hcell
    have hp := intervalIntegral.integral_add_adjacent_intervals
      (power_intervalIntegrable s hNr hM)
      (power_intervalIntegrable s hM (by positivity : 0 < ((N+M : ℕ) : ℝ)+1))
    have hr := intervalIntegral.integral_add_adjacent_intervals
      (tail_intervalIntegrable hs hNr (by exact_mod_cast Nat.le_add_right N M))
      (tail_intervalIntegrable hs hM (by linarith : ((N+M : ℕ) : ℝ) ≤ ((N+M : ℕ) : ℝ)+1))
    rw [sum_range_succ, ih, hcell]
    simp only [Nat.cast_add, Nat.cast_one, ← add_assoc] at hp hr ⊢
    linear_combination hp -
      ((ascPochhammer ℂ 12).eval s / ((12 : ℕ).factorial : ℂ)) * hr

end Reinmann.EulerMaclaurinFinite

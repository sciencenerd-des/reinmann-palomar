/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.CertifiedTaylorModel
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

@[expose] public section

/-! A scalar Horner certificate with rational outward rounding at every step. -/
noncomputable section
namespace Reinmann.CertifiedHorner
open Finset CertifiedTaylorModel

def horner (a : ℕ → ℚ) (z : ℂ) : ℕ → ℕ → ℂ
  | 0, _ => 0
  | n + 1, k => (a k : ℂ) + z * horner a z n (k + 1)

theorem horner_eq_sum (a : ℕ → ℚ) (z : ℂ) (n k : ℕ) :
    horner a z n k = ∑ j ∈ range n, (a (k + j) : ℂ) * z ^ j := by
  induction n generalizing k with
  | zero => simp [horner]
  | succ n ih =>
    rw [horner, ih, sum_range_succ', mul_sum]
    simp only [Nat.add_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    apply sum_congr rfl
    intro i hi
    rw [show k + 1 + i = k + (i + 1) by omega, pow_succ]
    ring

/-- Only the rational radius and centre - displacement checks vary by input. -/
theorem horner_contains {a : ℕ → ℚ} {z : ℂ} {input : Disk} {b : ℕ → Disk} {n : ℕ}
    (hz : Contains input z) (hb : Contains (b n) 0)
    (hstep : ∀ k < n,
      let raw := add (exact (a k, 0)) (mul input (b (k + 1)))
      raw.radius + size (raw.centre.1 - (b k).centre.1,
        raw.centre.2 - (b k).centre.2) ≤ (b k).radius) :
    Contains (b 0) (horner a z n 0) := by
  have h : ∀ l k, k + l=n → Contains (b k) (horner a z l k) := by
    intro l
    induction l with
    | zero =>
      intro k hk
      have hkn : k = n := by omega
      subst k
      exact hb
    | succ l ih =>
      intro k hk
      have hnext := ih (k + 1) (by omega)
      have hraw := contains_add (contains_exact (a k, 0)) (contains_mul hz hnext)
      simp only [value, Rat.cast_zero, zero_mul, add_zero] at hraw
      exact contains_round (b k).radius_nonneg (hstep k (by omega)) hraw
  exact h n 0 (by omega)

/-- The exponential polynomial coefficients are the ordinary factorial reciprocals. -/
theorem exp_horner_eq (z : ℂ) (n : ℕ) :
    horner (fun j => 1 / (j.factorial : ℚ)) z n 0 =
      ∑ j ∈ range n, z ^ j / (j.factorial : ℂ) := by
  rw [horner_eq_sum]
  apply sum_congr rfl
  intro j hj
  simp [div_eq_mul_inv, mul_comm]

/-- Includes the zero constant term of Mathlib's logTaylor convention. -/
theorem log_horner_eq (z : ℂ) (n : ℕ) :
    horner (fun j => (-1 : ℚ) ^ (j + 1) / (j : ℚ)) z n 0 = Complex.logTaylor n z := by
  rw [horner_eq_sum]
  unfold Complex.logTaylor
  apply sum_congr rfl
  intro j hj
  push_cast
  ring

end Reinmann.CertifiedHorner

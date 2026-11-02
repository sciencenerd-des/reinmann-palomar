/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

/-! Finite Bernstein certificates for periodic Bernoulli remainder factors.
The rational polynomial equalities are checked by the kernel, without a
Fourier expansion or a zeta-value formula. -/
noncomputable section
namespace Reinmann.BernoulliBernsteinBounds
open Polynomial Finset
set_option maxRecDepth 100000

private theorem positive_bernoulli_5 : bernoulli' 5 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, sum_range_succ]

private theorem positive_bernoulli_6 : bernoulli' 6 = (1/42 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, sum_range_succ, positive_bernoulli_5]

private theorem positive_bernoulli_7 : bernoulli' 7 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, sum_range_succ, positive_bernoulli_5, positive_bernoulli_6]

private theorem positive_bernoulli_8 : bernoulli' 8 = (-1/30 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, sum_range_succ, positive_bernoulli_5, positive_bernoulli_6,
    positive_bernoulli_7]

private theorem positive_bernoulli_9 : bernoulli' 9 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, sum_range_succ, positive_bernoulli_5, positive_bernoulli_6,
    positive_bernoulli_7, positive_bernoulli_8]

private theorem positive_bernoulli_10 : bernoulli' 10 = (5/66 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, sum_range_succ, positive_bernoulli_5, positive_bernoulli_6,
    positive_bernoulli_7, positive_bernoulli_8, positive_bernoulli_9]

private theorem positive_bernoulli_11 : bernoulli' 11 = (0 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, sum_range_succ, positive_bernoulli_5, positive_bernoulli_6,
    positive_bernoulli_7, positive_bernoulli_8, positive_bernoulli_9, positive_bernoulli_10]

private theorem positive_bernoulli_12 : bernoulli' 12 = (-691/2730 : ℚ) := by
  rw [bernoulli'_def]
  norm_num [Nat.choose, sum_range_succ, positive_bernoulli_5, positive_bernoulli_6,
    positive_bernoulli_7, positive_bernoulli_8, positive_bernoulli_9, positive_bernoulli_10,
    positive_bernoulli_11]

def bernsteinCoefficient (n k : ℕ) : ℚ :=
  ∑ j ∈ range (k+1), (k.choose j : ℚ)*_root_.bernoulli (n-j)

/-- A finite coefficient certificate proves a bound at every real point of
the interval, not just on a grid of rational samples. -/
theorem abs_aeval_le_of_bernstein {n : ℕ} {P : ℚ[X]} (b : ℕ → ℚ) {C : ℝ}
    (heq : ∀ x : ℝ, aeval x P =
      ∑ k ∈ range (n+1), (b k : ℝ)*(bernsteinPolynomial ℝ n k).eval x)
    (hb : ∀ k ∈ range (n+1), |(b k : ℝ)| ≤ C) {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    |aeval x P| ≤ C := by
  let t : unitInterval := ⟨x,hx⟩
  have heval : aeval x P = ∑ k : Fin (n+1), (b k.val : ℝ)*bernstein n k.val t := by
    rw [heq x, ← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro k _
    rfl
  have hsum : (∑ k : Fin (n+1), bernstein n k.val t) = 1 := bernstein.probability n t
  rw [heval]
  calc
    _ ≤ ∑ k : Fin (n+1), |(b k.val : ℝ)*bernstein n k.val t| := abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin (n+1), |(b k.val : ℝ)| *bernstein n k.val t := by
      apply sum_congr rfl
      intro k _
      rw [abs_mul, abs_of_nonneg bernstein_nonneg]
    _ ≤ ∑ k : Fin (n+1), C*bernstein n k.val t := by
      apply sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (hb k.val (mem_range.mpr k.isLt)) bernstein_nonneg
    _ = C := by rw [← mul_sum,hsum,mul_one]

set_option maxHeartbeats 5000000 in
-- Expand a finite degree-12 rational certificate and normalize its coefficients.
theorem bernoulli_twelve_bernstein (x : ℝ) :
    aeval x (Polynomial.bernoulli 12) =
      ∑ k ∈ range 13, (bernsteinCoefficient 12 k : ℝ)*
        (bernsteinPolynomial ℝ 12 k).eval x := by
  norm_num [Nat.choose, Polynomial.bernoulli, bernsteinCoefficient, bernsteinPolynomial,
    sum_range_succ, _root_.bernoulli, positive_bernoulli_5, positive_bernoulli_6,
    positive_bernoulli_7, positive_bernoulli_8, positive_bernoulli_9, positive_bernoulli_10,
    positive_bernoulli_11, positive_bernoulli_12,
    Polynomial.aeval_def, Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial]
  ring

set_option maxHeartbeats 5000000 in
-- Expand a finite degree-12 rational certificate and normalize its coefficients.
theorem bernoulli_twelve_coefficients :
    ∀ k : Fin 13, |bernsteinCoefficient 12 k.val| ≤ (6112/15015 : ℚ) := by
  intro k
  fin_cases k <;> norm_num [Nat.choose, bernsteinCoefficient, sum_range_succ, _root_.bernoulli,
    positive_bernoulli_5, positive_bernoulli_6, positive_bernoulli_7, positive_bernoulli_8,
    positive_bernoulli_9, positive_bernoulli_10, positive_bernoulli_11, positive_bernoulli_12]

theorem bernoulli_twelve_abs_le {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    |aeval x (Polynomial.bernoulli 12)| ≤ (6112/15015 : ℝ) := by
  apply abs_aeval_le_of_bernstein (bernsteinCoefficient 12) bernoulli_twelve_bernstein
    (x := x) (hx := hx)
  intro k hk
  have h := bernoulli_twelve_coefficients ⟨k,mem_range.mp hk⟩
  have hcast := (Rat.cast_le (K := ℝ)).mpr h
  simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_ofNat] using! hcast

theorem bernoulli_twelve_periodic_abs_le (x : ℝ) :
    |aeval (Int.fract x) (Polynomial.bernoulli 12)| ≤ (6112/15015 : ℝ) :=
  bernoulli_twelve_abs_le ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩

end Reinmann.BernoulliBernsteinBounds

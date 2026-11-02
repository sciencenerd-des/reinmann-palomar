/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.UniformXiRemainders
public import Reinmann.HardTileFiniteIdentities

@[expose] public section

/-! The shared pole-free finite formula at the uniform cutoff 27. -/
noncomputable section
namespace Reinmann.RectangleFiniteFormulas
open Finset Polynomial HardTileFiniteIdentities

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
theorem power_eq (s : ℂ) (k : ℕ) :
    EulerMaclaurinFinite.power s k 27 = rising s k*dirichletTerm s 27/(27 : ℂ)^k := by
  unfold EulerMaclaurinFinite.power
  norm_num only [Complex.ofReal_ofNat]
  have hp := cpow_neg_sub s (n := 27) (by norm_num) k
  norm_num only [Nat.cast_ofNat] at hp
  rw [rising_eq, hp]
  ring

theorem correction_eq (s : ℂ) :
    EulerMaclaurinFinite.correction s 27 =
      (1/(12*27) : ℂ)*rising s 1*dirichletTerm s 27 -
      (1/(720*27^3) : ℂ)*rising s 3*dirichletTerm s 27 +
      (1/(30240*27^5) : ℂ)*rising s 5*dirichletTerm s 27 -
      (1/(1209600*27^7) : ℂ)*rising s 7*dirichletTerm s 27 +
      (1/(47900160*27^9) : ℂ)*rising s 9*dirichletTerm s 27 -
      (691/(1307674368000*27^11) : ℂ)*rising s 11*dirichletTerm s 27 := by
  unfold EulerMaclaurinFinite.correction
  simp only [StirlingGamma.kernel_zero_eq, power_eq, sum_range_succ, sum_range_zero]
  norm_num only [_root_.bernoulli, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, positive_bernoulli_5, positive_bernoulli_6,
    positive_bernoulli_7, positive_bernoulli_8, positive_bernoulli_9,
    positive_bernoulli_10, positive_bernoulli_11, positive_bernoulli_12,
    Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Nat.factorial]
  ring

def finitePart (s : ℂ) : ℂ :=
  (∑ j ∈ range 26, dirichletTerm s (j+1)) + dirichletTerm s 27 / 2 +
    (1/(12*27) : ℂ)*rising s 1*dirichletTerm s 27 -
    (1/(720*27^3) : ℂ)*rising s 3*dirichletTerm s 27 +
    (1/(30240*27^5) : ℂ)*rising s 5*dirichletTerm s 27 -
    (1/(1209600*27^7) : ℂ)*rising s 7*dirichletTerm s 27 +
    (1/(47900160*27^9) : ℂ)*rising s 9*dirichletTerm s 27 -
    (691/(1307674368000*27^11) : ℂ)*rising s 11*dirichletTerm s 27

def regularExpr (s : ℂ) : ℂ := (s-1)*finitePart s+27*dirichletTerm s 27

theorem regularExpr_eq (s : ℂ) :
    regularExpr s = RegularizedEulerMaclaurin.regularModel s 27 := by
  have hsum : EulerMaclaurinZeta.initialSum s 27 =
      ∑ j ∈ range 26, dirichletTerm s (j+1) := by
    unfold EulerMaclaurinZeta.initialSum
    norm_num only
    apply sum_congr rfl
    intro j hj
    rw [EulerMaclaurinFinite.power_zero]
    simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
      Nat.cast_add, Nat.cast_one] using! cpow_neg_eq s (n := j+1) (by omega)
  unfold regularExpr finitePart RegularizedEulerMaclaurin.regularModel
  rw [hsum, cpow_one_sub s (by norm_num : 0 < 27)]
  norm_num only [Nat.cast_ofNat]
  rw [correction_eq, power_eq]
  simp only [show rising s 0 = 1 by simp [rising]]
  ring

end Reinmann.RectangleFiniteFormulas

/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.StirlingGamma
public import Reinmann.EulerMaclaurinZeta

@[expose] public section

/-! Exact evaluation identities for the finite hard-tile models. -/
noncomputable section
namespace Reinmann.HardTileFiniteIdentities
open Finset Polynomial
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


def stirlingMain (w : ℂ) : ℂ :=
  (w-1/2)*Complex.log w-w+((Real.log 2+Real.log Real.pi : ℝ) : ℂ)/2+
    (1/12 : ℂ)*(w⁻¹)^1-(1/360 : ℂ)*(w⁻¹)^3+(1/1260 : ℂ)*(w⁻¹)^5-
    (1/1680 : ℂ)*(w⁻¹)^7+(1/1188 : ℂ)*(w⁻¹)^9-(691/360360 : ℂ)*(w⁻¹)^11

theorem negative_powers (w : ℂ) (k : ℕ) :
    w^(-((k : ℤ)+1)) = (w⁻¹)^(k+1) := by
  rw [show -((k : ℤ)+1) = -((k+1 : ℕ) : ℤ) by push_cast; ring]
  rw [zpow_neg, zpow_natCast, inv_pow]

theorem stirlingMain_eq (w : ℂ) : StirlingGamma.mainTerm w = stirlingMain w := by
  unfold StirlingGamma.mainTerm stirlingMain
  rw [StirlingGamma.corr_zero_eq]
  simp only [negative_powers, Finset.sum_range_succ]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  norm_num only [_root_.bernoulli, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, positive_bernoulli_5, positive_bernoulli_6,
    positive_bernoulli_7, positive_bernoulli_8, positive_bernoulli_9,
    positive_bernoulli_10, positive_bernoulli_11, positive_bernoulli_12,
    Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Complex.ofReal_add]
  ring

def dirichletTerm (s : ℂ) (n : ℕ) : ℂ := Complex.exp (-s*(Real.log (n : ℝ) : ℂ))

theorem cpow_neg_eq (s : ℂ) {n : ℕ} (hn : 0 < n) :
    (n : ℂ)^(-s) = dirichletTerm s n := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [Complex.cpow_def_of_ne_zero hn0]
  unfold dirichletTerm
  rw [← Complex.ofReal_natCast, Complex.ofReal_log (by exact_mod_cast hn.le : (0 : ℝ) ≤ n)]
  congr 1
  ring

theorem cpow_neg_sub (s : ℂ) {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (n : ℂ)^(-s-(k : ℂ)) = dirichletTerm s n/(n : ℂ)^k := by
  rw [Complex.cpow_sub _ _ (by exact_mod_cast Nat.ne_of_gt hn),
    cpow_neg_eq s hn, Complex.cpow_natCast]

def rising (s : ℂ) (k : ℕ) : ℂ := ∏ j ∈ range k, (s+(j : ℂ))

theorem rising_eq (s : ℂ) (k : ℕ) : (ascPochhammer ℂ k).eval s = rising s k := by
  induction k with
  | zero => simp [rising]
  | succ k ih => rw [ascPochhammer_succ_eval, rising, prod_range_succ, ih]; rfl

theorem dirichletTerm_one (s : ℂ) : dirichletTerm s 1 = 1 := by
  simp [dirichletTerm]

theorem cpow_one_sub (s : ℂ) {n : ℕ} (hn : 0 < n) :
    (n : ℂ)^(1-s) = (n : ℂ)*dirichletTerm s n := by
  rw [show (1:ℂ)-s = 1+(-s) by ring,
    Complex.cpow_add _ _ (by exact_mod_cast Nat.ne_of_gt hn),
    Complex.cpow_one, cpow_neg_eq s hn]

def emFinite (s : ℂ) : ℂ :=
  (∑ j ∈ range 20, dirichletTerm s (j+1)) +
  21*dirichletTerm s 21*(s-1)⁻¹ + dirichletTerm s 21/2 +
  (1/(12*21) : ℂ)*rising s 1*dirichletTerm s 21 -
  (1/(720*21^3) : ℂ)*rising s 3*dirichletTerm s 21 +
  (1/(30240*21^5) : ℂ)*rising s 5*dirichletTerm s 21 -
  (1/(1209600*21^7) : ℂ)*rising s 7*dirichletTerm s 21 +
  (1/(47900160*21^9) : ℂ)*rising s 9*dirichletTerm s 21 -
  (691/(1307674368000*21^11) : ℂ)*rising s 11*dirichletTerm s 21

theorem power_eq (s : ℂ) (k : ℕ) :
    EulerMaclaurinFinite.power s k 21 = rising s k*dirichletTerm s 21/(21 : ℂ)^k := by
  unfold EulerMaclaurinFinite.power
  norm_num only [Complex.ofReal_ofNat]
  have hp := cpow_neg_sub s (n := 21) (by norm_num) k
  norm_num only [Nat.cast_ofNat] at hp
  rw [rising_eq, hp]
  ring

theorem correction_eq (s : ℂ) :
    EulerMaclaurinFinite.correction s 21 =
      (1/(12*21) : ℂ)*rising s 1*dirichletTerm s 21 -
      (1/(720*21^3) : ℂ)*rising s 3*dirichletTerm s 21 +
      (1/(30240*21^5) : ℂ)*rising s 5*dirichletTerm s 21 -
      (1/(1209600*21^7) : ℂ)*rising s 7*dirichletTerm s 21 +
      (1/(47900160*21^9) : ℂ)*rising s 9*dirichletTerm s 21 -
      (691/(1307674368000*21^11) : ℂ)*rising s 11*dirichletTerm s 21 := by
  unfold EulerMaclaurinFinite.correction
  simp only [StirlingGamma.kernel_zero_eq, power_eq, sum_range_succ, sum_range_zero]
  norm_num only [_root_.bernoulli, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, positive_bernoulli_5, positive_bernoulli_6,
    positive_bernoulli_7, positive_bernoulli_8, positive_bernoulli_9,
    positive_bernoulli_10, positive_bernoulli_11, positive_bernoulli_12,
    Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Nat.factorial]
  ring

theorem emFinite_eq (s : ℂ) : EulerMaclaurinZeta.finiteModel s 21 = emFinite s := by
  have hsum : EulerMaclaurinZeta.initialSum s 21 =
      ∑ j ∈ range 20, dirichletTerm s (j+1) := by
    unfold EulerMaclaurinZeta.initialSum
    norm_num only
    apply sum_congr rfl
    intro j hj
    rw [EulerMaclaurinFinite.power_zero]
    simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
      Nat.cast_add, Nat.cast_one] using! cpow_neg_eq s (n := j+1) (by omega)
  unfold EulerMaclaurinZeta.finiteModel emFinite
  rw [hsum, cpow_one_sub s (by norm_num : 0 < 21)]
  norm_num only [Nat.cast_ofNat]
  rw [correction_eq, power_eq]
  simp only [show rising s 0 = 1 by simp [rising]]
  ring

end Reinmann.HardTileFiniteIdentities

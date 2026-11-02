/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.XiMellinRemainder
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! A coarse actual-Xi circle bound for local Taylor derivative certificates.
The bound is for the entire Xi target and does not assert zero exclusion. -/
noncomputable section
namespace Reinmann.XiLocalCauchy
open Metric

/-- A common half-plane bound for the genuine upper Mellin transform. -/
theorem mellin_norm_le {u : ℂ} (hu : u.re ≤ 1) :
    ‖mellin thetaCenterUpper u‖ ≤ 4 * Real.exp (-1) := by
  have h := thetaUpperMellinRemainder_norm_le (T := 1) (s := u) (by norm_num) hu
  rw [thetaUpperMellinRemainder_eq_cutoff (by norm_num : (1 : ℝ) ≤ 1) u] at h
  exact h

/-- The pole-subtracted completion is only used to evaluate the true Xi target. -/
theorem completed_norm_le {z : ℂ} (hl : -1 ≤ z.re) (hu : z.re ≤ 2) :
    ‖completedRiemannZeta₀ z‖ ≤ 4 * Real.exp (-1) := by
  have h1 := mellin_norm_le (u := z / 2) (by simp only [Complex.div_ofNat_re]; linarith)
  have h2 := mellin_norm_le (u := (1 - z) / 2) (by
    simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.one_re]
    linarith)
  rw [completedRiemannZeta₀_eq_paired_mellin, norm_div]
  norm_num only [Complex.norm_ofNat]
  have h := (norm_add_le (mellin thetaCenterUpper (z / 2))
    (mellin thetaCenterUpper ((1 - z) / 2))).trans (add_le_add h1 h2)
  linarith

/-- A global estimate with sufficient strip margin for unit-radius Cauchy circles. -/
theorem xi_norm_le {z : ℂ} (hl : -1 ≤ z.re) (hu : z.re ≤ 2) :
    ‖xiCompleted z‖ ≤ 1 / 2 + 2 * ‖z‖ * ‖z - 1‖ * Real.exp (-1) := by
  have h := completed_norm_le hl hu
  unfold xiCompleted
  apply (norm_add_le _ _).trans
  simp only [norm_mul, norm_div, Complex.norm_ofNat, norm_one]
  norm_num only [norm_div, Complex.norm_ofNat]
  calc
    (1 : ℝ) / 2 + ‖z‖ * ‖z - 1‖ / 2 * ‖completedRiemannZeta₀ z‖ ≤
        1 / 2 + ‖z‖ * ‖z - 1‖ / 2 * (4 * Real.exp (-1)) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h
        (div_nonneg (mul_nonneg (norm_nonneg z) (norm_nonneg (z - 1)))
          (by norm_num : (0 : ℝ) ≤ 2)))
    _ = _ := by ring

/-- The pilot's universal majorant is proved, not a numerical hypothesis. -/
theorem unit_circle_bound {c z : ℂ}
    (hl : (1 / 2 : ℝ) ≤ c.re) (hu : c.re ≤ 1) (hi : |c.im| ≤ (141 / 10 : ℝ))
    (hz : z ∈ sphere c 1) : ‖xiCompleted z‖ ≤ 1000 := by
  have hd : ‖z - c‖ = 1 := mem_sphere_iff_norm.mp hz
  have hr : |z.re - c.re| ≤ 1 := by
    simpa only [Complex.sub_re, hd] using! Complex.abs_re_le_norm (z - c)
  have hb := abs_le.mp hr
  have hci := abs_le.mp hi
  have hc : ‖c‖ ≤ 15 := by
    have hs : ‖c‖ ^ 2 = c.re ^ 2 + c.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    nlinarith [norm_nonneg c, sq_nonneg (c.re - 1)]
  have hc1 : ‖c - 1‖ ≤ 15 := by
    have hs : ‖c - 1‖ ^ 2 = (c.re - 1) ^ 2 + c.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
      ring
    nlinarith [norm_nonneg (c - 1), sq_nonneg c.re]
  have hz0 : ‖z‖ ≤ 16 := by
    calc
      ‖z‖ = ‖(z - c) + c‖ := by congr 1; ring
      _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ 16 := by rw [hd]; linarith
  have hz1 : ‖z - 1‖ ≤ 16 := by
    calc
      ‖z - 1‖ = ‖(z - c) + (c - 1)‖ := by congr 1; ring
      _ ≤ ‖z - c‖ + ‖c - 1‖ := norm_add_le _ _
      _ ≤ 16 := by rw [hd]; linarith
  have he : Real.exp (-1) ≤ 1 := by
    simpa only [Real.exp_zero] using! Real.exp_le_exp.mpr (by norm_num : (-1 : ℝ) ≤ 0)
  have hp : ‖z‖ * ‖z - 1‖ ≤ 256 :=
    (mul_le_mul hz0 hz1 (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have h := xi_norm_le (z := z) (by linarith [hb.1]) (by linarith [hb.2])
  have hm := mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (mul_nonneg (norm_nonneg z) (norm_nonneg (z - 1))))
  nlinarith

/-- Actual Taylor coefficients on each such circle have a uniform Cauchy bound. -/
theorem coefficient_bound {c : ℂ}
    (hl : (1 / 2 : ℝ) ≤ c.re) (hu : c.re ≤ 1) (hi : |c.im| ≤ (141 / 10 : ℝ))
    (n : ℕ) : ‖iteratedDeriv n xiCompleted c‖ ≤ n.factorial * 1000 := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0 : ℝ) < 1) differentiable_xiCompleted.diffContOnCl
    (fun z hz => unit_circle_bound hl hu hi hz)
  simpa using! h

/-- The normalized ordinary Taylor coefficients used by the Arb pilot. -/
theorem taylor_coefficient_bound {c : ℂ}
    (hl : (1 / 2 : ℝ) ≤ c.re) (hu : c.re ≤ 1) (hi : |c.im| ≤ (141 / 10 : ℝ))
    (n : ℕ) : ‖iteratedDeriv n xiCompleted c / (n.factorial : ℂ)‖ ≤ 1000 := by
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos n))).mpr
  exact (coefficient_bound hl hu hi n).trans_eq (by ring)

end Reinmann.XiLocalCauchy

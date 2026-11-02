/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.EulerMaclaurinAnalytic
public import Mathlib.Analysis.Complex.Liouville

@[expose] public section

/-! Rational, kernel-checked ordinary zeta-jet error bounds on the hard disk.
Twenty Dirichlet terms and the order-12 corrections suffice for this coarse
uniform bound. No Arb enclosure is imported as a theorem. -/
noncomputable section
namespace Reinmann.ZetaJetRemainder
open Polynomial MeasureTheory Set Finset
open EulerMaclaurinFinite EulerMaclaurinZeta EulerMaclaurinAnalytic
open scoped Topology

def zetaError (s : ℂ) : ℂ := riemannZeta s-finiteModel s 21

theorem hard_disk_norm_le {s : ℂ} (hs : ‖s - hardCentre‖ ≤ 1) : ‖s‖ ≤ 16 := by
  have hc : ‖hardCentre‖ ≤ (29/2 : ℝ) := by
    have h := norm_add_le (1/2 : ℂ) (14*Complex.I)
    norm_num [norm_mul] at h
    exact h
  calc ‖s‖ = ‖(s - hardCentre)+hardCentre‖ := by rw [sub_add_cancel]
    _ ≤ ‖s - hardCentre‖+‖hardCentre‖ := norm_add_le _ _
    _ ≤ 16 := by linarith

theorem rising_norm_le {s : ℂ} (hs : ‖s‖ ≤ 16) (n : ℕ) :
    ‖(ascPochhammer ℂ n).eval s‖ ≤ ∏ j ∈ range n, ((16 : ℝ)+j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, norm_mul, prod_range_succ]
    apply mul_le_mul ih _ (norm_nonneg _) (by positivity)
    exact (norm_add_le s (n : ℂ)).trans (by simpa using! add_le_add_right hs (n : ℝ))

theorem hard_disk_re_lower {s : ℂ} (hs : ‖s - hardCentre‖ ≤ 1) : (-1/2 : ℝ) ≤ s.re := by
  have hn : ‖hardCentre - s‖ ≤ 1 := by rw [norm_sub_rev]; exact hs
  have hr := (Complex.re_le_norm (hardCentre - s)).trans hn
  norm_num [hardCentre, Complex.sub_re] at hr
  linarith

theorem remainder_norm_le {s : ℂ} (hs : ‖s - hardCentre‖ ≤ 1) :
    ‖EulerMaclaurinTail.remainder s 21‖ ≤ (1/10^7 : ℝ) := by
  have hre := hard_disk_re_lower hs
  have hpos : 0 < s.re+11 := by linarith
  have hR := EulerMaclaurinTail.remainder_norm_le (by linarith : -11 < s.re)
    (by norm_num : (0 : ℝ) < 21)
  have hP := rising_norm_le (hard_disk_norm_le hs) 12
  have ha := div_le_div_of_nonneg_right hP (Nat.cast_nonneg (α := ℝ) (12 : ℕ).factorial)
  have hexp : (21 : ℝ)^(-s.re-11) ≤ (21 : ℝ)^(-10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hb : (6112/15015 : ℝ)*(21 : ℝ)^(-s.re-11)/(s.re+11) ≤
      (6112/15015 : ℝ)*(21 : ℝ)^(-10 : ℝ)/(21/2) := by
    calc _ ≤ (6112/15015 : ℝ)*(21 : ℝ)^(-10 : ℝ)/(s.re+11) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by norm_num)) hpos.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have hfinal := mul_le_mul ha hb (by positivity)
    (by positivity : 0 ≤ (∏ j ∈ range 12, ((16 : ℝ)+j))/((12 : ℕ).factorial : ℝ))
  apply hR.trans (hfinal.trans _)
  norm_num [Real.rpow_neg, Real.rpow_natCast, prod_range_succ]

theorem zetaError_norm_le {s : ℂ} (hs : ‖s - hardCentre‖ ≤ 1) :
    ‖zetaError s‖ ≤ (1/10^7 : ℝ) := by
  rw [zetaError, hard_disk_identity hs 21 (by norm_num), add_sub_cancel_left]
  exact remainder_norm_le hs

theorem hard_disk_ne_one {s : ℂ} (hs : ‖s - hardCentre‖ ≤ 1) : s ≠ 1 := by
  intro h
  have hi := (hard_disk_domain hs).2
  rw [h] at hi
  norm_num at hi

theorem zetaError_differentiableAt {s : ℂ} (hs : ‖s - hardCentre‖ ≤ 1) :
    DifferentiableAt ℂ zetaError s :=
  (differentiableAt_riemannZeta (hard_disk_ne_one hs)).sub
    (model_differentiableAt (hard_disk_ne_one hs) 21 (by norm_num))

theorem zetaError_diffContOnCl : DiffContOnCl ℂ zetaError (Metric.ball hardCentre 1) := by
  apply DifferentiableOn.diffContOnCl
  intro s hs
  rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)] at hs
  exact (zetaError_differentiableAt (mem_closedBall_iff_norm.mp hs)).differentiableWithinAt

theorem zetaError_coefficient_le (n : ℕ) :
    ‖iteratedDeriv n zetaError hardCentre/(n.factorial : ℂ)‖ ≤ (1/10^7 : ℝ) := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0 : ℝ) < 1) zetaError_diffContOnCl
    (fun z hz => zetaError_norm_le (mem_sphere_iff_norm.mp hz).le)
  simp only [one_pow, div_one] at h
  rw [norm_div, Complex.norm_natCast]
  exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos n))).mpr (h.trans_eq (by ring))

/-- Explicit comparison of the actual ordinary zeta coefficients with the
finite 20-term model, valid at every order (hence through degree sixteen). -/
theorem zeta_coefficient_error_le (n : ℕ) :
    ‖iteratedDeriv n riemannZeta hardCentre/(n.factorial : ℂ) -
      iteratedDeriv n (fun z => finiteModel z 21) hardCentre/(n.factorial : ℂ)‖ ≤
      (1/10^7 : ℝ) := by
  have hF : AnalyticAt ℂ riemannZeta hardCentre := by
    apply DifferentiableOn.analyticAt (s := Metric.ball hardCentre 1)
      _ (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1))
    intro z hz
    exact (differentiableAt_riemannZeta
      (hard_disk_ne_one (mem_ball_iff_norm.mp hz).le)).differentiableWithinAt
  have hG : AnalyticAt ℂ (fun z => finiteModel z 21) hardCentre := by
    apply DifferentiableOn.analyticAt (s := Metric.ball hardCentre 1)
      _ (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1))
    intro z hz
    exact (model_differentiableAt (hard_disk_ne_one (mem_ball_iff_norm.mp hz).le)
      21 (by norm_num)).differentiableWithinAt
  have h := zetaError_coefficient_le n
  rw [show zetaError = (fun z => riemannZeta z-finiteModel z 21) from rfl] at h
  rw [iteratedDeriv_fun_sub hF.contDiffAt hG.contDiffAt, sub_div] at h
  exact h

end Reinmann.ZetaJetRemainder

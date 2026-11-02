/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal

The integral comparison is adapted from OpenAI math,
OAI/NumberTheory/CubicMoment/Estimates/GammaElementaryGrowth.lean,
blob 362a26a92faefda3dcc04466bb6bb2e99c71d7a5 (Apache-2.0).
The finite-product refinement retains the recurrence denominator explicitly.
-/
module

public import Reinmann.JensenProgram
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! Explicit finite Gamma bounds, indexed by a shift and by height.
A numerical Xi strip majorant additionally needs a proved zeta bound. -/
noncomputable section
namespace Reinmann.GammaHeightMajorant
open MeasureTheory Set Finset Complex

/-- Integral comparison, ported at file granularity rather than importing OAI. -/
theorem gamma_norm_le_real {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs,Complex.GammaIntegral,Real.Gamma_eq_integral hs]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul,Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- Unlike a coarse shift inequality, this identity retains every height factor. -/
theorem gamma_shift_norm {s : ℂ} (hi : s.im ≠ 0) (n : ℕ) :
    ‖Complex.Gamma s‖*(∏ k ∈ range n, ‖s+(k : ℂ)‖) = ‖Complex.Gamma (s+n)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : s+(n : ℂ) ≠ 0 := by
      intro h
      have hm := congrArg Complex.im h
      apply hi
      simpa using! hm
    rw [prod_range_succ,← mul_assoc,ih]
    rw [Nat.cast_add,Nat.cast_one,← add_assoc,Complex.Gamma_add_one _ hn,norm_mul]
    ring

/-- Explicit finite-product majorant; no unknown Stirling constant is used. -/
theorem gamma_norm_le_shift_product {s : ℂ} (hi : s.im ≠ 0) (n : ℕ)
    (hr : 0 < s.re+n) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma (s.re+n)/(∏ k ∈ range n, ‖s+(k : ℂ)‖) := by
  have hp : 0 < ∏ k ∈ range n, ‖s+(k : ℂ)‖ := by
    apply prod_pos
    intro k _
    apply norm_pos_iff.mpr
    intro h
    have hm := congrArg Complex.im h
    apply hi
    simpa using! hm
  apply (le_div_iff₀ hp).mpr
  rw [gamma_shift_norm hi]
  simpa using! gamma_norm_le_real (s := s+n) (by simpa using! hr)

/-- A simple height-only version, useful for deciding the finite shift size. -/
theorem gamma_norm_le_height {s : ℂ} {H : ℝ} (hH : 0 < H) (hi : H ≤ |s.im|)
    (n : ℕ) (hr : 0 < s.re+n) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma (s.re+n)/H^n := by
  have hne : s.im ≠ 0 := by intro h; simp [h] at hi; linarith
  have hb : H^n ≤ ∏ k ∈ range n, ‖s+(k : ℂ)‖ := by
    have h := prod_le_prod₀ (fun k (_ : k ∈ range n) => hH.le)
      (fun k _ => hi.trans (by simpa using! Complex.abs_im_le_norm (s+(k : ℂ))))
    simpa using! h
  have h := gamma_norm_le_shift_product hne n hr
  have hGamma : 0 ≤ Real.Gamma (s.re+n) := (Real.Gamma_pos_of_pos hr).le
  exact h.trans (div_le_div_of_nonneg_left hGamma (pow_pos hH n) hb)

/-- The explicit Gamma factor in the actual Xi target, with a finite shift.
The remaining zeta factor is shown explicitly, rather than hidden in a constant. -/
theorem xi_norm_le_gamma_product {s : ℂ} (hr : 0 < s.re) (h1 : s ≠ 1)
    (hi : s.im ≠ 0) (n : ℕ) :
    ‖xiCompleted s‖ ≤ (‖s‖*‖s-1‖/2) * ‖(Real.pi : ℂ)^(-s/2)‖ *
      (Real.Gamma (s.re/2+n)/(∏ k ∈ range n, ‖s/2+(k : ℂ)‖)) * ‖riemannZeta s‖ := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hr
  have hgamma : Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hr
  have heq : completedRiemannZeta s = Gammaℝ s*riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero h0]
    field_simp
  have him : (s/2).im ≠ 0 := by simpa using! hi
  have hb := gamma_norm_le_shift_product (s := s/2) him n (by
    simp only [Complex.div_ofNat_re]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith)
  simp only [Complex.div_ofNat_re] at hb
  rw [xiCompleted_eq_product h0 h1,heq,Complex.Gammaℝ_def]
  simp only [norm_mul,norm_div,Complex.norm_ofNat]
  have hm := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (div_nonneg (mul_nonneg (norm_nonneg s) (norm_nonneg (s-1))) (by norm_num : (0 : ℝ) ≤ 2))
      (norm_nonneg ((Real.pi : ℂ)^(-s/2))))
  have hm' := mul_le_mul_of_nonneg_right hm (norm_nonneg (riemannZeta s))
  nlinarith only [hm']

end Reinmann.GammaHeightMajorant

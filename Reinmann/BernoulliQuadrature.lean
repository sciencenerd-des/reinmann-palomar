/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! Unit-cell Bernoulli integration by parts, with actual polynomial constants.
This is finite quadrature, not yet the analytic continuation identity for zeta. -/
noncomputable section
namespace Reinmann.BernoulliQuadrature
open Polynomial MeasureTheory Set Finset
open scoped Interval

def kernel (n : ℕ) (t : ℝ) : ℂ :=
  aeval (t : ℂ) (Polynomial.bernoulli n) / (n.factorial : ℂ)

theorem kernel_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (kernel (n+1)) (kernel n t) t := by
  have h := ((Polynomial.bernoulli (n+1)).hasDerivAt_aeval (t : ℂ)).comp_ofReal
  have h' := h.div_const ((n+1).factorial : ℂ)
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hnp : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hk : kernel (n+1) =
      fun x : ℝ => aeval (x : ℂ) (Polynomial.bernoulli (n+1)) / ((n+1).factorial : ℂ) := rfl
  rw [hk]
  convert h' using 1
  · rw [Polynomial.derivative_bernoulli_add_one]
    simp only [map_mul, map_add, map_natCast, map_one, kernel,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp

theorem kernel_continuous (n : ℕ) : Continuous (kernel n) := by
  exact ((Polynomial.bernoulli n).continuous_aeval.comp Complex.continuous_ofReal).div_const _

theorem kernel_zero (t : ℝ) : kernel 0 t = 1 := by simp [kernel]

theorem kernel_one (t : ℝ) : kernel 1 t = (t : ℂ)-1/2 := by
  simp [kernel, Polynomial.bernoulli_one]

theorem kernel_at_zero (n : ℕ) :
    kernel n 0 = (_root_.bernoulli n : ℂ)/(n.factorial : ℂ) := by
  simp [kernel, Polynomial.aeval_def, Polynomial.coeff_bernoulli]

theorem kernel_at_one (n : ℕ) (hn : n ≠ 1) :
    kernel n 1 = kernel n 0 := by
  simp only [kernel, Complex.ofReal_one, Complex.ofReal_zero, Polynomial.aeval_def]
  have hzero : Polynomial.eval₂ (algebraMap ℚ ℂ) 0 (Polynomial.bernoulli n) =
      algebraMap ℚ ℂ ((Polynomial.bernoulli n).eval 0) := by
    simpa using! Polynomial.eval₂_at_apply (p := Polynomial.bernoulli n) (algebraMap ℚ ℂ) 0
  rw [Polynomial.eval₂_at_one, hzero,
    Polynomial.bernoulli_eval_one, Polynomial.bernoulli_eval_zero,
    ← bernoulli_eq_bernoulli'_of_ne_one hn]

/-- One integration-by-parts step. Neither the remainder integral nor the
Bernoulli endpoint coefficient is assumed as an algebraic identity. -/
theorem integration_step (n : ℕ) {f g : ℝ → ℂ}
    (hf : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt f (g t) t)
    (hg : IntervalIntegrable g volume 0 1) :
    (∫ t in (0 : ℝ)..1, kernel n t * f t) =
      kernel (n+1) 1*f 1-kernel (n+1) 0*f 0 -
        ∫ t in (0 : ℝ)..1, kernel (n+1) t*g t := by
  have hk := fun t (_ : t ∈ Set.uIcc (0 : ℝ) 1) => kernel_hasDerivAt n t
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul hk hf
    ((kernel_continuous n).intervalIntegrable 0 1) hg
  linear_combination hi

/-- Exact all-orders unit-cell quadrature for an actual derivative chain.
The last term is an integral remainder, not a claimed numerical bound. -/
theorem finite_quadrature (F : ℕ → ℝ → ℂ)
    (hF : ∀ k t, t ∈ Set.uIcc (0 : ℝ) 1 → HasDerivAt (F k) (F (k + 1) t) t)
    (m : ℕ) :
    (∫ t in (0 : ℝ)..1, F 0 t) =
      (∑ k ∈ range m, (-1 : ℂ)^k *
        (kernel (k+1) 1*F k 1-kernel (k+1) 0*F k 0)) +
      (-1 : ℂ)^m*(∫ t in (0 : ℝ)..1, kernel m t*F m t) := by
  have hI (k : ℕ) : IntervalIntegrable (F k) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    exact (hF k t ht).continuousAt.continuousWithinAt
  induction m with
  | zero => simp [kernel_zero]
  | succ m ih =>
    have hstep := integration_step m (hF m) (hI (m+1))
    rw [ih, hstep, sum_range_succ, pow_succ]
    ring

end Reinmann.BernoulliQuadrature

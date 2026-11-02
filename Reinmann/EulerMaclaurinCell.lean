/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.BernoulliQuadrature
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Exact Bernoulli quadrature applied to the shifted complex power itself.
This finite cell formula does not assume a derivative chain as input and does
not assert the infinite Euler--Maclaurin identity for zeta. -/
noncomputable section
namespace Reinmann.EulerMaclaurinCell
open Polynomial MeasureTheory Set Finset
open scoped Interval

/-- The actual spatial derivatives of the shifted power. -/
def powerDerivative (s : ℂ) (N : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  (-1 : ℂ)^k * (ascPochhammer ℂ k).eval s * ((t : ℂ)+(N : ℂ))^(-s-(k : ℂ))

theorem powerDerivative_hasDerivAt (s : ℂ) (N : ℝ) (k : ℕ) {t : ℝ}
    (ht : 0 < t + N) :
    HasDerivAt (powerDerivative s N k) (powerDerivative s N (k+1) t) t := by
  have hz : (t : ℂ)+(N : ℂ) ∈ Complex.slitPlane := by
    rw [← Complex.ofReal_add, Complex.ofReal_mem_slitPlane]
    exact ht
  have h := (((hasDerivAt_id (t : ℂ)).add_const (N : ℂ)).cpow_const
    (c := -s-(k : ℂ)) hz).comp_ofReal
  have h' := h.const_mul ((-1 : ℂ)^k * (ascPochhammer ℂ k).eval s)
  convert h' using 1
  · funext y; simp [powerDerivative]
  · simp only [id_eq, mul_one, powerDerivative, ascPochhammer_succ_eval,
      pow_succ, Nat.cast_add, Nat.cast_one]
    have he : -s-((k : ℂ)+1) = -s-(k : ℂ)-1 := by ring
    rw [he]
    ring

theorem powerDerivative_zero (s : ℂ) (N t : ℝ) :
    powerDerivative s N 0 t = ((t : ℂ)+(N : ℂ))^(-s) := by
  simp [powerDerivative]

/-- Exact finite-order formula on any cell starting at a positive real N. -/
theorem finite_cell (s : ℂ) {N : ℝ} (hN : 0 < N) (m : ℕ) :
    (∫ t in (0 : ℝ)..1, ((t : ℂ)+(N : ℂ))^(-s)) =
      (∑ k ∈ range m, (-1 : ℂ)^k *
        (BernoulliQuadrature.kernel (k+1) 1*powerDerivative s N k 1 -
          BernoulliQuadrature.kernel (k+1) 0*powerDerivative s N k 0)) +
      (-1 : ℂ)^m * (∫ t in (0 : ℝ)..1,
        BernoulliQuadrature.kernel m t*powerDerivative s N m t) := by
  have hF : ∀ k t, t ∈ Set.uIcc (0 : ℝ) 1 →
      HasDerivAt (powerDerivative s N k) (powerDerivative s N (k+1) t) t := by
    intro k t ht
    have ht0 : 0 ≤ t := (Set.mem_uIcc.mp ht).elim (fun h => h.1) (by
      intro h
      linarith [h.1, h.2])
    exact powerDerivative_hasDerivAt s N k (by linarith)
  simpa only [powerDerivative_zero] using!
    BernoulliQuadrature.finite_quadrature (powerDerivative s N) hF m

end Reinmann.EulerMaclaurinCell

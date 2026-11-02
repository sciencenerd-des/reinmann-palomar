/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.RiemannSpine
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

/-!
# Conjugate Symmetry in the Dirichlet-Series Half-Plane

This file proves the part of zeta conjugate symmetry available directly from
the Dirichlet series: if `1 < s.re`, then
`ζ(conj s) = conj (ζ s)`.

The global critical-strip statement remains a separate analytic-continuation
gap.
-/

noncomputable section

open Complex
open scoped ComplexConjugate

namespace Reinmann

/-! ### Half-plane topology -/

/-- The Dirichlet-series half-plane is open. -/
theorem one_lt_re_halfPlane_isOpen : IsOpen {s : ℂ | 1 < s.re} := by
  simpa [Set.preimage, Set.mem_setOf_eq] using! isOpen_Ioi.preimage Complex.continuous_re

/-- The Dirichlet-series half-plane is preconnected, since it is convex. -/
theorem one_lt_re_halfPlane_isPreconnected :
    IsPreconnected {s : ℂ | 1 < s.re} := by
  exact (convex_halfSpace_re_gt (r := 1)).isPreconnected

/-- The Dirichlet-series half-plane is connected, since it is nonempty and convex. -/
theorem one_lt_re_halfPlane_isConnected :
    IsConnected {s : ℂ | 1 < s.re} := by
  exact (convex_halfSpace_re_gt (r := 1)).isConnected ⟨(2 : ℂ), by norm_num⟩

/-- Positive real bases commute with complex conjugation under `cpow`. -/
theorem conj_ofReal_cpow (r : ℝ) (hr : 0 < r) (s : ℂ) :
    conj ((r : ℂ) ^ s) = (r : ℂ) ^ (conj s) := by
  have h_ne_zero : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero h_ne_zero,
    Complex.cpow_def_of_ne_zero h_ne_zero]
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul]
  have hlog : Complex.log (r : ℂ) = (Real.log r : ℂ) :=
    (Complex.ofReal_log hr.le).symm
  rw [hlog, Complex.conj_ofReal]

/-- Positive natural bases commute with complex conjugation under `cpow`. -/
theorem conj_natCast_cpow (n : ℕ) (hn : 0 < n) (s : ℂ) :
    conj ((n : ℂ) ^ s) = (n : ℂ) ^ (conj s) := by
  have hpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  exact conj_ofReal_cpow (n : ℝ) hpos s

/-- The Dirichlet-series term `1 / n ^ s` commutes with conjugation. -/
theorem conj_inv_natCast_cpow (n : ℕ) (hn : 0 < n) (s : ℂ) :
    conj (1 / (n : ℂ) ^ s) = 1 / (n : ℂ) ^ (conj s) := by
  rw [map_div₀, map_one, conj_natCast_cpow n hn s]

/-- In `1 < s.re`, zeta equals the standard Dirichlet series. -/
theorem dirichletSeries_eq_riemannZeta (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, if n = 0 then 0 else 1 / (n : ℂ) ^ s := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  congr 1
  funext n
  by_cases hn : n = 0
  · simp [hn, Complex.zero_cpow (Complex.ne_zero_of_one_lt_re hs)]
  · simp [hn]

/-- The same Dirichlet-series terms are summable in `1 < s.re`. -/
theorem summable_dirichletSeries_terms (s : ℂ) (hs : 1 < s.re) :
    Summable fun n : ℕ => if n = 0 then (0 : ℂ) else 1 / (n : ℂ) ^ s := by
  have h : Summable fun n : ℕ => 1 / (n : ℂ) ^ s :=
    Complex.summable_one_div_nat_cpow.mpr hs
  convert h using 1
  all_goals try rfl
  funext n
  by_cases hn : n = 0
  · simp [hn, Complex.zero_cpow (Complex.ne_zero_of_one_lt_re hs)]
  · simp [hn]

/-- Complex conjugation commutes with a summable series. -/
theorem conj_tsum_nat {f : ℕ → ℂ} :
    conj (∑' n, f n) = ∑' n, conj (f n) := by
  exact tsum_star

/-- Zeta has conjugate symmetry in the Dirichlet-series half-plane. -/
theorem riemannZeta_conj_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    riemannZeta (conj s) = conj (riemannZeta s) := by
  have h_conj_re : 1 < (conj s).re := by simpa using! hs
  rw [dirichletSeries_eq_riemannZeta (conj s) h_conj_re]
  rw [dirichletSeries_eq_riemannZeta s hs]
  rw [conj_tsum_nat]
  congr 1
  funext n
  by_cases hn : n = 0
  · simp [hn, map_zero]
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    simp only [hn, ↓reduceIte]
    exact (conj_inv_natCast_cpow n hn_pos s).symm

end Reinmann

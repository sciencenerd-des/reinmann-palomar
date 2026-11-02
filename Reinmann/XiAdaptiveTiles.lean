/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.EnclosureRules
public import Reinmann.XiDividedDifference
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Adaptive finite covers with local derivative bounds, and the actual Xi
quarter-rectangle reduction. This module supplies rules, not numerical tiles. -/
noncomputable section
namespace Reinmann.XiAdaptiveTiles
open Set Complex
open scoped ComplexConjugate

/-- Different tiles may have different shapes, radii, derivatives and errors. -/
theorem adaptive_cover_nonzero {n : ℕ} {f : ℂ → ℂ} {S : Set ℂ}
    (tiles : Fin n → Set ℂ) (c v : Fin n → ℂ) (radius K ε : Fin n → ℝ)
    (hconvex : ∀ i, Convex ℝ (tiles i)) (hc : ∀ i, c i ∈ tiles i)
    (hd : ∀ i z, z ∈ tiles i → DifferentiableAt ℂ f z)
    (hK : ∀ i, 0 ≤ K i) (hderiv : ∀ i z, z ∈ tiles i → ‖deriv f z‖ ≤ K i)
    (hcentre : ∀ i, ‖f (c i) - v i‖ ≤ ε i)
    (hcover : ∀ z ∈ S, ∃ i, z ∈ tiles i ∧ ‖z - c i‖ ≤ radius i)
    (hmargin : ∀ i, ε i + K i * radius i < ‖v i‖) :
    ∀ z ∈ S, f z ≠ 0 := by
  intro z hz
  obtain ⟨i, hi, hr⟩ := hcover z hz
  exact EnclosureRules.tile_nonzero (hK i) (hcentre i) hr
    (EnclosureRules.variation_of_deriv (hconvex i) (hd i) (hderiv i) (hc i) hi)
    (hmargin i)

/-- Both symmetry boundaries are retained. -/
def quarter (H : ℝ) : Set ℂ :=
  {z | (1 / 2 : ℝ) ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ H}

/-- Reflection and conjugation reduce the closed critical rectangle to a quarter. -/
theorem rectangle_nonzero_of_quarter {f : ℂ → ℂ} {H : ℝ}
    (hreflect : ∀ z, f (1 - z) = f z)
    (hconj : ∀ z, f (conj z) = conj (f z))
    (hq : ∀ z ∈ quarter H, f z ≠ 0) {z : ℂ}
    (hx0 : 0 ≤ z.re) (hx1 : z.re ≤ 1) (hyH : |z.im| ≤ H) : f z ≠ 0 := by
  intro hzero
  have hy := abs_le.mp hyH
  by_cases hx : (1 / 2 : ℝ) ≤ z.re
  · by_cases hiy : 0 ≤ z.im
    · exact hq z ⟨hx, hx1, hiy, hy.2⟩ hzero
    · have hw : conj z ∈ quarter H := by
        change (1 / 2 : ℝ) ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ -z.im ∧ -z.im ≤ H
        exact ⟨hx, hx1, by linarith, by linarith⟩
      apply hq (conj z) hw
      rw [hconj, hzero]
      simp
  · by_cases hiy : 0 ≤ z.im
    · have hw : conj (1 - z) ∈ quarter H := by
        simp only [quarter, mem_setOf_eq, conj_re, conj_im, sub_re, one_re,
          sub_im, one_im, zero_sub, neg_neg]
        exact ⟨by linarith, by linarith, hiy, hy.2⟩
      apply hq (conj (1 - z)) hw
      rw [hconj, hreflect, hzero]
      simp
    · have hw : 1 - z ∈ quarter H := by
        simp only [quarter, mem_setOf_eq, sub_re, one_re, sub_im, one_im, zero_sub]
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩
      exact hq (1 - z) hw (by rw [hreflect, hzero])

/-- The reduction uses the proved symmetries of actual Xi, not the zero set of Λ₀. -/
theorem xi_rectangle_nonzero_of_quarter {H : ℝ}
    (hq : ∀ z ∈ quarter H, xiCompleted z ≠ 0) {z : ℂ}
    (hx0 : 0 ≤ z.re) (hx1 : z.re ≤ 1) (hyH : |z.im| ≤ H) : xiCompleted z ≠ 0 :=
  rectangle_nonzero_of_quarter XiDividedDifference.xi_one_sub
    XiDividedDifference.xi_conj hq hx0 hx1 hyH

end Reinmann.XiAdaptiveTiles

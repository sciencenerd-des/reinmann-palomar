/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.XiAdaptiveTiles
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! A closed rational cell is covered by a ball if its four corners are.
Binary subdivisions retain their shared edges, so no mesh boundary is omitted. -/
noncomputable section
namespace Reinmann.RationalBallCover

def rectangle (x0 x1 y0 y1 : ℝ) : Set ℂ :=
  {z | x0 ≤ z.re ∧ z.re ≤ x1 ∧ y0 ≤ z.im ∧ z.im ≤ y1}

theorem square_between {a x b c : ℝ} (ha : a ≤ x) (hb : x ≤ b) :
    (x - c) ^ 2 ≤ max ((a - c) ^ 2) ((b - c) ^ 2) := by
  by_cases hc : c ≤ x
  · exact (pow_le_pow_left₀ (sub_nonneg.mpr hc) (sub_le_sub_right hb c) 2).trans
      (le_max_right _ _)
  · have h := pow_le_pow_left₀ (sub_nonneg.mpr (not_le.mp hc).le)
      (sub_le_sub_left ha c) 2
    apply le_trans _ (le_max_left _ _)
    nlinarith

/-- Squared corner distances avoid a numerical square-root oracle. -/
theorem rectangle_ball {x0 x1 y0 y1 r : ℝ} {c z : ℂ} (hr : 0 ≤ r)
    (h00 : (x0 - c.re) ^ 2 + (y0 - c.im) ^ 2 ≤ r ^ 2)
    (h01 : (x0 - c.re) ^ 2 + (y1 - c.im) ^ 2 ≤ r ^ 2)
    (h10 : (x1 - c.re) ^ 2 + (y0 - c.im) ^ 2 ≤ r ^ 2)
    (h11 : (x1 - c.re) ^ 2 + (y1 - c.im) ^ 2 ≤ r ^ 2)
    (hz : z ∈ rectangle x0 x1 y0 y1) : ‖z - c‖ ≤ r := by
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hz
  have hx := square_between (c := c.re) hx0 hx1
  have hy := square_between (c := c.im) hy0 hy1
  have hmax : max ((x0 - c.re) ^ 2) ((x1 - c.re) ^ 2) +
      max ((y0 - c.im) ^ 2) ((y1 - c.im) ^ 2) ≤ r ^ 2 := by
    rcases le_total ((x0 - c.re) ^ 2) ((x1 - c.re) ^ 2) with hxr | hxl <;>
      rcases le_total ((y0 - c.im) ^ 2) ((y1 - c.im) ^ 2) with hyr | hyl
    · simpa only [max_eq_right hxr, max_eq_right hyr] using! h11
    · simpa only [max_eq_right hxr, max_eq_left hyl] using! h10
    · simpa only [max_eq_left hxl, max_eq_right hyr] using! h01
    · simpa only [max_eq_left hxl, max_eq_left hyl] using! h00
  have hn : ‖z - c‖ ^ 2 = (z.re - c.re) ^ 2 + (z.im - c.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  exact (sq_le_sq₀ (norm_nonneg _) hr).mp (by nlinarith)

theorem split_x {P : ℂ → Prop} {x0 x1 xm y0 y1 : ℝ}
    (hleft : ∀ z ∈ rectangle x0 xm y0 y1, P z)
    (hright : ∀ z ∈ rectangle xm x1 y0 y1, P z) :
    ∀ z ∈ rectangle x0 x1 y0 y1, P z := by
  intro z hz
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hz
  by_cases hx : z.re ≤ xm
  · exact hleft z ⟨hx0, hx, hy0, hy1⟩
  · exact hright z ⟨(not_le.mp hx).le, hx1, hy0, hy1⟩

theorem split_y {P : ℂ → Prop} {x0 x1 y0 y1 ym : ℝ}
    (hlower : ∀ z ∈ rectangle x0 x1 y0 ym, P z)
    (hupper : ∀ z ∈ rectangle x0 x1 ym y1, P z) :
    ∀ z ∈ rectangle x0 x1 y0 y1, P z := by
  intro z hz
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hz
  by_cases hy : z.im ≤ ym
  · exact hlower z ⟨hx0, hx1, hy0, hy⟩
  · exact hupper z ⟨hx0, hx1, (not_le.mp hy).le, hy1⟩

end Reinmann.RationalBallCover

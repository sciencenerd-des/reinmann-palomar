/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Enclosure rules with variation inside intervals and a proved closed grid cover.
These are certificate rules, not certificates for a particular function. -/
noncomputable section
namespace Reinmann.EnclosureRules
open Set MeasureTheory

/-- A quadrature tile must enclose every integrand value, not only its sample. -/
theorem integral_tile_error {f : ℝ → ℂ} {a b ε : ℝ} {v : ℂ}
    (hf : IntervalIntegrable f volume a b)
    (hb : ∀ t ∈ Set.uIoc a b, ‖f t-v‖ ≤ ε) :
    ‖(∫ t in a..b, f t) - (b-a) • v‖ ≤ ε * |b-a| := by
  rw [← intervalIntegral.integral_const, ← intervalIntegral.integral_sub hf
    intervalIntegrable_const]
  exact intervalIntegral.norm_integral_le_of_norm_le_const hb

/-- Midpoint quadrature with a certified sample error and derivative control
throughout the tile. The error includes variation between sample points. -/
theorem integral_midpoint_error {f : ℝ → ℂ} {a b ε K : ℝ} {v : ℂ}
    (hab : a ≤ b) (hK : 0 ≤ K) (hf : IntervalIntegrable f volume a b)
    (hd : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hderiv : ∀ t ∈ Icc a b, ‖deriv f t‖ ≤ K)
    (hv : ‖f ((a+b)/2)-v‖ ≤ ε) :
    ‖(∫ t in a..b, f t) - (b-a) • v‖ ≤ (ε+K*((b-a)/2))*(b-a) := by
  have hc : (a+b)/2 ∈ Icc a b := by constructor <;> linarith
  have hb (t : ℝ) (ht : t ∈ Set.uIoc a b) : ‖f t-v‖ ≤ ε+K*((b-a)/2) := by
    have ht' : t ∈ Icc a b := by
      rw [Set.uIoc_of_le hab] at ht
      exact ⟨ht.1.le,ht.2⟩
    have hvar := (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le hd hderiv hc ht'
    have hdist : ‖t-(a+b)/2‖ ≤ (b-a)/2 := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [ht'.1,ht'.2]
    calc
      ‖f t-v‖ = ‖(f t-f ((a+b)/2))+(f ((a+b)/2)-v)‖ := by congr 1; ring
      _ ≤ ‖f t-f ((a+b)/2)‖+‖f ((a+b)/2)-v‖ := norm_add_le _ _
      _ ≤ K*((b-a)/2)+ε := add_le_add
        (hvar.trans (mul_le_mul_of_nonneg_left hdist hK)) hv
      _ = _ := by ring
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using! integral_tile_error hf hb

/-- A derivative bound supplies the missing within-tile variation. -/
theorem variation_of_deriv {f : ℂ → ℂ} {S : Set ℂ} {K : ℝ} {c z : ℂ}
    (hS : Convex ℝ S) (hf : ∀ w ∈ S, DifferentiableAt ℂ f w)
    (hK : ∀ w ∈ S, ‖deriv f w‖ ≤ K) (hc : c ∈ S) (hz : z ∈ S) :
    ‖f z-f c‖ ≤ K * ‖z-c‖ :=
  hS.norm_image_sub_le_of_norm_deriv_le hf hK hc hz

/-- An enclosure with a strictly positive modulus margin certifies the whole tile. -/
theorem tile_nonzero {f : ℂ → ℂ} {c z v : ℂ} {ε K ρ : ℝ}
    (hK : 0 ≤ K) (hc : ‖f c-v‖ ≤ ε) (hd : ‖z-c‖ ≤ ρ)
    (hv : ‖f z-f c‖ ≤ K * ‖z-c‖) (hmargin : ε + K*ρ < ‖v‖) :
    f z ≠ 0 := by
  intro hzero
  have ht : ‖f z-v‖ ≤ K*ρ+ε := by
    calc
      ‖f z-v‖ = ‖(f z-f c)+(f c-v)‖ := by congr 1; ring
      _ ≤ ‖f z-f c‖+‖f c-v‖ := norm_add_le _ _
      _ ≤ K*ρ+ε := add_le_add (hv.trans (mul_le_mul_of_nonneg_left hd hK)) hc
  rw [hzero, zero_sub, norm_neg] at ht
  linarith

/-- Every point of the CLOSED unit interval is covered, including the upper endpoint. -/
theorem unit_grid_cover {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    ∃ i : Fin (n+1), |x-(i.val : ℝ)/n| ≤ 1/n := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hi : Nat.floor (x*n) ≤ n := Nat.floor_le_of_le (by nlinarith)
  refine ⟨⟨Nat.floor (x*n), by omega⟩, ?_⟩
  have h0 := Nat.floor_le (mul_nonneg hx0 hnR.le)
  have h1 := Nat.lt_floor_add_one (x*n)
  rw [abs_of_nonneg (by apply sub_nonneg.mpr; exact (div_le_iff₀ hnR).mpr h0)]
  apply (le_div_iff₀ hnR).mpr
  rw [sub_mul, div_mul_cancel₀ _ hnR.ne']
  linarith

def gridCenter (H : ℝ) (n m : ℕ) (i : Fin (n+1)) (j : Fin (m+1)) : ℂ :=
  ((i.val : ℝ)/n : ℂ) + ((-H+2*H*(j.val : ℝ)/m : ℝ) : ℂ)*Complex.I

/-- A finite cover of the entire closed rectangle; no boundary strip is omitted. -/
theorem rectangle_grid_cover {H : ℝ} (hH : 0 < H) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) {z : ℂ}
    (hx0 : 0 ≤ z.re) (hx1 : z.re ≤ 1) (hy : |z.im| ≤ H) :
    ∃ i : Fin (n+1), ∃ j : Fin (m+1),
      ‖z-gridCenter H n m i j‖ ≤ 1/(n : ℝ)+2*H/m := by
  obtain ⟨i,hi⟩ := unit_grid_cover hx0 hx1 hn
  have h2 : 0 < 2*H := by positivity
  have hyy := abs_le.mp hy
  have hy0 : 0 ≤ (z.im+H)/(2*H) := div_nonneg (by linarith) h2.le
  have hy1 : (z.im+H)/(2*H) ≤ 1 := (div_le_one h2).mpr (by linarith)
  obtain ⟨j,hj⟩ := unit_grid_cover hy0 hy1 hm
  have him : |z.im-(-H+2*H*(j.val : ℝ)/m)| ≤ 2*H/m := by
    have he : z.im-(-H+2*H*(j.val : ℝ)/m) =
        (2*H)*((z.im+H)/(2*H)-(j.val : ℝ)/m) := by
      field_simp
      <;> ring
    rw [he, abs_mul, abs_of_pos h2]
    exact (mul_le_mul_of_nonneg_left hj h2.le).trans_eq (by ring)
  refine ⟨i,j,?_⟩
  have hc : z-gridCenter H n m i j =
      ((z.re-(i.val : ℝ)/n : ℝ) : ℂ) +
        ((z.im-(-H+2*H*(j.val : ℝ)/m) : ℝ) : ℂ)*Complex.I := by
    apply Complex.ext <;> simp [gridCenter] <;> ring
  rw [hc]
  calc
    _ ≤ ‖((z.re-(i.val : ℝ)/n : ℝ) : ℂ)‖ +
        ‖((z.im-(-H+2*H*(j.val : ℝ)/m) : ℝ) : ℂ)*Complex.I‖ := norm_add_le _ _
    _ = |z.re-(i.val : ℝ)/n| + |z.im-(-H+2*H*(j.val : ℝ)/m)| := by
      simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ _ := add_le_add hi him

/-- Once actual center enclosures and a valid variation bound are supplied,
every tile in the proved finite cover certifies nonvanishing on the rectangle. -/
theorem rectangle_nonzero {f : ℂ → ℂ} {H K : ℝ} {n m : ℕ}
    (hH : 0 < H) (hn : 0 < n) (hm : 0 < m) (hK : 0 ≤ K)
    (values : Fin (n+1) → Fin (m+1) → ℂ)
    (errors : Fin (n+1) → Fin (m+1) → ℝ)
    (hc : ∀ i j, ‖f (gridCenter H n m i j)-values i j‖ ≤ errors i j)
    (hv : ∀ i j z, 0 ≤ z.re → z.re ≤ 1 → |z.im| ≤ H →
      ‖f z-f (gridCenter H n m i j)‖ ≤ K*‖z-gridCenter H n m i j‖)
    (hmargin : ∀ i j, errors i j+K*(1/(n : ℝ)+2*H/m) < ‖values i j‖)
    {z : ℂ} (hx0 : 0 ≤ z.re) (hx1 : z.re ≤ 1) (hy : |z.im| ≤ H) : f z ≠ 0 := by
  obtain ⟨i,j,hij⟩ := rectangle_grid_cover hH hn hm hx0 hx1 hy
  exact tile_nonzero hK (hc i j) hij (hv i j z hx0 hx1 hy) (hmargin i j)

end Reinmann.EnclosureRules

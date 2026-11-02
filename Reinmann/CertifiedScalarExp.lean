/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.CertifiedHorner
public import Reinmann.CertifiedComplexInputs

@[expose] public section

/-! Range-reduced scalar exponential certificates. A certificate contains only
rational disks; all numerical obligations are finite rational inequalities. -/
noncomputable section
namespace Reinmann.CertifiedScalarExp
open CertifiedTaylorModel CertifiedComplexInputs CertifiedHorner

theorem disk_ext {a b : Disk} (hc : a.centre=b.centre) (hr : a.radius=b.radius) : a=b := by
  cases a
  cases b
  cases hc
  cases hr
  rfl

def piDisk : Disk :=
  ⟨(3.14159265358979323846, 0), 1/10^20, by norm_num⟩

theorem contains_real {a r : ℚ} (hr : 0 ≤ r) {x : ℝ}
    (hx : |x-(a : ℝ)| ≤ (r : ℝ)) : Contains (⟨(a,0),r,hr⟩ : Disk) (x : ℂ) := by
  unfold Contains value
  simp only [Rat.cast_zero, zero_mul, add_zero, ← Complex.ofReal_ratCast,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hx

theorem pi_contains : Contains piDisk (Real.pi : ℂ) := by
  apply contains_real
  have hl := Real.pi_gt_d20
  have hu := Real.pi_lt_d20
  rw [abs_le]
  norm_num
  constructor <;> linarith

structure Data where
  input : Disk
  turns : ℤ
  polynomial : ℕ → Disk
  squares : ℕ → Disk

def reduced (a : Data) : Disk :=
  mul (exact (1/64,0)) (add a.input (mul (exact (0,-2*(a.turns : ℚ))) piDisk))

def roundingCheck (a b : Disk) : Prop :=
  a.radius + size (a.centre.1-b.centre.1, a.centre.2-b.centre.2) ≤ b.radius

structure Checks (a : Data) : Prop where
  unit : size (reduced a).centre+(reduced a).radius ≤ 1
  polynomial_zero : a.polynomial 20 = zero
  polynomial_step : ∀ k < 20,
    roundingCheck (add (exact (1/(k.factorial : ℚ),0))
      (mul (reduced a) (a.polynomial (k+1)))) (a.polynomial k)
  square_zero : a.squares 0 = inflate (a.polynomial 0) (1/10^18) (by norm_num)
  square_step : ∀ k < 6,
    roundingCheck (mul (a.squares k) (a.squares k)) (a.squares (k+1))

/-- One replay covers exp at any complex value enclosed by the certified input. -/
theorem sound (a : Data) (hc : Checks a) {z : ℂ} (hz : Contains a.input z) :
    Contains (a.squares 6) (Complex.exp z) := by
  let w := (z-(a.turns : ℂ)*(2*(Real.pi : ℂ)*Complex.I))/64
  have hr : Contains (reduced a) w := by
    have h := contains_mul (contains_exact ((1/64 : ℚ),0))
      (contains_add hz (contains_mul (contains_exact (0,-2*(a.turns : ℚ))) pi_contains))
    have hv : value ((1/64 : ℚ),0)*(z+value (0,-2*(a.turns : ℚ))*(Real.pi : ℂ)) = w := by
      simp only [value, Rat.cast_zero, zero_mul, add_zero]
      dsimp [w]
      push_cast
      ring
    rw [hv] at h
    exact h
  have hu : ‖w‖ ≤ 1 := (norm_le_of_contains hr).trans (by exact_mod_cast hc.unit)
  have hp : Contains (a.polynomial 0) (∑ j ∈ Finset.range 20, w^j/(j.factorial : ℂ)) := by
    rw [← exp_horner_eq]
    apply horner_contains hr
    · rw [hc.polynomial_zero]
      exact contains_zero
    · exact hc.polynomial_step
  have he : Contains (a.squares 0) (Complex.exp w) := by
    rw [hc.square_zero]
    exact exp_series_contains hu hp
  have hs : ∀ k ≤ 6, Contains (a.squares k) ((Complex.exp w)^(2^k)) := by
    intro k
    induction k with
    | zero => simpa using! he
    | succ k ih =>
      intro hk
      have hi := ih (by omega)
      have hh := contains_mul hi hi
      have ht := contains_round (a.squares (k+1)).radius_nonneg (hc.square_step k (by omega)) hh
      have hv : Complex.exp w^(2^k)*Complex.exp w^(2^k) = Complex.exp w^(2^(k+1)) := by
        rw [pow_succ, pow_mul, pow_two]
      rw [hv] at ht
      exact ht
  have h := hs 6 (by norm_num)
  norm_num only [show (2 : ℕ)^6=64 by norm_num] at h
  rw [← Complex.exp_nat_mul] at h
  have hw : (64 : ℂ)*w = z-(a.turns : ℂ)*(2*(Real.pi : ℂ)*Complex.I) := by
    dsimp [w]
    ring
  norm_num only at h
  rw [hw, Complex.exp_periodic.sub_int_mul_eq] at h
  exact h

end Reinmann.CertifiedScalarExp

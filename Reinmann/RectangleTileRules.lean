/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.RectangleTaylor
public import Reinmann.XiAdaptiveTiles
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-! Degree-independent derivative bounds from ordinary coefficients and a proved
unit-circle coefficient majorant. This rule does not assume a zero-free region. -/
noncomputable section
namespace Reinmann.RectangleTileRules
open Finset Metric CertifiedTaylorModel CertifiedTaylorComposition

theorem derivative_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f) (d : ℕ) {c z : ℂ} {M r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hz : ‖z-c‖ ≤ r)
    (hM : ∀ n, ‖coefficient f c n‖ ≤ M) :
    ‖deriv f z‖ ≤
      (∑ n ∈ range d, ((n+1 : ℕ) : ℝ)*‖coefficient f c (n+1)‖*r^n) +
      M*r^d*(r/(1-r)^2+((d : ℝ) + 1)/(1-r)) := by
  let t : ℕ → ℂ := fun n => ((n+1 : ℕ) : ℂ)*coefficient f c (n+1)*(z-c)^n
  have hd : Differentiable ℂ (deriv f) := fun w => (hf.analyticAt w).deriv.differentiableAt
  have hs : HasSum t (deriv f z) := by
    convert Complex.hasSum_taylorSeries_of_entire hd c z using 1
    funext n
    dsimp [t]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [← coefficient_deriv]
    simp only [coefficient, smul_eq_mul, div_eq_mul_inv]
    ring
  have htnorm (n : ℕ) : ‖t n‖ =
      ((n+1 : ℕ) : ℝ)*‖coefficient f c (n+1)‖*‖z-c‖^n := by
    simp only [t, norm_mul, norm_pow, Complex.norm_natCast]
  have ht (n : ℕ) : ‖t n‖ ≤ ((n+1 : ℕ) : ℝ)*‖coefficient f c (n+1)‖*r^n := by
    rw [htnorm]
    gcongr
  have hnorm : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos hr0] using! hr1
  have hgeo := hasSum_geometric_of_norm_lt_one hnorm
  have hnat := hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have hg : HasSum (fun k : ℕ => M*r^d*((k : ℝ)+((d : ℝ) + 1))*r^k)
      (M*r^d*(r/(1-r)^2+((d : ℝ) + 1)/(1-r))) := by
    convert (hnat.add (hgeo.mul_left ((d : ℝ) + 1))).mul_left (M*r^d) using 1
    · funext k
      ring
    · ring
  have htail : HasSum (fun k : ℕ => t (k+d))
      (deriv f z-∑ n ∈ range d, t n) := (hasSum_nat_add_iff' d).mpr hs
  have hbound (k : ℕ) : ‖t (k+d)‖ ≤ M*r^d*((k : ℝ)+((d : ℝ) + 1))*r^k := by
    calc
      _ ≤ ((k+d+1 : ℕ) : ℝ)*‖coefficient f c (k+d+1)‖*r^(k+d) := ht (k+d)
      _ ≤ ((k+d+1 : ℕ) : ℝ)*M*r^(k+d) := by gcongr; exact hM _
      _ = _ := by rw [pow_add]; push_cast; ring
  have htailnorm := htail.norm_le_of_bounded hg hbound
  have hhead : ‖∑ n ∈ range d, t n‖ ≤
      ∑ n ∈ range d, ((n+1 : ℕ) : ℝ)*‖coefficient f c (n+1)‖*r^n :=
    (norm_sum_le _ _).trans (sum_le_sum (fun n _ => ht n))
  calc
    _ = ‖(∑ n ∈ range d, t n)+(deriv f z-∑ n ∈ range d, t n)‖ := by congr 1; ring
    _ ≤ ‖∑ n ∈ range d, t n‖+‖deriv f z-∑ n ∈ range d, t n‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hhead htailnorm

def derivativeBudget {d : ℕ} (a : Jet d) (r : ℚ) : ℚ :=
  (∑ n ∈ range d, (n + 1 : ℚ) *
    (size (CertifiedTaylorModel.get a (n + 1)).centre + (CertifiedTaylorModel.get a (n + 1)).radius) * r ^ n) +
      1000 * r ^ d * (r / (1 - r) ^ 2 + (d + 1 : ℚ) / (1 - r))

theorem norm_lower {v : QComplex} {L : ℚ} (hL : 0 ≤ L)
    (hsq : L ^ 2 ≤ v.1 ^ 2 + v.2 ^ 2) : (L : ℝ) ≤ ‖value v‖ := by
  have h : (L : ℝ) ^ 2 ≤ (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2 := by exact_mod_cast hsq
  have hv : ‖value v‖ ^ 2 = (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2 := by
    norm_num [Complex.sq_norm, Complex.normSq_apply, value]
    ring
  have hLp : (0 : ℝ) ≤ L := by exact_mod_cast hL
  nlinarith [norm_nonneg (value v)]

theorem xi_derivative_le {d : ℕ} {a : Jet d} {c z : ℂ} {r K : ℚ}
    (hc : c ∈ XiAdaptiveTiles.quarter (141 / 10)) (ha : Sound a xiCompleted c)
    (hr0 : 0 < r) (hr1 : r < 1) (hK : derivativeBudget a r ≤ K)
    (hz : ‖z - c‖ ≤ (r : ℝ)) : ‖deriv xiCompleted z‖ ≤ (K : ℝ) := by
  have hC (n : ℕ) : ‖coefficient xiCompleted c n‖ ≤ 1000 := by
    apply XiLocalCauchy.taylor_coefficient_bound hc.1 hc.2.1
    simpa only [abs_of_nonneg hc.2.2.1] using! hc.2.2.2
  have hp := derivative_bound differentiable_xiCompleted d
    (by exact_mod_cast hr0) (by exact_mod_cast hr1) hz hC
  have hhead :
      (∑ n ∈ range d, ((n + 1 : ℕ) : ℝ) * ‖coefficient xiCompleted c (n + 1)‖ * (r : ℝ) ^ n) ≤
      ((∑ n ∈ range d, (n + 1 : ℚ) *
        (size (CertifiedTaylorModel.get a (n + 1)).centre + (CertifiedTaylorModel.get a (n + 1)).radius) * r ^ n : ℚ) : ℝ) := by
    push_cast
    apply Finset.sum_le_sum
    intro n hn
    have hlt : n + 1 < d + 1 := by simp only [mem_range] at hn; omega
    have hb : ‖coefficient xiCompleted c (n + 1)‖ ≤
        ((size (CertifiedTaylorModel.get a (n + 1)).centre + (CertifiedTaylorModel.get a (n + 1)).radius : ℚ) : ℝ) := by
      simpa only [CertifiedTaylorModel.get, dif_pos hlt] using! norm_le_of_contains (ha ⟨n + 1, hlt⟩)
    push_cast at hb
    gcongr
  have hbudget :
      ((∑ n ∈ range d, (n + 1 : ℚ) *
        (size (CertifiedTaylorModel.get a (n + 1)).centre + (CertifiedTaylorModel.get a (n + 1)).radius) * r ^ n : ℚ) : ℝ) +
      1000 * (r : ℝ) ^ d * ((r : ℝ) / (1 - r) ^ 2 + ((d : ℝ) + 1) / (1 - r)) =
      (derivativeBudget a r : ℝ) := by
    push_cast [derivativeBudget]
    ring
  calc
    _ ≤ _ := hp
    _ ≤ _ := add_le_add hhead le_rfl
    _ = (derivativeBudget a r : ℝ) := hbudget
    _ ≤ (K : ℝ) := by exact_mod_cast hK

/-- The numerical module supplies only rational checks and the sound jet.
All derivative-series and nonvanishing reasoning is reused at every centre. -/
theorem certified_tile_nonzero {d : ℕ} {a : Jet d} {c z : ℂ} {r K L : ℚ}
    (hc : c ∈ XiAdaptiveTiles.quarter (141 / 10)) (ha : Sound a xiCompleted c)
    (hr0 : 0 < r) (hr1 : r < 1) (hK0 : 0 ≤ K) (hK : derivativeBudget a r ≤ K)
    (hL0 : 0 ≤ L) (hL : L ^ 2 ≤ (a ⟨0, by omega⟩).centre.1 ^ 2 +
      (a ⟨0, by omega⟩).centre.2 ^ 2)
    (hmargin : (a ⟨0, by omega⟩).radius + K * r < L)
    (hz : ‖z - c‖ ≤ (r : ℝ)) : xiCompleted z ≠ 0 := by
  have hreal : ((a ⟨0, by omega⟩).radius : ℝ) + (K : ℝ) * r < ‖value (a ⟨0, by omega⟩).centre‖ :=
    (show ((a ⟨0, by omega⟩).radius : ℝ) + (K : ℝ) * r < (L : ℝ) by exact_mod_cast hmargin).trans_le
      (norm_lower hL0 hL)
  have hcover := XiAdaptiveTiles.adaptive_cover_nonzero (n := 1)
    (f := xiCompleted) (S := Metric.closedBall c (r : ℝ))
    (fun _ => Metric.closedBall c (r : ℝ)) (fun _ => c)
    (fun _ => value (a ⟨0, by omega⟩).centre) (fun _ => (r : ℝ))
    (fun _ => (K : ℝ)) (fun _ => ((a ⟨0, by omega⟩).radius : ℝ))
    (fun _ => convex_closedBall c (r : ℝ)) (fun _ => by simp [hr0.le])
    (fun _ w _ => differentiable_xiCompleted w) (fun _ => by change (0 : ℝ) ≤ (K : ℝ); exact_mod_cast hK0)
    (fun _ _ hw => xi_derivative_le hc ha hr0 hr1 hK (mem_closedBall_iff_norm.mp hw))
    (fun _ => centre_contains ha)
    (fun w hw => ⟨⟨0, by omega⟩, hw, mem_closedBall_iff_norm.mp hw⟩)
    (fun _ => hreal)
  exact hcover z (mem_closedBall_iff_norm.mpr hz)

end Reinmann.RectangleTileRules


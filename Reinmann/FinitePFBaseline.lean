/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.XiToeplitzPositivity

@[expose] public section

/-!
# Finite Pólya-frequency interfaces

These are unconditional algebraic transport theorems, NOT a formalization of
Katkova's analytic theorem. No assertion `FinitePF XiMomentCoeff 43` is assumed
or declared as an axiom. See `research/FINITE_PF_BASELINE_2026_09_13.md` for the
external theorem boundary and the printed PF43/PF44 indexing discrepancy.
-/
noncomputable section
namespace Reinmann

/-- Lower triangular Toeplitz convention, including zero extension. -/
def sequenceToeplitz (a : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if j ≤ i then a (i - j) else 0

/-- All arbitrary minors through rank `r`; this is nonnegativity, not strictness. -/
def FinitePF (a : ℕ → ℝ) (r : ℕ) : Prop :=
  ∀ k ≤ r, ∀ (rows cols : Fin k → ℕ), StrictMono rows → StrictMono cols →
    0 ≤ (Matrix.of fun i j => sequenceToeplitz a (rows i) (cols j)).det

theorem finitePF_mono {a : ℕ → ℝ} {r s : ℕ}
    (h : FinitePF a r) (hs : s ≤ r) : FinitePF a s := by
  intro k hk rows cols hr hc
  exact h k (hk.trans hs) rows cols hr hc

/-- Changing the positive overall normalization preserves finite PF. -/
theorem finitePF_nonneg_scale {a : ℕ → ℝ} {r : ℕ} (h : FinitePF a r)
    {c : ℝ} (hc : 0 ≤ c) : FinitePF (fun n => c * a n) r := by
  intro k hk rows cols hr hcol
  have hm : (Matrix.of fun i j : Fin k =>
      sequenceToeplitz (fun n => c * a n) (rows i) (cols j)) =
      c • (Matrix.of fun i j : Fin k => sequenceToeplitz a (rows i) (cols j)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, sequenceToeplitz]
    split_ifs <;> simp
  rw [hm, Matrix.det_smul]
  exact mul_nonneg (pow_nonneg hc _) (h k hk rows cols hr hcol)

/-- Katkova uses the upper triangular transpose. Selecting columns as rows and
rows as columns preserves determinants and proves equivalence of conventions. -/
theorem finitePF_iff_upper {a : ℕ → ℝ} {r : ℕ} :
    FinitePF a r ↔
    ∀ k ≤ r, ∀ (rows cols : Fin k → ℕ), StrictMono rows → StrictMono cols →
      0 ≤ (Matrix.of fun i j => sequenceToeplitz a (cols j) (rows i)).det := by
  constructor <;> intro h k hk rows cols hr hc
  · have hh := h k hk cols rows hc hr
    rw [← Matrix.det_transpose] at hh
    exact hh
  · have hh := h k hk cols rows hc hr
    rw [← Matrix.det_transpose] at hh
    exact hh

/-- Exact transport into the repository's signed ordinary Xi coefficients. -/
theorem finitePF_xi_iff (r : ℕ) :
    FinitePF XiMomentCoeff r ↔
    ∀ k ≤ r, ∀ (rows cols : Fin k → ℕ), StrictMono rows → StrictMono cols →
      0 ≤ (Matrix.of fun i j => XiToeplitzEntry (rows i) (cols j)).det := Iff.rfl

theorem xi_contig_nonneg_of_finitePF {r : ℕ}
    (h : FinitePF XiMomentCoeff r) {k : ℕ} (hk : k ≤ r) (m : ℕ) :
    0 ≤ XiToeplitzContigMinor k m :=
  h k hk (fun i => m + i.val) (fun j => j.val)
    (strictMono_addLeft_val m k) (strictMono_fin_val k)

/-- Full PF is precisely finite PF at every rank; no uniform-rank conclusion
can be obtained merely by choosing one finite baseline. -/
theorem xi_fullPF_iff_all_finite :
    XiToeplitzTotalPositive ↔ ∀ r, FinitePF XiMomentCoeff r := by
  constructor
  · intro h r k _ rows cols hr hc
    exact h k rows cols hr hc
  · intro h k rows cols hr hc
    exact h k k le_rfl rows cols hr hc

/-- If the external rank-43 result is later formalized, all low-rank arbitrary
minors follow immediately. The premise is deliberately explicit. -/
theorem xi_finitePF_four_of_43 (h : FinitePF XiMomentCoeff 43) :
    FinitePF XiMomentCoeff 4 := finitePF_mono h (by norm_num)

end Reinmann

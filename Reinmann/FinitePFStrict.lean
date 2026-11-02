/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.FinitePFBaseline
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

/-!
# Strict finite-order positivity from positive linear factors

An elementary lower bidiagonal factor preserves ordered-minor nonnegativity.
The all-predecessor term supplies a quantitative strictly positive witness.
Analytic zero extraction and Schoenberg's sector theorem are not axioms here.
-/
noncomputable section
namespace Reinmann.FinitePFStrict
open Finset Matrix

def OrderedNonneg (A : ℤ → ℕ → ℝ) (r : ℕ) : Prop :=
  ∀ k ≤ r, ∀ (rows : Fin k → ℤ) (cols : Fin k → ℕ),
    StrictMono rows → StrictMono cols → 0 ≤ (Matrix.of fun i j => A (rows i) (cols j)).det

def rowStep (t : ℝ) (A : ℤ → ℕ → ℝ) (i : ℤ) (j : ℕ) : ℝ :=
  A i j + t * A (i - 1) j

def chosenRow {k : ℕ} (rows : Fin k → ℤ) (e : Fin k → Bool) (i : Fin k) : ℤ :=
  rows i - if e i then 1 else 0

def choiceWeight {k : ℕ} (t : ℝ) (e : Fin k → Bool) : ℝ :=
  ∏ i, if e i then t else 1

/-- Multilinearity expands a bidiagonal step into its ordered-row choices. -/
theorem rowStep_det_expansion {k : ℕ} (t : ℝ) (A : ℤ → ℕ → ℝ)
    (rows : Fin k → ℤ) (cols : Fin k → ℕ) :
    (Matrix.of fun i j => rowStep t A (rows i) (cols j)).det =
      ∑ e : Fin k → Bool, choiceWeight t e *
        (Matrix.of fun i j => A (chosenRow rows e i) (cols j)).det := by
  classical
  let v (i : Fin k) (b : Bool) : Fin k → ℝ :=
    if b then t • (fun j => A (rows i - 1) (cols j)) else (fun j => A (rows i) (cols j))
  have hv : (fun i j => rowStep t A (rows i) (cols j)) = fun i => ∑ b, v i b := by
    ext i j
    simp [v, rowStep, add_comm]
  change Matrix.detRowAlternating _ = _
  rw [hv]
  change Matrix.detRowAlternating.toMultilinearMap (fun i => ∑ b, v i b) = _
  rw [Matrix.detRowAlternating.toMultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro e _
  have he : (fun i => v i (e i)) =
      fun i => (if e i then t else 1) • (fun j => A (chosenRow rows e i) (cols j)) := by
    funext i
    cases h : e i <;> simp [v, chosenRow, h]
  rw [he, Matrix.detRowAlternating.toMultilinearMap.map_smul_univ]
  rfl

theorem chosenRow_monotone {k : ℕ} {rows : Fin k → ℤ} (hr : StrictMono rows)
    (e : Fin k → Bool) : Monotone (chosenRow rows e) := by
  intro i j hij
  by_cases heq : i = j
  · subst j; exact le_rfl
  have hlt := hr (lt_of_le_of_ne hij heq)
  unfold chosenRow
  cases e i <;> cases e j <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- A weakly ordered row choice is either strictly ordered or has zero determinant. -/
theorem chosen_det_nonneg {r k : ℕ} {A : ℤ → ℕ → ℝ} (hA : OrderedNonneg A r)
    (hk : k ≤ r) {rows : Fin k → ℤ} (hr : StrictMono rows)
    {cols : Fin k → ℕ} (hc : StrictMono cols) (e : Fin k → Bool) :
    0 ≤ (Matrix.of fun i j => A (chosenRow rows e i) (cols j)).det := by
  classical
  by_cases hs : StrictMono (chosenRow rows e)
  · exact hA k hk _ _ hs hc
  · have hn : ¬ Function.Injective (chosenRow rows e) := by
      intro hi
      exact hs ((chosenRow_monotone hr e).strictMono_of_injective hi)
    obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp hn
    have hz : (Matrix.of fun i j => A (chosenRow rows e i) (cols j)).det = 0 :=
      Matrix.det_zero_of_row_eq hne (by
        funext l
        exact congrArg (fun z => A z (cols l)) heq)
    rw [hz]

/-- Positive linear factors preserve all ordered minors through the given rank. -/
theorem orderedNonneg_rowStep {r : ℕ} {A : ℤ → ℕ → ℝ}
    (hA : OrderedNonneg A r) {t : ℝ} (ht : 0 ≤ t) : OrderedNonneg (rowStep t A) r := by
  intro k hk rows cols hr hc
  rw [rowStep_det_expansion]
  apply Finset.sum_nonneg
  intro e _
  apply mul_nonneg
  · exact Finset.prod_nonneg fun i _ => by cases e i <;> simp [ht]
  · exact chosen_det_nonneg hA hk hr hc e

/-- Keeping the all-predecessor term gives the strictness witness at every rank. -/
theorem rowStep_det_lower {r k : ℕ} {A : ℤ → ℕ → ℝ} (hA : OrderedNonneg A r)
    (hk : k ≤ r) {rows : Fin k → ℤ} (hr : StrictMono rows)
    {cols : Fin k → ℕ} (hc : StrictMono cols) {t : ℝ} (ht : 0 ≤ t) :
    t ^ k * (Matrix.of fun i j => A (rows i - 1) (cols j)).det ≤
      (Matrix.of fun i j => rowStep t A (rows i) (cols j)).det := by
  classical
  rw [rowStep_det_expansion]
  have hl := Finset.single_le_sum (s := Finset.univ)
    (f := fun e : Fin k → Bool => choiceWeight t e *
      (Matrix.of fun i j => A (chosenRow rows e i) (cols j)).det)
    (fun e _ => mul_nonneg
      (Finset.prod_nonneg fun i _ => by cases e i <;> simp [ht])
      (chosen_det_nonneg hA hk hr hc e)) (Finset.mem_univ (fun _ => true))
  simpa [choiceWeight, chosenRow] using! hl

def contig (A : ℤ → ℕ → ℝ) (k : ℕ) (m : ℤ) : ℝ :=
  (Matrix.of fun i j : Fin k => A (m + i.val) j.val).det

theorem int_contig_rows_strict (k : ℕ) (m : ℤ) :
    StrictMono (fun i : Fin k => m + (i.val : ℤ)) := by
  intro i j hij
  simpa only [add_comm] using! add_lt_add_left (Int.ofNat_lt.mpr hij) m

theorem contig_rowStep_lower {r k : ℕ} {A : ℤ → ℕ → ℝ} (hA : OrderedNonneg A r)
    (hk : k ≤ r) (m : ℤ) {t : ℝ} (ht : 0 ≤ t) :
    t ^ k * contig A k m ≤ contig (rowStep t A) k (m + 1) := by
  have h := rowStep_det_lower hA hk (int_contig_rows_strict k (m + 1))
    (strictMono_fin_val k) ht
  simpa [contig, add_sub_assoc] using! h

def rowSteps (t : ℕ → ℝ) : ℕ → (ℤ → ℕ → ℝ) → (ℤ → ℕ → ℝ)
  | 0, A => A
  | n + 1, A => rowStep (t n) (rowSteps t n A)

theorem orderedNonneg_rowSteps {r : ℕ} {A : ℤ → ℕ → ℝ} (hA : OrderedNonneg A r)
    {t : ℕ → ℝ} (ht : ∀ i, 0 ≤ t i) (m : ℕ) : OrderedNonneg (rowSteps t m A) r := by
  induction m with
  | zero => exact hA
  | succ m ih => exact orderedNonneg_rowStep ih (ht m)

/-- A finite product of positive linear factors transports the diagonal margin
to any prescribed shift. No cutoff or asymptotic limit occurs in this bound. -/
theorem rowSteps_contig_lower {r k : ℕ} {A : ℤ → ℕ → ℝ} (hA : OrderedNonneg A r)
    (hk : k ≤ r) {t : ℕ → ℝ} (ht : ∀ i, 0 ≤ t i) (m : ℕ) :
    (∏ i ∈ Finset.range m, t i) ^ k * contig A k 0 ≤
      contig (rowSteps t m A) k m := by
  induction m with
  | zero => simp [rowSteps]
  | succ m ih =>
    have hs := contig_rowStep_lower (orderedNonneg_rowSteps hA ht m) hk (m : ℤ) (ht m)
    have hm := mul_le_mul_of_nonneg_left ih (pow_nonneg (ht m) k)
    rw [Finset.prod_range_succ, mul_pow]
    calc
      _ = (t m) ^ k * ((∏ i ∈ Finset.range m, t i) ^ k * contig A k 0) := by ring
      _ ≤ (t m) ^ k * contig (rowSteps t m A) k m := hm
      _ ≤ _ := by simpa [rowSteps, Nat.cast_add, Nat.cast_one] using! hs

def intToeplitz (a : ℕ → ℝ) (i : ℤ) (j : ℕ) : ℝ :=
  if 0 ≤ i then sequenceToeplitz a i.toNat j else 0

/-- Coefficients of `(1 + t*z) * sum a_n*z^n`, with ordinary normalization. -/
def linearFactor (t : ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  a n + if n = 0 then 0 else t * a (n - 1)

theorem intToeplitz_linearFactor (t : ℝ) (a : ℕ → ℝ) :
    intToeplitz (linearFactor t a) = rowStep t (intToeplitz a) := by
  funext i j
  simp only [intToeplitz, sequenceToeplitz, linearFactor, rowStep]
  split_ifs <;> try omega
  all_goals try simp_all only [add_zero, mul_zero]
  all_goals have he : i.toNat - j - 1 = (i - 1).toNat - j := by omega
  all_goals rw [he]

def linearFactors (t : ℕ → ℝ) : ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | 0, a => a
  | n + 1, a => linearFactor (t n) (linearFactors t n a)

theorem intToeplitz_linearFactors (t : ℕ → ℝ) (a : ℕ → ℝ) (m : ℕ) :
    intToeplitz (linearFactors t m a) = rowSteps t m (intToeplitz a) := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [linearFactors, rowSteps, intToeplitz_linearFactor, ih]

/-- Integer row extension adds only zero rows; it adds no analytic premise. -/
theorem orderedNonneg_intToeplitz {a : ℕ → ℝ} {r : ℕ} (ha : FinitePF a r) :
    OrderedNonneg (intToeplitz a) r := by
  intro k hk rows cols hr hc
  classical
  by_cases hn : ∃ i, rows i < 0
  · obtain ⟨i, hi⟩ := hn
    have hz : (Matrix.of fun i j => intToeplitz a (rows i) (cols j)).det = 0 :=
      Matrix.det_eq_zero_of_row_eq_zero i (fun j => by simp [intToeplitz, not_le.mpr hi])
    rw [hz]
  · have hp : ∀ i, 0 ≤ rows i := fun i => le_of_not_gt (fun h => hn ⟨i, h⟩)
    have hs : StrictMono (fun i => (rows i).toNat) := by
      intro i j hij
      change (rows i).toNat < (rows j).toNat
      have h := hr hij
      have hi := hp i
      have hj := hp j
      omega
    simpa [intToeplitz, hp] using! ha k hk _ cols hs hc

/-- The initial contiguous Toeplitz block is lower triangular. -/
theorem intToeplitz_contig_zero (a : ℕ → ℝ) (k : ℕ) :
    contig (intToeplitz a) k 0 = a 0 ^ k := by
  classical
  unfold contig
  have hl : (Matrix.of fun i j : Fin k => intToeplitz a (0 + i.val) j.val).BlockTriangular
      OrderDual.toDual := by
    intro i j hij
    have h : i.val < j.val := hij
    change intToeplitz a (0 + (i.val : ℤ)) j.val = 0
    have hn : ¬ j.val ≤ i.val := Nat.not_le.mpr h
    simp only [intToeplitz, zero_add, Int.natCast_nonneg, ↓reduceIte,
      Int.toNat_natCast, sequenceToeplitz, hn]
  rw [Matrix.det_of_lowerTriangular _ hl]
  simp [intToeplitz, sequenceToeplitz]

/-- Quantitative positivity at an arbitrary shift after extracting that many
positive factors from a finite-PF quotient. -/
theorem extracted_factors_contig_positive {a : ℕ → ℝ} {r k : ℕ}
    (ha : FinitePF a r) (hk : k ≤ r) (ha₀ : 0 < a 0)
    {t : ℕ → ℝ} (ht : ∀ i, 0 < t i) (m : ℕ) :
    0 < contig (rowSteps t m (intToeplitz a)) k m := by
  have hl := rowSteps_contig_lower (orderedNonneg_intToeplitz ha) hk
    (fun i => (ht i).le) m
  rw [intToeplitz_contig_zero] at hl
  have hp : 0 < (∏ i ∈ Finset.range m, t i) ^ k * a 0 ^ k :=
    mul_pos (pow_pos (Finset.prod_pos fun i _ => ht i) _) (pow_pos ha₀ _)
  exact hp.trans_le hl

/-- The same strictness theorem in the repository's natural-number Toeplitz
convention, with the factorization premise fully visible. -/
theorem linearFactors_contig_positive {a : ℕ → ℝ} {r k : ℕ}
    (ha : FinitePF a r) (hk : k ≤ r) (ha₀ : 0 < a 0)
    {t : ℕ → ℝ} (ht : ∀ i, 0 < t i) (m : ℕ) :
    0 < (Matrix.of fun i j : Fin k =>
      sequenceToeplitz (linearFactors t m a) (m + i.val) j.val).det := by
  have h := extracted_factors_contig_positive ha hk ha₀ ht m
  rw [← intToeplitz_linearFactors] at h
  have h0 : ∀ i : Fin k, (0 : ℤ) ≤ (m : ℤ) + ((i.val : ℕ) : ℤ) := fun i => by positivity
  have h1 : ∀ i : Fin k, ((m : ℤ) + ((i.val : ℕ) : ℤ)).toNat = m + i.val := fun i => by omega
  simpa [contig, intToeplitz, Nat.cast_add, h0, h1] using! h

/-- Quantitative natural-index version of the extracted-factor witness. -/
theorem linearFactors_contig_lower {a : ℕ → ℝ} {r k : ℕ}
    (ha : FinitePF a r) (hk : k ≤ r) {t : ℕ → ℝ}
    (ht : ∀ i, 0 ≤ t i) (m : ℕ) :
    (∏ i ∈ Finset.range m, t i) ^ k * a 0 ^ k ≤
      (Matrix.of fun i j : Fin k =>
        sequenceToeplitz (linearFactors t m a) (m + i.val) j.val).det := by
  have h := rowSteps_contig_lower (orderedNonneg_intToeplitz ha) hk ht m
  rw [intToeplitz_contig_zero, ← intToeplitz_linearFactors] at h
  have h0 : ∀ i : Fin k, (0 : ℤ) ≤ (m : ℤ) + ((i.val : ℕ) : ℤ) := fun i => by positivity
  have h1 : ∀ i : Fin k, ((m : ℤ) + ((i.val : ℕ) : ℤ)).toNat = m + i.val := fun i => by omega
  simpa [contig, intToeplitz, Nat.cast_add, h0, h1] using! h

/-- Xi-facing target: analytic extraction is explicit, and the all-shift
determinant transport itself is a kernel-checked algebraic theorem. -/
theorem xi_contig_positive_of_factor_extraction {r : ℕ}
    (hextract : ∀ m : ℕ, ∃ (g : ℕ → ℝ) (t : ℕ → ℝ),
      FinitePF g r ∧ 0 < g 0 ∧ (∀ i, 0 < t i) ∧
        XiMomentCoeff = linearFactors t m g) :
    ∀ k ≤ r, ∀ m, 0 < XiToeplitzContigMinor k m := by
  intro k hk m
  obtain ⟨g, t, hg, hg₀, ht, heq⟩ := hextract m
  have h := linearFactors_contig_positive hg hk hg₀ ht m
  change 0 < (Matrix.of fun i j : Fin k =>
    sequenceToeplitz XiMomentCoeff (m + i.val) j.val).det
  rw [heq]
  exact h

end Reinmann.FinitePFStrict

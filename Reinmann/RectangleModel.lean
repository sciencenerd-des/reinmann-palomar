/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.RectangleTaylor
public import Reinmann.RectangleLogInputs
public import Reinmann.RectangleFiniteFormulas
public import Reinmann.UniformXiRemainders
public import Reinmann.CertifiedHorner
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! Shared analytic and finite-expression proofs; independent of tile centres. -/
noncomputable section
namespace Reinmann.RectangleModel
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor Filter
open scoped Topology
set_option maxRecDepth 20000
def F_variable (s:ℂ) : ℂ := s
theorem A_variable {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_variable c := by
  exact analyticAt_id

def F_halfVariable (s:ℂ) : ℂ := value ((1/2), 0) * F_variable s
theorem A_halfVariable {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_halfVariable c := by
  exact analyticAt_const.mul (A_variable hc)

def F_q0 (s:ℂ) : ℂ := value (1, 0)
theorem A_q0 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_q0 c := by
  exact analyticAt_const

def F_base (s:ℂ) : ℂ := F_q0 s + F_halfVariable s
theorem A_base {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_base c := by
  exact (A_q0 hc).add (A_halfVariable hc)

def F_q1 (s:ℂ) : ℂ := value (12, 0)
theorem A_q1 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_q1 c := by
  exact analyticAt_const

def F_shift (s:ℂ) : ℂ := F_base s + F_q1 s
theorem A_shift {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_shift c := by
  exact (A_base hc).add (A_q1 hc)

theorem P_shiftInv {c:ℂ} (hc:-2<c.re) : 0 < (F_shift c).re := by
  norm_num [F_shift, F_base, F_q0, F_halfVariable, F_variable, F_q1, value, Complex.mul_re] at *
  linarith

theorem N_shiftInv {c:ℂ} (hc:-2<c.re) : F_shift c ≠ 0 :=
  Complex.ne_zero_of_re_pos (P_shiftInv hc)

def F_shiftInv (s:ℂ) : ℂ := (F_shift s)⁻¹
theorem A_shiftInv {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_shiftInv c := by
  exact (A_shift hc).inv (N_shiftInv hc)

theorem L_shiftLog {c:ℂ} (hc:-2<c.re) : F_shift c ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (P_shiftInv hc))

def F_shiftLog (s:ℂ) : ℂ := Complex.log (F_shift s)
theorem A_shiftLog {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_shiftLog c := by
  exact (A_shift hc).clog (L_shiftLog hc)

def F_q2 (s:ℂ) : ℂ := value ((-1/2), 0)
theorem A_q2 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_q2 c := by
  exact analyticAt_const

def F_shiftMinusHalf (s:ℂ) : ℂ := F_shift s + F_q2 s
theorem A_shiftMinusHalf {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_shiftMinusHalf c := by
  exact (A_shift hc).add (A_q2 hc)

def F_mainLead (s:ℂ) : ℂ := F_shiftMinusHalf s * F_shiftLog s
theorem A_mainLead {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_mainLead c := by
  exact (A_shiftMinusHalf hc).mul (A_shiftLog hc)

def F_negativeShift (s:ℂ) : ℂ := value (-1, 0) * F_shift s
theorem A_negativeShift {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negativeShift c := by
  exact analyticAt_const.mul (A_shift hc)

def F_mainMinusShift (s:ℂ) : ℂ := F_mainLead s + F_negativeShift s
theorem A_mainMinusShift {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_mainMinusShift c := by
  exact (A_mainLead hc).add (A_negativeShift hc)

def F_log2 (s:ℂ) : ℂ := (Real.log (2:ℝ):ℂ)
theorem A_log2 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log2 c := by
  exact analyticAt_const

def F_logpi (s:ℂ) : ℂ := (Real.log (Real.pi:ℝ):ℂ)
theorem A_logpi {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_logpi c := by
  exact analyticAt_const

def F_logTwoPi (s:ℂ) : ℂ := F_log2 s + F_logpi s
theorem A_logTwoPi {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_logTwoPi c := by
  exact (A_log2 hc).add (A_logpi hc)

def F_halfLogTwoPi (s:ℂ) : ℂ := value ((1/2), 0) * F_logTwoPi s
theorem A_halfLogTwoPi {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_halfLogTwoPi c := by
  exact analyticAt_const.mul (A_logTwoPi hc)

def F_mainConstant (s:ℂ) : ℂ := F_mainMinusShift s + F_halfLogTwoPi s
theorem A_mainConstant {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_mainConstant c := by
  exact (A_mainMinusShift hc).add (A_halfLogTwoPi hc)

def F_invPower2 (s:ℂ) : ℂ := F_shiftInv s * F_shiftInv s
theorem A_invPower2 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_invPower2 c := by
  exact (A_shiftInv hc).mul (A_shiftInv hc)

def F_invPower3 (s:ℂ) : ℂ := F_invPower2 s * F_shiftInv s
theorem A_invPower3 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_invPower3 c := by
  exact (A_invPower2 hc).mul (A_shiftInv hc)

def F_invPower4 (s:ℂ) : ℂ := F_invPower3 s * F_shiftInv s
theorem A_invPower4 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_invPower4 c := by
  exact (A_invPower3 hc).mul (A_shiftInv hc)

def F_invPower5 (s:ℂ) : ℂ := F_invPower4 s * F_shiftInv s
theorem A_invPower5 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_invPower5 c := by
  exact (A_invPower4 hc).mul (A_shiftInv hc)

def F_invPower6 (s:ℂ) : ℂ := F_invPower5 s * F_shiftInv s
theorem A_invPower6 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_invPower6 c := by
  exact (A_invPower5 hc).mul (A_shiftInv hc)

def F_invPower7 (s:ℂ) : ℂ := F_invPower6 s * F_shiftInv s
theorem A_invPower7 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_invPower7 c := by
  exact (A_invPower6 hc).mul (A_shiftInv hc)

def F_invPower8 (s:ℂ) : ℂ := F_invPower7 s * F_shiftInv s
theorem A_invPower8 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_invPower8 c := by
  exact (A_invPower7 hc).mul (A_shiftInv hc)

def F_invPower9 (s:ℂ) : ℂ := F_invPower8 s * F_shiftInv s
theorem A_invPower9 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_invPower9 c := by
  exact (A_invPower8 hc).mul (A_shiftInv hc)

def F_invPower10 (s:ℂ) : ℂ := F_invPower9 s * F_shiftInv s
theorem A_invPower10 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_invPower10 c := by
  exact (A_invPower9 hc).mul (A_shiftInv hc)

def F_invPower11 (s:ℂ) : ℂ := F_invPower10 s * F_shiftInv s
theorem A_invPower11 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_invPower11 c := by
  exact (A_invPower10 hc).mul (A_shiftInv hc)

def F_mainTerm1 (s:ℂ) : ℂ := value ((1/12), 0) * F_shiftInv s
theorem A_mainTerm1 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_mainTerm1 c := by
  exact analyticAt_const.mul (A_shiftInv hc)

def F_mainCorr1 (s:ℂ) : ℂ := F_mainConstant s + F_mainTerm1 s
theorem A_mainCorr1 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_mainCorr1 c := by
  exact (A_mainConstant hc).add (A_mainTerm1 hc)

def F_mainTerm2 (s:ℂ) : ℂ := value ((-1/360), 0) * F_invPower3 s
theorem A_mainTerm2 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_mainTerm2 c := by
  exact analyticAt_const.mul (A_invPower3 hc)

def F_mainCorr2 (s:ℂ) : ℂ := F_mainCorr1 s + F_mainTerm2 s
theorem A_mainCorr2 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_mainCorr2 c := by
  exact (A_mainCorr1 hc).add (A_mainTerm2 hc)

def F_mainTerm3 (s:ℂ) : ℂ := value ((1/1260), 0) * F_invPower5 s
theorem A_mainTerm3 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_mainTerm3 c := by
  exact analyticAt_const.mul (A_invPower5 hc)

def F_mainCorr3 (s:ℂ) : ℂ := F_mainCorr2 s + F_mainTerm3 s
theorem A_mainCorr3 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_mainCorr3 c := by
  exact (A_mainCorr2 hc).add (A_mainTerm3 hc)

def F_mainTerm4 (s:ℂ) : ℂ := value ((-1/1680), 0) * F_invPower7 s
theorem A_mainTerm4 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_mainTerm4 c := by
  exact analyticAt_const.mul (A_invPower7 hc)

def F_mainCorr4 (s:ℂ) : ℂ := F_mainCorr3 s + F_mainTerm4 s
theorem A_mainCorr4 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_mainCorr4 c := by
  exact (A_mainCorr3 hc).add (A_mainTerm4 hc)

def F_mainTerm5 (s:ℂ) : ℂ := value ((1/1188), 0) * F_invPower9 s
theorem A_mainTerm5 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_mainTerm5 c := by
  exact analyticAt_const.mul (A_invPower9 hc)

def F_mainCorr5 (s:ℂ) : ℂ := F_mainCorr4 s + F_mainTerm5 s
theorem A_mainCorr5 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_mainCorr5 c := by
  exact (A_mainCorr4 hc).add (A_mainTerm5 hc)

def F_mainTerm6 (s:ℂ) : ℂ := value ((-691/360360), 0) * F_invPower11 s
theorem A_mainTerm6 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_mainTerm6 c := by
  exact analyticAt_const.mul (A_invPower11 hc)

def F_mainCorr6 (s:ℂ) : ℂ := F_mainCorr5 s + F_mainTerm6 s
theorem A_mainCorr6 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_mainCorr6 c := by
  exact (A_mainCorr5 hc).add (A_mainTerm6 hc)

def F_gammaExp (s:ℂ) : ℂ := Complex.exp (F_mainCorr6 s)
theorem A_gammaExp {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaExp c := by
  exact (A_mainCorr6 hc).cexp'

theorem P_gammaInverse0 {c:ℂ} (hc:-2<c.re) : 0 < (F_base c).re := by
  norm_num [F_base, F_q0, F_halfVariable, F_variable, value, Complex.mul_re] at *
  linarith

theorem N_gammaInverse0 {c:ℂ} (hc:-2<c.re) : F_base c ≠ 0 :=
  Complex.ne_zero_of_re_pos (P_gammaInverse0 hc)

def F_gammaInverse0 (s:ℂ) : ℂ := (F_base s)⁻¹
theorem A_gammaInverse0 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaInverse0 c := by
  exact (A_base hc).inv (N_gammaInverse0 hc)

def F_gammaFactor1 (s:ℂ) : ℂ := F_base s + F_q0 s
theorem A_gammaFactor1 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaFactor1 c := by
  exact (A_base hc).add (A_q0 hc)

theorem P_gammaInverse1 {c:ℂ} (hc:-2<c.re) : 0 < (F_gammaFactor1 c).re := by
  norm_num [F_gammaFactor1, F_base, F_q0, F_halfVariable, F_variable, value, Complex.mul_re] at *
  linarith

theorem N_gammaInverse1 {c:ℂ} (hc:-2<c.re) : F_gammaFactor1 c ≠ 0 :=
  Complex.ne_zero_of_re_pos (P_gammaInverse1 hc)

def F_gammaInverse1 (s:ℂ) : ℂ := (F_gammaFactor1 s)⁻¹
theorem A_gammaInverse1 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaInverse1 c := by
  exact (A_gammaFactor1 hc).inv (N_gammaInverse1 hc)

def F_gammaProduct1 (s:ℂ) : ℂ := F_gammaInverse0 s * F_gammaInverse1 s
theorem A_gammaProduct1 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaProduct1 c := by
  exact (A_gammaInverse0 hc).mul (A_gammaInverse1 hc)

def F_q3 (s:ℂ) : ℂ := value (2, 0)
theorem A_q3 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_q3 c := by
  exact analyticAt_const

def F_gammaFactor2 (s:ℂ) : ℂ := F_base s + F_q3 s
theorem A_gammaFactor2 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaFactor2 c := by
  exact (A_base hc).add (A_q3 hc)

theorem P_gammaInverse2 {c:ℂ} (hc:-2<c.re) : 0 < (F_gammaFactor2 c).re := by
  norm_num [F_gammaFactor2, F_base, F_q0, F_halfVariable, F_variable, F_q3, value, Complex.mul_re] at *
  linarith

theorem N_gammaInverse2 {c:ℂ} (hc:-2<c.re) : F_gammaFactor2 c ≠ 0 :=
  Complex.ne_zero_of_re_pos (P_gammaInverse2 hc)

def F_gammaInverse2 (s:ℂ) : ℂ := (F_gammaFactor2 s)⁻¹
theorem A_gammaInverse2 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaInverse2 c := by
  exact (A_gammaFactor2 hc).inv (N_gammaInverse2 hc)

def F_gammaProduct2 (s:ℂ) : ℂ := F_gammaProduct1 s * F_gammaInverse2 s
theorem A_gammaProduct2 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaProduct2 c := by
  exact (A_gammaProduct1 hc).mul (A_gammaInverse2 hc)

def F_q4 (s:ℂ) : ℂ := value (3, 0)
theorem A_q4 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_q4 c := by
  exact analyticAt_const

def F_gammaFactor3 (s:ℂ) : ℂ := F_base s + F_q4 s
theorem A_gammaFactor3 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaFactor3 c := by
  exact (A_base hc).add (A_q4 hc)

theorem P_gammaInverse3 {c:ℂ} (hc:-2<c.re) : 0 < (F_gammaFactor3 c).re := by
  norm_num [F_gammaFactor3, F_base, F_q0, F_halfVariable, F_variable, F_q4, value, Complex.mul_re] at *
  linarith

theorem N_gammaInverse3 {c:ℂ} (hc:-2<c.re) : F_gammaFactor3 c ≠ 0 :=
  Complex.ne_zero_of_re_pos (P_gammaInverse3 hc)

def F_gammaInverse3 (s:ℂ) : ℂ := (F_gammaFactor3 s)⁻¹
theorem A_gammaInverse3 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaInverse3 c := by
  exact (A_gammaFactor3 hc).inv (N_gammaInverse3 hc)

def F_gammaProduct3 (s:ℂ) : ℂ := F_gammaProduct2 s * F_gammaInverse3 s
theorem A_gammaProduct3 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaProduct3 c := by
  exact (A_gammaProduct2 hc).mul (A_gammaInverse3 hc)

def F_q5 (s:ℂ) : ℂ := value (4, 0)
theorem A_q5 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_q5 c := by
  exact analyticAt_const

def F_gammaFactor4 (s:ℂ) : ℂ := F_base s + F_q5 s
theorem A_gammaFactor4 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaFactor4 c := by
  exact (A_base hc).add (A_q5 hc)

theorem P_gammaInverse4 {c:ℂ} (hc:-2<c.re) : 0 < (F_gammaFactor4 c).re := by
  norm_num [F_gammaFactor4, F_base, F_q0, F_halfVariable, F_variable, F_q5, value, Complex.mul_re] at *
  linarith

theorem N_gammaInverse4 {c:ℂ} (hc:-2<c.re) : F_gammaFactor4 c ≠ 0 :=
  Complex.ne_zero_of_re_pos (P_gammaInverse4 hc)

def F_gammaInverse4 (s:ℂ) : ℂ := (F_gammaFactor4 s)⁻¹
theorem A_gammaInverse4 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaInverse4 c := by
  exact (A_gammaFactor4 hc).inv (N_gammaInverse4 hc)

def F_gammaProduct4 (s:ℂ) : ℂ := F_gammaProduct3 s * F_gammaInverse4 s
theorem A_gammaProduct4 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaProduct4 c := by
  exact (A_gammaProduct3 hc).mul (A_gammaInverse4 hc)

def F_q6 (s:ℂ) : ℂ := value (5, 0)
theorem A_q6 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_q6 c := by
  exact analyticAt_const

def F_gammaFactor5 (s:ℂ) : ℂ := F_base s + F_q6 s
theorem A_gammaFactor5 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaFactor5 c := by
  exact (A_base hc).add (A_q6 hc)

theorem P_gammaInverse5 {c:ℂ} (hc:-2<c.re) : 0 < (F_gammaFactor5 c).re := by
  norm_num [F_gammaFactor5, F_base, F_q0, F_halfVariable, F_variable, F_q6, value, Complex.mul_re] at *
  linarith

theorem N_gammaInverse5 {c:ℂ} (hc:-2<c.re) : F_gammaFactor5 c ≠ 0 :=
  Complex.ne_zero_of_re_pos (P_gammaInverse5 hc)

def F_gammaInverse5 (s:ℂ) : ℂ := (F_gammaFactor5 s)⁻¹
theorem A_gammaInverse5 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaInverse5 c := by
  exact (A_gammaFactor5 hc).inv (N_gammaInverse5 hc)

def F_gammaProduct5 (s:ℂ) : ℂ := F_gammaProduct4 s * F_gammaInverse5 s
theorem A_gammaProduct5 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaProduct5 c := by
  exact (A_gammaProduct4 hc).mul (A_gammaInverse5 hc)

def F_q7 (s:ℂ) : ℂ := value (6, 0)
theorem A_q7 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_q7 c := by
  exact analyticAt_const

def F_gammaFactor6 (s:ℂ) : ℂ := F_base s + F_q7 s
theorem A_gammaFactor6 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaFactor6 c := by
  exact (A_base hc).add (A_q7 hc)

theorem P_gammaInverse6 {c:ℂ} (hc:-2<c.re) : 0 < (F_gammaFactor6 c).re := by
  norm_num [F_gammaFactor6, F_base, F_q0, F_halfVariable, F_variable, F_q7, value, Complex.mul_re] at *
  linarith

theorem N_gammaInverse6 {c:ℂ} (hc:-2<c.re) : F_gammaFactor6 c ≠ 0 :=
  Complex.ne_zero_of_re_pos (P_gammaInverse6 hc)

def F_gammaInverse6 (s:ℂ) : ℂ := (F_gammaFactor6 s)⁻¹
theorem A_gammaInverse6 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaInverse6 c := by
  exact (A_gammaFactor6 hc).inv (N_gammaInverse6 hc)

def F_gammaProduct6 (s:ℂ) : ℂ := F_gammaProduct5 s * F_gammaInverse6 s
theorem A_gammaProduct6 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaProduct6 c := by
  exact (A_gammaProduct5 hc).mul (A_gammaInverse6 hc)

def F_q8 (s:ℂ) : ℂ := value (7, 0)
theorem A_q8 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_q8 c := by
  exact analyticAt_const

def F_gammaFactor7 (s:ℂ) : ℂ := F_base s + F_q8 s
theorem A_gammaFactor7 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaFactor7 c := by
  exact (A_base hc).add (A_q8 hc)

theorem P_gammaInverse7 {c:ℂ} (hc:-2<c.re) : 0 < (F_gammaFactor7 c).re := by
  norm_num [F_gammaFactor7, F_base, F_q0, F_halfVariable, F_variable, F_q8, value, Complex.mul_re] at *
  linarith

theorem N_gammaInverse7 {c:ℂ} (hc:-2<c.re) : F_gammaFactor7 c ≠ 0 :=
  Complex.ne_zero_of_re_pos (P_gammaInverse7 hc)

def F_gammaInverse7 (s:ℂ) : ℂ := (F_gammaFactor7 s)⁻¹
theorem A_gammaInverse7 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaInverse7 c := by
  exact (A_gammaFactor7 hc).inv (N_gammaInverse7 hc)

def F_gammaProduct7 (s:ℂ) : ℂ := F_gammaProduct6 s * F_gammaInverse7 s
theorem A_gammaProduct7 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaProduct7 c := by
  exact (A_gammaProduct6 hc).mul (A_gammaInverse7 hc)

def F_q9 (s:ℂ) : ℂ := value (8, 0)
theorem A_q9 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_q9 c := by
  exact analyticAt_const

def F_gammaFactor8 (s:ℂ) : ℂ := F_base s + F_q9 s
theorem A_gammaFactor8 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaFactor8 c := by
  exact (A_base hc).add (A_q9 hc)

theorem P_gammaInverse8 {c:ℂ} (hc:-2<c.re) : 0 < (F_gammaFactor8 c).re := by
  norm_num [F_gammaFactor8, F_base, F_q0, F_halfVariable, F_variable, F_q9, value, Complex.mul_re] at *
  linarith

theorem N_gammaInverse8 {c:ℂ} (hc:-2<c.re) : F_gammaFactor8 c ≠ 0 :=
  Complex.ne_zero_of_re_pos (P_gammaInverse8 hc)

def F_gammaInverse8 (s:ℂ) : ℂ := (F_gammaFactor8 s)⁻¹
theorem A_gammaInverse8 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaInverse8 c := by
  exact (A_gammaFactor8 hc).inv (N_gammaInverse8 hc)

def F_gammaProduct8 (s:ℂ) : ℂ := F_gammaProduct7 s * F_gammaInverse8 s
theorem A_gammaProduct8 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaProduct8 c := by
  exact (A_gammaProduct7 hc).mul (A_gammaInverse8 hc)

def F_q10 (s:ℂ) : ℂ := value (9, 0)
theorem A_q10 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_q10 c := by
  exact analyticAt_const

def F_gammaFactor9 (s:ℂ) : ℂ := F_base s + F_q10 s
theorem A_gammaFactor9 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaFactor9 c := by
  exact (A_base hc).add (A_q10 hc)

theorem P_gammaInverse9 {c:ℂ} (hc:-2<c.re) : 0 < (F_gammaFactor9 c).re := by
  norm_num [F_gammaFactor9, F_base, F_q0, F_halfVariable, F_variable, F_q10, value, Complex.mul_re] at *
  linarith

theorem N_gammaInverse9 {c:ℂ} (hc:-2<c.re) : F_gammaFactor9 c ≠ 0 :=
  Complex.ne_zero_of_re_pos (P_gammaInverse9 hc)

def F_gammaInverse9 (s:ℂ) : ℂ := (F_gammaFactor9 s)⁻¹
theorem A_gammaInverse9 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaInverse9 c := by
  exact (A_gammaFactor9 hc).inv (N_gammaInverse9 hc)

def F_gammaProduct9 (s:ℂ) : ℂ := F_gammaProduct8 s * F_gammaInverse9 s
theorem A_gammaProduct9 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaProduct9 c := by
  exact (A_gammaProduct8 hc).mul (A_gammaInverse9 hc)

def F_q11 (s:ℂ) : ℂ := value (10, 0)
theorem A_q11 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_q11 c := by
  exact analyticAt_const

def F_gammaFactor10 (s:ℂ) : ℂ := F_base s + F_q11 s
theorem A_gammaFactor10 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaFactor10 c := by
  exact (A_base hc).add (A_q11 hc)

theorem P_gammaInverse10 {c:ℂ} (hc:-2<c.re) : 0 < (F_gammaFactor10 c).re := by
  norm_num [F_gammaFactor10, F_base, F_q0, F_halfVariable, F_variable, F_q11, value, Complex.mul_re] at *
  linarith

theorem N_gammaInverse10 {c:ℂ} (hc:-2<c.re) : F_gammaFactor10 c ≠ 0 :=
  Complex.ne_zero_of_re_pos (P_gammaInverse10 hc)

def F_gammaInverse10 (s:ℂ) : ℂ := (F_gammaFactor10 s)⁻¹
theorem A_gammaInverse10 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaInverse10 c := by
  exact (A_gammaFactor10 hc).inv (N_gammaInverse10 hc)

def F_gammaProduct10 (s:ℂ) : ℂ := F_gammaProduct9 s * F_gammaInverse10 s
theorem A_gammaProduct10 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaProduct10 c := by
  exact (A_gammaProduct9 hc).mul (A_gammaInverse10 hc)

def F_q12 (s:ℂ) : ℂ := value (11, 0)
theorem A_q12 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_q12 c := by
  exact analyticAt_const

def F_gammaFactor11 (s:ℂ) : ℂ := F_base s + F_q12 s
theorem A_gammaFactor11 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaFactor11 c := by
  exact (A_base hc).add (A_q12 hc)

theorem P_gammaInverse11 {c:ℂ} (hc:-2<c.re) : 0 < (F_gammaFactor11 c).re := by
  norm_num [F_gammaFactor11, F_base, F_q0, F_halfVariable, F_variable, F_q12, value, Complex.mul_re] at *
  linarith

theorem N_gammaInverse11 {c:ℂ} (hc:-2<c.re) : F_gammaFactor11 c ≠ 0 :=
  Complex.ne_zero_of_re_pos (P_gammaInverse11 hc)

def F_gammaInverse11 (s:ℂ) : ℂ := (F_gammaFactor11 s)⁻¹
theorem A_gammaInverse11 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaInverse11 c := by
  exact (A_gammaFactor11 hc).inv (N_gammaInverse11 hc)

def F_gammaProduct11 (s:ℂ) : ℂ := F_gammaProduct10 s * F_gammaInverse11 s
theorem A_gammaProduct11 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaProduct11 c := by
  exact (A_gammaProduct10 hc).mul (A_gammaInverse11 hc)

def F_gammaFinite (s:ℂ) : ℂ := F_gammaExp s * F_gammaProduct11 s
theorem A_gammaFinite {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaFinite c := by
  exact (A_gammaExp hc).mul (A_gammaProduct11 hc)

def F_gammaActual (s:ℂ) : ℂ := RegularizedEulerMaclaurin.gammaFactor s
theorem A_gammaActual {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_gammaActual c := by
  apply DifferentiableOn.analyticAt (s := {z : ℂ | -2<z.re})
    (fun z hz => (RegularizedEulerMaclaurin.gammaFactor_differentiableAt hz).differentiableWithinAt)
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hc)

def F_negLog2 (s:ℂ) : ℂ := value (-1, 0) * F_log2 s
theorem A_negLog2 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog2 c := by
  exact analyticAt_const.mul (A_log2 hc)

def F_arg2 (s:ℂ) : ℂ := F_negLog2 s * F_variable s
theorem A_arg2 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg2 c := by
  exact (A_negLog2 hc).mul (A_variable hc)

def F_term2 (s:ℂ) : ℂ := Complex.exp (F_arg2 s)
theorem A_term2 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term2 c := by
  exact (A_arg2 hc).cexp'

def F_log3 (s:ℂ) : ℂ := (Real.log (3:ℝ):ℂ)
theorem A_log3 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log3 c := by
  exact analyticAt_const

def F_negLog3 (s:ℂ) : ℂ := value (-1, 0) * F_log3 s
theorem A_negLog3 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog3 c := by
  exact analyticAt_const.mul (A_log3 hc)

def F_arg3 (s:ℂ) : ℂ := F_negLog3 s * F_variable s
theorem A_arg3 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg3 c := by
  exact (A_negLog3 hc).mul (A_variable hc)

def F_term3 (s:ℂ) : ℂ := Complex.exp (F_arg3 s)
theorem A_term3 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term3 c := by
  exact (A_arg3 hc).cexp'

def F_log4 (s:ℂ) : ℂ := (Real.log (4:ℝ):ℂ)
theorem A_log4 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log4 c := by
  exact analyticAt_const

def F_negLog4 (s:ℂ) : ℂ := value (-1, 0) * F_log4 s
theorem A_negLog4 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog4 c := by
  exact analyticAt_const.mul (A_log4 hc)

def F_arg4 (s:ℂ) : ℂ := F_negLog4 s * F_variable s
theorem A_arg4 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg4 c := by
  exact (A_negLog4 hc).mul (A_variable hc)

def F_term4 (s:ℂ) : ℂ := Complex.exp (F_arg4 s)
theorem A_term4 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term4 c := by
  exact (A_arg4 hc).cexp'

def F_log5 (s:ℂ) : ℂ := (Real.log (5:ℝ):ℂ)
theorem A_log5 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log5 c := by
  exact analyticAt_const

def F_negLog5 (s:ℂ) : ℂ := value (-1, 0) * F_log5 s
theorem A_negLog5 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog5 c := by
  exact analyticAt_const.mul (A_log5 hc)

def F_arg5 (s:ℂ) : ℂ := F_negLog5 s * F_variable s
theorem A_arg5 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg5 c := by
  exact (A_negLog5 hc).mul (A_variable hc)

def F_term5 (s:ℂ) : ℂ := Complex.exp (F_arg5 s)
theorem A_term5 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term5 c := by
  exact (A_arg5 hc).cexp'

def F_log6 (s:ℂ) : ℂ := (Real.log (6:ℝ):ℂ)
theorem A_log6 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log6 c := by
  exact analyticAt_const

def F_negLog6 (s:ℂ) : ℂ := value (-1, 0) * F_log6 s
theorem A_negLog6 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog6 c := by
  exact analyticAt_const.mul (A_log6 hc)

def F_arg6 (s:ℂ) : ℂ := F_negLog6 s * F_variable s
theorem A_arg6 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg6 c := by
  exact (A_negLog6 hc).mul (A_variable hc)

def F_term6 (s:ℂ) : ℂ := Complex.exp (F_arg6 s)
theorem A_term6 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term6 c := by
  exact (A_arg6 hc).cexp'

def F_log7 (s:ℂ) : ℂ := (Real.log (7:ℝ):ℂ)
theorem A_log7 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log7 c := by
  exact analyticAt_const

def F_negLog7 (s:ℂ) : ℂ := value (-1, 0) * F_log7 s
theorem A_negLog7 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog7 c := by
  exact analyticAt_const.mul (A_log7 hc)

def F_arg7 (s:ℂ) : ℂ := F_negLog7 s * F_variable s
theorem A_arg7 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg7 c := by
  exact (A_negLog7 hc).mul (A_variable hc)

def F_term7 (s:ℂ) : ℂ := Complex.exp (F_arg7 s)
theorem A_term7 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term7 c := by
  exact (A_arg7 hc).cexp'

def F_log8 (s:ℂ) : ℂ := (Real.log (8:ℝ):ℂ)
theorem A_log8 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log8 c := by
  exact analyticAt_const

def F_negLog8 (s:ℂ) : ℂ := value (-1, 0) * F_log8 s
theorem A_negLog8 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog8 c := by
  exact analyticAt_const.mul (A_log8 hc)

def F_arg8 (s:ℂ) : ℂ := F_negLog8 s * F_variable s
theorem A_arg8 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg8 c := by
  exact (A_negLog8 hc).mul (A_variable hc)

def F_term8 (s:ℂ) : ℂ := Complex.exp (F_arg8 s)
theorem A_term8 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term8 c := by
  exact (A_arg8 hc).cexp'

def F_log9 (s:ℂ) : ℂ := (Real.log (9:ℝ):ℂ)
theorem A_log9 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log9 c := by
  exact analyticAt_const

def F_negLog9 (s:ℂ) : ℂ := value (-1, 0) * F_log9 s
theorem A_negLog9 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog9 c := by
  exact analyticAt_const.mul (A_log9 hc)

def F_arg9 (s:ℂ) : ℂ := F_negLog9 s * F_variable s
theorem A_arg9 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg9 c := by
  exact (A_negLog9 hc).mul (A_variable hc)

def F_term9 (s:ℂ) : ℂ := Complex.exp (F_arg9 s)
theorem A_term9 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term9 c := by
  exact (A_arg9 hc).cexp'

def F_log10 (s:ℂ) : ℂ := (Real.log (10:ℝ):ℂ)
theorem A_log10 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log10 c := by
  exact analyticAt_const

def F_negLog10 (s:ℂ) : ℂ := value (-1, 0) * F_log10 s
theorem A_negLog10 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog10 c := by
  exact analyticAt_const.mul (A_log10 hc)

def F_arg10 (s:ℂ) : ℂ := F_negLog10 s * F_variable s
theorem A_arg10 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg10 c := by
  exact (A_negLog10 hc).mul (A_variable hc)

def F_term10 (s:ℂ) : ℂ := Complex.exp (F_arg10 s)
theorem A_term10 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term10 c := by
  exact (A_arg10 hc).cexp'

def F_log11 (s:ℂ) : ℂ := (Real.log (11:ℝ):ℂ)
theorem A_log11 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log11 c := by
  exact analyticAt_const

def F_negLog11 (s:ℂ) : ℂ := value (-1, 0) * F_log11 s
theorem A_negLog11 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog11 c := by
  exact analyticAt_const.mul (A_log11 hc)

def F_arg11 (s:ℂ) : ℂ := F_negLog11 s * F_variable s
theorem A_arg11 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg11 c := by
  exact (A_negLog11 hc).mul (A_variable hc)

def F_term11 (s:ℂ) : ℂ := Complex.exp (F_arg11 s)
theorem A_term11 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term11 c := by
  exact (A_arg11 hc).cexp'

def F_log12 (s:ℂ) : ℂ := (Real.log (12:ℝ):ℂ)
theorem A_log12 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log12 c := by
  exact analyticAt_const

def F_negLog12 (s:ℂ) : ℂ := value (-1, 0) * F_log12 s
theorem A_negLog12 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog12 c := by
  exact analyticAt_const.mul (A_log12 hc)

def F_arg12 (s:ℂ) : ℂ := F_negLog12 s * F_variable s
theorem A_arg12 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg12 c := by
  exact (A_negLog12 hc).mul (A_variable hc)

def F_term12 (s:ℂ) : ℂ := Complex.exp (F_arg12 s)
theorem A_term12 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term12 c := by
  exact (A_arg12 hc).cexp'

def F_log13 (s:ℂ) : ℂ := (Real.log (13:ℝ):ℂ)
theorem A_log13 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log13 c := by
  exact analyticAt_const

def F_negLog13 (s:ℂ) : ℂ := value (-1, 0) * F_log13 s
theorem A_negLog13 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog13 c := by
  exact analyticAt_const.mul (A_log13 hc)

def F_arg13 (s:ℂ) : ℂ := F_negLog13 s * F_variable s
theorem A_arg13 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg13 c := by
  exact (A_negLog13 hc).mul (A_variable hc)

def F_term13 (s:ℂ) : ℂ := Complex.exp (F_arg13 s)
theorem A_term13 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term13 c := by
  exact (A_arg13 hc).cexp'

def F_log14 (s:ℂ) : ℂ := (Real.log (14:ℝ):ℂ)
theorem A_log14 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log14 c := by
  exact analyticAt_const

def F_negLog14 (s:ℂ) : ℂ := value (-1, 0) * F_log14 s
theorem A_negLog14 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog14 c := by
  exact analyticAt_const.mul (A_log14 hc)

def F_arg14 (s:ℂ) : ℂ := F_negLog14 s * F_variable s
theorem A_arg14 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg14 c := by
  exact (A_negLog14 hc).mul (A_variable hc)

def F_term14 (s:ℂ) : ℂ := Complex.exp (F_arg14 s)
theorem A_term14 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term14 c := by
  exact (A_arg14 hc).cexp'

def F_log15 (s:ℂ) : ℂ := (Real.log (15:ℝ):ℂ)
theorem A_log15 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log15 c := by
  exact analyticAt_const

def F_negLog15 (s:ℂ) : ℂ := value (-1, 0) * F_log15 s
theorem A_negLog15 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog15 c := by
  exact analyticAt_const.mul (A_log15 hc)

def F_arg15 (s:ℂ) : ℂ := F_negLog15 s * F_variable s
theorem A_arg15 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg15 c := by
  exact (A_negLog15 hc).mul (A_variable hc)

def F_term15 (s:ℂ) : ℂ := Complex.exp (F_arg15 s)
theorem A_term15 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term15 c := by
  exact (A_arg15 hc).cexp'

def F_log16 (s:ℂ) : ℂ := (Real.log (16:ℝ):ℂ)
theorem A_log16 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log16 c := by
  exact analyticAt_const

def F_negLog16 (s:ℂ) : ℂ := value (-1, 0) * F_log16 s
theorem A_negLog16 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog16 c := by
  exact analyticAt_const.mul (A_log16 hc)

def F_arg16 (s:ℂ) : ℂ := F_negLog16 s * F_variable s
theorem A_arg16 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg16 c := by
  exact (A_negLog16 hc).mul (A_variable hc)

def F_term16 (s:ℂ) : ℂ := Complex.exp (F_arg16 s)
theorem A_term16 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term16 c := by
  exact (A_arg16 hc).cexp'

def F_log17 (s:ℂ) : ℂ := (Real.log (17:ℝ):ℂ)
theorem A_log17 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log17 c := by
  exact analyticAt_const

def F_negLog17 (s:ℂ) : ℂ := value (-1, 0) * F_log17 s
theorem A_negLog17 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog17 c := by
  exact analyticAt_const.mul (A_log17 hc)

def F_arg17 (s:ℂ) : ℂ := F_negLog17 s * F_variable s
theorem A_arg17 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg17 c := by
  exact (A_negLog17 hc).mul (A_variable hc)

def F_term17 (s:ℂ) : ℂ := Complex.exp (F_arg17 s)
theorem A_term17 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term17 c := by
  exact (A_arg17 hc).cexp'

def F_log18 (s:ℂ) : ℂ := (Real.log (18:ℝ):ℂ)
theorem A_log18 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log18 c := by
  exact analyticAt_const

def F_negLog18 (s:ℂ) : ℂ := value (-1, 0) * F_log18 s
theorem A_negLog18 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog18 c := by
  exact analyticAt_const.mul (A_log18 hc)

def F_arg18 (s:ℂ) : ℂ := F_negLog18 s * F_variable s
theorem A_arg18 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg18 c := by
  exact (A_negLog18 hc).mul (A_variable hc)

def F_term18 (s:ℂ) : ℂ := Complex.exp (F_arg18 s)
theorem A_term18 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term18 c := by
  exact (A_arg18 hc).cexp'

def F_log19 (s:ℂ) : ℂ := (Real.log (19:ℝ):ℂ)
theorem A_log19 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log19 c := by
  exact analyticAt_const

def F_negLog19 (s:ℂ) : ℂ := value (-1, 0) * F_log19 s
theorem A_negLog19 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog19 c := by
  exact analyticAt_const.mul (A_log19 hc)

def F_arg19 (s:ℂ) : ℂ := F_negLog19 s * F_variable s
theorem A_arg19 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg19 c := by
  exact (A_negLog19 hc).mul (A_variable hc)

def F_term19 (s:ℂ) : ℂ := Complex.exp (F_arg19 s)
theorem A_term19 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term19 c := by
  exact (A_arg19 hc).cexp'

def F_log20 (s:ℂ) : ℂ := (Real.log (20:ℝ):ℂ)
theorem A_log20 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log20 c := by
  exact analyticAt_const

def F_negLog20 (s:ℂ) : ℂ := value (-1, 0) * F_log20 s
theorem A_negLog20 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog20 c := by
  exact analyticAt_const.mul (A_log20 hc)

def F_arg20 (s:ℂ) : ℂ := F_negLog20 s * F_variable s
theorem A_arg20 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg20 c := by
  exact (A_negLog20 hc).mul (A_variable hc)

def F_term20 (s:ℂ) : ℂ := Complex.exp (F_arg20 s)
theorem A_term20 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term20 c := by
  exact (A_arg20 hc).cexp'

def F_log21 (s:ℂ) : ℂ := (Real.log (21:ℝ):ℂ)
theorem A_log21 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log21 c := by
  exact analyticAt_const

def F_negLog21 (s:ℂ) : ℂ := value (-1, 0) * F_log21 s
theorem A_negLog21 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog21 c := by
  exact analyticAt_const.mul (A_log21 hc)

def F_arg21 (s:ℂ) : ℂ := F_negLog21 s * F_variable s
theorem A_arg21 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg21 c := by
  exact (A_negLog21 hc).mul (A_variable hc)

def F_term21 (s:ℂ) : ℂ := Complex.exp (F_arg21 s)
theorem A_term21 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term21 c := by
  exact (A_arg21 hc).cexp'

def F_log22 (s:ℂ) : ℂ := (Real.log (22:ℝ):ℂ)
theorem A_log22 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log22 c := by
  exact analyticAt_const

def F_negLog22 (s:ℂ) : ℂ := value (-1, 0) * F_log22 s
theorem A_negLog22 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog22 c := by
  exact analyticAt_const.mul (A_log22 hc)

def F_arg22 (s:ℂ) : ℂ := F_negLog22 s * F_variable s
theorem A_arg22 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg22 c := by
  exact (A_negLog22 hc).mul (A_variable hc)

def F_term22 (s:ℂ) : ℂ := Complex.exp (F_arg22 s)
theorem A_term22 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term22 c := by
  exact (A_arg22 hc).cexp'

def F_log23 (s:ℂ) : ℂ := (Real.log (23:ℝ):ℂ)
theorem A_log23 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log23 c := by
  exact analyticAt_const

def F_negLog23 (s:ℂ) : ℂ := value (-1, 0) * F_log23 s
theorem A_negLog23 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog23 c := by
  exact analyticAt_const.mul (A_log23 hc)

def F_arg23 (s:ℂ) : ℂ := F_negLog23 s * F_variable s
theorem A_arg23 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg23 c := by
  exact (A_negLog23 hc).mul (A_variable hc)

def F_term23 (s:ℂ) : ℂ := Complex.exp (F_arg23 s)
theorem A_term23 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term23 c := by
  exact (A_arg23 hc).cexp'

def F_log24 (s:ℂ) : ℂ := (Real.log (24:ℝ):ℂ)
theorem A_log24 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log24 c := by
  exact analyticAt_const

def F_negLog24 (s:ℂ) : ℂ := value (-1, 0) * F_log24 s
theorem A_negLog24 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog24 c := by
  exact analyticAt_const.mul (A_log24 hc)

def F_arg24 (s:ℂ) : ℂ := F_negLog24 s * F_variable s
theorem A_arg24 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg24 c := by
  exact (A_negLog24 hc).mul (A_variable hc)

def F_term24 (s:ℂ) : ℂ := Complex.exp (F_arg24 s)
theorem A_term24 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term24 c := by
  exact (A_arg24 hc).cexp'

def F_log25 (s:ℂ) : ℂ := (Real.log (25:ℝ):ℂ)
theorem A_log25 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log25 c := by
  exact analyticAt_const

def F_negLog25 (s:ℂ) : ℂ := value (-1, 0) * F_log25 s
theorem A_negLog25 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog25 c := by
  exact analyticAt_const.mul (A_log25 hc)

def F_arg25 (s:ℂ) : ℂ := F_negLog25 s * F_variable s
theorem A_arg25 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg25 c := by
  exact (A_negLog25 hc).mul (A_variable hc)

def F_term25 (s:ℂ) : ℂ := Complex.exp (F_arg25 s)
theorem A_term25 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term25 c := by
  exact (A_arg25 hc).cexp'

def F_log26 (s:ℂ) : ℂ := (Real.log (26:ℝ):ℂ)
theorem A_log26 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log26 c := by
  exact analyticAt_const

def F_negLog26 (s:ℂ) : ℂ := value (-1, 0) * F_log26 s
theorem A_negLog26 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog26 c := by
  exact analyticAt_const.mul (A_log26 hc)

def F_arg26 (s:ℂ) : ℂ := F_negLog26 s * F_variable s
theorem A_arg26 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg26 c := by
  exact (A_negLog26 hc).mul (A_variable hc)

def F_term26 (s:ℂ) : ℂ := Complex.exp (F_arg26 s)
theorem A_term26 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term26 c := by
  exact (A_arg26 hc).cexp'

def F_log27 (s:ℂ) : ℂ := (Real.log (27:ℝ):ℂ)
theorem A_log27 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_log27 c := by
  exact analyticAt_const

def F_negLog27 (s:ℂ) : ℂ := value (-1, 0) * F_log27 s
theorem A_negLog27 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negLog27 c := by
  exact analyticAt_const.mul (A_log27 hc)

def F_arg27 (s:ℂ) : ℂ := F_negLog27 s * F_variable s
theorem A_arg27 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_arg27 c := by
  exact (A_negLog27 hc).mul (A_variable hc)

def F_term27 (s:ℂ) : ℂ := Complex.exp (F_arg27 s)
theorem A_term27 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_term27 c := by
  exact (A_arg27 hc).cexp'

def F_initial2 (s:ℂ) : ℂ := F_q0 s + F_term2 s
theorem A_initial2 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial2 c := by
  exact (A_q0 hc).add (A_term2 hc)

def F_initial3 (s:ℂ) : ℂ := F_initial2 s + F_term3 s
theorem A_initial3 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial3 c := by
  exact (A_initial2 hc).add (A_term3 hc)

def F_initial4 (s:ℂ) : ℂ := F_initial3 s + F_term4 s
theorem A_initial4 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial4 c := by
  exact (A_initial3 hc).add (A_term4 hc)

def F_initial5 (s:ℂ) : ℂ := F_initial4 s + F_term5 s
theorem A_initial5 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial5 c := by
  exact (A_initial4 hc).add (A_term5 hc)

def F_initial6 (s:ℂ) : ℂ := F_initial5 s + F_term6 s
theorem A_initial6 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial6 c := by
  exact (A_initial5 hc).add (A_term6 hc)

def F_initial7 (s:ℂ) : ℂ := F_initial6 s + F_term7 s
theorem A_initial7 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial7 c := by
  exact (A_initial6 hc).add (A_term7 hc)

def F_initial8 (s:ℂ) : ℂ := F_initial7 s + F_term8 s
theorem A_initial8 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial8 c := by
  exact (A_initial7 hc).add (A_term8 hc)

def F_initial9 (s:ℂ) : ℂ := F_initial8 s + F_term9 s
theorem A_initial9 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial9 c := by
  exact (A_initial8 hc).add (A_term9 hc)

def F_initial10 (s:ℂ) : ℂ := F_initial9 s + F_term10 s
theorem A_initial10 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial10 c := by
  exact (A_initial9 hc).add (A_term10 hc)

def F_initial11 (s:ℂ) : ℂ := F_initial10 s + F_term11 s
theorem A_initial11 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial11 c := by
  exact (A_initial10 hc).add (A_term11 hc)

def F_initial12 (s:ℂ) : ℂ := F_initial11 s + F_term12 s
theorem A_initial12 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial12 c := by
  exact (A_initial11 hc).add (A_term12 hc)

def F_initial13 (s:ℂ) : ℂ := F_initial12 s + F_term13 s
theorem A_initial13 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial13 c := by
  exact (A_initial12 hc).add (A_term13 hc)

def F_initial14 (s:ℂ) : ℂ := F_initial13 s + F_term14 s
theorem A_initial14 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial14 c := by
  exact (A_initial13 hc).add (A_term14 hc)

def F_initial15 (s:ℂ) : ℂ := F_initial14 s + F_term15 s
theorem A_initial15 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial15 c := by
  exact (A_initial14 hc).add (A_term15 hc)

def F_initial16 (s:ℂ) : ℂ := F_initial15 s + F_term16 s
theorem A_initial16 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial16 c := by
  exact (A_initial15 hc).add (A_term16 hc)

def F_initial17 (s:ℂ) : ℂ := F_initial16 s + F_term17 s
theorem A_initial17 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial17 c := by
  exact (A_initial16 hc).add (A_term17 hc)

def F_initial18 (s:ℂ) : ℂ := F_initial17 s + F_term18 s
theorem A_initial18 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial18 c := by
  exact (A_initial17 hc).add (A_term18 hc)

def F_initial19 (s:ℂ) : ℂ := F_initial18 s + F_term19 s
theorem A_initial19 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial19 c := by
  exact (A_initial18 hc).add (A_term19 hc)

def F_initial20 (s:ℂ) : ℂ := F_initial19 s + F_term20 s
theorem A_initial20 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial20 c := by
  exact (A_initial19 hc).add (A_term20 hc)

def F_initial21 (s:ℂ) : ℂ := F_initial20 s + F_term21 s
theorem A_initial21 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial21 c := by
  exact (A_initial20 hc).add (A_term21 hc)

def F_initial22 (s:ℂ) : ℂ := F_initial21 s + F_term22 s
theorem A_initial22 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial22 c := by
  exact (A_initial21 hc).add (A_term22 hc)

def F_initial23 (s:ℂ) : ℂ := F_initial22 s + F_term23 s
theorem A_initial23 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial23 c := by
  exact (A_initial22 hc).add (A_term23 hc)

def F_initial24 (s:ℂ) : ℂ := F_initial23 s + F_term24 s
theorem A_initial24 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial24 c := by
  exact (A_initial23 hc).add (A_term24 hc)

def F_initial25 (s:ℂ) : ℂ := F_initial24 s + F_term25 s
theorem A_initial25 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial25 c := by
  exact (A_initial24 hc).add (A_term25 hc)

def F_initial26 (s:ℂ) : ℂ := F_initial25 s + F_term26 s
theorem A_initial26 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initial26 c := by
  exact (A_initial25 hc).add (A_term26 hc)

def F_endpointHalf (s:ℂ) : ℂ := value ((1/2), 0) * F_term27 s
theorem A_endpointHalf {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_endpointHalf c := by
  exact analyticAt_const.mul (A_term27 hc)

def F_initialHalf (s:ℂ) : ℂ := F_initial26 s + F_endpointHalf s
theorem A_initialHalf {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_initialHalf c := by
  exact (A_initial26 hc).add (A_endpointHalf hc)

def F_risingFactor1 (s:ℂ) : ℂ := F_variable s + F_q0 s
theorem A_risingFactor1 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_risingFactor1 c := by
  exact (A_variable hc).add (A_q0 hc)

def F_rising2 (s:ℂ) : ℂ := F_variable s * F_risingFactor1 s
theorem A_rising2 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_rising2 c := by
  exact (A_variable hc).mul (A_risingFactor1 hc)

def F_risingFactor2 (s:ℂ) : ℂ := F_variable s + F_q3 s
theorem A_risingFactor2 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_risingFactor2 c := by
  exact (A_variable hc).add (A_q3 hc)

def F_rising3 (s:ℂ) : ℂ := F_rising2 s * F_risingFactor2 s
theorem A_rising3 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_rising3 c := by
  exact (A_rising2 hc).mul (A_risingFactor2 hc)

def F_risingFactor3 (s:ℂ) : ℂ := F_variable s + F_q4 s
theorem A_risingFactor3 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_risingFactor3 c := by
  exact (A_variable hc).add (A_q4 hc)

def F_rising4 (s:ℂ) : ℂ := F_rising3 s * F_risingFactor3 s
theorem A_rising4 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_rising4 c := by
  exact (A_rising3 hc).mul (A_risingFactor3 hc)

def F_risingFactor4 (s:ℂ) : ℂ := F_variable s + F_q5 s
theorem A_risingFactor4 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_risingFactor4 c := by
  exact (A_variable hc).add (A_q5 hc)

def F_rising5 (s:ℂ) : ℂ := F_rising4 s * F_risingFactor4 s
theorem A_rising5 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_rising5 c := by
  exact (A_rising4 hc).mul (A_risingFactor4 hc)

def F_risingFactor5 (s:ℂ) : ℂ := F_variable s + F_q6 s
theorem A_risingFactor5 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_risingFactor5 c := by
  exact (A_variable hc).add (A_q6 hc)

def F_rising6 (s:ℂ) : ℂ := F_rising5 s * F_risingFactor5 s
theorem A_rising6 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_rising6 c := by
  exact (A_rising5 hc).mul (A_risingFactor5 hc)

def F_risingFactor6 (s:ℂ) : ℂ := F_variable s + F_q7 s
theorem A_risingFactor6 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_risingFactor6 c := by
  exact (A_variable hc).add (A_q7 hc)

def F_rising7 (s:ℂ) : ℂ := F_rising6 s * F_risingFactor6 s
theorem A_rising7 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_rising7 c := by
  exact (A_rising6 hc).mul (A_risingFactor6 hc)

def F_risingFactor7 (s:ℂ) : ℂ := F_variable s + F_q8 s
theorem A_risingFactor7 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_risingFactor7 c := by
  exact (A_variable hc).add (A_q8 hc)

def F_rising8 (s:ℂ) : ℂ := F_rising7 s * F_risingFactor7 s
theorem A_rising8 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_rising8 c := by
  exact (A_rising7 hc).mul (A_risingFactor7 hc)

def F_risingFactor8 (s:ℂ) : ℂ := F_variable s + F_q9 s
theorem A_risingFactor8 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_risingFactor8 c := by
  exact (A_variable hc).add (A_q9 hc)

def F_rising9 (s:ℂ) : ℂ := F_rising8 s * F_risingFactor8 s
theorem A_rising9 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_rising9 c := by
  exact (A_rising8 hc).mul (A_risingFactor8 hc)

def F_risingFactor9 (s:ℂ) : ℂ := F_variable s + F_q10 s
theorem A_risingFactor9 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_risingFactor9 c := by
  exact (A_variable hc).add (A_q10 hc)

def F_rising10 (s:ℂ) : ℂ := F_rising9 s * F_risingFactor9 s
theorem A_rising10 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_rising10 c := by
  exact (A_rising9 hc).mul (A_risingFactor9 hc)

def F_risingFactor10 (s:ℂ) : ℂ := F_variable s + F_q11 s
theorem A_risingFactor10 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_risingFactor10 c := by
  exact (A_variable hc).add (A_q11 hc)

def F_rising11 (s:ℂ) : ℂ := F_rising10 s * F_risingFactor10 s
theorem A_rising11 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_rising11 c := by
  exact (A_rising10 hc).mul (A_risingFactor10 hc)

def F_zetaCorrProduct1 (s:ℂ) : ℂ := F_variable s * F_term27 s
theorem A_zetaCorrProduct1 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaCorrProduct1 c := by
  exact (A_variable hc).mul (A_term27 hc)

def F_zetaCorr1 (s:ℂ) : ℂ := value ((1/324), 0) * F_zetaCorrProduct1 s
theorem A_zetaCorr1 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaCorr1 c := by
  exact analyticAt_const.mul (A_zetaCorrProduct1 hc)

def F_zetaPart1 (s:ℂ) : ℂ := F_initialHalf s + F_zetaCorr1 s
theorem A_zetaPart1 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaPart1 c := by
  exact (A_initialHalf hc).add (A_zetaCorr1 hc)

def F_zetaCorrProduct2 (s:ℂ) : ℂ := F_rising3 s * F_term27 s
theorem A_zetaCorrProduct2 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaCorrProduct2 c := by
  exact (A_rising3 hc).mul (A_term27 hc)

def F_zetaCorr2 (s:ℂ) : ℂ := value ((-1/14171760), 0) * F_zetaCorrProduct2 s
theorem A_zetaCorr2 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaCorr2 c := by
  exact analyticAt_const.mul (A_zetaCorrProduct2 hc)

def F_zetaPart2 (s:ℂ) : ℂ := F_zetaPart1 s + F_zetaCorr2 s
theorem A_zetaPart2 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaPart2 c := by
  exact (A_zetaPart1 hc).add (A_zetaCorr2 hc)

def F_zetaCorrProduct3 (s:ℂ) : ℂ := F_rising5 s * F_term27 s
theorem A_zetaCorrProduct3 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaCorrProduct3 c := by
  exact (A_rising5 hc).mul (A_term27 hc)

def F_zetaCorr3 (s:ℂ) : ℂ := value ((1/433910947680), 0) * F_zetaCorrProduct3 s
theorem A_zetaCorr3 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaCorr3 c := by
  exact analyticAt_const.mul (A_zetaCorrProduct3 hc)

def F_zetaPart3 (s:ℂ) : ℂ := F_zetaPart2 s + F_zetaCorr3 s
theorem A_zetaPart3 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaPart3 c := by
  exact (A_zetaPart2 hc).add (A_zetaCorr3 hc)

def F_zetaCorrProduct4 (s:ℂ) : ℂ := F_rising7 s * F_term27 s
theorem A_zetaCorrProduct4 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaCorrProduct4 c := by
  exact (A_rising7 hc).mul (A_term27 hc)

def F_zetaCorr4 (s:ℂ) : ℂ := value ((-1/12652843234348800), 0) * F_zetaCorrProduct4 s
theorem A_zetaCorr4 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaCorr4 c := by
  exact analyticAt_const.mul (A_zetaCorrProduct4 hc)

def F_zetaPart4 (s:ℂ) : ℂ := F_zetaPart3 s + F_zetaCorr4 s
theorem A_zetaPart4 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaPart4 c := by
  exact (A_zetaPart3 hc).add (A_zetaCorr4 hc)

def F_zetaCorrProduct5 (s:ℂ) : ℂ := F_rising9 s * F_term27 s
theorem A_zetaCorrProduct5 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaCorrProduct5 c := by
  exact (A_rising9 hc).mul (A_term27 hc)

def F_zetaCorr5 (s:ℂ) : ℂ := value ((1/365267339626474897920), 0) * F_zetaCorrProduct5 s
theorem A_zetaCorr5 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaCorr5 c := by
  exact analyticAt_const.mul (A_zetaCorrProduct5 hc)

def F_zetaPart5 (s:ℂ) : ℂ := F_zetaPart4 s + F_zetaCorr5 s
theorem A_zetaPart5 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaPart5 c := by
  exact (A_zetaPart4 hc).add (A_zetaCorr5 hc)

def F_zetaCorrProduct6 (s:ℂ) : ℂ := F_rising11 s * F_term27 s
theorem A_zetaCorrProduct6 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaCorrProduct6 c := by
  exact (A_rising11 hc).mul (A_term27 hc)

def F_zetaCorr6 (s:ℂ) : ℂ := value ((-691/7269441013044215475934464000), 0) * F_zetaCorrProduct6 s
theorem A_zetaCorr6 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaCorr6 c := by
  exact analyticAt_const.mul (A_zetaCorrProduct6 hc)

def F_zetaPart6 (s:ℂ) : ℂ := F_zetaPart5 s + F_zetaCorr6 s
theorem A_zetaPart6 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaPart6 c := by
  exact (A_zetaPart5 hc).add (A_zetaCorr6 hc)

def F_q13 (s:ℂ) : ℂ := value (-1, 0)
theorem A_q13 {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_q13 c := by
  exact analyticAt_const

def F_sminusone (s:ℂ) : ℂ := F_variable s + F_q13 s
theorem A_sminusone {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_sminusone c := by
  exact (A_variable hc).add (A_q13 hc)

def F_zetaRegularPart (s:ℂ) : ℂ := F_sminusone s * F_zetaPart6 s
theorem A_zetaRegularPart {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaRegularPart c := by
  exact (A_sminusone hc).mul (A_zetaPart6 hc)

def F_zetaIntegral (s:ℂ) : ℂ := value (27, 0) * F_term27 s
theorem A_zetaIntegral {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaIntegral c := by
  exact analyticAt_const.mul (A_term27 hc)

def F_zetaFinite (s:ℂ) : ℂ := F_zetaRegularPart s + F_zetaIntegral s
theorem A_zetaFinite {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaFinite c := by
  exact (A_zetaRegularPart hc).add (A_zetaIntegral hc)

def F_zetaActual (s:ℂ) : ℂ := RegularizedEulerMaclaurin.regularZeta s
theorem A_zetaActual {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_zetaActual c := by
  exact RegularizedEulerMaclaurin.regularZeta_differentiable.analyticAt c

def F_negativeHalfLogPi (s:ℂ) : ℂ := value ((-1/2), 0) * F_logpi s
theorem A_negativeHalfLogPi {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_negativeHalfLogPi c := by
  exact analyticAt_const.mul (A_logpi hc)

def F_piArg (s:ℂ) : ℂ := F_negativeHalfLogPi s * F_variable s
theorem A_piArg {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_piArg c := by
  exact (A_negativeHalfLogPi hc).mul (A_variable hc)

def F_piPower (s:ℂ) : ℂ := Complex.exp (F_piArg s)
theorem A_piPower {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_piPower c := by
  exact (A_piArg hc).cexp'

def F_piGamma (s:ℂ) : ℂ := F_piPower s * F_gammaActual s
theorem A_piGamma {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_piGamma c := by
  exact (A_piPower hc).mul (A_gammaActual hc)

def F_xiProduct (s:ℂ) : ℂ := F_piGamma s * F_zetaActual s
theorem A_xiProduct {c:ℂ} (hc:-2<c.re) : AnalyticAt ℂ F_xiProduct c := by
  exact (A_piGamma hc).mul (A_zetaActual hc)

theorem gammaMain_identity (s:ℂ) : F_mainCorr6 s =
    StirlingGamma.mainTerm (1+s/2+12) := by
  rw [HardTileFiniteIdentities.stirlingMain_eq]
  simp only [F_mainCorr6, F_mainCorr5, F_mainCorr4, F_mainCorr3, F_mainCorr2, F_mainCorr1, F_mainConstant, F_mainMinusShift, F_mainLead, F_shiftMinusHalf, F_q2, F_shiftLog, F_shiftInv, F_negativeShift, F_halfLogTwoPi, F_logTwoPi, F_log2, F_logpi, F_mainTerm1, F_mainTerm2, F_invPower3, F_invPower2, F_mainTerm3, F_invPower5, F_invPower4, F_mainTerm4, F_invPower7, F_invPower6, F_mainTerm5, F_invPower9, F_invPower8, F_mainTerm6, F_invPower11, F_invPower10, F_shift,F_base,F_halfVariable,F_variable,F_q0,F_q1, HardTileFiniteIdentities.stirlingMain]
  norm_num [value, div_eq_mul_inv, ← inv_pow]
  ring

theorem shift_identity (s:ℂ) : F_shift s=1+s/2+12 := by
  norm_num [F_shift,F_base,F_halfVariable,F_variable,F_q0,F_q1,value]
  ring

theorem gammaFinite_identity (s:ℂ) : F_gammaFinite s = UniformXiRemainders.gammaApprox s := by
  unfold F_gammaFinite F_gammaExp
  rw [gammaMain_identity]
  unfold UniformXiRemainders.gammaApprox
  simp only [div_eq_mul_inv, ← Finset.prod_inv_distrib]
  congr 1
  norm_num [F_gammaProduct11, F_gammaProduct10, F_gammaProduct9, F_gammaProduct8, F_gammaProduct7, F_gammaProduct6, F_gammaProduct5, F_gammaProduct4, F_gammaProduct3, F_gammaProduct2, F_gammaProduct1, F_gammaInverse0, F_base, F_q0, F_halfVariable, F_variable, F_gammaInverse1, F_gammaFactor1, F_gammaInverse2, F_gammaFactor2, F_q3, F_gammaInverse3, F_gammaFactor3, F_q4, F_gammaInverse4, F_gammaFactor4, F_q5, F_gammaInverse5, F_gammaFactor5, F_q6, F_gammaInverse6, F_gammaFactor6, F_q7, F_gammaInverse7, F_gammaFactor7, F_q8, F_gammaInverse8, F_gammaFactor8, F_q9, F_gammaInverse9, F_gammaFactor9, F_q10, F_gammaInverse10, F_gammaFactor10, F_q11, F_gammaInverse11, F_gammaFactor11, F_q12, Finset.prod_range_succ, value]
  ring

theorem term_1_identity (s:ℂ) : F_q0 s=HardTileFiniteIdentities.dirichletTerm s 1 := by
  norm_num [F_q0, HardTileFiniteIdentities.dirichletTerm, value]
  skip

theorem term_2_identity (s:ℂ) : F_term2 s=HardTileFiniteIdentities.dirichletTerm s 2 := by
  norm_num [F_term2, F_arg2, F_negLog2, F_log2, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_3_identity (s:ℂ) : F_term3 s=HardTileFiniteIdentities.dirichletTerm s 3 := by
  norm_num [F_term3, F_arg3, F_negLog3, F_log3, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_4_identity (s:ℂ) : F_term4 s=HardTileFiniteIdentities.dirichletTerm s 4 := by
  norm_num [F_term4, F_arg4, F_negLog4, F_log4, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_5_identity (s:ℂ) : F_term5 s=HardTileFiniteIdentities.dirichletTerm s 5 := by
  norm_num [F_term5, F_arg5, F_negLog5, F_log5, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_6_identity (s:ℂ) : F_term6 s=HardTileFiniteIdentities.dirichletTerm s 6 := by
  norm_num [F_term6, F_arg6, F_negLog6, F_log6, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_7_identity (s:ℂ) : F_term7 s=HardTileFiniteIdentities.dirichletTerm s 7 := by
  norm_num [F_term7, F_arg7, F_negLog7, F_log7, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_8_identity (s:ℂ) : F_term8 s=HardTileFiniteIdentities.dirichletTerm s 8 := by
  norm_num [F_term8, F_arg8, F_negLog8, F_log8, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_9_identity (s:ℂ) : F_term9 s=HardTileFiniteIdentities.dirichletTerm s 9 := by
  norm_num [F_term9, F_arg9, F_negLog9, F_log9, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_10_identity (s:ℂ) : F_term10 s=HardTileFiniteIdentities.dirichletTerm s 10 := by
  norm_num [F_term10, F_arg10, F_negLog10, F_log10, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_11_identity (s:ℂ) : F_term11 s=HardTileFiniteIdentities.dirichletTerm s 11 := by
  norm_num [F_term11, F_arg11, F_negLog11, F_log11, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_12_identity (s:ℂ) : F_term12 s=HardTileFiniteIdentities.dirichletTerm s 12 := by
  norm_num [F_term12, F_arg12, F_negLog12, F_log12, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_13_identity (s:ℂ) : F_term13 s=HardTileFiniteIdentities.dirichletTerm s 13 := by
  norm_num [F_term13, F_arg13, F_negLog13, F_log13, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_14_identity (s:ℂ) : F_term14 s=HardTileFiniteIdentities.dirichletTerm s 14 := by
  norm_num [F_term14, F_arg14, F_negLog14, F_log14, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_15_identity (s:ℂ) : F_term15 s=HardTileFiniteIdentities.dirichletTerm s 15 := by
  norm_num [F_term15, F_arg15, F_negLog15, F_log15, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_16_identity (s:ℂ) : F_term16 s=HardTileFiniteIdentities.dirichletTerm s 16 := by
  norm_num [F_term16, F_arg16, F_negLog16, F_log16, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_17_identity (s:ℂ) : F_term17 s=HardTileFiniteIdentities.dirichletTerm s 17 := by
  norm_num [F_term17, F_arg17, F_negLog17, F_log17, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_18_identity (s:ℂ) : F_term18 s=HardTileFiniteIdentities.dirichletTerm s 18 := by
  norm_num [F_term18, F_arg18, F_negLog18, F_log18, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_19_identity (s:ℂ) : F_term19 s=HardTileFiniteIdentities.dirichletTerm s 19 := by
  norm_num [F_term19, F_arg19, F_negLog19, F_log19, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_20_identity (s:ℂ) : F_term20 s=HardTileFiniteIdentities.dirichletTerm s 20 := by
  norm_num [F_term20, F_arg20, F_negLog20, F_log20, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_21_identity (s:ℂ) : F_term21 s=HardTileFiniteIdentities.dirichletTerm s 21 := by
  norm_num [F_term21, F_arg21, F_negLog21, F_log21, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_22_identity (s:ℂ) : F_term22 s=HardTileFiniteIdentities.dirichletTerm s 22 := by
  norm_num [F_term22, F_arg22, F_negLog22, F_log22, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_23_identity (s:ℂ) : F_term23 s=HardTileFiniteIdentities.dirichletTerm s 23 := by
  norm_num [F_term23, F_arg23, F_negLog23, F_log23, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_24_identity (s:ℂ) : F_term24 s=HardTileFiniteIdentities.dirichletTerm s 24 := by
  norm_num [F_term24, F_arg24, F_negLog24, F_log24, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_25_identity (s:ℂ) : F_term25 s=HardTileFiniteIdentities.dirichletTerm s 25 := by
  norm_num [F_term25, F_arg25, F_negLog25, F_log25, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_26_identity (s:ℂ) : F_term26 s=HardTileFiniteIdentities.dirichletTerm s 26 := by
  norm_num [F_term26, F_arg26, F_negLog26, F_log26, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem term_27_identity (s:ℂ) : F_term27 s=HardTileFiniteIdentities.dirichletTerm s 27 := by
  norm_num [F_term27, F_arg27, F_negLog27, F_log27, F_variable, HardTileFiniteIdentities.dirichletTerm, value]
  congr 1
  ring

theorem rising_1_identity (s:ℂ) : F_variable s=HardTileFiniteIdentities.rising s 1 := by
  norm_num [F_variable, HardTileFiniteIdentities.rising, Finset.prod_range_succ, value] <;> ring

theorem rising_2_identity (s:ℂ) : F_rising2 s=HardTileFiniteIdentities.rising s 2 := by
  norm_num [F_rising2, F_variable, F_risingFactor1, F_q0, HardTileFiniteIdentities.rising, Finset.prod_range_succ, value] <;> ring

theorem rising_3_identity (s:ℂ) : F_rising3 s=HardTileFiniteIdentities.rising s 3 := by
  norm_num [F_rising3, F_rising2, F_variable, F_risingFactor1, F_q0, F_risingFactor2, F_q3, HardTileFiniteIdentities.rising, Finset.prod_range_succ, value] <;> ring

theorem rising_4_identity (s:ℂ) : F_rising4 s=HardTileFiniteIdentities.rising s 4 := by
  norm_num [F_rising4, F_rising3, F_rising2, F_variable, F_risingFactor1, F_q0, F_risingFactor2, F_q3, F_risingFactor3, F_q4, HardTileFiniteIdentities.rising, Finset.prod_range_succ, value] <;> ring

theorem rising_5_identity (s:ℂ) : F_rising5 s=HardTileFiniteIdentities.rising s 5 := by
  norm_num [F_rising5, F_rising4, F_rising3, F_rising2, F_variable, F_risingFactor1, F_q0, F_risingFactor2, F_q3, F_risingFactor3, F_q4, F_risingFactor4, F_q5, HardTileFiniteIdentities.rising, Finset.prod_range_succ, value] <;> ring

theorem rising_6_identity (s:ℂ) : F_rising6 s=HardTileFiniteIdentities.rising s 6 := by
  norm_num [F_rising6, F_rising5, F_rising4, F_rising3, F_rising2, F_variable, F_risingFactor1, F_q0, F_risingFactor2, F_q3, F_risingFactor3, F_q4, F_risingFactor4, F_q5, F_risingFactor5, F_q6, HardTileFiniteIdentities.rising, Finset.prod_range_succ, value] <;> ring

theorem rising_7_identity (s:ℂ) : F_rising7 s=HardTileFiniteIdentities.rising s 7 := by
  norm_num [F_rising7, F_rising6, F_rising5, F_rising4, F_rising3, F_rising2, F_variable, F_risingFactor1, F_q0, F_risingFactor2, F_q3, F_risingFactor3, F_q4, F_risingFactor4, F_q5, F_risingFactor5, F_q6, F_risingFactor6, F_q7, HardTileFiniteIdentities.rising, Finset.prod_range_succ, value] <;> ring

theorem rising_8_identity (s:ℂ) : F_rising8 s=HardTileFiniteIdentities.rising s 8 := by
  norm_num [F_rising8, F_rising7, F_rising6, F_rising5, F_rising4, F_rising3, F_rising2, F_variable, F_risingFactor1, F_q0, F_risingFactor2, F_q3, F_risingFactor3, F_q4, F_risingFactor4, F_q5, F_risingFactor5, F_q6, F_risingFactor6, F_q7, F_risingFactor7, F_q8, HardTileFiniteIdentities.rising, Finset.prod_range_succ, value] <;> ring

theorem rising_9_identity (s:ℂ) : F_rising9 s=HardTileFiniteIdentities.rising s 9 := by
  norm_num [F_rising9, F_rising8, F_rising7, F_rising6, F_rising5, F_rising4, F_rising3, F_rising2, F_variable, F_risingFactor1, F_q0, F_risingFactor2, F_q3, F_risingFactor3, F_q4, F_risingFactor4, F_q5, F_risingFactor5, F_q6, F_risingFactor6, F_q7, F_risingFactor7, F_q8, F_risingFactor8, F_q9, HardTileFiniteIdentities.rising, Finset.prod_range_succ, value] <;> ring

theorem rising_10_identity (s:ℂ) : F_rising10 s=HardTileFiniteIdentities.rising s 10 := by
  norm_num [F_rising10, F_rising9, F_rising8, F_rising7, F_rising6, F_rising5, F_rising4, F_rising3, F_rising2, F_variable, F_risingFactor1, F_q0, F_risingFactor2, F_q3, F_risingFactor3, F_q4, F_risingFactor4, F_q5, F_risingFactor5, F_q6, F_risingFactor6, F_q7, F_risingFactor7, F_q8, F_risingFactor8, F_q9, F_risingFactor9, F_q10, HardTileFiniteIdentities.rising, Finset.prod_range_succ, value] <;> ring

theorem rising_11_identity (s:ℂ) : F_rising11 s=HardTileFiniteIdentities.rising s 11 := by
  norm_num [F_rising11, F_rising10, F_rising9, F_rising8, F_rising7, F_rising6, F_rising5, F_rising4, F_rising3, F_rising2, F_variable, F_risingFactor1, F_q0, F_risingFactor2, F_q3, F_risingFactor3, F_q4, F_risingFactor4, F_q5, F_risingFactor5, F_q6, F_risingFactor6, F_q7, F_risingFactor7, F_q8, F_risingFactor8, F_q9, F_risingFactor9, F_q10, F_risingFactor10, F_q11, HardTileFiniteIdentities.rising, Finset.prod_range_succ, value] <;> ring

set_option maxHeartbeats 2000000 in
theorem zetaFinite_identity (s:ℂ) : F_zetaFinite s=RegularizedEulerMaclaurin.regularModel s 27 := by
  rw [← RectangleFiniteFormulas.regularExpr_eq]
  simp only [F_zetaFinite, F_zetaRegularPart, F_sminusone, F_variable, F_q13, F_zetaPart6, F_zetaPart5, F_zetaPart4, F_zetaPart3, F_zetaPart2, F_zetaPart1, F_initialHalf, F_initial26, F_initial25, F_initial24, F_initial23, F_initial22, F_initial21, F_initial20, F_initial19, F_initial18, F_initial17, F_initial16, F_initial15, F_initial14, F_initial13, F_initial12, F_initial11, F_initial10, F_initial9, F_initial8, F_initial7, F_initial6, F_initial5, F_initial4, F_initial3, F_initial2, F_endpointHalf, F_zetaCorr1, F_zetaCorrProduct1, F_zetaCorr2, F_zetaCorrProduct2, F_zetaCorr3, F_zetaCorrProduct3, F_zetaCorr4, F_zetaCorrProduct4, F_zetaCorr5, F_zetaCorrProduct5, F_zetaCorr6, F_zetaCorrProduct6, F_zetaIntegral]
  simp only [term_1_identity, term_2_identity, term_3_identity, term_4_identity, term_5_identity, term_6_identity, term_7_identity, term_8_identity, term_9_identity, term_10_identity, term_11_identity, term_12_identity, term_13_identity, term_14_identity, term_15_identity, term_16_identity, term_17_identity, term_18_identity, term_19_identity, term_20_identity, term_21_identity, term_22_identity, term_23_identity, term_24_identity, term_25_identity, term_26_identity, term_27_identity, rising_2_identity, rising_3_identity, rising_4_identity, rising_5_identity, rising_6_identity, rising_7_identity, rising_8_identity, rising_9_identity, rising_10_identity, rising_11_identity]
  norm_num [RectangleFiniteFormulas.regularExpr,RectangleFiniteFormulas.finitePart,
    Finset.sum_range_succ,HardTileFiniteIdentities.rising,value,F_variable]
  ring

theorem piPower_identity (s:ℂ) : F_piPower s=RegularizedEulerMaclaurin.piFactor s := by
  unfold F_piPower F_piArg F_negativeHalfLogPi F_logpi F_variable RegularizedEulerMaclaurin.piFactor
  norm_num [value]
  congr 1
  ring

theorem xiProduct_identity {s:ℂ} (hs:0<s.re) : F_xiProduct s=xiCompleted s := by
  rw [RegularizedEulerMaclaurin.xi_eq_regular_product hs]
  unfold F_xiProduct F_piGamma F_gammaActual F_zetaActual
  rw [piPower_identity]

 theorem gamma_sound {d:ℕ} {a:Jet d} {c:ℂ}
    (hc:c ∈ XiAdaptiveTiles.quarter (141/10)) (ha:Sound a F_gammaFinite c) :
    Sound (fun k => inflate (a k) (4/10^14) (by norm_num)) F_gammaActual c := by
  apply sound_perturb (by norm_num) (sound_congr ha (Eventually.of_forall gammaFinite_identity))
  intro k
  simpa only [coefficient,F_gammaActual,Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow] using!
    UniformXiRemainders.gamma_coefficient_error_le hc.1 (by linarith [hc.2.1]) k.val

theorem zeta_sound {d:ℕ} {a:Jet d} {c:ℂ}
    (hc:c ∈ XiAdaptiveTiles.quarter (141/10)) (ha:Sound a F_zetaFinite c) :
    Sound (fun k => inflate (a k) (6/10^8) (by norm_num)) F_zetaActual c := by
  apply sound_perturb (by norm_num) (sound_congr ha (Eventually.of_forall zetaFinite_identity))
  intro k
  simpa only [coefficient,F_zetaActual,Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow] using!
    UniformXiRemainders.zeta_coefficient_error_le hc k.val

theorem xi_sound {d:ℕ} {a:Jet d} {c:ℂ}
    (hc:c ∈ XiAdaptiveTiles.quarter (141/10)) (ha:Sound a F_xiProduct c) :
    Sound a xiCompleted c := by
  apply sound_congr ha
  have hc0 : 0<c.re := by linarith [hc.1]
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hc0] with s hs
  exact xiProduct_identity hs

theorem log_scaled16_contains {w z:QComplex} {a:Disk}
    (hscale:value w=(16:ℂ)*(1+value z)) (hz0:1+value z≠0)
    (hn:‖value z‖≤1/2) (ha:Contains a (Complex.logTaylor 48 (value z))) :
    Contains (add (mul (exact (4,0)) RectangleLogInputs.log2Disk)
      (inflate a (1/10^15) (by norm_num))) (Complex.log (value w)) := by
  have h := contains_add (contains_mul (contains_exact ((4:ℚ),0))
    RectangleLogInputs.log2_contains) (CertifiedComplexInputs.log_series_contains hn ha)
  have h16 : Real.log (16:ℝ)=4*Real.log 2 := by
    have h := Real.log_pow (2:ℝ) 4
    norm_num only at h
    exact h
  have he : value ((4:ℚ),0)*(Real.log (2:ℝ):ℂ)+Complex.log (1+value z)=
      Complex.log (value w) := by
    rw [hscale]
    change _=Complex.log (((16:ℝ):ℂ)*(1+value z))
    rw [Complex.log_ofReal_mul (by norm_num : (0:ℝ)<16) hz0,h16]
    simp [value]
  rw [he] at h
  exact h

end Reinmann.RectangleModel

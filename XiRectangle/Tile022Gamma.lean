/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile022Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨22,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (1269/128)), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_variable : Sound J_variable F_variable c := by
  have h := variable_sound 12 ((3/4), (1269/128))
  have he : value ((3/4), (1269/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (1269/256)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_halfVariable : Sound J_halfVariable F_halfVariable c := by
  apply sound_round (sound_scale (A_variable hcre) S_variable)
  intro k
  fin_cases k <;> norm_num [J_halfVariable, J_variable, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q0 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(1, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q0 : Sound J_q0 F_q0 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (1, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_base : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11/8), (1269/256)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_base : Sound J_base F_base c := by
  apply sound_round (sound_add (A_q0 hcre) (A_halfVariable hcre) S_q0 S_halfVariable)
  intro k
  fin_cases k <;> norm_num [J_base, J_q0, J_halfVariable, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(12, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q1 : Sound J_q1 F_q1 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (12, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_shift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((107/8), (1269/256)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_shift : Sound J_shift F_shift c := by
  apply sound_round (sound_add (A_base hcre) (A_q1 hcre) S_base S_q1)
  intro k
  fin_cases k <;> norm_num [J_shift, J_base, J_q1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftInv : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((876544/13334137), (-324864/13334137)), 0, by norm_num⟩
  | 1 => ⟨((-331396382720/177799209534769), (284757590016/177799209534769)), 0, by norm_num⟩
  | 2 => ⟨((1469053669/35184372088832), (-662752031/8796093022208)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((-1023473693/2251799813685248), (6721917835/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-192976777/9007199254740992), (-1867251403/18014398509481984)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((1133821297/576460752303423488), (1813505409/576460752303423488)), (5/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-1899469761/18446744073709551616), (-2930894293/36893488147419103232)), (9/36893488147419103232), by norm_num⟩
  | 7 => ⟨((5138185921/1180591620717411303424), (1601806393/1180591620717411303424)), (7/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-6028694947/37778931862957161709568), (2485705/295147905179352825856)), (21/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((3108445235/604462909807314587353088), (-167794599/75557863725914323419136)), (17/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-2746161223/19342813113834066795298816), (2623589957/19342813113834066795298816)), (25/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((1865673005/618970019642690137449562112), (-3829954295/618970019642690137449562112)), (37/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-469327959/19807040628566084398385987584), (4755569501/19807040628566084398385987584)), (27/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (1269/256)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (1269/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (1269/256)))⁻¹=value ((876544/13334137), (-324864/13334137)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((876544/13334137), (-324864/13334137))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5707456527/2147483648), (762194371/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((438272/13334137), (-162432/13334137)), 0, by norm_num⟩
  | 2 => ⟨((-82849095680/177799209534769), (71189397504/177799209534769)), 0, by norm_num⟩
  | 3 => ⟨((1958738225/281474976710656), (-3534677499/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-1023473693/18014398509481984), (6721917835/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((-1235051373/576460752303423488), (-2987602245/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((3023523459/18446744073709551616), (604501803/2305843009213693952)), (7/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-271352823/36893488147419103232), (-1674796739/295147905179352825856)), (11/590295810358705651712), by norm_num⟩
  | 8 => ⟨((5138185921/18889465931478580854784), (1601806393/18889465931478580854784)), (7/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-5358839953/604462909807314587353088), (282817991/604462909807314587353088)), (19/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((621689047/2417851639229258349412352), (-2147770867/19342813113834066795298816)), (7/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-998604081/154742504910672534362390528), (3816130847/618970019642690137449562112)), (19/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((2487564007/19807040628566084398385987584), (-5106605727/19807040628566084398385987584)), (25/9903520314283042199192993792), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (27/4096)), 0, by norm_num⟩
  | 45 => ⟨((19847617741/816127672320), (-53649/6029312)), 0, by norm_num⟩
  | 44 => ⟨((-9177698592827/383035920875520), (71079534183/7902739824640)), 0, by norm_num⟩
  | 43 => ⟨((1676772965/68719476736), (-152882071/17179869184)), (1/137438953472), by norm_num⟩
  | 42 => ⟨((-1721813281/68719476736), (1239634717/137438953472)), (1/68719476736), by norm_num⟩
  | 41 => ⟨((883270707/34359738368), (-1270262851/137438953472)), (1/68719476736), by norm_num⟩
  | 40 => ⟨((-226379653/8589934592), (1303002623/137438953472)), (1/68719476736), by norm_num⟩
  | 39 => ⟨((1857316637/68719476736), (-667972441/68719476736)), (1/68719476736), by norm_num⟩
  | 38 => ⟨((-1906175777/68719476736), (685012767/68719476736)), (1/68719476736), by norm_num⟩
  | 37 => ⟨((3915576525/137438953472), (-702945713/68719476736)), (1/68719476736), by norm_num⟩
  | 36 => ⟨((-2012291249/68719476736), (721878131/68719476736)), (1/68719476736), by norm_num⟩
  | 35 => ⟨((4139813751/137438953472), (-1483740087/137438953472)), (1/68719476736), by norm_num⟩
  | 34 => ⟨((-4261826231/137438953472), (1526000241/137438953472)), (1/68719476736), by norm_num⟩
  | 33 => ⟨((1097811427/34359738368), (-785367389/68719476736)), (1/68719476736), by norm_num⟩
  | 32 => ⟨((-4528769709/137438953472), (809085031/68719476736)), (1/68719476736), by norm_num⟩
  | 31 => ⟨((1168795859/34359738368), (-1668559337/137438953472)), (1/68719476736), by norm_num⟩
  | 30 => ⟨((-4831376933/137438953472), (215273427/17179869184)), (1/68719476736), by norm_num⟩
  | 29 => ⟨((4998363483/137438953472), (-1779376775/137438953472)), (1/68719476736), by norm_num⟩
  | 28 => ⟨((-5177301419/137438953472), (1840494251/137438953472)), (1/68719476736), by norm_num⟩
  | 27 => ⟨((671190113/17179869184), (-119122431/8589934592)), (1/68719476736), by norm_num⟩
  | 26 => ⟨((-5576557005/137438953472), (494062891/34359738368)), (1/68719476736), by norm_num⟩
  | 25 => ⟨((5800190725/137438953472), (-2051926731/137438953472)), (1/68719476736), by norm_num⟩
  | 24 => ⟨((-3021250147/68719476736), (2133627147/137438953472)), (1/68719476736), by norm_num⟩
  | 23 => ⟨((6305925849/137438953472), (-138881383/8589934592)), (1/68719476736), by norm_num⟩
  | 22 => ⟨((-3296675881/68719476736), (1159115299/68719476736)), (1/68719476736), by norm_num⟩
  | 21 => ⟨((3454106249/68719476736), (-1211525189/68719476736)), (1/68719476736), by norm_num⟩
  | 20 => ⟨((-3627315129/68719476736), (634448945/34359738368)), (1/68719476736), by norm_num⟩
  | 19 => ⟨((119337439/2147483648), (-1331973213/68719476736)), (1/34359738368), by norm_num⟩
  | 18 => ⟨((-2015802855/34359738368), (350411421/17179869184)), (1/34359738368), by norm_num⟩
  | 17 => ⟨((2134753691/34359738368), (-1479007213/68719476736)), (1/34359738368), by norm_num⟩
  | 16 => ⟨((-1134303885/17179869184), (391351179/17179869184)), (1/34359738368), by norm_num⟩
  | 15 => ⟨((302543773/4294967296), (-831259581/34359738368)), (1/34359738368), by norm_num⟩
  | 14 => ⟨((-324227437/4294967296), (1772475987/68719476736)), (1/34359738368), by norm_num⟩
  | 13 => ⟨((5588071939/68719476736), (-1898002379/68719476736)), (1/34359738368), by norm_num⟩
  | 12 => ⟨((-6055387545/68719476736), (2042656467/68719476736)), (1/34359738368), by norm_num⟩
  | 11 => ⟨((825980335/8589934592), (-552792477/17179869184)), (1/17179869184), by norm_num⟩
  | 10 => ⟨((-1817748617/17179869184), (1204987615/34359738368)), (1/17179869184), by norm_num⟩
  | 9 => ⟨((2020437447/17179869184), (-331005717/8589934592)), (1/17179869184), by norm_num⟩
  | 8 => ⟨((-4547721913/34359738368), (1469143947/34359738368)), (1/17179869184), by norm_num⟩
  | 7 => ⟨((2599741325/17179869184), (-824990703/17179869184)), (1/17179869184), by norm_num⟩
  | 6 => ⟨((-6068475097/34359738368), (470393737/8589934592)), (1/17179869184), by norm_num⟩
  | 5 => ⟨((1821154439/8589934592), (-8549989/134217728)), (1/17179869184), by norm_num⟩
  | 4 => ⟨((-4553473095/17179869184), (653994851/8589934592)), (1/17179869184), by norm_num⟩
  | 3 => ⟨((6068443127/17179869184), (-1625323837/17179869184)), (1/17179869184), by norm_num⟩
  | 2 => ⟨((-4540994863/8589934592), (67085815/536870912)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((1125299385/1073741824), (-197870763/1073741824)), (1/4294967296), by norm_num⟩
  | 0 => ⟨((-986529665/8589934592), (3048777485/8589934592)), (1/8589934592), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (1269/4096)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (1269/4096)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (1269/4096))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((5707456527/2147483648), (762194371/2147483648)), (1/2147483648), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (1269/256))) (z:=((-21/128), (1269/4096))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((5707456527/2147483648), (762194371/2147483648))) (r:=(1/2147483648)) (by norm_num) ?_ hs
  norm_num [J_shiftLog,RectangleLogInputs.log2Disk,logTable,inflate,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

set_option maxHeartbeats 5000000 in
theorem S_shiftLog : Sound J_shiftLog F_shiftLog c := by
  apply log_coefficients_sound (A_shift hcre) (L_shiftLog hcre) S_shift S_shiftInv
  · exact logValue
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftLog,J_shift,J_shiftInv,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1/2), 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q2 : Sound J_q2 F_q2 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact ((-1/2), 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_shiftMinusHalf : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((103/8), (1269/256)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_shiftMinusHalf : Sound J_shiftMinusHalf F_shiftMinusHalf c := by
  apply sound_round (sound_add (A_shift hcre) (A_q2 hcre) S_shift S_q2)
  intro k
  fin_cases k <;> norm_num [J_shiftMinusHalf, J_shift, J_q2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainLead : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1089145023/33554432), (1190790403/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((7784355783/4294967296), (788354299/4294967296)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((1502419270656/177799209534769), (-577067334048/177799209534769)), 0, by norm_num⟩
  | 3 => ⟨((-2854898051/35184372088832), (2568841401/35184372088832)), (5/35184372088832), by norm_num⟩
  | 4 => ⟨((2022705329/2251799813685248), (-3954797365/2251799813685248)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-664397533/144115188075855872), (6124434825/144115188075855872)), (5/18014398509481984), by norm_num⟩
  | 6 => ⟨((-1201308015/4611686018427387904), (-4587971465/4611686018427387904)), (7/576460752303423488), by norm_num⟩
  | 7 => ⟨((1135216669/73786976294838206464), (3182135995/147573952589676412928)), (39/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-2813095825/4722366482869645213696), (-468755635/1180591620717411303424)), (107/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((5906986361/302231454903657293676544), (676561703/151115727451828646838272)), (141/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-5530450051/9671406556917033397649408), (763197107/9671406556917033397649408)), (403/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((4615703991/309485009821345068724781056), (-314505985/38685626227668133590597632)), (141/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-821208803/2475880078570760549798248448), (955184667/2475880078570760549798248448)), (375/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-1269/256)), 0, by norm_num⟩
  | 1 => ⟨((-1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_negativeShift : Sound J_negativeShift F_negativeShift c := by
  apply sound_round (sound_scale (A_shift hcre) S_shift)
  intro k
  fin_cases k <;> norm_num [J_negativeShift, J_shift, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainMinusShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((640354495/33554432), (858129667/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((5636872135/4294967296), (788354299/4294967296)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((1502419270656/177799209534769), (-577067334048/177799209534769)), 0, by norm_num⟩
  | 3 => ⟨((-2854898051/35184372088832), (2568841401/35184372088832)), (5/35184372088832), by norm_num⟩
  | 4 => ⟨((2022705329/2251799813685248), (-3954797365/2251799813685248)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-664397533/144115188075855872), (6124434825/144115188075855872)), (5/18014398509481984), by norm_num⟩
  | 6 => ⟨((-1201308015/4611686018427387904), (-4587971465/4611686018427387904)), (7/576460752303423488), by norm_num⟩
  | 7 => ⟨((1135216669/73786976294838206464), (3182135995/147573952589676412928)), (39/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-2813095825/4722366482869645213696), (-468755635/1180591620717411303424)), (107/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((5906986361/302231454903657293676544), (676561703/151115727451828646838272)), (141/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-5530450051/9671406556917033397649408), (763197107/9671406556917033397649408)), (403/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((4615703991/309485009821345068724781056), (-314505985/38685626227668133590597632)), (141/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-821208803/2475880078570760549798248448), (955184667/2475880078570760549798248448)), (375/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainMinusShift : Sound J_mainMinusShift F_mainMinusShift c := by
  apply sound_round (sound_add (A_mainLead hcre) (A_negativeShift hcre) S_mainLead S_negativeShift)
  intro k
  fin_cases k <;> norm_num [J_mainMinusShift, J_mainLead, J_negativeShift, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_logpi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5723649429247/5000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_logpi : Sound J_logpi F_logpi c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.logpi_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_logTwoPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3946810947/2147483648), 0), (1/4294967296), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_logTwoPi : Sound J_logTwoPi F_logTwoPi c := by
  apply sound_round (sound_add (A_log2 hcre) (A_logpi hcre) S_log2 S_logpi)
  intro k
  fin_cases k <;> norm_num [J_logTwoPi, J_log2, J_logpi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_halfLogTwoPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3946810947/4294967296), 0), (1/8589934592), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_halfLogTwoPi : Sound J_halfLogTwoPi F_halfLogTwoPi c := by
  apply sound_round (sound_scale (A_logTwoPi hcre) S_logTwoPi)
  intro k
  fin_cases k <;> norm_num [J_halfLogTwoPi, J_logTwoPi, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainConstant : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1342377911/67108864), (858129667/67108864)), (3/134217728), by norm_num⟩
  | 1 => ⟨((5636872135/4294967296), (788354299/4294967296)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((1502419270656/177799209534769), (-577067334048/177799209534769)), 0, by norm_num⟩
  | 3 => ⟨((-2854898051/35184372088832), (2568841401/35184372088832)), (5/35184372088832), by norm_num⟩
  | 4 => ⟨((2022705329/2251799813685248), (-3954797365/2251799813685248)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-664397533/144115188075855872), (6124434825/144115188075855872)), (5/18014398509481984), by norm_num⟩
  | 6 => ⟨((-1201308015/4611686018427387904), (-4587971465/4611686018427387904)), (7/576460752303423488), by norm_num⟩
  | 7 => ⟨((1135216669/73786976294838206464), (3182135995/147573952589676412928)), (39/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-2813095825/4722366482869645213696), (-468755635/1180591620717411303424)), (107/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((5906986361/302231454903657293676544), (676561703/151115727451828646838272)), (141/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-5530450051/9671406556917033397649408), (763197107/9671406556917033397649408)), (403/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((4615703991/309485009821345068724781056), (-314505985/38685626227668133590597632)), (141/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-821208803/2475880078570760549798248448), (955184667/2475880078570760549798248448)), (375/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((662792765440/177799209534769), (-569515180032/177799209534769)), 0, by norm_num⟩
  | 1 => ⟨((-1469053669/8796093022208), (662752031/2199023255552)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((383802635/140737488355328), (-630179797/35184372088832)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((192976777/1125899906842624), (1867251403/2251799813685248)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((-2834553243/144115188075855872), (-2266881761/72057594037927936)), (5/144115188075855872), by norm_num⟩
  | 5 => ⟨((2849204641/2305843009213693952), (2198170719/2305843009213693952)), (5/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-4495912681/73786976294838206464), (-700790297/36893488147419103232)), (9/73786976294838206464), by norm_num⟩
  | 7 => ⟨((6028694947/2361183241434822606848), (-2485705/18446744073709551616)), (15/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-3497000889/37778931862957161709568), (1510151391/37778931862957161709568)), (13/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((429087691/151115727451828646838272), (-1639743723/604462909807314587353088)), (21/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-1282650191/19342813113834066795298816), (5266187155/38685626227668133590597632)), (1/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((351995969/618970019642690137449562112), (-1783338563/309485009821345068724781056)), (49/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((1105121945/19807040628566084398385987584), (4212656411/19807040628566084398385987584)), (19/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1469053669/8796093022208), (-662752031/2199023255552)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((-383802635/70368744177664), (630179797/17592186044416)), (1/70368744177664), by norm_num⟩
  | 2 => ⟨((-578930331/1125899906842624), (-175054819/70368744177664)), (3/2251799813685248), by norm_num⟩
  | 3 => ⟨((2834553243/36028797018963968), (2266881761/18014398509481984)), (5/36028797018963968), by norm_num⟩
  | 4 => ⟨((-1780752901/288230376151711744), (-2747713399/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 5 => ⟨((3371934511/9223372036854775808), (1051185445/9223372036854775808)), (3/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-2637554039/147573952589676412928), (17399935/18446744073709551616)), (11/295147905179352825856), by norm_num⟩
  | 7 => ⟨((3497000889/4722366482869645213696), (-1510151391/4722366482869645213696)), (5/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-3861789219/151115727451828646838272), (230588961/9444732965739290427392)), (9/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((801656369/1208925819614629174706176), (-822841743/604462909807314587353088)), (15/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-483994457/77371252455336267181195264), (613022631/9671406556917033397649408)), (13/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-1657682917/2475880078570760549798248448), (-6318984617/2475880078570760549798248448)), (41/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((613485483/9903520314283042199192993792), (875007905/9903520314283042199192993792)), (33/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1023473693/281474976710656), (-6721917835/281474976710656)), (3/281474976710656), by norm_num⟩
  | 1 => ⟨((192976777/281474976710656), (1867251403/562949953421312)), (3/1125899906842624), by norm_num⟩
  | 2 => ⟨((-1417276621/9007199254740992), (-2266881761/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((2374337201/144115188075855872), (3663617865/288230376151711744)), (3/144115188075855872), by norm_num⟩
  | 4 => ⟨((-5619890851/4611686018427387904), (-1751975741/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((2637554039/36893488147419103232), (-278398961/73786976294838206464)), (5/36893488147419103232), by norm_num⟩
  | 6 => ⟨((-2039917185/590295810358705651712), (1761843289/1180591620717411303424)), (11/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((1287263073/9444732965739290427392), (-76862987/590295810358705651712)), (11/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-2404969107/604462909807314587353088), (2468525229/302231454903657293676544)), (5/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((201664357/4835703278458516698824704), (-1021704385/2417851639229258349412352)), (9/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((759771337/154742504910672534362390528), (5792402565/309485009821345068724781056)), (31/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-613485483/1237940039285380274899124224), (-3500031619/4951760157141521099596496896)), (27/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((4931736263/158456325028528675187087900672), (851474049/39614081257132168796771975168)), (11/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-192976777/562949953421312), (-1867251403/1125899906842624)), (3/2251799813685248), by norm_num⟩
  | 1 => ⟨((2834553243/18014398509481984), (4533763523/18014398509481984)), (3/9007199254740992), by norm_num⟩
  | 2 => ⟨((-3561505801/144115188075855872), (-2747713399/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 3 => ⟨((5619890851/2305843009213693952), (875987871/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 4 => ⟨((-6593885097/36893488147419103232), (347998701/36893488147419103232)), (11/36893488147419103232), by norm_num⟩
  | 5 => ⟨((3059875777/295147905179352825856), (-1321382467/295147905179352825856)), (1/36893488147419103232), by norm_num⟩
  | 6 => ⟨((-2252710377/4722366482869645213696), (538040909/1180591620717411303424)), (9/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((2404969107/151115727451828646838272), (-4937050457/151115727451828646838272)), (19/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((-113436201/604462909807314587353088), (1149417433/604462909807314587353088)), (19/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((-237428543/9671406556917033397649408), (-3620251603/38685626227668133590597632)), (19/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((3374170157/1237940039285380274899124224), (1203135869/309485009821345068724781056)), (17/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-3698802197/19807040628566084398385987584), (-1277211073/9903520314283042199192993792)), (15/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((6514811591/633825300114114700748351602688), (12967415/4951760157141521099596496896)), (13/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1133821297/18014398509481984), (-1813505409/18014398509481984)), (5/36028797018963968), by norm_num⟩
  | 1 => ⟨((1424602321/72057594037927936), (68692835/4503599627370496)), (3/72057594037927936), by norm_num⟩
  | 2 => ⟨((-1685967255/576460752303423488), (-1051185445/1152921504606846976)), (3/576460752303423488), by norm_num⟩
  | 3 => ⟨((2637554039/9223372036854775808), (-17399935/1152921504606846976)), (5/9223372036854775808), by norm_num⟩
  | 4 => ⟨((-3059875777/147573952589676412928), (1321382467/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 5 => ⟨((2703252453/2361183241434822606848), (-2582596363/2361183241434822606848)), (11/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((-1683478375/37778931862957161709568), (431991915/4722366482869645213696)), (7/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((725991685/1208925819614629174706176), (-3678135785/604462909807314587353088)), (15/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((427371377/4835703278458516698824704), (6516452885/19342813113834066795298816)), (1/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-3374170157/309485009821345068724781056), (-1203135869/77371252455336267181195264)), (33/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((4068682417/4951760157141521099596496896), (2809864361/4951760157141521099596496896)), (1/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-1954443477/39614081257132168796771975168), (-7780449/618970019642690137449562112)), (15/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((6374348279/2535301200456458802993406410752), (-674704119/2535301200456458802993406410752)), (27/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1899469761/288230376151711744), (-2930894293/576460752303423488)), (9/576460752303423488), by norm_num⟩
  | 1 => ⟨((2247956341/1152921504606846976), (700790297/1152921504606846976)), (11/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-2637554039/9223372036854775808), (17399935/1152921504606846976)), (13/18446744073709551616), by norm_num⟩
  | 3 => ⟨((2039917185/73786976294838206464), (-1761843289/147573952589676412928)), (3/36893488147419103232), by norm_num⟩
  | 4 => ⟨((-2252710377/1180591620717411303424), (538040909/295147905179352825856)), (5/590295810358705651712), by norm_num⟩
  | 5 => ⟨((1683478375/18889465931478580854784), (-431991915/2361183241434822606848)), (7/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-211747575/151115727451828646838272), (268197401/18889465931478580854784)), (19/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-569828503/2417851639229258349412352), (-4344301923/4835703278458516698824704)), (23/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((2530627617/77371252455336267181195264), (3609407607/77371252455336267181195264)), (25/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((-3390568681/1237940039285380274899124224), (-1170776817/618970019642690137449562112)), (27/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((3583146375/19807040628566084398385987584), (28528313/618970019642690137449562112)), (7/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-6374348279/633825300114114700748351602688), (674704119/633825300114114700748351602688)), (27/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((4831097499/10141204801825835211973625643008), (-2395839305/10141204801825835211973625643008)), (13/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5138185921/9223372036854775808), (-1601806393/9223372036854775808)), (7/4611686018427387904), by norm_num⟩
  | 1 => ⟨((1507173737/9223372036854775808), (-2485705/288230376151711744)), (19/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-3497000889/147573952589676412928), (755075695/73786976294838206464)), (13/147573952589676412928), by norm_num⟩
  | 3 => ⟨((1287263073/590295810358705651712), (-76862987/36893488147419103232)), (13/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((-2404969107/18889465931478580854784), (4937050457/18889465931478580854784)), (23/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((362995843/151115727451828646838272), (-3678135785/151115727451828646838272)), (17/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((569828503/1208925819614629174706176), (4344301923/2417851639229258349412352)), (25/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((-361518231/4835703278458516698824704), (-4125037265/38685626227668133590597632)), (1/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((4359302589/618970019642690137449562112), (1505284479/309485009821345068724781056)), (37/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((-5118780535/9903520314283042199192993792), (-1304151451/9903520314283042199192993792)), (21/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((5008416505/158456325028528675187087900672), (-530124665/158456325028528675187087900672)), (45/158456325028528675187087900672), by norm_num⟩
  | 11 => ⟨((-4140940713/2535301200456458802993406410752), (2053576547/2535301200456458802993406410752)), (23/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((87946401/1267650600228229401496703205376), (-1493924017/20282409603651670423947251286016)), (23/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6028694947/147573952589676412928), (2485705/1152921504606846976)), (21/147573952589676412928), by norm_num⟩
  | 1 => ⟨((3497000889/295147905179352825856), (-1510151391/295147905179352825856)), (1/18446744073709551616), by norm_num⟩
  | 2 => ⟨((-965447305/590295810358705651712), (3689423375/2361183241434822606848)), (25/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((601242277/4722366482869645213696), (-4937050457/18889465931478580854784)), (27/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((-113436201/37778931862957161709568), (4597669731/151115727451828646838272)), (25/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((-427371377/604462909807314587353088), (-1629113221/604462909807314587353088)), (5/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((2530627617/19342813113834066795298816), (3609407607/19342813113834066795298816)), (31/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((-4359302589/309485009821345068724781056), (-1505284479/154742504910672534362390528)), (41/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((2879314051/2475880078570760549798248448), (1467170383/4951760157141521099596496896)), (51/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((-6260520631/79228162514264337593543950336), (662655831/79228162514264337593543950336)), (61/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((711724185/158456325028528675187087900672), (-352958469/158456325028528675187087900672)), (17/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((-263839203/1267650600228229401496703205376), (2240886025/10141204801825835211973625643008)), (37/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((2244165063/324518553658426726783156020576256), (-662442589/40564819207303340847894502572032)), (19/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3108445235/1180591620717411303424), (167794599/147573952589676412928)), (17/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((429087691/590295810358705651712), (-1639743723/2361183241434822606848)), (13/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((-1603312739/18889465931478580854784), (3291366971/18889465931478580854784)), (23/18889465931478580854784), by norm_num⟩
  | 3 => ⟨((403328715/151115727451828646838272), (-4086817539/151115727451828646838272)), (27/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((949714171/1208925819614629174706176), (1810125801/604462909807314587353088)), (27/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((-843542539/4835703278458516698824704), (-1203135869/4835703278458516698824704)), (45/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((423821085/19342813113834066795298816), (1170776817/77371252455336267181195264)), (9/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((-5118780535/2475880078570760549798248448), (-1304151451/2475880078570760549798248448)), (13/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((6260520631/39614081257132168796771975168), (-331327915/19807040628566084398385987584)), (17/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((-395402325/39614081257132168796771975168), (784352153/158456325028528675187087900672)), (43/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((322470137/633825300114114700748351602688), (-2738860697/5070602400912917605986812821504)), (25/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((-748055021/40564819207303340847894502572032), (3533027141/81129638414606681695789005144064)), (7/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((343650485/2596148429267413814265248164610048), (-1880901797/649037107316853453566312041152512)), (15/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2746161223/18889465931478580854784), (2623589957/18889465931478580854784)), (25/18889465931478580854784), by norm_num⟩
  | 1 => ⟨((2565300381/75557863725914323419136), (-5266187155/75557863725914323419136)), (21/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((-241997229/151115727451828646838272), (4904181047/302231454903657293676544)), (5/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((-1519542673/2417851639229258349412352), (-1448100641/604462909807314587353088)), (13/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((3374170155/19342813113834066795298816), (1203135869/4835703278458516698824704)), (55/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((-254292651/9671406556917033397649408), (-2809864361/154742504910672534362390528)), (49/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((1791573187/618970019642690137449562112), (28528313/38685626227668133590597632)), (41/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((-626052063/2475880078570760549798248448), (530124665/19807040628566084398385987584)), (63/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((711724185/39614081257132168796771975168), (-2823667751/316912650057057350374175801344)), (43/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((-322470137/316912650057057350374175801344), (2738860697/2535301200456458802993406410752)), (7/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((822860523/20282409603651670423947251286016), (-3886329855/40564819207303340847894502572032)), (35/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((-206190291/649037107316853453566312041152512), (4514164313/649037107316853453566312041152512)), (81/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((-1414244831/10384593717069655257060992658440192), (-553245677/1298074214633706907132624082305024)), (91/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((219136/40002411), (-27072/13334137)), 0, by norm_num⟩
  | 1 => ⟨((-82849095680/533397628604307), (23729799168/177799209534769)), 0, by norm_num⟩
  | 2 => ⟨((1958738225/562949953421312), (-3534677499/562949953421312)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-682315795/18014398509481984), (4481278557/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((-1029209477/576460752303423488), (-4979337075/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 5 => ⟨((3023523459/18446744073709551616), (604501803/2305843009213693952)), (7/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-633156587/73786976294838206464), (-1953929529/295147905179352825856)), (7/295147905179352825856), by norm_num⟩
  | 7 => ⟨((3425457281/9444732965739290427392), (1067870929/9444732965739290427392)), (5/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-8038259929/604462909807314587353088), (424226987/604462909807314587353088)), (29/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((4144593647/9671406556917033397649408), (-55931533/302231454903657293676544)), (23/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-3661548297/309485009821345068724781056), (3498119943/309485009821345068724781056)), (17/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((2487564007/9903520314283042199192993792), (-5106605727/9903520314283042199192993792)), (25/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-156442653/79228162514264337593543950336), (6340759335/316912650057057350374175801344)), (73/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((671372769/33554432), (1715986835/134217728)), (1/33554432), by norm_num⟩
  | 1 => ⟨((2818102513/2147483648), (788927523/4294967296)), (3/4294967296), by norm_num⟩
  | 2 => ⟨((4647398775/549755813888), (-893873083/274877906944)), (1/549755813888), by norm_num⟩
  | 3 => ⟨((-2856230699/35184372088832), (1288796949/17592186044416)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((2018684979/2251799813685248), (-993561975/562949953421312)), (17/2251799813685248), by norm_num⟩
  | 5 => ⟨((-10012129/2251799813685248), (1540554047/36028797018963968)), (41/144115188075855872), by norm_num⟩
  | 6 => ⟨((-620440151/2305843009213693952), (-2309250807/2305843009213693952)), (57/4611686018427387904), by norm_num⟩
  | 7 => ⟨((580989027/36893488147419103232), (1599410739/73786976294838206464)), (79/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2875894731/4722366482869645213696), (-1871708267/4722366482869645213696)), (27/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((377281557/18889465931478580854784), (1297191873/302231454903657293676544)), (71/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-5644873435/9671406556917033397649408), (872513355/9671406556917033397649408)), (405/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((2346720183/154742504910672534362390528), (-2675629309/309485009821345068724781056)), (283/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-206524409/618970019642690137449562112), (4018887397/9903520314283042199192993792)), (753/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1044660387/2251799813685248), (3770322665/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((1091705273/72057594037927936), (-3585022845/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 2 => ⟨((411683791/288230376151711744), (3983469659/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 3 => ⟨((-1007841153/4611686018427387904), (-201500601/576460752303423488)), (5/9223372036854775808), by norm_num⟩
  | 4 => ⟨((633156587/36893488147419103232), (244241191/18446744073709551616)), (1/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-4795640193/4722366482869645213696), (-373754825/1180591620717411303424)), (5/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((7502375933/151115727451828646838272), (-98986297/37778931862957161709568)), (17/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-4973512375/2417851639229258349412352), (2147770867/2417851639229258349412352)), (15/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((1373080611/19342813113834066795298816), (-655897489/9671406556917033397649408)), (7/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-2280267005/1237940039285380274899124224), (4681055249/1237940039285380274899124224)), (11/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((86043459/4951760157141521099596496896), (-1743708817/9903520314283042199192993792)), (19/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((1178796741/633825300114114700748351602688), (1123375043/158456325028528675187087900672)), (15/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-872512687/5070602400912917605986812821504), (-1244455687/5070602400912917605986812821504)), (3/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1342745507/67108864), (1715986947/134217728)), (5/134217728), by norm_num⟩
  | 1 => ⟨((5636205091/4294967296), (98615887/536870912)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((580924945/68719476736), (-1787742367/549755813888)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((-714059597/8796093022208), (2577581599/35184372088832)), (7/35184372088832), by norm_num⟩
  | 4 => ⟨((252340453/281474976710656), (-3974218085/2251799813685248)), (9/1125899906842624), by norm_num⟩
  | 5 => ⟨((-640922607/144115188075855872), (1540542641/36028797018963968)), (21/72057594037927936), by norm_num⟩
  | 6 => ⟨((-310162837/1152921504606846976), (-4618513697/4611686018427387904)), (29/2305843009213693952), by norm_num⟩
  | 7 => ⟨((2323652549/147573952589676412928), (399869071/18446744073709551616)), (5/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-1437779753/2361183241434822606848), (-1872028529/4722366482869645213696)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((3017974103/151115727451828646838272), (1298334709/302231454903657293676544)), (285/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-5644705381/9671406556917033397649408), (435405257/4835703278458516698824704)), (203/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((2347007975/154742504910672534362390528), (-2673435217/309485009821345068724781056)), (567/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-1653047335/4951760157141521099596496896), (4016456819/9903520314283042199192993792)), (377/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1254655363/4611686018427387904), (-6070049005/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 1 => ⟨((2303636921/18446744073709551616), (3684582419/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-2894430111/147573952589676412928), (-1116531159/73786976294838206464)), (5/147573952589676412928), by norm_num⟩
  | 3 => ⟨((2283638187/1180591620717411303424), (1423827905/2361183241434822606848)), (1/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-334927497/2361183241434822606848), (35352249/4722366482869645213696)), (5/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((2486756187/302231454903657293676544), (-2147770867/604462909807314587353088)), (7/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-3661548295/9671406556917033397649408), (1749059971/4835703278458516698824704)), (1/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((122157161/9671406556917033397649408), (-2006166535/77371252455336267181195264)), (1/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((-184378841/1237940039285380274899124224), (7473037787/4951760157141521099596496896)), (1/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-24119725/1237940039285380274899124224), (-5884345463/79228162514264337593543950336)), (1/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((2742182731/1267650600228229401496703205376), (977786611/316912650057057350374175801344)), (7/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((-1503005337/10141204801825835211973625643008), (-2075974823/20282409603651670423947251286016)), (13/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((5294577039/649037107316853453566312041152512), (1348940491/649037107316853453566312041152512)), (43/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1342745507/67108864), (1715986947/134217728)), (3/67108864), by norm_num⟩
  | 1 => ⟨((1409051273/1073741824), (788927097/4294967296)), (5/4294967296), by norm_num⟩
  | 2 => ⟨((4647399549/549755813888), (-1787742375/549755813888)), (3/549755813888), by norm_num⟩
  | 3 => ⟨((-178514895/2199023255552), (644395405/8796093022208)), (1/4398046511104), by norm_num⟩
  | 4 => ⟨((2018723305/2251799813685248), (-993554517/562949953421312)), (19/2251799813685248), by norm_num⟩
  | 5 => ⟨((-640921421/144115188075855872), (1540542513/36028797018963968)), (43/144115188075855872), by norm_num⟩
  | 6 => ⟨((-620326547/2305843009213693952), (-4618512029/4611686018427387904)), (59/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2323654413/147573952589676412928), (1599474371/73786976294838206464)), (81/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2875560209/4722366482869645213696), (-936010701/2361183241434822606848)), (55/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((6035942317/302231454903657293676544), (649156131/151115727451828646838272)), (143/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-1411171115/2417851639229258349412352), (435420177/4835703278458516698824704)), (407/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((2346985041/154742504910672534362390528), (-1336733447/154742504910672534362390528)), (71/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((-3306013881/9903520314283042199192993792), (2008238701/4951760157141521099596496896)), (755/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4631088179/1180591620717411303424), (1786449855/590295810358705651712)), (3/295147905179352825856), by norm_num⟩
  | 1 => ⟨((-2740365825/2361183241434822606848), (-854296743/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((6430607943/37778931862957161709568), (-339381589/37778931862957161709568)), (17/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((-4973512375/302231454903657293676544), (2147770867/302231454903657293676544)), (1/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((2746161221/2417851639229258349412352), (-655897489/604462909807314587353088)), (13/2417851639229258349412352), by norm_num⟩
  | 5 => ⟨((-2052240305/38685626227668133590597632), (4212949723/38685626227668133590597632)), (9/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((258130377/309485009821345068724781056), (-2615563225/309485009821345068724781056)), (3/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((43415505/309485009821345068724781056), (1323977729/2475880078570760549798248448)), (29/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((-3084955571/158456325028528675187087900672), (-4400039749/158456325028528675187087900672)), (1/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((2066632339/1267650600228229401496703205376), (1427232691/1267650600228229401496703205376)), (17/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((-4368026057/40564819207303340847894502572032), (-1112875905/40564819207303340847894502572032)), (35/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((1942658523/324518553658426726783156020576256), (-411248225/649037107316853453566312041152512)), (17/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((-368083619/1298074214633706907132624082305024), (365080275/2596148429267413814265248164610048)), (33/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1342745507/67108864), (1715986947/134217728)), (7/134217728), by norm_num⟩
  | 1 => ⟨((1409051273/1073741824), (788927097/4294967296)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((4647399549/549755813888), (-1787742375/549755813888)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-2856238321/35184372088832), (644395405/8796093022208)), (9/35184372088832), by norm_num⟩
  | 4 => ⟨((504680827/562949953421312), (-1987109035/1125899906842624)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((-640921429/144115188075855872), (1540542517/36028797018963968)), (11/36028797018963968), by norm_num⟩
  | 6 => ⟨((-620326545/2305843009213693952), (-1154628017/1152921504606846976)), (15/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1161827217/73786976294838206464), (3198948821/147573952589676412928)), (41/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-2875560301/4722366482869645213696), (-1872021533/4722366482869645213696)), (111/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((3017971405/151115727451828646838272), (649156301/151115727451828646838272)), (287/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-5644685501/9671406556917033397649408), (870840089/9671406556917033397649408)), (51/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((4693971935/309485009821345068724781056), (-1336733545/154742504910672534362390528)), (569/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-3306016689/9903520314283042199192993792), (4016478795/9903520314283042199192993792)), (189/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5196450863/151115727451828646838272), (274247749/151115727451828646838272)), (19/151115727451828646838272), by norm_num⟩
  | 1 => ⟨((3014249925/302231454903657293676544), (-1301679313/302231454903657293676544)), (15/302231454903657293676544), by norm_num⟩
  | 2 => ⟨((-1664340135/1208925819614629174706176), (3180109037/2417851639229258349412352)), (23/2417851639229258349412352), by norm_num⟩
  | 3 => ⟨((1036485003/9671406556917033397649408), (-4255504771/19342813113834066795298816)), (3/2417851639229258349412352), by norm_num⟩
  | 4 => ⟨((-48888329/19342813113834066795298816), (3962974583/154742504910672534362390528)), (23/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((-736747963/1237940039285380274899124224), (-5616875213/2475880078570760549798248448)), (35/2475880078570760549798248448), by norm_num⟩
  | 6 => ⟨((2181281717/19807040628566084398385987584), (3111139217/19807040628566084398385987584)), (27/19807040628566084398385987584), by norm_num⟩
  | 7 => ⟨((-3757513343/316912650057057350374175801344), (-2594968529/316912650057057350374175801344)), (37/316912650057057350374175801344), by norm_num⟩
  | 8 => ⟨((4963665973/5070602400912917605986812821504), (1264631711/5070602400912917605986812821504)), (45/5070602400912917605986812821504), by norm_num⟩
  | 9 => ⟨((-5396273675/81129638414606681695789005144064), (285589045/40564819207303340847894502572032)), (53/81129638414606681695789005144064), by norm_num⟩
  | 10 => ⟨((4907781585/1298074214633706907132624082305024), (-608467125/324518553658426726783156020576256)), (15/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((-1819335649/10384593717069655257060992658440192), (3863076245/20769187434139310514121985316880384)), (1/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((1934364499/332306998946228968225951765070086144), (-1141988571/83076749736557242056487941267521536)), (67/332306998946228968225951765070086144), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1342745507/67108864), (1715986947/134217728)), (1/16777216), by norm_num⟩
  | 1 => ⟨((1409051273/1073741824), (788927097/4294967296)), (7/4294967296), by norm_num⟩
  | 2 => ⟨((4647399549/549755813888), (-1787742375/549755813888)), (5/549755813888), by norm_num⟩
  | 3 => ⟨((-2856238321/35184372088832), (644395405/8796093022208)), (5/17592186044416), by norm_num⟩
  | 4 => ⟨((504680827/562949953421312), (-1987109035/1125899906842624)), (21/2251799813685248), by norm_num⟩
  | 5 => ⟨((-640921429/144115188075855872), (1540542517/36028797018963968)), (45/144115188075855872), by norm_num⟩
  | 6 => ⟨((-1240653089/4611686018427387904), (-4618512067/4611686018427387904)), (61/4611686018427387904), by norm_num⟩
  | 7 => ⟨((72614201/4611686018427387904), (799737205/36893488147419103232)), (83/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-359445037/590295810358705651712), (-468005383/1180591620717411303424)), (7/295147905179352825856), by norm_num⟩
  | 9 => ⟨((3017971395/151115727451828646838272), (324578151/75557863725914323419136)), (9/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-705585683/1208925819614629174706176), (870840071/9671406556917033397649408)), (409/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((4693971881/309485009821345068724781056), (-334183379/38685626227668133590597632)), (285/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-3306016631/9903520314283042199192993792), (4016478659/9903520314283042199192993792)), (757/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2696109089/9671406556917033397649408), (-1287885917/4835703278458516698824704)), (25/9671406556917033397649408), by norm_num⟩
  | 1 => ⟨((-157409041/2417851639229258349412352), (5170204479/38685626227668133590597632)), (21/19342813113834066795298816), by norm_num⟩
  | 2 => ⟨((475173069/154742504910672534362390528), (-4814796373/154742504910672534362390528)), (5/19342813113834066795298816), by norm_num⟩
  | 3 => ⟨((1491847157/1237940039285380274899124224), (5686828971/1237940039285380274899124224)), (13/309485009821345068724781056), by norm_num⟩
  | 4 => ⟨((-3312671793/9903520314283042199192993792), (-295301813/618970019642690137449562112)), (55/9903520314283042199192993792), by norm_num⟩
  | 5 => ⟨((1997262861/39614081257132168796771975168), (344831395/9903520314283042199192993792)), (49/79228162514264337593543950336), by norm_num⟩
  | 6 => ⟨((-1758919583/316912650057057350374175801344), (-112033399/79228162514264337593543950336)), (41/633825300114114700748351602688), by norm_num⟩
  | 7 => ⟨((1229283003/2535301200456458802993406410752), (-520462497/10141204801825835211973625643008)), (63/10141204801825835211973625643008), by norm_num⟩
  | 8 => ⟨((-5590017157/162259276829213363391578010288128), (1386101483/81129638414606681695789005144064)), (43/81129638414606681695789005144064), by norm_num⟩
  | 9 => ⟨((2532741807/1298074214633706907132624082305024), (-336117703/162259276829213363391578010288128)), (7/162259276829213363391578010288128), by norm_num⟩
  | 10 => ⟨((-1615725775/20769187434139310514121985316880384), (3815496759/20769187434139310514121985316880384)), (69/20769187434139310514121985316880384), by norm_num⟩
  | 11 => ⟨((101216111/166153499473114484112975882535043072), (-4431888169/332306998946228968225951765070086144)), (5/20769187434139310514121985316880384), by norm_num⟩
  | 12 => ⟨((86779281/332306998946228968225951765070086144), (1086324201/1329227995784915872903807060280344576)), (45/2658455991569831745807614120560689152), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1342745507/67108864), (1715986947/134217728)), (9/134217728), by norm_num⟩
  | 1 => ⟨((1409051273/1073741824), (788927097/4294967296)), (1/536870912), by norm_num⟩
  | 2 => ⟨((4647399549/549755813888), (-1787742375/549755813888)), (3/274877906944), by norm_num⟩
  | 3 => ⟨((-2856238321/35184372088832), (644395405/8796093022208)), (11/35184372088832), by norm_num⟩
  | 4 => ⟨((504680827/562949953421312), (-1987109035/1125899906842624)), (11/1125899906842624), by norm_num⟩
  | 5 => ⟨((-640921429/144115188075855872), (1540542517/36028797018963968)), (23/72057594037927936), by norm_num⟩
  | 6 => ⟨((-1240653089/4611686018427387904), (-4618512067/4611686018427387904)), (31/2305843009213693952), by norm_num⟩
  | 7 => ⟨((72614201/4611686018427387904), (799737205/36893488147419103232)), (21/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-359445037/590295810358705651712), (-468005383/1180591620717411303424)), (113/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((6035942791/302231454903657293676544), (1298312603/302231454903657293676544)), (289/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-5644685465/9671406556917033397649408), (870840073/9671406556917033397649408)), (205/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((4693971881/309485009821345068724781056), (-668366759/77371252455336267181195264)), (571/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-826504157/2475880078570760549798248448), (4016478667/9903520314283042199192993792)), (379/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1001668756662379/2097152), (55663897890485/524288)), (10543863/262144), by norm_num⟩
  | 1 => ⟨((2429146447/4), 227060171), (491/8), by norm_num⟩
  | 2 => ⟨(381994444, 204102863), (189/4), by norm_num⟩
  | 3 => ⟨((1267727469/8), (1802538405/16)), (49/2), by norm_num⟩
  | 4 => ⟨((3117576749/64), (2847831113/64)), (307/32), by norm_num⟩
  | 5 => ⟨((1511122833/128), (1747092331/128)), (97/32), by norm_num⟩
  | 6 => ⟨((299467613/128), (1751136469/512)), (103/128), by norm_num⟩
  | 7 => ⟨((1585736427/4096), (741846275/1024)), (189/1024), by norm_num⟩
  | 8 => ⟨((220853055/4096), (4356225747/32768)), (153/4096), by norm_num⟩
  | 9 => ⟨((821411899/131072), (176352529/8192)), (889/131072), by norm_num⟩
  | 10 => ⟨((610469371/1048576), (6544042643/2097152)), (293/262144), by norm_num⟩
  | 11 => ⟨((38149935/1048576), (1717654641/4194304)), (2835/16777216), by norm_num⟩
  | 12 => ⟨((-29243215/134217728), (6591672769/134217728)), (793/33554432), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((402509757411305/2535301200456458802993406410752), (71229552761/2535301200456458802993406410752)), (21837/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((906716032504335/316912650057057350374175801344), (349474705093/633825300114114700748351602688)), (107177/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((964389774690171/19807040628566084398385987584), (197090632491/19807040628566084398385987584)), (120891/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((965516687084661/1237940039285380274899124224), (419693261827/2475880078570760549798248448)), (64359/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1812743280239341/154742504910672534362390528), (105168293857/38685626227668133590597632)), (64511/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((794277730071829/4835703278458516698824704), (197712661517/4835703278458516698824704)), (60641/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((646481026211647/302231454903657293676544), (347045027691/604462909807314587353088)), (106447/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1943411355814121/75557863725914323419136), (141480179973/18889465931478580854784)), (43397/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1339330808434945/4722366482869645213696), (426174351101/4722366482869645213696)), (130729/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((839518292599085/295147905179352825856), (588821934791/590295810358705651712)), (180629/590295810358705651712), by norm_num⟩
  | 8 => ⟨((236956127070559/9223372036854775808), (740301705539/73786976294838206464)), (227113/73786976294838206464), by norm_num⟩
  | 7 => ⟨((952056978598931/4611686018427387904), (419379540947/4611686018427387904)), (128669/4611686018427387904), by norm_num⟩
  | 6 => ⟨((837845225041275/576460752303423488), (423111478865/576460752303423488)), (129827/576460752303423488), by norm_num⟩
  | 5 => ⟨((633221954598671/72057594037927936), (374465603775/72057594037927936)), (114915/72057594037927936), by norm_num⟩
  | 4 => ⟨((800091027072049/18014398509481984), (285148694351/9007199254740992)), (175041/18014398509481984), by norm_num⟩
  | 3 => ⟨((101641628157603/562949953421312), (1456354975439/9007199254740992)), (3493/70368744177664), by norm_num⟩
  | 2 => ⟨((1253004486735549/2251799813685248), (751660279421/1125899906842624)), (115421/562949953421312), by norm_num⟩
  | 1 => ⟨((1321762175656083/1125899906842624), (2376147295017/1125899906842624)), (730157/1125899906842624), by norm_num⟩
  | 0 => ⟨((1539117335944265/1125899906842624), (2630078443649/562949953421312)), (1618117/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1539117335944265/1125899906842624), (2630078443649/562949953421312)), (6172626499656295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1051982725177011/562949953421312), (1797672822829/140737488355328)), (277443/70368744177664), by norm_num⟩
  | 2 => ⟨((1965744807871779/562949953421312), (26874442300145/562949953421312)), (2088003/140737488355328), by norm_num⟩
  | 3 => ⟨((428926939968867/35184372088832), (23460475968999/70368744177664)), (3695351/35184372088832), by norm_num⟩
  | 4 => ⟨((1306266890906351/8796093022208), (4468794297983/549755813888)), (23140715/8796093022208), by norm_num⟩
  | 5 => ⟨((1510987636276313/68719476736), (165909967612557/68719476736)), (56634747/68719476736), by norm_num⟩
  | 6 => ⟨((1001668756662379/2097152), (55663897890485/524288)), (10543863/262144), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((1342745507/67108864), (1715986947/134217728)), (9/134217728), by norm_num⟩, 2, gammaExpValuePoly, gammaExpValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem gammaExpValue_checks : CertifiedScalarExp.Checks gammaExpValue := by
  constructor
  · norm_num [gammaExpValue, CertifiedScalarExp.reduced, gammaExpValuePoly, gammaExpValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [gammaExpValue, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        gammaExpValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [gammaExpValue, gammaExpValueSquares, gammaExpValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [gammaExpValue, CertifiedScalarExp.roundingCheck, gammaExpValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_gammaExp : Sound J_gammaExp F_gammaExp c := by
  apply exp_sound (A_mainCorr6 hcre) S_mainCorr6 gammaExpValue gammaExpValue_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [gammaExpValue,J_mainCorr6]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaExp,J_mainCorr6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse0 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((90112/1734265), (-324864/1734265)), 0, by norm_num⟩
  | 1 => ⟨((48708222976/3007675090225), (29274144768/3007675090225)), 0, by norm_num⟩
  | 2 => ⟨((-6949655577362432/5216105640349059625), (6592798207770624/5216105640349059625)), 0, by norm_num⟩
  | 3 => ⟨((-1473629609/17592186044416), (-5545931085/35184372088832)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((2384014875/140737488355328), (-1055671369/281474976710656)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-399971507/4503599627370496), (7584030699/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 6 => ⟨((-2799729357/18014398509481984), (-1875949795/36028797018963968)), (3/18014398509481984), by norm_num⟩
  | 7 => ⟨((2569404279/288230376151711744), (-951421477/72057594037927936)), (7/288230376151711744), by norm_num⟩
  | 8 => ⟨((2317514771/2305843009213693952), (84880693/72057594037927936)), (1/288230376151711744), by norm_num⟩
  | 9 => ⟨((-5033720671/36893488147419103232), (1171946641/18446744073709551616)), (1/2305843009213693952), by norm_num⟩
  | 10 => ⟨((-710036609/295147905179352825856), (-532354497/36893488147419103232)), (1/18446744073709551616), by norm_num⟩
  | 11 => ⟨((1669324249/1180591620717411303424), (706267587/4722366482869645213696)), (1/147573952589676412928), by norm_num⟩
  | 12 => ⟨((-1916997691/37778931862957161709568), (4856397901/37778931862957161709568)), (1/1180591620717411303424), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (1269/256)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (1269/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (1269/256)))⁻¹=value ((90112/1734265), (-324864/1734265)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((90112/1734265), (-324864/1734265))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (1269/256)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor1 : Sound J_gammaFactor1 F_gammaFactor1 c := by
  apply sound_round (sound_add (A_base hcre) (A_q0 hcre) S_base S_q0)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor1, J_base, J_q0, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((155648/1980025), (-324864/1980025)), 0, by norm_num⟩
  | 1 => ⟨((40655159296/3920499000625), (50564431872/3920499000625)), 0, by norm_num⟩
  | 2 => ⟨((-11377228914884608/7762686033712515625), (2668572488761344/7762686033712515625)), 0, by norm_num⟩
  | 3 => ⟨((129323373/4398046511104), (-2352869897/17592186044416)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((690745853/70368744177664), (2158637499/281474976710656)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-1142729465/1125899906842624), (1134543723/2251799813685248)), (5/4503599627370496), by norm_num⟩
  | 6 => ⟨((-103799097/72057594037927936), (-1856648863/18014398509481984)), (11/72057594037927936), by norm_num⟩
  | 7 => ⟨((4906583759/576460752303423488), (1133535323/288230376151711744)), (3/144115188075855872), by norm_num⟩
  | 8 => ⟨((-3030647769/4611686018427387904), (2507256049/4611686018427387904)), (13/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-692522499/36893488147419103232), (-2777334117/36893488147419103232)), (27/73786976294838206464), by norm_num⟩
  | 10 => ⟨((4080940847/590295810358705651712), (837609107/590295810358705651712)), (27/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-3665809577/9444732965739290427392), (4829751483/9444732965739290427392)), (53/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((-252127235/9444732965739290427392), (-981114239/18889465931478580854784)), (53/75557863725914323419136), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (1269/256)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (1269/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (1269/256)))⁻¹=value ((155648/1980025), (-324864/1980025)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((155648/1980025), (-324864/1980025))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-18302173184/686777611325), (-15967715328/686777611325)), 0, by norm_num⟩
  | 1 => ⟨((100068417/17179869184), (-869796337/274877906944)), (1/549755813888), by norm_num⟩
  | 2 => ⟨((586192757/4398046511104), (4046914823/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-3981846203/35184372088832), (-840191291/35184372088832)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((1002523169/140737488355328), (-803577217/70368744177664)), (3/281474976710656), by norm_num⟩
  | 5 => ⟨((2085473177/2251799813685248), (2657471627/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 6 => ⟨((-2773779583/18014398509481984), (1837347931/36028797018963968)), (7/36028797018963968), by norm_num⟩
  | 7 => ⟨((116112399/288230376151711744), (-4939221231/288230376151711744)), (9/288230376151711744), by norm_num⟩
  | 8 => ⟨((7486013/4503599627370496), (1462554151/2305843009213693952)), (11/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-1085299543/9223372036854775808), (640153425/4611686018427387904)), (3/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-2750507033/295147905179352825856), (-2338820265/147573952589676412928)), (3/36893488147419103232), by norm_num⟩
  | 11 => ⟨((4255100893/2361183241434822606848), (-427152039/1180591620717411303424)), (13/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((-908488751/37778931862957161709568), (6818626381/37778931862957161709568)), (13/9444732965739290427392), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct1 : Sound J_gammaProduct1 F_gammaProduct1 c := by
  apply sound_round (sound_mul (A_gammaInverse0 hcre) (A_gammaInverse1 hcre) S_gammaInverse0 S_gammaInverse1)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct1, J_gammaInverse0, J_gammaInverse1, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(2, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q3 : Sound J_q3 F_q3 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (2, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((27/8), (1269/256)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor2 : Sound J_gammaFactor2 F_gammaFactor2 c := by
  apply sound_round (sound_add (A_base hcre) (A_q3 hcre) S_base S_q3)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor2, J_base, J_q3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((8192/87291), (-12032/87291)), 0, by norm_num⟩
  | 1 => ⟨((12943360/2539906227), (98566144/7619718681)), 0, by norm_num⟩
  | 2 => ⟨((-752021929984/665132863383171), (-170125164544/665132863383171)), 0, by norm_num⟩
  | 3 => ⟨((1243435721/17592186044416), (-2319359033/35184372088832)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((690479159/562949953421312), (4483598665/562949953421312)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-5462470533/9007199254740992), (-2604785833/9007199254740992)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((435837267/9007199254740992), (-508483577/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 7 => ⟨((-93726353/288230376151711744), (2685909971/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 8 => ⟨((-705256125/2305843009213693952), (-1111610839/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 9 => ⟨((2284754943/73786976294838206464), (-1441608853/147573952589676412928)), (15/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-1841013371/2361183241434822606848), (6121135299/2361183241434822606848)), (57/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-2683801005/18889465931478580854784), (-3312846147/18889465931478580854784)), (27/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((5668017337/302231454903657293676544), (-118057029/75557863725914323419136)), (101/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (1269/256)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (1269/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (1269/256)))⁻¹=value ((8192/87291), (-12032/87291)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((8192/87291), (-12032/87291))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-342054953549824/59949504470170575), (89404223782912/59949504470170575)), 0, by norm_num⟩
  | 1 => ⟨((605669923/2199023255552), (-6874326011/4398046511104)), (3/4398046511104), by norm_num⟩
  | 2 => ⟨((2059522001/8796093022208), (1410086145/8796093022208)), (3/17592186044416), by norm_num⟩
  | 3 => ⟨((-5059123491/140737488355328), (3092378939/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-825394987/1125899906842624), (-6262294069/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((6010628947/9007199254740992), (435865723/2251799813685248)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((-3752310549/72057594037927936), (4533678503/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 7 => ⟨((-2430905833/576460752303423488), (-147806299/18014398509481984)), (3/144115188075855872), by norm_num⟩
  | 8 => ⟨((4642906415/4611686018427387904), (-346879293/4611686018427387904)), (7/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-1253149101/36893488147419103232), (3769079651/36893488147419103232)), (17/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-2451711/288230376151711744), (-2165651585/295147905179352825856)), (9/147573952589676412928), by norm_num⟩
  | 11 => ⟨((4836078161/4722366482869645213696), (-2475847717/4722366482869645213696)), (19/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((202130589/18889465931478580854784), (1090228293/9444732965739290427392)), (5/4722366482869645213696), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct2 : Sound J_gammaProduct2 F_gammaProduct2 c := by
  apply sound_round (sound_mul (A_gammaProduct1 hcre) (A_gammaInverse2 hcre) S_gammaProduct1 S_gammaInverse2)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct2, J_gammaProduct1, J_gammaInverse2, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(3, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q4 : Sound J_q4 F_q4 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (3, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((35/8), (1269/256)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor3 : Sound J_gammaFactor3 F_gammaFactor3 c := by
  apply sound_round (sound_add (A_base hcre) (A_q4 hcre) S_base S_q4)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor3, J_base, J_q4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((286720/2864761), (-324864/2864761)), 0, by norm_num⟩
  | 1 => ⟨((11664130048/8206855587121), (93145006080/8206855587121)), 0, by norm_num⟩
  | 2 => ⟨((-3143062439/4398046511104), (-1071760419/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((2230596711/35184372088832), (-567555257/35184372088832)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((-1271110345/562949953421312), (2478028745/562949953421312)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-1230314353/9007199254740992), (-784315615/2251799813685248)), (3/4503599627370496), by norm_num⟩
  | 6 => ⟨((3831214857/144115188075855872), (348951309/36028797018963968)), (11/144115188075855872), by norm_num⟩
  | 7 => ⟨((-4333856251/2305843009213693952), (2358084339/2305843009213693952)), (5/576460752303423488), by norm_num⟩
  | 8 => ⟨((1330782019/36893488147419103232), (-1454937301/9223372036854775808)), (35/36893488147419103232), by norm_num⟩
  | 9 => ⟨((2107073065/295147905179352825856), (2933524523/295147905179352825856)), (31/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-1087096969/1180591620717411303424), (-437280365/4722366482869645213696)), (27/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((3878372877/75557863725914323419136), (-1797368301/37778931862957161709568)), (93/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((155806199/1208925819614629174706176), (199896833/37778931862957161709568)), (5/37778931862957161709568), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (1269/256)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (1269/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (1269/256)))⁻¹=value ((286720/2864761), (-324864/2864761)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((286720/2864761), (-324864/2864761))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-220969505/549755813888), (3502112177/4398046511104)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((-3073673879/17592186044416), (-4403481355/17592186044416)), (3/17592186044416), by norm_num⟩
  | 2 => ⟨((4542218939/70368744177664), (-138758249/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((-273667519/70368744177664), (5815377209/562949953421312)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-2466195431/2251799813685248), (-1363466827/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((955705575/4503599627370496), (-130148263/2251799813685248)), (3/9007199254740992), by norm_num⟩
  | 6 => ⟨((-781011053/144115188075855872), (3909393741/144115188075855872)), (9/144115188075855872), by norm_num⟩
  | 7 => ⟨((-3019945591/1152921504606846976), (-1157395821/576460752303423488)), (11/1152921504606846976), by norm_num⟩
  | 8 => ⟨((3109696115/9223372036854775808), (-1565589221/9223372036854775808)), (7/4611686018427387904), by norm_num⟩
  | 9 => ⟨((69198369/73786976294838206464), (768999869/18446744073709551616)), (1/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-4833369101/1180591620717411303424), (-2128329251/1180591620717411303424)), (9/295147905179352825856), by norm_num⟩
  | 11 => ⟨((3306920767/9444732965739290427392), (-733193601/2361183241434822606848)), (39/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((33637153/2361183241434822606848), (1727683493/37778931862957161709568)), (21/37778931862957161709568), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct3 : Sound J_gammaProduct3 F_gammaProduct3 c := by
  apply sound_round (sound_mul (A_gammaProduct2 hcre) (A_gammaInverse3 hcre) S_gammaProduct2 S_gammaInverse3)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct3, J_gammaProduct2, J_gammaInverse3, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(4, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q5 : Sound J_q5 F_q5 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (4, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((43/8), (1269/256)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor4 : Sound J_gammaFactor4 F_gammaFactor4 c := by
  apply sound_round (sound_add (A_base hcre) (A_q5 hcre) S_base S_q5)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor4, J_base, J_q5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((352256/3503737), (-324864/3503737)), 0, by norm_num⟩
  | 1 => ⟨((-9273835520/12276172965169), (114435293184/12276172965169)), 0, by norm_num⟩
  | 2 => ⟨((-3467225851/8796093022208), (-2214911573/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((6074522547/140737488355328), (495533681/70368744177664)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-2810426835/1125899906842624), (1854344967/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((884951791/18014398509481984), (-3576091799/18014398509481984)), (3/9007199254740992), by norm_num⟩
  | 6 => ⟨((1940816695/288230376151711744), (1766329803/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 7 => ⟨((-4181360087/4611686018427387904), (-350425313/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 8 => ⟨((2201388351/36893488147419103232), (-123384787/4611686018427387904)), (13/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-2076804515/1180591620717411303424), (2426794197/590295810358705651712)), (41/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-482450189/4722366482869645213696), (-5444209209/18889465931478580854784)), (1/295147905179352825856), by norm_num⟩
  | 11 => ⟨((5590400137/302231454903657293676544), (1473663767/151115727451828646838272)), (25/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-3341269739/2417851639229258349412352), (1776174279/4835703278458516698824704)), (39/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (1269/256)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (1269/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (1269/256)))⁻¹=value ((352256/3503737), (-324864/3503737)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((352256/3503737), (-324864/3503737))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1175904467/35184372088832), (2063990905/17592186044416)), (3/35184372088832), by norm_num⟩
  | 1 => ⟨((-1685095459/35184372088832), (-468443305/35184372088832)), (3/70368744177664), by norm_num⟩
  | 2 => ⟨((618048383/70368744177664), (-1172195289/140737488355328)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((1151640769/2251799813685248), (2505149011/1125899906842624)), (7/2251799813685248), by norm_num⟩
  | 4 => ⟨((-3163803249/9007199254740992), (-1951724311/18014398509481984)), (11/18014398509481984), by norm_num⟩
  | 5 => ⟨((1392718329/36028797018963968), (-654362435/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 6 => ⟨((493207039/288230376151711744), (3947476933/576460752303423488)), (3/144115188075855872), by norm_num⟩
  | 7 => ⟨((-3933685491/4611686018427387904), (-516248595/2305843009213693952)), (15/4611686018427387904), by norm_num⟩
  | 8 => ⟨((1317388275/18446744073709551616), (-2826611687/36893488147419103232)), (19/36893488147419103232), by norm_num⟩
  | 9 => ⟨((144674895/36893488147419103232), (3325242949/295147905179352825856)), (23/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-3065244833/2361183241434822606848), (-879298929/4722366482869645213696)), (13/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((3033657141/37778931862957161709568), (-4325922819/37778931862957161709568)), (29/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((2098789319/302231454903657293676544), (3855143251/302231454903657293676544)), (1/4722366482869645213696), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct4 : Sound J_gammaProduct4 F_gammaProduct4 c := by
  apply sound_round (sound_mul (A_gammaProduct3 hcre) (A_gammaInverse4 hcre) S_gammaProduct3 S_gammaInverse4)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct4, J_gammaProduct3, J_gammaInverse4, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(5, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q6 : Sound J_q6 F_q6 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (5, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((51/8), (1269/256)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor5 : Sound J_gammaFactor5 F_gammaFactor5 c := by
  apply sound_round (sound_add (A_base hcre) (A_q6 hcre) S_base S_q6)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor5, J_base, J_q6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((139264/1424595), (-36096/474865)), 0, by norm_num⟩
  | 1 => ⟨((-3834085376/2029470914025), (1675624448/225496768225)), 0, by norm_num⟩
  | 2 => ⟨((-549550058110976/2891174116765444875), (-46580979728384/107080522843164625)), 0, by norm_num⟩
  | 3 => ⟨((908599417/35184372088832), (1975718699/140737488355328)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-4043745111/2251799813685248), (664975889/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 5 => ⟨((2758056627/36028797018963968), (-2979071373/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 6 => ⟨((-345363095/576460752303423488), (1001746927/144115188075855872)), (3/288230376151711744), by norm_num⟩
  | 7 => ⟨((-270822261/1152921504606846976), (-3343702961/9223372036854775808)), (9/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1863853901/73786976294838206464), (648726245/73786976294838206464)), (7/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-3704261405/2361183241434822606848), (1252159941/2361183241434822606848)), (5/590295810358705651712), by norm_num⟩
  | 10 => ⟨((2135491783/37778931862957161709568), (-403979981/4722366482869645213696)), (29/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((590453801/1208925819614629174706176), (3826081539/604462909807314587353088)), (41/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-639386207/2417851639229258349412352), (-2812678067/9671406556917033397649408)), (29/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (1269/256)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (1269/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (1269/256)))⁻¹=value ((139264/1424595), (-36096/474865)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((139264/1424595), (-36096/474865))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3429870547/281474976710656), (2513235921/281474976710656)), (5/281474976710656), by norm_num⟩
  | 1 => ⟨((-3731733963/562949953421312), (1331763619/562949953421312)), (5/562949953421312), by norm_num⟩
  | 2 => ⟨((1034897571/2251799813685248), (-1041124371/562949953421312)), (7/2251799813685248), by norm_num⟩
  | 3 => ⟨((2404494797/9007199254740992), (2580553915/9007199254740992)), (7/9007199254740992), by norm_num⟩
  | 4 => ⟨((-4792544405/72057594037927936), (220693313/18014398509481984)), (11/72057594037927936), by norm_num⟩
  | 5 => ⟨((1096143761/288230376151711744), (-1385801125/144115188075855872)), (17/576460752303423488), by norm_num⟩
  | 6 => ⟨((500011759/576460752303423488), (665177297/576460752303423488)), (13/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-6886365649/36893488147419103232), (360021859/18446744073709551616)), (33/36893488147419103232), by norm_num⟩
  | 8 => ⟨((703872695/73786976294838206464), (-1547040947/73786976294838206464)), (11/73786976294838206464), by norm_num⟩
  | 9 => ⟨((463480239/295147905179352825856), (2586251805/1180591620717411303424)), (27/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-5687126523/18889465931478580854784), (624949607/18889465931478580854784)), (61/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((1904741047/151115727451828646838272), (-573438247/18889465931478580854784)), (69/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((660722197/302231454903657293676544), (810577043/302231454903657293676544)), (39/604462909807314587353088), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct5 : Sound J_gammaProduct5 F_gammaProduct5 c := by
  apply sound_round (sound_mul (A_gammaProduct4 hcre) (A_gammaInverse5 hcre) S_gammaProduct4 S_gammaInverse5)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct5, J_gammaProduct4, J_gammaInverse5, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(6, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q7 : Sound J_q7 F_q7 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (6, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((59/8), (1269/256)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor6 : Sound J_gammaFactor6 F_gammaFactor6 c := by
  apply sound_round (sound_add (A_base hcre) (A_q7 hcre) S_base S_q7)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor6, J_base, J_q7, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((483328/5174905), (-324864/5174905)), 0, by norm_num⟩
  | 1 => ⟨((-64034668544/26779641759025), (157015867392/26779641759025)), 0, by norm_num⟩
  | 2 => ⟨((-636594865/8796093022208), (-6137287427/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((4033545719/281474976710656), (3946289795/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-624462299/562949953421312), (-922913263/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 5 => ⟨((4196223439/72057594037927936), (-1819322659/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((-2221675329/1152921504606846976), (216673689/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 7 => ⟨((-162117163/36893488147419103232), (-3706091155/18446744073709551616)), (21/36893488147419103232), by norm_num⟩
  | 8 => ⟨((480454609/73786976294838206464), (2728435959/295147905179352825856)), (7/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-5612437037/9444732965739290427392), (-536744053/2361183241434822606848)), (9/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((2635892445/75557863725914323419136), (-607226627/75557863725914323419136)), (23/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-416136935/302231454903657293676544), (3554990693/2417851639229258349412352)), (59/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((175522667/9671406556917033397649408), (-4328164193/38685626227668133590597632)), (75/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (1269/256)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (1269/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (1269/256)))⁻¹=value ((483328/5174905), (-324864/5174905)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((483328/5174905), (-324864/5174905))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7649879087/4503599627370496), (310655599/4503599627370496)), (13/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1243234073/2251799813685248), (96713057/140737488355328)), (1/562949953421312), by norm_num⟩
  | 2 => ⟨((-1242309403/18014398509481984), (-2260843999/9007199254740992)), (11/18014398509481984), by norm_num⟩
  | 3 => ⟨((973093369/18014398509481984), (704623075/36028797018963968)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((-618203207/72057594037927936), (439674955/72057594037927936)), (19/576460752303423488), by norm_num⟩
  | 5 => ⟨((-181417395/4611686018427387904), (-3899385957/2305843009213693952)), (15/2305843009213693952), by norm_num⟩
  | 6 => ⟨((480463593/2305843009213693952), (2417604471/18446744073709551616)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-4434958147/147573952589676412928), (2060201101/147573952589676412928)), (31/147573952589676412928), by norm_num⟩
  | 8 => ⟨((637498209/1180591620717411303424), (-2451088685/590295810358705651712)), (21/590295810358705651712), by norm_num⟩
  | 9 => ⟨((3676886237/9444732965739290427392), (748213015/2361183241434822606848)), (13/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-2046466871/37778931862957161709568), (366684429/18889465931478580854784)), (61/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((180107333/151115727451828646838272), (-3767886845/604462909807314587353088)), (35/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((2478529347/4835703278458516698824704), (2136221375/4835703278458516698824704)), (5/302231454903657293676544), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct6 : Sound J_gammaProduct6 F_gammaProduct6 c := by
  apply sound_round (sound_mul (A_gammaProduct5 hcre) (A_gammaInverse6 hcre) S_gammaProduct5 S_gammaInverse6)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct6, J_gammaProduct5, J_gammaInverse6, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(7, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q8 : Sound J_q8 F_q8 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (7, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((67/8), (1269/256)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor7 : Sound J_gammaFactor7 F_gammaFactor7 c := by
  apply sound_round (sound_add (A_base hcre) (A_q8 hcre) S_base S_q8)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor7, J_base, J_q8, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((548864/6207097), (-324864/6207097)), 0, by norm_num⟩
  | 1 => ⟨((-97857536000/38528053167409), (178306154496/38528053167409)), 0, by norm_num⟩
  | 2 => ⟨((-155023771/17592186044416), (-4768892931/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((2106399949/281474976710656), (3308615293/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-2875388737/4503599627370496), (-182321351/562949953421312)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((5289518139/144115188075855872), (-86064889/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 6 => ⟨((-3597673499/2305843009213693952), (2458251511/2305843009213693952)), (5/1152921504606846976), by norm_num⟩
  | 7 => ⟨((757865423/18446744073709551616), (-1622658941/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 8 => ⟨((573168045/1180591620717411303424), (5860761099/1180591620717411303424)), (7/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-714840319/4722366482869645213696), (-488240979/2361183241434822606848)), (1/590295810358705651712), by norm_num⟩
  | 10 => ⟨((3658129791/302231454903657293676544), (782922923/151115727451828646838272)), (37/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-6486775237/9671406556917033397649408), (847953913/9671406556917033397649408)), (21/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((4233718537/154742504910672534362390528), (-414482185/19342813113834066795298816)), (95/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (1269/256)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (1269/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (1269/256)))⁻¹=value ((548864/6207097), (-324864/6207097)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((548864/6207097), (-324864/6207097))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((692701283/4503599627370496), (-1491623311/18014398509481984)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1260145963/72057594037927936), (3507278491/36028797018963968)), (21/72057594037927936), by norm_num⟩
  | 2 => ⟨((-3027738853/144115188075855872), (-1682356111/72057594037927936)), (1/9007199254740992), by norm_num⟩
  | 3 => ⟨((16528055/2251799813685248), (-354711421/576460752303423488)), (9/288230376151711744), by norm_num⟩
  | 4 => ⟨((-431015439/576460752303423488), (1392552203/1152921504606846976)), (15/2305843009213693952), by norm_num⟩
  | 5 => ⟨((-417525043/4611686018427387904), (-2033239793/9223372036854775808)), (3/2305843009213693952), by norm_num⟩
  | 6 => ⟨((5173331569/147573952589676412928), (1189538849/147573952589676412928)), (37/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-2176766757/590295810358705651712), (497075449/147573952589676412928)), (51/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-447113939/4722366482869645213696), (-6052670781/9444732965739290427392)), (17/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((5437559677/75557863725914323419136), (2531265237/75557863725914323419136)), (43/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-4734416177/604462909807314587353088), (2994327131/604462909807314587353088)), (13/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-10138273/2417851639229258349412352), (-5017300515/4835703278458516698824704)), (121/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((3705296235/38685626227668133590597632), (560946383/9671406556917033397649408)), (139/38685626227668133590597632), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct7 : Sound J_gammaProduct7 F_gammaProduct7 c := by
  apply sound_round (sound_mul (A_gammaProduct6 hcre) (A_gammaInverse7 hcre) S_gammaProduct6 S_gammaInverse7)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct7, J_gammaProduct6, J_gammaInverse7, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(8, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q9 : Sound J_q9 F_q9 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (8, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((75/8), (1269/256)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor8 : Sound J_gammaFactor8 F_gammaFactor8 c := by
  apply sound_round (sound_add (A_base hcre) (A_q9 hcre) S_base S_q9)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor8, J_base, J_q9, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((204800/2456787), (-36096/818929)), 0, by norm_num⟩
  | 1 => ⟨((-15108374528/6035802363369), (2464153600/670644707041)), 0, by norm_num⟩
  | 2 => ⟨((346325359001600/14828680780894235403), (-114407103266816/549210399292379089)), 0, by norm_num⟩
  | 3 => ⟨((1018219017/281474976710656), (2588795813/281474976710656)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-198986227/562949953421312), (-341848505/1125899906842624)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((1543776967/72057594037927936), (1402283303/288230376151711744)), (5/288230376151711744), by norm_num⟩
  | 6 => ⟨((-2306284665/2305843009213693952), (310570237/1152921504606846976)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((2638014869/73786976294838206464), (-306866263/9223372036854775808)), (7/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-893609333/1180591620717411303424), (5134739247/2361183241434822606848)), (15/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-618721153/37778931862957161709568), (-1013623837/9444732965739290427392)), (17/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1842299831/604462909807314587353088), (2485719995/604462909807314587353088)), (9/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-2105112579/9671406556917033397649408), (-1008069453/9671406556917033397649408)), (37/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((7037339499/618970019642690137449562112), (-140058097/309485009821345068724781056)), (19/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (1269/256)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (1269/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (1269/256)))⁻¹=value ((204800/2456787), (-36096/818929)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((204800/2456787), (-36096/818929))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((330460871/36028797018963968), (-985888317/72057594037927936)), (17/288230376151711744), by norm_num⟩
  | 1 => ⟨((3098661/1125899906842624), (5567531467/576460752303423488)), (3/72057594037927936), by norm_num⟩
  | 2 => ⟨((-3583267901/1152921504606846976), (-1570438217/1152921504606846976)), (19/1152921504606846976), by norm_num⟩
  | 3 => ⟨((3432493967/4611686018427387904), (-1782591445/4611686018427387904)), (23/4611686018427387904), by norm_num⟩
  | 4 => ⟨((-582809457/18446744073709551616), (1532534551/9223372036854775808)), (5/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-2893740059/147573952589676412928), (-3247760341/147573952589676412928)), (33/147573952589676412928), by norm_num⟩
  | 6 => ⟨((5406986625/1180591620717411303424), (-114539987/295147905179352825856)), (25/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-1611623689/4722366482869645213696), (5293142027/9444732965739290427392)), (9/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-323634419/9444732965739290427392), (-3027189703/37778931862957161709568)), (3/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((6449553849/604462909807314587353088), (1333013285/604462909807314587353088)), (125/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-2243528189/2417851639229258349412352), (1089734469/1208925819614629174706176)), (77/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-527521245/19342813113834066795298816), (-2791694775/19342813113834066795298816)), (181/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((2299203165/154742504910672534362390528), (1865535849/309485009821345068724781056)), (105/154742504910672534362390528), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct8 : Sound J_gammaProduct8 F_gammaProduct8 c := by
  apply sound_round (sound_mul (A_gammaProduct7 hcre) (A_gammaInverse8 hcre) S_gammaProduct7 S_gammaInverse8)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct8, J_gammaProduct7, J_gammaInverse8, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(9, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q10 : Sound J_q10 F_q10 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (9, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((83/8), (1269/256)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor9 : Sound J_gammaFactor9 F_gammaFactor9 c := by
  apply sound_round (sound_add (A_base hcre) (A_q10 hcre) S_base S_q10)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor9, J_base, J_q10, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((679936/8664697), (-324864/8664697)), 0, by norm_num⟩
  | 1 => ⟨((-178388172800/75076974101809), (220886728704/75076974101809)), 0, by norm_num⟩
  | 2 => ⟨((1339573435/35184372088832), (-703601511/4398046511104)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((211842193/140737488355328), (983856945/140737488355328)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-3424720507/18014398509481984), (-4432809437/18014398509481984)), (5/18014398509481984), by norm_num⟩
  | 5 => ⟨((3479545533/288230376151711744), (877795641/144115188075855872)), (5/288230376151711744), by norm_num⟩
  | 6 => ⟨((-5421903021/9223372036854775808), (-29226935/2305843009213693952)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1719402845/73786976294838206464), (-1552867985/147573952589676412928)), (11/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-3386056095/4722366482869645213696), (4012595049/4722366482869645213696)), (21/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((115267015/9444732965739290427392), (-110457283/2361183241434822606848)), (5/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((481292295/1208925819614629174706176), (4991090795/2417851639229258349412352)), (19/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-525332077/9671406556917033397649408), (-711141597/9671406556917033397649408)), (9/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((4344740003/1237940039285380274899124224), (2310944601/1237940039285380274899124224)), (17/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (1269/256)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (1269/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (1269/256)))⁻¹=value ((679936/8664697), (-324864/8664697)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((679936/8664697), (-324864/8664697))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((476803243/2305843009213693952), (-6537244283/4611686018427387904)), (33/4611686018427387904), by norm_num⟩
  | 1 => ⟨((2751049751/4611686018427387904), (3293670775/4611686018427387904)), (25/4611686018427387904), by norm_num⟩
  | 2 => ⟨((-6119799989/18446744073709551616), (-33212367/4611686018427387904)), (5/2305843009213693952), by norm_num⟩
  | 3 => ⟨((16448247/288230376151711744), (-2367642873/36893488147419103232)), (13/18446744073709551616), by norm_num⟩
  | 4 => ⟨((801168775/295147905179352825856), (5256892383/295147905179352825856)), (47/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-827673051/295147905179352825856), (-1935871111/1180591620717411303424)), (5/147573952589676412928), by norm_num⟩
  | 6 => ⟨((4586465755/9444732965739290427392), (-449567451/2361183241434822606848)), (31/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((-1605785561/75557863725914323419136), (5541989845/75557863725914323419136)), (89/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((-471053545/75557863725914323419136), (-2502302529/302231454903657293676544)), (61/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((6382113475/4835703278458516698824704), (-91933439/4835703278458516698824704)), (5/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-3498915743/38685626227668133590597632), (1267071601/9671406556917033397649408)), (25/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-249857109/38685626227668133590597632), (-1326069061/77371252455336267181195264)), (239/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((4869228795/2475880078570760549798248448), (1157057587/2475880078570760549798248448)), (35/309485009821345068724781056), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct9 : Sound J_gammaProduct9 F_gammaProduct9 c := by
  apply sound_round (sound_mul (A_gammaProduct8 hcre) (A_gammaInverse9 hcre) S_gammaProduct8 S_gammaInverse9)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct9, J_gammaProduct8, J_gammaInverse9, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(10, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q11 : Sound J_q11 F_q11 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (10, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((91/8), (1269/256)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor10 : Sound J_gammaFactor10 F_gammaFactor10 c := by
  apply sound_round (sound_add (A_base hcre) (A_q11 hcre) S_base S_q11)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor10, J_base, J_q11, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((745472/10090105), (-324864/10090105)), 0, by norm_num⟩
  | 1 => ⟨((-225095942144/101810218911025), (242177015808/101810218911025)), 0, by norm_num⟩
  | 2 => ⟨((381581707/8796093022208), (-2171989619/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((433483787/1125899906842624), (740163463/140737488355328)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-890682399/9007199254740992), (-1694073875/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((1925565539/288230376151711744), (1543744479/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 6 => ⟨((-6142928185/18446744073709551616), (-416464535/4611686018427387904)), (15/18446744073709551616), by norm_num⟩
  | 7 => ⟨((4059865223/295147905179352825856), (-597627575/295147905179352825856)), (7/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2245660011/4722366482869645213696), (699464943/2361183241434822606848)), (25/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((1933957597/151115727451828646838272), (-1405255667/75557863725914323419136)), (11/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-838329883/4835703278458516698824704), (4318576595/4835703278458516698824704)), (19/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-1233681691/154742504910672534362390528), (-5536863897/154742504910672534362390528)), (65/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((538825495/618970019642690137449562112), (1477407117/1237940039285380274899124224)), (7/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (1269/256)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (1269/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (1269/256)))⁻¹=value ((745472/10090105), (-324864/10090105)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((745472/10090105), (-324864/10090105))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1120169427/36893488147419103232), (-1027367899/9223372036854775808)), (29/36893488147419103232), by norm_num⟩
  | 1 => ⟨((5163800009/73786976294838206464), (2743831735/73786976294838206464)), (23/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-4121188119/147573952589676412928), (1461295017/147573952589676412928)), (39/147573952589676412928), by norm_num⟩
  | 3 => ⟨((445991459/147573952589676412928), (-4364663771/590295810358705651712)), (51/590295810358705651712), by norm_num⟩
  | 4 => ⟨((1844999919/2361183241434822606848), (1830274477/1180591620717411303424)), (25/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-740937237/2361183241434822606848), (-713553463/9444732965739290427392)), (85/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((3215418291/75557863725914323419136), (-2415021849/75557863725914323419136)), (17/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-160870879/604462909807314587353088), (4817006429/604462909807314587353088)), (99/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((-255574519/302231454903657293676544), (-1715807127/2417851639229258349412352)), (137/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((2699442347/19342813113834066795298816), (-1210676979/38685626227668133590597632)), (91/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((-137637117/19342813113834066795298816), (4949920263/309485009821345068724781056)), (231/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-2534323471/2475880078570760549798248448), (-4366696295/2475880078570760549798248448)), (35/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((4487314961/19807040628566084398385987584), (393800913/19807040628566084398385987584)), (331/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct10 : Sound J_gammaProduct10 F_gammaProduct10 c := by
  apply sound_round (sound_mul (A_gammaProduct9 hcre) (A_gammaInverse10 hcre) S_gammaProduct9 S_gammaInverse10)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct10, J_gammaProduct9, J_gammaInverse10, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(11, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q12 : Sound J_q12 F_q12 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (11, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((99/8), (1269/256)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor11 : Sound J_gammaFactor11 F_gammaFactor11 c := by
  apply sound_round (sound_add (A_base hcre) (A_q12 hcre) S_base S_q12)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor11, J_base, J_q12, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((90112/1294065), (-12032/431355)), 0, by norm_num⟩
  | 1 => ⟨((-3408625664/1674604224225), (1084227584/558201408075)), 0, by norm_num⟩
  | 2 => ⟨((94874619609088/2167046715421724625), (-23119083339776/240782968380191625)), 0, by norm_num⟩
  | 3 => ⟨((-104265495/562949953421312), (2225699043/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((-438576179/9007199254740992), (-2526312165/18014398509481984)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((2104768675/576460752303423488), (302904955/72057594037927936)), (3/576460752303423488), by norm_num⟩
  | 6 => ⟨((-3426525535/18446744073709551616), (-1760520411/18446744073709551616)), (5/18446744073709551616), by norm_num⟩
  | 7 => ⟨((4603401699/590295810358705651712), (432252161/590295810358705651712)), (9/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-5321826127/18889465931478580854784), (1572882735/18889465931478580854784)), (15/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((2613690167/302231454903657293676544), (-2063774199/302231454903657293676544)), (13/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-995503965/4835703278458516698824704), (3465848543/9671406556917033397649408)), (11/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((671501819/309485009821345068724781056), (-4750079369/309485009821345068724781056)), (35/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((1371782629/9903520314283042199192993792), (2796012143/4951760157141521099596496896)), (7/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (1269/256)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (1269/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (1269/256)))⁻¹=value ((90112/1294065), (-12032/431355)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((90112/1294065), (-12032/431355))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3082085603/590295810358705651712), (-4078670779/590295810358705651712)), (23/295147905179352825856), by norm_num⟩
  | 1 => ⟨((1826558895/295147905179352825856), (950524481/1180591620717411303424)), (19/295147905179352825856), by norm_num⟩
  | 2 => ⟨((-2237381899/1180591620717411303424), (3604989073/2361183241434822606848)), (17/590295810358705651712), by norm_num⟩
  | 3 => ⟨((1803805/36893488147419103232), (-6410798143/9444732965739290427392)), (23/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((995659123/9444732965739290427392), (4173602101/37778931862957161709568)), (47/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((-4408031821/151115727451828646838272), (84310783/75557863725914323419136)), (41/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((3713663771/1208925819614629174706176), (-4664531977/1208925819614629174706176)), (133/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((728307073/4835703278458516698824704), (223509467/302231454903657293676544)), (99/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((-3645627261/38685626227668133590597632), (-239252845/4835703278458516698824704)), (139/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((3966449079/309485009821345068724781056), (-876409569/154742504910672534362390528)), (187/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((-515736759/1237940039285380274899124224), (4179691727/2475880078570760549798248448)), (15/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-2565275973/19807040628566084398385987584), (-3146358311/19807040628566084398385987584)), (147/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((7306490633/316912650057057350374175801344), (-383581519/316912650057057350374175801344)), (701/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-241927589/137438953472), (-2119069667/549755813888)), (147/274877906944), by norm_num⟩
  | 1 => ⟨((1394720253/1099511627776), (-4771886343/1099511627776)), (621/549755813888), by norm_num⟩
  | 2 => ⟨((4230796493/2199023255552), (-705291263/549755813888)), (691/549755813888), by norm_num⟩
  | 3 => ⟨((6584549461/8796093022208), (143793495/2199023255552)), (4203/4398046511104), by norm_num⟩
  | 4 => ⟨((285839719/2199023255552), (1012822033/8796093022208)), (4873/8796093022208), by norm_num⟩
  | 5 => ⟨((1137924171/140737488355328), (4130966583/140737488355328)), (2291/8796093022208), by norm_num⟩
  | 6 => ⟨((-1033761329/1125899906842624), (4724217161/1125899906842624)), (116357/1125899906842624), by norm_num⟩
  | 7 => ⟨((-2646794041/9007199254740992), (1982052499/4503599627370496)), (80157/2251799813685248), by norm_num⟩
  | 8 => ⟨((-217208955/4503599627370496), (2767938809/72057594037927936)), (783051/72057594037927936), by norm_num⟩
  | 9 => ⟨((-3641346955/576460752303423488), (1335355477/576460752303423488)), (1722721/576460752303423488), by norm_num⟩
  | 10 => ⟨((-5986648545/9223372036854775808), (86353907/4611686018427387904)), (3458109/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-4052560927/73786976294838206464), (-931482139/73786976294838206464)), (6399861/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-1305052809/295147905179352825856), (-1173220365/590295810358705651712)), (44047235/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-241927589/137438953472), (-2119069667/549755813888)), (589/1099511627776), by norm_num⟩
  | 1 => ⟨((1394720253/1099511627776), (-4771886343/1099511627776)), (1243/1099511627776), by norm_num⟩
  | 2 => ⟨((4230796493/2199023255552), (-705291263/549755813888)), (2765/2199023255552), by norm_num⟩
  | 3 => ⟨((6584549461/8796093022208), (143793495/2199023255552)), (8407/8796093022208), by norm_num⟩
  | 4 => ⟨((285839719/2199023255552), (1012822033/8796093022208)), (9747/17592186044416), by norm_num⟩
  | 5 => ⟨((1137924171/140737488355328), (4130966583/140737488355328)), (18331/70368744177664), by norm_num⟩
  | 6 => ⟨((-1033761329/1125899906842624), (4724217161/1125899906842624)), (116403/1125899906842624), by norm_num⟩
  | 7 => ⟨((-2646794041/9007199254740992), (1982052499/4503599627370496)), (320989/9007199254740992), by norm_num⟩
  | 8 => ⟨((-217208955/4503599627370496), (2767938809/72057594037927936)), (392967/36028797018963968), by norm_num⟩
  | 9 => ⟨((-3641346955/576460752303423488), (1335355477/576460752303423488)), (436445/144115188075855872), by norm_num⟩
  | 10 => ⟨((-5986648545/9223372036854775808), (86353907/4611686018427387904)), (7285153/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-4052560927/73786976294838206464), (-931482139/73786976294838206464)), (7875601/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-1305052809/295147905179352825856), (-1173220365/590295810358705651712)), (22817725/295147905179352825856), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile022Gamma

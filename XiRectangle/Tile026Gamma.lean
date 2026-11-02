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
namespace Reinmann.XiRectangle.Tile026Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨26,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (7191/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (7191/640))
  have he : value ((7/8), (7191/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/16), (7191/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((23/16), (7191/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((215/16), (7191/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((22016000/347550481), (-9204480/347550481)), 0, by norm_num⟩
  | 1 => ⟨((-199990901964800/120791336843331361), (202645831680000/120791336843331361)), 0, by norm_num⟩
  | 2 => ⟨((531722455/17592186044416), (-2640964981/35184372088832)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((82488733/2251799813685248), (3127347359/1125899906842624)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-1366990699/36028797018963968), (-394026481/4503599627370496)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((1360611281/576460752303423488), (2615638791/1152921504606846976)), (5/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-3866421045/36893488147419103232), (-46811135/1152921504606846976)), (1/4611686018427387904), by norm_num⟩
  | 7 => ⟨((4553515653/1180591620717411303424), (-120127071/1180591620717411303424)), (3/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-1141065817/9444732965739290427392), (512817145/9444732965739290427392)), (9/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((1878425471/604462909807314587353088), (-1003277553/302231454903657293676544)), (27/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-1053596301/19342813113834066795298816), (1414844755/9671406556917033397649408)), (5/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-262393591/1237940039285380274899124224), (-6628907559/1237940039285380274899124224)), (29/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((768722911/9903520314283042199192993792), (3303734913/19807040628566084398385987584)), (43/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((215/16), (7191/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((215/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((215/16), (7191/1280)))⁻¹=value ((22016000/347550481), (-9204480/347550481)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((22016000/347550481), (-9204480/347550481))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5752238713/2147483648), (106299357/268435456)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((11008000/347550481), (-4602240/347550481)), 0, by norm_num⟩
  | 2 => ⟨((-49997725491200/120791336843331361), (50661457920000/120791336843331361)), 0, by norm_num⟩
  | 3 => ⟨((1417926547/281474976710656), (-3521286641/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((82488733/18014398509481984), (3127347359/9007199254740992)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((-1093592559/288230376151711744), (-5043538957/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((3628296749/18446744073709551616), (871879597/4611686018427387904)), (7/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-4418766909/590295810358705651712), (-6687305/2305843009213693952)), (5/295147905179352825856), by norm_num⟩
  | 8 => ⟨((4553515653/18889465931478580854784), (-120127071/18889465931478580854784)), (3/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-4057122905/604462909807314587353088), (1823349849/604462909807314587353088)), (17/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((1502740377/9671406556917033397649408), (-1605244085/9671406556917033397649408)), (23/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-1532503711/618970019642690137449562112), (4115912015/618970019642690137449562112)), (15/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-174929061/19807040628566084398385987584), (-2209635853/9903520314283042199192993792)), (39/19807040628566084398385987584), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-6959/276736), (153/20480)), 0, by norm_num⟩
  | 45 => ⟨((96411157313/4080638361600), (-604503/60293120)), 0, by norm_num⟩
  | 44 => ⟨((-10567571249009/459643105050624), (1956232848721/197568495616000)), 0, by norm_num⟩
  | 43 => ⟨((3224493425/137438953472), (-663720207/68719476736)), (1/137438953472), by norm_num⟩
  | 42 => ⟨((-3322683887/137438953472), (1344791835/137438953472)), (1/68719476736), by norm_num⟩
  | 41 => ⟨((1706065391/68719476736), (-345511927/34359738368)), (1/68719476736), by norm_num⟩
  | 40 => ⟨((-3497179105/137438953472), (1419421335/137438953472)), (1/68719476736), by norm_num⟩
  | 39 => ⟨((3585779277/137438953472), (-1455269381/137438953472)), (1/68719476736), by norm_num⟩
  | 38 => ⟨((-920030227/34359738368), (186515029/17179869184)), (1/68719476736), by norm_num⟩
  | 37 => ⟨((472505359/17179869184), (-1531147647/137438953472)), (1/68719476736), by norm_num⟩
  | 36 => ⟨((-971381243/34359738368), (393120759/34359738368)), (1/68719476736), by norm_num⟩
  | 35 => ⟨((999245829/34359738368), (-1616140353/137438953472)), (1/68719476736), by norm_num⟩
  | 34 => ⟨((-4114999895/137438953472), (1662267939/137438953472)), (1/68719476736), by norm_num⟩
  | 33 => ⟨((1060049785/34359738368), (-1711093901/137438953472)), (1/68719476736), by norm_num⟩
  | 32 => ⟨((-2186628593/68719476736), (220359253/17179869184)), (1/68719476736), by norm_num⟩
  | 31 => ⟨((4514933401/137438953472), (-1817886681/137438953472)), (1/68719476736), by norm_num⟩
  | 30 => ⟨((-4666091341/137438953472), (938221543/68719476736)), (1/68719476736), by norm_num⟩
  | 29 => ⟨((4827715535/137438953472), (-1938896297/137438953472)), (1/68719476736), by norm_num⟩
  | 28 => ⟨((-5000931693/137438953472), (501412137/34359738368)), (1/68719476736), by norm_num⟩
  | 27 => ⟨((5187032647/137438953472), (-519289881/34359738368)), (1/68719476736), by norm_num⟩
  | 26 => ⟨((-673438839/17179869184), (2153956787/137438953472)), (1/68719476736), by norm_num⟩
  | 25 => ⟨((5604097781/137438953472), (-1118324409/68719476736)), (1/68719476736), by norm_num⟩
  | 24 => ⟨((-5838815399/137438953472), (2325941175/137438953472)), (1/68719476736), by norm_num⟩
  | 23 => ⟨((6094037899/137438953472), (-2422656669/137438953472)), (1/68719476736), by norm_num⟩
  | 22 => ⟨((-796571603/17179869184), (1263880381/68719476736)), (1/68719476736), by norm_num⟩
  | 21 => ⟨((834720547/17179869184), (-1321196935/68719476736)), (1/34359738368), by norm_num⟩
  | 20 => ⟨((-1753406997/34359738368), (691978217/34359738368)), (1/34359738368), by norm_num⟩
  | 19 => ⟨((230782109/4294967296), (-1452972487/68719476736)), (1/34359738368), by norm_num⟩
  | 18 => ⟨((-3898955735/68719476736), (1529229301/68719476736)), (1/34359738368), by norm_num⟩
  | 17 => ⟨((4129816639/68719476736), (-100870553/4294967296)), (1/34359738368), by norm_num⟩
  | 16 => ⟨((-1097423907/17179869184), (1708554593/68719476736)), (1/34359738368), by norm_num⟩
  | 15 => ⟨((4684422745/68719476736), (-226869875/8589934592)), (1/34359738368), by norm_num⟩
  | 14 => ⟨((-5021499699/68719476736), (967742907/34359738368)), (1/34359738368), by norm_num⟩
  | 13 => ⟨((169085765/2147483648), (-259143053/8589934592)), (1/34359738368), by norm_num⟩
  | 12 => ⟨((-1466314705/17179869184), (557966031/17179869184)), (1/34359738368), by norm_num⟩
  | 11 => ⟨((1600731021/17179869184), (-302109317/8589934592)), (1/34359738368), by norm_num⟩
  | 10 => ⟨((-440549727/4294967296), (20588217/536870912)), (1/17179869184), by norm_num⟩
  | 9 => ⟨((1959773603/17179869184), (-362131631/8589934592)), (1/17179869184), by norm_num⟩
  | 8 => ⟨((-551762029/4294967296), (1608233933/34359738368)), (1/17179869184), by norm_num⟩
  | 7 => ⟨((2525395577/17179869184), (-903729817/17179869184)), (1/17179869184), by norm_num⟩
  | 6 => ⟨((-2950449049/17179869184), (128932821/2147483648)), (1/17179869184), by norm_num⟩
  | 5 => ⟨((3546336413/17179869184), (-1201165837/17179869184)), (1/8589934592), by norm_num⟩
  | 4 => ⟨((-4441178229/17179869184), (1437574663/17179869184)), (1/8589934592), by norm_num⟩
  | 3 => ⟨((1483284979/4294967296), (-1789636599/17179869184)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((-17405823/33554432), (592470913/4294967296)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((4443756475/4294967296), (-877170877/4294967296)), (1/4294967296), by norm_num⟩
  | 0 => ⟨((-201850231/2147483648), (6803158845/17179869184)), (3/17179869184), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-41/256), (7191/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-41/256), (7191/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-41/256), (7191/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((5752238713/2147483648), (106299357/268435456)), (1/1073741824), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((215/16), (7191/1280))) (z:=((-41/256), (7191/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((5752238713/2147483648), (106299357/268435456))) (r:=(1/1073741824)) (by norm_num) ?_ hs
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
  | 0 => ⟨((207/16), (7191/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((4352631039/134217728), (2707367549/134217728)), (3/134217728), by norm_num⟩
  | 1 => ⟨((978963113/536870912), (439415845/2147483648)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((981457786457600/120791336843331361), (-425208410379360/120791336843331361)), 0, by norm_num⟩
  | 3 => ⟨((-628965513/8796093022208), (167471519/2199023255552)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((1412771003/2251799813685248), (-3912205059/2251799813685248)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((42423641/18014398509481984), (5634198147/144115188075855872)), (41/144115188075855872), by norm_num⟩
  | 6 => ⟨((-238957563/576460752303423488), (-118696847/144115188075855872)), (57/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2625658287/147573952589676412928), (1103430705/73786976294838206464)), (75/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2778572913/4722366482869645213696), (-840959155/4722366482869645213696)), (3/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1265462549/75557863725914323419136), (-70327135/37778931862957161709568)), (255/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-3997068507/9671406556917033397649408), (70665685/302231454903657293676544)), (175/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((40139533/4835703278458516698824704), (-840969623/77371252455336267181195264)), (463/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-61121055/618970019642690137449562112), (3848759273/9903520314283042199192993792)), (603/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-215/16), (-7191/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2549080319/134217728), (1953336547/134217728)), (1/33554432), by norm_num⟩
  | 1 => ⟨((710527657/536870912), (439415845/2147483648)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((981457786457600/120791336843331361), (-425208410379360/120791336843331361)), 0, by norm_num⟩
  | 3 => ⟨((-628965513/8796093022208), (167471519/2199023255552)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((1412771003/2251799813685248), (-3912205059/2251799813685248)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((42423641/18014398509481984), (5634198147/144115188075855872)), (41/144115188075855872), by norm_num⟩
  | 6 => ⟨((-238957563/576460752303423488), (-118696847/144115188075855872)), (57/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2625658287/147573952589676412928), (1103430705/73786976294838206464)), (75/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2778572913/4722366482869645213696), (-840959155/4722366482869645213696)), (3/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1265462549/75557863725914323419136), (-70327135/37778931862957161709568)), (255/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-3997068507/9671406556917033397649408), (70665685/302231454903657293676544)), (175/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((40139533/4835703278458516698824704), (-840969623/77371252455336267181195264)), (463/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-61121055/618970019642690137449562112), (3848759273/9903520314283042199192993792)), (603/9903520314283042199192993792), by norm_num⟩
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
  | 0 => ⟨((2672418161/134217728), (1953336547/134217728)), (5/134217728), by norm_num⟩
  | 1 => ⟨((710527657/536870912), (439415845/2147483648)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((981457786457600/120791336843331361), (-425208410379360/120791336843331361)), 0, by norm_num⟩
  | 3 => ⟨((-628965513/8796093022208), (167471519/2199023255552)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((1412771003/2251799813685248), (-3912205059/2251799813685248)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((42423641/18014398509481984), (5634198147/144115188075855872)), (41/144115188075855872), by norm_num⟩
  | 6 => ⟨((-238957563/576460752303423488), (-118696847/144115188075855872)), (57/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2625658287/147573952589676412928), (1103430705/73786976294838206464)), (75/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2778572913/4722366482869645213696), (-840959155/4722366482869645213696)), (3/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1265462549/75557863725914323419136), (-70327135/37778931862957161709568)), (255/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-3997068507/9671406556917033397649408), (70665685/302231454903657293676544)), (175/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((40139533/4835703278458516698824704), (-840969623/77371252455336267181195264)), (463/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-61121055/618970019642690137449562112), (3848759273/9903520314283042199192993792)), (603/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((399981803929600/120791336843331361), (-405291663360000/120791336843331361)), 0, by norm_num⟩
  | 1 => ⟨((-531722455/4398046511104), (2640964981/8796093022208)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-61866549/281474976710656), (-2345510519/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((1366990699/4503599627370496), (394026481/562949953421312)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((-1700764101/72057594037927936), (-3269548489/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 5 => ⟨((5799631567/4611686018427387904), (140433405/288230376151711744)), (9/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-996081549/18446744073709551616), (105111187/73786976294838206464)), (15/147573952589676412928), by norm_num⟩
  | 7 => ⟨((1141065817/590295810358705651712), (-512817145/590295810358705651712)), (13/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-2113228655/37778931862957161709568), (1128687247/18889465931478580854784)), (11/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((82312211/75557863725914323419136), (-3537111887/1208925819614629174706176)), (1/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((90197797/19342813113834066795298816), (2278686973/19342813113834066795298816)), (25/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-576542183/309485009821345068724781056), (-4955602369/1237940039285380274899124224)), (19/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((1201765563/9903520314283042199192993792), (547824951/4951760157141521099596496896)), (29/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((531722455/4398046511104), (-2640964981/8796093022208)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((61866549/140737488355328), (2345510519/70368744177664)), (1/70368744177664), by norm_num⟩
  | 2 => ⟨((-64077689/70368744177664), (-4728317773/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 3 => ⟨((1700764101/18014398509481984), (3269548489/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((-3624769729/576460752303423488), (-702167025/288230376151711744)), (5/576460752303423488), by norm_num⟩
  | 5 => ⟨((2988244647/9223372036854775808), (-39416695/4611686018427387904)), (5/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-3993730359/295147905179352825856), (1794860007/295147905179352825856)), (5/147573952589676412928), by norm_num⟩
  | 7 => ⟨((2113228655/4722366482869645213696), (-1128687247/2361183241434822606848)), (9/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-740809899/75557863725914323419136), (3979250873/151115727451828646838272)), (15/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-56373623/1208925819614629174706176), (-5696717433/4835703278458516698824704)), (3/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((1585491003/77371252455336267181195264), (851744157/19342813113834066795298816)), (5/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-225331043/154742504910672534362390528), (-3286949705/2475880078570760549798248448)), (31/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((2944040899/39614081257132168796771975168), (2104359811/79228162514264337593543950336)), (3/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-82488733/281474976710656), (-3127347359/140737488355328)), (3/281474976710656), by norm_num⟩
  | 1 => ⟨((1366990699/1125899906842624), (394026481/140737488355328)), (3/1125899906842624), by norm_num⟩
  | 2 => ⟨((-1700764101/9007199254740992), (-1634774245/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((2416513153/144115188075855872), (1872445401/288230376151711744)), (3/144115188075855872), by norm_num⟩
  | 4 => ⟨((-4980407745/4611686018427387904), (16423623/576460752303423488)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((3993730359/73786976294838206464), (-1794860007/73786976294838206464)), (9/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-1232716715/590295810358705651712), (329200447/147573952589676412928)), (9/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((1975493065/37778931862957161709568), (-2652833915/18889465931478580854784)), (9/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((169120869/604462909807314587353088), (4272538075/604462909807314587353088)), (17/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-2642485005/19342813113834066795298816), (-5678294381/19342813113834066795298816)), (7/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((3304855297/309485009821345068724781056), (1506518615/154742504910672534362390528)), (3/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-2944040899/4951760157141521099596496896), (-2104359811/9903520314283042199192993792)), (5/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((535898937/19807040628566084398385987584), (-226359795/158456325028528675187087900672)), (1/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1366990699/2251799813685248), (-394026481/281474976710656)), (3/2251799813685248), by norm_num⟩
  | 1 => ⟨((1700764101/9007199254740992), (3269548489/18014398509481984)), (3/9007199254740992), by norm_num⟩
  | 2 => ⟨((-3624769729/144115188075855872), (-1404334051/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 3 => ⟨((2490203873/1152921504606846976), (-131388983/2305843009213693952)), (1/288230376151711744), by norm_num⟩
  | 4 => ⟨((-2496081475/18446744073709551616), (2243575009/36893488147419103232)), (11/36893488147419103232), by norm_num⟩
  | 5 => ⟨((1849075073/295147905179352825856), (-987601341/147573952589676412928)), (13/590295810358705651712), by norm_num⟩
  | 6 => ⟨((-1728556431/9444732965739290427392), (4642459351/9444732965739290427392)), (15/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-169120869/151115727451828646838272), (-2136269037/75557863725914323419136)), (1/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((1486397815/2417851639229258349412352), (3194040589/2417851639229258349412352)), (1/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-4131069121/77371252455336267181195264), (-3766296537/77371252455336267181195264)), (29/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((1012014059/309485009821345068724781056), (723373685/618970019642690137449562112)), (25/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-1607696811/9903520314283042199192993792), (84884923/9903520314283042199192993792)), (11/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((4249318073/633825300114114700748351602688), (-2046086911/633825300114114700748351602688)), (19/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1360611281/18014398509481984), (-2615638791/36028797018963968)), (5/36028797018963968), by norm_num⟩
  | 1 => ⟨((5799631567/288230376151711744), (2246934481/288230376151711744)), (11/288230376151711744), by norm_num⟩
  | 2 => ⟨((-2988244647/1152921504606846976), (39416695/576460752303423488)), (11/2305843009213693952), by norm_num⟩
  | 3 => ⟨((499216295/2305843009213693952), (-1794860007/18446744073709551616)), (5/9223372036854775808), by norm_num⟩
  | 4 => ⟨((-3698150147/295147905179352825856), (987601341/73786976294838206464)), (7/147573952589676412928), by norm_num⟩
  | 5 => ⟨((1037133859/2361183241434822606848), (-2785475611/2361183241434822606848)), (9/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((3699519/1180591620717411303424), (747694163/9444732965739290427392)), (11/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-297279563/151115727451828646838272), (-2555232471/604462909807314587353088)), (25/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((3717962209/19342813113834066795298816), (847416721/4835703278458516698824704)), (13/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-1012014059/77371252455336267181195264), (-723373685/154742504910672534362390528)), (13/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((442116623/618970019642690137449562112), (-373493661/9903520314283042199192993792)), (47/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((-637397711/19807040628566084398385987584), (2455304293/158456325028528675187087900672)), (11/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((2923861759/2535301200456458802993406410752), (-3293242491/2535301200456458802993406410752)), (39/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3866421045/576460752303423488), (-46811135/18014398509481984)), (1/72057594037927936), by norm_num⟩
  | 1 => ⟨((7968652393/4611686018427387904), (-105111187/2305843009213693952)), (19/4611686018427387904), by norm_num⟩
  | 2 => ⟨((-499216295/2305843009213693952), (1794860007/18446744073709551616)), (11/18446744073709551616), by norm_num⟩
  | 3 => ⟨((2465433431/147573952589676412928), (-329200447/18446744073709551616)), (11/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-108034777/147573952589676412928), (580307419/295147905179352825856)), (17/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((-3699519/590295810358705651712), (-5981553305/37778931862957161709568)), (23/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((1387304627/302231454903657293676544), (1490552275/151115727451828646838272)), (15/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-38728773/75557863725914323419136), (-1129888961/2417851639229258349412352)), (19/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((3036042177/77371252455336267181195264), (2170121055/154742504910672534362390528)), (5/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-5894888307/2475880078570760549798248448), (311244717/2475880078570760549798248448)), (21/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((4674249881/39614081257132168796771975168), (-2250695601/39614081257132168796771975168)), (41/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((-11421335/2475880078570760549798248448), (3293242491/633825300114114700748351602688)), (5/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((1175972679/10141204801825835211973625643008), (-1716297215/5070602400912917605986812821504)), (37/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4553515653/9223372036854775808), (120127071/9223372036854775808)), (3/2305843009213693952), by norm_num⟩
  | 1 => ⟨((1141065817/9223372036854775808), (-512817145/9223372036854775808)), (1/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-2113228655/147573952589676412928), (1128687247/73786976294838206464)), (11/147573952589676412928), by norm_num⟩
  | 3 => ⟨((1975493065/2361183241434822606848), (-5305667831/2361183241434822606848)), (23/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((169120869/18889465931478580854784), (4272538075/18889465931478580854784)), (19/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((-297279563/37778931862957161709568), (-5110464943/302231454903657293676544)), (29/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((38728773/37778931862957161709568), (2259777923/2417851639229258349412352)), (5/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((-433720311/4835703278458516698824704), (-1240069175/38685626227668133590597632)), (13/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((1894785527/309485009821345068724781056), (-400171779/1237940039285380274899124224)), (57/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((-3338749915/9903520314283042199192993792), (1607639715/9903520314283042199192993792)), (1/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((1148659977/79228162514264337593543950336), (-323443459/19807040628566084398385987584)), (33/158456325028528675187087900672), by norm_num⟩
  | 11 => ⟨((-503988291/1267650600228229401496703205376), (5884447595/5070602400912917605986812821504)), (67/5070602400912917605986812821504), by norm_num⟩
  | 12 => ⟨((-178219723/40564819207303340847894502572032), (-5397869435/81129638414606681695789005144064)), (1/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1141065817/36893488147419103232), (512817145/36893488147419103232)), (9/73786976294838206464), by norm_num⟩
  | 1 => ⟨((2113228655/295147905179352825856), (-1128687247/147573952589676412928)), (7/147573952589676412928), by norm_num⟩
  | 2 => ⟨((-1481619799/2361183241434822606848), (3979250873/2361183241434822606848)), (21/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-169120869/18889465931478580854784), (-4272538075/18889465931478580854784)), (23/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((185799727/18889465931478580854784), (1597020295/75557863725914323419136)), (21/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((-3717962209/2417851639229258349412352), (-847416721/604462909807314587353088)), (33/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((3036042177/19342813113834066795298816), (67816283/1208925819614629174706176)), (3/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((-7579142109/618970019642690137449562112), (200085889/309485009821345068724781056)), (65/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((1878046827/2475880078570760549798248448), (-1808594679/4951760157141521099596496896)), (5/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((-2871649943/79228162514264337593543950336), (3234434589/79228162514264337593543950336)), (23/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((173245975/158456325028528675187087900672), (-4045557721/1267650600228229401496703205376)), (25/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((267329585/20282409603651670423947251286016), (1012100519/5070602400912917605986812821504)), (53/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((-206919409/40564819207303340847894502572032), (-207809117/20282409603651670423947251286016)), (53/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1878425471/1180591620717411303424), (1003277553/590295810358705651712)), (27/2361183241434822606848), by norm_num⟩
  | 1 => ⟨((1316995377/4722366482869645213696), (-3537111887/4722366482869645213696)), (23/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((225494491/37778931862957161709568), (5696717433/37778931862957161709568)), (19/18889465931478580854784), by norm_num⟩
  | 3 => ⟨((-2642485005/302231454903657293676544), (-2839147191/151115727451828646838272)), (45/302231454903657293676544), by norm_num⟩
  | 4 => ⟨((2065534561/1208925819614629174706176), (1883148269/1208925819614629174706176)), (11/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((-1012014059/4835703278458516698824704), (-723373685/9671406556917033397649408)), (37/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((5894888307/309485009821345068724781056), (-311244717/309485009821345068724781056)), (7/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((-3338749915/2475880078570760549798248448), (1607639715/2475880078570760549798248448)), (5/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((2871649943/39614081257132168796771975168), (-3234434589/39614081257132168796771975168)), (51/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((-1539964223/633825300114114700748351602688), (2247532067/316912650057057350374175801344)), (63/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((-326736159/10141204801825835211973625643008), (-2474023491/5070602400912917605986812821504)), (9/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((2207140363/162259276829213363391578010288128), (4433261163/162259276829213363391578010288128)), (79/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((-450141703/324518553658426726783156020576256), (-3113272567/2596148429267413814265248164610048)), (83/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1053596301/18889465931478580854784), (1414844755/9444732965739290427392)), (5/4722366482869645213696), by norm_num⟩
  | 1 => ⟨((-180395593/75557863725914323419136), (-4557373947/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 2 => ⟨((1585491003/302231454903657293676544), (3406976629/302231454903657293676544)), (17/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((-3304855297/2417851639229258349412352), (-3013037231/2417851639229258349412352)), (43/2417851639229258349412352), by norm_num⟩
  | 4 => ⟨((4048056237/19342813113834066795298816), (723373685/9671406556917033397649408)), (45/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((-7073865969/309485009821345068724781056), (373493661/309485009821345068724781056)), (79/309485009821345068724781056), by norm_num⟩
  | 6 => ⟨((4674249881/2475880078570760549798248448), (-2250695601/2475880078570760549798248448)), (63/2475880078570760549798248448), by norm_num⟩
  | 7 => ⟨((-1148659977/9903520314283042199192993792), (323443459/2475880078570760549798248448)), (3/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((1385967801/316912650057057350374175801344), (-4045557721/316912650057057350374175801344)), (1/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((163368079/2535301200456458802993406410752), (2474023491/2535301200456458802993406410752)), (41/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((-2427854399/81129638414606681695789005144064), (-4876587279/81129638414606681695789005144064)), (49/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((1080340087/324518553658426726783156020576256), (466990885/162259276829213363391578010288128)), (7/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((-5466024913/20769187434139310514121985316880384), (-1792419723/20769187434139310514121985316880384)), (61/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5504000/1042651443), (-767040/347550481)), 0, by norm_num⟩
  | 1 => ⟨((-49997725491200/362374010529994083), (16887152640000/120791336843331361)), 0, by norm_num⟩
  | 2 => ⟨((1417926547/562949953421312), (-3521286641/562949953421312)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((109984977/36028797018963968), (8339592957/36028797018963968)), (5/36028797018963968), by norm_num⟩
  | 4 => ⟨((-1822654265/576460752303423488), (-4202949131/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 5 => ⟨((3628296749/18446744073709551616), (871879597/4611686018427387904)), (7/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-1288807015/147573952589676412928), (-1997275093/590295810358705651712)), (11/590295810358705651712), by norm_num⟩
  | 7 => ⟨((1517838551/4722366482869645213696), (-40042357/4722366482869645213696)), (1/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-3042842179/302231454903657293676544), (1367512387/302231454903657293676544)), (13/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((2504567295/9671406556917033397649408), (-334425851/1208925819614629174706176)), (19/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-351198767/77371252455336267181195264), (3772919347/309485009821345068724781056)), (27/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-174929061/9903520314283042199192993792), (-2209635853/4951760157141521099596496896)), (39/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((2049927763/316912650057057350374175801344), (1101244971/79228162514264337593543950336)), (29/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((668281669/33554432), (976520165/67108864)), (3/67108864), by norm_num⟩
  | 1 => ⟨((1420907167/1073741824), (879432145/4294967296)), (5/4294967296), by norm_num⟩
  | 2 => ⟨((34908429/4294967296), (-1938683467/549755813888)), (1/549755813888), by norm_num⟩
  | 3 => ⟨((-2515754645/35184372088832), (1343844219/17592186044416)), (7/35184372088832), by norm_num⟩
  | 4 => ⟨((351412815/562949953421312), (-3928622829/2251799813685248)), (17/2251799813685248), by norm_num⟩
  | 5 => ⟨((91933799/36028797018963968), (176920137/4503599627370496)), (21/72057594037927936), by norm_num⟩
  | 6 => ⟨((-1951935723/4611686018427387904), (-119184463/144115188075855872)), (29/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1336545371/73786976294838206464), (1102805043/73786976294838206464)), (19/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1413058661/2361183241434822606848), (-409795887/2361183241434822606848)), (193/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((1285029481/75557863725914323419136), (-646223543/302231454903657293676544)), (1/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-4040968353/9671406556917033397649408), (1189602825/4835703278458516698824704)), (11/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((2563463579/309485009821345068724781056), (-3501980733/309485009821345068724781056)), (465/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-913876637/9903520314283042199192993792), (1993207447/4951760157141521099596496896)), (303/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1512454983/4503599627370496), (939009771/1125899906842624)), (1/4503599627370496), by norm_num⟩
  | 1 => ⟨((-87987981/72057594037927936), (-6671674365/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 2 => ⟨((364530853/144115188075855872), (3362359305/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 3 => ⟨((-2418864499/9223372036854775808), (-2325012259/9223372036854775808)), (1/2305843009213693952), by norm_num⟩
  | 4 => ⟨((5155228059/295147905179352825856), (1997275093/295147905179352825856)), (1/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-2124973971/2361183241434822606848), (112118599/4722366482869645213696)), (1/590295810358705651712), by norm_num⟩
  | 6 => ⟨((2839986033/75557863725914323419136), (-638172447/37778931862957161709568)), (15/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-1502740377/1208925819614629174706176), (3210488169/2417851639229258349412352)), (7/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((1053596301/38685626227668133590597632), (-5659379019/77371252455336267181195264)), (23/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((160351639/1237940039285380274899124224), (8101998127/2475880078570760549798248448)), (35/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((-1127460269/19807040628566084398385987584), (-4845477871/39614081257132168796771975168)), (29/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((1281883267/316912650057057350374175801344), (2337386457/633825300114114700748351602688)), (23/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((-2093540195/10141204801825835211973625643008), (-1496433643/20282409603651670423947251286016)), (35/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2673126631/134217728), (976520221/67108864)), (7/134217728), by norm_num⟩
  | 1 => ⟨((5683628663/4294967296), (879431747/4294967296)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((4468280303/549755813888), (-484670065/137438953472)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((-78617621/1099511627776), (2687679569/35184372088832)), (1/4398046511104), by norm_num⟩
  | 4 => ⟨((1405690591/2251799813685248), (-3928607591/2251799813685248)), (9/1125899906842624), by norm_num⟩
  | 5 => ⟨((183802749/72057594037927936), (2830723903/72057594037927936)), (43/144115188075855872), by norm_num⟩
  | 6 => ⟨((-121985149/288230376151711744), (-1906990359/2305843009213693952)), (59/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1336453651/73786976294838206464), (2205806039/147573952589676412928)), (77/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2825988709/4722366482869645213696), (-819937195/4722366482869645213696)), (97/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((321259817/18889465931478580854784), (-322617265/151115727451828646838272)), (257/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-4041518871/9671406556917033397649408), (148626417/604462909807314587353088)), (353/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1282357709/154742504910672534362390528), (-3500839431/309485009821345068724781056)), (233/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-457960555/4951760157141521099596496896), (1992842107/4951760157141521099596496896)), (607/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2221902343/4611686018427387904), (-5123595131/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 1 => ⟨((2764416571/18446744073709551616), (2657156867/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-2945844605/147573952589676412928), (-570650027/73786976294838206464)), (9/295147905179352825856), by norm_num⟩
  | 3 => ⟨((2023784735/1180591620717411303424), (-53389809/1180591620717411303424)), (7/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((-4057122905/37778931862957161709568), (1823349849/37778931862957161709568)), (5/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((1502740377/302231454903657293676544), (-3210488169/604462909807314587353088)), (3/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((-351198767/2417851639229258349412352), (1886459673/4835703278458516698824704)), (13/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((-68722131/77371252455336267181195264), (-3472284911/154742504910672534362390528)), (27/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((1207993145/2475880078570760549798248448), (2595791717/2475880078570760549798248448)), (27/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((-3357313317/79228162514264337593543950336), (-3060863217/79228162514264337593543950336)), (25/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((1644924439/633825300114114700748351602688), (1175769291/1267650600228229401496703205376)), (21/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((-2613145293/20282409603651670423947251286016), (275943369/40564819207303340847894502572032)), (37/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((3453414053/649037107316853453566312041152512), (-1662851585/649037107316853453566312041152512)), (1/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2673126631/134217728), (976520221/67108864)), (1/16777216), by norm_num⟩
  | 1 => ⟨((710453583/536870912), (219857937/1073741824)), (7/4294967296), by norm_num⟩
  | 2 => ⟨((1117070073/137438953472), (-242335033/68719476736)), (3/549755813888), by norm_num⟩
  | 3 => ⟨((-628940953/8796093022208), (2687679567/35184372088832)), (9/35184372088832), by norm_num⟩
  | 4 => ⟨((1405690349/2251799813685248), (-1964303741/1125899906842624)), (19/2251799813685248), by norm_num⟩
  | 5 => ⟨((367606215/144115188075855872), (5661447041/144115188075855872)), (11/36028797018963968), by norm_num⟩
  | 6 => ⟨((-975881527/2305843009213693952), (-3813978919/4611686018427387904)), (15/1152921504606846976), by norm_num⟩
  | 7 => ⟨((2672907171/147573952589676412928), (275725341/18446744073709551616)), (39/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-2825986405/4722366482869645213696), (-204983061/1180591620717411303424)), (195/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((5140144265/302231454903657293676544), (-322623103/151115727451828646838272)), (129/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-4041493771/9671406556917033397649408), (1189015821/4835703278458516698824704)), (177/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((2564675545/309485009821345068724781056), (-1750418663/154742504910672534362390528)), (467/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-915868415/9903520314283042199192993792), (3985658841/9903520314283042199192993792)), (19/309485009821345068724781056), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4713351369/1180591620717411303424), (1826080085/1180591620717411303424)), (11/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((-4857083363/4722366482869645213696), (64067771/2361183241434822606848)), (13/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((2434273743/18889465931478580854784), (-1094009909/18889465931478580854784)), (7/18889465931478580854784), by norm_num⟩
  | 3 => ⟨((-1502740377/151115727451828646838272), (3210488169/302231454903657293676544)), (7/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((2107192603/4835703278458516698824704), (-1414844755/1208925819614629174706176)), (11/2417851639229258349412352), by norm_num⟩
  | 5 => ⟨((288632949/77371252455336267181195264), (7291798315/77371252455336267181195264)), (29/77371252455336267181195264), by norm_num⟩
  | 6 => ⟨((-845595201/309485009821345068724781056), (-908527101/154742504910672534362390528)), (19/618970019642690137449562112), by norm_num⟩
  | 7 => ⟨((3021581985/9903520314283042199192993792), (2754776895/9903520314283042199192993792)), (3/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((-3701079987/158456325028528675187087900672), (-1322740453/158456325028528675187087900672)), (13/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((7186149555/5070602400912917605986812821504), (-379422131/5070602400912917605986812821504)), (13/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((-1424533297/20282409603651670423947251286016), (1371852557/40564819207303340847894502572032)), (51/81129638414606681695789005144064), by norm_num⟩
  | 11 => ⟨((3564326717/1298074214633706907132624082305024), (-2007309709/649037107316853453566312041152512)), (25/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((-716783347/10384593717069655257060992658440192), (4184496067/20769187434139310514121985316880384)), (23/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2673126631/134217728), (976520221/67108864)), (9/134217728), by norm_num⟩
  | 1 => ⟨((710453583/536870912), (219857937/1073741824)), (1/536870912), by norm_num⟩
  | 2 => ⟨((1117070073/137438953472), (-242335033/68719476736)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-628940953/8796093022208), (2687679567/35184372088832)), (5/17592186044416), by norm_num⟩
  | 4 => ⟨((702845175/1125899906842624), (-3928607485/2251799813685248)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((45950777/18014398509481984), (5661447055/144115188075855872)), (45/144115188075855872), by norm_num⟩
  | 6 => ⟨((-1951763067/4611686018427387904), (-1906989473/2305843009213693952)), (61/4611686018427387904), by norm_num⟩
  | 7 => ⟨((167056701/9223372036854775808), (2205802769/147573952589676412928)), (79/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-5651973031/9444732965739290427392), (-1639864567/9444732965739290427392)), (49/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((5140144693/302231454903657293676544), (-645246229/302231454903657293676544)), (259/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-2020747225/4835703278458516698824704), (2378031969/9671406556917033397649408)), (355/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((2564676395/309485009821345068724781056), (-3500838283/309485009821345068724781056)), (117/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-915869099/9903520314283042199192993792), (996415209/2475880078570760549798248448)), (609/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3934179787/151115727451828646838272), (1768096823/151115727451828646838272)), (17/151115727451828646838272), by norm_num⟩
  | 1 => ⟨((1821503487/302231454903657293676544), (-3891500811/604462909807314587353088)), (25/604462909807314587353088), by norm_num⟩
  | 2 => ⟨((-638543213/1208925819614629174706176), (1714963339/1208925819614629174706176)), (19/2417851639229258349412352), by norm_num⟩
  | 3 => ⟨((-145774217/19342813113834066795298816), (-7365452843/38685626227668133590597632)), (5/4835703278458516698824704), by norm_num⟩
  | 4 => ⟨((2562409703/309485009821345068724781056), (5506224855/309485009821345068724781056)), (37/309485009821345068724781056), by norm_num⟩
  | 5 => ⟨((-3204708167/2475880078570760549798248448), (-182608317/154742504910672534362390528)), (15/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((5233850487/39614081257132168796771975168), (1870542055/39614081257132168796771975168)), (21/19807040628566084398385987584), by norm_num⟩
  | 7 => ⟨((-25518997/2475880078570760549798248448), (344929209/633825300114114700748351602688)), (57/633825300114114700748351602688), by norm_num⟩
  | 8 => ⟨((3237575675/5070602400912917605986812821504), (-48716355/158456325028528675187087900672)), (35/5070602400912917605986812821504), by norm_num⟩
  | 9 => ⟨((-2475226887/81129638414606681695789005144064), (2787930151/81129638414606681695789005144064)), (5/10141204801825835211973625643008), by norm_num⟩
  | 10 => ⟨((18666233/20282409603651670423947251286016), (-435885007/162259276829213363391578010288128)), (11/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((230425501/20769187434139310514121985316880384), (6979063511/41538374868278621028243970633760768)), (93/41538374868278621028243970633760768), by norm_num⟩
  | 12 => ⟨((-713419107/166153499473114484112975882535043072), (-1432973305/166153499473114484112975882535043072)), (93/664613997892457936451903530140172288), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2673126631/134217728), (976520221/67108864)), (5/67108864), by norm_num⟩
  | 1 => ⟨((710453583/536870912), (219857937/1073741824)), (9/4294967296), by norm_num⟩
  | 2 => ⟨((1117070073/137438953472), (-242335033/68719476736)), (5/549755813888), by norm_num⟩
  | 3 => ⟨((-628940953/8796093022208), (2687679567/35184372088832)), (11/35184372088832), by norm_num⟩
  | 4 => ⟨((702845175/1125899906842624), (-3928607485/2251799813685248)), (21/2251799813685248), by norm_num⟩
  | 5 => ⟨((45950777/18014398509481984), (5661447055/144115188075855872)), (23/72057594037927936), by norm_num⟩
  | 6 => ⟨((-975881533/2305843009213693952), (-1906989473/2305843009213693952)), (31/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1336453607/73786976294838206464), (2205802769/147573952589676412928)), (5/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-5651973025/9444732965739290427392), (-819932285/4722366482869645213696)), (197/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((1285036171/75557863725914323419136), (-645246219/302231454903657293676544)), (65/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-4041494441/9671406556917033397649408), (2378031943/9671406556917033397649408)), (89/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((1282338199/154742504910672534362390528), (-3500838231/309485009821345068724781056)), (469/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-457934571/4951760157141521099596496896), (3985660751/9903520314283042199192993792)), (305/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1034393225/9671406556917033397649408), (-5556229943/19342813113834066795298816)), (5/2417851639229258349412352), by norm_num⟩
  | 1 => ⟨((11069229/2417851639229258349412352), (4474310255/38685626227668133590597632)), (37/38685626227668133590597632), by norm_num⟩
  | 2 => ⟨((-778296749/77371252455336267181195264), (-3344880329/154742504910672534362390528)), (17/77371252455336267181195264), by norm_num⟩
  | 3 => ⟨((3244620283/1237940039285380274899124224), (2958120957/1237940039285380274899124224)), (43/1237940039285380274899124224), by norm_num⟩
  | 4 => ⟨((-3974275481/9903520314283042199192993792), (-1420378637/9903520314283042199192993792)), (45/9903520314283042199192993792), by norm_num⟩
  | 5 => ⟨((434058509/9903520314283042199192993792), (-91671571/39614081257132168796771975168)), (39/79228162514264337593543950336), by norm_num⟩
  | 6 => ⟨((-4589055983/1267650600228229401496703205376), (552418483/316912650057057350374175801344)), (63/1267650600228229401496703205376), by norm_num⟩
  | 7 => ⟨((2255448499/10141204801825835211973625643008), (-2540386463/10141204801825835211973625643008)), (3/633825300114114700748351602688), by norm_num⟩
  | 8 => ⟨((-1360706849/162259276829213363391578010288128), (3971822503/162259276829213363391578010288128)), (1/2535301200456458802993406410752), by norm_num⟩
  | 9 => ⟨((-320780993/2596148429267413814265248164610048), (-2428931399/1298074214633706907132624082305024)), (41/1298074214633706907132624082305024), by norm_num⟩
  | 10 => ⟨((2383603795/41538374868278621028243970633760768), (4787705535/41538374868278621028243970633760768)), (97/41538374868278621028243970633760768), by norm_num⟩
  | 11 => ⟨((-4242598291/664613997892457936451903530140172288), (-1833917629/332306998946228968225951765070086144)), (111/664613997892457936451903530140172288), by norm_num⟩
  | 12 => ⟨((2683199975/5316911983139663491615228241121378304), (879875345/5316911983139663491615228241121378304)), (15/1329227995784915872903807060280344576), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2673126631/134217728), (976520221/67108864)), (11/134217728), by norm_num⟩
  | 1 => ⟨((710453583/536870912), (219857937/1073741824)), (5/2147483648), by norm_num⟩
  | 2 => ⟨((1117070073/137438953472), (-242335033/68719476736)), (3/274877906944), by norm_num⟩
  | 3 => ⟨((-628940953/8796093022208), (2687679567/35184372088832)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((702845175/1125899906842624), (-3928607485/2251799813685248)), (11/1125899906842624), by norm_num⟩
  | 5 => ⟨((45950777/18014398509481984), (5661447055/144115188075855872)), (47/144115188075855872), by norm_num⟩
  | 6 => ⟨((-975881533/2305843009213693952), (-1906989473/2305843009213693952)), (63/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1336453607/73786976294838206464), (2205802769/147573952589676412928)), (81/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-5651973025/9444732965739290427392), (-819932285/4722366482869645213696)), (99/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1285036171/75557863725914323419136), (-161311555/75557863725914323419136)), (261/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-505186805/1208925819614629174706176), (297253993/1208925819614629174706176)), (357/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((641169099/77371252455336267181195264), (-3500838233/309485009821345068724781056)), (235/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-915869137/9903520314283042199192993792), (3985660753/9903520314283042199192993792)), (611/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-376554927212997/2097152), (428354798718485/1048576)), (27471881/262144), by norm_num⟩
  | 1 => ⟨((-2570047283/8), (2015305641/4)), (1293/8), by norm_num⟩
  | 2 => ⟨((-2113302865/8), (2435408171/8)), (503/4), by norm_num⟩
  | 3 => ⟨((-2206029237/16), (3830306729/32)), (1053/16), by norm_num⟩
  | 4 => ⟨((-3346491971/64), (2188779335/64)), (417/16), by norm_num⟩
  | 5 => ⟨((-993348427/64), (1912135721/256)), (533/64), by norm_num⟩
  | 6 => ⟨((-3869705239/1024), (1293003319/1024)), (2291/1024), by norm_num⟩
  | 7 => ⟨((-1596038757/2048), (649480955/4096)), (2129/4096), by norm_num⟩
  | 8 => ⟨((-4565300887/32768), (379721849/32768)), (1747/16384), by norm_num⟩
  | 9 => ⟨((-2880123647/131072), (-178777477/262144)), (2571/131072), by norm_num⟩
  | 10 => ⟨((-3249823201/1048576), (-463117845/1048576)), (6873/2097152), by norm_num⟩
  | 11 => ⟨((-1657415477/4194304), (-1684469085/16777216)), (8431/16777216), by norm_num⟩
  | 12 => ⟨((-6166012385/134217728), (-2271877525/134217728)), (9569/134217728), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1609919030673489/10141204801825835211973625643008), (2585572893545/10141204801825835211973625643008)), (53379/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((28332499009111/9903520314283042199192993792), (792736075247/158456325028528675187087900672)), (65671/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1928607377368579/39614081257132168796771975168), (111766340825/1237940039285380274899124224)), (148191/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((241356207340389/309485009821345068724781056), (118998786061/77371252455336267181195264)), (78907/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((906279347174663/77371252455336267181195264), (1908404473995/77371252455336267181195264)), (158217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((794190741041045/4835703278458516698824704), (3587686636041/9671406556917033397649408)), (148759/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1292808887962987/604462909807314587353088), (3148686731281/604462909807314587353088)), (32649/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((485790175635641/18889465931478580854784), (2567212479841/37778931862957161709568)), (26629/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1339141267103057/4722366482869645213696), (3866471723423/4722366482869645213696)), (80245/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((839386712542235/295147905179352825856), (5341966893283/590295810358705651712)), (221843/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1895316220333833/73786976294838206464), (3358021828589/36893488147419103232)), (69767/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1903734215804933/9223372036854775808), (475561510917/576460752303423488)), (316399/9223372036854775808), by norm_num⟩
  | 6 => ⟨((418825984956997/288230376151711744), (7676353537867/1152921504606846976)), (159743/576460752303423488), by norm_num⟩
  | 5 => ⟨((1266097976855097/144115188075855872), (6793398771957/144115188075855872)), (283063/144115188075855872), by norm_num⟩
  | 4 => ⟨((799823688507487/18014398509481984), (10345297053255/36028797018963968)), (107931/9007199254740992), by norm_num⟩
  | 3 => ⟨((1625569388148235/9007199254740992), (6603913975527/4503599627370496)), (276181/4503599627370496), by norm_num⟩
  | 2 => ⟨((1252263910794673/2251799813685248), (851969748081/140737488355328)), (571899/2251799813685248), by norm_num⟩
  | 1 => ⟨((330134084516811/281474976710656), (21540053983447/1125899906842624)), (227097/281474976710656), by norm_num⟩
  | 0 => ⟨((1536173386024867/1125899906842624), (23829304866123/562949953421312)), (2029479/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1536173386024867/1125899906842624), (23829304866123/562949953421312)), (7741847996238326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((261741442836249/140737488355328), (130050437771029/1125899906842624)), (356865/70368744177664), by norm_num⟩
  | 2 => ⟨((1939620104133357/562949953421312), (30233228563925/70368744177664)), (11278607/562949953421312), by norm_num⟩
  | 3 => ⟨((1644740818809959/140737488355328), (416669208899007/140737488355328)), (5463213/35184372088832), by norm_num⟩
  | 4 => ⟨((140529761794857/1099511627776), (608680089280123/8796093022208)), (40010385/8796093022208), by norm_num⟩
  | 5 => ⟨((793516223149003/68719476736), (1215563371997177/68719476736)), (123163213/68719476736), by norm_num⟩
  | 6 => ⟨((-376554927212997/2097152), (428354798718485/1048576)), (27471881/262144), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((2673126631/134217728), (976520221/67108864)), (11/134217728), by norm_num⟩, 2, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((2355200/55096081), (-9204480/55096081)), 0, by norm_num⟩
  | 1 => ⟨((39587742515200/3035578141558561), (21678391296000/3035578141558561)), 0, by norm_num⟩
  | 2 => ⟨((-3849481491/4398046511104), (4119707673/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-2094774623/35184372088832), (-1638418199/17592186044416)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((5095852575/562949953421312), (-1679060409/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((125349241/2251799813685248), (3692400277/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-5020621277/72057594037927936), (-115957285/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 7 => ⟨((1478375881/576460752303423488), (-3196407915/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 8 => ⟨((941606059/2305843009213693952), (3068945851/9223372036854775808)), (7/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-673709135/18446744073709551616), (1992155869/73786976294838206464)), (13/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-217617653/147573952589676412928), (-4282917261/1180591620717411303424)), (23/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((6319475397/18889465931478580854784), (-862105883/18889465931478580854784)), (5/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-252228179/75557863725914323419136), (4370395541/151115727451828646838272)), (35/151115727451828646838272), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((23/16), (7191/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((23/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((23/16), (7191/1280)))⁻¹=value ((2355200/55096081), (-9204480/55096081)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2355200/55096081), (-9204480/55096081))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((39/16), (7191/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1331200/20481627), (-1022720/6827209)), 0, by norm_num⟩
  | 1 => ⟨((3820756172800/419497044567129), (1361444864000/139832348189043)), 0, by norm_num⟩
  | 2 => ⟨((-2254513217/2199023255552), (402184143/1099511627776)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((416589869/70368744177664), (-6240115463/70368744177664)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((3630787383/562949953421312), (467980697/140737488355328)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-2065590353/4503599627370496), (3377830483/9007199254740992)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-3710869/281474976710656), (-419197443/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 7 => ⟨((4512897445/1152921504606846976), (18914353/36028797018963968)), (7/576460752303423488), by norm_num⟩
  | 8 => ⟨((-1535932949/9223372036854775808), (636696013/2305843009213693952)), (25/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-2253456531/147573952589676412928), (-3164891917/147573952589676412928)), (23/147573952589676412928), by norm_num⟩
  | 10 => ⟨((620565745/295147905179352825856), (-65933753/147573952589676412928)), (5/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-1317103217/37778931862957161709568), (3249018481/18889465931478580854784)), (35/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-887804923/75557863725914323419136), (-2478566807/302231454903657293676544)), (61/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((39/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((39/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((39/16), (7191/1280)))⁻¹=value ((1331200/20481627), (-1022720/6827209)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((1331200/20481627), (-1022720/6827209))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-25105575116800/1128457380203787), (-6493044736000/376152460067929)), 0, by norm_num⟩
  | 1 => ⟨((4324717443/1099511627776), (-178315227/68719476736)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((659544943/4398046511104), (5021942201/8796093022208)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-2303069557/35184372088832), (-156778667/35184372088832)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((183133149/70368744177664), (-887745799/140737488355328)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((1158144417/2251799813685248), (500871259/1125899906842624)), (5/4503599627370496), by norm_num⟩
  | 6 => ⟨((-4070638813/72057594037927936), (2425921263/72057594037927936)), (5/36028797018963968), by norm_num⟩
  | 7 => ⟨((-778072841/576460752303423488), (-3499037563/576460752303423488)), (19/1152921504606846976), by norm_num⟩
  | 8 => ⟨((5302357185/9223372036854775808), (65270225/1152921504606846976)), (19/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-1568108275/73786976294838206464), (893650457/18446744073709551616)), (9/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-1055801051/295147905179352825856), (-1877723619/590295810358705651712)), (17/590295810358705651712), by norm_num⟩
  | 11 => ⟨((3489013503/9444732965739290427392), (-1027781091/4722366482869645213696)), (31/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((1271153487/151115727451828646838272), (5609678945/151115727451828646838272)), (7/18889465931478580854784), by norm_num⟩
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
  | 0 => ⟨((55/16), (7191/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5632000/71070481), (-9204480/71070481)), 0, by norm_num⟩
  | 1 => ⟨((26501514035200/5051013269571361), (51839631360000/5051013269571361)), 0, by norm_num⟩
  | 2 => ⟨((-7674552781/8796093022208), (-588420633/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((342189799/8796093022208), (-3789268435/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((1095281285/562949953421312), (327411553/70368744177664)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-426025665/1125899906842624), (-1051431803/18014398509481984)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((1352682775/72057594037927936), (-3197943827/144115188075855872)), (1/18014398509481984), by norm_num⟩
  | 7 => ⟨((1598277205/2305843009213693952), (1207598489/576460752303423488)), (7/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-3008999575/18446744073709551616), (-1406318687/36893488147419103232)), (3/4611686018427387904), by norm_num⟩
  | 9 => ⟨((2636132627/295147905179352825856), (-2671835919/295147905179352825856)), (21/295147905179352825856), by norm_num⟩
  | 10 => ⟨((274267493/1180591620717411303424), (553141183/590295810358705651712)), (9/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-2640179893/37778931862957161709568), (-1668695111/75557863725914323419136)), (61/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((1269119231/302231454903657293676544), (-2206534957/604462909807314587353088)), (13/151115727451828646838272), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((55/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((55/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((55/16), (7191/1280)))⁻¹=value ((5632000/71070481), (-9204480/71070481)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((5632000/71070481), (-9204480/71070481))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4396536603/1099511627776), (1664036363/1099511627776)), (1/1099511627776), by norm_num⟩
  | 1 => ⟨((19828049/549755813888), (-142103583/137438953472)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((665647493/4398046511104), (2432096847/35184372088832)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-2285210591/140737488355328), (1068644847/70368744177664)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-535220453/562949953421312), (-2803613559/1125899906842624)), (7/2251799813685248), by norm_num⟩
  | 5 => ⟨((2677776527/9007199254740992), (51711843/9007199254740992)), (9/18014398509481984), by norm_num⟩
  | 6 => ⟨((-883986787/72057594037927936), (4180528893/144115188075855872)), (11/144115188075855872), by norm_num⟩
  | 7 => ⟨((-1317476131/576460752303423488), (-1297034361/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 8 => ⟨((5333790347/18446744073709551616), (-594050481/4611686018427387904)), (23/18446744073709551616), by norm_num⟩
  | 9 => ⟨((217653147/147573952589676412928), (4489088807/147573952589676412928)), (23/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-6431199691/2361183241434822606848), (-16575741/18446744073709551616)), (11/590295810358705651712), by norm_num⟩
  | 11 => ⟨((1579122167/9444732965739290427392), (-3888658311/18889465931478580854784)), (21/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((920330737/75557863725914323419136), (3148664305/151115727451828646838272)), (5/18889465931478580854784), by norm_num⟩
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
  | 0 => ⟨((71/16), (7191/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7270400/83972881), (-9204480/83972881)), 0, by norm_num⟩
  | 1 => ⟨((15931867955200/7051444743440161), (66920251392000/7051444743440161)), 0, by norm_num⟩
  | 2 => ⟨((-1358855857/2199023255552), (-315568881/1099511627776)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((2989292799/70368744177664), (-1508856189/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-747395365/1125899906842624), (3666409761/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-337174713/2251799813685248), (-798725751/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((4669943961/288230376151711744), (-76211291/144115188075855872)), (7/144115188075855872), by norm_num⟩
  | 7 => ⟨((-1550471513/2305843009213693952), (4200649391/4611686018427387904)), (23/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-767852523/36893488147419103232), (-5628766687/73786976294838206464)), (37/73786976294838206464), by norm_num⟩
  | 9 => ⟨((2999780863/590295810358705651712), (2552063821/1180591620717411303424)), (59/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-3196728905/9444732965739290427392), (1746674435/9444732965739290427392)), (3/590295810358705651712), by norm_num⟩
  | 11 => ⟨((682531583/151115727451828646838272), (-4013033597/151115727451828646838272)), (19/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((1523139827/1208925819614629174706176), (1689055197/1208925819614629174706176)), (15/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((71/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((71/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((71/16), (7191/1280)))⁻¹=value ((7270400/83972881), (-9204480/83972881)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7270400/83972881), (-9204480/83972881))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1586034929/8796093022208), (312994163/549755813888)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((-293805693/2199023255552), (-2251816477/17592186044416)), (1/8796093022208), by norm_num⟩
  | 2 => ⟨((294493451/8796093022208), (-871619919/70368744177664)), (5/140737488355328), by norm_num⟩
  | 3 => ⟨((-576150599/1125899906842624), (192310373/35184372088832)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-712322679/1125899906842624), (-846770919/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((2679347981/36028797018963968), (-1818924733/36028797018963968)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((479925633/288230376151711744), (5832360341/576460752303423488)), (17/576460752303423488), by norm_num⟩
  | 7 => ⟨((-4939526005/4611686018427387904), (-167763761/576460752303423488)), (5/1152921504606846976), by norm_num⟩
  | 8 => ⟨((2701791235/36893488147419103232), (-3281699655/36893488147419103232)), (21/36893488147419103232), by norm_num⟩
  | 9 => ⟨((381245853/73786976294838206464), (1525370939/147573952589676412928)), (11/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-5310224381/4722366482869645213696), (133335201/2361183241434822606848)), (21/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((1416514645/37778931862957161709568), (-3786351153/37778931862957161709568)), (41/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((4357106365/604462909807314587353088), (4148141757/604462909807314587353088)), (79/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((87/16), (7191/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2969600/33384027), (-1022720/11128009)), 0, by norm_num⟩
  | 1 => ⟨((297540812800/1114493258736729), (3037069312000/371497752912243)), 0, by norm_num⟩
  | 2 => ⟨((-3408883143/8796093022208), (-1545188167/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((1174501113/35184372088832), (-307169017/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-48708737/35184372088832), (1836375037/1125899906842624)), (5/2251799813685248), by norm_num⟩
  | 5 => ⟨((-240986515/18014398509481984), (-4905616767/36028797018963968)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((3949789341/576460752303423488), (24504513/4503599627370496)), (13/576460752303423488), by norm_num⟩
  | 7 => ⟨((-5116894149/9223372036854775808), (671987147/9223372036854775808)), (5/2305843009213693952), by norm_num⟩
  | 8 => ⟨((1573610611/73786976294838206464), (-2120173577/73786976294838206464)), (15/73786976294838206464), by norm_num⟩
  | 9 => ⟨((219510689/590295810358705651712), (5331486983/2361183241434822606848)), (11/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-4544758095/37778931862957161709568), (-196776861/2361183241434822606848)), (65/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((5549001009/604462909807314587353088), (-137624737/75557863725914323419136)), (95/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-784822975/2417851639229258349412352), (4863342889/9671406556917033397649408)), (139/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((87/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((87/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((87/16), (7191/1280)))⁻¹=value ((2969600/33384027), (-1022720/11128009)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((2969600/33384027), (-1022720/11128009))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((159584843/4398046511104), (591231501/8796093022208)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((-498759945/17592186044416), (-60366261/140737488355328)), (7/281474976710656), by norm_num⟩
  | 2 => ⟨((878323163/281474976710656), (-3075128459/562949953421312)), (5/562949953421312), by norm_num⟩
  | 3 => ⟨((2562753761/4503599627370496), (4141383179/4503599627370496)), (9/4503599627370496), by norm_num⟩
  | 4 => ⟨((-5707088825/36028797018963968), (358322621/36028797018963968)), (13/36028797018963968), by norm_num⟩
  | 5 => ⟨((1234126677/144115188075855872), (-5489886631/288230376151711744)), (9/144115188075855872), by norm_num⟩
  | 6 => ⟨((3625579913/2305843009213693952), (4583097607/2305843009213693952)), (11/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-5225783429/18446744073709551616), (1040451903/18446744073709551616)), (13/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1231807439/147573952589676412928), (-4452204493/147573952589676412928)), (7/36893488147419103232), by norm_num⟩
  | 9 => ⟨((2862549243/1180591620717411303424), (2561852559/1180591620717411303424)), (15/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-44625247/147573952589676412928), (291077615/2361183241434822606848)), (59/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((72106887/37778931862957161709568), (-4796370619/151115727451828646838272)), (59/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1599119895/604462909807314587353088), (874864809/604462909807314587353088)), (29/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((103/16), (7191/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((10547200/119608081), (-9204480/119608081)), 0, by norm_num⟩
  | 1 => ⟨((-13260487884800/14306093040502561), (97081491456000/14306093040502561)), 0, by norm_num⟩
  | 2 => ⟨((-968635507/4398046511104), (-2945510119/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((6360061751/281474976710656), (885245339/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-2788349705/2251799813685248), (166658229/281474976710656)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((71639237/2251799813685248), (-5314360721/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 6 => ⟨((1654532987/1152921504606846976), (5160352801/1152921504606846976)), (13/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-543015605/2305843009213693952), (-1310886587/9223372036854775808)), (9/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1169660305/73786976294838206464), (-824897053/295147905179352825856)), (25/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-2792708713/4722366482869645213696), (1731147705/2361183241434822606848)), (17/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-80709313/37778931862957161709568), (-4161789279/75557863725914323419136)), (23/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1338023999/604462909807314587353088), (2836560809/1208925819614629174706176)), (31/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-3634127743/19342813113834066795298816), (-707128661/38685626227668133590597632)), (165/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((103/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((103/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((103/16), (7191/1280)))⁻¹=value ((10547200/119608081), (-9204480/119608081)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((10547200/119608081), (-9204480/119608081))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1178291629/140737488355328), (55147543/17592186044416)), (7/562949953421312), by norm_num⟩
  | 1 => ⟨((-3403386347/1125899906842624), (1310482849/562949953421312)), (3/562949953421312), by norm_num⟩
  | 2 => ⟨((-114279331/1125899906842624), (-4236875841/4503599627370496)), (9/4503599627370496), by norm_num⟩
  | 3 => ⟨((5822946261/36028797018963968), (2697543871/36028797018963968)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-1672433279/72057594037927936), (287952593/18014398509481984)), (13/144115188075855872), by norm_num⟩
  | 5 => ⟨((-348573251/1152921504606846976), (-4538369843/1152921504606846976)), (9/576460752303423488), by norm_num⟩
  | 6 => ⟨((4209566843/9223372036854775808), (1994043469/9223372036854775808)), (23/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-1810811443/36893488147419103232), (2568046281/73786976294838206464)), (7/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-449055195/590295810358705651712), (-992552429/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 9 => ⟨((794698737/1180591620717411303424), (321160327/1180591620717411303424)), (35/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-4331342053/75557863725914323419136), (1815199807/37778931862957161709568)), (35/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-482214979/302231454903657293676544), (-549299875/75557863725914323419136)), (35/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((6719145965/9671406556917033397649408), (885831215/4835703278458516698824704)), (139/9671406556917033397649408), by norm_num⟩
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
  | 0 => ⟨((119/16), (7191/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((716800/8372993), (-541440/8372993)), 0, by norm_num⟩
  | 1 => ⟨((-110322483200/70107011778049), (388104192000/70107011778049)), 0, by norm_num⟩
  | 2 => ⟨((-1963832595/17592186044416), (-2531858073/8796093022208)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((1982265445/140737488355328), (2452049549/281474976710656)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-3983677951/4503599627370496), (371600921/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((2536059211/72057594037927936), (-144708477/4503599627370496)), (7/72057594037927936), by norm_num⟩
  | 6 => ⟨((-1078193985/2305843009213693952), (5795311627/2305843009213693952)), (9/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-1129805831/18446744073709551616), (-4526798697/36893488147419103232)), (23/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1944671171/295147905179352825856), (30176861/9223372036854775808)), (29/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-3662799199/9444732965739290427392), (689336283/9444732965739290427392)), (9/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((16811941/1180591620717411303424), (-591736371/37778931862957161709568)), (11/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-498638131/4835703278458516698824704), (5468566209/4835703278458516698824704)), (107/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((-1243749601/38685626227668133590597632), (-125100155/2417851639229258349412352)), (129/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((119/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((119/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((119/16), (7191/1280)))⁻¹=value ((716800/8372993), (-541440/8372993)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((716800/8372993), (-541440/8372993))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2070413053/2251799813685248), (-614807439/2251799813685248)), (5/2251799813685248), by norm_num⟩
  | 1 => ⟨((-624985283/4503599627370496), (30692895/70368744177664)), (9/9007199254740992), by norm_num⟩
  | 2 => ⟨((-2798969097/36028797018963968), (-3499545133/36028797018963968)), (13/36028797018963968), by norm_num⟩
  | 3 => ⟨((3623551777/144115188075855872), (-345241667/144115188075855872)), (25/288230376151711744), by norm_num⟩
  | 4 => ⟨((-140663265/72057594037927936), (4363536383/1152921504606846976)), (21/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-368063059/1152921504606846976), (-5004231283/9223372036854775808)), (31/9223372036854775808), by norm_num⟩
  | 6 => ⟨((6217254265/73786976294838206464), (34989335/18446744073709551616)), (41/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-3317035603/590295810358705651712), (2596271815/295147905179352825856)), (51/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-642162955/1180591620717411303424), (-5122856685/4722366482869645213696)), (15/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((5046301587/37778931862957161709568), (325188919/37778931862957161709568)), (67/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-2356300397/302231454903657293676544), (1778720321/151115727451828646838272)), (35/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-790100105/1208925819614629174706176), (-3083004123/2417851639229258349412352)), (9/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((2718127499/19342813113834066795298816), (162685313/38685626227668133590597632)), (143/38685626227668133590597632), by norm_num⟩
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
  | 0 => ⟨((135/16), (7191/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((512000/6235203), (-1022720/18705609)), 0, by norm_num⟩
  | 1 => ⟨((-656669900800/349899808060881), (523632640000/116633269353627)), 0, by norm_num⟩
  | 2 => ⟨((-803590123/17592186044416), (-259082125/1099511627776)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((2341034697/281474976710656), (2371632857/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-2575204325/4503599627370496), (-1068004843/9007199254740992)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((1925261583/72057594037927936), (-1551179861/144115188075855872)), (7/144115188075855872), by norm_num⟩
  | 6 => ⟨((-115686715/144115188075855872), (1351598725/1152921504606846976)), (9/2305843009213693952), by norm_num⟩
  | 7 => ⟨((67147869/73786976294838206464), (-2585386301/36893488147419103232)), (21/73786976294838206464), by norm_num⟩
  | 8 => ⟨((2217565193/1180591620717411303424), (3426129643/1180591620717411303424)), (3/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-5910656163/37778931862957161709568), (-2561445057/37778931862957161709568)), (53/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((2501583125/302231454903657293676544), (-451322737/302231454903657293676544)), (59/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-2891842669/9671406556917033397649408), (1390663439/4835703278458516698824704)), (33/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1366308225/309485009821345068724781056), (-3091976709/154742504910672534362390528)), (73/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((135/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((135/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((135/16), (7191/1280)))⁻¹=value ((512000/6235203), (-1022720/18705609)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((512000/6235203), (-1022720/18705609))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1091171567/18014398509481984), (-2618933873/36028797018963968)), (3/9007199254740992), by norm_num⟩
  | 1 => ⟨((215314053/18014398509481984), (3461919747/72057594037927936)), (3/18014398509481984), by norm_num⟩
  | 2 => ⟨((-1944686721/144115188075855872), (-1549015953/288230376151711744)), (17/288230376151711744), by norm_num⟩
  | 3 => ⟨((1518744837/576460752303423488), (-991313985/576460752303423488)), (9/576460752303423488), by norm_num⟩
  | 4 => ⟨((-133957639/9223372036854775808), (5166384921/9223372036854775808)), (15/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-2604499947/36893488147419103232), (-465709501/9223372036854775808)), (3/4611686018427387904), by norm_num⟩
  | 6 => ⟨((3335579895/295147905179352825856), (-1271466931/295147905179352825856)), (1/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-48214743/147573952589676412928), (3578067551/2361183241434822606848)), (41/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-1246592175/9444732965739290427392), (-1232418677/9444732965739290427392)), (49/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((771643739/37778931862957161709568), (-1464930739/302231454903657293676544)), (55/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-212389977/302231454903657293676544), (1299699263/604462909807314587353088)), (119/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-185339337/1208925819614629174706176), (-853319453/4835703278458516698824704)), (31/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((7083306929/309485009821345068724781056), (-1325759049/309485009821345068724781056)), (251/309485009821345068724781056), by norm_num⟩
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
  | 0 => ⟨((151/16), (7191/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((15462400/197636881), (-9204480/197636881)), 0, by norm_num⟩
  | 1 => ⟨((-77181680844800/39060336731408161), (142323351552000/39060336731408161)), 0, by norm_num⟩
  | 2 => ⟨((-132855185/17592186044416), (-6633911163/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((659494547/140737488355328), (2026554187/281474976710656)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-1580600311/4503599627370496), (-194242923/1125899906842624)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((1278769205/72057594037927936), (-102602585/72057594037927936)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-3048570679/4611686018427387904), (1081327551/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 7 => ⟨((1102308577/73786976294838206464), (-4978855831/147573952589676412928)), (17/147573952589676412928), by norm_num⟩
  | 8 => ⟨((237589393/1180591620717411303424), (1968810971/1180591620717411303424)), (9/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-441123809/9444732965739290427392), (-4574960835/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((3913309997/1208925819614629174706176), (1548591619/1208925819614629174706176)), (19/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-3026283139/19342813113834066795298816), (488776811/19342813113834066795298816)), (77/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((3424030075/618970019642690137449562112), (-1433458169/309485009821345068724781056)), (39/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((151/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((151/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((151/16), (7191/1280)))⁻¹=value ((15462400/197636881), (-9204480/197636881)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((15462400/197636881), (-9204480/197636881))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6095989/4503599627370496), (-2452268485/288230376151711744)), (25/576460752303423488), by norm_num⟩
  | 1 => ⟨((478146305/144115188075855872), (4111847939/1152921504606846976)), (27/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-7004453907/4611686018427387904), (336045141/2305843009213693952)), (5/576460752303423488), by norm_num⟩
  | 3 => ⟨((419787531/2305843009213693952), (-687855019/2305843009213693952)), (11/4611686018427387904), by norm_num⟩
  | 4 => ⟨((914068871/36893488147419103232), (1114340105/18446744073709551616)), (19/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-6050858137/590295810358705651712), (-722718825/295147905179352825856)), (31/295147905179352825856), by norm_num⟩
  | 6 => ⟨((2695415997/2361183241434822606848), (-297001629/295147905179352825856)), (43/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((898794431/37778931862957161709568), (235787371/1180591620717411303424)), (113/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-830563003/37778931862957161709568), (-53459545/4722366482869645213696)), (35/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((754332543/302231454903657293676544), (-1691991291/1208925819614629174706176)), (5/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-384604847/19342813113834066795298816), (758768275/2417851639229258349412352)), (175/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-4138212055/154742504910672534362390528), (-3002750865/154742504910672534362390528)), (185/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((956033367/309485009821345068724781056), (-782828877/618970019642690137449562112)), (191/1237940039285380274899124224), by norm_num⟩
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
  | 0 => ⟨((167/16), (7191/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((17100800/230200081), (-9204480/230200081)), 0, by norm_num⟩
  | 1 => ⟨((-103857454284800/52992077292406561), (157403971584000/52992077292406561)), 0, by norm_num⟩
  | 2 => ⟨((235949109/17592186044416), (-5260427523/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((175280837/70368744177664), (51206051/8796093022208)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-1881644687/9007199254740992), (-2998127341/18014398509481984)), (5/18014398509481984), by norm_num⟩
  | 5 => ⟨((6391063751/576460752303423488), (288987809/144115188075855872)), (5/288230376151711744), by norm_num⟩
  | 6 => ⟨((-65123909/144115188075855872), (678691813/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2042777037/147573952589676412928), (-2139911527/147573952589676412928)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-264749667/1180591620717411303424), (3850347867/4722366482869645213696)), (19/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-1204567813/151115727451828646838272), (-2626986421/75557863725914323419136)), (9/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((149780923/151115727451828646838272), (2737087427/2417851639229258349412352)), (17/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-2299753985/38685626227668133590597632), (-1720096459/77371252455336267181195264)), (63/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((1641838855/618970019642690137449562112), (-898074651/2475880078570760549798248448)), (29/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((167/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((167/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((167/16), (7191/1280)))⁻¹=value ((17100800/230200081), (-9204480/230200081)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((17100800/230200081), (-9204480/230200081))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2210264209/9223372036854775808), (-395541295/576460752303423488)), (23/4611686018427387904), by norm_num⟩
  | 1 => ⟨((1898591497/4611686018427387904), (1410937339/9223372036854775808)), (7/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-4624706511/36893488147419103232), (683504293/9223372036854775808)), (21/18446744073709551616), by norm_num⟩
  | 3 => ⟨((704051271/147573952589676412928), (-2560291909/73786976294838206464)), (3/9223372036854775808), by norm_num⟩
  | 4 => ⟨((2817146553/590295810358705651712), (2881284761/590295810358705651712)), (11/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-2678141727/2361183241434822606848), (335463129/2361183241434822606848)), (9/590295810358705651712), by norm_num⟩
  | 6 => ⟨((1583982297/18889465931478580854784), (-2802272557/18889465931478580854784)), (13/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((725680071/75557863725914323419136), (796076115/37778931862957161709568)), (35/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((-6924339133/2417851639229258349412352), (-668024041/1208925819614629174706176)), (175/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((2387564805/9671406556917033397649408), (-2325949569/9671406556917033397649408)), (103/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((519120179/77371252455336267181195264), (2938249785/77371252455336267181195264)), (229/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-4668214821/1237940039285380274899124224), (-1020460849/618970019642690137449562112)), (123/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((3485405953/9903520314283042199192993792), (-2293890009/9903520314283042199192993792)), (257/9903520314283042199192993792), by norm_num⟩
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
  | 0 => ⟨((183/16), (7191/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((6246400/88680027), (-1022720/29560009)), 0, by norm_num⟩
  | 1 => ⟨((-14801953587200/7864147188720729), (6388318208000/2621382396240243)), 0, by norm_num⟩
  | 2 => ⟨((849039257/35184372088832), (-4165429147/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((84311705/70368744177664), (645555169/140737488355328)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-1094796533/9007199254740992), (-634195965/4503599627370496)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((1935978923/288230376151711744), (1646863701/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((-5275350459/18446744073709551616), (143691139/9223372036854775808)), (11/18446744073709551616), by norm_num⟩
  | 7 => ⟨((2893117233/295147905179352825856), (-405519135/73786976294838206464)), (11/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-1181305651/4722366482869645213696), (1714810977/4722366482869645213696)), (19/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((764129013/302231454903657293676544), (-5173053917/302231454903657293676544)), (33/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((2002471495/9671406556917033397649408), (3126515427/4835703278458516698824704)), (7/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-357392055/19342813113834066795298816), (-2969329631/154742504910672534362390528)), (3/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((304123591/309485009821345068724781056), (1763704027/4951760157141521099596496896)), (41/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((183/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((183/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((183/16), (7191/1280)))⁻¹=value ((6246400/88680027), (-1022720/29560009)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((6246400/88680027), (-1022720/29560009))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-374645105/9223372036854775808), (-369304151/9223372036854775808)), (5/9223372036854775808), by norm_num⟩
  | 1 => ⟨((671725981/18446744073709551616), (-407471381/147573952589676412928)), (51/147573952589676412928), by norm_num⟩
  | 2 => ⟨((-1106853987/147573952589676412928), (3035291889/295147905179352825856)), (5/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-114842641/147573952589676412928), (-3661096863/1180591620717411303424)), (3/73786976294838206464), by norm_num⟩
  | 4 => ⟨((2767719569/4722366482869645213696), (648022285/2361183241434822606848)), (45/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((-473966451/4722366482869645213696), (234809415/4722366482869645213696)), (19/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((1042249357/302231454903657293676544), (-1272253257/75557863725914323419136)), (7/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((3809043769/2417851639229258349412352), (1090837915/604462909807314587353088)), (77/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-5948716029/19342813113834066795298816), (461456565/19342813113834066795298816)), (197/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((3015399835/154742504910672534362390528), (-612037611/19342813113834066795298816)), (59/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((1019797885/618970019642690137449562112), (301304999/77371252455336267181195264)), (67/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-138664517/309485009821345068724781056), (-116748415/1237940039285380274899124224)), (73/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((677142195/19807040628566084398385987584), (-2608247043/79228162514264337593543950336)), (77/19807040628566084398385987584), by norm_num⟩
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
  | 0 => ⟨((199/16), (7191/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((20377600/305156881), (-9204480/305156881)), 0, by norm_num⟩
  | 1 => ⟨((-165262064844800/93120722021648161), (187565211648000/93120722021648161)), 0, by norm_num⟩
  | 2 => ⟨((1016044847/35184372088832), (-826986209/8796093022208)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((255432067/562949953421312), (1006172837/281474976710656)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-622045629/9007199254740992), (-1013397587/9007199254740992)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((2307387047/576460752303423488), (782548521/288230376151711744)), (11/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-1610317015/9223372036854775808), (-1117287451/36893488147419103232)), (9/18446744073709551616), by norm_num⟩
  | 7 => ⟨((3710658821/590295810358705651712), (-957432417/590295810358705651712)), (15/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-875636865/4722366482869645213696), (703439615/4722366482869645213696)), (3/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((74509753/18889465931478580854784), (-1174173391/151115727451828646838272)), (19/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-280822699/19342813113834066795298816), (6168824135/19342813113834066795298816)), (15/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-669273137/154742504910672534362390528), (-1681635455/154742504910672534362390528)), (47/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((3053302691/9903520314283042199192993792), (2947455313/9903520314283042199192993792)), (37/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((199/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((199/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((199/16), (7191/1280)))⁻¹=value ((20377600/305156881), (-9204480/305156881)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((20377600/305156881), (-9204480/305156881))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4628122601/1180591620717411303424), (-855086761/590295810358705651712)), (63/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((2952788083/1180591620717411303424), (-1527103957/1180591620717411303424)), (43/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((-2348801/9223372036854775808), (4693464871/4722366482869645213696)), (35/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-717756945/4722366482869645213696), (-2083824531/9444732965739290427392)), (43/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((4217482397/75557863725914323419136), (54053537/9444732965739290427392)), (21/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((-270210565/37778931862957161709568), (4230307063/604462909807314587353088)), (9/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-698009551/4835703278458516698824704), (-3795941341/2417851639229258349412352)), (109/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((1819488073/9671406556917033397649408), (297959039/2417851639229258349412352)), (77/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((-2163085685/77371252455336267181195264), (1484322319/154742504910672534362390528)), (25/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((702930181/618970019642690137449562112), (-4261770931/1237940039285380274899124224)), (61/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((1195783919/4951760157141521099596496896), (1695612873/4951760157141521099596496896)), (141/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-1821910229/39614081257132168796771975168), (-45502077/79228162514264337593543950336)), (623/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((898189057/316912650057057350374175801344), (-4948898757/1267650600228229401496703205376)), (665/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22259031/17179869184), (-2949625241/2199023255552)), (1307/2199023255552), by norm_num⟩
  | 1 => ⟨((4548750919/2199023255552), (-562371663/2199023255552)), (183/137438953472), by norm_num⟩
  | 2 => ⟨((4241778801/4398046511104), (2561604769/4398046511104)), (6547/4398046511104), by norm_num⟩
  | 3 => ⟨((1279457671/8796093022208), (1598794149/4398046511104)), (9859/8796093022208), by norm_num⟩
  | 4 => ⟨((-1629509797/70368744177664), (6713369277/70368744177664)), (45049/70368744177664), by norm_num⟩
  | 5 => ⟨((-3885459297/281474976710656), (1826729341/140737488355328)), (83291/281474976710656), by norm_num⟩
  | 6 => ⟨((-6468288013/2251799813685248), (769178055/1125899906842624)), (259631/2251799813685248), by norm_num⟩
  | 7 => ⟨((-6855188297/18014398509481984), (-1504497447/18014398509481984)), (175465/4503599627370496), by norm_num⟩
  | 8 => ⟨((-2735782365/72057594037927936), (-463271475/18014398509481984)), (420045/36028797018963968), by norm_num⟩
  | 9 => ⟨((-1716700143/576460752303423488), (-289095259/72057594037927936)), (904887/288230376151711744), by norm_num⟩
  | 10 => ⟨((-1440702545/9223372036854775808), (-4421178625/9223372036854775808)), (3553465/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-50613211/147573952589676412928), (-6860939381/147573952589676412928)), (25701475/147573952589676412928), by norm_num⟩
  | 12 => ⟨((612822201/590295810358705651712), (-564853931/147573952589676412928)), (21580539/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22259031/17179869184), (-2949625241/2199023255552)), (327/549755813888), by norm_num⟩
  | 1 => ⟨((4548750919/2199023255552), (-562371663/2199023255552)), (2929/2199023255552), by norm_num⟩
  | 2 => ⟨((4241778801/4398046511104), (2561604769/4398046511104)), (1637/1099511627776), by norm_num⟩
  | 3 => ⟨((1279457671/8796093022208), (1598794149/4398046511104)), (2465/2199023255552), by norm_num⟩
  | 4 => ⟨((-1629509797/70368744177664), (6713369277/70368744177664)), (11263/17592186044416), by norm_num⟩
  | 5 => ⟨((-3885459297/281474976710656), (1826729341/140737488355328)), (83303/281474976710656), by norm_num⟩
  | 6 => ⟨((-6468288013/2251799813685248), (769178055/1125899906842624)), (129861/1125899906842624), by norm_num⟩
  | 7 => ⟨((-6855188297/18014398509481984), (-1504497447/18014398509481984)), (702581/18014398509481984), by norm_num⟩
  | 8 => ⟨((-2735782365/72057594037927936), (-463271475/18014398509481984)), (842973/72057594037927936), by norm_num⟩
  | 9 => ⟨((-1716700143/576460752303423488), (-289095259/72057594037927936)), (3665665/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-1440702545/9223372036854775808), (-4421178625/9223372036854775808)), (7475865/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-50613211/147573952589676412928), (-6860939381/147573952589676412928)), (15802217/73786976294838206464), by norm_num⟩
  | 12 => ⟨((612822201/590295810358705651712), (-564853931/147573952589676412928)), (90384743/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile026Gamma

/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile018Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨18,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (5217/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (5217/640))
  have he : value ((3/4), (5217/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

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

def J_negLog2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale (A_log2 hcre) S_log2)
  intro k
  fin_cases k <;> norm_num [J_negLog2, J_log2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1116391677/2147483648), (-12133782039/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-23816355775/34359738368), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul (A_negLog2 hcre) (A_variable hcre) S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg2, J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((134944612243897/281474976710656), (792013620568671/2251799813685248)), (1055475/2251799813685248), by norm_num⟩
  | 1 => ⟨((-356813345/1073741824), (-2094200165/8589934592)), (13/34359738368), by norm_num⟩
  | 2 => ⟨((15828746501/137438953472), (11612711519/137438953472)), (5/34359738368), by norm_num⟩
  | 3 => ⟨((-3657217003/137438953472), (-10732424331/549755813888)), (5/137438953472), by norm_num⟩
  | 4 => ⟨((10139958617/2199023255552), (3719574833/1099511627776)), (1/137438953472), by norm_num⟩
  | 5 => ⟨((-5622786981/8796093022208), (-8250280987/17592186044416)), (5/4398046511104), by norm_num⟩
  | 6 => ⟨((10393117181/140737488355328), (7624878673/140737488355328)), (5/35184372088832), by norm_num⟩
  | 7 => ⟨((-2058274249/281474976710656), (-3020093231/562949953421312)), (17/1125899906842624), by norm_num⟩
  | 8 => ⟨((2853373985/4503599627370496), (8373476433/18014398509481984)), (13/9007199254740992), by norm_num⟩
  | 9 => ⟨((-14064413389/288230376151711744), (-5159156961/144115188075855872)), (17/144115188075855872), by norm_num⟩
  | 10 => ⟨((15597933579/4611686018427387904), (11443376325/4611686018427387904)), (5/576460752303423488), by norm_num⟩
  | 11 => ⟨((-7863028133/36893488147419103232), (-11537373143/73786976294838206464)), (21/36893488147419103232), by norm_num⟩
  | 12 => ⟨((14533962083/1180591620717411303424), (10662796887/1180591620717411303424)), (41/1180591620717411303424), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791649295455309/5070602400912917605986812821504), (412245808641/5070602400912917605986812821504)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781168425415443/633825300114114700748351602688), (489123323025/316912650057057350374175801344)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892441172704003/39614081257132168796771975168), (275118869363/9903520314283042199192993792)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((118274037914461/154742504910672534362390528), (292298275781/618970019642690137449562112)), (863/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774050465740643/154742504910672534362390528), (1169123252321/154742504910672534362390528)), (863/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776117026416283/4835703278458516698824704), (547989417785/4835703278458516698824704)), (809/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261133817958801/604462909807314587353088), (479453635507/302231454903657293676544)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891602110856507/75557863725914323419136), (1558085178609/75557863725914323419136)), (1151/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300396322239069/4722366482869645213696), (1168442146431/4722366482869645213696)), (863/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406343800844237/147573952589676412928), (1606410141303/590295810358705651712)), (1187/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914190909959389/36893488147419103232), (2007715985089/73786976294838206464)), (371/18446744073709551616), by norm_num⟩
  | 7 => ⟨((914087600285991/4611686018427387904), (1129136285293/4611686018427387904)), (1669/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799710416914657/576460752303423488), (1128881368569/576460752303423488)), (835/576460752303423488), by norm_num⟩
  | 5 => ⟨((599666566929063/72057594037927936), (1974968911243/144115188075855872)), (1461/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498759501386877/36028797018963968), (11567603893/140737488355328)), (2193/36028797018963968), by norm_num⟩
  | 3 => ⟨((1498149016183825/9007199254740992), (3699626841767/9007199254740992)), (1371/4503599627370496), by norm_num⟩
  | 2 => ⟨((70178028842221/140737488355328), (924154531017/562949953421312)), (2745/2251799813685248), by norm_num⟩
  | 1 => ⟨((140165160016883/140737488355328), (1384352125639/281474976710656)), (1031/281474976710656), by norm_num⟩
  | 0 => ⟨((558368426618135/562949953421312), (11044760948641/1125899906842624)), (4137/562949953421312), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((558368426618135/562949953421312), (11044760948641/1125899906842624)), (15781404735374273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1107540026474071/1125899906842624), (10954873973763/562949953421312)), (16577/1125899906842624), by norm_num⟩
  | 2 => ⟨((1089053179359089/1125899906842624), (10776234492235/281474976710656)), (33259/1125899906842624), by norm_num⟩
  | 3 => ⟨((1051762047938739/1125899906842624), (83388531175555/1125899906842624)), (66889/1125899906842624), by norm_num⟩
  | 4 => ⟨((488164956614711/562949953421312), (77897592664127/562949953421312)), (67439/562949953421312), by norm_num⟩
  | 5 => ⟨((1650143061651309/2251799813685248), (270197197546011/1125899906842624)), (16953/70368744177664), by norm_num⟩
  | 6 => ⟨((134944612243897/281474976710656), (792013620568671/2251799813685248)), (1055475/2251799813685248), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1116391677/2147483648), (-12133782039/2147483648)), (1/2147483648), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term2Value_checks : CertifiedScalarExp.Checks term2Value := by
  constructor
  · norm_num [term2Value, CertifiedScalarExp.reduced, term2ValuePoly, term2ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term2ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value, term2ValueSquares, term2ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, term2ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term2 : Sound J_term2 F_term2 c := by
  apply exp_sound (A_arg2 hcre) S_arg2 term2Value term2Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value,J_arg2]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term2,J_arg2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log3 : Sound J_log3 F_log3 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log3_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale (A_log3 hcre) S_log3)
  intro k
  fin_cases k <;> norm_num [J_negLog3, J_log3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/67108864), (-19231589523/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-18874015403/17179869184), 0), (1/17179869184), by norm_num⟩
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
theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul (A_negLog3 hcre) (A_variable hcre) S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg3, J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-440506233854537/1125899906842624), (-223413808230027/1125899906842624)), (1354851/1125899906842624), by norm_num⟩
  | 1 => ⟨((14768846489/34359738368), (3745195849/17179869184)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((-8112618121/34359738368), (-4114518183/34359738368)), (55/68719476736), by norm_num⟩
  | 3 => ⟨((2970873987/34359738368), (3013506825/68719476736)), (21/68719476736), by norm_num⟩
  | 4 => ⟨((-13055354681/549755813888), (-1655337815/137438953472)), (3/34359738368), by norm_num⟩
  | 5 => ⟨((2868554617/549755813888), (5819438289/2199023255552)), (11/549755813888), by norm_num⟩
  | 6 => ⟨((-1050476451/1099511627776), (-2131102139/4398046511104)), (67/17592186044416), by norm_num⟩
  | 7 => ⟨((5275731831/35184372088832), (1337859999/17592186044416)), (87/140737488355328), by norm_num⟩
  | 8 => ⟨((-5795983821/281474976710656), (-2939578871/281474976710656)), (25/281474976710656), by norm_num⟩
  | 9 => ⟨((22640138847/9007199254740992), (11482515453/9007199254740992)), (25/2251799813685248), by norm_num⟩
  | 10 => ⟨((-19898187803/72057594037927936), (-10091866065/72057594037927936)), (45/36028797018963968), by norm_num⟩
  | 11 => ⟨((15898468103/576460752303423488), (8063307691/576460752303423488)), (75/576460752303423488), by norm_num⟩
  | 12 => ⟨((-5822084143/2305843009213693952), (-5905632611/4611686018427387904)), (57/4611686018427387904), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791451234115199/5070602400912917605986812821504), (-3480866763837/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780689975567547/633825300114114700748351602688), (-2063963769689/316912650057057350374175801344)), (181/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((945951216935309/19807040628566084398385987584), (-4643551429441/39614081257132168796771975168)), (1629/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472952900364331/618970019642690137449562112), (-4933355590553/2475880078570760549798248448)), (1731/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886738395571315/77371252455336267181195264), (-4932885364839/154742504910672534362390528)), (433/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551695521826183/9671406556917033397649408), (-1156020064783/2417851639229258349412352)), (1625/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78791368279597/37778931862957161709568), (-2022785140709/302231454903657293676544)), (711/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472708474887439/18889465931478580854784), (-6573113938369/75557863725914323419136)), (2311/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649909499187157/2361183241434822606848), (-4929014534771/4722366482869645213696)), (867/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624579490174343/590295810358705651712), (-1694015074131/147573952589676412928)), (1193/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1827384340590837/73786976294838206464), (-4234036060837/36893488147419103232)), (373/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1827049136770719/9223372036854775808), (-4761912348005/4611686018427387904)), (3361/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1598289899260259/1152921504606846976), (-9520376188403/1152921504606846976)), (3365/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599169045778625/72057594037927936), (-4163222767359/72057594037927936)), (2949/144115188075855872), by norm_num⟩
  | 4 => ⟨((1497256001488753/36028797018963968), (-12481890912501/36028797018963968)), (4431/36028797018963968), by norm_num⟩
  | 3 => ⟨((1496250531031585/9007199254740992), (-3897182617127/2251799813685248)), (2777/4503599627370496), by norm_num⟩
  | 2 => ⟨((560460683978385/1125899906842624), (-15568235356061/2251799813685248)), (5577/2251799813685248), by norm_num⟩
  | 1 => ⟨((279589829710319/281474976710656), (-23300957082141/1125899906842624)), (8423/1125899906842624), by norm_num⟩
  | 0 => ⟨((1110528847703925/1125899906842624), (-46395385884933/1125899906842624)), (8537/562949953421312), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1110528847703925/1125899906842624), (-46395385884933/1125899906842624)), (32566072704124273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1093455805679607/1125899906842624), (-91523969604121/1125899906842624)), (17545/562949953421312), by norm_num⟩
  | 2 => ⟨((1054506670394721/1125899906842624), (-177773202243383/1125899906842624)), (9233/140737488355328), by norm_num⟩
  | 3 => ⟨((959571095001527/1125899906842624), (-333001231181877/1125899906842624)), (161687/1125899906842624), by norm_num⟩
  | 4 => ⟨((719324037129517/1125899906842624), (-70951768025751/140737488355328)), (185623/562949953421312), by norm_num⟩
  | 5 => ⟨((346818136324579/2251799813685248), (-362641914490497/562949953421312)), (1697383/2251799813685248), by norm_num⟩
  | 6 => ⟨((-440506233854537/1125899906842624), (-223413808230027/1125899906842624)), (1354851/1125899906842624), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/67108864), (-19231589523/2147483648)), (1/1073741824), by norm_num⟩, -1, term3ValuePoly, term3ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term3Value_checks : CertifiedScalarExp.Checks term3Value := by
  constructor
  · norm_num [term3Value, CertifiedScalarExp.reduced, term3ValuePoly, term3ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term3ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value, term3ValueSquares, term3ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, term3ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term3 : Sound J_term3 F_term3 c := by
  apply exp_sound (A_arg3 hcre) S_arg3 term3Value term3Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value,J_arg3]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term3,J_arg3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log4 : Sound J_log4 F_log4 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log4_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale (A_log4 hcre) S_log4)
  intro k
  fin_cases k <;> norm_num [J_negLog4, J_log4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1116391677/1073741824), (-12133782039/1073741824)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-23816355775/17179869184), 0), (1/17179869184), by norm_num⟩
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
theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul (A_negLog4 hcre) (A_variable hcre) S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg4, J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((14936871760233/140737488355328), (1518827316992817/4503599627370496)), (3537391/4503599627370496), by norm_num⟩
  | 1 => ⟨((-5055395775/34359738368), (-16064008675/34359738368)), (39/34359738368), by norm_num⟩
  | 2 => ⟨((219008333/2147483648), (5567361161/17179869184)), (7/8589934592), by norm_num⟩
  | 3 => ⟨((-3238506849/68719476736), (-321583391/2147483648)), (27/68719476736), by norm_num⟩
  | 4 => ⟨((4489523783/274877906944), (14265895731/274877906944)), (39/274877906944), by norm_num⟩
  | 5 => ⟨((-1244760301/274877906944), (-15821384647/1099511627776)), (45/1099511627776), by norm_num⟩
  | 6 => ⟨((4601611163/4398046511104), (7311032107/2199023255552)), (11/1099511627776), by norm_num⟩
  | 7 => ⟨((-7290500123/35184372088832), (-5791567191/8796093022208)), (9/4398046511104), by norm_num⟩
  | 8 => ⟨((5053389605/140737488355328), (8028816939/70368744177664)), (13/35184372088832), by norm_num⟩
  | 9 => ⟨((-6227098235/1125899906842624), (-19787206487/1125899906842624)), (33/562949953421312), by norm_num⟩
  | 10 => ⟨((863259117/1125899906842624), (21944714221/9007199254740992)), (19/2251799813685248), by norm_num⟩
  | 11 => ⟨((-6962799977/72057594037927936), (-22124969877/72057594037927936)), (79/72057594037927936), by norm_num⟩
  | 12 => ⟨((1608748391/144115188075855872), (20447813987/576460752303423488)), (75/576460752303423488), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791310707357927/5070602400912917605986812821504), (412245808641/2535301200456458802993406410752)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780363781143673/633825300114114700748351602688), (977409496577/316912650057057350374175801344)), (361/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472883980253389/9903520314283042199192993792), (1099482329917/19807040628566084398385987584)), (1625/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891422740302319/2475880078570760549798248448), (1168075874071/1237940039285380274899124224)), (1727/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886544279246319/77371252455336267181195264), (2335872536865/154742504910672534362390528)), (1727/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193916527668759/1208925819614629174706176), (273697983169/1208925819614629174706176)), (405/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630172336008937/302231454903657293676544), (957794635621/302231454903657293676544)), (1417/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472579916858041/18889465931478580854784), (3112276477681/75557863725914323419136)), (9/295147905179352825856), by norm_num⟩
  | 10 => ⟨((649717209326085/2361183241434822606848), (2333720838623/4722366482869645213696)), (27/73786976294838206464), by norm_num⟩
  | 9 => ⟨((812026235356901/295147905179352825856), (3208075666419/590295810358705651712)), (2377/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913364115773855/36893488147419103232), (4008909041567/73786976294838206464)), (743/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1826314676903841/9223372036854775808), (4508392858793/9223372036854775808)), (3345/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199695001870565/144115188075855872), (2253178026279/576460752303423488)), (1673/576460752303423488), by norm_num⟩
  | 5 => ⟨((149713073284297/18014398509481984), (3940770771735/144115188075855872)), (1465/72057594037927936), by norm_num⟩
  | 4 => ⟨((1496316020403079/36028797018963968), (5906576191863/36028797018963968)), (4399/36028797018963968), by norm_num⟩
  | 3 => ⟨((186886689545327/1125899906842624), (230475276981/281474976710656)), (2753/4503599627370496), by norm_num⟩
  | 2 => ⟨((1119791250199011/2251799813685248), (7363198931889/2251799813685248)), (1379/562949953421312), by norm_num⟩
  | 1 => ⟨((2181115672913/2199023255552), (11014798561747/1125899906842624)), (4151/562949953421312), by norm_num⟩
  | 0 => ⟨((553770013237035/562949953421312), (21909747947525/1125899906842624)), (16711/1125899906842624), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((553770013237035/562949953421312), (21909747947525/1125899906842624)), (63747410300826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1089053179359087/1125899906842624), (21552468984469/562949953421312)), (4191/140737488355328), by norm_num⟩
  | 2 => ⟨((1051762047938735/1125899906842624), (83388531175551/1125899906842624)), (33715/562949953421312), by norm_num⟩
  | 3 => ⟨((976329913229415/1125899906842624), (77897592664123/562949953421312)), (135969/1125899906842624), by norm_num⟩
  | 4 => ⟨((1650143061651289/2251799813685248), (270197197545995/1125899906842624)), (136721/562949953421312), by norm_num⟩
  | 5 => ⟨((539778448975581/1125899906842624), (792013620568615/2251799813685248)), (266003/562949953421312), by norm_num⟩
  | 6 => ⟨((14936871760233/140737488355328), (1518827316992817/4503599627370496)), (3537391/4503599627370496), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1116391677/1073741824), (-12133782039/1073741824)), (1/1073741824), by norm_num⟩, -2, term4ValuePoly, term4ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term4Value_checks : CertifiedScalarExp.Checks term4Value := by
  constructor
  · norm_num [term4Value, CertifiedScalarExp.reduced, term4ValuePoly, term4ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term4ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value, term4ValueSquares, term4ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, term4ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term4 : Sound J_term4 F_term4 c := by
  apply exp_sound (A_arg4 hcre) S_arg4 term4Value term4Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value,J_arg4]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term4,J_arg4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/10000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log5 : Sound J_log5 F_log5 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log5_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale (A_log5 hcre) S_log5)
  intro k
  fin_cases k <;> norm_num [J_negLog5, J_log5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-162011325/134217728), (-7043442353/536870912)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-27649932795/17179869184), 0), (1/17179869184), by norm_num⟩
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
theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul (A_negLog5 hcre) (A_variable hcre) S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg5, J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((286523826125631/1125899906842624), (-88439546541439/562949953421312)), (2033033/4503599627370496), by norm_num⟩
  | 1 => ⟨((-14072946429/34359738368), (4343809789/17179869184)), (27/34359738368), by norm_num⟩
  | 2 => ⟨((11324766761/34359738368), (-6991092159/34359738368)), (23/34359738368), by norm_num⟩
  | 3 => ⟨((-12151005983/68719476736), (7501152513/68719476736)), (13/34359738368), by norm_num⟩
  | 4 => ⟨((19556289703/274877906944), (-12072639241/274877906944)), (11/68719476736), by norm_num⟩
  | 5 => ⟨((-6294926815/274877906944), (7772065319/549755813888)), (15/274877906944), by norm_num⟩
  | 6 => ⟨((13508391829/2199023255552), (-2084776097/549755813888)), (17/1099511627776), by norm_num⟩
  | 7 => ⟨((-12423381683/8796093022208), (958662197/1099511627776)), (33/8796093022208), by norm_num⟩
  | 8 => ⟨((19994661481/70368744177664), (-1542907285/8796093022208)), (55/70368744177664), by norm_num⟩
  | 9 => ⟨((-1787787013/35184372088832), (2207300871/70368744177664)), (41/281474976710656), by norm_num⟩
  | 10 => ⟨((18414926067/2251799813685248), (-11368043859/2251799813685248)), (55/2251799813685248), by norm_num⟩
  | 11 => ⟨((-5388669121/4503599627370496), (6653149373/9007199254740992)), (17/4503599627370496), by norm_num⟩
  | 12 => ⟨((11563637841/72057594037927936), (-1784638473/18014398509481984)), (19/36028797018963968), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582403412673403/10141204801825835211973625643008), (-720426461461/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890053515737273/316912650057057350374175801344), (-426903981761/316912650057057350374175801344)), (1443/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945623602499243/19807040628566084398385987584), (-960430598275/39614081257132168796771975168)), (1623/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891116136760481/2475880078570760549798248448), (-249104443/604462909807314587353088)), (1725/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886391065888511/77371252455336267181195264), (-1020190397693/154742504910672534362390528)), (1725/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551045134130061/9671406556917033397649408), (-956278285271/9671406556917033397649408)), (1617/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260093658467775/604462909807314587353088), (-836593316093/604462909807314587353088)), (1415/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944956061176465/37778931862957161709568), (-1359182606265/75557863725914323419136)), (2299/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324782266916443/1180591620717411303424), (-1019140675559/4722366482869645213696)), (1725/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405908278271783/147573952589676412928), (-87557396309/36893488147419103232)), (593/147573952589676412928), by norm_num⟩
  | 8 => ⟨((456551196019137/18446744073709551616), (-437636999147/18446744073709551616)), (2965/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912863414242605/4611686018427387904), (-1968541921643/9223372036854775808)), (417/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1596973453036979/1152921504606846976), (-491877924075/288230376151711744)), (3337/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197192790527001/144115188075855872), (-860207204015/72057594037927936)), (2921/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495551215254331/36028797018963968), (-644576662947/9007199254740992)), (4383/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494142557094927/9007199254740992), (-3218835939043/9007199254740992)), (5481/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118847846380827/2251799813685248), (-6425544956495/4503599627370496)), (10971/4503599627370496), by norm_num⟩
  | 1 => ⟨((1115334953929745/1125899906842624), (-9608053289039/2251799813685248)), (515/70368744177664), by norm_num⟩
  | 0 => ⟨((276205626319565/281474976710656), (-19095368458035/2251799813685248)), (16527/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((276205626319565/281474976710656), (-19095368458035/2251799813685248)), (63045506003951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((67753669890935/70368744177664), (-4684473435605/281474976710656)), (8179/281474976710656), by norm_num⟩
  | 2 => ⟨((1043460603222965/1125899906842624), (-36083095752569/1125899906842624)), (128179/2251799813685248), by norm_num⟩
  | 3 => ⟨((58953929015/68719476736), (-33441062239461/562949953421312)), (61451/562949953421312), by norm_num⟩
  | 4 => ⟨((1649332861207011/2251799813685248), (-229510712606295/2251799813685248)), (450951/2251799813685248), by norm_num⟩
  | 5 => ⟨((592331454964125/1125899906842624), (-42026333557721/281474976710656)), (752525/2251799813685248), by norm_num⟩
  | 6 => ⟨((286523826125631/1125899906842624), (-88439546541439/562949953421312)), (2033033/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-162011325/134217728), (-7043442353/536870912)), (1/1073741824), by norm_num⟩, -2, term5ValuePoly, term5ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term5Value_checks : CertifiedScalarExp.Checks term5Value := by
  constructor
  · norm_num [term5Value, CertifiedScalarExp.reduced, term5ValuePoly, term5ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term5ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value, term5ValueSquares, term5ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, term5ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term5 : Sound J_term5 F_term5 c := by
  apply exp_sound (A_arg5 hcre) S_arg5 term5Value term5Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value,J_arg5]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term5,J_arg5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((358351893845611/200000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log6 : Sound J_log6 F_log6 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log6_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale (A_log6 hcre) S_log6)
  intro k
  fin_cases k <;> norm_num [J_negLog6, J_log6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2885830621/2147483648), (-15682685781/1073741824)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((-30782193291/17179869184), 0), (1/17179869184), by norm_num⟩
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
theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul (A_negLog6 hcre) (A_variable hcre) S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg6, J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-265214307588169/2251799813685248), (-524091752156889/2251799813685248)), (201673/281474976710656), by norm_num⟩
  | 1 => ⟨((7250980331/34359738368), (7164355161/17179869184)), (23/17179869184), by norm_num⟩
  | 2 => ⟨((-6496006335/34359738368), (-12836801201/34359738368)), (43/34359738368), by norm_num⟩
  | 3 => ⟨((7759520575/68719476736), (15333640071/68719476736)), (53/68719476736), by norm_num⟩
  | 4 => ⟨((-3475798617/68719476736), (-6868548699/68719476736)), (49/137438953472), by norm_num⟩
  | 5 => ⟨((1245559017/68719476736), (9845429737/274877906944)), (9/68719476736), by norm_num⟩
  | 6 => ⟨((-5951312435/1099511627776), (-11760427973/1099511627776)), (45/1099511627776), by norm_num⟩
  | 7 => ⟨((6093325949/4398046511104), (12041061819/4398046511104)), (3/274877906944), by norm_num⟩
  | 8 => ⟨((-2729443617/8796093022208), (-10787343267/17592186044416)), (11/4398046511104), by norm_num⟩
  | 9 => ⟨((8694233683/140737488355328), (8590366421/70368744177664)), (9/17592186044416), by norm_num⟩
  | 10 => ⟨((-1557797553/140737488355328), (-12313496303/562949953421312)), (53/562949953421312), by norm_num⟩
  | 11 => ⟨((8119850231/4503599627370496), (16045689891/4503599627370496)), (71/4503599627370496), by norm_num⟩
  | 12 => ⟨((-1212401545/4503599627370496), (-19166677869/36028797018963968)), (87/36028797018963968), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646017817/5070602400912917605986812821504), (-2656375146555/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779891055938133/633825300114114700748351602688), (-1573736718861/316912650057057350374175801344)), (723/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945501986280619/19807040628566084398385987584), (-3540475053671/39614081257132168796771975168)), (1627/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890857373780697/2475880078570760549798248448), (-1880618858863/1237940039285380274899124224)), (1729/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886261499695215/77371252455336267181195264), (-940164014515/38685626227668133590597632)), (865/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775400902597495/4835703278458516698824704), (-220312316965/604462909807314587353088)), (811/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259880353520483/604462909807314587353088), (-3083754488671/604462909807314587353088)), (355/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944782383491335/37778931862957161709568), (-5009942462699/75557863725914323419136)), (577/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((81179244285755/295147905179352825856), (-1878221580555/2361183241434822606848)), (433/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1623272975934029/590295810358705651712), (-5163462243679/590295810358705651712)), (1191/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825753048884095/73786976294838206464), (-6451857390177/73786976294838206464)), (2979/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825216478425297/9223372036854775808), (-7254943134837/9223372036854775808)), (3353/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399115105324737/288230376151711744), (-3625349093103/576460752303423488)), (839/288230376151711744), by norm_num⟩
  | 5 => ⟨((1196740875379025/144115188075855872), (-1584896539155/36028797018963968)), (735/36028797018963968), by norm_num⟩
  | 4 => ⟨((1494867329046881/36028797018963968), (-9499831757743/36028797018963968)), (4417/36028797018963968), by norm_num⟩
  | 3 => ⟨((746638600534807/4503599627370496), (-11858086214295/9007199254740992)), (1383/2251799813685248), by norm_num⟩
  | 2 => ⟨((558983396785027/1125899906842624), (-11833040250417/2251799813685248)), (2775/1125899906842624), by norm_num⟩
  | 1 => ⟨((1113974309655725/1125899906842624), (-17686978129203/1125899906842624)), (523/70368744177664), by norm_num⟩
  | 0 => ⟨((1101946015999289/1125899906842624), (-35123825260153/1125899906842624)), (16911/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1101946015999289/1125899906842624), (-35123825260153/1125899906842624)), (64510349753951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((134675752669433/140737488355328), (-68753108649987/1125899906842624)), (34159/1125899906842624), by norm_num⟩
  | 2 => ⟨((256700604085219/281474976710656), (-131583656408911/1125899906842624)), (17387/281474976710656), by norm_num⟩
  | 3 => ⟨((230262241178619/281474976710656), (-240004312160447/1125899906842624)), (143111/1125899906842624), by norm_num⟩
  | 4 => ⟨((702308545138307/1125899906842624), (-785347691740375/2251799813685248)), (295159/1125899906842624), by norm_num⟩
  | 5 => ⟨((602264093430097/2251799813685248), (-979760974242635/2251799813685248)), (1148217/2251799813685248), by norm_num⟩
  | 6 => ⟨((-265214307588169/2251799813685248), (-524091752156889/2251799813685248)), (201673/281474976710656), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2885830621/2147483648), (-15682685781/1073741824)), (1/1073741824), by norm_num⟩, -2, term6ValuePoly, term6ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term6Value_checks : CertifiedScalarExp.Checks term6Value := by
  constructor
  · norm_num [term6Value, CertifiedScalarExp.reduced, term6ValuePoly, term6ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term6ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value, term6ValueSquares, term6ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, term6ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term6 : Sound J_term6 F_term6 c := by
  apply exp_sound (A_arg6 hcre) S_arg6 term6Value term6Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value,J_arg6]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term6,J_arg6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1945910149055313/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log7 : Sound J_log7 F_log7 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log7_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale (A_log7 hcre) S_log7)
  intro k
  fin_cases k <;> norm_num [J_negLog7, J_log7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1567053835/1073741824), (-17031916365/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-33430481805/17179869184), 0), (1/17179869184), by norm_num⟩
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
theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul (A_negLog7 hcre) (A_variable hcre) S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg7, J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-517034322392979/2251799813685248), (40194228934705/1125899906842624)), (1365841/1125899906842624), by norm_num⟩
  | 1 => ⟨((15351903311/34359738368), (-2386912781/34359738368)), (83/34359738368), by norm_num⟩
  | 2 => ⟨((-7468356115/17179869184), (2322358903/34359738368)), (41/17179869184), by norm_num⟩
  | 3 => ⟨((4844249987/17179869184), (-1506367253/34359738368)), (27/17179869184), by norm_num⟩
  | 4 => ⟨((-18852950429/137438953472), (1465627663/68719476736)), (107/137438953472), by norm_num⟩
  | 5 => ⟨((1834307379/34359738368), (-4563167591/549755813888)), (21/68719476736), by norm_num⟩
  | 6 => ⟨((-9518392921/549755813888), (1479919021/549755813888)), (111/1099511627776), by norm_num⟩
  | 7 => ⟨((21167928443/4398046511104), (-3291187935/4398046511104)), (125/4398046511104), by norm_num⟩
  | 8 => ⟨((-5148860849/4398046511104), (3202178003/17592186044416)), (123/17592186044416), by norm_num⟩
  | 9 => ⟨((8905973851/35184372088832), (-692350075/17592186044416)), (27/17592186044416), by norm_num⟩
  | 10 => ⟨((-27728359847/562949953421312), (4311203321/562949953421312)), (171/562949953421312), by norm_num⟩
  | 11 => ⟨((19620689761/2251799813685248), (-3050623381/2251799813685248)), (123/2251799813685248), by norm_num⟩
  | 12 => ⟨((-25453399559/18014398509481984), (3957492665/18014398509481984)), (81/9007199254740992), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197759336647691/1267650600228229401496703205376), (1945676973409/5070602400912917605986812821504)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222463321225089/79228162514264337593543950336), (4609890685175/633825300114114700748351602688)), (181/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((945398049698479/19807040628566084398385987584), (2592712178737/19807040628566084398385987584)), (3259/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890636092559489/2475880078570760549798248448), (5508689104105/2475880078570760549798248448)), (433/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1772301250402683/154742504910672534362390528), (1376940396345/38685626227668133590597632)), (3465/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387648354691599/2417851639229258349412352), (5162540914011/9671406556917033397649408)), (1625/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259697518923077/604462909807314587353088), (4516237633299/604462909807314587353088)), (2845/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944633365235775/37778931862957161709568), (917129728733/9444732965739290427392)), (4625/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298643567780053/4722366482869645213696), (687645111201/590295810358705651712)), (3471/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622963186672109/590295810358705651712), (7561467441597/590295810358705651712)), (4775/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912681916625321/36893488147419103232), (1180986310101/9223372036854775808)), (2987/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824775892809411/9223372036854775808), (1327931623371/1152921504606846976)), (841/1152921504606846976), by norm_num⟩
  | 6 => ⟨((199502055363505/144115188075855872), (10616671665099/1152921504606846976)), (421/72057594037927936), by norm_num⟩
  | 5 => ⟨((1196348583959755/144115188075855872), (4640978288963/72057594037927936)), (369/9007199254740992), by norm_num⟩
  | 4 => ⟨((1494271287622995/36028797018963968), (3476916822947/9007199254740992)), (2219/9007199254740992), by norm_num⟩
  | 3 => ⟨((186564859822017/1125899906842624), (17357853998843/9007199254740992)), (11129/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117188638595445/2251799813685248), (17317735365357/2251799813685248)), (2795/562949953421312), by norm_num⟩
  | 1 => ⟨((556378876740035/562949953421312), (12938112760255/562949953421312)), (16899/1125899906842624), by norm_num⟩
  | 0 => ⟨((549658576560091/562949953421312), (25675232284583/562949953421312)), (17157/562949953421312), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((549658576560091/562949953421312), (25675232284583/562949953421312)), (65448763133811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((535510006530867/562949953421312), (100276136765797/1125899906842624)), (70139/1125899906842624), by norm_num⟩
  | 2 => ⟨((1009884233814947/1125899906842624), (190776726520675/1125899906842624)), (145935/1125899906842624), by norm_num⟩
  | 3 => ⟨((436748595656259/562949953421312), (85559296666229/281474976710656)), (77813/281474976710656), by norm_num⟩
  | 4 => ⟨((143412182417211/281474976710656), (1062059671548717/2251799813685248)), (1344347/2251799813685248), by norm_num⟩
  | 5 => ⟨((41815598599847/1125899906842624), (541121975154041/1125899906842624)), (1319009/1125899906842624), by norm_num⟩
  | 6 => ⟨((-517034322392979/2251799813685248), (40194228934705/1125899906842624)), (1365841/1125899906842624), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1567053835/1073741824), (-17031916365/1073741824)), (1/536870912), by norm_num⟩, -3, term7ValuePoly, term7ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term7Value_checks : CertifiedScalarExp.Checks term7Value := by
  constructor
  · norm_num [term7Value, CertifiedScalarExp.reduced, term7ValuePoly, term7ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term7ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value, term7ValueSquares, term7ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, term7ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term7 : Sound J_term7 F_term7 c := by
  apply exp_sound (A_arg7 hcre) S_arg7 term7Value term7Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value,J_arg7]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term7,J_arg7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((519860385419959/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log8 : Sound J_log8 F_log8 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log8_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale (A_log8 hcre) S_log8)
  intro k
  fin_cases k <;> norm_num [J_negLog8, J_log8, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1674587515/1073741824), (-9100336529/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-17862266831/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul (A_negLog8 hcre) (A_variable hcre) S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg8, J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-305056171189209/4503599627370496), (224068219059699/1125899906842624)), (5105529/4503599627370496), by norm_num⟩
  | 1 => ⟨((4839679527/34359738368), (-14219261563/34359738368)), (83/34359738368), by norm_num⟩
  | 2 => ⟨((-78623677/536870912), (14784061593/34359738368)), (11/4294967296), by norm_num⟩
  | 3 => ⟨((6975715845/68719476736), (-20495061221/68719476736)), (31/17179869184), by norm_num⟩
  | 4 => ⟨((-453299791/8589934592), (21309140851/137438953472)), (33/34359738368), by norm_num⟩
  | 5 => ⟨((754088333/34359738368), (-17724445081/274877906944)), (7/17179869184), by norm_num⟩
  | 6 => ⟨((-8363107231/1099511627776), (12285649135/549755813888)), (79/549755813888), by norm_num⟩
  | 7 => ⟨((4968740741/2199023255552), (-14598450959/2199023255552)), (3/68719476736), by norm_num⟩
  | 8 => ⟨((-5166102953/8796093022208), (3794578171/2199023255552)), (51/4398046511104), by norm_num⟩
  | 9 => ⟨((18650363/137438953472), (-14027739523/35184372088832)), (97/35184372088832), by norm_num⟩
  | 10 => ⟨((-1985655787/70368744177664), (1458493215/17592186044416)), (41/70368744177664), by norm_num⟩
  | 11 => ⟨((1501474593/281474976710656), (-8822840377/562949953421312)), (63/562949953421312), by norm_num⟩
  | 12 => ⟨((-8325943047/9007199254740992), (1528881733/562949953421312)), (89/4503599627370496), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49435757453803/316912650057057350374175801344), (618368713113/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779558805178961/633825300114114700748351602688), (1464858521017/316912650057057350374175801344)), (2891/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945315141328769/19807040628566084398385987584), (823867370721/9903520314283042199192993792)), (3253/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472615109850111/618970019642690137449562112), (3500878241137/2475880078570760549798248448)), (3457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772126190043677/154742504910672534362390528), (1750125224135/77371252455336267181195264)), (1729/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775214964632827/4835703278458516698824704), (1640408923295/4835703278458516698824704)), (3243/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259555094898889/604462909807314587353088), (2870048758445/604462909807314587353088)), (1419/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944518235359099/37778931862957161709568), (4662579069153/75557863725914323419136)), (4613/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298471904209385/4722366482869645213696), (1747920301591/2361183241434822606848)), (3461/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622728823851609/590295810358705651712), (600625491665/73786976294838206464)), (4761/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825073389538657/73786976294838206464), (3001795105187/36893488147419103232)), (2977/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912226295631577/4611686018427387904), (3375188026245/4611686018427387904)), (6703/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595697445852741/1152921504606846976), (3372899470541/576460752303423488)), (1677/288230376151711744), by norm_num⟩
  | 5 => ⟨((1196074297149935/144115188075855872), (1474356741125/36028797018963968)), (1469/36028797018963968), by norm_num⟩
  | 4 => ⟨((746934755643907/18014398509481984), (552240724167/2251799813685248)), (4413/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492033513412585/9007199254740992), (1378352630649/1125899906842624)), (5527/4503599627370496), by norm_num⟩
  | 2 => ⟨((558364239121783/1125899906842624), (10999855051617/2251799813685248)), (11087/2251799813685248), by norm_num⟩
  | 1 => ⟨((278032562929015/281474976710656), (4108113074791/281474976710656)), (16711/1125899906842624), by norm_num⟩
  | 0 => ⟨((1098311464955935/1125899906842624), (32596092776807/1125899906842624)), (33749/1125899906842624), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1098311464955935/1125899906842624), (32596092776807/1125899906842624)), (128742222312545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1070455341069499/1125899906842624), (15898687881559/281474976710656)), (67799/1125899906842624), by norm_num⟩
  | 2 => ⟨((253537267803091/281474976710656), (7557881147063/70368744177664)), (136581/1125899906842624), by norm_num⟩
  | 3 => ⟨((450251044171965/562949953421312), (435694468343819/2251799813685248)), (550777/2251799813685248), by norm_num⟩
  | 4 => ⟨((1356153578192171/2251799813685248), (696942554554005/2251799813685248)), (1094167/2251799813685248), by norm_num⟩
  | 5 => ⟨((601040818579775/2251799813685248), (419735863467355/1125899906842624)), (62351/70368744177664), by norm_num⟩
  | 6 => ⟨((-305056171189209/4503599627370496), (224068219059699/1125899906842624)), (5105529/4503599627370496), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1674587515/1073741824), (-9100336529/536870912)), (1/536870912), by norm_num⟩, -3, term8ValuePoly, term8ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term8Value_checks : CertifiedScalarExp.Checks term8Value := by
  constructor
  · norm_num [term8Value, CertifiedScalarExp.reduced, term8ValuePoly, term8ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term8ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value, term8ValueSquares, term8ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, term8ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term8 : Sound J_term8 F_term8 c := by
  apply exp_sound (A_arg8 hcre) S_arg8 term8Value term8Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value,J_arg8]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term8,J_arg8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term2Jet : Jet 12 := J_term2
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile018Terms0

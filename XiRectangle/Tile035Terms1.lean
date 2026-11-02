/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile035Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨35,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (8601/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (8601/640))
  have he : value ((5/8), (8601/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-46079139/33554432), (-495408345/16777216)), (3/67108864), by norm_num⟩
  | 1 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-355014389320239/4503599627370496), (542005991464191/2251799813685248)), (73439247/2251799813685248), by norm_num⟩
  | 1 => ⟨((371955081/2147483648), (-567869609/1073741824)), (39/536870912), by norm_num⟩
  | 2 => ⟨((-408634423/2147483648), (623868531/1073741824)), (173/2147483648), by norm_num⟩
  | 3 => ⟨((299287199/2147483648), (-456926423/1073741824)), (129/2147483648), by norm_num⟩
  | 4 => ⟨((-328800595/4294967296), (1003969967/4294967296)), (9/268435456), by norm_num⟩
  | 5 => ⟨((288979499/8589934592), (-882378995/8589934592)), (129/8589934592), by norm_num⟩
  | 6 => ⟨((-423301905/34359738368), (646261605/17179869184)), (191/34359738368), by norm_num⟩
  | 7 => ⟨((132869907/34359738368), (-405709109/34359738368)), (61/34359738368), by norm_num⟩
  | 8 => ⟨((-291945025/274877906944), (445717013/137438953472)), (17/34359738368), by norm_num⟩
  | 9 => ⟨((285097237/1099511627776), (-435262389/549755813888)), (135/1099511627776), by norm_num⟩
  | 10 => ⟨((-501138125/8796093022208), (765095375/4398046511104)), (15/549755813888), by norm_num⟩
  | 11 => ⟨((400404729/35184372088832), (-152826033/4398046511104)), (97/17592186044416), by norm_num⟩
  | 12 => ⟨((-36657463/17592186044416), (895448309/140737488355328)), (9/8796093022208), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791093467826773/5070602400912917605986812821504), (153650217783/633825300114114700748351602688)), (58233/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779846368637259/633825300114114700748351602688), (2912760309095/633825300114114700748351602688)), (69365/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890953750353845/39614081257132168796771975168), (819112036719/9903520314283042199192993792)), (39025/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890804076230973/2475880078570760549798248448), (217546087849/154742504910672534362390528)), (82943/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443117443326795/38685626227668133590597632), (3480187579847/154742504910672534362390528)), (41481/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550751981649087/9671406556917033397649408), (1631045856203/4835703278458516698824704)), (77795/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259836833795751/604462909807314587353088), (2853746156519/604462909807314587353088)), (34045/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236186773704879/9444732965739290427392), (2318121221217/37778931862957161709568)), (55341/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298815099935203/4722366482869645213696), (3476223763021/4722366482869645213696)), (83043/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623200566044583/590295810358705651712), (2389125509727/295147905179352825856)), (114235/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825662839298033/73786976294838206464), (2985239577527/36893488147419103232)), (71435/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912557704313363/4611686018427387904), (6713579538121/9223372036854775808)), (160833/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798179935493123/576460752303423488), (6709568535365/1152921504606846976)), (160965/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299163369398659/36028797018963968), (5866361310963/144115188075855872)), (2203/2251799813685248), by norm_num⟩
  | 4 => ⟨((747368699071489/18014398509481984), (4395261354259/18014398509481984)), (211785/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493116823704443/9007199254740992), (5486188288843/4503599627370496)), (265249/9007199254740992), by norm_num⟩
  | 2 => ⟨((139726182866029/281474976710656), (10948725190167/2251799813685248)), (66507/562949953421312), by norm_num⟩
  | 1 => ⟨((556872951824587/562949953421312), (16364007870673/1125899906842624)), (12531/35184372088832), by norm_num⟩
  | 0 => ⟨((275379850686375/281474976710656), (32491988753493/1125899906842624)), (404901/562949953421312), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((275379850686375/281474976710656), (32491988753493/1125899906842624)), (1544574739696311773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((67295572741635/70368744177664), (31788399508913/562949953421312)), (1631273/1125899906842624), by norm_num⟩
  | 2 => ⟨((16033059365519/17592186044416), (121600496157283/1125899906842624)), (826073/281474976710656), by norm_num⟩
  | 3 => ⟨((922041956651293/1125899906842624), (221647039071091/1125899906842624)), (6736639/1125899906842624), by norm_num⟩
  | 4 => ⟨((1422922153253771/2251799813685248), (726060525803527/2251799813685248)), (13686155/1125899906842624), by norm_num⟩
  | 5 => ⟨((665042939425155/2251799813685248), (57350102820537/140737488355328)), (52244983/2251799813685248), by norm_num⟩
  | 6 => ⟨((-355014389320239/4503599627370496), (542005991464191/2251799813685248)), (73439247/2251799813685248), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-46079139/33554432), (-495408345/16777216)), (3/67108864), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-48288709/33554432), (-259581993/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((951520041862485/4503599627370496), (242473370592767/2251799813685248)), (97664129/4503599627370496), by norm_num⟩
  | 1 => ⟨((-65295573/134217728), (-266225609/1073741824)), (109/2147483648), by norm_num⟩
  | 2 => ⟨((150348613/268435456), (613007119/2147483648)), (1/16777216), by norm_num⟩
  | 3 => ⟨((-115396825/268435456), (-470500351/2147483648)), (101/2147483648), by norm_num⟩
  | 4 => ⟨((265711009/1073741824), (541683547/4294967296)), (119/4294967296), by norm_num⟩
  | 5 => ⟨((-489457767/4294967296), (-62363623/1073741824)), (7/536870912), by norm_num⟩
  | 6 => ⟨((751345439/17179869184), (95731699/4294967296)), (11/2147483648), by norm_num⟩
  | 7 => ⟨((-494296231/34359738368), (-125960219/17179869184)), (59/34359738368), by norm_num⟩
  | 8 => ⟨((1138159133/274877906944), (580068245/274877906944)), (69/137438953472), by norm_num⟩
  | 9 => ⟨((-145594903/137438953472), (-148406277/274877906944)), (9/68719476736), by norm_num⟩
  | 10 => ⟨((1072782891/4398046511104), (273374465/2199023255552)), (135/4398046511104), by norm_num⟩
  | 11 => ⟨((-224561263/4398046511104), (-228897443/8796093022208)), (115/17592186044416), by norm_num⟩
  | 12 => ⟨((1378857111/140737488355328), (5490165/1099511627776)), (179/140737488355328), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395525289565701/2535301200456458802993406410752), (613975020735/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779748991933439/633825300114114700748351602688), (727369592835/633825300114114700748351602688)), (5767/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1890844464285765/39614081257132168796771975168), (204546610211/9903520314283042199192993792)), (51905/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472672072604339/618970019642690137449562112), (869195443217/2475880078570760549798248448)), (3447/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1772354359290439/154742504910672534362390528), (434525934943/77371252455336267181195264)), (55155/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775322087940367/4835703278458516698824704), (203645903437/2417851639229258349412352)), (51711/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629871449219381/302231454903657293676544), (356304092101/302231454903657293676544)), (90501/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889342284341587/75557863725914323419136), (1157702480823/75557863725914323419136)), (147075/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324675454444001/1180591620717411303424), (868026846823/4722366482869645213696)), (110317/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623045853423695/590295810358705651712), (1193130787035/590295810358705651712)), (151703/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825471022776483/73786976294838206464), (93175284159/4611686018427387904)), (189653/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912450888790679/4611686018427387904), (838159119167/4611686018427387904)), (213395/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596148940031331/1152921504606846976), (1675272760627/1152921504606846976)), (213439/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196471946369985/144115188075855872), (1464688352281/144115188075855872)), (23351/18014398509481984), by norm_num⟩
  | 4 => ⟨((1494471157433927/36028797018963968), (1097342011579/18014398509481984)), (35039/4503599627370496), by norm_num⟩
  | 3 => ⟨((1492794597228537/9007199254740992), (2739249913187/9007199254740992)), (350563/9007199254740992), by norm_num⟩
  | 2 => ⟨((2235006100995797/4503599627370496), (2733101765425/2251799813685248)), (350823/2251799813685248), by norm_num⟩
  | 1 => ⟨((2226651307756909/2251799813685248), (1021078892439/281474976710656)), (1053775/2251799813685248), by norm_num⟩
  | 0 => ⟨((2201670766632083/2251799813685248), (8107482176297/1125899906842624)), (2112795/2251799813685248), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2201670766632083/2251799813685248), (8107482176297/1125899906842624)), (8059673317916106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2152540918653289/2251799813685248), (31707981127027/2251799813685248)), (2080975/1125899906842624), by norm_num⟩
  | 2 => ⟨((514302712685221/562949953421312), (30310299525299/1125899906842624)), (8074195/2251799813685248), by norm_num⟩
  | 3 => ⟨((938902650599433/1125899906842624), (55382078543299/1125899906842624)), (3796915/562949953421312), by norm_num⟩
  | 4 => ⟨((780238995793483/1125899906842624), (92367678554711/1125899906842624)), (26824515/2251799813685248), by norm_num⟩
  | 5 => ⟨((1066242387742087/2251799813685248), (256040041645999/2251799813685248)), (41579631/2251799813685248), by norm_num⟩
  | 6 => ⟨((951520041862485/4503599627370496), (242473370592767/2251799813685248)), (97664129/4503599627370496), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-48288709/33554432), (-259581993/8388608)), (1/16777216), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-50287509/33554432), (-1081307155/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((173529514219307/1125899906842624), (-728465518152565/4503599627370496)), (28758345/1125899906842624), by norm_num⟩
  | 1 => ⟨((-793658451/2147483648), (832931529/2147483648)), (67/1073741824), by norm_num⟩
  | 2 => ⟨((237888731/536870912), (-124830161/268435456)), (163/2147483648), by norm_num⟩
  | 3 => ⟨((-760576351/2147483648), (99776551/268435456)), (33/536870912), by norm_num⟩
  | 4 => ⟨((455945609/2147483648), (-29906715/134217728)), (161/4294967296), by norm_num⟩
  | 5 => ⟨((-54665491/536870912), (917928583/8589934592)), (157/8589934592), by norm_num⟩
  | 6 => ⟨((699104653/17179869184), (-366849435/8589934592)), (127/17179869184), by norm_num⟩
  | 7 => ⟨((-478965641/34359738368), (1005333173/68719476736)), (177/68719476736), by norm_num⟩
  | 8 => ⟨((574254723/137438953472), (-150667729/34359738368)), (27/34359738368), by norm_num⟩
  | 9 => ⟨((-306000597/274877906944), (321142609/274877906944)), (117/549755813888), by norm_num⟩
  | 10 => ⟨((146751477/549755813888), (-616053075/2199023255552)), (57/1099511627776), by norm_num⟩
  | 11 => ⟨((-511846797/8796093022208), (1074349641/17592186044416)), (201/17592186044416), by norm_num⟩
  | 12 => ⟨((818236677/70368744177664), (-858725975/70368744177664)), (163/70368744177664), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791011781571557/5070602400912917605986812821504), (-1054513496913/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779656519293525/633825300114114700748351602688), (-312287022965/158456325028528675187087900672)), (92323/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472685103507099/9903520314283042199192993792), (-1405104802743/39614081257132168796771975168)), (1623/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((1890577712885575/2475880078570760549798248448), (-746347759125/1237940039285380274899124224)), (27593/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772243754629837/154742504910672534362390528), (-746219349167/77371252455336267181195264)), (110383/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387635113801339/2417851639229258349412352), (-349722116263/2417851639229258349412352)), (103495/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157456514257793/75557863725914323419136), (-611877327935/302231454903657293676544)), (90569/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889194705800921/75557863725914323419136), (-62127813833/2361183241434822606848)), (147195/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298591086726375/4722366482869645213696), (-1490620303051/4722366482869645213696)), (55207/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622893521703193/590295810358705651712), (-1024438211405/295147905179352825856)), (151849/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912640246739139/36893488147419103232), (-5000012169/144115188075855872)), (94927/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912343637356579/4611686018427387904), (-1439254971973/4611686018427387904)), (106823/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595934240752207/1152921504606846976), (-2876639690689/1152921504606846976)), (213721/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299070966004359/36028797018963968), (-2514957176533/144115188075855872)), (187091/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494188594134333/36028797018963968), (-942058590481/9007199254740992)), (280805/36028797018963968), by norm_num⟩
  | 3 => ⟨((746220313095775/4503599627370496), (-4702948821779/9007199254740992)), (351303/9007199254740992), by norm_num⟩
  | 2 => ⟨((139643491806761/281474976710656), (-9383898515293/4503599627370496)), (351749/2251799813685248), by norm_num⟩
  | 1 => ⟨((2225580272027745/2251799813685248), (-1752620777745/281474976710656)), (528741/1125899906842624), by norm_num⟩
  | 0 => ⟨((549876542156595/562949953421312), (-27823102635667/2251799813685248)), (2123931/2251799813685248), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((549876542156595/562949953421312), (-27823102635667/2251799813685248)), (8102153786666106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1074041580292389/1125899906842624), (-13588482756227/562949953421312)), (4201701/2251799813685248), by norm_num⟩
  | 2 => ⟨((1023915822122585/1125899906842624), (-103700838091029/2251799813685248)), (2054797/562949953421312), by norm_num⟩
  | 3 => ⟨((1857563249597003/2251799813685248), (-188615219245451/2251799813685248)), (15706415/2251799813685248), by norm_num⟩
  | 4 => ⟨((758274670902807/1125899906842624), (-155593182598071/1125899906842624)), (28544393/2251799813685248), by norm_num⟩
  | 5 => ⟨((978366255675957/2251799813685248), (-52394697171675/281474976710656)), (1448053/70368744177664), by norm_num⟩
  | 6 => ⟨((173529514219307/1125899906842624), (-728465518152565/4503599627370496)), (28758345/1125899906842624), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50287509/33554432), (-1081307155/33554432)), (1/16777216), by norm_num⟩, -5, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-52112269/33554432), (-1120544075/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-378188538002347/4503599627370496), (-874695910810495/4503599627370496)), (20828433/562949953421312), by norm_num⟩
  | 1 => ⟨((112028505/536870912), (1036423533/2147483648)), (199/2147483648), by norm_num⟩
  | 2 => ⟨((-278380377/1073741824), (-160963483/268435456)), (249/2147483648), by norm_num⟩
  | 3 => ⟨((461166167/2147483648), (533305639/1073741824)), (209/2147483648), by norm_num⟩
  | 4 => ⟨((-572977437/4294967296), (-165651841/536870912)), (131/2147483648), by norm_num⟩
  | 5 => ⟨((569518177/8589934592), (329303489/2147483648)), (263/8589934592), by norm_num⟩
  | 6 => ⟨((-29483323/1073741824), (-1091051239/17179869184)), (55/4294967296), by norm_num⟩
  | 7 => ⟨((334917967/34359738368), (12103395/536870912)), (79/17179869184), by norm_num⟩
  | 8 => ⟨((-208059971/68719476736), (-962425815/137438953472)), (99/68719476736), by norm_num⟩
  | 9 => ⟨((229782047/274877906944), (531452957/274877906944)), (221/549755813888), by norm_num⟩
  | 10 => ⟨((-456789549/2199023255552), (-1056488789/2199023255552)), (111/1099511627776), by norm_num⟩
  | 11 => ⟨((412756141/8796093022208), (14916341/137438953472)), (101/4398046511104), by norm_num⟩
  | 12 => ⟨((-170943413/17592186044416), (-197683813/8796093022208)), (169/35184372088832), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197744090550571/1267650600228229401496703205376), (-2577724175159/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111223028849531/39614081257132168796771975168), (-1526614180733/316912650057057350374175801344)), (23125/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945320560802249/19807040628566084398385987584), (-1717200687407/19807040628566084398385987584)), (52041/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890471924785967/2475880078570760549798248448), (-912118044953/618970019642690137449562112)), (55305/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110758602535937/9671406556917033397649408), (-3647820531385/154742504910672534362390528)), (110635/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775220313561259/4835703278458516698824704), (-854784862015/2417851639229258349412352)), (103747/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314891104631447/151115727451828646838272), (-2991054802741/604462909807314587353088)), (90805/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472262888069997/18889465931478580854784), (-1214791583757/18889465931478580854784)), (18451/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((649241577377175/2361183241434822606848), (-1821619714633/2361183241434822606848)), (55375/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622744194906279/590295810358705651712), (-5007609659341/590295810358705651712)), (152353/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912546227909041/36893488147419103232), (-6256745839817/73786976294838206464)), (47637/18446744073709551616), by norm_num⟩
  | 7 => ⟨((912236919084775/4611686018427387904), (-7035036472407/9223372036854775808)), (214513/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398929609937161/288230376151711744), (-7030284689155/1152921504606846976)), (214697/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196092382600779/144115188075855872), (-3073077680539/72057594037927936)), (188067/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493896072119173/36028797018963968), (-4604275299557/18014398509481984)), (141257/18014398509481984), by norm_num⟩
  | 3 => ⟨((746032862003413/4503599627370496), (-5746002666751/4503599627370496)), (353867/9007199254740992), by norm_num⟩
  | 2 => ⟨((139594900997937/281474976710656), (-5732001859029/1125899906842624)), (354957/2251799813685248), by norm_num⟩
  | 1 => ⟨((278043165254365/281474976710656), (-17126081368051/1125899906842624)), (535165/1125899906842624), by norm_num⟩
  | 0 => ⟨((274595410784679/281474976710656), (-16986473146621/562949953421312)), (1081277/1125899906842624), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((274595410784679/281474976710656), (-16986473146621/562949953421312)), (4124744419578170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1070510855875517/1125899906842624), (-66285218330781/1125899906842624)), (2174953/1125899906842624), by norm_num⟩
  | 2 => ⟨((253486068219771/281474976710656), (-31512146584225/281474976710656)), (1098001/281474976710656), by norm_num⟩
  | 3 => ⟨((899009526721851/1125899906842624), (-227029492486971/1125899906842624)), (8893959/1125899906842624), by norm_num⟩
  | 4 => ⟨((1344126123608467/2251799813685248), (-725114818296695/2251799813685248)), (35580233/2251799813685248), by norm_num⟩
  | 5 => ⟨((568826557613489/2251799813685248), (-865659339666709/2251799813685248)), (16347829/562949953421312), by norm_num⟩
  | 6 => ⟨((-378188538002347/4503599627370496), (-874695910810495/4503599627370496)), (20828433/562949953421312), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-52112269/33554432), (-1120544075/33554432)), (1/16777216), by norm_num⟩, -5, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-53790887/33554432), (-1156638543/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1806048207066663/9007199254740992), (-157531916219617/9007199254740992)), (4652973/140737488355328), by norm_num⟩
  | 1 => ⟨((276113879/536870912), (48167871/1073741824)), (23/268435456), by norm_num⟩
  | 2 => ⟨((-1416436233/2147483648), (-61774075/1073741824)), (119/1073741824), by norm_num⟩
  | 3 => ⟨((1211029069/2147483648), (105631583/2147483648)), (103/1073741824), by norm_num⟩
  | 4 => ⟨((-388278529/1073741824), (-67734915/2147483648)), (267/4294967296), by norm_num⟩
  | 5 => ⟨((796731811/4294967296), (138989301/8589934592)), (69/2147483648), by norm_num⟩
  | 6 => ⟨((-681192249/8589934592), (-59416753/8589934592)), (119/8589934592), by norm_num⟩
  | 7 => ⟨((499206749/17179869184), (10885783/4294967296)), (11/2147483648), by norm_num⟩
  | 8 => ⟨((-640220015/68719476736), (-13960741/17179869184)), (57/34359738368), by norm_num⟩
  | 9 => ⟨((1459672815/549755813888), (31829861/137438953472)), (131/274877906944), by norm_num⟩
  | 10 => ⟨((-374398685/549755813888), (-65313585/1099511627776)), (271/2199023255552), by norm_num⟩
  | 11 => ⟨((1396819879/8796093022208), (60918559/4398046511104)), (255/8796093022208), by norm_num⟩
  | 12 => ⟨((-1194257417/35184372088832), (-104168679/35184372088832)), (55/8796093022208), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581887559023027/10141204801825835211973625643008), (-994735547069/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889742195429623/316912650057057350374175801344), (-2356267807311/316912650057057350374175801344)), (11583/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((945273078358087/19807040628566084398385987584), (-5300817776575/39614081257132168796771975168)), (26069/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890370532361981/2475880078570760549798248448), (-5631193644925/2475880078570760549798248448)), (27707/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772035694663193/154742504910672534362390528), (-2815076273907/77371252455336267181195264)), (110867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550344465051895/9671406556917033397649408), (-5277161794955/9671406556917033397649408)), (103979/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259479689275559/604462909807314587353088), (-4616410292225/604462909807314587353088)), (91023/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944456383261741/37778931862957161709568), (-1874898081637/18889465931478580854784)), (147989/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649189051512401/2361183241434822606848), (-5622879020613/4722366482869645213696)), (27765/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((25353096659565/9223372036854775808), (-7728508679363/590295810358705651712)), (152817/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824907603470245/73786976294838206464), (-9656210480509/73786976294838206464)), (95593/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912131331795833/4611686018427387904), (-10857151251017/9223372036854775808)), (13457/576460752303423488), by norm_num⟩
  | 6 => ⟨((797751625667255/576460752303423488), (-10849543348833/1152921504606846976)), (53899/288230376151711744), by norm_num⟩
  | 5 => ⟨((149487448138415/18014398509481984), (-9484790209937/144115188075855872)), (94483/72057594037927936), by norm_num⟩
  | 4 => ⟨((746798940224109/18014398509481984), (-14210061590615/36028797018963968)), (284089/36028797018963968), by norm_num⟩
  | 3 => ⟨((745838643510117/4503599627370496), (-17732603198115/9007199254740992)), (178117/4503599627370496), by norm_num⟩
  | 2 => ⟨((1116347314074665/2251799813685248), (-17687628256375/2251799813685248)), (357919/2251799813685248), by norm_num⟩
  | 1 => ⟨((138937061223713/140737488355328), (-26418956429377/1125899906842624)), (541101/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096797849488331/1125899906842624), (-6548460972881/140737488355328)), (549573/562949953421312), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1096797849488331/1125899906842624), (-6548460972881/140737488355328)), (2096454622508811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1066010437976471/1125899906842624), (-51033580295113/562949953421312)), (2243757/1125899906842624), by norm_num⟩
  | 2 => ⟨((500026930351821/562949953421312), (-96637949699209/562949953421312)), (4655623/1125899906842624), by norm_num⟩
  | 3 => ⟨((855095684055833/1125899906842624), (-343345457619571/1125899906842624)), (9868895/1125899906842624), by norm_num⟩
  | 4 => ⟨((544722068005861/1125899906842624), (-260763161242279/562949953421312)), (42018975/2251799813685248), by norm_num⟩
  | 5 => ⟨((87867229326529/4503599627370496), (-2018558809192541/4503599627370496)), (159171041/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1806048207066663/9007199254740992), (-157531916219617/9007199254740992)), (4652973/140737488355328), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-53790887/33554432), (-1156638543/33554432)), (1/16777216), by norm_num⟩, -5, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-13836261/8388608), (-1190056799/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-531877163556387/4503599627370496), (170672966227663/1125899906842624)), (155691131/4503599627370496), by norm_num⟩
  | 1 => ⟨((167328635/536870912), (-429549925/1073741824)), (99/1073741824), by norm_num⟩
  | 2 => ⟨((-883179721/2147483648), (566803439/1073741824)), (33/268435456), by norm_num⟩
  | 3 => ⟨((388460319/1073741824), (-997217847/2147483648)), (235/2147483648), by norm_num⟩
  | 4 => ⟨((-256292263/1073741824), (657928767/2147483648)), (157/2147483648), by norm_num⟩
  | 5 => ⟨((135273995/1073741824), (-347262347/2147483648)), (167/4294967296), by norm_num⟩
  | 6 => ⟨((-475994437/8589934592), (610963495/8589934592)), (149/8589934592), by norm_num⟩
  | 7 => ⟨((179453801/8589934592), (-921352965/34359738368)), (227/34359738368), by norm_num⟩
  | 8 => ⟨((-473588869/68719476736), (37992239/4294967296)), (19/8589934592), by norm_num⟩
  | 9 => ⟨((555479189/274877906944), (-44561643/17179869184)), (45/68719476736), by norm_num⟩
  | 10 => ⟨((-293188285/549755813888), (188161169/274877906944)), (3/17179869184), by norm_num⟩
  | 11 => ⟨((562720503/4398046511104), (-361140445/2199023255552)), (93/2199023255552), by norm_num⟩
  | 12 => ⟨((-495017223/17592186044416), (635380225/17592186044416)), (83/8796093022208), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581827225323591/10141204801825835211973625643008), (727070753355/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779418464387605/633825300114114700748351602688), (3444217028555/633825300114114700748351602688)), (92539/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945236160681703/19807040628566084398385987584), (3874167402863/39614081257132168796771975168)), (1627/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((945146251811099/1237940039285380274899124224), (1028902162063/618970019642690137449562112)), (110661/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771958139710729/154742504910672534362390528), (128588365141/4835703278458516698824704)), (55345/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550272260445573/9671406556917033397649408), (3856821263109/9671406556917033397649408)), (103801/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259417013139933/604462909807314587353088), (843472251795/151115727451828646838272)), (90857/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888811860164289/75557863725914323419136), (685126792285/9444732965739290427392)), (73849/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298303247254719/4722366482869645213696), (4109400065711/4722366482869645213696)), (110823/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202812074683071/73786976294838206464), (5648214344109/590295810358705651712)), (76231/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824782622580647/73786976294838206464), (7056952461995/73786976294838206464)), (95349/36893488147419103232), by norm_num⟩
  | 7 => ⟨((114007800875373/576460752303423488), (1983628452633/2305843009213693952)), (214701/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595368839610419/1152921504606846976), (7928818265395/1152921504606846976)), (214909/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597892918105733/72057594037927936), (866413835699/18014398509481984)), (188279/144115188075855872), by norm_num⟩
  | 4 => ⟨((746717482125917/18014398509481984), (5192080462375/18014398509481984)), (141443/18014398509481984), by norm_num⟩
  | 3 => ⟨((745743547117343/4503599627370496), (3239451151247/2251799813685248)), (177213/4503599627370496), by norm_num⟩
  | 2 => ⟨((558088614944969/1125899906842624), (12924234611149/2251799813685248)), (44457/281474976710656), by norm_num⟩
  | 1 => ⟨((138911423717043/140737488355328), (9651257083949/562949953421312)), (268283/562949953421312), by norm_num⟩
  | 0 => ⟨((1096586282896553/1125899906842624), (9567550829419/281474976710656)), (1085495/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1096586282896553/1125899906842624), (9567550829419/281474976710656)), (4140834812644576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((533367513433315/562949953421312), (74547621412481/1125899906842624)), (2188261/1125899906842624), by norm_num⟩
  | 2 => ⟨((1005743283931341/1125899906842624), (17657555180303/140737488355328)), (2218159/562949953421312), by norm_num⟩
  | 3 => ⟨((880686671017807/1125899906842624), (252370107506817/1125899906842624)), (9038945/1125899906842624), by norm_num⟩
  | 4 => ⟨((1264621014743427/2251799813685248), (394811276728619/1125899906842624)), (4548201/281474976710656), by norm_num⟩
  | 5 => ⟨((216662806363203/1125899906842624), (886911233182087/2251799813685248)), (33193405/1125899906842624), by norm_num⟩
  | 6 => ⟨((-531877163556387/4503599627370496), (170672966227663/1125899906842624)), (155691131/4503599627370496), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13836261/8388608), (-1190056799/33554432)), (1/16777216), by norm_num⟩, -6, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-56791929/33554432), (-305292113/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((54342292712769/1125899906842624), (1599784665171267/9007199254740992)), (241910593/9007199254740992), by norm_num⟩
  | 1 => ⟨((-280688585/2147483648), (-1032900139/2147483648)), (79/1073741824), by norm_num⟩
  | 2 => ⟨((380059389/2147483648), (699286357/1073741824)), (217/2147483648), by norm_num⟩
  | 3 => ⟨((-171536651/1073741824), (-1262468373/2147483648)), (99/1073741824), by norm_num⟩
  | 4 => ⟨((232264931/2147483648), (854706933/2147483648)), (17/268435456), by norm_num⟩
  | 5 => ⟨((-251594037/4294967296), (-925835713/4294967296)), (149/4294967296), by norm_num⟩
  | 6 => ⟨((227109761/8589934592), (1671473059/17179869184)), (271/17179869184), by norm_num⟩
  | 7 => ⟨((-43930331/4294967296), (-646633279/17179869184)), (211/34359738368), by norm_num⟩
  | 8 => ⟨((237931083/68719476736), (437778845/34359738368)), (145/68719476736), by norm_num⟩
  | 9 => ⟨((-286368585/274877906944), (-1053801857/274877906944)), (11/17179869184), by norm_num⟩
  | 10 => ⟨((155100101/549755813888), (285374833/274877906944)), (193/1099511627776), by norm_num⟩
  | 11 => ⟨((-152734131/2199023255552), (-562043181/2199023255552)), (3/68719476736), by norm_num⟩
  | 12 => ⟨((275741129/17592186044416), (1014694099/17592186044416)), (11/1099511627776), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581771056014629/10141204801825835211973625643008), (1700502125739/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779356119756963/633825300114114700748351602688), (2013724881337/633825300114114700748351602688)), (46199/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945201217795011/19807040628566084398385987584), (141568770485/2475880078570760549798248448)), (103961/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472554642702821/618970019642690137449562112), (601563317427/618970019642690137449562112)), (110473/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771884567631985/154742504910672534362390528), (2405785561551/154742504910672534362390528)), (55245/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387550917427955/2417851639229258349412352), (563731781853/2417851639229258349412352)), (51801/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629678689563361/302231454903657293676544), (493141129053/151115727451828646838272)), (90669/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944357836170923/37778931862957161709568), (3204486235361/75557863725914323419136)), (73685/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324557933426791/1180591620717411303424), (2402550207953/4722366482869645213696)), (110557/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811199642444829/295147905179352825856), (3302183487497/590295810358705651712)), (76031/295147905179352825856), by norm_num⟩
  | 8 => ⟨((228082813527577/9223372036854775808), (515718199591/9223372036854775808)), (47537/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823991781705051/9223372036854775808), (1159684359643/2305843009213693952)), (214013/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398809606042689/288230376151711744), (4635331464535/1152921504606846976)), (214135/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298918665437401/36028797018963968), (4052086022647/144115188075855872)), (187505/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493274068362107/36028797018963968), (758809724117/4503599627370496)), (140765/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491296211897143/9007199254740992), (1893680701897/2251799813685248)), (352391/9007199254740992), by norm_num⟩
  | 2 => ⟨((2232003297293941/4503599627370496), (7554691610829/2251799813685248)), (706221/4503599627370496), by norm_num⟩
  | 1 => ⟨((1111066077746569/1125899906842624), (11282065909145/1125899906842624)), (132867/281474976710656), by norm_num⟩
  | 0 => ⟨((1096286743739087/1125899906842624), (349451310555/17592186044416)), (2140329/2251799813685248), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1096286743739087/1125899906842624), (349451310555/17592186044416)), (8164707192427825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1067008203097051/1125899906842624), (87106591159613/2251799813685248)), (4253101/2251799813685248), by norm_num⟩
  | 2 => ⟨((2019024264968535/2251799813685248), (165100728308559/2251799813685248)), (8390321/2251799813685248), by norm_num⟩
  | 3 => ⟨((1798206353617589/2251799813685248), (148033752642255/1125899906842624)), (16276323/2251799813685248), by norm_num⟩
  | 4 => ⟨((1397055858778483/2251799813685248), (236428862755351/1125899906842624)), (1892213/140737488355328), by norm_num⟩
  | 5 => ⟨((767461935767657/2251799813685248), (586738351942801/2251799813685248)), (25140955/1125899906842624), by norm_num⟩
  | 6 => ⟨((54342292712769/1125899906842624), (1599784665171267/9007199254740992)), (241910593/9007199254740992), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56791929/33554432), (-305292113/8388608)), (1/16777216), by norm_num⟩, -6, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 12 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile035Terms1

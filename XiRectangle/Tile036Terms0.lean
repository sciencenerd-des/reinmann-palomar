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
namespace Reinmann.XiRectangle.Tile036Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨36,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (8601/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (8601/640))
  have he : value ((7/8), (8601/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-10175445/16777216), (-312567865/33554432)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-1220445091826823/2251799813685248), (-8388255820093/140737488355328)), (24984353/1125899906842624), by norm_num⟩
  | 1 => ⟨((1613517903/4294967296), (177438229/4294967296)), (69/4294967296), by norm_num⟩
  | 2 => ⟨((-1118405385/8589934592), (-15373851/1073741824)), (25/4294967296), by norm_num⟩
  | 3 => ⟨((1033626053/34359738368), (56833821/17179869184)), (3/2147483648), by norm_num⟩
  | 4 => ⟨((-1432909969/274877906944), (-157576811/274877906944)), (17/68719476736), by norm_num⟩
  | 5 => ⟨((198643501/274877906944), (43689569/549755813888)), (39/1099511627776), by norm_num⟩
  | 6 => ⟨((-1468684615/17592186044416), (-80755471/8796093022208)), (37/8796093022208), by norm_num⟩
  | 7 => ⟨((1163445257/140737488355328), (127943833/140737488355328)), (15/35184372088832), by norm_num⟩
  | 8 => ⟨((-1612877599/2251799813685248), (-88683907/1125899906842624)), (85/2251799813685248), by norm_num⟩
  | 9 => ⟨((993743609/18014398509481984), (54640889/9007199254740992)), (27/9007199254740992), by norm_num⟩
  | 10 => ⟨((-1102096929/288230376151711744), (-60598685/144115188075855872)), (31/144115188075855872), by norm_num⟩
  | 11 => ⟨((555574821/2305843009213693952), (122192895/4611686018427387904)), (1/72057594037927936), by norm_num⟩
  | 12 => ⟨((-513460161/36893488147419103232), (-56465107/36893488147419103232)), (61/73786976294838206464), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583185728209367/10141204801825835211973625643008), (-3949600554683/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781023339972485/633825300114114700748351602688), (-585684006241/79228162514264337593543950336)), (11583/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236534660021291/4951760157141521099596496896), (-5270833171571/39614081257132168796771975168)), (26069/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892209652448091/2475880078570760549798248448), (-5599909274113/2475880078570760549798248448)), (13853/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773874590976843/154742504910672534362390528), (-1399878530097/38685626227668133590597632)), (6929/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((776034096155703/4835703278458516698824704), (-5249124356031/9671406556917033397649408)), (12997/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260987712282571/604462909807314587353088), (-574070420483/75557863725914323419136)), (22755/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891362856353505/75557863725914323419136), (-7462126456045/75557863725914323419136)), (9249/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((20315863720729/73786976294838206464), (-1398975946881/1180591620717411303424)), (6941/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1625123663303219/590295810358705651712), (-3846621743819/295147905179352825856)), (38203/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914031744832809/36893488147419103232), (-300464557233/2305843009213693952)), (23897/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1827811711828305/9223372036854775808), (-1351799845669/1152921504606846976)), (841/144115188075855872), by norm_num⟩
  | 6 => ⟨((1599050639660015/1152921504606846976), (-10811486797535/1152921504606846976)), (26947/576460752303423488), by norm_num⟩
  | 5 => ⟨((149875209411629/18014398509481984), (-591047977263/9007199254740992)), (47237/144115188075855872), by norm_num⟩
  | 4 => ⟨((23410113258875/562949953421312), (-14178566482653/36028797018963968)), (35507/18014398509481984), by norm_num⟩
  | 3 => ⟨((748741182166453/4503599627370496), (-17711643177439/9007199254740992)), (89045/9007199254740992), by norm_num⟩
  | 2 => ⟨((280535590442195/562949953421312), (-2211776685483/281474976710656)), (89463/2251799813685248), by norm_num⟩
  | 1 => ⟨((1120163707163817/1125899906842624), (-6624364646025/281474976710656)), (67619/562949953421312), by norm_num⟩
  | 0 => ⟨((278507299011841/281474976710656), (-52817751436391/1125899906842624)), (68667/281474976710656), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((278507299011841/281474976710656), (-52817751436391/1125899906842624)), (261943818212413699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1099805877284101/1125899906842624), (-52260877554133/562949953421312)), (569315/1125899906842624), by norm_num⟩
  | 2 => ⟨((532306718889037/562949953421312), (-51049671411061/281474976710656)), (608973/562949953421312), by norm_num⟩
  | 3 => ⟨((242407131851599/281474976710656), (-386166946799241/1125899906842624)), (2745085/1125899906842624), by norm_num⟩
  | 4 => ⟨((702597598198949/1125899906842624), (-41571023063677/70368744177664)), (6611199/1125899906842624), by norm_num⟩
  | 5 => ⟨((91015187570377/2251799813685248), (-103766598724109/140737488355328)), (32124923/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1220445091826823/2251799813685248), (-8388255820093/140737488355328)), (24984353/1125899906842624), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-10175445/16777216), (-312567865/33554432)), (1/67108864), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-64510795/67108864), (-495408345/33554432)), (3/134217728), by norm_num⟩
  | 1 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-505323355360219/2251799813685248), (-174306617931025/562949953421312)), (57334919/2251799813685248), by norm_num⟩
  | 1 => ⟨((529436539/2147483648), (365248475/1073741824)), (31/1073741824), by norm_num⟩
  | 2 => ⟨((-36352843/268435456), (-401266463/2147483648)), (35/2147483648), by norm_num⟩
  | 3 => ⟨((852003841/17179869184), (293890845/4294967296)), (105/17179869184), by norm_num⟩
  | 4 => ⟨((-468010945/34359738368), (-161436047/8589934592)), (59/34359738368), by norm_num⟩
  | 5 => ⟨((822660121/274877906944), (1135076001/274877906944)), (53/137438953472), by norm_num⟩
  | 6 => ⟨((-150630753/274877906944), (-415669481/549755813888)), (5/68719476736), by norm_num⟩
  | 7 => ⟨((378250963/4398046511104), (1043793371/8796093022208)), (103/8796093022208), by norm_num⟩
  | 8 => ⟨((-831102313/70368744177664), (-8958783/549755813888)), (29/17592186044416), by norm_num⟩
  | 9 => ⟨((811608191/562949953421312), (1119826955/562949953421312)), (29/140737488355328), by norm_num⟩
  | 10 => ⟨((-356657093/2251799813685248), (-984204523/4503599627370496)), (13/562949953421312), by norm_num⟩
  | 11 => ⟨((35620715/2251799813685248), (786370315/36028797018963968)), (43/18014398509481984), by norm_num⟩
  | 12 => ⟨((-52177807/36028797018963968), (-575944061/288230376151711744)), (129/576460752303423488), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395680896270333/2535301200456458802993406410752), (-2863073449679/10141204801825835211973625643008)), (29117/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890240400967103/316912650057057350374175801344), (-1697262134455/316912650057057350374175801344)), (34701/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891667311635855/39614081257132168796771975168), (-1909249107699/19807040628566084398385987584)), (39047/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945781012321409/1237940039285380274899124224), (-4056754731879/2475880078570760549798248448)), (5187/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((443306871236815/38685626227668133590597632), (-4056305075635/154742504910672534362390528)), (20753/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775731042376697/4835703278458516698824704), (-118822131171/302231454903657293676544)), (38923/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630228961233455/302231454903657293676544), (-3326541804295/604462909807314587353088)), (34069/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890502987110635/75557863725914323419136), (-5404734306385/75557863725914323419136)), (27691/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299571285400403/4722366482869645213696), (-506595812235/590295810358705651712)), (41555/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624239650574665/590295810358705651712), (-696409916161/73786976294838206464)), (3573/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1826960689326953/73786976294838206464), (-3481093427275/36893488147419103232)), (4469/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1826574107315151/9223372036854775808), (-7829830141843/9223372036854775808)), (10063/1152921504606846976), by norm_num⟩
  | 6 => ⟨((399454210415435/288230376151711744), (-3913270793067/576460752303423488)), (20145/288230376151711744), by norm_num⟩
  | 5 => ⟨((598963191619633/72057594037927936), (-3422261467063/72057594037927936)), (35297/72057594037927936), by norm_num⟩
  | 4 => ⟨((748321435009591/18014398509481984), (-2564844795719/9007199254740992)), (106063/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495491863839349/9007199254740992), (-12811257426301/9007199254740992)), (8305/562949953421312), by norm_num⟩
  | 2 => ⟨((1120174307191183/2251799813685248), (-6395896415061/1125899906842624)), (133333/2251799813685248), by norm_num⟩
  | 1 => ⟨((1117267693500707/1125899906842624), (-19138976394757/1125899906842624)), (100567/562949953421312), by norm_num⟩
  | 0 => ⟨((554230578385067/562949953421312), (-38082795842203/1125899906842624)), (406815/1125899906842624), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((554230578385067/562949953421312), (-38082795842203/1125899906842624)), (1551876072410201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((545002193032673/562949953421312), (-9373235506047/140737488355328)), (828549/1125899906842624), by norm_num⟩
  | 2 => ⟨((262564787431069/281474976710656), (-145190424138017/1125899906842624)), (214329/140737488355328), by norm_num⟩
  | 3 => ⟨((480488547757477/562949953421312), (-270872340385787/1125899906842624)), (3641099/1125899906842624), by norm_num⟩
  | 4 => ⟨((377522525826583/562949953421312), (-231194721073599/562949953421312)), (7967469/1125899906842624), by norm_num⟩
  | 5 => ⟨((632896462023665/2251799813685248), (-1240340666548113/2251799813685248)), (8615217/562949953421312), by norm_num⟩
  | 6 => ⟨((-505323355360219/2251799813685248), (-174306617931025/562949953421312)), (57334919/2251799813685248), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-64510795/67108864), (-495408345/33554432)), (3/134217728), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-10175445/8388608), (-312567865/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((1306930862398359/4503599627370496), (290964568552575/4503599627370496)), (49871153/4503599627370496), by norm_num⟩
  | 1 => ⟨((-863929217/2147483648), (-384676495/4294967296)), (17/1073741824), by norm_num⟩
  | 2 => ⟨((598830101/2147483648), (66659357/1073741824)), (49/4294967296), by norm_num⟩
  | 3 => ⟨((-34589783/268435456), (-246425309/8589934592)), (3/536870912), by norm_num⟩
  | 4 => ⟨((383612969/8589934592), (10675563/1073741824)), (69/34359738368), by norm_num⟩
  | 5 => ⟨((-1701761587/137438953472), (-378866503/137438953472)), (79/137438953472), by norm_num⟩
  | 6 => ⟨((1572761661/549755813888), (175073499/274877906944)), (75/549755813888), by norm_num⟩
  | 7 => ⟨((-155736473/274877906944), (-277375319/2199023255552)), (61/2199023255552), by norm_num⟩
  | 8 => ⟨((1727172755/17592186044416), (384523841/17592186044416)), (87/17592186044416), by norm_num⟩
  | 9 => ⟨((-532082189/35184372088832), (-925457/274877906944)), (55/70368744177664), by norm_num⟩
  | 10 => ⟨((1180196061/562949953421312), (32843669/70368744177664)), (63/562949953421312), by norm_num⟩
  | 11 => ⟨((-1189890287/4503599627370496), (-66226899/1125899906842624)), (33/2251799813685248), by norm_num⟩
  | 12 => ⟨((549846065/18014398509481984), (61206651/9007199254740992)), (63/36028797018963968), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582395689313353/10141204801825835211973625643008), (35668659315/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((55628068946783/19807040628566084398385987584), (338176226715/633825300114114700748351602688)), (46117/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891237297126915/39614081257132168796771975168), (95101797731/9903520314283042199192993792)), (51883/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472776408800891/618970019642690137449562112), (202066306219/1237940039285380274899124224)), (27563/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886385829479747/77371252455336267181195264), (404076342035/154742504910672534362390528)), (6891/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1551035346388243/9671406556917033397649408), (378761794333/9671406556917033397649408)), (12921/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260085124705939/604462909807314587353088), (165678403033/302231454903657293676544)), (45225/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472474578043541/18889465931478580854784), (538342778641/75557863725914323419136)), (73493/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649559380020821/2361183241434822606848), (403659082897/4722366482869645213696)), (55123/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623619021320919/590295810358705651712), (138718009097/147573952589676412928)), (75797/590295810358705651712), by norm_num⟩
  | 8 => ⟨((57068352847131/2305843009213693952), (693351327603/73786976294838206464)), (94753/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825707316147763/9223372036854775808), (779692146177/9223372036854775808)), (26651/2305843009213693952), by norm_num⟩
  | 6 => ⟨((798477074777509/576460752303423488), (779282233923/1152921504606846976)), (106615/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598588067327469/72057594037927936), (170352772813/36028797018963968)), (23325/36028797018963968), by norm_num⟩
  | 4 => ⟨((747763350038413/18014398509481984), (63824726823/2251799813685248)), (34993/9007199254740992), by norm_num⟩
  | 3 => ⟨((186764091451425/1125899906842624), (1274884389731/9007199254740992)), (175005/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118819245404303/2251799813685248), (2544944799665/4503599627370496)), (350131/4503599627370496), by norm_num⟩
  | 1 => ⟨((2230590204929653/2251799813685248), (1902689915735/1125899906842624)), (525501/2251799813685248), by norm_num⟩
  | 0 => ⟨((17261795858053/17592186044416), (7562745440627/2251799813685248)), (1052231/2251799813685248), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((17261795858053/17592186044416), (7562745440627/2251799813685248)), (4013942727095793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2167988752859639/2251799813685248), (7420713241261/1125899906842624)), (259001/281474976710656), by norm_num⟩
  | 2 => ⟨((521799821638453/562949953421312), (7144517353397/562949953421312)), (4017091/2251799813685248), by norm_num⟩
  | 3 => ⟨((1934267926157733/2251799813685248), (26489089184845/1125899906842624)), (7548869/2251799813685248), by norm_num⟩
  | 4 => ⟨((1660265579585725/2251799813685248), (22753796892595/562949953421312)), (6661987/1125899906842624), by norm_num⟩
  | 5 => ⟨((1220445091826795/2251799813685248), (134212093121491/2251799813685248)), (20724773/2251799813685248), by norm_num⟩
  | 6 => ⟨((1306930862398359/4503599627370496), (290964568552575/4503599627370496)), (49871153/4503599627370496), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-10175445/8388608), (-312567865/16777216)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-47253303/33554432), (-1451520215/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-257532476016381/1125899906842624), (-194938098162495/2251799813685248)), (48051615/2251799813685248), by norm_num⟩
  | 1 => ⟨((6176271/16777216), (149603255/1073741824)), (75/2147483648), by norm_num⟩
  | 2 => ⟨((-636180781/2147483648), (-481554301/4294967296)), (123/4294967296), by norm_num⟩
  | 3 => ⟨((1365191291/8589934592), (516687833/8589934592)), (67/4294967296), by norm_num⟩
  | 4 => ⟨((-1098595311/17179869184), (-207894247/8589934592)), (55/8589934592), by norm_num⟩
  | 5 => ⟨((1414496755/68719476736), (535348613/68719476736)), (9/4294967296), by norm_num⟩
  | 6 => ⟨((-758848235/137438953472), (-574406903/274877906944)), (39/68719476736), by norm_num⟩
  | 7 => ⟨((1395793279/1099511627776), (528269855/1099511627776)), (73/549755813888), by norm_num⟩
  | 8 => ⟨((-1123221311/4398046511104), (-212554383/2199023255552)), (15/549755813888), by norm_num⟩
  | 9 => ⟨((401723325/8796093022208), (76020685/4398046511104)), (87/17592186044416), by norm_num⟩
  | 10 => ⟨((-1034477999/140737488355328), (-48940229/17592186044416)), (57/70368744177664), by norm_num⟩
  | 11 => ⟨((151357101/140737488355328), (229138211/562949953421312)), (135/1125899906842624), by norm_num⟩
  | 12 => ⟨((-324799809/2251799813685248), (-30731977/562949953421312)), (147/9007199254740992), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582141353606259/10141204801825835211973625643008), (-1810487413939/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889893532569355/316912650057057350374175801344), (-4289948101495/633825300114114700748351602688)), (5789/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((945443366282505/19807040628566084398385987584), (-4825563006529/39614081257132168796771975168)), (26057/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890732488515847/2475880078570760549798248448), (-5126420854109/2475880078570760549798248448)), (55387/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772397756790279/154742504910672534362390528), (-5125588383245/154742504910672534362390528)), (55405/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550684010767469/9671406556917033397649408), (-1201088638701/2417851639229258349412352)), (51961/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629888452053767/302231454903657293676544), (-4202925619925/604462909807314587353088)), (11371/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944697975473565/37778931862957161709568), (-6828095348923/75557863725914323419136)), (36973/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298740675075473/4722366482869645213696), (-5119619947255/4722366482869645213696)), (55491/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405774255197077/147573952589676412928), (-7037118394453/590295810358705651712)), (38175/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825531592721395/73786976294838206464), (-8792859023905/73786976294838206464)), (11939/9223372036854775808), by norm_num⟩
  | 7 => ⟨((456241315800541/2305843009213693952), (-9887099640777/9223372036854775808)), (53777/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596206613190753/1152921504606846976), (-9881015177495/1152921504606846976)), (107683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196515880983855/144115188075855872), (-269970058667/4503599627370496)), (2949/4503599627370496), by norm_num⟩
  | 4 => ⟨((1494524024589573/36028797018963968), (-12944866584341/36028797018963968)), (141843/36028797018963968), by norm_num⟩
  | 3 => ⟨((373209481096923/2251799813685248), (-16157107195871/9007199254740992)), (88907/4503599627370496), by norm_num⟩
  | 2 => ⟨((1117512350517015/2251799813685248), (-8060564041263/1125899906842624)), (44645/562949953421312), by norm_num⟩
  | 1 => ⟨((139156864234687/140737488355328), (-24091692509025/1125899906842624)), (67447/281474976710656), by norm_num⟩
  | 0 => ⟨((275089351900535/281474976710656), (-23911541313653/562949953421312)), (273637/562949953421312), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((275089351900535/281474976710656), (-23911541313653/562949953421312)), (1043842317821311773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((268340766769831/281474976710656), (-93476307979979/1125899906842624)), (1116209/1125899906842624), by norm_num⟩
  | 2 => ⟨((1015516962624799/1125899906842624), (-44557254167473/281474976710656)), (2313593/1125899906842624), by norm_num⟩
  | 3 => ⟨((887742429785359/1125899906842624), (-160755488618681/562949953421312)), (2453009/562949953421312), by norm_num⟩
  | 4 => ⟨((1216302282282359/2251799813685248), (-63375734912299/140737488355328)), (10538449/1125899906842624), by norm_num⟩
  | 5 => ⟨((100180174225691/1125899906842624), (-1095430249835531/2251799813685248)), (20875791/1125899906842624), by norm_num⟩
  | 6 => ⟨((-257532476016381/1125899906842624), (-194938098162495/2251799813685248)), (48051615/2251799813685248), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47253303/33554432), (-1451520215/67108864)), (1/33554432), by norm_num⟩, -3, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-105212575/67108864), (-403988105/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((232322243525217/2251799813685248), (816011374501227/4503599627370496)), (1912797/140737488355328), by norm_num⟩
  | 1 => ⟨((-12405681/67108864), (-697181753/2147483648)), (27/1073741824), by norm_num⟩
  | 2 => ⟨((711295885/4294967296), (156147751/536870912)), (49/2147483648), by norm_num⟩
  | 3 => ⟨((-424823713/4294967296), (-746077897/4294967296)), (15/1073741824), by norm_num⟩
  | 4 => ⟨((761181911/17179869184), (1336792137/17179869184)), (109/17179869184), by norm_num⟩
  | 5 => ⟨((-545541959/34359738368), (-239520997/8589934592)), (5/2147483648), by norm_num⟩
  | 6 => ⟨((325826657/68719476736), (286109343/34359738368)), (97/137438953472), by norm_num⟩
  | 7 => ⟨((-333601713/274877906944), (-1171746571/549755813888)), (51/274877906944), by norm_num⟩
  | 8 => ⟨((149433507/549755813888), (1049744007/2199023255552)), (93/2199023255552), by norm_num⟩
  | 9 => ⟨((-475998047/8796093022208), (-417975281/4398046511104)), (19/2199023255552), by norm_num⟩
  | 10 => ⟨((682299207/70368744177664), (299564467/17592186044416)), (111/70368744177664), by norm_num⟩
  | 11 => ⟨((-3473057/2199023255552), (-780723593/281474976710656)), (37/140737488355328), by norm_num⟩
  | 12 => ⟨((265509665/1125899906842624), (932579261/2251799813685248)), (91/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790966773092659/5070602400912917605986812821504), (342969094881/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779549316420923/633825300114114700748351602688), (1624902393189/633825300114114700748351602688)), (11545/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890619793778131/39614081257132168796771975168), (3569845387/77371252455336267181195264)), (25979/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945224765649927/1237940039285380274899124224), (1941685125575/2475880078570760549798248448)), (55211/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443028886919227/38685626227668133590597632), (485333897293/38685626227668133590597632)), (27609/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387605058563675/2417851639229258349412352), (909815404101/4835703278458516698824704)), (25887/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259546893821157/604462909807314587353088), (1591805735775/604462909807314587353088)), (22655/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889023672502629/75557863725914323419136), (646497115403/18889465931478580854784)), (73641/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649231383847875/2361183241434822606848), (1938882650629/4722366482869645213696)), (55243/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622717011534795/590295810358705651712), (2664974853701/590295810358705651712)), (75977/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825059748675305/73786976294838206464), (3329735974535/73786976294838206464)), (11875/9223372036854775808), by norm_num⟩
  | 7 => ⟨((456109697454141/2305843009213693952), (3743915371095/9223372036854775808)), (53457/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595685572502031/1152921504606846976), (3741369817019/1152921504606846976)), (53481/576460752303423488), by norm_num⟩
  | 5 => ⟨((598033036779307/72057594037927936), (1635418414593/72057594037927936)), (93647/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493861498296593/36028797018963968), (4900536688575/36028797018963968)), (140581/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492031041620953/9007199254740992), (764459319399/1125899906842624)), (175919/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116737283687245/2251799813685248), (3050351204679/1125899906842624)), (352417/4503599627370496), by norm_num⟩
  | 1 => ⟨((1112171515190241/1125899906842624), (18227402508785/2251799813685248)), (530079/2251799813685248), by norm_num⟩
  | 0 => ⟨((2197010776851901/2251799813685248), (2259807548869/140737488355328)), (1065987/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2197010776851901/2251799813685248), (2259807548869/140737488355328)), (4066417702681731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2142974256128733/2251799813685248), (70554357570195/2251799813685248)), (1057167/1125899906842624), by norm_num⟩
  | 2 => ⟨((2037197408570159/2251799813685248), (134289177050055/2251799813685248)), (4156799/2251799813685248), by norm_num⟩
  | 3 => ⟨((917519326828973/1125899906842624), (242982135288187/2251799813685248)), (2004271/562949953421312), by norm_num⟩
  | 4 => ⟨((734596060059003/1125899906842624), (49502803012543/281474976710656)), (7398379/1125899906842624), by norm_num⟩
  | 5 => ⟨((222232424177019/562949953421312), (258385768282857/1125899906842624)), (3064119/281474976710656), by norm_num⟩
  | 6 => ⟨((232322243525217/2251799813685248), (816011374501227/4503599627370496)), (1912797/140737488355328), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-105212575/67108864), (-403988105/16777216)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-57132171/33554432), (-1754977869/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((53814170792265/562949953421312), (-698528278080305/4503599627370496)), (26345033/2251799813685248), by norm_num⟩
  | 1 => ⟨((-199732859/1073741824), (1296304003/4294967296)), (25/1073741824), by norm_num⟩
  | 2 => ⟨((777324395/4294967296), (-630622779/2147483648)), (99/4294967296), by norm_num⟩
  | 3 => ⟨((-504201143/4294967296), (818090177/4294967296)), (33/2147483648), by norm_num⟩
  | 4 => ⟨((490565061/8589934592), (-795964989/8589934592)), (33/4294967296), by norm_num⟩
  | 5 => ⟨((-763676425/34359738368), (154887635/4294967296)), (105/34359738368), by norm_num⟩
  | 6 => ⟨((495348569/68719476736), (-100465807/8589934592)), (35/34359738368), by norm_num⟩
  | 7 => ⟨((-2151571/1073741824), (893702553/274877906944)), (79/274877906944), by norm_num⟩
  | 8 => ⟨((133976443/274877906944), (-434766217/549755813888)), (39/549755813888), by norm_num⟩
  | 9 => ⟨((-463477547/4398046511104), (752014217/4398046511104)), (69/4398046511104), by norm_num⟩
  | 10 => ⟨((360754265/17592186044416), (-585340839/17592186044416)), (109/35184372088832), by norm_num⟩
  | 11 => ⟨((-510542099/140737488355328), (207094669/35184372088832)), (79/140737488355328), by norm_num⟩
  | 12 => ⟨((662312701/1125899906842624), (-1074633649/1125899906842624)), (13/140737488355328), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581757847530181/10141204801825835211973625643008), (-1326666835193/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889670663439401/316912650057057350374175801344), (-785502498191/316912650057057350374175801344)), (23089/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890385845087825/39614081257132168796771975168), (-1767114570517/39614081257132168796771975168)), (51955/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890201009097551/2475880078570760549798248448), (-469308245859/618970019642690137449562112)), (6901/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885933539890295/77371252455336267181195264), (-1876866045149/154742504910672534362390528)), (55215/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550187353290483/9671406556917033397649408), (-109948258433/604462909807314587353088)), (51771/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259343180653089/604462909807314587353088), (-769442968189/302231454903657293676544)), (22653/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888692746718765/75557863725914323419136), (-1249979603711/37778931862957161709568)), (73635/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162276833491285/590295810358705651712), (-1874330485177/4722366482869645213696)), (55237/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622376027985841/590295810358705651712), (-2576166572425/590295810358705651712)), (37985/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912316874795811/36893488147419103232), (-3218652149875/73786976294838206464)), (47495/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823959857435339/9223372036854775808), (-3618845217595/9223372036854775808)), (106901/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99700439727223/72057594037927936), (-226010866367/72057594037927936)), (26737/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195647798451935/144115188075855872), (-3161149201127/144115188075855872)), (93633/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493234974183125/36028797018963968), (-4735723809467/36028797018963968)), (35139/9007199254740992), by norm_num⟩
  | 3 => ⟨((1491249439734167/9007199254740992), (-5909167957591/9007199254740992)), (87941/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115958008281419/2251799813685248), (-11786928174099/4503599627370496)), (352325/4503599627370496), by norm_num⟩
  | 1 => ⟨((2222016812767533/2251799813685248), (-4400514250775/562949953421312)), (264947/1125899906842624), by norm_num⟩
  | 0 => ⟨((548101158332801/562949953421312), (-17445937747527/1125899906842624)), (1065435/2251799813685248), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((548101158332801/562949953421312), (-17445937747527/1125899906842624)), (4064311989791106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2134035452028979/2251799813685248), (-67943081828201/2251799813685248)), (526921/562949953421312), by norm_num⟩
  | 2 => ⟨((1010189942396037/1125899906842624), (-32194901265267/562949953421312)), (515263/281474976710656), by norm_num⟩
  | 3 => ⟨((1805378376659283/2251799813685248), (-231089568491471/2251799813685248)), (3934213/1125899906842624), by norm_num⟩
  | 4 => ⟨((355936246503689/562949953421312), (-370551687135313/2251799813685248)), (1778999/281474976710656), by norm_num⟩
  | 5 => ⟨((839213690701315/2251799813685248), (-58572158969451/281474976710656)), (22680895/2251799813685248), by norm_num⟩
  | 6 => ⟨((53814170792265/562949953421312), (-698528278080305/4503599627370496)), (26345033/2251799813685248), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-57132171/33554432), (-1754977869/67108864)), (1/33554432), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-30526335/16777216), (-937703595/33554432)), (3/67108864), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1381993535255575/9007199254740992), (-235594746464099/4503599627370496)), (191242161/9007199254740992), by norm_num⟩
  | 1 => ⟨((685161297/2147483648), (58401287/536870912)), (193/4294967296), by norm_num⟩
  | 2 => ⟨((-44523527/134217728), (-485768249/4294967296)), (203/4294967296), by norm_num⟩
  | 3 => ⟨((987563431/4294967296), (84177223/1073741824)), (143/4294967296), by norm_num⟩
  | 4 => ⟨((-256697553/2147483648), (-350083229/8589934592)), (151/8589934592), by norm_num⟩
  | 5 => ⟨((854060089/17179869184), (72797761/4294967296)), (1/134217728), by norm_num⟩
  | 6 => ⟨((-591989343/34359738368), (-201838251/34359738368)), (45/17179869184), by norm_num⟩
  | 7 => ⟨((343473/67108864), (14989673/8589934592)), (27/34359738368), by norm_num⟩
  | 8 => ⟨((-1462747187/1099511627776), (-124680595/274877906944)), (57/274877906944), by norm_num⟩
  | 9 => ⟨((1351865451/4398046511104), (460917349/4398046511104)), (107/2199023255552), by norm_num⟩
  | 10 => ⟨((-1124450071/17592186044416), (-383380273/17592186044416)), (45/4398046511104), by norm_num⟩
  | 11 => ⟨((212566199/17592186044416), (144948521/35184372088832)), (69/35184372088832), by norm_num⟩
  | 12 => ⟨((-294679323/140737488355328), (-401882635/562949953421312)), (97/281474976710656), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790802825208669/5070602400912917605986812821504), (-3664251280163/10141204801825835211973625643008)), (58233/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779152369838741/633825300114114700748351602688), (-4338276624085/633825300114114700748351602688)), (69471/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236271600025855/4951760157141521099596496896), (-2439877198183/19807040628566084398385987584)), (78175/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944987022118797/1237940039285380274899124224), (-647971697843/309485009821345068724781056)), (20771/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885819717552445/77371252455336267181195264), (-5182687383895/154742504910672534362390528)), (83111/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549973214524995/9671406556917033397649408), (-4857615404647/9671406556917033397649408)), (77945/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39348596494561/18889465931478580854784), (-4249259538103/604462909807314587353088)), (68231/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888385744244307/75557863725914323419136), (-3451441636843/37778931862957161709568)), (6933/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1297983234405903/4722366482869645213696), (-2587634789007/2361183241434822606848)), (83243/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811027944283877/295147905179352825856), (-3556460026351/295147905179352825856)), (114535/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912115350570329/36893488147419103232), (-8886537181957/73786976294838206464)), (71641/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823502481300117/9223372036854775808), (-2497753124511/2305843009213693952)), (161349/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594744734261507/1152921504606846976), (-9983086540191/1152921504606846976)), (80773/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195237754911069/144115188075855872), (-8726285861125/144115188075855872)), (70787/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492608876808079/36028797018963968), (-13071603700941/36028797018963968)), (212803/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490447573966595/9007199254740992), (-16308321221731/9007199254740992)), (133389/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115127400397871/2251799813685248), (-16261567327271/2251799813685248)), (267943/2251799813685248), by norm_num⟩
  | 1 => ⟨((8669461502811/8796093022208), (-6068885352593/281474976710656)), (404831/1125899906842624), by norm_num⟩
  | 0 => ⟨((546642276145795/562949953421312), (-48084302707459/1125899906842624)), (821371/1125899906842624), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((546642276145795/562949953421312), (-48084302707459/1125899906842624)), (3133281712058639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((264890112536289/281474976710656), (-93382768820365/1125899906842624)), (1665313/1125899906842624), by norm_num⟩
  | 2 => ⟨((494692289798259/562949953421312), (-43940268564627/281474976710656)), (1705313/562949953421312), by norm_num⟩
  | 3 => ⟨((841984163385655/1125899906842624), (-308900099392215/1125899906842624)), (7059023/1125899906842624), by norm_num⟩
  | 4 => ⟨((1089827001954761/2251799813685248), (-231005429679687/562949953421312)), (7215667/562949953421312), by norm_num⟩
  | 5 => ⟨((296568776226417/4503599627370496), (-1788833649123125/4503599627370496)), (103250827/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1381993535255575/9007199254740992), (-235594746464099/4503599627370496)), (191242161/9007199254740992), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-30526335/16777216), (-937703595/33554432)), (3/67108864), by norm_num⟩, -4, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile036Terms0

/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile009Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨9,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (2679/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (2679/640))
  have he : value ((3/4), (2679/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-47632711549/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-17862266831/34359738368), (-49846888375/17179869184)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-47632711549/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-650256493812469/1125899906842624), (-39803156321825/281474976710656)), (220203/2251799813685248), by norm_num⟩
  | 1 => ⟨((110039906085/274877906944), (26942817951/274877906944)), (21/274877906944), by norm_num⟩
  | 2 => ⟨((-19068462663/137438953472), (-18675338299/549755813888)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((8811500755/274877906944), (17259677451/2199023255552)), (17/2199023255552), by norm_num⟩
  | 4 => ⟨((-97722670477/17592186044416), (-23926993525/17592186044416)), (25/17592186044416), by norm_num⟩
  | 5 => ⟨((27094477407/35184372088832), (13267942481/70368744177664)), (15/70368744177664), by norm_num⟩
  | 6 => ⟨((-50081228329/562949953421312), (-24524365127/1125899906842624)), (15/562949953421312), by norm_num⟩
  | 7 => ⟨((79345513635/9007199254740992), (19427422335/9007199254740992)), (13/4503599627370496), by norm_num⟩
  | 8 => ⟨((-27499059533/36028797018963968), (-13466063017/72057594037927936)), (19/72057594037927936), by norm_num⟩
  | 9 => ⟨((67772073185/1152921504606846976), (16593713091/1152921504606846976)), (25/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-37580817159/9223372036854775808), (-9201508355/9223372036854775808)), (15/9223372036854775808), by norm_num⟩
  | 11 => ⟨((9472377257/36893488147419103232), (579818143/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-70034683615/4722366482869645213696), (-8573851969/2361183241434822606848)), (1/147573952589676412928), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((24739040482979/158456325028528675187087900672), (-944872409199/2535301200456458802993406410752)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890579112993633/316912650057057350374175801344), (-2242153215071/316912650057057350374175801344)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((473107269104265/9903520314283042199192993792), (-315286091741/2475880078570760549798248448)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892370999349449/2475880078570760549798248448), (-5359575376097/2475880078570760549798248448)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((887018004582527/77371252455336267181195264), (-5359250899683/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776109798782179/4835703278458516698824704), (-2511976354563/4835703278458516698824704)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((4926251045057/2361183241434822606848), (-1098903331657/151115727451828646838272)), (45/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1891578400395067/75557863725914323419136), (-1785555906343/18889465931478580854784)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650188530048903/2361183241434822606848), (-669512511031/590295810358705651712)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1625346314733283/590295810358705651712), (-3681857044491/295147905179352825856)), (75/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828342105462881/73786976294838206464), (-4601627666049/36893488147419103232)), (47/18446744073709551616), by norm_num⟩
  | 7 => ⟨((457031392163979/2305843009213693952), (-2587937880807/2305843009213693952)), (211/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599365013276603/1152921504606846976), (-10349358294927/1152921504606846976)), (211/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299819333130261/36028797018963968), (-4526494750961/72057594037927936)), (93/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498661892349583/36028797018963968), (-13574069695959/36028797018963968)), (139/18014398509481984), by norm_num⟩
  | 3 => ⟨((374500672350363/2251799813685248), (-4239518616053/2251799813685248)), (87/2251799813685248), by norm_num⟩
  | 2 => ⟨((561332852614763/1125899906842624), (-16943731229397/2251799813685248)), (175/1125899906842624), by norm_num⟩
  | 1 => ⟨((1120956225848705/1125899906842624), (-3172434922297/140737488355328)), (529/1125899906842624), by norm_num⟩
  | 0 => ⟨((1115643991946673/1125899906842624), (-50612936635659/1125899906842624)), (67/70368744177664), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1115643991946673/1125899906842624), (-50612936635659/1125899906842624)), (255584985232331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((4309399529625/4398046511104), (-25075949615583/281474976710656)), (1111/562949953421312), by norm_num⟩
  | 2 => ⟨((67002139576977/70368744177664), (-196564152207963/1125899906842624)), (4751/1125899906842624), by norm_num⟩
  | 3 => ⟨((493214327729107/562949953421312), (-187160065395177/562949953421312)), (10707/1125899906842624), by norm_num⟩
  | 4 => ⟨((23118338687683/35184372088832), (-655902182924833/1125899906842624)), (12941/562949953421312), by norm_num⟩
  | 5 => ⟨((207970338055115/2251799813685248), (-1723875449311765/2251799813685248)), (8021/140737488355328), by norm_num⟩
  | 6 => ⟨((-650256493812469/1125899906842624), (-39803156321825/281474976710656)), (220203/2251799813685248), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/34359738368), (-49846888375/17179869184)), (1/17179869184), by norm_num⟩, 0, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-75496061613/68719476736), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-55294967/67108864), (-19751362213/4294967296)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-75496061613/68719476736), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-224086722555511/4503599627370496), (1962940826702411/4503599627370496)), (314281/2251799813685248), by norm_num⟩
  | 1 => ⟨((939119061/17179869184), (-16452872575/34359738368)), (23/137438953472), by norm_num⟩
  | 2 => ⟨((-8253821927/274877906944), (72301311979/274877906944)), (27/274877906944), by norm_num⟩
  | 3 => ⟨((12090333597/1099511627776), (-26477036609/274877906944)), (21/549755813888), by norm_num⟩
  | 4 => ⟨((-1660323633/549755813888), (116351991145/4398046511104)), (49/4398046511104), by norm_num⟩
  | 5 => ⟨((11673932457/17592186044416), (-51130290913/8796093022208)), (23/8796093022208), by norm_num⟩
  | 6 => ⟨((-4275041885/35184372088832), (37448243947/35184372088832)), (9/17592186044416), by norm_num⟩
  | 7 => ⟨((2683779171/140737488355328), (-94036802261/562949953421312)), (3/35184372088832), by norm_num⟩
  | 8 => ⟨((-11793731109/4503599627370496), (103309986551/4503599627370496)), (55/4503599627370496), by norm_num⟩
  | 9 => ⟨((5758550189/18014398509481984), (-100886774015/36028797018963968)), (7/4503599627370496), by norm_num⟩
  | 10 => ⟨((-2530565601/72057594037927936), (44334179879/144115188075855872)), (13/72057594037927936), by norm_num⟩
  | 11 => ⟨((2021898521/576460752303423488), (-70845199743/2305843009213693952)), (11/576460752303423488), by norm_num⟩
  | 12 => ⟨((-11846840329/36893488147419103232), (51887604687/18446744073709551616)), (67/36893488147419103232), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791451234115199/5070602400912917605986812821504), (548550259425/2535301200456458802993406410752)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780695449782823/633825300114114700748351602688), (1301041307377/316912650057057350374175801344)), (181/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945954460643407/19807040628566084398385987584), (2927120571269/39614081257132168796771975168)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891818898943815/2475880078570760549798248448), (777450834237/618970019642690137449562112)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773484543737595/154742504910672534362390528), (194344266027/9671406556917033397649408)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551703273313251/9671406556917033397649408), (364356306521/1208925819614629174706176)), (203/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260669158315257/604462909807314587353088), (2550180590327/604462909807314587353088)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((118177913276079/4722366482869645213696), (1035863876701/18889465931478580854784)), (289/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299829325370233/4722366482869645213696), (3107077135491/4722366482869645213696)), (217/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624594976801247/590295810358705651712), (2135697469905/295147905179352825856)), (149/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1827405628416483/73786976294838206464), (5337989374215/73786976294838206464)), (373/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913537868559429/4611686018427387904), (6003513190929/9223372036854775808)), (105/2305843009213693952), by norm_num⟩
  | 6 => ⟨((799159905836573/576460752303423488), (6001356835179/1152921504606846976)), (105/288230376151711744), by norm_num⟩
  | 5 => ⟨((1198367987735995/144115188075855872), (1312190234331/36028797018963968)), (23/9007199254740992), by norm_num⟩
  | 4 => ⟨((1497308283245431/36028797018963968), (7868287839819/36028797018963968)), (69/4503599627370496), by norm_num⟩
  | 3 => ⟨((1461258672345/8796093022208), (2456715966557/2251799813685248)), (691/9007199254740992), by norm_num⟩
  | 2 => ⟨((280254794132675/562949953421312), (4907057803391/1125899906842624)), (693/2251799813685248), by norm_num⟩
  | 1 => ⟨((1118554550621691/1125899906842624), (14689287623249/1125899906842624)), (1043/1125899906842624), by norm_num⟩
  | 0 => ⟨((138889076457699/140737488355328), (14625471108443/562949953421312)), (2103/1125899906842624), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((138889076457699/140737488355328), (14625471108443/562949953421312)), (8022312644576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1095759588108141/1125899906842624), (14433383732711/281474976710656)), (4261/1125899906842624), by norm_num⟩
  | 2 => ⟨((531732841702187/562949953421312), (112376018634295/1125899906842624)), (2183/281474976710656), by norm_num⟩
  | 3 => ⟨((496638681386335/562949953421312), (106144461624765/562949953421312)), (285/17592186044416), by norm_num⟩
  | 4 => ⟨((104531198415157/140737488355328), (187282884161937/562949953421312)), (19531/562949953421312), by norm_num⟩
  | 5 => ⟨((993008089080613/2251799813685248), (139102271561557/281474976710656)), (168033/2251799813685248), by norm_num⟩
  | 6 => ⟨((-224086722555511/4503599627370496), (1962940826702411/4503599627370496)), (314281/2251799813685248), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/67108864), (-19751362213/4294967296)), (1/8589934592), by norm_num⟩, -1, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-47632711549/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-17862266831/17179869184), (-49846888375/8589934592)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-47632711549/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((1412149855519873/4503599627370496), (735618097919921/4503599627370496)), (284617/4503599627370496), by norm_num⟩
  | 1 => ⟨((-59742901055/137438953472), (-3890164265/17179869184)), (7/68719476736), by norm_num⟩
  | 2 => ⟨((82821246849/274877906944), (43143302275/274877906944)), (11/137438953472), by norm_num⟩
  | 3 => ⟨((-1195985703/8589934592), (-2492054861/34359738368)), (23/549755813888), by norm_num⟩
  | 4 => ⟨((53055623553/1099511627776), (27637772811/1099511627776)), (9/549755813888), by norm_num⟩
  | 5 => ⟨((-29420284703/2199023255552), (-30651270881/4398046511104)), (11/2199023255552), by norm_num⟩
  | 6 => ⟨((6797529131/2199023255552), (14163894661/8796093022208)), (11/8796093022208), by norm_num⟩
  | 7 => ⟨((-86156583349/140737488355328), (-22440374057/70368744177664)), (37/140737488355328), by norm_num⟩
  | 8 => ⟨((59719192835/562949953421312), (31108964017/562949953421312)), (7/140737488355328), by norm_num⟩
  | 9 => ⟨((-36794835679/2251799813685248), (-4791797933/562949953421312)), (9/1125899906842624), by norm_num⟩
  | 10 => ⟨((2550423661/1125899906842624), (21257095853/18014398509481984)), (21/18014398509481984), by norm_num⟩
  | 11 => ⟨((-41141968753/144115188075855872), (-5357925839/36028797018963968)), (45/288230376151711744), by norm_num⟩
  | 12 => ⟨((76046505717/2305843009213693952), (39614199349/2305843009213693952)), (11/576460752303423488), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582621414715929/10141204801825835211973625643008), (312785555147/5070602400912917605986812821504)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111272845393159/39614081257132168796771975168), (741595343323/633825300114114700748351602688)), (181/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891537988059643/39614081257132168796771975168), (834217161539/39614081257132168796771975168)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945712532702333/1237940039285380274899124224), (886261672923/2475880078570760549798248448)), (27/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1773091028520307/154742504910672534362390528), (886155870033/154742504910672534362390528)), (27/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1551334690935033/9671406556917033397649408), (830658729209/9671406556917033397649408)), (203/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260346986783471/604462909807314587353088), (363357003905/302231454903657293676544)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890323717331513/75557863725914323419136), (590349794729/37778931862957161709568)), (9/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((1299437708313897/4722366482869645213696), (885340392737/4722366482869645213696)), (27/590295810358705651712), by norm_num⟩
  | 9 => ⟨((812028701832061/295147905179352825856), (304260907005/147573952589676412928)), (297/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826735011848857/73786976294838206464), (760427773655/36893488147419103232)), (371/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456580787130773/2305843009213693952), (1710345344249/9223372036854775808)), (209/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399392385092971/288230376151711744), (1709574228491/1152921504606846976)), (209/576460752303423488), by norm_num⟩
  | 5 => ⟨((299428526307281/36028797018963968), (1495010380859/144115188075855872)), (183/72057594037927936), by norm_num⟩
  | 4 => ⟨((748166332031529/18014398509481984), (1120391261495/18014398509481984)), (137/9007199254740992), by norm_num⟩
  | 3 => ⟨((373779613212451/2251799813685248), (2797947769867/9007199254740992)), (343/4503599627370496), by norm_num⟩
  | 2 => ⟨((139977796261947/281474976710656), (87293971613/70368744177664)), (343/1125899906842624), by norm_num⟩
  | 1 => ⟨((1116793312357033/1125899906842624), (8357552132777/2251799813685248)), (2059/2251799813685248), by norm_num⟩
  | 0 => ⟨((2215451062600647/2251799813685248), (8312316461517/1125899906842624)), (129/70368744177664), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2215451062600647/2251799813685248), (8312316461517/1125899906842624)), (492096215701081/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((2179566319586051/2251799813685248), (16356276632959/1125899906842624)), (8185/2251799813685248), by norm_num⟩
  | 2 => ⟨((1054587357514671/1125899906842624), (63326392419735/2251799813685248)), (4021/562949953421312), by norm_num⟩
  | 3 => ⟨((493450585563849/562949953421312), (118630816890547/2251799813685248)), (7759/562949953421312), by norm_num⟩
  | 4 => ⟨((1723875449311749/2251799813685248), (103985169027535/1125899906842624)), (3605/140737488355328), by norm_num⟩
  | 5 => ⟨((650256493812461/1125899906842624), (4975394540227/35184372088832)), (98969/2251799813685248), by norm_num⟩
  | 6 => ⟨((1412149855519873/4503599627370496), (735618097919921/4503599627370496)), (284617/4503599627370496), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/17179869184), (-49846888375/8589934592)), (1/8589934592), by norm_num⟩, -1, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-55299865591/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-20737449597/17179869184), (-115740890561/17179869184)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-55299865591/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((1210556091248283/4503599627370496), (-295240501411605/2251799813685248)), (236701/4503599627370496), by norm_num⟩
  | 1 => ⟨((-7432231401/17179869184), (29002151871/137438953472)), (13/137438953472), by norm_num⟩
  | 2 => ⟨((47846859963/137438953472), (-11669290691/68719476736)), (3/34359738368), by norm_num⟩
  | 3 => ⟨((-51337700277/274877906944), (25041331799/274877906944)), (7/137438953472), by norm_num⟩
  | 4 => ⟨((82624841163/1099511627776), (-40302468775/1099511627776)), (25/1099511627776), by norm_num⟩
  | 5 => ⟨((-53191820751/2199023255552), (25945728485/2199023255552)), (9/1099511627776), by norm_num⟩
  | 6 => ⟨((28536310983/4398046511104), (-13919346363/4398046511104)), (21/8796093022208), by norm_num⟩
  | 7 => ⟨((-6561060111/4398046511104), (12801327859/17592186044416)), (21/35184372088832), by norm_num⟩
  | 8 => ⟨((21119237777/70368744177664), (-10301471193/70368744177664)), (9/70368744177664), by norm_num⟩
  | 9 => ⟨((-60426847929/1125899906842624), (7368701463/281474976710656)), (7/281474976710656), by norm_num⟩
  | 10 => ⟨((77802607989/9007199254740992), (-592973375/140737488355328)), (19/4503599627370496), by norm_num⟩
  | 11 => ⟨((-91067975989/72057594037927936), (44420832851/72057594037927936)), (47/72057594037927936), by norm_num⟩
  | 12 => ⟨((48856084389/288230376151711744), (-11915428749/144115188075855872)), (27/288230376151711744), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582403412673631/10141204801825835211973625643008), (-591152788155/10141204801825835211973625643008)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445026789646935/158456325028528675187087900672), (-175150062215/158456325028528675187087900672)), (181/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945623677747935/19807040628566084398385987584), (-788090522707/39614081257132168796771975168)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945558153021461/1237940039285380274899124224), (-209310758215/618970019642690137449562112)), (27/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1772782311606355/154742504910672534362390528), (-209281753343/38685626227668133590597632)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551045313921989/9671406556917033397649408), (-392341663017/4835703278458516698824704)), (203/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260093826982977/604462909807314587353088), (-686474685693/604462909807314587353088)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889912417175095/75557863725914323419136), (-139411296253/9444732965739290427392)), (9/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((1299129307134335/4722366482869645213696), (-836265709427/4722366482869645213696)), (27/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1623633472159745/590295810358705651712), (-1149537087021/590295810358705651712)), (149/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456551319397465/18446744073709551616), (-1436429133675/73786976294838206464)), (371/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912863722529855/4611686018427387904), (-807653121055/4611686018427387904)), (209/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399243536561869/288230376151711744), (-1614460989699/1152921504606846976)), (209/576460752303423488), by norm_num⟩
  | 5 => ⟨((299298370798275/36028797018963968), (-1411703026231/144115188075855872)), (183/72057594037927936), by norm_num⟩
  | 4 => ⟨((747776213098057/18014398509481984), (-2115655281973/36028797018963968)), (137/9007199254740992), by norm_num⟩
  | 3 => ⟨((1494144371062303/9007199254740992), (-2641248599457/9007199254740992)), (685/9007199254740992), by norm_num⟩
  | 2 => ⟨((2237700219132601/4503599627370496), (-2636274233693/2251799813685248)), (343/1125899906842624), by norm_num⟩
  | 1 => ⟨((1115339467501389/1125899906842624), (-492749721203/140737488355328)), (2059/2251799813685248), by norm_num⟩
  | 0 => ⟨((2209671964298419/2251799813685248), (-15668949999383/2251799813685248)), (2063/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2209671964298419/2251799813685248), (-15668949999383/2251799813685248)), (7869724753951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2168223233761579/2251799813685248), (-30751614164997/2251799813685248)), (2039/562949953421312), by norm_num⟩
  | 2 => ⟨((1043664339317411/1125899906842624), (-59220507882623/2251799813685248)), (7965/1125899906842624), by norm_num⟩
  | 3 => ⟨((483328260092177/562949953421312), (-27447525245243/562949953421312)), (7593/562949953421312), by norm_num⟩
  | 4 => ⟨((413629735550179/562949953421312), (-188523538051575/2251799813685248)), (55115/2251799813685248), by norm_num⟩
  | 5 => ⟨((1199880997094335/2251799813685248), (-277036851021453/2251799813685248)), (45111/1125899906842624), by norm_num⟩
  | 6 => ⟨((1210556091248283/4503599627370496), (-295240501411605/2251799813685248)), (236701/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20737449597/17179869184), (-115740890561/17179869184)), (1/8589934592), by norm_num⟩, -1, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-61564386581/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-2885830621/2147483648), (-64426168613/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-61564386581/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((406997821116827/4503599627370496), (-68874771668167/281474976710656)), (321239/2251799813685248), by norm_num⟩
  | 1 => ⟨((-22254705809/137438953472), (60257336097/137438953472)), (37/137438953472), by norm_num⟩
  | 2 => ⟨((9968769967/68719476736), (-53983326271/137438953472)), (17/68719476736), by norm_num⟩
  | 3 => ⟨((-23815517313/274877906944), (32241712009/137438953472)), (21/137438953472), by norm_num⟩
  | 4 => ⟨((10667919665/274877906944), (-14442348199/137438953472)), (39/549755813888), by norm_num⟩
  | 5 => ⟨((-30582953723/2199023255552), (82807085259/2199023255552)), (29/1099511627776), by norm_num⟩
  | 6 => ⟨((36531531287/8796093022208), (-12364198261/1099511627776)), (71/8796093022208), by norm_num⟩
  | 7 => ⟨((-4675408365/4398046511104), (50636958431/17592186044416)), (19/8796093022208), by norm_num⟩
  | 8 => ⟨((16754414421/70368744177664), (-45364624881/70368744177664)), (35/70368744177664), by norm_num⟩
  | 9 => ⟨((-26684338391/562949953421312), (18062776933/140737488355328)), (57/562949953421312), by norm_num⟩
  | 10 => ⟨((19124766397/2251799813685248), (-3236415161/140737488355328)), (21/1125899906842624), by norm_num⟩
  | 11 => ⟨((-24921440937/18014398509481984), (33738923701/9007199254740992)), (57/18014398509481984), by norm_num⟩
  | 12 => ⟨((7442204631/36028797018963968), (-80602714697/144115188075855872)), (35/72057594037927936), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646017817/5070602400912917605986812821504), (-396322149755/2535301200456458802993406410752)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779894461947885/633825300114114700748351602688), (-469592346831/158456325028528675187087900672)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236376000473557/4951760157141521099596496896), (-1056455730275/19807040628566084398385987584)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472715477022527/618970019642690137449562112), (-1122330178507/1237940039285380274899124224)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1772527816101105/154742504910672534362390528), (-2244313827365/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387701655197137/2417851639229258349412352), (-525919020141/2417851639229258349412352)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259884866952665/604462909807314587353088), (-230043562493/75557863725914323419136)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889572663115787/75557863725914323419136), (-2989876311959/75557863725914323419136)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298874321955737/4722366482869645213696), (-2241803615395/4722366482869645213696)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623282592117393/590295810358705651712), (-3081499338123/590295810358705651712)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912883132406469/36893488147419103232), (-240650228471/4611686018427387904)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((114077061803369/576460752303423488), (-4329682854089/9223372036854775808)), (837/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399119745624199/288230376151711744), (-4327157334933/1152921504606846976)), (837/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196759420290001/144115188075855872), (-3783422907797/144115188075855872)), (733/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494899746012275/36028797018963968), (-708682307801/4503599627370496)), (275/9007199254740992), by norm_num⟩
  | 3 => ⟨((1493325753301735/9007199254740992), (-7076898400137/9007199254740992)), (1377/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118027355826111/2251799813685248), (-14124055340469/4503599627370496)), (1379/2251799813685248), by norm_num⟩
  | 1 => ⟨((557047525220793/562949953421312), (-2638980415717/281474976710656)), (4149/2251799813685248), by norm_num⟩
  | 0 => ⟨((1102306322363273/1125899906842624), (-20963705673547/1125899906842624)), (4175/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1102306322363273/1125899906842624), (-20963705673547/1125899906842624)), (15926365378951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2157633629747261/2251799813685248), (-10262202334183/281474976710656)), (8331/1125899906842624), by norm_num⟩
  | 2 => ⟨((2064412135116317/2251799813685248), (-39332222583795/562949953421312)), (16573/1125899906842624), by norm_num⟩
  | 3 => ⟨((470406500849997/562949953421312), (-288472952558587/2251799813685248)), (511/17592186044416), by norm_num⟩
  | 4 => ⟨((1535349524101345/2251799813685248), (-482101655318531/2251799813685248)), (126071/2251799813685248), by norm_num⟩
  | 5 => ⟨((943634572746425/2251799813685248), (-657424823079979/2251799813685248)), (112951/1125899906842624), by norm_num⟩
  | 6 => ⟨((406997821116827/4503599627370496), (-68874771668167/281474976710656)), (321239/2251799813685248), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2885830621/2147483648), (-64426168613/8589934592)), (1/4294967296), by norm_num⟩, -1, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-66860963609/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-12536430677/8589934592), (-34984476857/4294967296)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-66860963609/34359738368), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-300727375991021/4503599627370496), (-1002352345664213/4503599627370496)), (1367/8796093022208), by norm_num⟩
  | 1 => ⟨((17858534333/137438953472), (59524157787/137438953472)), (43/137438953472), by norm_num⟩
  | 2 => ⟨((-17375551603/137438953472), (-3619645711/8589934592)), (43/137438953472), by norm_num⟩
  | 3 => ⟨((22540841473/274877906944), (75130723467/274877906944)), (57/274877906944), by norm_num⟩
  | 4 => ⟨((-21931226095/549755813888), (-36549409325/274877906944)), (57/549755813888), by norm_num⟩
  | 5 => ⟨((533452443/34359738368), (28448746619/549755813888)), (23/549755813888), by norm_num⟩
  | 6 => ⟨((-22145077821/4398046511104), (-73811606365/4398046511104)), (61/4398046511104), by norm_num⟩
  | 7 => ⟨((24624189533/17592186044416), (82074716539/17592186044416)), (35/8796093022208), by norm_num⟩
  | 8 => ⟨((-11979115081/35184372088832), (-79855011947/70368744177664)), (35/35184372088832), by norm_num⟩
  | 9 => ⟨((10360125161/140737488355328), (69062523645/281474976710656)), (63/281474976710656), by norm_num⟩
  | 10 => ⟨((-16127898157/1125899906842624), (-1679868321/35184372088832)), (25/562949953421312), by norm_num⟩
  | 11 => ⟨((11412160257/4503599627370496), (38037792755/4503599627370496)), (73/9007199254740992), by norm_num⟩
  | 12 => ⟨((-14804692311/36028797018963968), (-98690835959/72057594037927936)), (97/72057594037927936), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693181983/10141204801825835211973625643008), (-1212909225389/5070602400912917605986812821504)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((55616047203605/19807040628566084398385987584), (-179609045351/39614081257132168796771975168)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945402155909643/19807040628566084398385987584), (-3232537407867/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((945322664841183/1237940039285380274899124224), (-3434058659171/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772311062643867/154742504910672534362390528), (-3433482316573/154742504910672534362390528)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775301614265069/4835703278458516698824704), (-1609138685485/4835703278458516698824704)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259706712944341/604462909807314587353088), (-2815380469815/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889282814744357/75557863725914323419136), (-2286922741807/37778931862957161709568)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298656631316419/4722366482869645213696), (-3429379956431/4722366482869645213696)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811491386670039/295147905179352825856), (-294610373097/36893488147419103232)), (149/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912695375442497/36893488147419103232), (-1472440188097/18446744073709551616)), (745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912404759400891/4611686018427387904), (-6622617427763/9223372036854775808)), (839/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596054243205899/1152921504606846976), (-3309207182903/576460752303423488)), (839/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598193174039827/72057594037927936), (-2893192896279/72057594037927936)), (23/4503599627370496), by norm_num⟩
  | 4 => ⟨((23349020209947/562949953421312), (-2167532326579/9007199254740992)), (69/2251799813685248), by norm_num⟩
  | 3 => ⟨((746308862257485/4503599627370496), (-5410567307105/4503599627370496)), (691/4503599627370496), by norm_num⟩
  | 2 => ⟨((1117311911176595/2251799813685248), (-10796362918915/2251799813685248)), (693/1125899906842624), by norm_num⟩
  | 1 => ⟨((556501722110953/562949953421312), (-16132681194949/1125899906842624)), (2089/1125899906842624), by norm_num⟩
  | 0 => ⟨((1100049954038117/1125899906842624), (-32018307102143/1125899906842624)), (2109/562949953421312), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1100049954038117/1125899906842624), (-32018307102143/1125899906842624)), (8045198680686773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1073882964232787/1125899906842624), (-62566373870415/1125899906842624)), (8483/1125899906842624), by norm_num⟩
  | 2 => ⟨((1020792401478325/1125899906842624), (-119351574016339/1125899906842624)), (8563/562949953421312), by norm_num⟩
  | 3 => ⟨((114105650339059/140737488355328), (-108209601155413/562949953421312)), (17343/562949953421312), by norm_num⟩
  | 4 => ⟨((1397014225166373/2251799813685248), (-87733034439229/281474976710656)), (17395/281474976710656), by norm_num⟩
  | 5 => ⟨((647941826448071/2251799813685248), (-870871709882793/2251799813685248)), (64855/562949953421312), by norm_num⟩
  | 6 => ⟨((-300727375991021/4503599627370496), (-1002352345664213/4503599627370496)), (1367/8796093022208), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-12536430677/8589934592), (-34984476857/4294967296)), (1/4294967296), by norm_num⟩, -1, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-17862266831/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-13396700123/8589934592), (-74770332563/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-17862266831/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-355777596394133/2251799813685248), (-624542667278915/4503599627370496)), (333907/2251799813685248), by norm_num⟩
  | 1 => ⟨((22577475389/68719476736), (39633177701/137438953472)), (11/34359738368), by norm_num⟩
  | 2 => ⟨((-23474270115/68719476736), (-20603719035/68719476736)), (3/8589934592), by norm_num⟩
  | 3 => ⟨((8135562073/34359738368), (57125639033/274877906944)), (69/274877906944), by norm_num⟩
  | 4 => ⟨((-33834851479/274877906944), (-29697356725/274877906944)), (75/549755813888), by norm_num⟩
  | 5 => ⟨((28143038289/549755813888), (24701566901/549755813888)), (65/1099511627776), by norm_num⟩
  | 6 => ⟨((-39014535285/2199023255552), (-17121821453/1099511627776)), (47/2199023255552), by norm_num⟩
  | 7 => ⟨((23179555829/4398046511104), (20345043885/4398046511104)), (29/4398046511104), by norm_num⟩
  | 8 => ⟨((-48200531309/35184372088832), (-21153164711/17592186044416)), (31/17592186044416), by norm_num⟩
  | 9 => ⟨((22273374919/70368744177664), (9774837653/35184372088832)), (59/140737488355328), by norm_num⟩
  | 10 => ⟨((-1157904527/17592186044416), (-16260962783/281474976710656)), (51/562949953421312), by norm_num⟩
  | 11 => ⟨((28017975561/2251799813685248), (6147949367/562949953421312)), (5/281474976710656), by norm_num⟩
  | 12 => ⟨((-19420580765/9007199254740992), (-2130716885/1125899906842624)), (29/9007199254740992), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238521241/10141204801825835211973625643008), (-1576959263289/5070602400912917605986812821504)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779555934500023/633825300114114700748351602688), (-3735671234877/633825300114114700748351602688)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472656721710677/9903520314283042199192993792), (-4202034015597/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890456619914539/2475880078570760549798248448), (-1115987180775/618970019642690137449562112)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886061066405787/77371252455336267181195264), (-17434168855/604462909807314587353088)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550425873126657/9671406556917033397649408), (-4183348977153/9671406556917033397649408)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259551293429867/604462909807314587353088), (-1829789426867/302231454903657293676544)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1889029820469675/75557863725914323419136), (-2972609586017/37778931862957161709568)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324616625764815/1180591620717411303424), (-2228758785877/2361183241434822606848)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405680181483793/147573952589676412928), (-6126817037081/590295810358705651712)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825062261091563/73786976294838206464), (-7655117189797/73786976294838206464)), (747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456109672496045/2305843009213693952), (-4303663364745/4611686018427387904)), (105/1152921504606846976), by norm_num⟩
  | 6 => ⟨((199460227458789/144115188075855872), (-8601477402791/1152921504606846976)), (841/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196058686907875/144115188075855872), (-7519713353571/144115188075855872)), (737/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493842229215869/36028797018963968), (-11266414095681/36028797018963968)), (1107/36028797018963968), by norm_num⟩
  | 3 => ⟨((745996330986257/4503599627370496), (-14060001108353/9007199254740992)), (1387/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116677539282233/2251799813685248), (-14025489202687/2251799813685248)), (87/140737488355328), by norm_num⟩
  | 1 => ⟨((556014374744349/562949953421312), (-5237999889579/281474976710656)), (2101/1125899906842624), by norm_num⟩
  | 0 => ⟨((1098008834492979/1125899906842624), (-20779669632587/562949953421312)), (2127/562949953421312), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1098008834492979/1125899906842624), (-20779669632587/562949953421312)), (8113863231468023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1069274643889593/1125899906842624), (-81059641965545/1125899906842624)), (8613/1125899906842624), by norm_num⟩
  | 2 => ⟨((504830665497395/562949953421312), (-153965764220711/1125899906842624)), (17601/1125899906842624), by norm_num⟩
  | 3 => ⟨((884368619894807/1125899906842624), (-276140494347589/1125899906842624)), (36383/1125899906842624), by norm_num⟩
  | 4 => ⟨((626924541823217/1125899906842624), (-216902041113129/562949953421312)), (75003/1125899906842624), by norm_num⟩
  | 5 => ⟨((363883855286113/2251799813685248), (-966204629160707/2251799813685248)), (282647/2251799813685248), by norm_num⟩
  | 6 => ⟨((-355777596394133/2251799813685248), (-624542667278915/4503599627370496)), (333907/2251799813685248), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13396700123/8589934592), (-74770332563/8589934592)), (1/4294967296), by norm_num⟩, -1, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile009Terms0

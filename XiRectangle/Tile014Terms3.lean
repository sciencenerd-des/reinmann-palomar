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
namespace Reinmann.XiRectangle.Tile014Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨14,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (4089/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (4089/640))
  have he : value ((3/4), (4089/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-53103704991/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4978472343/2147483648), (-42410361271/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-53103704991/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((137914350572993/2251799813685248), (-347093900330537/4503599627370496)), (211027/2251799813685248), by norm_num⟩
  | 1 => ⟨((-52038465887/274877906944), (32741759681/137438953472)), (41/137438953472), by norm_num⟩
  | 2 => ⟨((2513329801/8589934592), (-25301542293/68719476736)), (65/137438953472), by norm_num⟩
  | 3 => ⟨((-41433648609/137438953472), (52138760909/137438953472)), (69/137438953472), by norm_num⟩
  | 4 => ⟨((31267863/134217728), (-40290780859/137438953472)), (55/137438953472), by norm_num⟩
  | 5 => ⟨((-19793979793/137438953472), (24908102823/137438953472)), (35/137438953472), by norm_num⟩
  | 6 => ⟨((20394677287/274877906944), (-12832000543/137438953472)), (37/274877906944), by norm_num⟩
  | 7 => ⟨((-36023321895/1099511627776), (22665290537/549755813888)), (67/1099511627776), by norm_num⟩
  | 8 => ⟨((13918702161/1099511627776), (-17514843817/1099511627776)), (53/2199023255552), by norm_num⟩
  | 9 => ⟨((-38242932689/8796093022208), (12030916845/2199023255552)), (37/4398046511104), by norm_num⟩
  | 10 => ⟨((47284211393/35184372088832), (-59500919553/35184372088832)), (93/35184372088832), by norm_num⟩
  | 11 => ⟨((-6643522945/17592186044416), (261249813/549755813888)), (107/140737488355328), by norm_num⟩
  | 12 => ⟨((27380548617/281474976710656), (-17227397609/140737488355328)), (113/562949953421312), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790477973085591/5070602400912917605986812821504), (-585724215497/5070602400912917605986812821504)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778392508547931/633825300114114700748351602688), (-1385790817227/633825300114114700748351602688)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889318630495927/39614081257132168796771975168), (-1558700266319/39614081257132168796771975168)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889067347768519/2475880078570760549798248448), (-1655727454719/2475880078570760549798248448)), (27/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1770733704314753/154742504910672534362390528), (-1655287106271/154742504910672534362390528)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774562558719153/4835703278458516698824704), (-1551363949459/9671406556917033397649408)), (405/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314603506959143/151115727451828646838272), (-678487960197/302231454903657293676544)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((58974482573705/2361183241434822606848), (-2204209618375/75557863725914323419136)), (1151/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648541593654307/2361183241434822606848), (-1652390869445/4722366482869645213696)), (27/147573952589676412928), by norm_num⟩
  | 9 => ⟨((810410525219997/295147905179352825856), (-2270792841305/590295810358705651712)), (297/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822691239475735/73786976294838206464), (-1418312689491/36893488147419103232)), (1485/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821776198751635/9223372036854775808), (-3188640254677/9223372036854775808)), (1671/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796512728436065/576460752303423488), (-796359784039/288230376151711744)), (1671/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596870627389555/72057594037927936), (-1391831054975/72057594037927936)), (1463/144115188075855872), by norm_num⟩
  | 4 => ⟨((372594957188835/9007199254740992), (-2084154597395/18014398509481984)), (549/9007199254740992), by norm_num⟩
  | 3 => ⟨((743844334216293/4503599627370496), (-324864855215/562949953421312)), (2747/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112409453412429/2251799813685248), (-10358121321025/4503599627370496)), (5501/4503599627370496), by norm_num⟩
  | 1 => ⟨((2211432060518431/2251799813685248), (-15443619464013/2251799813685248)), (8271/2251799813685248), by norm_num⟩
  | 0 => ⟨((1085738880676205/1125899906842624), (-953591202185/70368744177664)), (16619/2251799813685248), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1085738880676205/1125899906842624), (-953591202185/70368744177664)), (63396462447356467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2093607290997767/2251799813685248), (-58852893089523/2251799813685248)), (4063/281474976710656), by norm_num⟩
  | 2 => ⟨((121561866847475/140737488355328), (-27359191816187/562949953421312)), (62141/2251799813685248), by norm_num⟩
  | 3 => ⟨((13083316328447/17592186044416), (-189051799714767/2251799813685248)), (113389/2251799813685248), by norm_num⟩
  | 4 => ⟨((1229576694341367/2251799813685248), (-17574738095977/140737488355328)), (187695/2251799813685248), by norm_num⟩
  | 5 => ⟨((1272571171965925/4503599627370496), (-614178599447731/4503599627370496)), (503713/4503599627370496), by norm_num⟩
  | 6 => ⟨((137914350572993/2251799813685248), (-347093900330537/4503599627370496)), (211027/2251799813685248), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4978472343/2147483648), (-42410361271/2147483648)), (1/2147483648), by norm_num⟩, -3, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-53867380457/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2525033459/1073741824), (-86040515113/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-53867380457/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((162029726651517/4503599627370496), (-794036600861481/9007199254740992)), (469637/4503599627370496), by norm_num⟩
  | 1 => ⟨((-31008500411/274877906944), (37989763935/137438953472)), (23/68719476736), by norm_num⟩
  | 2 => ⟨((24306743421/137438953472), (-29779171271/68719476736)), (37/68719476736), by norm_num⟩
  | 3 => ⟨((-25404551135/137438953472), (62248279517/137438953472)), (79/137438953472), by norm_num⟩
  | 4 => ⟨((39827911571/274877906944), (-97589560189/274877906944)), (63/137438953472), by norm_num⟩
  | 5 => ⟨((-24976037273/274877906944), (30599150151/137438953472)), (81/274877906944), by norm_num⟩
  | 6 => ⟨((26104073469/549755813888), (-63962305541/549755813888)), (43/274877906944), by norm_num⟩
  | 7 => ⟨((-730796173/34359738368), (57300982589/1099511627776)), (79/1099511627776), by norm_num⟩
  | 8 => ⟨((4582814347/549755813888), (-44916724869/2199023255552)), (63/2199023255552), by norm_num⟩
  | 9 => ⟨((-25545578449/8796093022208), (62593836011/8796093022208)), (45/4398046511104), by norm_num⟩
  | 10 => ⟨((8009801347/8796093022208), (-39252522153/17592186044416)), (115/35184372088832), by norm_num⟩
  | 11 => ⟨((-1141576627/4398046511104), (44754929517/70368744177664)), (133/140737488355328), by norm_num⟩
  | 12 => ⟨((1193135637/17592186044416), (-11694068553/70368744177664)), (141/562949953421312), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790456259316641/5070602400912917605986812821504), (-770698384655/5070602400912917605986812821504)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((889170191995859/316912650057057350374175801344), (-1823329014159/633825300114114700748351602688)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472314990082445/9903520314283042199192993792), (-2050824992189/39614081257132168796771975168)), (813/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944502485064111/1237940039285380274899124224), (-2178478846873/2475880078570760549798248448)), (27/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((110666955066745/9671406556917033397649408), (-2126846707/151115727451828646838272)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774533273614821/4835703278458516698824704), (-2041148486895/9671406556917033397649408)), (405/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258362730536731/604462909807314587353088), (-1785380805713/604462909807314587353088)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887099993658565/75557863725914323419136), (-1450037037719/37778931862957161709568)), (9/590295810358705651712), by norm_num⟩
  | 10 => ⟨((1297020521620113/4722366482869645213696), (-2174032531001/4722366482869645213696)), (865/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810367378333197/295147905179352825856), (-186727077171/36893488147419103232)), (1189/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822583179910901/73786976294838206464), (-933012727867/18446744073709551616)), (743/36893488147419103232), by norm_num⟩
  | 7 => ⟨((113853397987411/576460752303423488), (-4195135272831/9223372036854775808)), (209/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1592903296793141/1152921504606846976), (-4190861691149/1152921504606846976)), (1673/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193633995544709/144115188075855872), (-1831100793785/72057594037927936)), (1465/144115188075855872), by norm_num⟩
  | 4 => ⟨((372554551080281/9007199254740992), (-685463881289/4503599627370496)), (2199/36028797018963968), by norm_num⟩
  | 3 => ⟨((743742678394011/4503599627370496), (-6837884213213/9007199254740992)), (43/140737488355328), by norm_num⟩
  | 2 => ⟨((2224408464826031/4503599627370496), (-6812812672239/2251799813685248)), (5513/4503599627370496), by norm_num⟩
  | 1 => ⟨((552701734123027/562949953421312), (-10156750958083/1125899906842624)), (8295/2251799813685248), by norm_num⟩
  | 0 => ⟨((67818443155095/70368744177664), (-20064890912367/1125899906842624)), (16693/2251799813685248), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((67818443155095/70368744177664), (-20064890912367/1125899906842624)), (63678750045012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2090823080073841/2251799813685248), (-2417212499057/70368744177664)), (8193/562949953421312), by norm_num⟩
  | 2 => ⟨((1938697205400737/2251799813685248), (-143642287255015/2251799813685248)), (63111/2251799813685248), by norm_num⟩
  | 3 => ⟨((1659967162633069/2251799813685248), (-247338950102243/2251799813685248)), (29181/562949953421312), by norm_num⟩
  | 4 => ⟨((1196515963989243/2251799813685248), (-364663441851809/2251799813685248)), (197735/2251799813685248), by norm_num⟩
  | 5 => ⟨((1153451579812081/4503599627370496), (-775070016450301/4503599627370496)), (274181/2251799813685248), by norm_num⟩
  | 6 => ⟨((162029726651517/4503599627370496), (-794036600861481/9007199254740992)), (469637/4503599627370496), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2525033459/1073741824), (-86040515113/4294967296)), (1/2147483648), by norm_num⟩, -3, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-54598549065/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5118613975/2147483648), (-21802096399/1073741824)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-54598549065/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((191571383060975/18014398509481984), (-825134345708499/9007199254740992)), (505653/4503599627370496), by norm_num⟩
  | 1 => ⟨((-9289919551/274877906944), (80026897215/274877906944)), (25/68719476736), by norm_num⟩
  | 2 => ⟨((7380966103/137438953472), (-31791223403/68719476736)), (81/137438953472), by norm_num⟩
  | 3 => ⟨((-7819035865/137438953472), (67356146205/137438953472)), (87/137438953472), by norm_num⟩
  | 4 => ⟨((1553082305/34359738368), (-53515364611/137438953472)), (35/68719476736), by norm_num⟩
  | 5 => ⟨((-7897246669/274877906944), (34014941897/137438953472)), (91/274877906944), by norm_num⟩
  | 6 => ⟨((4182979171/274877906944), (-1126055379/8589934592)), (49/274877906944), by norm_num⟩
  | 7 => ⟨((-1899104711/274877906944), (32719219295/549755813888)), (91/1099511627776), by norm_num⟩
  | 8 => ⟨((6035457001/2199023255552), (-51991720103/2199023255552)), (73/2199023255552), by norm_num⟩
  | 9 => ⟨((-8524892107/8796093022208), (36718330049/4398046511104)), (105/8796093022208), by norm_num⟩
  | 10 => ⟨((5418513203/17592186044416), (-93354263565/35184372088832)), (17/4398046511104), by norm_num⟩
  | 11 => ⟨((-97842765/1099511627776), (107885409055/140737488355328)), (159/140737488355328), by norm_num⟩
  | 12 => ⟨((13267181827/562949953421312), (-28572136457/140737488355328)), (171/562949953421312), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790435469823053/5070602400912917605986812821504), (-1895597766123/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((889145144271671/316912650057057350374175801344), (-2242197671869/633825300114114700748351602688)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236150445474779/4951760157141521099596496896), (-2521947821795/39614081257132168796771975168)), (813/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888944996054209/2475880078570760549798248448), (-334864739649/309485009821345068724781056)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221326405963773/19342813113834066795298816), (-669546271353/38685626227668133590597632)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1549010203021615/9671406556917033397649408), (-2510020132669/9671406556917033397649408)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314578341620033/151115727451828646838272), (-2195489511139/604462909807314587353088)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887019659305393/75557863725914323419136), (-445776512941/9444732965739290427392)), (1153/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162120020992839/590295810358705651712), (-668345903513/1180591620717411303424)), (865/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620651603367897/590295810358705651712), (-3673830955113/590295810358705651712)), (1189/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911239494110301/36893488147419103232), (-4589183371319/73786976294838206464)), (1487/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821536808987827/9223372036854775808), (-5158564639039/9223372036854775808)), (837/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592785310056845/1152921504606846976), (-2576618032965/576460752303423488)), (1675/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193530277139115/144115188075855872), (-4503093430667/144115188075855872)), (1467/144115188075855872), by norm_num⟩
  | 4 => ⟨((372515417548875/9007199254740992), (-6742680170427/36028797018963968)), (1101/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487288023094321/9007199254740992), (-8407456838781/9007199254740992)), (2757/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224008830709007/4503599627370496), (-8376189834607/2251799813685248)), (5525/4503599627370496), by norm_num⟩
  | 1 => ⟨((2210195177903841/2251799813685248), (-24972744905103/2251799813685248)), (8319/2251799813685248), by norm_num⟩
  | 0 => ⟨((1084459043626271/1125899906842624), (-12331311532827/562949953421312)), (16763/2251799813685248), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1084459043626271/1125899906842624), (-12331311532827/562949953421312)), (63945778853606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((261000814811025/281474976710656), (-95019475392257/2251799813685248)), (33027/2251799813685248), by norm_num⟩
  | 2 => ⟨((966058904105037/1125899906842624), (-176215738891693/2251799813685248)), (32019/1125899906842624), by norm_num⟩
  | 3 => ⟨((822015175521019/1125899906842624), (-151198861075635/1125899906842624)), (119917/2251799813685248), by norm_num⟩
  | 4 => ⟨((1159690749112987/2251799813685248), (-441558819111045/2251799813685248)), (207311/2251799813685248), by norm_num⟩
  | 5 => ⟨((255330965891143/1125899906842624), (-909622026967465/4503599627370496)), (294837/2251799813685248), by norm_num⟩
  | 6 => ⟨((191571383060975/18014398509481984), (-825134345708499/9007199254740992)), (505653/4503599627370496), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5118613975/2147483648), (-21802096399/1073741824)), (1/2147483648), by norm_num⟩, -3, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55299865591/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5184362399/2147483648), (-11041071797/536870912)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-55299865591/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-58301882451737/4503599627370496), (-797145325150275/9007199254740992)), (2117639/18014398509481984), by norm_num⟩
  | 1 => ⟨((11454255369/274877906944), (19576353577/68719476736)), (53/137438953472), by norm_num⟩
  | 2 => ⟨((-9217456425/137438953472), (-15753462817/34359738368)), (87/137438953472), by norm_num⟩
  | 3 => ⟨((4944974609/68719476736), (4225703385/8589934592)), (95/137438953472), by norm_num⟩
  | 4 => ⟨((-1989657403/34359738368), (-108816115753/274877906944)), (155/274877906944), by norm_num⟩
  | 5 => ⟨((10247136183/274877906944), (70053112871/274877906944)), (101/274877906944), by norm_num⟩
  | 6 => ⟨((-5497376489/274877906944), (-75164090493/549755813888)), (55/274877906944), by norm_num⟩
  | 7 => ⟨((10111641303/1099511627776), (34563410541/549755813888)), (103/1099511627776), by norm_num⟩
  | 8 => ⟨((-8137029435/2199023255552), (-13906915827/549755813888)), (21/549755813888), by norm_num⟩
  | 9 => ⟨((1455115963/1099511627776), (79581573607/8796093022208)), (61/4398046511104), by norm_num⟩
  | 10 => ⟨((-7494140153/17592186044416), (-25616320339/8796093022208)), (159/35184372088832), by norm_num⟩
  | 11 => ⟨((8771893297/70368744177664), (59967821281/70368744177664)), (47/35184372088832), by norm_num⟩
  | 12 => ⟨((-1176484803/35184372088832), (-4021436879/17592186044416)), (51/140737488355328), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580831058242031/10141204801825835211973625643008), (-1117668739467/5070602400912917605986812821504)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((444560516018811/158456325028528675187087900672), (-2643923304421/633825300114114700748351602688)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889149264216957/39614081257132168796771975168), (-2973785965893/39614081257132168796771975168)), (813/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944443619687835/1237940039285380274899124224), (-3158869143173/2475880078570760549798248448)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885276709909923/77371252455336267181195264), (-3157993688395/154742504910672534362390528)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774477956888149/4835703278458516698824704), (-1479844599177/4835703278458516698824704)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629132893932427/302231454903657293676544), (-1294399242965/302231454903657293676544)), (355/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886942202598975/75557863725914323419136), (-525631911689/9444732965739290427392)), (1153/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296901951792223/4722366482869645213696), (-1576133844179/2361183241434822606848)), (433/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405142838891395/147573952589676412928), (-2165946603669/295147905179352825856)), (595/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822378378078471/73786976294838206464), (-2705578227069/36893488147419103232)), (93/4611686018427387904), by norm_num⟩
  | 7 => ⟨((455355802590143/2305843009213693952), (-6082453325369/9223372036854775808)), (1675/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398167799345755/288230376151711744), (-6076086675493/1152921504606846976)), (1677/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193429851929037/144115188075855872), (-663677607281/18014398509481984)), (1469/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489909883336267/36028797018963968), (-7949840052109/36028797018963968)), (2205/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487096288114233/9007199254740992), (-2478083126093/2251799813685248)), (2761/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223619394106703/4503599627370496), (-4937482629633/1125899906842624)), (173/140737488355328), by norm_num⟩
  | 1 => ⟨((276199529677923/281474976710656), (-29438647272063/2251799813685248)), (8341/2251799813685248), by norm_num⟩
  | 0 => ⟨((1083830923130743/1125899906842624), (-29067909611057/1125899906842624)), (8415/1125899906842624), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1083830923130743/1125899906842624), (-29067909611057/1125899906842624)), (32100681785201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((521291688289197/562949953421312), (-111927176175303/2251799813685248)), (4159/281474976710656), by norm_num⟩
  | 2 => ⟨((1925301116624853/2251799813685248), (-25911142846387/281474976710656)), (2029/70368744177664), by norm_num⟩
  | 3 => ⟨((1627060975269381/2251799813685248), (-44308336781973/281474976710656)), (61491/1125899906842624), by norm_num⟩
  | 4 => ⟨((139981403130425/281474976710656), (-512247067213715/2251799813685248)), (216443/2251799813685248), by norm_num⟩
  | 5 => ⟨((220194908609395/1125899906842624), (-1018990235735671/4503599627370496)), (313755/2251799813685248), by norm_num⟩
  | 6 => ⟨((-58301882451737/4503599627370496), (-797145325150275/9007199254740992)), (2117639/18014398509481984), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5184362399/2147483648), (-11041071797/536870912)), (1/2147483648), by norm_num⟩, -3, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6996709039/2147483648), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5247531779/2147483648), (-89404822689/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-603250690670879/18014398509481984), (-1443574999364785/18014398509481984)), (540903/4503599627370496), by norm_num⟩
  | 1 => ⟨((29990371503/274877906944), (71766764951/274877906944)), (55/137438953472), by norm_num⟩
  | 2 => ⟨((-1526742587/8589934592), (-14613940527/34359738368)), (91/137438953472), by norm_num⟩
  | 3 => ⟨((26529465265/137438953472), (63484838717/137438953472)), (25/34359738368), by norm_num⟩
  | 4 => ⟨((-10804444867/68719476736), (-25854966655/68719476736)), (83/137438953472), by norm_num⟩
  | 5 => ⟨((28161539533/274877906944), (67390381879/274877906944)), (55/137438953472), by norm_num⟩
  | 6 => ⟨((-30584338153/549755813888), (-73188123299/549755813888)), (61/274877906944), by norm_num⟩
  | 7 => ⟨((28470493215/1099511627776), (68129706041/1099511627776)), (29/274877906944), by norm_num⟩
  | 8 => ⟨((-23189903845/2199023255552), (-55493289847/2199023255552)), (3/68719476736), by norm_num⟩
  | 9 => ⟨((33579975749/8796093022208), (40178332341/4398046511104)), (141/8796093022208), by norm_num⟩
  | 10 => ⟨((-21881360547/17592186044416), (-52361954201/17592186044416)), (47/8796093022208), by norm_num⟩
  | 11 => ⟨((3240526593/8796093022208), (15509118337/17592186044416)), (113/70368744177664), by norm_num⟩
  | 12 => ⟨((-1759658079/17592186044416), (-67373606349/281474976710656)), (31/70368744177664), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((6174971645405/39614081257132168796771975168), (-2561750579387/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((889097785244581/316912650057057350374175801344), (-1514926298093/316912650057057350374175801344)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889096905004607/39614081257132168796771975168), (-3407854346423/39614081257132168796771975168)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888831535054629/2475880078570760549798248448), (-3619942068775/2475880078570760549798248448)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770497633853253/154742504910672534362390528), (-3618926311667/154742504910672534362390528)), (865/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774451763879165/4835703278458516698824704), (-211979030783/604462909807314587353088)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629109931754123/302231454903657293676544), (-2966627863071/604462909807314587353088)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886867413338691/75557863725914323419136), (-301171795041/4722366482869645213696)), (577/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648422859057897/2361183241434822606848), (-3612293436033/4722366482869645213696)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101280862767427/36893488147419103232), (-4964031725205/590295810358705651712)), (1191/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822281094577237/73786976294838206464), (-1550183629347/18446744073709551616)), (745/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910656646911273/4611686018427387904), (-6969910802181/9223372036854775808)), (1677/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199070086438213/144115188075855872), (-6962522441741/1152921504606846976)), (839/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193332498214991/144115188075855872), (-1520975887005/36028797018963968)), (735/72057594037927936), by norm_num⟩
  | 4 => ⟨((186220316931485/4503599627370496), (-1138658615541/4503599627370496)), (69/1125899906842624), by norm_num⟩
  | 3 => ⟨((185863726100321/1125899906842624), (-5678803338307/4503599627370496)), (2765/9007199254740992), by norm_num⟩
  | 2 => ⟨((555809898840659/1125899906842624), (-707139425129/140737488355328)), (5547/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209009589830501/2251799813685248), (-33726465621511/2251799813685248)), (8363/2251799813685248), by norm_num⟩
  | 0 => ⟨((1083210826895079/1125899906842624), (-4161995817733/140737488355328)), (16895/2251799813685248), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1083210826895079/1125899906842624), (-4161995817733/140737488355328)), (64449318892668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2082311344002299/2251799813685248), (-128134130683873/2251799813685248)), (33509/2251799813685248), by norm_num⟩
  | 2 => ⟨((959144359028341/1125899906842624), (-3702804089413/35184372088832)), (16447/562949953421312), by norm_num⟩
  | 3 => ⟨((1609233786468287/2251799813685248), (-403761493424503/2251799813685248)), (7871/140737488355328), by norm_num⟩
  | 4 => ⟨((538815666737119/1125899906842624), (-18034091911301/70368744177664)), (112581/1125899906842624), by norm_num⟩
  | 5 => ⟨((367819257946887/2251799813685248), (-1104700829408345/4503599627370496)), (661837/4503599627370496), by norm_num⟩
  | 6 => ⟨((-603250690670879/18014398509481984), (-1443574999364785/18014398509481984)), (540903/4503599627370496), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5247531779/2147483648), (-89404822689/4294967296)), (1/2147483648), by norm_num⟩, -3, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-28311023105/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-165884901/67108864), (-22610112007/1073741824)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-452274283208285/9007199254740992), (-152832072114391/2251799813685248)), (2162339/18014398509481984), by norm_num⟩
  | 1 => ⟨((45490181157/274877906944), (61487985545/274877906944)), (55/137438953472), by norm_num⟩
  | 2 => ⟨((-37482054025/137438953472), (-25331796197/68719476736)), (23/34359738368), by norm_num⟩
  | 3 => ⟨((41178245157/137438953472), (6957455649/17179869184)), (103/137438953472), by norm_num⟩
  | 4 => ⟨((-33929194617/137438953472), (-45861277643/137438953472)), (87/137438953472), by norm_num⟩
  | 5 => ⟨((44730036181/274877906944), (60460515831/274877906944)), (117/274877906944), by norm_num⟩
  | 6 => ⟨((-49140967421/549755813888), (-66422665671/549755813888)), (131/549755813888), by norm_num⟩
  | 7 => ⟨((11568615147/274877906944), (1954627413/34359738368)), (125/1099511627776), by norm_num⟩
  | 8 => ⟨((-19064134145/1099511627776), (-51537064697/2199023255552)), (105/2199023255552), by norm_num⟩
  | 9 => ⟨((55850912119/8796093022208), (37746168399/4398046511104)), (39/2199023255552), by norm_num⟩
  | 10 => ⟨((-36815099033/17592186044416), (-1555065167/549755813888)), (105/17592186044416), by norm_num⟩
  | 11 => ⟨((2757649105/4398046511104), (59639169239/70368744177664)), (1/549755813888), by norm_num⟩
  | 12 => ⟨((-24236697557/140737488355328), (-16380081053/70368744177664)), (143/281474976710656), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790377935240215/5070602400912917605986812821504), (-2875843222997/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778150683058489/633825300114114700748351602688), (-425147447997/79228162514264337593543950336)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889046346724469/39614081257132168796771975168), (-3825496172443/39614081257132168796771975168)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944388868040873/1237940039285380274899124224), (-2031781896257/1237940039285380274899124224)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((27663183501321/2417851639229258349412352), (-1015602496063/38685626227668133590597632)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193606613714075/1208925819614629174706176), (-951820945191/2417851639229258349412352)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629087738212027/302231454903657293676544), (-3330148112959/604462909807314587353088)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886795103973617/75557863725914323419136), (-676149282373/9444732965739290427392)), (1155/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648395664240535/2361183241434822606848), (-4054887139047/4722366482869645213696)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810209381392319/295147905179352825856), (-5572207444309/590295810358705651712)), (149/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1822186909738999/73786976294838206464), (-6960368425041/73786976294838206464)), (1491/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910603405174447/4611686018427387904), (-977961733443/1152921504606846976)), (839/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796226776348755/576460752303423488), (-3907649813593/576460752303423488)), (105/72057594037927936), by norm_num⟩
  | 5 => ⟨((37288688021065/4503599627370496), (-426809538713/9007199254740992)), (23/2251799813685248), by norm_num⟩
  | 4 => ⟨((1489619348382605/36028797018963968), (-10224582226385/36028797018963968)), (2211/36028797018963968), by norm_num⟩
  | 3 => ⟨((92920517111571/562949953421312), (-12747796441875/9007199254740992)), (2769/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111434460118615/2251799813685248), (-12698500145057/2251799813685248)), (5557/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208434733413565/2251799813685248), (-4731215423749/281474976710656)), (8383/2251799813685248), by norm_num⟩
  | 0 => ⟨((2165197575358977/2251799813685248), (-37360280343733/1125899906842624)), (8479/1125899906842624), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2165197575358977/2251799813685248), (-37360280343733/1125899906842624)), (32344822410201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1039723280394021/1125899906842624), (-143693747416375/2251799813685248)), (16869/1125899906842624), by norm_num⟩
  | 2 => ⟨((955557878629477/1125899906842624), (-132695396391703/1125899906842624)), (33309/1125899906842624), by norm_num⟩
  | 3 => ⟨((795348490345407/1125899906842624), (-225238728077587/1125899906842624)), (64391/1125899906842624), by norm_num⟩
  | 4 => ⟨((516783714904453/1125899906842624), (-159111197412035/562949953421312)), (233473/2251799813685248), by norm_num⟩
  | 5 => ⟨((294519813733417/2251799813685248), (-292125703827705/1125899906842624)), (5411/35184372088832), by norm_num⟩
  | 6 => ⟨((-452274283208285/9007199254740992), (-152832072114391/2251799813685248)), (2162339/18014398509481984), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-165884901/67108864), (-22610112007/1073741824)), (1/2147483648), by norm_num⟩, -3, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 12 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile014Terms3

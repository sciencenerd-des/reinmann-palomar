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
namespace Reinmann.XiRectangle.Tile016Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨16,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (4653/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (4653/640))
  have he : value ((3/4), (4653/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2489236171/1073741824), (-24130033137/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-785795674309023/9007199254740992), (410789180796767/9007199254740992)), (4987111/9007199254740992), by norm_num⟩
  | 1 => ⟨((9265624195/34359738368), (-9687551859/68719476736)), (15/8589934592), by norm_num⟩
  | 2 => ⟨((-1790027359/4294967296), (1871539629/8589934592)), (95/34359738368), by norm_num⟩
  | 3 => ⟨((14754801491/34359738368), (-7713344595/34359738368)), (25/8589934592), by norm_num⟩
  | 4 => ⟨((-5700964725/17179869184), (1490142225/8589934592)), (79/34359738368), by norm_num⟩
  | 5 => ⟨((1762192399/8589934592), (-3684874303/34359738368)), (99/68719476736), by norm_num⟩
  | 6 => ⟨((-14525364043/137438953472), (7593401937/137438953472)), (13/17179869184), by norm_num⟩
  | 7 => ⟨((1603518461/34359738368), (-3353075393/137438953472)), (47/137438953472), by norm_num⟩
  | 8 => ⟨((-9913087275/549755813888), (10364498389/1099511627776)), (147/1099511627776), by norm_num⟩
  | 9 => ⟨((13618566049/2199023255552), (-3559678281/1099511627776)), (103/2199023255552), by norm_num⟩
  | 10 => ⟨((-4209556581/2199023255552), (8802493349/8796093022208)), (129/8796093022208), by norm_num⟩
  | 11 => ⟨((18926426329/35184372088832), (-9894138413/35184372088832)), (147/35184372088832), by norm_num⟩
  | 12 => ⟨((-19500795757/140737488355328), (637150039/8796093022208)), (77/70368744177664), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395238986542947/2535301200456458802993406410752), (1732406177611/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889192268654019/316912650057057350374175801344), (4098776367997/633825300114114700748351602688)), (2895/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944654609393955/19807040628566084398385987584), (288135799571/2475880078570760549798248448)), (1629/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889056762795457/2475880078570760549798248448), (4897148014561/2475880078570760549798248448)), (1731/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770722461776075/154742504910672534362390528), (4895842549433/154742504910672534362390528)), (3463/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549113879392559/9671406556917033397649408), (4588465612441/9671406556917033397649408)), (203/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((314600874235179/151115727451828646838272), (4013520946667/604462909807314587353088)), (2843/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943582511415519/37778931862957161709568), (1629843146037/18889465931478580854784)), (4621/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648534115191191/2361183241434822606848), (2443628009805/2361183241434822606848)), (867/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620798630687271/590295810358705651712), (3358141985915/295147905179352825856)), (4771/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455665109427487/18446744073709551616), (262181799071/2305843009213693952)), (373/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1821737734608915/9223372036854775808), (4715467203203/4611686018427387904)), (105/144115188075855872), by norm_num⟩
  | 6 => ⟨((1592982237006737/1152921504606846976), (147209793669/18014398509481984)), (841/144115188075855872), by norm_num⟩
  | 5 => ⟨((37303065631793/4503599627370496), (8233059727257/144115188075855872)), (737/18014398509481984), by norm_num⟩
  | 4 => ⟨((1490304455026013/36028797018963968), (3082057632317/9007199254740992)), (8861/36028797018963968), by norm_num⟩
  | 3 => ⟨((371893975224347/2251799813685248), (30025295277/17592186044416)), (5553/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112269005837523/2251799813685248), (15317028554637/2251799813685248)), (697/140737488355328), by norm_num⟩
  | 1 => ⟨((276359166652447/281474976710656), (22836026597695/1125899906842624)), (16843/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084908419038009/1125899906842624), (45115733308137/1125899906842624)), (8537/281474976710656), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1084908419038009/1125899906842624), (45115733308137/1125899906842624)), (32566071630382449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1043601514811973/1125899906842624), (86946341499099/1125899906842624)), (68547/1125899906842624), by norm_num⟩
  | 2 => ⟨((1921208890496769/2251799813685248), (322363766599021/2251799813685248)), (275321/2251799813685248), by norm_num⟩
  | 3 => ⟨((1593003596992623/2251799813685248), (275036941827651/1125899906842624)), (548631/2251799813685248), by norm_num⟩
  | 4 => ⟨((992574548131757/2251799813685248), (389141907708267/1125899906842624)), (1044285/2251799813685248), by norm_num⟩
  | 5 => ⟨((337044646645207/4503599627370496), (1372244018691983/4503599627370496)), (410623/562949953421312), by norm_num⟩
  | 6 => ⟨((-785795674309023/9007199254740992), (410789180796767/9007199254740992)), (4987111/9007199254740992), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2489236171/1073741824), (-24130033137/1073741824)), (1/536870912), by norm_num⟩, -4, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2525033459/1073741824), (-6119260773/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-594502433232179/9007199254740992), (618122568479533/9007199254740992)), (1223899/2251799813685248), by norm_num⟩
  | 1 => ⟨((111106571/536870912), (-14786680131/68719476736)), (119/68719476736), by norm_num⟩
  | 2 => ⟨((-11147968343/34359738368), (5795443753/17179869184)), (95/34359738368), by norm_num⟩
  | 3 => ⟨((11651463419/34359738368), (-12114386911/34359738368)), (101/34359738368), by norm_num⟩
  | 4 => ⟨((-9133274039/34359738368), (4748073761/17179869184)), (81/34359738368), by norm_num⟩
  | 5 => ⟨((11454931169/68719476736), (-11910046251/68719476736)), (13/8589934592), by norm_num⟩
  | 6 => ⟨((-11972290141/137438953472), (12447960377/137438953472)), (55/68719476736), by norm_num⟩
  | 7 => ⟨((5362720927/137438953472), (-5575786823/137438953472)), (25/68719476736), by norm_num⟩
  | 8 => ⟨((-525461889/34359738368), (4370711833/274877906944)), (159/1099511627776), by norm_num⟩
  | 9 => ⟨((11716143741/2199023255552), (-12181637041/2199023255552)), (113/2199023255552), by norm_num⟩
  | 10 => ⟨((-14694360373/8796093022208), (15278180993/8796093022208)), (9/549755813888), by norm_num⟩
  | 11 => ⟨((4188552905/8796093022208), (-1088742003/2199023255552)), (83/17592186044416), by norm_num⟩
  | 12 => ⟨((-2188863901/17592186044416), (1137914751/8796093022208)), (11/8796093022208), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790456259316641/5070602400912917605986812821504), (760959165139/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222291902413633/79228162514264337593543950336), (3600575664913/633825300114114700748351602688)), (2893/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118078366428205/2475880078570760549798248448), (2024903079363/19807040628566084398385987584)), (407/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1888998112559155/2475880078570760549798248448), (2150942737417/1237940039285380274899124224)), (865/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770663997525683/154742504910672534362390528), (4300722963749/154742504910672534362390528)), (3461/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549059266639177/9671406556917033397649408), (4030692910453/9671406556917033397649408)), (3245/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629177954059115/302231454903657293676544), (3525621765723/604462909807314587353088)), (2841/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943544030346809/37778931862957161709568), (5726821340231/75557863725914323419136)), (2309/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297010831958947/4722366482869645213696), (2146545973069/2361183241434822606848)), (3465/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810360116223211/295147905179352825856), (5899713673233/590295810358705651712)), (4767/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455640806447339/18446744073709551616), (7369712813073/73786976294838206464)), (2981/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227703681268659/1152921504606846976), (8284152976421/9223372036854775808)), (6713/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592875298785831/1152921504606846976), (8275691282795/1152921504606846976)), (105/18014398509481984), by norm_num⟩
  | 5 => ⟨((1193606040426941/144115188075855872), (1807929586125/36028797018963968)), (5887/144115188075855872), by norm_num⟩
  | 4 => ⟨((93135586202565/2251799813685248), (10828574153363/36028797018963968)), (4423/18014398509481984), by norm_num⟩
  | 3 => ⟨((743706155803255/4503599627370496), (6751253055581/4503599627370496)), (2771/2251799813685248), by norm_num⟩
  | 2 => ⟨((2224226523998485/4503599627370496), (26905554687829/4503599627370496)), (2781/562949953421312), by norm_num⟩
  | 1 => ⟨((1105222532793537/1125899906842624), (40110308351861/2251799813685248)), (16787/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084557291330437/1125899906842624), (39616121168141/1125899906842624)), (8495/281474976710656), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1084557291330437/1125899906842624), (39616121168141/1125899906842624)), (32405854345226199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((521669410390049/562949953421312), (152645729184319/2251799813685248)), (135713/2251799813685248), by norm_num⟩
  | 2 => ⟨((480829027832309/562949953421312), (282904748666165/2251799813685248)), (269923/2251799813685248), by norm_num⟩
  | 3 => ⟨((1607207596912351/2251799813685248), (241635716360903/1125899906842624)), (66115/281474976710656), by norm_num⟩
  | 4 => ⟨((260854114074481/562949953421312), (689863737727239/2251799813685248)), (122757/281474976710656), by norm_num⟩
  | 5 => ⟨((272140498865845/2251799813685248), (1278648611964777/4503599627370496)), (3023677/4503599627370496), by norm_num⟩
  | 6 => ⟨((-594502433232179/9007199254740992), (618122568479533/9007199254740992)), (1223899/2251799813685248), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2525033459/1073741824), (-6119260773/268435456)), (1/536870912), by norm_num⟩, -4, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2559306987/1073741824), (-12404641055/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-183084833237549/4503599627370496), (1491229510391927/18014398509481984)), (4631045/9007199254740992), by norm_num⟩
  | 1 => ⟨((1109797393/8589934592), (-4519660623/17179869184)), (57/34359738368), by norm_num⟩
  | 2 => ⟨((-220437241/1073741824), (14363724755/34359738368)), (23/8589934592), by norm_num⟩
  | 3 => ⟨((7472655127/34359738368), (-15216230159/34359738368)), (99/34359738368), by norm_num⟩
  | 4 => ⟨((-2968562531/17179869184), (12089499635/34359738368)), (5/2147483648), by norm_num⟩
  | 5 => ⟨((3773700609/34359738368), (-15368432249/68719476736)), (103/68719476736), by norm_num⟩
  | 6 => ⟨((-7995349117/137438953472), (16280568325/137438953472)), (111/137438953472), by norm_num⟩
  | 7 => ⟨((113435937/4294967296), (-3695751609/68719476736)), (103/274877906944), by norm_num⟩
  | 8 => ⟨((-5768088225/549755813888), (11745297557/549755813888)), (21/137438953472), by norm_num⟩
  | 9 => ⟨((1018405271/274877906944), (-16589861285/2199023255552)), (121/2199023255552), by norm_num⟩
  | 10 => ⟨((-1294618709/1099511627776), (21089388881/8796093022208)), (39/2199023255552), by norm_num⟩
  | 11 => ⟨((1496133799/4398046511104), (-3046509687/4398046511104)), (23/4398046511104), by norm_num⟩
  | 12 => ⟨((-6339725001/70368744177664), (12909295707/70368744177664)), (99/70368744177664), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197608867455839/1267650600228229401496703205376), (2640780352279/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444571938562465/158456325028528675187087900672), (12201691037/2475880078570760549798248448)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889200572021725/39614081257132168796771975168), (3513351231689/39614081257132168796771975168)), (1627/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888941631344319/2475880078570760549798248448), (933006822691/618970019642690137449562112)), (1729/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770607674011053/154742504910672534362390528), (3643560193/151115727451828646838272)), (3459/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549006630790097/9671406556917033397649408), (3496732580267/9671406556917033397649408)), (3243/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((19661094047997/9444732965739290427392), (1529278070827/302231454903657293676544)), (2839/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235876725557111/9444732965739290427392), (4968120326397/75557863725914323419136)), (2307/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648477706899069/2361183241434822606848), (3724311736443/4722366482869645213696)), (1731/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620644477257799/590295810358705651712), (5118039911151/590295810358705651712)), (4763/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822469198112171/73786976294838206464), (1598304790115/18446744073709551616)), (5957/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821524583782031/9223372036854775808), (1796605159915/2305843009213693952)), (3353/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592771573775465/1152921504606846976), (7178987746495/1152921504606846976)), (839/144115188075855872), by norm_num⟩
  | 5 => ⟨((596758281089015/72057594037927936), (3136630089287/72057594037927936)), (5879/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490037716919291/36028797018963968), (4696600910831/18014398509481984)), (69/281474976710656), by norm_num⟩
  | 3 => ⟨((743626094414515/4503599627370496), (11712341913009/9007199254740992)), (11063/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223919579087317/4503599627370496), (23337380263107/4503599627370496)), (22195/4503599627370496), by norm_num⟩
  | 1 => ⟨((276252209233541/281474976710656), (34788432218225/2251799813685248)), (33467/2251799813685248), by norm_num⟩
  | 0 => ⟨((542097637700539/562949953421312), (68710031127595/2251799813685248)), (8455/281474976710656), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((542097637700539/562949953421312), (68710031127595/2251799813685248)), (32253266454601199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2085974287715741/2251799813685248), (16541233076861/281474976710656)), (67199/1125899906842624), by norm_num⟩
  | 2 => ⟨((962291920801261/1125899906842624), (245169835618563/2251799813685248)), (132399/1125899906842624), by norm_num⟩
  | 3 => ⟨((1618223206572139/2251799813685248), (209543451070641/1125899906842624)), (510301/2251799813685248), by norm_num⟩
  | 4 => ⟨((1084915497325695/2251799813685248), (75292677716493/281474976710656)), (230847/562949953421312), by norm_num⟩
  | 5 => ⟨((361589179932853/2251799813685248), (1160830619394521/4503599627370496)), (43243/70368744177664), by norm_num⟩
  | 6 => ⟨((-183084833237549/4503599627370496), (1491229510391927/18014398509481984)), (4631045/9007199254740992), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2559306987/1073741824), (-12404641055/536870912)), (1/536870912), by norm_num⟩, -4, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-162011325/67108864), (-25127956503/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-64061007217615/4503599627370496), (397687646341697/4503599627370496)), (1062497/2251799813685248), by norm_num⟩
  | 1 => ⟨((1573214931/34359738368), (-19532884989/68719476736)), (53/34359738368), by norm_num⟩
  | 2 => ⟨((-1265995877/17179869184), (3929620705/8589934592)), (87/34359738368), by norm_num⟩
  | 3 => ⟨((2716722349/34359738368), (-16865281451/34359738368)), (95/34359738368), by norm_num⟩
  | 4 => ⟨((-2186197973/34359738368), (27143623371/68719476736)), (155/68719476736), by norm_num⟩
  | 5 => ⟨((2814839921/68719476736), (-17474390613/68719476736)), (51/34359738368), by norm_num⟩
  | 6 => ⟨((-755051681/34359738368), (18749297833/137438953472)), (111/137438953472), by norm_num⟩
  | 7 => ⟨((2777620117/274877906944), (-17243331865/274877906944)), (13/34359738368), by norm_num⟩
  | 8 => ⟨((-4470407123/1099511627776), (3469009005/137438953472)), (85/549755813888), by norm_num⟩
  | 9 => ⟨((1598853935/1099511627776), (-19851216395/2199023255552)), (123/2199023255552), by norm_num⟩
  | 10 => ⟨((-4117209823/8796093022208), (25559440219/8796093022208)), (5/274877906944), by norm_num⟩
  | 11 => ⟨((1204798833/8796093022208), (-14958666221/17592186044416)), (95/17592186044416), by norm_num⟩
  | 12 => ⟨((-1292699279/35184372088832), (8025014845/35184372088832)), (103/70368744177664), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98801941140089/633825300114114700748351602688), (1127089995507/5070602400912917605986812821504)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778242000654919/633825300114114700748351602688), (2666209942241/633825300114114700748351602688)), (1445/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889149189353915/39614081257132168796771975168), (1499426517353/19807040628566084398385987584)), (813/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888887155181077/2475880078570760549798248448), (3185496329587/2475880078570760549798248448)), (27/19342813113834066795298816), by norm_num⟩
  | 14 => ⟨((442638332599055/38685626227668133590597632), (3184613479541/154742504910672534362390528)), (27/1208925819614629174706176), by norm_num⟩
  | 13 => ⟨((774477912194959/4835703278458516698824704), (186539837283/604462909807314587353088)), (3241/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258265704104673/604462909807314587353088), (2610620304929/604462909807314587353088)), (2837/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886942056097713/75557863725914323419136), (530062628229/9444732965739290427392)), (4611/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648450916417005/2361183241434822606848), (1589419553969/2361183241434822606848)), (865/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620571177257775/590295810358705651712), (1092101996573/147573952589676412928)), (4759/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227797266639441/9223372036854775808), (5456768554717/73786976294838206464)), (5951/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821422904472035/9223372036854775808), (6133723818935/9223372036854775808)), (6699/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592670853691279/1152921504606846976), (3063651648637/576460752303423488)), (419/72057594037927936), by norm_num⟩
  | 5 => ⟨((1193429508777705/144115188075855872), (5354174834675/144115188075855872)), (367/9007199254740992), by norm_num⟩
  | 4 => ⟨((1489909284035559/36028797018963968), (8016849976931/36028797018963968)), (4409/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487095391586997/9007199254740992), (1249485413229/1125899906842624)), (11043/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111808580626215/2251799813685248), (19916398169997/4503599627370496)), (173/35184372088832), by norm_num⟩
  | 1 => ⟨((1104795898514455/1125899906842624), (14843383448239/1125899906842624)), (16683/1125899906842624), by norm_num⟩
  | 0 => ⟨((2167648651111963/2251799813685248), (29312874639155/1125899906842624)), (67333/2251799813685248), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2167648651111963/2251799813685248), (29312874639155/1125899906842624)), (256855019576262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((130319746554893/140737488355328), (112869736973271/2251799813685248)), (133141/2251799813685248), by norm_num⟩
  | 2 => ⟨((120319557818695/140737488355328), (209029672022241/2251799813685248)), (16245/140737488355328), by norm_num⟩
  | 3 => ⟨((406604346925073/562949953421312), (357408079433737/2251799813685248)), (492679/2251799813685248), by norm_num⟩
  | 4 => ⟨((558995734982599/1125899906842624), (258146710628003/1125899906842624)), (868097/2251799813685248), by norm_num⟩
  | 5 => ⟨((873386723017255/4503599627370496), (128166730775839/562949953421312)), (1260075/2251799813685248), by norm_num⟩
  | 6 => ⟨((-64061007217615/4503599627370496), (397687646341697/4503599627370496)), (1062497/2251799813685248), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-162011325/67108864), (-25127956503/1073741824)), (1/536870912), by norm_num⟩, -4, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1311882945/536870912), (-25434130593/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((195735375542279/18014398509481984), (1552258945880989/18014398509481984)), (7600023/18014398509481984), by norm_num⟩
  | 1 => ⟨((-1216363429/34359738368), (-9646243091/34359738368)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((990757369/17179869184), (7857097805/17179869184)), (5/2147483648), by norm_num⟩
  | 3 => ⟨((-2151988769/34359738368), (-17066122105/34359738368)), (11/4294967296), by norm_num⟩
  | 4 => ⟨((3505693579/68719476736), (13900768337/34359738368)), (145/68719476736), by norm_num⟩
  | 5 => ⟨((-2284377623/68719476736), (-9058009039/34359738368)), (3/2147483648), by norm_num⟩
  | 6 => ⟨((310113451/17179869184), (9837289297/68719476736)), (53/68719476736), by norm_num⟩
  | 7 => ⟨((-2309438997/274877906944), (-18314764687/274877906944)), (25/68719476736), by norm_num⟩
  | 8 => ⟨((235136725/68719476736), (29835635711/1099511627776)), (165/1099511627776), by norm_num⟩
  | 9 => ⟨((-680976133/549755813888), (-21601640315/2199023255552)), (61/1099511627776), by norm_num⟩
  | 10 => ⟨((1774948785/4398046511104), (14076045905/4398046511104)), (161/8796093022208), by norm_num⟩
  | 11 => ⟨((-1051446271/8796093022208), (-4169192403/4398046511104)), (97/17592186044416), by norm_num⟩
  | 12 => ⟨((1141904485/35184372088832), (9055754223/35184372088832)), (107/70368744177664), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396370611537/5070602400912917605986812821504), (941372196393/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778197832950143/633825300114114700748351602688), (1113386688059/316912650057057350374175801344)), (2889/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944549787740161/19807040628566084398385987584), (2504586861249/39614081257132168796771975168)), (3251/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944417269196005/1237940039285380274899124224), (665115031457/618970019642690137449562112)), (1727/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770500823705075/154742504910672534362390528), (2659714069243/154742504910672534362390528)), (3455/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774453358133689/4835703278458516698824704), (2492689516747/9671406556917033397649408)), (3239/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258222851309369/604462909807314587353088), (272538899835/75557863725914323419136)), (2835/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943436319569881/37778931862957161709568), (1770760541481/37778931862957161709568)), (9/147573952589676412928), by norm_num⟩
  | 10 => ⟨((324212490351965/1180591620717411303424), (2654842399927/4722366482869645213696)), (3457/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620500164544967/590295810358705651712), (3648299552627/590295810358705651712)), (4755/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822289832356525/73786976294838206464), (4557213371011/73786976294838206464)), (2973/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821324204675951/9223372036854775808), (1280630475621/2305843009213693952)), (1673/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592572950596127/1152921504606846976), (5117097970549/1152921504606846976)), (837/144115188075855872), by norm_num⟩
  | 5 => ⟨((298336184450859/36028797018963968), (4471365660245/144115188075855872)), (733/18014398509481984), by norm_num⟩
  | 4 => ⟨((1489783910914327/36028797018963968), (1673718873359/9007199254740992)), (8805/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486941784516783/9007199254740992), (8347330118747/9007199254740992)), (11023/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111659614583945/2251799813685248), (16631021238587/4503599627370496)), (1381/281474976710656), by norm_num⟩
  | 1 => ⟨((276145992973467/281474976710656), (24787971385205/2251799813685248)), (8317/562949953421312), by norm_num⟩
  | 0 => ⟨((2166892166872121/2251799813685248), (48944914369047/2251799813685248)), (67039/2251799813685248), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2166892166872121/2251799813685248), (48944914369047/2251799813685248)), (255733498580168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2084122233995861/2251799813685248), (94198739079689/2251799813685248)), (131937/2251799813685248), by norm_num⟩
  | 2 => ⟨((1924989982434375/2251799813685248), (87184342647697/1125899906842624)), (255265/2251799813685248), by norm_num⟩
  | 3 => ⟨((816054333898875/1125899906842624), (149062083762479/1125899906842624)), (237985/1125899906842624), by norm_num⟩
  | 4 => ⟨((571742805152841/1125899906842624), (432161895511627/2251799813685248)), (6375/17592186044416), by norm_num⟩
  | 5 => ⟨((248866580020203/1125899906842624), (219455968437631/1125899906842624)), (2283913/4503599627370496), by norm_num⟩
  | 6 => ⟨((195735375542279/18014398509481984), (1552258945880989/18014398509481984)), (7600023/18014398509481984), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1311882945/536870912), (-25434130593/1073741824)), (1/536870912), by norm_num⟩, -4, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-165884901/67108864), (-12864374073/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((592007816080443/18014398509481984), (1400936815056225/18014398509481984)), (3319325/9007199254740992), by norm_num⟩
  | 1 => ⟨((-3721544619/34359738368), (-17613446053/68719476736)), (85/68719476736), by norm_num⟩
  | 2 => ⟨((6132801977/34359738368), (7256380605/17179869184)), (9/4294967296), by norm_num⟩
  | 3 => ⟨((-210549113/1073741824), (-996493613/2147483648)), (81/34359738368), by norm_num⟩
  | 4 => ⟨((2775742115/17179869184), (6568560773/17179869184)), (17/8589934592), by norm_num⟩
  | 5 => ⟨((-7318714555/68719476736), (-8659561901/34359738368)), (23/17179869184), by norm_num⟩
  | 6 => ⟨((8040429747/137438953472), (9513501119/68719476736)), (103/137438953472), by norm_num⟩
  | 7 => ⟨((-3785706397/137438953472), (-17917112979/274877906944)), (99/274877906944), by norm_num⟩
  | 8 => ⟨((3119267677/274877906944), (3690742593/137438953472)), (83/549755813888), by norm_num⟩
  | 9 => ⟨((-2284577201/549755813888), (-21625040891/2199023255552)), (31/549755813888), by norm_num⟩
  | 10 => ⟨((3011837505/2199023255552), (1781815175/549755813888)), (21/1099511627776), by norm_num⟩
  | 11 => ⟨((-3609645485/8796093022208), (-2135480779/2199023255552)), (51/8796093022208), by norm_num⟩
  | 12 => ⟨((7931201775/70368744177664), (1173032713/4398046511104)), (57/35184372088832), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790377935240215/5070602400912917605986812821504), (190666078291/1267650600228229401496703205376)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778155139135565/633825300114114700748351602688), (112747726937/39614081257132168796771975168)), (361/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889051606045849/39614081257132168796771975168), (507255874505/9903520314283042199192993792)), (3249/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944391825465335/1237940039285380274899124224), (2155293928613/2475880078570760549798248448)), (863/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770450026232325/154742504910672534362390528), (1077341351805/77371252455336267181195264)), (3453/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548859189185079/9671406556917033397649408), (2019365835265/9671406556917033397649408)), (3237/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629090680294093/302231454903657293676544), (1766296162125/604462909807314587353088)), (1417/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886805395580897/75557863725914323419136), (1434507518477/37778931862957161709568)), (4605/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324199921272469/1180591620717411303424), (1075348811135/2361183241434822606848)), (3455/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405107822097463/147573952589676412928), (1477740903807/295147905179352825856)), (4751/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113887757333209/4611686018427387904), (461470362977/9223372036854775808)), (5941/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821228297185747/9223372036854775808), (4149675791215/9223372036854775808)), (6685/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398119423567651/288230376151711744), (4145233275911/1152921504606846976)), (6689/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193262119394639/144115188075855872), (3622087233471/144115188075855872)), (5857/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489661440850179/36028797018963968), (5423161933717/36028797018963968)), (8793/36028797018963968), by norm_num⟩
  | 3 => ⟨((185848904776421/1125899906842624), (6761540176371/9007199254740992)), (2751/2251799813685248), by norm_num⟩
  | 2 => ⟨((2223025722740621/4503599627370496), (6735488421305/2251799813685248)), (689/140737488355328), by norm_num⟩
  | 1 => ⟨((1104373259163929/1125899906842624), (313697994567/35184372088832)), (16587/1125899906842624), by norm_num⟩
  | 0 => ⟨((2166123868717439/2251799813685248), (38707960181/2199023255552)), (66757/2251799813685248), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2166123868717439/2251799813685248), (38707960181/2199023255552)), (254657753951262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2083009998587999/2251799813685248), (76257707821631/2251799813685248)), (130785/2251799813685248), by norm_num⟩
  | 2 => ⟨((1924289801376207/2251799813685248), (141083205439915/2251799813685248)), (250823/2251799813685248), by norm_num⟩
  | 3 => ⟨((817787342027483/1125899906842624), (241127094623199/2251799813685248)), (460115/2251799813685248), by norm_num⟩
  | 4 => ⟨((581082353647861/1125899906842624), (350281023391679/2251799813685248)), (383471/1125899906842624), by norm_num⟩
  | 5 => ⟨((545310468573947/2251799813685248), (723126879302847/4503599627370496)), (515125/1125899906842624), by norm_num⟩
  | 6 => ⟨((592007816080443/18014398509481984), (1400936815056225/18014398509481984)), (3319325/9007199254740992), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-165884901/67108864), (-12864374073/536870912)), (1/536870912), by norm_num⟩, -4, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile016Terms3

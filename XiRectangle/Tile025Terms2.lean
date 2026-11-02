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
namespace Reinmann.XiRectangle.Tile025Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨25,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (7191/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (7191/640))
  have he : value ((5/8), (7191/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2772588722239781/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log16 : Sound J_log16 F_log16 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log16_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/134217728), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog16 : Sound J_negLog16 F_negLog16 c := by
  apply sound_round (sound_scale (A_log16 hcre) S_log16)
  intro k
  fin_cases k <;> norm_num [J_negLog16, J_log16, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-232581599/134217728), (-4181235703/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg16 : Sound J_arg16 F_arg16 c := by
  apply sound_round (sound_mul (A_negLog16 hcre) (A_variable hcre) S_negLog16 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg16, J_negLog16, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((384347665181037/2251799813685248), (414404597475923/9007199254740992)), (15523959/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1016271593/2147483648), (-547873265/4294967296)), (21/2147483648), by norm_num⟩
  | 2 => ⟨((5635406315/8589934592), (379756809/2147483648)), (119/8589934592), by norm_num⟩
  | 3 => ⟨((-1302055333/2147483648), (-1403879261/8589934592)), (7/536870912), by norm_num⟩
  | 4 => ⟨((902515983/2147483648), (121636869/1073741824)), (79/8589934592), by norm_num⟩
  | 5 => ⟨((-2001844509/8589934592), (-269799209/4294967296)), (89/17179869184), by norm_num⟩
  | 6 => ⟨((925048585/8589934592), (997389659/34359738368)), (21/8589934592), by norm_num⟩
  | 7 => ⟨((-5862352627/137438953472), (-1580200755/137438953472)), (17/17179869184), by norm_num⟩
  | 8 => ⟨((4063473195/274877906944), (547655849/137438953472)), (3/8589934592), by norm_num⟩
  | 9 => ⟨((-2503631101/549755813888), (-1349710605/1099511627776)), (15/137438953472), by norm_num⟩
  | 10 => ⟨((5553231485/4398046511104), (1496876961/4398046511104)), (135/4398046511104), by norm_num⟩
  | 11 => ⟨((-2799423089/8796093022208), (-1509172429/17592186044416)), (139/17592186044416), by norm_num⟩
  | 12 => ⟨((5174432591/70368744177664), (697385743/35184372088832)), (131/70368744177664), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790859256563237/5070602400912917605986812821504), (171484222949/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55602999392363/19807040628566084398385987584), (203057125077/316912650057057350374175801344)), (23061/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945167454606445/19807040628566084398385987584), (456808906539/39614081257132168796771975168)), (3243/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890146990122973/2475880078570760549798248448), (485273670589/2475880078570760549798248448)), (13783/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442953293419619/38685626227668133590597632), (485177182849/154742504910672534362390528)), (27567/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550136936187257/9671406556917033397649408), (454751117659/9671406556917033397649408)), (25845/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629649592744165/302231454903657293676544), (397804767025/604462909807314587353088)), (22615/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888621479059909/75557863725914323419136), (646240696621/75557863725914323419136)), (36751/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649080706733713/2361183241434822606848), (484512543311/4722366482869645213696)), (27565/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405575780447557/147573952589676412928), (166482975413/147573952589676412928)), (2369/36893488147419103232), by norm_num⟩
  | 8 => ⟨((912271547208829/36893488147419103232), (416002910065/36893488147419103232)), (47383/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823858526268041/9223372036854775808), (233861109325/2305843009213693952)), (53311/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398776630803615/288230376151711744), (233685578357/288230376151711744)), (53317/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195560769616691/144115188075855872), (817110341157/144115188075855872)), (11665/36028797018963968), by norm_num⟩
  | 4 => ⟨((1493106266111315/36028797018963968), (612044454749/18014398509481984)), (70003/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491091757483421/9007199254740992), (1527356047143/9007199254740992)), (10941/1125899906842624), by norm_num⟩
  | 2 => ⟨((2231610225738467/4503599627370496), (761615664599/1125899906842624)), (87565/2251799813685248), by norm_num⟩
  | 1 => ⟨((138848871194051/140737488355328), (4549125709043/2251799813685248)), (262881/2251799813685248), by norm_num⟩
  | 0 => ⟨((1095814704574079/1125899906842624), (4508154664757/1125899906842624)), (32907/140737488355328), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1095814704574079/1125899906842624), (4508154664757/1125899906842624)), (125530243456792787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1066515358962667/1125899906842624), (1096923035101/140737488355328)), (1029103/2251799813685248), by norm_num⟩
  | 2 => ⟨((1010194597780503/1125899906842624), (16625069527765/1125899906842624)), (1965691/2251799813685248), by norm_num⟩
  | 3 => ⟨((906134485177387/1125899906842624), (59666246786611/2251799813685248)), (1792709/1125899906842624), by norm_num⟩
  | 4 => ⟨((728474782697475/1125899906842624), (96039876166381/2251799813685248)), (2980581/1125899906842624), by norm_num⟩
  | 5 => ⟨((938572943050211/2251799813685248), (124278592609167/2251799813685248)), (2055605/562949953421312), by norm_num⟩
  | 6 => ⟨((384347665181037/2251799813685248), (414404597475923/9007199254740992)), (15523959/4503599627370496), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-232581599/134217728), (-4181235703/134217728)), (1/67108864), by norm_num⟩, -5, term16ValuePoly, term16ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term16Value_checks : CertifiedScalarExp.Checks term16Value := by
  constructor
  · norm_num [term16Value, CertifiedScalarExp.reduced, term16ValuePoly, term16ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term16ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value, term16ValueSquares, term16ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, term16ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term16 : Sound J_term16 F_term16 c := by
  apply exp_sound (A_arg16 hcre) S_arg16 term16Value term16Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value,J_arg16]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term16,J_arg16,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((354151668007027/125000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log17 : Sound J_log17 F_log17 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log17_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-190133729/67108864), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog17 : Sound J_negLog17 F_negLog17 c := by
  apply sound_round (sound_scale (A_log17 hcre) S_log17)
  intro k
  fin_cases k <;> norm_num [J_negLog17, J_log17, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-237667161/134217728), (-4272661391/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg17 : Sound J_arg17 F_arg17 c := by
  apply sound_round (sound_mul (A_negLog17 hcre) (A_variable hcre) S_negLog17 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg17, J_negLog17, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1401141432741947/9007199254740992), (-622154411471749/9007199254740992)), (2115751/562949953421312), by norm_num⟩
  | 1 => ⟨((-946458007/2147483648), (1681038075/8589934592)), (93/8589934592), by norm_num⟩
  | 2 => ⟨((2681517455/4294967296), (-2381369753/8589934592)), (67/4294967296), by norm_num⟩
  | 3 => ⟨((-633109253/1073741824), (2248976187/8589934592)), (129/8589934592), by norm_num⟩
  | 4 => ⟨((112108349/268435456), (-199119667/1073741824)), (93/8589934592), by norm_num⟩
  | 5 => ⟨((-4065623941/17179869184), (225659399/2147483648)), (107/17179869184), by norm_num⟩
  | 6 => ⟨((1919796667/17179869184), (-1704909921/34359738368)), (103/34359738368), by norm_num⟩
  | 7 => ⟨((-12141057/268435456), (1380106725/68719476736)), (43/34359738368), by norm_num⟩
  | 8 => ⟨((2201485101/137438953472), (-1955068395/274877906944)), (31/68719476736), by norm_num⟩
  | 9 => ⟨((-5544246191/1099511627776), (1230916859/549755813888)), (79/549755813888), by norm_num⟩
  | 10 => ⟨((1570803229/1099511627776), (-348745007/549755813888)), (91/2199023255552), by norm_num⟩
  | 11 => ⟨((-1618334789/4398046511104), (359297821/2199023255552)), (95/8796093022208), by norm_num⟩
  | 12 => ⟨((1528362573/17592186044416), (-1357289841/35184372088832)), (23/8796093022208), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790834578331793/5070602400912917605986812821504), (-544337337963/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779237404677085/633825300114114700748351602688), (-644517991409/633825300114114700748351602688)), (23067/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236283626725431/4951760157141521099596496896), (-724969870585/39614081257132168796771975168)), (25951/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890076978874711/2475880078570760549798248448), (-385070675955/1237940039285380274899124224)), (13787/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771743165386003/154742504910672534362390528), (-769984871807/154742504910672534362390528)), (3447/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((387517826639017/2417851639229258349412352), (-360847300703/4835703278458516698824704)), (25853/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259241762706835/604462909807314587353088), (-315658305021/302231454903657293676544)), (22623/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472132043236069/18889465931478580854784), (-1025578035345/75557863725914323419136)), (36765/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649045719526441/2361183241434822606848), (-768911108121/4722366482869645213696)), (3447/590295810358705651712), by norm_num⟩
  | 9 => ⟨((405551728846529/147573952589676412928), (-264202572919/147573952589676412928)), (1185/18446744073709551616), by norm_num⟩
  | 8 => ⟨((456105712263933/18446744073709551616), (-1320349487743/73786976294838206464)), (23703/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823723267651753/9223372036854775808), (-1484481592677/9223372036854775808)), (13335/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594971286415131/1152921504606846976), (-1483342959015/1152921504606846976)), (26675/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195442462026005/144115188075855872), (-648322641977/72057594037927936)), (11673/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492928854103989/36028797018963968), (-971205603487/18014398509481984)), (17515/9007199254740992), by norm_num⟩
  | 3 => ⟨((1490870079248751/9007199254740992), (-605886562133/2251799813685248)), (87613/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115583565517219/2251799813685248), (-2416857585037/2251799813685248)), (87671/2251799813685248), by norm_num⟩
  | 1 => ⟨((2220917956485195/2251799813685248), (-7217220102579/2251799813685248)), (32913/281474976710656), by norm_num⟩
  | 0 => ⟨((1095152055803717/1125899906842624), (-14301572206965/2251799813685248)), (65973/281474976710656), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1095152055803717/1125899906842624), (-14301572206965/2251799813685248)), (251667023778819949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((532599249853587/562949953421312), (-27822004617809/2251799813685248)), (516723/1125899906842624), by norm_num⟩
  | 2 => ⟨((1007597852081311/1125899906842624), (-52644035935387/2251799813685248)), (1980997/2251799813685248), by norm_num⟩
  | 3 => ⟨((225277703800093/281474976710656), (-94225103334699/2251799813685248)), (3638321/2251799813685248), by norm_num⟩
  | 4 => ⟨((1438460210938911/2251799813685248), (-37706397861057/562949953421312)), (6128327/2251799813685248), by norm_num⟩
  | 5 => ⟨((454396391496007/1125899906842624), (-192696180864127/2251799813685248)), (8650559/2251799813685248), by norm_num⟩
  | 6 => ⟨((1401141432741947/9007199254740992), (-622154411471749/9007199254740992)), (2115751/562949953421312), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-237667161/134217728), (-4272661391/134217728)), (1/67108864), by norm_num⟩, -5, term17ValuePoly, term17ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term17Value_checks : CertifiedScalarExp.Checks term17Value := by
  constructor
  · norm_num [term17Value, CertifiedScalarExp.reduced, term17ValuePoly, term17ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term17ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value, term17ValueSquares, term17ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, term17ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term17 : Sound J_term17 F_term17 c := by
  apply exp_sound (A_arg17 hcre) S_arg17 term17Value term17Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value,J_arg17]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term17,J_arg17,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((722592939474041/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log18 : Sound J_log18 F_log18 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log18_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6207026087/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog18 : Sound J_negLog18 F_negLog18 c := by
  apply sound_round (sound_scale (A_log18 hcre) S_log18)
  intro k
  fin_cases k <;> norm_num [J_negLog18, J_log18, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-242461957/134217728), (-4358859823/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6207026087/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg18 : Sound J_arg18 F_arg18 c := by
  apply sound_round (sound_mul (A_negLog18 hcre) (A_variable hcre) S_negLog18 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg18, J_negLog18, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((180756752148025/2251799813685248), (-1290519848163301/9007199254740992)), (24278565/4503599627370496), by norm_num⟩
  | 1 => ⟨((-498251163/2147483648), (1778641759/4294967296)), (135/8589934592), by norm_num⟩
  | 2 => ⟨((720065545/2147483648), (-1285233977/2147483648)), (197/8589934592), by norm_num⟩
  | 3 => ⟨((-2775009487/8589934592), (2476535993/4294967296)), (3/134217728), by norm_num⟩
  | 4 => ⟨((1002601131/4294967296), (-1789527423/4294967296)), (141/8589934592), by norm_num⟩
  | 5 => ⟨((-2318311995/17179869184), (4137919619/17179869184)), (165/17179869184), by norm_num⟩
  | 6 => ⟨((1116797253/17179869184), (-996677167/8589934592)), (161/34359738368), by norm_num⟩
  | 7 => ⟨((-1844548137/68719476736), (3292305755/68719476736)), (135/68719476736), by norm_num⟩
  | 8 => ⟨((2665714921/274877906944), (-4757993787/274877906944)), (99/137438953472), by norm_num⟩
  | 9 => ⟨((-1712201583/549755813888), (3056082415/549755813888)), (129/549755813888), by norm_num⟩
  | 10 => ⟨((247444955/274877906944), (-3533285721/2199023255552)), (151/2199023255552), by norm_num⟩
  | 11 => ⟨((-520151207/2199023255552), (3713639731/8796093022208)), (5/274877906944), by norm_num⟩
  | 12 => ⟨((2004573811/35184372088832), (-3577933133/35184372088832)), (39/8796093022208), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581622622146687/10141204801825835211973625643008), (-1380911488473/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222397637503973/79228162514264337593543950336), (-204370017763/79228162514264337593543950336)), (23091/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890205611758589/39614081257132168796771975168), (-459759264303/9903520314283042199192993792)), (6495/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472502384344661/618970019642690137449562112), (-1953616667691/2475880078570760549798248448)), (27607/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771675637529393/154742504910672534362390528), (-976605772111/77371252455336267181195264)), (13805/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550007907487455/9671406556917033397649408), (-457676371105/2417851639229258349412352)), (809/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1259186196880693/604462909807314587353088), (-200179634893/75557863725914323419136)), (177/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((944218853390629/37778931862957161709568), (-2601528843511/75557863725914323419136)), (36821/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649011719664243/2361183241434822606848), (-975220637801/2361183241434822606848)), (13811/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622113172095429/590295810358705651712), (-1340355510373/295147905179352825856)), (18995/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824305304868643/73786976294838206464), (-3349171001739/73786976294838206464)), (47501/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227948816145527/1152921504606846976), (-941364194613/2305843009213693952)), (53459/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594837922379153/1152921504606846976), (-3762508040757/1152921504606846976)), (53483/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195325066191599/144115188075855872), (-102777499011/4503599627370496)), (23413/72057594037927936), by norm_num⟩
  | 4 => ⟨((93296959958681/2251799813685248), (-2463348859569/18014398509481984)), (35147/18014398509481984), by norm_num⟩
  | 3 => ⟨((745322883543521/4503599627370496), (-384174922113/562949953421312)), (87965/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115355603897607/2251799813685248), (-12258939303325/4503599627370496)), (176221/4503599627370496), by norm_num⟩
  | 1 => ⟨((1110107968355341/1125899906842624), (-571936876663/70368744177664)), (265063/2251799813685248), by norm_num⟩
  | 0 => ⟨((1094414102014591/1125899906842624), (-18129770778977/1125899906842624)), (533069/2251799813685248), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1094414102014591/1125899906842624), (-18129770778977/1125899906842624)), (2033496865279387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2127033727994219/2251799813685248), (-70491086059137/2251799813685248)), (263373/562949953421312), by norm_num⟩
  | 2 => ⟨((1003486957265307/1125899906842624), (-133170734502677/2251799813685248)), (2056201/2251799813685248), by norm_num⟩
  | 3 => ⟨((1780890923210145/2251799813685248), (-237383615276481/2251799813685248)), (1954245/1125899906842624), by norm_num⟩
  | 4 => ⟨((1383436254252213/2251799813685248), (-187740634489539/1125899906842624)), (7006313/2251799813685248), by norm_num⟩
  | 5 => ⟨((24604064427853/70368744177664), (-230684094181603/1125899906842624)), (2736373/562949953421312), by norm_num⟩
  | 6 => ⟨((180756752148025/2251799813685248), (-1290519848163301/9007199254740992)), (24278565/4503599627370496), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-242461957/134217728), (-4358859823/134217728)), (1/67108864), by norm_num⟩, -5, term18ValuePoly, term18ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term18Value_checks : CertifiedScalarExp.Checks term18Value := by
  constructor
  · norm_num [term18Value, CertifiedScalarExp.reduced, term18ValuePoly, term18ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term18ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value, term18ValueSquares, term18ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, term18ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term18 : Sound J_term18 F_term18 c := by
  apply exp_sound (A_arg18 hcre) S_arg18 term18Value term18Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value,J_arg18]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term18,J_arg18,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((73610974479161/25000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log19 : Sound J_log19 F_log19 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log19_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-197597955/67108864), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog19 : Sound J_negLog19 F_negLog19 c := by
  apply sound_round (sound_scale (A_log19 hcre) S_log19)
  intro k
  fin_cases k <;> norm_num [J_negLog19, J_log19, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-61749361/33554432), (-4440396545/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg19 : Sound J_arg19 F_arg19 c := by
  apply sound_round (sound_mul (A_negLog19 hcre) (A_variable hcre) S_negLog19 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg19, J_negLog19, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4319744735509/281474976710656), (-1423411472086953/9007199254740992)), (14717341/2251799813685248), by norm_num⟩
  | 1 => ⟨((6064999/134217728), (3996990415/8589934592)), (167/8589934592), by norm_num⟩
  | 2 => ⟨((-571456623/8589934592), (-1471111797/2147483648)), (31/1073741824), by norm_num⟩
  | 3 => ⟨((140218263/2147483648), (5775465223/8589934592)), (123/4294967296), by norm_num⟩
  | 4 => ⟨((-412864119/8589934592), (-4251376231/8589934592)), (183/8589934592), by norm_num⟩
  | 5 => ⟨((243130641/8589934592), (1251791789/4294967296)), (217/17179869184), by norm_num⟩
  | 6 => ⟨((-238627779/17179869184), (-1228608179/8589934592)), (215/34359738368), by norm_num⟩
  | 7 => ⟨((200749981/34359738368), (4134356357/68719476736)), (183/68719476736), by norm_num⟩
  | 8 => ⟨((-591096069/274877906944), (-6086680005/274877906944)), (271/274877906944), by norm_num⟩
  | 9 => ⟨((193382923/274877906944), (497829385/68719476736)), (179/549755813888), by norm_num⟩
  | 10 => ⟨((-455523373/2199023255552), (-1172662597/549755813888)), (213/2199023255552), by norm_num⟩
  | 11 => ⟨((487731191/8796093022208), (2511151607/4398046511104)), (115/4398046511104), by norm_num⟩
  | 12 => ⟨((-478698243/35184372088832), (-4929288449/35184372088832)), (57/8796093022208), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581578604278889/10141204801825835211973625643008), (-271530343759/1267650600228229401496703205376)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889563438818877/316912650057057350374175801344), (-2571730604295/633825300114114700748351602688)), (11557/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890144500704411/39614081257132168796771975168), (-1446362118627/19807040628566084398385987584)), (26007/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118121528963917/154742504910672534362390528), (-1536470964487/1237940039285380274899124224)), (27637/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885805201148763/77371252455336267181195264), (-1536146143525/77371252455336267181195264)), (27643/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387486644550997/2417851639229258349412352), (-2879583916217/9671406556917033397649408)), (25921/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259132362618871/604462909807314587353088), (-1259472991543/302231454903657293676544)), (11343/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944174952732209/37778931862957161709568), (-4091993916715/75557863725914323419136)), (36875/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297957308023367/4722366482869645213696), (-1533932066691/2361183241434822606848)), (13833/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811010893245835/295147905179352825856), (-2108237724307/295147905179352825856)), (38055/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824190391073791/73786976294838206464), (-5267838818745/73786976294838206464)), (5949/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1823460314980377/9223372036854775808), (-5922531673273/9223372036854775808)), (13393/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398676634983245/288230376151711744), (-2958900315535/576460752303423488)), (26805/576460752303423488), by norm_num⟩
  | 5 => ⟨((597604397462709/72057594037927936), (-5172756848351/144115188075855872)), (5869/18014398509481984), by norm_num⟩
  | 4 => ⟨((373143583963181/9007199254740992), (-7748507158981/36028797018963968)), (17629/9007199254740992), by norm_num⟩
  | 3 => ⟨((745209961836903/4503599627370496), (-9667055654963/9007199254740992)), (88297/9007199254740992), by norm_num⟩
  | 2 => ⟨((139390368035555/281474976710656), (-9639230007039/2251799813685248)), (88527/2251799813685248), by norm_num⟩
  | 1 => ⟨((277435510689723/281474976710656), (-28778854175427/2251799813685248)), (266733/2251799813685248), by norm_num⟩
  | 0 => ⟨((2187230259816103/2251799813685248), (-57004118084289/2251799813685248)), (538085/2251799813685248), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2187230259816103/2251799813685248), (-57004118084289/2251799813685248)), (2052631386763762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((132691822529081/140737488355328), (-55369545396683/1125899906842624)), (1072555/2251799813685248), by norm_num⟩
  | 2 => ⟨((1996251836672991/2251799813685248), (-104408370181269/1125899906842624)), (531993/562949953421312), by norm_num⟩
  | 3 => ⟨((437585186348583/562949953421312), (-92559471526595/562949953421312)), (2083811/1125899906842624), by norm_num⟩
  | 4 => ⟨((1299678867940497/2251799813685248), (-143894331459263/562949953421312)), (3924759/1125899906842624), by norm_num⟩
  | 5 => ⟨((603018036284091/2251799813685248), (-664415799939027/2251799813685248)), (3268465/562949953421312), by norm_num⟩
  | 6 => ⟨((-4319744735509/281474976710656), (-1423411472086953/9007199254740992)), (14717341/2251799813685248), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-61749361/33554432), (-4440396545/134217728)), (1/67108864), by norm_num⟩, -5, term19ValuePoly, term19ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term19Value_checks : CertifiedScalarExp.Checks term19Value := by
  constructor
  · norm_num [term19Value, CertifiedScalarExp.reduced, term19ValuePoly, term19ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term19ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value, term19ValueSquares, term19ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, term19ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term19 : Sound J_term19 F_term19 c := by
  apply exp_sound (A_arg19 hcre) S_arg19 term19Value term19Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value,J_arg19]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term19,J_arg19,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2995732273553991/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log20 : Sound J_log20 F_log20 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log20_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6433286071/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog20 : Sound J_negLog20 F_negLog20 c := by
  apply sound_round (sound_scale (A_log20 hcre) S_log20)
  intro k
  fin_cases k <;> norm_num [J_negLog20, J_log20, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-251300237/134217728), (-4517750013/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6433286071/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg20 : Sound J_arg20 F_arg20 c := by
  apply sound_round (sound_mul (A_negLog20 hcre) (A_variable hcre) S_negLog20 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg20, J_negLog20, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-863460190238325/9007199254740992), (-270719916806299/2251799813685248)), (31275163/4503599627370496), by norm_num⟩
  | 1 => ⟨((2466865119/8589934592), (773434059/2147483648)), (45/2147483648), by norm_num⟩
  | 2 => ⟨((-1847516863/4294967296), (-579250343/1073741824)), (17/536870912), by norm_num⟩
  | 3 => ⟨((3689777261/8589934592), (4627410525/8589934592)), (137/4294967296), by norm_num⟩
  | 4 => ⟨((-1381698103/4294967296), (-3465620763/8589934592)), (207/8589934592), by norm_num⟩
  | 5 => ⟨((3311358079/17179869184), (4152828787/17179869184)), (125/8589934592), by norm_num⟩
  | 6 => ⟨((-1653323711/17179869184), (-2073460537/17179869184)), (63/8589934592), by norm_num⟩
  | 7 => ⟨((2830237257/68719476736), (887361807/17179869184)), (109/34359738368), by norm_num⟩
  | 8 => ⟨((-2119658273/137438953472), (-2658298403/137438953472)), (165/137438953472), by norm_num⟩
  | 9 => ⟨((705547633/137438953472), (3539355697/549755813888)), (221/549755813888), by norm_num⟩
  | 10 => ⟨((-3381810903/2199023255552), (-4241184835/2199023255552)), (267/2199023255552), by norm_num⟩
  | 11 => ⟨((460500003/1099511627776), (1155041299/2199023255552)), (147/4398046511104), by norm_num⟩
  | 12 => ⟨((-459844907/4398046511104), (-2306796331/17592186044416)), (37/4398046511104), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790768422377973/5070602400912917605986812821504), (-730743660049/2535301200456458802993406410752)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((55596080372319/19807040628566084398385987584), (-3460343360015/633825300114114700748351602688)), (723/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1890085502648137/39614081257132168796771975168), (-1946116748199/19807040628566084398385987584)), (26033/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944940789153511/1237940039285380274899124224), (-2067353352537/1237940039285380274899124224)), (27667/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110721705793649/9671406556917033397649408), (-258363530439/9671406556917033397649408)), (13837/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549887174585409/9671406556917033397649408), (-1937253621297/4835703278458516698824704)), (811/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1259080146245535/604462909807314587353088), (-1694624141809/302231454903657293676544)), (5679/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((236033075945529/9444732965739290427392), (-5505755888607/75557863725914323419136)), (18463/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297892944436017/4722366482869645213696), (-4127766256663/4722366482869645213696)), (6927/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405483163297827/147573952589676412928), (-354572463767/36893488147419103232)), (38117/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824078025526297/73786976294838206464), (-7087671621051/73786976294838206464)), (47677/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823332600806051/9223372036854775808), (-7968438119441/9223372036854775808)), (26839/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594577199841475/1152921504606846976), (-497621892743/72057594037927936)), (26865/576460752303423488), by norm_num⟩
  | 5 => ⟨((597546898482921/72057594037927936), (-217481607591/4503599627370496)), (47073/144115188075855872), by norm_num⟩
  | 4 => ⟨((373099549396905/9007199254740992), (-2606134115029/9007199254740992)), (35363/18014398509481984), by norm_num⟩
  | 3 => ⟨((745096699859863/4503599627370496), (-6502587764827/4503599627370496)), (44307/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114886935972155/2251799813685248), (-405217980925/70368744177664)), (22231/562949953421312), by norm_num⟩
  | 1 => ⟨((69335279201597/70368744177664), (-19355111475793/1125899906842624)), (8385/70368744177664), by norm_num⟩
  | 0 => ⟨((546383305542951/562949953421312), (-2395606930989/70368744177664)), (135715/562949953421312), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((546383305542951/562949953421312), (-2395606930989/70368744177664)), (517711641551780523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((8275808507699/8796093022208), (-74403466995555/1125899906842624)), (272683/562949953421312), by norm_num⟩
  | 2 => ⟨((495864685257457/562949953421312), (-140005078074891/1125899906842624)), (137287/140737488355328), by norm_num⟩
  | 3 => ⟨((428069012439259/562949953421312), (-493284161777663/2251799813685248)), (4415951/2251799813685248), by norm_num⟩
  | 4 => ⟨((1193960488837073/2251799813685248), (-750189826647201/2251799813685248)), (540659/140737488355328), by norm_num⟩
  | 5 => ⟨((191570508989237/1125899906842624), (-99442344597055/281474976710656)), (14937349/2251799813685248), by norm_num⟩
  | 6 => ⟨((-863460190238325/9007199254740992), (-270719916806299/2251799813685248)), (31275163/4503599627370496), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-251300237/134217728), (-4517750013/134217728)), (1/67108864), by norm_num⟩, -5, term20ValuePoly, term20ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term20Value_checks : CertifiedScalarExp.Checks term20Value := by
  constructor
  · norm_num [term20Value, CertifiedScalarExp.reduced, term20ValuePoly, term20ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term20ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value, term20ValueSquares, term20ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, term20ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term20 : Sound J_term20 F_term20 c := by
  apply exp_sound (A_arg20 hcre) S_arg20 term20Value term20Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value,J_arg20]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term20,J_arg20,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3044522437723423/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log21 : Sound J_log21 F_log21 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log21_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6538062151/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog21 : Sound J_negLog21 F_negLog21 c := by
  apply sound_round (sound_scale (A_log21 hcre) S_log21)
  intro k
  fin_cases k <;> norm_num [J_negLog21, J_log21, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-255393053/134217728), (-2295664303/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg21 : Sound J_arg21 F_arg21 c := by
  apply sound_round (sound_mul (A_negLog21 hcre) (A_variable hcre) S_negLog21 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg21, J_negLog21, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1262196347032791/9007199254740992), (-459958751086031/9007199254740992)), (58944011/9007199254740992), by norm_num⟩
  | 1 => ⟨((3664765453/8589934592), (333870587/2147483648)), (173/8589934592), by norm_num⟩
  | 2 => ⟨((-5578730325/8589934592), (-2032952987/8589934592)), (133/4294967296), by norm_num⟩
  | 3 => ⟨((353845201/536870912), (2063123661/8589934592)), (17/536870912), by norm_num⟩
  | 4 => ⟨((-538644827/1073741824), (-1570306569/8589934592)), (209/8589934592), by norm_num⟩
  | 5 => ⟨((2623866019/8589934592), (1912333433/17179869184)), (257/17179869184), by norm_num⟩
  | 6 => ⟨((-2662806323/17179869184), (-1940714015/34359738368)), (263/34359738368), by norm_num⟩
  | 7 => ⟨((2316278171/34359738368), (844078195/34359738368)), (231/68719476736), by norm_num⟩
  | 8 => ⟨((-220373777/8589934592), (-642453751/68719476736)), (177/137438953472), by norm_num⟩
  | 9 => ⟨((2385539231/274877906944), (1738635431/549755813888)), (121/274877906944), by norm_num⟩
  | 10 => ⟨((-1452565543/549755813888), (-264665729/274877906944)), (297/2199023255552), by norm_num⟩
  | 11 => ⟨((3216267919/4398046511104), (146505591/549755813888)), (83/2199023255552), by norm_num⟩
  | 12 => ⟨((-815999987/4398046511104), (-148679853/2199023255552)), (85/8796093022208), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581497123104531/10141204801825835211973625643008), (-909267641015/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889512018471469/316912650057057350374175801344), (-4305504274619/633825300114114700748351602688)), (23157/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945014230103203/19807040628566084398385987584), (-4842858130601/39614081257132168796771975168)), (13029/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236227590420485/309485009821345068724781056), (-5144534984493/2475880078570760549798248448)), (27695/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771486159672883/154742504910672534362390528), (-2571703982235/77371252455336267181195264)), (27703/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549829567094039/9671406556917033397649408), (-4820747609527/9671406556917033397649408)), (25981/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629514722307889/302231454903657293676544), (-4216956915145/604462909807314587353088)), (22743/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472045416146613/18889465931478580854784), (-6850310398691/75557863725914323419136)), (36975/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297830253912643/4722366482869645213696), (-5135769027129/4722366482869645213696)), (27747/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621845669192031/590295810358705651712), (-3529245869721/295147905179352825856)), (38177/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455992030040341/18446744073709551616), (-8818329465575/73786976294838206464)), (23879/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823207343462933/9223372036854775808), (-9914042290977/9223372036854775808)), (13445/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398612482179435/288230376151711744), (-9905821305787/1152921504606846976)), (53845/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597490087004897/72057594037927936), (-2164586935343/36028797018963968)), (11797/36028797018963968), by norm_num⟩
  | 4 => ⟨((746111626825009/18014398509481984), (-6484518302727/18014398509481984)), (70927/36028797018963968), by norm_num⟩
  | 3 => ⟨((372491713752821/2251799813685248), (-16178962362349/9007199254740992)), (22229/2251799813685248), by norm_num⟩
  | 2 => ⟨((557324323855655/1125899906842624), (-1008155824733/140737488355328)), (89301/2251799813685248), by norm_num⟩
  | 1 => ⟨((1108977863367769/1125899906842624), (-24074675970929/1125899906842624)), (134917/1125899906842624), by norm_num⟩
  | 0 => ⟨((1091877839735137/1125899906842624), (-47665758033487/1125899906842624)), (68427/281474976710656), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1091877839735137/1125899906842624), (-47665758033487/1125899906842624)), (261028290868663699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1056865876961199/1125899906842624), (-46225410087201/562949953421312)), (554051/1125899906842624), by norm_num⟩
  | 2 => ⟨((984473238693479/1125899906842624), (-173564482145497/1125899906842624)), (565575/562949953421312), by norm_num⟩
  | 3 => ⟨((834055427604235/1125899906842624), (-18970335065031/70368744177664)), (581719/281474976710656), by norm_num⟩
  | 4 => ⟨((536034160633143/1125899906842624), (-899394247225021/2251799813685248)), (9404067/2251799813685248), by norm_num⟩
  | 5 => ⟨((302354118205673/4503599627370496), (-1712784724324271/4503599627370496)), (16466621/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1262196347032791/9007199254740992), (-459958751086031/9007199254740992)), (58944011/9007199254740992), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-255393053/134217728), (-2295664303/67108864)), (1/67108864), by norm_num⟩, -5, term21ValuePoly, term21ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term21Value_checks : CertifiedScalarExp.Checks term21Value := by
  constructor
  · norm_num [term21Value, CertifiedScalarExp.reduced, term21ValuePoly, term21ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term21ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value, term21ValueSquares, term21ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, term21ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term21 : Sound J_term21 F_term21 c := by
  apply exp_sound (A_arg21 hcre) S_arg21 term21Value term21Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value,J_arg21]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term21,J_arg21,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term16Jet : Jet 12 := J_term16
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile025Terms2

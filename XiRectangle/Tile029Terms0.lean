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
namespace Reinmann.XiRectangle.Tile029Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨29,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (1551/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (1551/128))
  have he : value ((5/8), (1551/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-372130559/536870912), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-232581599/536870912), (-2254587879/268435456)), (1/268435456), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-189241028507879/562949953421312), (-1248571593456683/2251799813685248)), (7977451/1125899906842624), by norm_num⟩
  | 1 => ⟨((1000762065/4294967296), (1650703201/4294967296)), (11/2147483648), by norm_num⟩
  | 2 => ⟨((-2774701615/34359738368), (-4576721079/34359738368)), (63/34359738368), by norm_num⟩
  | 3 => ⟨((1282184401/68719476736), (16522611/536870912)), (15/34359738368), by norm_num⟩
  | 4 => ⟨((-1777485005/549755813888), (-2931865915/549755813888)), (43/549755813888), by norm_num⟩
  | 5 => ⟨((7700367/17179869184), (3251543349/4398046511104)), (25/2199023255552), by norm_num⟩
  | 6 => ⟨((-455465615/8796093022208), (-751266035/8796093022208)), (3/2199023255552), by norm_num⟩
  | 7 => ⟨((1443221517/281474976710656), (1190258135/140737488355328)), (79/562949953421312), by norm_num⟩
  | 8 => ⟨((-2000729851/4503599627370496), (-1650048141/2251799813685248)), (7/562949953421312), by norm_num⟩
  | 9 => ⟨((616355669/18014398509481984), (508322763/9007199254740992)), (71/72057594037927936), by norm_num⟩
  | 10 => ⟨((-2734241243/1152921504606846976), (-35234249/9007199254740992)), (81/1152921504606846976), by norm_num⟩
  | 11 => ⟨((1378350261/9223372036854775808), (1136757311/4611686018427387904)), (21/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-2547732259/295147905179352825856), (-2101173667/147573952589676412928)), (5/18446744073709551616), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583411453610655/10141204801825835211973625643008), (-2756077513057/10141204801825835211973625643008)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445324289949285/158456325028528675187087900672), (-3270510055355/633825300114114700748351602688)), (723/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((118286604673669/2475880078570760549798248448), (-919791944065/9903520314283042199192993792)), (1627/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((946268874148693/1237940039285380274899124224), (-3908941418047/2475880078570760549798248448)), (6915/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1774203166678103/154742504910672534362390528), (-3908745182571/154742504910672534362390528)), (6917/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552376741748363/9671406556917033397649408), (-1832120006729/4835703278458516698824704)), (6487/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157657275326959/75557863725914323419136), (-3206001309745/604462909807314587353088)), (2839/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((118237709893685/4722366482869645213696), (-1302340146271/18889465931478580854784)), (9229/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650273245022511/2361183241434822606848), (-3906677611599/4722366482869645213696)), (6925/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406395109187035/147573952589676412928), (-5371124196507/590295810358705651712)), (9527/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1828636491069273/73786976294838206464), (-6713068222655/73786976294838206464)), (11915/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828459134371245/9223372036854775808), (-471940602237/576460752303423488)), (6707/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599701554742923/1152921504606846976), (-7549607681321/1152921504606846976)), (6713/576460752303423488), by norm_num⟩
  | 5 => ⟨((599787575886231/72057594037927936), (-825535254227/18014398509481984)), (5881/72057594037927936), by norm_num⟩
  | 4 => ⟨((1499115306521375/36028797018963968), (-9903167459761/36028797018963968)), (8835/18014398509481984), by norm_num⟩
  | 3 => ⟨((1498581143650269/9007199254740992), (-12373248067963/9007199254740992)), (2767/1125899906842624), by norm_num⟩
  | 2 => ⟨((1123261663724351/2251799813685248), (-12364653272987/2251799813685248)), (22209/2251799813685248), by norm_num⟩
  | 1 => ⟨((1121893834350357/1125899906842624), (-9262697698127/562949953421312)), (16747/562949953421312), by norm_num⟩
  | 0 => ⟨((1117693349561355/1125899906842624), (-18481934428257/562949953421312)), (16929/281474976710656), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1117693349561355/1125899906842624), (-18481934428257/562949953421312)), (64579011083507449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((554166533130047/562949953421312), (-73388886780961/1125899906842624)), (34723/281474976710656), by norm_num⟩
  | 2 => ⟨((1086256646465381/1125899906842624), (-72243837503689/562949953421312)), (145779/562949953421312), by norm_num⟩
  | 3 => ⟨((1029467012757459/1125899906842624), (-17425027788353/70368744177664)), (637417/1125899906842624), by norm_num⟩
  | 4 => ⟨((218063931898049/281474976710656), (-254921293738043/562949953421312)), (740663/562949953421312), by norm_num⟩
  | 5 => ⟨((444880212946935/1125899906842624), (-197492296781317/281474976710656)), (909201/281474976710656), by norm_num⟩
  | 6 => ⟨((-189241028507879/562949953421312), (-1248571593456683/2251799813685248)), (7977451/1125899906842624), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-232581599/536870912), (-2254587879/268435456)), (1/268435456), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-4718503851/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-368633113/536870912), (-7146874485/536870912)), (3/536870912), by norm_num⟩
  | 1 => ⟨((-4718503851/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((832490861018431/2251799813685248), (-384458662263737/1125899906842624)), (11543893/2251799813685248), by norm_num⟩
  | 1 => ⟨((-3488863717/8589934592), (402804385/1073741824)), (51/8589934592), by norm_num⟩
  | 2 => ⟨((3832908553/17179869184), (-1770103389/8589934592)), (59/17179869184), by norm_num⟩
  | 3 => ⟨((-2807253625/34359738368), (2592876447/34359738368)), (45/34359738368), by norm_num⟩
  | 4 => ⟨((1542041665/68719476736), (-356070741/17179869184)), (51/137438953472), by norm_num⟩
  | 5 => ⟨((-2710569477/549755813888), (2503575627/549755813888)), (47/549755813888), by norm_num⟩
  | 6 => ⟨((1985243291/2199023255552), (-3667278599/4398046511104)), (9/549755813888), by norm_num⟩
  | 7 => ⟨((-2492585915/17592186044416), (2302238477/17592186044416)), (47/17592186044416), by norm_num⟩
  | 8 => ⟨((2738385517/140737488355328), (-1264633741/70368744177664)), (27/70368744177664), by norm_num⟩
  | 9 => ⟨((-2674154649/1125899906842624), (2469941633/1125899906842624)), (27/562949953421312), by norm_num⟩
  | 10 => ⟨((2350287327/9007199254740992), (-271350823/1125899906842624)), (25/4503599627370496), by norm_num⟩
  | 11 => ⟨((-1877857847/72057594037927936), (3468908785/144115188075855872)), (41/72057594037927936), by norm_num⟩
  | 12 => ⟨((2750716943/1152921504606846976), (-2540657213/1152921504606846976)), (31/576460752303423488), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583081351377037/10141204801825835211973625643008), (-30355755681/316912650057057350374175801344)), (455/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1780910511654029/633825300114114700748351602688), (-1152216012511/633825300114114700748351602688)), (8655/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892151023778179/39614081257132168796771975168), (-1296162390225/39614081257132168796771975168)), (4869/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892076327767729/2475880078570760549798248448), (-688537977099/1237940039285380274899124224)), (10347/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773742191797279/154742504910672534362390528), (-688483650809/77371252455336267181195264)), (2587/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775972525621167/4835703278458516698824704), (-1290791409283/9671406556917033397649408)), (4851/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260880946803373/604462909807314587353088), (-1129327055443/604462909807314587353088)), (4245/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236398900631967/9444732965739290427392), (-1834940055843/75557863725914323419136)), (6899/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300088151496187/4722366482869645213696), (-344003925359/1180591620717411303424)), (5175/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624951482610325/590295810358705651712), (-1891713944341/590295810358705651712)), (7117/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456963047499519/18446744073709551616), (-2364181020641/73786976294838206464)), (4449/18446744073709551616), by norm_num⟩
  | 7 => ⟨((456894848971777/2305843009213693952), (-664767325971/2305843009213693952)), (10013/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1598825065438161/1152921504606846976), (-664569128663/288230376151711744)), (313/18014398509481984), by norm_num⟩
  | 5 => ⟨((1198811877447747/144115188075855872), (-2325100256587/144115188075855872)), (137/1125899906842624), by norm_num⟩
  | 4 => ⟨((46811803090265/1125899906842624), (-1742933741425/18014398509481984)), (26317/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497171907335499/9007199254740992), (-4354215367389/9007199254740992)), (16461/4503599627370496), by norm_num⟩
  | 2 => ⟨((1121871570177077/2251799813685248), (-4349539073263/2251799813685248)), (32961/2251799813685248), by norm_num⟩
  | 1 => ⟨((1119856491038341/1125899906842624), (-6512625524213/1125899906842624)), (387/8796093022208), by norm_num⟩
  | 0 => ⟨((1113809490254815/1125899906842624), (-12978564616809/1125899906842624)), (99455/1125899906842624), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1113809490254815/1125899906842624), (-12978564616809/1125899906842624)), (379390720847701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1101699298404471/1125899906842624), (-12839194987257/562949953421312)), (49767/281474976710656), by norm_num⟩
  | 2 => ⟨((538716611050747/562949953421312), (-1570402930977/35184372088832)), (99665/281474976710656), by norm_num⟩
  | 3 => ⟨((2057619842960909/2251799813685248), (-96179308566217/1125899906842624)), (1597171/2251799813685248), by norm_num⟩
  | 4 => ⟨((1863752521452155/2251799813685248), (-351541824606919/2251799813685248)), (3191759/2251799813685248), by norm_num⟩
  | 5 => ⟨((371923803618313/562949953421312), (-36370182532721/140737488355328)), (6280031/2251799813685248), by norm_num⟩
  | 6 => ⟨((832490861018431/2251799813685248), (-384458662263737/1125899906842624)), (11543893/2251799813685248), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-368633113/536870912), (-7146874485/536870912)), (3/536870912), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-372130559/268435456), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-232581599/268435456), (-2254587879/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-54730462054367/281474976710656), (104929830385225/281474976710656)), (20679351/2251799813685248), by norm_num⟩
  | 1 => ⟨((1157722945/4294967296), (-69362465/134217728)), (7/536870912), by norm_num⟩
  | 2 => ⟨((-802472395/4294967296), (3077017411/8589934592)), (5/536870912), by norm_num⟩
  | 3 => ⟨((741641971/8589934592), (-710941981/4294967296)), (19/4294967296), by norm_num⟩
  | 4 => ⟨((-2056268165/68719476736), (1971149719/34359738368)), (107/68719476736), by norm_num⟩
  | 5 => ⟨((1140237185/137438953472), (-4372149985/274877906944)), (121/274877906944), by norm_num⟩
  | 6 => ⟨((-131725365/68719476736), (1010181145/274877906944)), (57/549755813888), by norm_num⟩
  | 7 => ⟨((834789169/2199023255552), (-3200933543/4398046511104)), (23/1099511627776), by norm_num⟩
  | 8 => ⟨((-578631759/8796093022208), (4437436121/35184372088832)), (65/17592186044416), by norm_num⟩
  | 9 => ⟨((2852102915/281474976710656), (-683510297/35184372088832)), (163/281474976710656), by norm_num⟩
  | 10 => ⟨((-1581541675/1125899906842624), (1516074353/562949953421312)), (23/281474976710656), by norm_num⟩
  | 11 => ⟨((797266293/4503599627370496), (-3057055021/9007199254740992)), (95/9007199254740992), by norm_num⟩
  | 12 => ⟨((-736830511/36028797018963968), (1412659379/36028797018963968)), (45/36028797018963968), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197855892514491/1267650600228229401496703205376), (668098839443/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222578511788121/79228162514264337593543950336), (3168947116005/633825300114114700748351602688)), (11565/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891833047805055/39614081257132168796771975168), (3564777870195/39614081257132168796771975168)), (13013/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891738161258935/2475880078570760549798248448), (3787240248775/2475880078570760549798248448)), (13829/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773403668712883/154742504910672534362390528), (3786861913727/154742504910672534362390528)), (1729/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((775813653549157/4835703278458516698824704), (3549781017583/9671406556917033397649408)), (12971/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260602542047725/604462909807314587353088), (776414078157/151115727451828646838272)), (11353/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890738087658133/75557863725914323419136), (1261484375871/18889465931478580854784)), (18455/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299747692747903/4722366482869645213696), (3783793265017/4722366482869645213696)), (13847/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101530146480185/36893488147419103232), (5201643259255/590295810358705651712)), (19049/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827264254972191/73786976294838206464), (406277812397/4611686018427387904)), (1489/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1826915892244859/9223372036854775808), (913848445909/1152921504606846976)), (26821/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1598158967959845/1152921504606846976), (3654010191953/576460752303423488)), (26845/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599113063478863/72057594037927936), (24966420195/562949953421312)), (23517/144115188075855872), by norm_num⟩
  | 4 => ⟨((374273312483297/9007199254740992), (598804616813/2251799813685248)), (69/70368744177664), by norm_num⟩
  | 3 => ⟨((187007021455581/1125899906842624), (2991295152867/2251799813685248)), (22127/4503599627370496), by norm_num⟩
  | 2 => ⟨((1120740605018657/2251799813685248), (11948799829497/2251799813685248)), (44395/2251799813685248), by norm_num⟩
  | 1 => ⟨((1118122082603319/1125899906842624), (17882201851541/1125899906842624)), (523/8796093022208), by norm_num⟩
  | 0 => ⟨((555094754211025/562949953421312), (8900034613905/281474976710656)), (67651/562949953421312), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((555094754211025/562949953421312), (8900034613905/281474976710656)), (258068086864280523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((546786338318987/562949953421312), (8775846763021/140737488355328)), (137693/562949953421312), by norm_num⟩
  | 2 => ⟨((1057795813571819/1125899906842624), (136381945515063/1125899906842624)), (569303/1125899906842624), by norm_num⟩
  | 3 => ⟨((977291090851289/1125899906842624), (256264788967211/1125899906842624)), (1207655/1125899906842624), by norm_num⟩
  | 4 => ⟨((789969187125277/1125899906842624), (55610026618367/140737488355328)), (2646257/1125899906842624), by norm_num⟩
  | 5 => ⟨((756964114031539/2251799813685248), (312142898364175/562949953421312)), (5804653/1125899906842624), by norm_num⟩
  | 6 => ⟨((-54730462054367/281474976710656), (104929830385225/281474976710656)), (20679351/2251799813685248), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-232581599/268435456), (-2254587879/134217728)), (1/134217728), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-6912483199/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-270018875/268435456), (-2617495469/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6912483199/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((654439458434377/2251799813685248), (-499892222600691/2251799813685248)), (10597801/2251799813685248), by norm_num⟩
  | 1 => ⟨((-4017943099/8589934592), (3069097501/8589934592)), (67/8589934592), by norm_num⟩
  | 2 => ⟨((3233314977/8589934592), (-1234880469/4294967296)), (7/1073741824), by norm_num⟩
  | 3 => ⟨((-1734606569/8589934592), (2649951259/17179869184)), (31/8589934592), by norm_num⟩
  | 4 => ⟨((2791741575/34359738368), (-2132466011/34359738368)), (13/8589934592), by norm_num⟩
  | 5 => ⟨((-1797253893/68719476736), (686414329/34359738368)), (69/137438953472), by norm_num⟩
  | 6 => ⟨((482094759/68719476736), (-2945976653/549755813888)), (19/137438953472), by norm_num⟩
  | 7 => ⟨((-3546978663/2199023255552), (1354676147/1099511627776)), (71/2199023255552), by norm_num⟩
  | 8 => ⟨((2854320967/8796093022208), (-1090133575/4398046511104)), (59/8796093022208), by norm_num⟩
  | 9 => ⟨((-4083424337/70368744177664), (3119115209/70368744177664)), (87/70368744177664), by norm_num⟩
  | 10 => ⟨((328600897/35184372088832), (-502002227/70368744177664)), (29/140737488355328), by norm_num⟩
  | 11 => ⟨((-769254897/562949953421312), (2350375029/2251799813685248)), (69/2251799813685248), by norm_num⟩
  | 12 => ⟨((3301514655/18014398509481984), (-157615945/1125899906842624)), (19/4503599627370496), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197833183968175/1267650600228229401496703205376), (-849700134843/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780417508113653/633825300114114700748351602688), (-1007349550249/633825300114114700748351602688)), (5769/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472899111862563/9903520314283042199192993792), (-566583012007/19807040628566084398385987584)), (12981/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891487153679981/2475880078570760549798248448), (-18810394769/38685626227668133590597632)), (6897/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886576544436391/77371252455336267181195264), (-300931548445/38685626227668133590597632)), (6897/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551392842855159/9671406556917033397649408), (-1128345562845/9671406556917033397649408)), (12933/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630198920030961/302231454903657293676544), (-987154645687/604462909807314587353088)), (5659/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945203149165267/37778931862957161709568), (-1603849367653/75557863725914323419136)), (18393/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299499595450401/4722366482869645213696), (-1202644757383/4722366482869645213696)), (13797/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812071209757777/295147905179352825856), (-1653242943025/590295810358705651712)), (18973/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456710290820391/18446744073709551616), (-1032981717333/36893488147419103232)), (23721/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826442406208175/9223372036854775808), (-2323397527637/9223372036854775808)), (6673/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1597688594857949/1152921504606846976), (-2322383731027/1152921504606846976)), (6675/288230376151711744), by norm_num⟩
  | 5 => ⟨((598909024753683/72057594037927936), (-2030945757333/144115188075855872)), (23371/144115188075855872), by norm_num⟩
  | 4 => ⟨((748244062095257/18014398509481984), (-3044139905547/36028797018963968)), (137/140737488355328), by norm_num⟩
  | 3 => ⟨((747655990317655/4503599627370496), (-3801189991679/9007199254740992)), (21935/4503599627370496), by norm_num⟩
  | 2 => ⟨((2240029408169967/4503599627370496), (-3795218428969/2251799813685248)), (87829/4503599627370496), by norm_num⟩
  | 1 => ⟨((2234157673532253/2251799813685248), (-709739865713/140737488355328)), (1031/17592186044416), by norm_num⟩
  | 0 => ⟨((277071180305601/281474976710656), (-11296323992035/1125899906842624)), (264833/2251799813685248), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((277071180305601/281474976710656), (-11296323992035/1125899906842624)), (1010257729537200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1090831794989179/1125899906842624), (-5559794085719/281474976710656)), (526695/2251799813685248), by norm_num⟩
  | 2 => ⟨((2112833328728855/2251799813685248), (-86185993983109/2251799813685248)), (260347/562949953421312), by norm_num⟩
  | 3 => ⟨((247393031029197/281474976710656), (-40433576610685/562949953421312)), (1016979/1125899906842624), by norm_num⟩
  | 4 => ⟨((1727886264928605/2251799813685248), (-284301935183425/2251799813685248)), (241721/140737488355328), by norm_num⟩
  | 5 => ⟨((1289974062759163/2251799813685248), (-54538752280571/281474976710656)), (863999/281474976710656), by norm_num⟩
  | 6 => ⟨((654439458434377/2251799813685248), (-499892222600691/2251799813685248)), (10597801/2251799813685248), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-270018875/268435456), (-2617495469/134217728)), (1/134217728), by norm_num⟩, -3, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-7695548323/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-75151839/67108864), (-2914012561/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-7695548323/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-706196895194387/2251799813685248), (-406236481425843/4503599627370496)), (3929673/562949953421312), by norm_num⟩
  | 1 => ⟨((2413434933/4294967296), (1388317227/8589934592)), (109/8589934592), by norm_num⟩
  | 2 => ⟨((-4324294895/8589934592), (-1243765269/8589934592)), (99/8589934592), by norm_num⟩
  | 3 => ⟨((5165397551/17179869184), (742842733/8589934592)), (15/2147483648), by norm_num⟩
  | 4 => ⟨((-4627574987/34359738368), (-1330995501/34359738368)), (109/34359738368), by norm_num⟩
  | 5 => ⟨((3316600521/68719476736), (953929517/68719476736)), (79/68719476736), by norm_num⟩
  | 6 => ⟨((-990425065/68719476736), (-569737415/137438953472)), (3/8589934592), by norm_num⟩
  | 7 => ⟨((2028118273/549755813888), (583332805/549755813888)), (25/274877906944), by norm_num⟩
  | 8 => ⟨((-3633900121/4398046511104), (-1045192077/4398046511104)), (91/4398046511104), by norm_num⟩
  | 9 => ⟨((1446905545/8796093022208), (1664651379/35184372088832)), (147/35184372088832), by norm_num⟩
  | 10 => ⟨((-2074005369/70368744177664), (-1193061949/140737488355328)), (107/140737488355328), by norm_num⟩
  | 11 => ⟨((2702631825/562949953421312), (388669099/281474976710656)), (141/1125899906842624), by norm_num⟩
  | 12 => ⟨((-6456621553/9007199254740992), (-928535385/4503599627370496)), (171/9007199254740992), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582517037882311/10141204801825835211973625643008), (-3727461697275/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780231676060431/633825300114114700748351602688), (-2209104018753/316912650057057350374175801344)), (2895/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1891386820561237/39614081257132168796771975168), (-1242489690661/9903520314283042199192993792)), (13031/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891263719093913/2475880078570760549798248448), (-1319993560275/618970019642690137449562112)), (13849/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221616107532385/19342813113834066795298816), (-2639645602379/77371252455336267181195264)), (6927/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775590892586867/4835703278458516698824704), (-4948609634981/9671406556917033397649408)), (12993/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260212321569875/604462909807314587353088), (-4329307399909/604462909807314587353088)), (5687/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945051625414729/37778931862957161709568), (-7033762875073/75557863725914323419136)), (18491/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649635464039785/2361183241434822606848), (-5274130370951/4722366482869645213696)), (3469/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202978219735135/73786976294838206464), (-7249991968881/590295810358705651712)), (4773/147573952589676412928), by norm_num⟩
  | 8 => ⟨((114152623286087/4611686018427387904), (-2264895726541/18446744073709551616)), (23885/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825988695431999/9223372036854775808), (-10188031755219/9223372036854775808)), (26897/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597229113239773/1152921504606846976), (-10183030272793/1152921504606846976)), (13465/576460752303423488), by norm_num⟩
  | 5 => ⟨((598704759366569/72057594037927936), (-4452260548917/72057594037927936)), (23601/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495862378912103/36028797018963968), (-13345511585759/36028797018963968)), (8869/9007199254740992), by norm_num⟩
  | 3 => ⟨((1494507182187601/9007199254740992), (-16662146075589/9007199254740992)), (11119/2251799813685248), by norm_num⟩
  | 2 => ⟨((559588034294025/1125899906842624), (-16632489562043/2251799813685248)), (44673/2251799813685248), by norm_num⟩
  | 1 => ⟨((1115736599751841/1125899906842624), (-6218612257107/281474976710656)), (67503/1125899906842624), by norm_num⟩
  | 0 => ⟨((1105264965749757/1125899906842624), (-49450899663303/1125899906842624)), (136985/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1105264965749757/1125899906842624), (-49450899663303/1125899906842624)), (522556309226607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((541418133897543/562949953421312), (-24272293918173/281474976710656)), (280983/1125899906842624), by norm_num⟩
  | 2 => ⟨((1033047491833717/1125899906842624), (-46687844980617/281474976710656)), (147233/281474976710656), by norm_num⟩
  | 3 => ⟨((114609548793719/140737488355328), (-342700169798233/1125899906842624)), (638049/562949953421312), by norm_num⟩
  | 4 => ⟨((80293428439521/140737488355328), (-558155645536919/1125899906842624)), (178451/70368744177664), by norm_num⟩
  | 5 => ⟨((89770407100701/1125899906842624), (-1273753877712615/2251799813685248)), (6088811/1125899906842624), by norm_num⟩
  | 6 => ⟨((-706196895194387/2251799813685248), (-406236481425843/4503599627370496)), (3929673/562949953421312), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75151839/67108864), (-2914012561/134217728)), (1/134217728), by norm_num⟩, -3, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-8357620451/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-326469549/268435456), (-6329428379/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-8357620451/4294967296), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((2838241953491/562949953421312), (667237808571287/2251799813685248)), (13170181/2251799813685248), by norm_num⟩
  | 1 => ⟨((-21068435/2147483648), (-1238236259/2147483648)), (99/8589934592), by norm_num⟩
  | 2 => ⟨((81994563/8589934592), (4818993007/8589934592)), (49/4294967296), by norm_num⟩
  | 3 => ⟨((-13296171/2147483648), (-390721975/1073741824)), (129/17179869184), by norm_num⟩
  | 4 => ⟨((12936577/4294967296), (6082478853/34359738368)), (127/34359738368), by norm_num⟩
  | 5 => ⟨((-80554933/68719476736), (-4734382933/68719476736)), (101/68719476736), by norm_num⟩
  | 6 => ⟨((52250887/137438953472), (6141789199/274877906944)), (133/274877906944), by norm_num⟩
  | 7 => ⟨((-116200607/1099511627776), (-6829354249/1099511627776)), (75/549755813888), by norm_num⟩
  | 8 => ⟨((56528985/2199023255552), (830581859/549755813888)), (37/1099511627776), by norm_num⟩
  | 9 => ⟨((-97778067/17592186044416), (-5746622823/17592186044416)), (65/8796093022208), by norm_num⟩
  | 10 => ⟨((76106933/70368744177664), (2236482335/35184372088832)), (103/70368744177664), by norm_num⟩
  | 11 => ⟨((-107707093/562949953421312), (-791271577/70368744177664)), (37/140737488355328), by norm_num⟩
  | 12 => ⟨((69862775/2251799813685248), (8211964759/4503599627370496)), (97/2251799813685248), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791195769417651/5070602400912917605986812821504), (63249248757/316912650057057350374175801344)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890045138690441/316912650057057350374175801344), (2398663743581/633825300114114700748351602688)), (2889/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1891228200290385/39614081257132168796771975168), (2698200134799/39614081257132168796771975168)), (6501/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891095748462047/2475880078570760549798248448), (1433240658885/1237940039285380274899124224)), (13817/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886380761648543/77371252455336267181195264), (716520118517/38685626227668133590597632)), (6909/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775512789912597/4835703278458516698824704), (167907786529/604462909807314587353088)), (12957/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260076314694979/604462909807314587353088), (1175141596213/302231454903657293676544)), (11341/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((59058859394989/2361183241434822606848), (477301483031/9444732965739290427392)), (18433/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81194201141791/295147905179352825856), (2863110452347/4722366482869645213696)), (6915/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623602448002509/590295810358705651712), (3935642061015/590295810358705651712)), (9511/295147905179352825856), by norm_num⟩
  | 8 => ⟨((913082760082017/36893488147419103232), (4917850646135/73786976294838206464)), (5947/18446744073709551616), by norm_num⟩
  | 7 => ⟨((912840687718341/4611686018427387904), (5530242288483/9223372036854775808)), (26775/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798463200115875/576460752303423488), (5527318376691/1152921504606846976)), (13397/576460752303423488), by norm_num⟩
  | 5 => ⟨((598574910950301/72057594037927936), (1208278785085/36028797018963968)), (23465/144115188075855872), by norm_num⟩
  | 4 => ⟨((747741586614035/18014398509481984), (3621549118985/18014398509481984)), (35237/36028797018963968), by norm_num⟩
  | 3 => ⟨((373512809150545/2251799813685248), (4521186445057/4503599627370496)), (44117/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118747149802973/2251799813685248), (4512566941785/1125899906842624)), (691/35184372088832), by norm_num⟩
  | 1 => ⟨((557580279606397/562949953421312), (6747320684111/562949953421312)), (66603/1125899906842624), by norm_num⟩
  | 0 => ⟨((552190428793271/562949953421312), (13408636904865/562949953421312)), (134277/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((552190428793271/562949953421312), (13408636904865/562949953421312)), (512226109031295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1082634348773759/1125899906842624), (6576180455325/140737488355328)), (269819/1125899906842624), by norm_num⟩
  | 2 => ⟨((519286560234099/562949953421312), (50587792406059/562949953421312)), (544117/1125899906842624), by norm_num⟩
  | 3 => ⟨((948927716490445/1125899906842624), (186656455329477/1125899906842624)), (275405/281474976710656), by norm_num⟩
  | 4 => ⟨((384413913504569/562949953421312), (19664657005425/70368744177664)), (4444383/2251799813685248), by norm_num⟩
  | 5 => ⟨((874147601215281/2251799813685248), (53712538468037/140737488355328)), (8553731/2251799813685248), by norm_num⟩
  | 6 => ⟨((2838241953491/562949953421312), (667237808571287/2251799813685248)), (13170181/2251799813685248), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-326469549/268435456), (-6329428379/268435456)), (1/134217728), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-1116391677/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-348872399/268435456), (-6763763637/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((306317461926311/1125899906842624), (-78822039416517/4503599627370496)), (9942251/4503599627370496), by norm_num⟩
  | 1 => ⟨((-4859689753/8589934592), (78156387/2147483648)), (41/8589934592), by norm_num⟩
  | 2 => ⟨((631590047/1073741824), (-81260819/2147483648)), (45/8589934592), by norm_num⟩
  | 3 => ⟨((-3502278883/8589934592), (450605661/17179869184)), (65/17179869184), by norm_num⟩
  | 4 => ⟨((910348025/4294967296), (-468504065/34359738368)), (35/17179869184), by norm_num⟩
  | 5 => ⟨((-3028824801/34359738368), (194845363/34359738368)), (15/17179869184), by norm_num⟩
  | 6 => ⟨((4198842743/137438953472), (-67528257/34359738368)), (43/137438953472), by norm_num⟩
  | 7 => ⟨((-4989284587/549755813888), (320962429/549755813888)), (53/549755813888), by norm_num⟩
  | 8 => ⟨((5187462817/2199023255552), (-41713913/274877906944)), (57/2199023255552), by norm_num⟩
  | 9 => ⟨((-4794233635/8796093022208), (308414733/8796093022208)), (55/8796093022208), by norm_num⟩
  | 10 => ⟨((7975462865/70368744177664), (-256532163/35184372088832)), (95/70368744177664), by norm_num⟩
  | 11 => ⟨((-6030730471/281474976710656), (12123719/8796093022208)), (75/281474976710656), by norm_num⟩
  | 12 => ⟨((4180183823/1125899906842624), (-268912693/1125899906842624)), (27/562949953421312), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582282826618775/10141204801825835211973625643008), (-20920538821/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779964514579615/633825300114114700748351602688), (-99160142225/633825300114114700748351602688)), (11527/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472771728508441/9903520314283042199192993792), (-111542287997/39614081257132168796771975168)), (1621/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890945877775017/2475880078570760549798248448), (-118497965485/2475880078570760549798248448)), (6889/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772611929208125/154742504910672534362390528), (-29620072333/38685626227668133590597632)), (13779/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550885629146811/9671406556917033397649408), (-111056494069/9671406556917033397649408)), (6459/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259954151512821/604462909807314587353088), (-1518057177/9444732965739290427392)), (11303/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944842767915941/37778931862957161709568), (-78921377993/37778931862957161709568)), (18367/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298959225978807/4722366482869645213696), (-118351284287/4722366482869645213696)), (861/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1623399740270351/590295810358705651712), (-81341505357/295147905179352825856)), (9471/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456478326793153/18446744073709551616), (-203278784859/73786976294838206464)), (23677/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825399245531455/9223372036854775808), (-228585584969/9223372036854775808)), (26637/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596646280453273/1152921504606846976), (-114228423083/576460752303423488)), (13319/576460752303423488), by norm_num⟩
  | 5 => ⟨((598453487861887/72057594037927936), (-6242343971/4503599627370496)), (11655/72057594037927936), by norm_num⟩
  | 4 => ⟨((373780853579649/9007199254740992), (-149671644179/18014398509481984)), (17483/18014398509481984), by norm_num⟩
  | 3 => ⟨((1493609415570731/9007199254740992), (-186836760455/4503599627370496)), (21855/4503599627370496), by norm_num⟩
  | 2 => ⟨((2236634228362169/4503599627370496), (-186458117081/1125899906842624)), (21857/1125899906842624), by norm_num⟩
  | 1 => ⟨((2229089721940739/2251799813685248), (-557484970275/1125899906842624)), (131165/2251799813685248), by norm_num⟩
  | 0 => ⟨((275816558288147/281474976710656), (-2214870775397/2251799813685248)), (131213/1125899906842624), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((275816558288147/281474976710656), (-2214870775397/2251799813685248)), (500537876609420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2162172938116603/2251799813685248), (-4340691605783/2251799813685248)), (514819/2251799813685248), by norm_num⟩
  | 2 => ⟨((2076105053525697/2251799813685248), (-1041980493303/281474976710656)), (495321/1125899906842624), by norm_num⟩
  | 3 => ⟨((957043934542021/1125899906842624), (-7685446831195/1125899906842624)), (114627/140737488355328), by norm_num⟩
  | 4 => ⟨((813459545546171/1125899906842624), (-26131311422405/2251799813685248)), (785747/562949953421312), by norm_num⟩
  | 5 => ⟨((146892658232871/281474976710656), (-18879799691791/1125899906842624)), (1153637/562949953421312), by norm_num⟩
  | 6 => ⟨((306317461926311/1125899906842624), (-78822039416517/4503599627370496)), (9942251/4503599627370496), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-348872399/268435456), (-6763763637/268435456)), (1/134217728), by norm_num⟩, -4, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile029Terms0

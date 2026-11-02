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
namespace Reinmann.XiRectangle.Tile016Terms0
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
  | 0 => ⟨((-1116391677/2147483648), (-21644043637/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((107519505763839/562949953421312), (316993845086637/562949953421312)), (731047/1125899906842624), by norm_num⟩
  | 1 => ⟨((-4548757463/34359738368), (-13410851439/34359738368)), (17/34359738368), by norm_num⟩
  | 2 => ⟨((6305916821/137438953472), (1161961733/8589934592)), (25/137438953472), by norm_num⟩
  | 3 => ⟨((-5827904621/549755813888), (-17182090649/549755813888)), (25/549755813888), by norm_num⟩
  | 4 => ⟨((8079191313/4398046511104), (23819435379/4398046511104)), (37/4398046511104), by norm_num⟩
  | 5 => ⟨((-140001717/549755813888), (-13208299581/17592186044416)), (11/8796093022208), by norm_num⟩
  | 6 => ⟨((8280899875/281474976710656), (24414121639/281474976710656)), (43/281474976710656), by norm_num⟩
  | 7 => ⟨((-6559865601/2251799813685248), (-19340090949/2251799813685248)), (9/562949953421312), by norm_num⟩
  | 8 => ⟨((2273476173/9007199254740992), (13405529513/18014398509481984)), (27/18014398509481984), by norm_num⟩
  | 9 => ⟨((-1400758755/72057594037927936), (-16519119975/288230376151711744)), (35/288230376151711744), by norm_num⟩
  | 10 => ⟨((6213964683/4611686018427387904), (9160145149/2305843009213693952)), (41/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-6265006691/73786976294838206464), (-18470774643/73786976294838206464)), (43/73786976294838206464), by norm_num⟩
  | 12 => ⟨((361880977/73786976294838206464), (17070620489/1180591620717411303424)), (41/1180591620717411303424), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791649295455309/5070602400912917605986812821504), (1620173646145/10141204801825835211973625643008)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890583483562489/316912650057057350374175801344), (961155578867/316912650057057350374175801344)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946219721602547/19807040628566084398385987584), (2162496099423/39614081257132168796771975168)), (813/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892382661084371/2475880078570760549798248448), (574382468527/618970019642690137449562112)), (27/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1774048398761843/154742504910672534362390528), (2297392350993/154742504910672534362390528)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1552231986039279/9671406556917033397649408), (2153659200287/9671406556917033397649408)), (405/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261131880537205/604462909807314587353088), (942152829861/302231454903657293676544)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945799360381473/37778931862957161709568), (3061722658575/75557863725914323419136)), (9/590295810358705651712), by norm_num⟩
  | 10 => ⟨((1300393568157653/4722366482869645213696), (287006523163/590295810358705651712)), (865/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101585692056353/36893488147419103232), (3156682018999/590295810358705651712)), (1189/590295810358705651712), by norm_num⟩
  | 8 => ⟨((457094035391591/18446744073709551616), (1972633919135/36893488147419103232)), (1487/73786976294838206464), by norm_num⟩
  | 7 => ⟨((914084052104107/4611686018427387904), (4437622242739/9223372036854775808)), (1673/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599412852588209/1152921504606846976), (1109154237411/288230376151711744)), (1673/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599662577663671/72057594037927936), (485113575375/18014398509481984)), (1465/144115188075855872), by norm_num⟩
  | 4 => ⟨((187343193132081/4503599627370496), (5819099766671/36028797018963968)), (275/4503599627370496), by norm_num⟩
  | 3 => ⟨((749064046943409/4503599627370496), (1817478171417/2251799813685248)), (2753/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122822329953709/2251799813685248), (7263966596025/2251799813685248)), (1379/1125899906842624), by norm_num⟩
  | 1 => ⟨((70079317571813/70368744177664), (10881074008055/1125899906842624)), (2075/562949953421312), by norm_num⟩
  | 0 => ⟨((558290288315285/562949953421312), (10851290381815/562949953421312)), (8353/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((558290288315285/562949953421312), (10851290381815/562949953421312)), (31864170554732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((276730012704197/281474976710656), (43045887109773/1125899906842624)), (16891/1125899906842624), by norm_num⟩
  | 2 => ⟨((135826799863367/140737488355328), (84640482262095/1125899906842624)), (34505/1125899906842624), by norm_num⟩
  | 3 => ⟨((260584185490647/281474976710656), (163374321638123/1125899906842624)), (71791/1125899906842624), by norm_num⟩
  | 4 => ⟨((470634515658859/562949953421312), (302497685809707/1125899906842624)), (153761/1125899906842624), by norm_num⟩
  | 5 => ⟨((352821123160737/562949953421312), (505785109257947/1125899906842624)), (339717/1125899906842624), by norm_num⟩
  | 6 => ⟨((107519505763839/562949953421312), (316993845086637/562949953421312)), (731047/1125899906842624), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1116391677/2147483648), (-21644043637/4294967296)), (1/2147483648), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-55294967/67108864), (-4288124691/536870912)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-262527425267433/4503599627370496), (-1958170293754629/4503599627370496)), (5049981/4503599627370496), by norm_num⟩
  | 1 => ⟨((2200438351/34359738368), (2051610897/4294967296)), (45/34359738368), by norm_num⟩
  | 2 => ⟨((-2417428613/68719476736), (-2253924943/8589934592)), (51/68719476736), by norm_num⟩
  | 3 => ⟨((1770544521/137438953472), (13206344747/137438953472)), (77/274877906944), by norm_num⟩
  | 4 => ⟨((-3890283937/1099511627776), (-14508652627/549755813888)), (11/137438953472), by norm_num⟩
  | 5 => ⟨((213695687/274877906944), (25503014509/4398046511104)), (5/274877906944), by norm_num⟩
  | 6 => ⟨((-1252099775/8796093022208), (-9339308379/8796093022208)), (61/17592186044416), by norm_num⟩
  | 7 => ⟨((3144165027/140737488355328), (11726033089/70368744177664)), (79/140737488355328), by norm_num⟩
  | 8 => ⟨((-107944323/35184372088832), (-25764728097/1125899906842624)), (45/562949953421312), by norm_num⟩
  | 9 => ⟨((3373197077/9007199254740992), (25160397245/9007199254740992)), (45/4503599627370496), by norm_num⟩
  | 10 => ⟨((-2964668609/72057594037927936), (-22113217281/72057594037927936)), (41/36028797018963968), by norm_num⟩
  | 11 => ⟨((2368742811/576460752303423488), (17668256179/576460752303423488)), (17/144115188075855872), by norm_num⟩
  | 12 => ⟨((-3469773281/9223372036854775808), (-25880751143/9223372036854775808)), (51/4611686018427387904), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791451234115199/5070602400912917605986812821504), (-554935146463/2535301200456458802993406410752)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890347682634779/316912650057057350374175801344), (-2632369727509/633825300114114700748351602688)), (723/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945954410565661/19807040628566084398385987584), (-2961190844183/39614081257132168796771975168)), (813/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472954696570443/618970019642690137449562112), (-1572999966041/1237940039285380274899124224)), (27/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((1773484424049331/154742504910672534362390528), (-3145701396165/154742504910672534362390528)), (27/2417851639229258349412352), by norm_num⟩
  | 13 => ⟨((1551703153642041/9671406556917033397649408), (-1474388923917/4835703278458516698824704)), (1621/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630334523070809/302231454903657293676544), (-1289931693523/302231454903657293676544)), (1419/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236355802018705/9444732965739290427392), (-2095841579147/37778931862957161709568)), (1153/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649914582968385/2361183241434822606848), (-3143241839067/4722366482869645213696)), (865/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624594737710527/590295810358705651712), (-4321111593707/590295810358705651712)), (595/147573952589676412928), by norm_num⟩
  | 8 => ⟨((228425662470425/9223372036854775808), (-5400120459807/73786976294838206464)), (93/2305843009213693952), by norm_num⟩
  | 7 => ⟨((456768831611877/2305843009213693952), (-6073390387359/9223372036854775808)), (3349/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199789918733411/144115188075855872), (-189725270627/36028797018963968)), (3353/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1198367526179445/144115188075855872), (-663731587839/18014398509481984)), (367/18014398509481984), by norm_num⟩
  | 4 => ⟨((748653738041269/18014398509481984), (-7959868229295/36028797018963968)), (4409/36028797018963968), by norm_num⟩
  | 3 => ⟨((11690059928589/70368744177664), (-621327433459/562949953421312)), (5521/9007199254740992), by norm_num⟩
  | 2 => ⟨((280254416617081/562949953421312), (-4964169810051/1125899906842624)), (5535/2251799813685248), by norm_num⟩
  | 1 => ⟨((559275768197329/562949953421312), (-1857530563327/140737488355328)), (8339/1125899906842624), by norm_num⟩
  | 0 => ⟨((1111103598488251/1125899906842624), (-7397832623807/281474976710656)), (2103/140737488355328), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1111103598488251/1125899906842624), (-7397832623807/281474976710656)), (8022308886480287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1095724009066379/1125899906842624), (-58404896558711/1125899906842624)), (34091/1125899906842624), by norm_num⟩
  | 2 => ⟨((1063327179287001/1125899906842624), (-113679105962237/1125899906842624)), (69893/1125899906842624), by norm_num⟩
  | 3 => ⟨((992754102105377/1125899906842624), (-3355040775385/17592186044416)), (36533/281474976710656), by norm_num⟩
  | 4 => ⟨((834403575711773/1125899906842624), (-189330108497317/562949953421312)), (313441/1125899906842624), by norm_num⟩
  | 5 => ⟨((245512839936421/562949953421312), (-1122499210169247/2251799813685248)), (337707/562949953421312), by norm_num⟩
  | 6 => ⟨((-262527425267433/4503599627370496), (-1958170293754629/4503599627370496)), (5049981/4503599627370496), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/67108864), (-4288124691/536870912)), (1/1073741824), by norm_num⟩, -1, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-1116391677/1073741824), (-21644043637/2147483648)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-1263695334374555/4503599627370496), (968697735114977/4503599627370496)), (4445433/4503599627370496), by norm_num⟩
  | 1 => ⟨((6682791581/17179869184), (-5122757751/17179869184)), (49/34359738368), by norm_num⟩
  | 2 => ⟨((-18528632571/68719476736), (14203300367/68719476736)), (35/34359738368), by norm_num⟩
  | 3 => ⟨((17124092569/137438953472), (-6563318403/68719476736)), (67/137438953472), by norm_num⟩
  | 4 => ⟨((-2967379121/68719476736), (2274672823/68719476736)), (3/17179869184), by norm_num⟩
  | 5 => ⟨((13163715017/1099511627776), (-5045385773/549755813888)), (55/1099511627776), by norm_num⟩
  | 6 => ⟨((-12165855933/4398046511104), (9325853129/4398046511104)), (53/4398046511104), by norm_num⟩
  | 7 => ⟨((19274808547/35184372088832), (-3693822173/8796093022208)), (43/17592186044416), by norm_num⟩
  | 8 => ⟨((-417508725/4398046511104), (10241449699/140737488355328)), (31/70368744177664), by norm_num⟩
  | 9 => ⟨((8231679875/562949953421312), (-12620145749/1125899906842624)), (79/1125899906842624), by norm_num⟩
  | 10 => ⟨((-9129225115/4503599627370496), (13996189511/9007199254740992)), (45/4503599627370496), by norm_num⟩
  | 11 => ⟨((2301053327/9007199254740992), (-14111155343/72057594037927936)), (93/72057594037927936), by norm_num⟩
  | 12 => ⟨((-17012998677/576460752303423488), (13041476721/576460752303423488)), (11/72057594037927936), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791310707357927/5070602400912917605986812821504), (1620173646145/5070602400912917605986812821504)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780357947981815/633825300114114700748351602688), (3841332221343/633825300114114700748351602688)), (181/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1891529011901993/39614081257132168796771975168), (4321078386551/39614081257132168796771975168)), (1629/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891414968669575/2475880078570760549798248448), (2295328169437/1237940039285380274899124224)), (1731/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773080302452325/154742504910672534362390528), (2295052789963/77371252455336267181195264)), (433/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551323966794377/9671406556917033397649408), (1075659679231/2417851639229258349412352)), (203/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((315084233737345/151115727451828646838272), (3764223519849/604462909807314587353088)), (1421/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890306130717383/75557863725914323419136), (6115765476683/75557863725914323419136)), (1155/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299423423029453/4722366482869645213696), (1146465846185/1180591620717411303424)), (867/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624035982456599/590295810358705651712), (6304000609573/590295810358705651712)), (2385/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826705568607035/73786976294838206464), (1969414449741/18446744073709551616)), (2983/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913143180424223/4611686018427387904), (8859142401403/9223372036854775808)), (3359/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798764088378447/576460752303423488), (8855112554391/1152921504606846976)), (1681/576460752303423488), by norm_num⟩
  | 5 => ⟨((598836384881233/72057594037927936), (7743687755521/144115188075855872)), (1473/72057594037927936), by norm_num⟩
  | 4 => ⟨((748130195164503/18014398509481984), (725403425743/2251799813685248)), (4427/36028797018963968), by norm_num⟩
  | 3 => ⟨((747505084455447/4503599627370496), (14492172058973/9007199254740992)), (5547/9007199254740992), by norm_num⟩
  | 2 => ⟨((279921809205871/562949953421312), (14468303454695/2251799813685248)), (5569/2251799813685248), by norm_num⟩
  | 1 => ⟨((139565463842035/140737488355328), (10821350236709/562949953421312)), (4203/562949953421312), by norm_num⟩
  | 0 => ⟨((276730012704197/281474976710656), (43045887109773/1125899906842624)), (8513/562949953421312), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((276730012704197/281474976710656), (43045887109773/1125899906842624)), (32474519969749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((135826799863367/140737488355328), (84640482262095/1125899906842624)), (34781/1125899906842624), by norm_num⟩
  | 2 => ⟨((260584185490647/281474976710656), (163374321638123/1125899906842624)), (72365/1125899906842624), by norm_num⟩
  | 3 => ⟨((470634515658859/562949953421312), (302497685809707/1125899906842624)), (77495/562949953421312), by norm_num⟩
  | 4 => ⟨((352821123160737/562949953421312), (505785109257947/1125899906842624)), (10701/35184372088832), by norm_num⟩
  | 5 => ⟨((107519505763839/562949953421312), (316993845086637/562949953421312)), (1473779/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1263695334374555/4503599627370496), (968697735114977/4503599627370496)), (4445433/4503599627370496), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1116391677/1073741824), (-21644043637/2147483648)), (1/1073741824), by norm_num⟩, -2, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-162011325/134217728), (-25127956503/2147483648)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((873386723017255/4503599627370496), (128166730775839/562949953421312)), (2472671/4503599627370496), by norm_num⟩
  | 1 => ⟨((-10724347719/34359738368), (-12590112037/34359738368)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((4315042951/17179869184), (10131501817/34359738368)), (27/34359738368), by norm_num⟩
  | 3 => ⟨((-9259724959/68719476736), (-10870682089/68719476736)), (31/68719476736), by norm_num⟩
  | 4 => ⟨((1862869051/34359738368), (1093480493/17179869184)), (13/68719476736), by norm_num⟩
  | 5 => ⟨((-9594150645/549755813888), (-2815822339/137438953472)), (35/549755813888), by norm_num⟩
  | 6 => ⟨((2573531631/549755813888), (1510630409/274877906944)), (39/2199023255552), by norm_num⟩
  | 7 => ⟨((-4733645001/4398046511104), (-2778589545/2199023255552)), (19/4398046511104), by norm_num⟩
  | 8 => ⟨((15237015457/70368744177664), (17887869427/70368744177664)), (63/70368744177664), by norm_num⟩
  | 9 => ⟨((-10899124599/281474976710656), (-12795295657/281474976710656)), (47/281474976710656), by norm_num⟩
  | 10 => ⟨((14033171473/2251799813685248), (16474587145/2251799813685248)), (63/2251799813685248), by norm_num⟩
  | 11 => ⟨((-8212915709/9007199254740992), (-9641754597/9007199254740992)), (19/4503599627370496), by norm_num⟩
  | 12 => ⟨((8812118609/72057594037927936), (5172601797/36028797018963968)), (21/36028797018963968), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582403412673403/10141204801825835211973625643008), (1127089995507/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445026617053727/158456325028528675187087900672), (1335762170393/633825300114114700748351602688)), (361/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1891246538119557/39614081257132168796771975168), (1502570260425/39614081257132168796771975168)), (203/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((945557693321025/1237940039285380274899124224), (798142085407/1237940039285380274899124224)), (863/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772781334923513/154742504910672534362390528), (1596062882351/154742504910672534362390528)), (863/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551044337442255/9671406556917033397649408), (1496073869251/9671406556917033397649408)), (1619/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260092911748979/604462909807314587353088), (1308829593179/604462909807314587353088)), (1417/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944955407973497/37778931862957161709568), (2126407470521/75557863725914323419136)), (2301/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649564003270409/2361183241434822606848), (199302518489/590295810358705651712)), (863/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405907880494197/147573952589676412928), (2191701500481/590295810358705651712)), (1187/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826202597237251/73786976294838206464), (2738687853715/73786976294838206464)), (371/9223372036854775808), by norm_num⟩
  | 7 => ⟨((456431024085407/2305843009213693952), (1539866569613/4611686018427387904)), (3339/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596970381307095/1152921504606846976), (1539060228555/576460752303423488)), (3341/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197189721210217/144115188075855872), (2691542078463/144115188075855872)), (2925/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495545849375431/36028797018963968), (1008422209601/9007199254740992)), (2195/18014398509481984), by norm_num⟩
  | 3 => ⟨((1494134519117517/9007199254740992), (629471734375/1125899906842624)), (1373/2251799813685248), by norm_num⟩
  | 2 => ⟨((1118837817858219/2251799813685248), (5026278740441/2251799813685248)), (5499/2251799813685248), by norm_num⟩
  | 1 => ⟨((2230629907284233/2251799813685248), (7515717432043/1125899906842624)), (8267/1125899906842624), by norm_num⟩
  | 0 => ⟨((1104762787574943/1125899906842624), (14936854860019/1125899906842624)), (33215/2251799813685248), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1104762787574943/1125899906842624), (14936854860019/1125899906842624)), (126705178267668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2167648651111963/2251799813685248), (29312874639155/1125899906842624)), (66065/2251799813685248), by norm_num⟩
  | 2 => ⟨((130319746554893/140737488355328), (112869736973271/2251799813685248)), (130633/2251799813685248), by norm_num⟩
  | 3 => ⟨((120319557818695/140737488355328), (209029672022241/2251799813685248)), (255023/2251799813685248), by norm_num⟩
  | 4 => ⟨((406604346925073/562949953421312), (357408079433737/2251799813685248)), (483397/2251799813685248), by norm_num⟩
  | 5 => ⟨((558995734982599/1125899906842624), (258146710628003/1125899906842624)), (425871/1125899906842624), by norm_num⟩
  | 6 => ⟨((873386723017255/4503599627370496), (128166730775839/562949953421312)), (2472671/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-162011325/134217728), (-25127956503/2147483648)), (1/1073741824), by norm_num⟩, -2, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-2885830621/2147483648), (-27974520583/2147483648)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((1052493402065673/4503599627370496), (-260912252070335/2251799813685248)), (103909/281474976710656), by norm_num⟩
  | 1 => ⟨((-14387626797/34359738368), (3566680895/17179869184)), (25/34359738368), by norm_num⟩
  | 2 => ⟨((12889583277/34359738368), (-6390634267/34359738368)), (3/4294967296), by norm_num⟩
  | 3 => ⟨((-7698344297/34359738368), (7633652975/68719476736)), (15/34359738368), by norm_num⟩
  | 4 => ⟨((3448395323/34359738368), (-6838835001/137438953472)), (29/137438953472), by norm_num⟩
  | 5 => ⟨((-4942955979/137438953472), (9802837897/549755813888)), (43/549755813888), by norm_num⟩
  | 6 => ⟨((5904392121/549755813888), (-1463693969/274877906944)), (27/1099511627776), by norm_num⟩
  | 7 => ⟨((-1511321499/549755813888), (5994485781/4398046511104)), (29/4398046511104), by norm_num⟩
  | 8 => ⟨((21663396855/35184372088832), (-10740676661/35184372088832)), (27/17592186044416), by norm_num⟩
  | 9 => ⟨((-17251376201/140737488355328), (4276602025/70368744177664)), (45/140737488355328), by norm_num⟩
  | 10 => ⟨((6182063333/281474976710656), (-1532528435/140737488355328)), (17/281474976710656), by norm_num⟩
  | 11 => ⟨((-8055833103/2251799813685248), (7988137703/4503599627370496)), (23/2251799813685248), by norm_num⟩
  | 12 => ⟨((19245486993/36028797018963968), (-4770940457/18014398509481984)), (57/36028797018963968), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646017817/5070602400912917605986812821504), (-599566940011/10141204801825835211973625643008)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444974019134335/158456325028528675187087900672), (-710412089297/633825300114114700748351602688)), (1443/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236376239344605/4951760157141521099596496896), (-99889777973/4951760157141521099596496896)), (1623/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945432028773165/1237940039285380274899124224), (-848946685575/2475880078570760549798248448)), (1725/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886265049714151/77371252455336267181195264), (-106101966591/19342813113834066795298816)), (1725/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550808903587081/9671406556917033397649408), (-795625639529/9671406556917033397649408)), (1617/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629943503257357/302231454903657293676544), (-696033355619/604462909807314587353088)), (1415/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889576406226513/75557863725914323419136), (-565396747765/37778931862957161709568)), (2299/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298877362180831/4722366482869645213696), (-847867068415/4722366482869645213696)), (1725/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811643575307005/295147905179352825856), (-1165446755713/590295810358705651712)), (2371/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912886264877643/36893488147419103232), (-1456252965031/73786976294838206464)), (2965/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825240815548127/9223372036854775808), (-1637521151115/9223372036854775808)), (3335/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798243890683003/576460752303423488), (-1636567382553/1152921504606846976)), (417/144115188075855872), by norm_num⟩
  | 5 => ⟨((299192052865485/36028797018963968), (-1430924191031/144115188075855872)), (365/18014398509481984), by norm_num⟩
  | 4 => ⟨((1494915113257957/36028797018963968), (-536060887551/9007199254740992)), (4381/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493348769593945/9007199254740992), (-334569837259/1125899906842624)), (2739/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118056065759511/2251799813685248), (-667737044427/562949953421312)), (2741/1125899906842624), by norm_num⟩
  | 1 => ⟨((2228304578638529/2251799813685248), (-7984848477455/2251799813685248)), (1029/140737488355328), by norm_num⟩
  | 0 => ⟨((551238568096693/562949953421312), (-15858051386159/2251799813685248)), (33007/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((551238568096693/562949953421312), (-15858051386159/2251799813685248)), (125911721236418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2158971608389365/2251799813685248), (-485254588673/35184372088832)), (65107/2251799813685248), by norm_num⟩
  | 2 => ⟨((517385458082501/562949953421312), (-59552057779551/2251799813685248)), (126643/2251799813685248), by norm_num⟩
  | 3 => ⟨((1900460654703751/2251799813685248), (-109463971021841/2251799813685248)), (239485/2251799813685248), by norm_num⟩
  | 4 => ⟨((1598618277365355/2251799813685248), (-184769506392471/2251799813685248)), (427523/2251799813685248), by norm_num⟩
  | 5 => ⟨((559872287694065/1125899906842624), (-262346508977965/2251799813685248)), (677183/2251799813685248), by norm_num⟩
  | 6 => ⟨((1052493402065673/4503599627370496), (-260912252070335/2251799813685248)), (103909/281474976710656), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2885830621/2147483648), (-27974520583/2147483648)), (1/1073741824), by norm_num⟩, -2, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-3134107669/2147483648), (-15190628109/1073741824)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-21364699005117/9007199254740992), (-2092876553639033/9007199254740992)), (2612917/4503599627370496), by norm_num⟩
  | 1 => ⟨((317182805/68719476736), (7767772153/17179869184)), (5/4294967296), by norm_num⟩
  | 2 => ⟨((-77151155/17179869184), (-30230773337/68719476736)), (5/4294967296), by norm_num⟩
  | 3 => ⟨((200172287/68719476736), (9804394775/34359738368)), (27/34359738368), by norm_num⟩
  | 4 => ⟨((-97379321/68719476736), (-9539235649/68719476736)), (27/68719476736), by norm_num⟩
  | 5 => ⟨((151593127/274877906944), (14849996371/274877906944)), (43/274877906944), by norm_num⟩
  | 6 => ⟨((-24582217/137438953472), (-2408063221/137438953472)), (57/1099511627776), by norm_num⟩
  | 7 => ⟨((218673305/4398046511104), (21421141309/4398046511104)), (65/4398046511104), by norm_num⟩
  | 8 => ⟨((-106379651/8796093022208), (-20841808139/17592186044416)), (65/17592186044416), by norm_num⟩
  | 9 => ⟨((46001165/17592186044416), (2253126999/8796093022208)), (29/35184372088832), by norm_num⟩
  | 10 => ⟨((-71611307/140737488355328), (-28060049245/562949953421312)), (23/140737488355328), by norm_num⟩
  | 11 => ⟨((50672425/562949953421312), (19855394403/2251799813685248)), (67/2251799813685248), by norm_num⟩
  | 12 => ⟨((-262943963/18014398509481984), (-25757875655/18014398509481984)), (11/2251799813685248), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693182135/10141204801825835211973625643008), (-514858644173/2535301200456458802993406410752)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889857371254473/316912650057057350374175801344), (-609927058909/158456325028528675187087900672)), (723/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890805769544047/39614081257132168796771975168), (-2744312510409/39614081257132168796771975168)), (813/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118165435581343/154742504910672534362390528), (-2915397313397/2475880078570760549798248448)), (27/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((1772312804349229/154742504910672534362390528), (-1457454149569/77371252455336267181195264)), (1729/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387651242449213/2417851639229258349412352), (-2732207023809/9671406556917033397649408)), (1621/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259708344915899/604462909807314587353088), (-1195080859529/302231454903657293676544)), (709/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889285669762781/75557863725914323419136), (-3883039037979/75557863725914323419136)), (2305/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40583092192047/147573952589676412928), (-1455713706079/2361183241434822606848)), (865/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811493125027823/295147905179352825856), (-500228590901/73786976294838206464)), (2379/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456348882221619/18446744073709551616), (-5000210519287/73786976294838206464)), (2975/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824815487581183/9223372036854775808), (-2811192039323/4611686018427387904)), (837/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1596060952966269/1152921504606846976), (-5618819492395/1152921504606846976)), (1675/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196393051447327/144115188075855872), (-614057345521/18014398509481984)), (1467/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494349009954361/36028797018963968), (-920084529197/4503599627370496)), (2203/18014398509481984), by norm_num⟩
  | 3 => ⟨((373158817639995/2251799813685248), (-1148354369581/1125899906842624)), (5517/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117333793496925/2251799813685248), (-2291460121107/562949953421312)), (2765/1125899906842624), by norm_num⟩
  | 1 => ⟨((278261764583115/281474976710656), (-13696348185199/1125899906842624)), (8329/1125899906842624), by norm_num⟩
  | 0 => ⟨((550090022482195/562949953421312), (-13591744144035/562949953421312)), (16793/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((550090022482195/562949953421312), (-13591744144035/562949953421312)), (64060215476607921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1074391410773447/1125899906842624), (-53125026807979/1125899906842624)), (33631/1125899906842624), by norm_num⟩
  | 2 => ⟨((2045465370540017/2251799813685248), (-202778496215223/2251799813685248)), (67359/1125899906842624), by norm_num⟩
  | 3 => ⟨((1839776981227771/2251799813685248), (-368395440285257/2251799813685248)), (67253/562949953421312), by norm_num⟩
  | 4 => ⟨((1442874326788069/2251799813685248), (-601976647219691/2251799813685248)), (527601/2251799813685248), by norm_num⟩
  | 5 => ⟨((763616032231635/2251799813685248), (-192862759007373/562949953421312)), (479113/1125899906842624), by norm_num⟩
  | 6 => ⟨((-21364699005117/9007199254740992), (-2092876553639033/9007199254740992)), (2612917/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3134107669/2147483648), (-15190628109/1073741824)), (1/1073741824), by norm_num⟩, -2, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-1674587515/1073741824), (-16233032727/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-196706259089321/1125899906842624), (-131641249809679/1125899906842624)), (2656023/2251799813685248), by norm_num⟩
  | 1 => ⟨((12482884725/34359738368), (4176945243/17179869184)), (43/17179869184), by norm_num⟩
  | 2 => ⟨((-12978714529/34359738368), (-542857091/2147483648)), (23/8589934592), by norm_num⟩
  | 3 => ⟨((8996159383/34359738368), (6020477793/34359738368)), (65/34359738368), by norm_num⟩
  | 4 => ⟨((-18706987537/137438953472), (-1564903953/17179869184)), (69/68719476736), by norm_num⟩
  | 5 => ⟨((7780017401/137438953472), (2603301031/68719476736)), (117/274877906944), by norm_num⟩
  | 6 => ⟨((-2696348563/137438953472), (-7217883079/549755813888)), (83/549755813888), by norm_num⟩
  | 7 => ⟨((12815769629/2199023255552), (8576666239/2199023255552)), (101/2199023255552), by norm_num⟩
  | 8 => ⟨((-6662410939/4398046511104), (-8917338033/8796093022208)), (107/8796093022208), by norm_num⟩
  | 9 => ⟨((769671893/2199023255552), (515085643/2199023255552)), (101/35184372088832), by norm_num⟩
  | 10 => ⟨((-5121560665/70368744177664), (-6854979095/140737488355328)), (171/281474976710656), by norm_num⟩
  | 11 => ⟨((15490888735/1125899906842624), (10366929671/1125899906842624)), (33/281474976710656), by norm_num⟩
  | 12 => ⟨((-10737465851/4503599627370496), (-7185808073/4503599627370496)), (47/2251799813685248), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49435757453803/316912650057057350374175801344), (-3324029444541/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889777554179255/316912650057057350374175801344), (-3937159782417/633825300114114700748351602688)), (1447/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945312954787171/19807040628566084398385987584), (-4428674420079/39614081257132168796771975168)), (3257/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890455520721759/2475880078570760549798248448), (-2352357741397/1237940039285380274899124224)), (3461/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221515120649887/19342813113834066795298816), (-1175967613377/38685626227668133590597632)), (1731/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550424705829045/9671406556917033397649408), (-4408980731697/9671406556917033397649408)), (3247/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157443774927861/75557863725914323419136), (-3856960349923/604462909807314587353088)), (1421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((29516061041039/1180591620717411303424), (-6265877271893/75557863725914323419136)), (1155/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298464948688865/4722366482869645213696), (-4697935129687/4722366482869645213696)), (3467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622718395477087/590295810358705651712), (-6457267577853/590295810358705651712)), (2385/295147905179352825856), by norm_num⟩
  | 8 => ⟨((57033095577969/2305843009213693952), (-8067994834753/73786976294838206464)), (2983/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824434689413205/9223372036854775808), (-4535779382953/4611686018427387904)), (3359/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199459665338161/144115188075855872), (-9065389983839/1152921504606846976)), (6725/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598027097269429/72057594037927936), (-7925277046175/144115188075855872)), (5893/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493834377909287/36028797018963968), (-5937019467921/18014398509481984)), (1107/4503599627370496), by norm_num⟩
  | 3 => ⟨((372995226421597/2251799813685248), (-3704567136559/2251799813685248)), (11099/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116662880092939/2251799813685248), (-14781856471787/2251799813685248)), (11143/2251799813685248), by norm_num⟩
  | 1 => ⟨((555999769785737/562949953421312), (-22081783542995/1125899906842624)), (2103/140737488355328), by norm_num⟩
  | 0 => ⟨((1097921746734775/1125899906842624), (-21899870803417/562949953421312)), (4261/140737488355328), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1097921746734775/1125899906842624), (-21899870803417/562949953421312)), (16254425585699037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1068934935755829/1125899906842624), (-85422671268111/1125899906842624)), (69135/1125899906842624), by norm_num⟩
  | 2 => ⟨((126046380456739/140737488355328), (-162201412521891/1125899906842624)), (70883/562949953421312), by norm_num⟩
  | 3 => ⟨((879743267972429/1125899906842624), (-290539517114819/1125899906842624)), (294783/1125899906842624), by norm_num⟩
  | 4 => ⟨((1224860224868779/2251799813685248), (-908074270930549/2251799813685248)), (612807/1125899906842624), by norm_num⟩
  | 5 => ⟨((300063835529739/2251799813685248), (-123486116408949/281474976710656)), (580459/562949953421312), by norm_num⟩
  | 6 => ⟨((-196706259089321/1125899906842624), (-131641249809679/1125899906842624)), (2656023/2251799813685248), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1674587515/1073741824), (-16233032727/1073741824)), (1/536870912), by norm_num⟩, -2, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile016Terms0

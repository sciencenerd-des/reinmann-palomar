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
namespace Reinmann.XiRectangle.Tile028Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨28,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (7473/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (7473/640))
  have he : value ((7/8), (7473/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-325614239/536870912), (-2172602865/268435456)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((-72842138032849/562949953421312), (-1192729424701565/2251799813685248)), (12820349/2251799813685248), by norm_num⟩
  | 1 => ⟨((1540842365/17179869184), (1576875759/4294967296)), (35/8589934592), by norm_num⟩
  | 2 => ⟨((-1068030541/34359738368), (-2186013973/17179869184)), (25/17179869184), by norm_num⟩
  | 3 => ⟨((987069811/137438953472), (252538237/8589934592)), (3/8589934592), by norm_num⟩
  | 4 => ⟨((-1368369313/1099511627776), (-5601477343/1099511627776)), (17/274877906944), by norm_num⟩
  | 5 => ⟨((758785065/4398046511104), (1553059291/2199023255552)), (77/8796093022208), by norm_num⟩
  | 6 => ⟨((-1402532609/70368744177664), (-2870663117/35184372088832)), (73/70368744177664), by norm_num⟩
  | 7 => ⟨((1111041741/562949953421312), (4548096105/562949953421312)), (15/140737488355328), by norm_num⟩
  | 8 => ⟨((-1540230901/9007199254740992), (-6304999985/9007199254740992)), (43/4503599627370496), by norm_num⟩
  | 9 => ⟨((948983739/72057594037927936), (485588107/9007199254740992)), (55/72057594037927936), by norm_num⟩
  | 10 => ⟨((-1052456645/1152921504606846976), (-4308275549/1152921504606846976)), (63/1152921504606846976), by norm_num⟩
  | 11 => ⟨((1061101609/18446744073709551616), (4343664073/18446744073709551616)), (65/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-490333059/147573952589676412928), (-501799751/36893488147419103232)), (31/147573952589676412928), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791592864105897/5070602400912917605986812821504), (-589559124391/2535301200456458802993406410752)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1781030865470783/633825300114114700748351602688), (-2797612326489/633825300114114700748351602688)), (5781/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892286203327577/39614081257132168796771975168), (-786783595851/9903520314283042199192993792)), (813/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1892219690090393/2475880078570760549798248448), (-3343622355569/2475880078570760549798248448)), (27/9671406556917033397649408), by norm_num⟩
  | 14 => ⟨((1773885254970177/154742504910672534362390528), (-1671694192595/77371252455336267181195264)), (3457/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((194009856897143/1208925819614629174706176), (-195886123287/604462909807314587353088)), (6483/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39406178360015/18889465931478580854784), (-2742157036897/604462909807314587353088)), (2837/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945690172810465/37778931862957161709568), (-4455538785389/75557863725914323419136)), (9223/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1300229485905881/4722366482869645213696), (-1670622941007/2361183241434822606848)), (865/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1625144971030419/590295810358705651712), (-4593549550093/590295810358705651712)), (4759/295147905179352825856), by norm_num⟩
  | 8 => ⟨((457023195344851/18446744073709551616), (-5740941279161/73786976294838206464)), (93/576460752303423488), by norm_num⟩
  | 7 => ⟨((1827848316843419/9223372036854775808), (-3228594668629/4611686018427387904)), (1675/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1599091807047711/1152921504606846976), (-1613869119681/288230376151711744)), (6705/576460752303423488), by norm_num⟩
  | 5 => ⟨((599521413043637/72057594037927936), (-5646613777015/144115188075855872)), (5873/72057594037927936), by norm_num⟩
  | 4 => ⟨((1498319225052269/36028797018963968), (-8466061445861/36028797018963968)), (17643/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497590254071995/9007199254740992), (-10575816578429/9007199254740992)), (11047/4503599627370496), by norm_num⟩
  | 2 => ⟨((280569273079755/562949953421312), (-10565663074443/2251799813685248)), (5539/562949953421312), by norm_num⟩
  | 1 => ⟨((1120432771812201/1125899906842624), (-15823064916991/1125899906842624)), (33389/1125899906842624), by norm_num⟩
  | 0 => ⟨((1114834396688439/1125899906842624), (-31544136467143/1125899906842624)), (67401/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114834396688439/1125899906842624), (-31544136467143/1125899906842624)), (257114414695357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1102993873564467/1125899906842624), (-31234116046801/562949953421312)), (137255/1125899906842624), by norm_num⟩
  | 2 => ⟨((538543967243331/562949953421312), (-30598669061475/281474976710656)), (284157/1125899906842624), by norm_num⟩
  | 3 => ⟨((508543412644349/562949953421312), (-117088409217079/562949953421312)), (605457/1125899906842624), by norm_num⟩
  | 4 => ⟨((870083407885767/1125899906842624), (-52886174732293/140737488355328)), (84109/70368744177664), by norm_num⟩
  | 5 => ⟨((128350774030833/281474976710656), (-326958962241375/562949953421312)), (1545679/562949953421312), by norm_num⟩
  | 6 => ⟨((-72842138032849/562949953421312), (-1192729424701565/2251799813685248)), (12820349/2251799813685248), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-325614239/536870912), (-2172602865/268435456)), (1/268435456), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-516086359/536870912), (-1721747035/134217728)), (3/536870912), by norm_num⟩
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
  | 0 => ⟨((1663567703197247/4503599627370496), (-222737678283893/2251799813685248)), (12423847/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1742950365/4294967296), (933465387/8589934592)), (7/2147483648), by norm_num⟩
  | 2 => ⟨((3829653379/17179869184), (-1025516545/17179869184)), (33/17179869184), by norm_num⟩
  | 3 => ⟨((-2804869509/34359738368), (751096719/34359738368)), (51/68719476736), by norm_num⟩
  | 4 => ⟨((3081464111/137438953472), (-1650328171/274877906944)), (59/274877906944), by norm_num⟩
  | 5 => ⟨((-5416534943/1099511627776), (1450456647/1099511627776)), (27/549755813888), by norm_num⟩
  | 6 => ⟨((3967114567/4398046511104), (-1062326331/4398046511104)), (41/4398046511104), by norm_num⟩
  | 7 => ⟨((-4980938073/35184372088832), (333452789/8796093022208)), (27/17592186044416), by norm_num⟩
  | 8 => ⟨((171003743/8796093022208), (-1465341327/281474976710656)), (31/140737488355328), by norm_num⟩
  | 9 => ⟨((-5343767139/2251799813685248), (1430970657/2251799813685248)), (63/2251799813685248), by norm_num⟩
  | 10 => ⟨((2348291299/9007199254740992), (-1257665559/18014398509481984)), (29/9007199254740992), by norm_num⟩
  | 11 => ⟨((-1876263039/72057594037927936), (1004863155/144115188075855872)), (3/9007199254740992), by norm_num⟩
  | 12 => ⟨((1374190421/576460752303423488), (-735970007/1152921504606846976)), (9/288230376151711744), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582723585083759/10141204801825835211973625643008), (-340821092497/10141204801825835211973625643008)), (455/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((111280428765741/39614081257132168796771975168), (-404085151909/633825300114114700748351602688)), (1081/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1891674488826053/39614081257132168796771975168), (-56819585155/4951760157141521099596496896)), (4865/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891570097918951/2475880078570760549798248448), (-482919090385/2475880078570760549798248448)), (5169/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773236061537177/154742504910672534362390528), (-241432895935/77371252455336267181195264)), (5169/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387867664979767/2417851639229258349412352), (-452630058333/9671406556917033397649408)), (9693/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260465960171535/604462909807314587353088), (-395994688639/604462909807314587353088)), (8481/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118157315629217/4722366482869645213696), (-321692620105/37778931862957161709568)), (6891/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649791354357925/2361183241434822606848), (-241223043427/2361183241434822606848)), (5169/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624256780583361/590295810358705651712), (-331606267731/295147905179352825856)), (14215/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913492117511041/36893488147419103232), (-828789482079/73786976294838206464)), (17769/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826603527334549/9223372036854775808), (-932077263343/9223372036854775808)), (2499/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1597849922547873/1152921504606846976), (-58230549281/72057594037927936)), (19995/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197959443332431/144115188075855872), (-407395434485/72057594037927936)), (8749/72057594037927936), by norm_num⟩
  | 4 => ⟨((748350339201223/18014398509481984), (-152664149293/4503599627370496)), (26251/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495578482865477/9007199254740992), (-1525114750067/9007199254740992)), (32823/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120282417287447/2251799813685248), (-1522827030039/2251799813685248)), (8209/562949953421312), by norm_num⟩
  | 1 => ⟨((2234966845458793/2251799813685248), (-4557059232773/2251799813685248)), (98575/2251799813685248), by norm_num⟩
  | 0 => ⟨((2218211780614019/2251799813685248), (-9068531356597/2251799813685248)), (197421/2251799813685248), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((2218211780614019/2251799813685248), (-9068531356597/2251799813685248)), (753101357466887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2185088228309807/2251799813685248), (-4466632194793/562949953421312)), (24409/140737488355328), by norm_num⟩
  | 2 => ⟨((2120211274391203/2251799813685248), (-34674433738615/2251799813685248)), (382073/1125899906842624), by norm_num⟩
  | 3 => ⟨((1995778445485141/2251799813685248), (-65296324210477/2251799813685248)), (731259/1125899906842624), by norm_num⟩
  | 4 => ⟨((441743085833633/562949953421312), (-115744743948091/2251799813685248)), (1338645/1125899906842624), by norm_num⟩
  | 5 => ⟨((1380582055946497/2251799813685248), (-45412065539677/562949953421312)), (4476935/2251799813685248), by norm_num⟩
  | 6 => ⟨((1663567703197247/4503599627370496), (-222737678283893/2251799813685248)), (12423847/4503599627370496), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-516086359/536870912), (-1721747035/134217728)), (3/536870912), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-325614239/268435456), (-2172602865/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-594061620952229/2251799813685248), (617326359914867/4503599627370496)), (7398235/1125899906842624), by norm_num⟩
  | 1 => ⟨((3141572095/8589934592), (-1632301429/8589934592)), (5/536870912), by norm_num⟩
  | 2 => ⟨((-4355143681/17179869184), (2262850267/17179869184)), (113/17179869184), by norm_num⟩
  | 3 => ⟨((2012503709/17179869184), (-1045658855/17179869184)), (53/17179869184), by norm_num⟩
  | 4 => ⟨((-5579845087/137438953472), (2899181949/137438953472)), (149/137438953472), by norm_num⟩
  | 5 => ⟨((386765389/34359738368), (-1607647835/274877906944)), (21/68719476736), by norm_num⟩
  | 6 => ⟨((-2859576949/1099511627776), (742891043/549755813888)), (5/68719476736), by norm_num⟩
  | 7 => ⟨((2265265943/4398046511104), (-588494665/2199023255552)), (129/8796093022208), by norm_num⟩
  | 8 => ⟨((-3140325403/35184372088832), (1631653671/35184372088832)), (23/8796093022208), by norm_num⟩
  | 9 => ⟨((241856411/17592186044416), (-502656063/70368744177664)), (115/281474976710656), by norm_num⟩
  | 10 => ⟨((-4291637489/2251799813685248), (1114926825/1125899906842624)), (65/1125899906842624), by norm_num⟩
  | 11 => ⟨((2163444673/9007199254740992), (-281021231/2251799813685248)), (133/18014398509481984), by norm_num⟩
  | 12 => ⟨((-999723717/36028797018963968), (1038875061/72057594037927936)), (125/144115188075855872), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582395689318205/10141204801825835211973625643008), (3468077388759/10141204801825835211973625643008)), (9707/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780089250334245/633825300114114700748351602688), (513765685609/79228162514264337593543950336)), (1447/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1891226693747839/39614081257132168796771975168), (2311684399901/19807040628566084398385987584)), (13027/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891093708376443/2475880078570760549798248448), (4911718520221/2475880078570760549798248448)), (3461/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886379494532699/77371252455336267181195264), (4911031185195/154742504910672534362390528)), (13849/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551022679148973/9671406556917033397649408), (1150840340693/2417851639229258349412352)), (12987/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260073251989789/604462909807314587353088), (503401341151/75557863725914323419136)), (11369/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889877540562023/75557863725914323419136), (6542847625763/75557863725914323419136)), (9241/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649550944197541/2361183241434822606848), (2452968472973/2361183241434822606848)), (13869/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((25368651923517/9223372036854775808), (3371857468903/295147905179352825856)), (9541/295147905179352825856), by norm_num⟩
  | 8 => ⟨((57067266284317/2305843009213693952), (8426720506177/73786976294838206464)), (11935/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456415969047093/2305843009213693952), (2369010052107/2305843009213693952)), (13439/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399226327652019/288230376151711744), (9471013250431/1152921504606846976)), (26909/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197127334462205/144115188075855872), (4140739601193/72057594037927936)), (23581/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495441386922347/36028797018963968), (12410898883341/36028797018963968)), (2215/2251799813685248), by norm_num⟩
  | 3 => ⟨((746992468104519/4503599627370496), (15493802249881/9007199254740992)), (22211/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118659806144449/2251799813685248), (15464047390097/2251799813685248)), (44605/2251799813685248), by norm_num⟩
  | 1 => ⟨((557488569292499/562949953421312), (23121604753041/1125899906842624)), (33683/562949953421312), by norm_num⟩
  | 0 => ⟨((275951403513905/281474976710656), (45944874806047/1125899906842624)), (136573/1125899906842624), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((275951403513905/281474976710656), (45944874806047/1125899906842624)), (520984653953170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((540135004323155/562949953421312), (90086535116991/1125899906842624)), (278933/1125899906842624), by norm_num⟩
  | 2 => ⟨((128660161166229/140737488355328), (43217776943715/281474976710656)), (289947/562949953421312), by norm_num⟩
  | 3 => ⟨((914411260187697/1125899906842624), (316072495640157/1125899906842624)), (19349/17592186044416), by norm_num⟩
  | 4 => ⟨((326958962241377/562949953421312), (513403096123331/1125899906842624)), (2706729/1125899906842624), by norm_num⟩
  | 5 => ⟨((291368552131407/2251799813685248), (596364712350785/1125899906842624)), (701577/140737488355328), by norm_num⟩
  | 6 => ⟨((-594061620952229/2251799813685248), (617326359914867/4503599627370496)), (7398235/1125899906842624), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-325614239/268435456), (-2172602865/134217728)), (1/134217728), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-378026425/268435456), (-5044627631/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((274915204833395/1125899906842624), (15646767027537/1125899906842624)), (4435547/2251799813685248), by norm_num⟩
  | 1 => ⟨((-3375693919/8589934592), (-384254457/17179869184)), (57/17179869184), by norm_num⟩
  | 2 => ⟨((2716484887/8589934592), (154608423/8589934592)), (3/1073741824), by norm_num⟩
  | 3 => ⟨((-728668961/4294967296), (-331776877/34359738368)), (53/34359738368), by norm_num⟩
  | 4 => ⟨((2345494903/34359738368), (133493571/34359738368)), (11/17179869184), by norm_num⟩
  | 5 => ⟨((-6039885473/274877906944), (-343759383/274877906944)), (59/274877906944), by norm_num⟩
  | 6 => ⟨((6480547111/1099511627776), (368839589/1099511627776)), (65/1099511627776), by norm_num⟩
  | 7 => ⟨((-5960021837/4398046511104), (-339213953/4398046511104)), (31/2199023255552), by norm_num⟩
  | 8 => ⟨((599517819/2199023255552), (136485949/8796093022208)), (13/4398046511104), by norm_num⟩
  | 9 => ⟨((-857677073/17592186044416), (-195258365/70368744177664)), (77/140737488355328), by norm_num⟩
  | 10 => ⟨((4417209593/562949953421312), (62851243/140737488355328)), (51/562949953421312), by norm_num⟩
  | 11 => ⟨((-2585172577/2251799813685248), (-294269595/4503599627370496)), (61/4503599627370496), by norm_num⟩
  | 12 => ⟨((5547566341/36028797018963968), (315739095/36028797018963968)), (67/36028797018963968), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582141353601407/10141204801825835211973625643008), (74058094551/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779796890626867/633825300114114700748351602688), (685471017/4951760157141521099596496896)), (11527/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945449179897481/19807040628566084398385987584), (98695515353/39614081257132168796771975168)), (1621/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890745566655411/2475880078570760549798248448), (104848918645/2475880078570760549798248448)), (6889/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772411649310473/154742504910672534362390528), (52415986465/77371252455336267181195264)), (6889/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550697899909205/9671406556917033397649408), (24565493419/2417851639229258349412352)), (12917/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157473740198577/75557863725914323419136), (85961230383/604462909807314587353088)), (11303/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889418724361159/75557863725914323419136), (34913316261/18889465931478580854784)), (18367/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298759171745917/4722366482869645213696), (52355220255/2361183241434822606848)), (861/295147905179352825856), by norm_num⟩
  | 9 => ⟨((25361324281575/9223372036854775808), (143928922119/590295810358705651712)), (18941/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912784853393881/36893488147419103232), (22479910331/9223372036854775808)), (23677/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825012877098167/9223372036854775808), (202220421059/9223372036854775808)), (26637/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596260139388271/1152921504606846976), (6315532191/36028797018963968)), (26637/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1168524763575/140737488355328), (22087023519/18014398509481984)), (23309/144115188075855872), by norm_num⟩
  | 4 => ⟨((373654374587809/9007199254740992), (264767109679/36028797018963968)), (34965/36028797018963968), by norm_num⟩
  | 3 => ⟨((373244478360207/2251799813685248), (165237202867/4503599627370496)), (10927/2251799813685248), by norm_num⟩
  | 2 => ⟨((1117686949271249/2251799813685248), (659497646961/4503599627370496)), (683/35184372088832), by norm_num⟩
  | 1 => ⟨((2227205899165803/2251799813685248), (246406631307/562949953421312)), (32789/562949953421312), by norm_num⟩
  | 0 => ⟨((2202791423869801/2251799813685248), (489205241495/562949953421312)), (262399/2251799813685248), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2202791423869801/2251799813685248), (489205241495/562949953421312)), (1000972756392668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2154847956926021/2251799813685248), (1914232524451/1125899906842624)), (256917/1125899906842624), by norm_num⟩
  | 2 => ⟨((2062063879792405/2251799813685248), (3663629439283/1125899906842624)), (492585/1125899906842624), by norm_num⟩
  | 3 => ⟨((1888291192574091/2251799813685248), (13419732766255/2251799813685248)), (452683/562949953421312), by norm_num⟩
  | 4 => ⟨((395845971415439/562949953421312), (11253381866013/1125899906842624)), (1529217/1125899906842624), by norm_num⟩
  | 5 => ⟨((556576557055795/1125899906842624), (31651878461935/2251799813685248)), (4362299/2251799813685248), by norm_num⟩
  | 6 => ⟨((274915204833395/1125899906842624), (15646767027537/1125899906842624)), (4435547/2251799813685248), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-378026425/268435456), (-5044627631/268435456)), (1/134217728), by norm_num⟩, -3, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-420850299/268435456), (-5616096935/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-56401709903119/562949953421312), (-823513985862873/4503599627370496)), (20789779/4503599627370496), by norm_num⟩
  | 1 => ⟨((1542027249/8589934592), (2814367261/8589934592)), (73/8589934592), by norm_num⟩
  | 2 => ⟨((-2762941925/17179869184), (-2521334595/8589934592)), (133/17179869184), by norm_num⟩
  | 3 => ⟨((825087893/8589934592), (3011750091/17179869184)), (81/17179869184), by norm_num⟩
  | 4 => ⟨((-2956718091/68719476736), (-5396331745/68719476736)), (147/68719476736), by norm_num⟩
  | 5 => ⟨((2119091055/137438953472), (3867571401/137438953472)), (107/137438953472), by norm_num⟩
  | 6 => ⟨((-2531267643/549755813888), (-2309919227/274877906944)), (129/549755813888), by norm_num⟩
  | 7 => ⟨((1295835077/1099511627776), (2365039799/1099511627776)), (67/1099511627776), by norm_num⟩
  | 8 => ⟨((-1160912385/4398046511104), (-4237582455/8796093022208)), (61/4398046511104), by norm_num⟩
  | 9 => ⟨((924478115/17592186044416), (843636499/8796093022208)), (99/35184372088832), by norm_num⟩
  | 10 => ⟨((-2650307867/281474976710656), (-2418549897/140737488355328)), (9/17592186044416), by norm_num⟩
  | 11 => ⟨((863402585/562949953421312), (12310965/4398046511104)), (95/1125899906842624), by norm_num⟩
  | 12 => ⟨((-2062679677/9007199254740992), (-3764614505/9007199254740992)), (115/9007199254740992), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790966773095085/5070602400912917605986812821504), (-674764397515/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779545265919849/633825300114114700748351602688), (-199804133363/39614081257132168796771975168)), (11565/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236326875301533/4951760157141521099596496896), (-3595965782817/39614081257132168796771975168)), (13013/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890444142139531/2475880078570760549798248448), (-1910050632307/1237940039285380274899124224)), (13829/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772109823069911/154742504910672534362390528), (-3819412372217/154742504910672534362390528)), (13833/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387603627798829/2417851639229258349412352), (-3579967225137/9671406556917033397649408)), (3243/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259541530097043/604462909807314587353088), (-3131739531737/604462909807314587353088)), (5677/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944507144636445/37778931862957161709568), (-317981550625/4722366482869645213696)), (2307/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1298455146902869/4722366482869645213696), (-3814578347333/4722366482869645213696)), (1731/590295810358705651712), by norm_num⟩
  | 9 => ⟨((25354774777129/9223372036854775808), (-81923361537/9223372036854775808)), (9525/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912522023479773/36893488147419103232), (-3275472186669/36893488147419103232)), (11913/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824419175802747/9223372036854775808), (-3682896057241/4611686018427387904)), (3353/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1595663524783271/1152921504606846976), (-7360768159433/1152921504606846976)), (839/36028797018963968), by norm_num⟩
  | 5 => ⟨((299011012096481/36028797018963968), (-804377769313/18014398509481984)), (23519/144115188075855872), by norm_num⟩
  | 4 => ⟨((373455751234649/9007199254740992), (-4820619090167/18014398509481984)), (8833/9007199254740992), by norm_num⟩
  | 3 => ⟨((1491973402885629/9007199254740992), (-6015896236405/4503599627370496)), (11065/2251799813685248), by norm_num⟩
  | 2 => ⟨((558332706174849/1125899906842624), (-12002181819959/2251799813685248)), (44403/2251799813685248), by norm_num⟩
  | 1 => ⟨((1112028302971241/1125899906842624), (-17929324119069/1125899906842624)), (66961/1125899906842624), by norm_num⟩
  | 0 => ⟨((1098078398510327/1125899906842624), (-35563323754537/1125899906842624)), (67677/562949953421312), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1098078398510327/1125899906842624), (-35563323754537/1125899906842624)), (258167268993186773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((267455262221391/281474976710656), (-34684537547923/562949953421312)), (272571/1125899906842624), by norm_num⟩
  | 2 => ⟨((1012261392982121/1125899906842624), (-131827876045171/1125899906842624)), (275789/562949953421312), by norm_num⟩
  | 3 => ⟨((447328635830645/562949953421312), (-7407645021793/35184372088832)), (1120979/1125899906842624), by norm_num⟩
  | 4 => ⟨((661001450955001/1125899906842624), (-376718587894667/1125899906842624)), (281689/140737488355328), by norm_num⟩
  | 5 => ⟨((524035967862461/2251799813685248), (-884666680179059/2251799813685248)), (8308073/2251799813685248), by norm_num⟩
  | 6 => ⟨((-56401709903119/562949953421312), (-823513985862873/4503599627370496)), (20789779/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-420850299/268435456), (-5616096935/268435456)), (1/134217728), by norm_num⟩, -3, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-57132171/33554432), (-6099267347/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-305614642602025/2251799813685248), (547432438555271/4503599627370496)), (9276073/2251799813685248), by norm_num⟩
  | 1 => ⟨((283574407/1073741824), (-2031811405/8589934592)), (35/4294967296), by norm_num⟩
  | 2 => ⟨((-4414482533/17179869184), (1976861217/8589934592)), (69/8589934592), by norm_num⟩
  | 3 => ⟨((2863395455/17179869184), (-2564529537/17179869184)), (91/17179869184), by norm_num⟩
  | 4 => ⟨((-1392977569/17179869184), (2495172027/34359738368)), (45/17179869184), by norm_num⟩
  | 5 => ⟨((2168487351/68719476736), (-3884304457/137438953472)), (71/68719476736), by norm_num⟩
  | 6 => ⟨((-1406560515/137438953472), (314937811/34359738368)), (47/137438953472), by norm_num⟩
  | 7 => ⟨((1564023075/549755813888), (-2801557407/1099511627776)), (53/549755813888), by norm_num⟩
  | 8 => ⟨((-3043448375/4398046511104), (340723687/549755813888)), (105/4398046511104), by norm_num⟩
  | 9 => ⟨((2632123147/17592186044416), (-2357396197/17592186044416)), (23/4398046511104), by norm_num⟩
  | 10 => ⟨((-1024375029/35184372088832), (917456237/35184372088832)), (145/140737488355328), by norm_num⟩
  | 11 => ⟨((724851551/140737488355328), (-2596781677/562949953421312)), (13/70368744177664), by norm_num⟩
  | 12 => ⟨((-3761322639/4503599627370496), (421091985/562949953421312)), (17/562949953421312), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581757847530181/10141204801825835211973625643008), (785214222603/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779335250641385/633825300114114700748351602688), (1859661271717/316912650057057350374175801344)), (11571/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945189329932979/19807040628566084398385987584), (4183593684753/39614081257132168796771975168)), (13021/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890192927556233/2475880078570760549798248448), (4444294211837/2475880078570760549798248448)), (6919/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771858495384827/154742504910672534362390528), (4443423386617/154742504910672534362390528)), (6921/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550178771416415/9671406556917033397649408), (1041196063715/2417851639229258349412352)), (12981/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259335137824881/604462909807314587353088), (3643261144655/604462909807314587353088)), (5681/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888678677125587/75557863725914323419136), (739820629165/9444732965739290427392)), (18471/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((20284425646967/73786976294838206464), (554675804309/590295810358705651712)), (3465/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811179448490825/295147905179352825856), (6098968535873/590295810358705651712)), (4767/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912305104363581/36893488147419103232), (7620013345429/73786976294838206464)), (23851/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823930452745299/9223372036854775808), (8567432238993/9223372036854775808)), (26855/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595173984756767/1152921504606846976), (4280540171753/576460752303423488)), (26883/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74725924018641/9007199254740992), (7483801585753/144115188075855872)), (11777/72057594037927936), by norm_num⟩
  | 4 => ⟨((746588640992949/18014398509481984), (2802855095775/9007199254740992)), (17697/18014398509481984), by norm_num⟩
  | 3 => ⟨((745581533216081/4503599627370496), (6994647127395/4503599627370496)), (22177/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115850330056419/2251799813685248), (13951847057987/2251799813685248)), (44519/2251799813685248), by norm_num⟩
  | 1 => ⟨((138849239224223/140737488355328), (20834239295217/1125899906842624)), (67195/1125899906842624), by norm_num⟩
  | 0 => ⟨((1095563148757225/1125899906842624), (10323719327589/281474976710656)), (136059/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1095563148757225/1125899906842624), (10323719327589/281474976710656)), (519023899558639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((8316634506225/8796093022208), (80364418788429/1125899906842624)), (274767/1125899906842624), by norm_num⟩
  | 2 => ⟨((125095935122533/140737488355328), (75983905204403/562949953421312)), (279403/562949953421312), by norm_num⟩
  | 3 => ⟨((869030479211063/1125899906842624), (67539060039271/281474976710656)), (1144251/1125899906842624), by norm_num⟩
  | 4 => ⟨((605941589972401/1125899906842624), (417042412773529/1125899906842624)), (2315509/1125899906842624), by norm_num⟩
  | 5 => ⟨((171632340700891/1125899906842624), (448891311112331/1125899906842624)), (1051927/281474976710656), by norm_num⟩
  | 6 => ⟨((-305614642602025/2251799813685248), (547432438555271/4503599627370496)), (9276073/2251799813685248), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-57132171/33554432), (-6099267347/268435456)), (1/134217728), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-488421359/268435456), (-6517808595/268435456)), (3/268435456), by norm_num⟩
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
  | 0 => ⟨((480719935345359/4503599627370496), (549444960998029/4503599627370496)), (32234917/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1906641013/8589934592), (-2179219583/8589934592)), (131/17179869184), by norm_num⟩
  | 2 => ⟨((247796783/1073741824), (2265779865/8589934592)), (139/17179869184), by norm_num⟩
  | 3 => ⟨((-343519283/2147483648), (-3141037851/17179869184)), (99/17179869184), by norm_num⟩
  | 4 => ⟨((1428656535/17179869184), (408225287/4294967296)), (105/34359738368), by norm_num⟩
  | 5 => ⟨((-1188323099/34359738368), (-2716417985/68719476736)), (45/34359738368), by norm_num⟩
  | 6 => ⟨((3294731223/274877906944), (3765754935/274877906944)), (127/274877906944), by norm_num⟩
  | 7 => ⟨((-3914971985/1099511627776), (-4474666999/1099511627776)), (77/549755813888), by norm_num⟩
  | 8 => ⟨((2035238845/2199023255552), (2326202111/2199023255552)), (41/1099511627776), by norm_num⟩
  | 9 => ⟨((-3761920179/17592186044416), (-4299734493/17592186044416)), (155/17592186044416), by norm_num⟩
  | 10 => ⟨((3129077239/70368744177664), (3576418609/70368744177664)), (131/70368744177664), by norm_num⟩
  | 11 => ⟨((-2366084799/281474976710656), (-2704346701/281474976710656)), (51/140737488355328), by norm_num⟩
  | 12 => ⟨((3280090015/2251799813685248), (1874510291/1125899906842624)), (9/140737488355328), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581605650422191/10141204801825835211973625643008), (1109840891195/10141204801825835211973625643008)), (7279/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779161512377905/633825300114114700748351602688), (1313991979977/633825300114114700748351602688)), (17313/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890183608236551/39614081257132168796771975168), (184750527049/4951760157141521099596496896)), (9739/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889986200322535/2475880078570760549798248448), (1570087953887/2475880078570760549798248448)), (10349/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885826173670017/77371252455336267181195264), (1569760081487/154742504910672534362390528)), (20699/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774993061352533/4835703278458516698824704), (367825450471/2417851639229258349412352)), (1213/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1259167184937221/604462909807314587353088), (10055007057/4722366482869645213696)), (2123/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1888406905576083/75557863725914323419136), (1045394428855/37778931862957161709568)), (27603/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324500104978901/1180591620717411303424), (1567520824219/4722366482869645213696)), (10353/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622081652710169/590295810358705651712), (2154413954941/590295810358705651712)), (28475/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912133051948201/36893488147419103232), (1345813690197/36893488147419103232)), (8901/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823546700349299/9223372036854775808), (3026170609749/9223372036854775808)), (40065/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797397216710839/576460752303423488), (3023784582929/1152921504606846976)), (2505/72057594037927936), by norm_num⟩
  | 5 => ⟨((1195287395018895/144115188075855872), (41298899779/2251799813685248)), (35087/144115188075855872), by norm_num⟩
  | 4 => ⟨((186586951778245/4503599627370496), (989834103789/9007199254740992)), (6583/4503599627370496), by norm_num⟩
  | 3 => ⟨((1490577414793729/9007199254740992), (4939807309265/9007199254740992)), (2059/281474976710656), by norm_num⟩
  | 2 => ⟨((2230578475402071/4503599627370496), (4925788912889/2251799813685248)), (8247/281474976710656), by norm_num⟩
  | 1 => ⟨((1110013357947541/1125899906842624), (14707459367349/2251799813685248)), (99185/1125899906842624), by norm_num⟩
  | 0 => ⟨((547122239590081/562949953421312), (455256162265/35184372088832)), (398517/2251799813685248), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((547122239590081/562949953421312), (455256162265/35184372088832)), (1520221718795012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2126581129585547/2251799813685248), (28317205201985/1125899906842624)), (784939/2251799813685248), by norm_num⟩
  | 2 => ⟨((2006901242642705/2251799813685248), (106970138036543/2251799813685248)), (95129/140737488355328), by norm_num⟩
  | 3 => ⟨((1783555519847225/2251799813685248), (190672813494785/2251799813685248)), (2857669/2251799813685248), by norm_num⟩
  | 4 => ⟨((1396533631213387/2251799813685248), (18877985230227/140737488355328)), (5010829/2251799813685248), by norm_num⟩
  | 5 => ⟨((206398601716869/562949953421312), (187325648422825/1125899906842624)), (3779777/1125899906842624), by norm_num⟩
  | 6 => ⟨((480719935345359/4503599627370496), (549444960998029/4503599627370496)), (32234917/9007199254740992), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-488421359/268435456), (-6517808595/268435456)), (3/268435456), by norm_num⟩, -4, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile028Terms0

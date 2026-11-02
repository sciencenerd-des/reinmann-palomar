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
namespace Reinmann.XiRectangle.Tile035Terms3
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
  | 0 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-64823859/33554432), (-348468755/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-998031890552269/9007199254740992), (840644684644697/9007199254740992)), (236771731/9007199254740992), by norm_num⟩
  | 1 => ⟨((91938941/268435456), (-309761573/1073741824)), (11/134217728), by norm_num⟩
  | 2 => ⟨((-1136748679/2147483648), (957486173/2147483648)), (137/1073741824), by norm_num⟩
  | 3 => ⟨((585623071/1073741824), (-493271735/1073741824)), (71/536870912), by norm_num⟩
  | 4 => ⟨((-905092887/2147483648), (762361937/2147483648)), (221/2147483648), by norm_num⟩
  | 5 => ⟨((1119072215/4294967296), (-942597245/4294967296)), (275/4294967296), by norm_num⟩
  | 6 => ⟨((-576516621/4294967296), (242800675/2147483648)), (143/4294967296), by norm_num⟩
  | 7 => ⟨((1018307057/17179869184), (-214430627/4294967296)), (255/17179869184), by norm_num⟩
  | 8 => ⟨((-393453793/17179869184), (662814171/34359738368)), (199/34359738368), by norm_num⟩
  | 9 => ⟨((540525501/68719476736), (-910571885/137438953472)), (275/137438953472), by norm_num⟩
  | 10 => ⟨((-167078727/68719476736), (562923271/274877906944)), (43/68719476736), by norm_num⟩
  | 11 => ⟨((375598137/549755813888), (-632734447/1099511627776)), (195/1099511627776), by norm_num⟩
  | 12 => ⟨((-773993191/4398046511104), (325968173/2199023255552)), (203/4398046511104), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581459249645961/10141204801825835211973625643008), (3180436332289/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778981537924669/633825300114114700748351602688), (3764767578457/633825300114114700748351602688)), (92571/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889980790779889/39614081257132168796771975168), (4234629369863/39614081257132168796771975168)), (52083/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889770256761093/2475880078570760549798248448), (4498405074419/2475880078570760549798248448)), (6919/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((221429487236345/19342813113834066795298816), (2248702720181/77371252455336267181195264)), (110735/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549782664177051/9671406556917033397649408), (4215255637945/9671406556917033397649408)), (103847/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258988621934351/604462909807314587353088), (1843643443973/302231454903657293676544)), (90899/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888115735017461/75557863725914323419136), (2994925341075/37778931862957161709568)), (36943/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297781162831061/4722366482869645213696), (4490646670233/4722366482869645213696)), (27721/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621778747080627/590295810358705651712), (3085905079439/295147905179352825856)), (152553/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823885333785495/73786976294838206464), (1927630086929/18446744073709551616)), (95411/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823115398399121/9223372036854775808), (8668504058525/9223372036854775808)), (214857/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199294933551419/144115188075855872), (4330608872557/576460752303423488)), (53771/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194902688496021/144115188075855872), (7570372350827/144115188075855872)), (94227/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492110352147433/36028797018963968), (11339182003143/36028797018963968)), (283193/36028797018963968), by norm_num⟩
  | 3 => ⟨((744915766285855/4503599627370496), (1768167592513/1125899906842624)), (44361/1125899906842624), by norm_num⟩
  | 2 => ⟨((34828812410809/70368744177664), (7051214993477/1125899906842624)), (89059/562949953421312), by norm_num⟩
  | 1 => ⟨((138601180698057/140737488355328), (5261630967987/281474976710656)), (537729/1125899906842624), by norm_num⟩
  | 0 => ⟨((545813253847765/562949953421312), (20832750569737/562949953421312)), (1089007/1125899906842624), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((545813253847765/562949953421312), (20832750569737/562949953421312)), (4154232029441451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((528427265641767/562949953421312), (80794332113975/1125899906842624)), (2192315/1125899906842624), by norm_num⟩
  | 2 => ⟨((986245552952165/1125899906842624), (37919825500357/281474976710656)), (2215193/562949953421312), by norm_num⟩
  | 3 => ⟨((1686959336777039/2251799813685248), (132865307266347/562949953421312)), (17910817/2251799813685248), by norm_num⟩
  | 4 => ⟨((142296217361367/281474976710656), (49768715954349/140737488355328)), (17645319/1125899906842624), by norm_num⟩
  | 5 => ⟨((293895059382257/2251799813685248), (1610237637404721/4503599627370496)), (121282027/4503599627370496), by norm_num⟩
  | 6 => ⟨((-998031890552269/9007199254740992), (840644684644697/9007199254740992)), (236771731/9007199254740992), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-64823859/33554432), (-348468755/8388608)), (1/16777216), by norm_num⟩, -7, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-4109755/2097152), (-1413920103/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-342674238697919/9007199254740992), (611001881924943/4503599627370496)), (218101579/9007199254740992), by norm_num⟩
  | 1 => ⟨((64042395/536870912), (-456760613/1073741824)), (165/2147483648), by norm_num⟩
  | 2 => ⟨((-200804559/1073741824), (358042565/536870912)), (261/2147483648), by norm_num⟩
  | 3 => ⟨((419747689/2147483648), (-1496853855/2147483648)), (275/2147483648), by norm_num⟩
  | 4 => ⟨((-329029113/2147483648), (1173344151/2147483648)), (217/2147483648), by norm_num⟩
  | 5 => ⟨((12895861/134217728), (-1471605519/4294967296)), (137/2147483648), by norm_num⟩
  | 6 => ⟨((-215652787/4294967296), (1538070197/8589934592)), (289/8589934592), by norm_num⟩
  | 7 => ⟨((193193733/8589934592), (-688944315/8589934592)), (261/17179869184), by norm_num⟩
  | 8 => ⟨((-75719729/8589934592), (1080090457/34359738368)), (103/17179869184), by norm_num⟩
  | 9 => ⟨((422077817/137438953472), (-94072705/8589934592)), (289/137438953472), by norm_num⟩
  | 10 => ⟨((-264684511/274877906944), (117985769/34359738368)), (183/274877906944), by norm_num⟩
  | 11 => ⟨((150893955/549755813888), (-1076199843/1099511627776)), (211/1099511627776), by norm_num⟩
  | 12 => ⟨((-157709041/2199023255552), (1124806127/4398046511104)), (111/2199023255552), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395355765008039/2535301200456458802993406410752), (2402269124671/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778941957179693/633825300114114700748351602688), (2843499882197/633825300114114700748351602688)), (1445/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((236242057014963/4951760157141521099596496896), (3198381301357/39614081257132168796771975168)), (52029/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889723400843973/2475880078570760549798248448), (1698800015477/1237940039285380274899124224)), (55291/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885694661329879/77371252455336267181195264), (1698417534479/77371252455336267181195264)), (55303/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774869648978229/4835703278458516698824704), (397965034689/1208925819614629174706176)), (51859/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258950974358079/604462909807314587353088), (2784942837125/604462909807314587353088)), (45389/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888055115798891/75557863725914323419136), (2262004630869/37778931862957161709568)), (147561/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297736186341269/4722366482869645213696), (3391674865849/4722366482869645213696)), (13839/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810858848260423/295147905179352825856), (4661389082349/590295810358705651712)), (152295/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823810207421625/73786976294838206464), (5823491917471/73786976294838206464)), (47617/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823032510971455/9223372036854775808), (6546969504849/9223372036854775808)), (107207/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594278614899003/1152921504606846976), (6541399171211/1152921504606846976)), (214585/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298708556340785/36028797018963968), (5717462178327/144115188075855872)), (187955/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492012213678597/36028797018963968), (2140920098621/9007199254740992)), (282319/36028797018963968), by norm_num⟩
  | 3 => ⟨((372429201957337/2251799813685248), (5341364214601/4503599627370496)), (44197/1125899906842624), by norm_num⟩
  | 2 => ⟨((278604786217849/562949953421312), (21299942491663/4503599627370496)), (354593/2251799813685248), by norm_num⟩
  | 1 => ⟨((8661599011707/8796093022208), (31786484069789/2251799813685248)), (1068879/2251799813685248), by norm_num⟩
  | 0 => ⟨((2182987884699863/2251799813685248), (31460692923313/1125899906842624)), (539555/562949953421312), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2182987884699863/2251799813685248), (31460692923313/1125899906842624)), (2058238985301780523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2114520560403187/2251799813685248), (121997188344123/2251799813685248)), (4305149/2251799813685248), by norm_num⟩
  | 2 => ⟨((989500456328493/1125899906842624), (114559723070075/1125899906842624)), (1068983/281474976710656), by norm_num⟩
  | 3 => ⟨((1715938010215019/2251799813685248), (402724603015887/2251799813685248)), (8385979/1125899906842624), by norm_num⟩
  | 4 => ⟨((1235569934821601/2251799813685248), (306888050067273/1125899906842624)), (493135/35184372088832), by norm_num⟩
  | 5 => ⟨((127665873732439/562949953421312), (673561913833873/2251799813685248)), (51839907/2251799813685248), by norm_num⟩
  | 6 => ⟨((-342674238697919/9007199254740992), (611001881924943/4503599627370496)), (218101579/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4109755/2097152), (-1413920103/33554432)), (1/16777216), by norm_num⟩, -7, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-66648619/33554432), (-358277985/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((363515238751205/9007199254740992), (73822145408971/562949953421312)), (44697753/2251799813685248), by norm_num⟩
  | 1 => ⟨((-137719035/1073741824), (-447484497/1073741824)), (137/2147483648), by norm_num⟩
  | 2 => ⟨((437678507/2147483648), (1422129819/2147483648)), (55/536870912), by norm_num⟩
  | 3 => ⟨((-463655285/2147483648), (-1506535039/2147483648)), (235/2147483648), by norm_num⟩
  | 4 => ⟨((92095091/536870912), (1196962363/2147483648)), (189/2147483648), by norm_num⟩
  | 5 => ⟨((-468293051/4294967296), (-1521604329/4294967296)), (243/4294967296), by norm_num⟩
  | 6 => ⟨((496086841/8589934592), (100744593/536870912)), (65/2147483648), by norm_num⟩
  | 7 => ⟨((-450454481/17179869184), (-731821119/8589934592)), (119/8589934592), by norm_num⟩
  | 8 => ⟨((357892147/34359738368), (1162883455/34359738368)), (191/34359738368), by norm_num⟩
  | 9 => ⟨((-252755669/68719476736), (-51329253/4294967296)), (137/68719476736), by norm_num⟩
  | 10 => ⟨((321308449/274877906944), (522006813/137438953472)), (11/17179869184), by norm_num⟩
  | 11 => ⟨((-371322017/1099511627776), (-603260273/549755813888)), (205/1099511627776), by norm_num⟩
  | 12 => ⟨((393360453/4398046511104), (1278129081/4398046511104)), (219/4398046511104), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388410907415/10141204801825835211973625643008), (1657225654043/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222362901539869/79228162514264337593543950336), (122595395199/39614081257132168796771975168)), (92393/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236236625621101/4951760157141521099596496896), (1103165720191/19807040628566084398385987584)), (103955/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236209676322099/309485009821345068724781056), (2343751982579/2475880078570760549798248448)), (110467/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771343530905979/154742504910672534362390528), (2343217566081/154742504910672534362390528)), (55241/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774848289492933/4835703278458516698824704), (1098099399897/4835703278458516698824704)), (103595/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78682112870015/37778931862957161709568), (960553224579/302231454903657293676544)), (90663/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887995111786279/75557863725914323419136), (780183568125/18889465931478580854784)), (147359/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297691528402173/4722366482869645213696), (292452539583/590295810358705651712)), (27637/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405414213012085/147573952589676412928), (3215466723111/590295810358705651712)), (9503/36893488147419103232), by norm_num⟩
  | 8 => ⟨((455933747791869/18446744073709551616), (251066734593/4611686018427387904)), (190129/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822949045223919/9223372036854775808), (1129021962643/2305843009213693952)), (213989/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49818643359457/36028797018963968), (2256099489845/576460752303423488)), (53527/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194764066347267/144115188075855872), (3943803035805/144115188075855872)), (93739/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491910197104207/36028797018963968), (5906972174103/36028797018963968)), (70371/9007199254740992), by norm_num⟩
  | 3 => ⟨((372398726908833/2251799813685248), (7368455499841/9007199254740992)), (176161/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114305639758547/2251799813685248), (14691219528617/4503599627370496)), (1379/8796093022208), by norm_num⟩
  | 1 => ⟨((1108535278881103/1125899906842624), (21922907036503/2251799813685248)), (531297/1125899906842624), by norm_num⟩
  | 0 => ⟨((2182555719878367/2251799813685248), (5423994980431/281474976710656)), (2139327/2251799813685248), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2182555719878367/2251799813685248), (5423994980431/281474976710656)), (8160884865767668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1057302380801311/1125899906842624), (84115265999651/2251799813685248)), (4229533/2251799813685248), by norm_num⟩
  | 2 => ⟨((495656617951289/562949953421312), (78990388455195/1125899906842624)), (8259669/2251799813685248), by norm_num⟩
  | 3 => ⟨((1734545751843331/2251799813685248), (278192464921009/2251799813685248)), (15703623/2251799813685248), by norm_num⟩
  | 4 => ⟨((1301740012537653/2251799813685248), (13393107684655/70368744177664)), (28072907/2251799813685248), by norm_num⟩
  | 5 => ⟨((670950725550189/2251799813685248), (123878465994245/562949953421312)), (21571677/1125899906842624), by norm_num⟩
  | 6 => ⟨((363515238751205/9007199254740992), (73822145408971/562949953421312)), (44697753/2251799813685248), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66648619/33554432), (-358277985/8388608)), (1/16777216), by norm_num⟩, -7, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-67504719/33554432), (-1451520215/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((902812428625333/9007199254740992), (398817247620997/4503599627370496)), (65923381/4503599627370496), by norm_num⟩
  | 1 => ⟨((-346427095/1073741824), (-306068229/1073741824)), (103/2147483648), by norm_num⟩
  | 2 => ⟨((1115105801/2147483648), (985195623/2147483648)), (21/268435456), by norm_num⟩
  | 3 => ⟨((-37389449/67108864), (-264268531/536870912)), (23/268435456), by norm_num⟩
  | 4 => ⟨((240703987/536870912), (425323793/1073741824)), (75/1073741824), by norm_num⟩
  | 5 => ⟨((-154959249/536870912), (-273812895/1073741824)), (49/1073741824), by norm_num⟩
  | 6 => ⟨((665059441/4294967296), (293789903/2147483648)), (107/4294967296), by norm_num⟩
  | 7 => ⟨((-611641073/8589934592), (-540384695/8589934592)), (25/2147483648), by norm_num⟩
  | 8 => ⟨((246099583/8589934592), (27178613/1073741824)), (163/34359738368), by norm_num⟩
  | 9 => ⟨((-44009111/4294967296), (-622112571/68719476736)), (119/68719476736), by norm_num⟩
  | 10 => ⟨((453311563/137438953472), (400500623/137438953472)), (155/274877906944), by norm_num⟩
  | 11 => ⟨((-1061202641/1099511627776), (-937572199/1099511627776)), (183/1099511627776), by norm_num⟩
  | 12 => ⟨((1138626509/4398046511104), (502988081/2199023255552)), (99/2199023255552), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49417349261741/316912650057057350374175801344), (942600728129/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889432634466533/316912650057057350374175801344), (278908652837/158456325028528675187087900672)), (46155/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944925202693979/19807040628566084398385987584), (156858487165/4951760157141521099596496896)), (6491/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((944816130251945/1237940039285380274899124224), (666511766793/1237940039285380274899124224)), (27589/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442824626679799/38685626227668133590597632), (333178957585/38685626227668133590597632)), (110365/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549654502487245/9671406556917033397649408), (1249094252511/9671406556917033397649408)), (103477/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629438561286601/302231454903657293676544), (1092630740831/604462909807314587353088)), (11319/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943967875820963/37778931862957161709568), (443728141241/18889465931478580854784)), (147165/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324411806779129/1180591620717411303424), (332662203359/1180591620717411303424)), (110389/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810798146510187/295147905179352825856), (914386091389/295147905179352825856)), (37953/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911829912317799/36893488147419103232), (1142330539401/36893488147419103232)), (47451/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911432606869329/4611686018427387904), (1284225866067/4611686018427387904)), (213583/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199264208515061/144115188075855872), (2566213590307/1152921504606846976)), (106825/576460752303423488), by norm_num⟩
  | 5 => ⟨((37334141749291/4503599627370496), (280365187875/18014398509481984)), (187021/144115188075855872), by norm_num⟩
  | 4 => ⟨((745902472334629/18014398509481984), (3359357773507/36028797018963968)), (280683/36028797018963968), by norm_num⟩
  | 3 => ⟨((744733453095139/4503599627370496), (2095209261625/4503599627370496)), (21945/562949953421312), by norm_num⟩
  | 2 => ⟨((1114182961791301/2251799813685248), (4177278734081/2251799813685248)), (703043/4503599627370496), by norm_num⟩
  | 1 => ⟨((554182245757645/562949953421312), (12466334611619/2251799813685248)), (1056579/2251799813685248), by norm_num⟩
  | 0 => ⟨((2181977461549803/2251799813685248), (24671843768127/2251799813685248)), (530315/562949953421312), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2181977461549803/2251799813685248), (24671843768127/2251799813685248)), (2022991182567405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2114049798701069/2251799813685248), (47813670389135/2251799813685248)), (2078727/1125899906842624), by norm_num⟩
  | 2 => ⟨((30995486762719/35184372088832), (22444375305255/562949953421312)), (7982813/2251799813685248), by norm_num⟩
  | 3 => ⟨((1743960504040675/2251799813685248), (19772253883489/281474976710656)), (3675343/562949953421312), by norm_num⟩
  | 4 => ⟨((669770450243697/1125899906842624), (7656548694761/70368744177664)), (24837063/2251799813685248), by norm_num⟩
  | 5 => ⟨((385100871292591/1125899906842624), (145750222674305/1125899906842624)), (34954777/2251799813685248), by norm_num⟩
  | 6 => ⟨((902812428625333/9007199254740992), (398817247620997/4503599627370496)), (65923381/4503599627370496), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-67504719/33554432), (-1451520215/33554432)), (1/16777216), by norm_num⟩, -7, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-68327237/33554432), (-183650801/4194304)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((288223520585717/2251799813685248), (229546125233981/9007199254740992)), (43493389/4503599627370496), by norm_num⟩
  | 1 => ⟨((-55972341/134217728), (-89154653/1073741824)), (69/2147483648), by norm_num⟩
  | 2 => ⟨((364726581/536870912), (145237233/1073741824)), (115/2147483648), by norm_num⟩
  | 3 => ⟨((-1584419215/2147483648), (-315464617/2147483648)), (127/2147483648), by norm_num⟩
  | 4 => ⟨((645273845/1073741824), (32119193/268435456)), (105/2147483648), by norm_num⟩
  | 5 => ⟨((-1681891585/4294967296), (-334871781/4294967296)), (139/4294967296), by norm_num⟩
  | 6 => ⟨((57080887/268435456), (181840765/4294967296)), (77/4294967296), by norm_num⟩
  | 7 => ⟨((-850171613/8589934592), (-338545581/17179869184)), (145/17179869184), by norm_num⟩
  | 8 => ⟨((1384970595/34359738368), (137876773/17179869184)), (15/4294967296), by norm_num⟩
  | 9 => ⟨((-1002748423/68719476736), (-199651483/68719476736)), (89/68719476736), by norm_num⟩
  | 10 => ⟨((653410233/137438953472), (130096761/137438953472)), (59/137438953472), by norm_num⟩
  | 11 => ⟨((-774135861/549755813888), (-38533437/137438953472)), (71/549755813888), by norm_num⟩
  | 12 => ⟨((1681472913/4398046511104), (334788421/4398046511104)), (157/4398046511104), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581323245525873/10141204801825835211973625643008), (256007640927/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778828094245715/633825300114114700748351602688), (302990888039/633825300114114700748351602688)), (46115/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472452156576847/9903520314283042199192993792), (340804140137/39614081257132168796771975168)), (51881/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889587924903953/2475880078570760549798248448), (45253650115/309485009821345068724781056)), (13781/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771254232581239/154742504910672534362390528), (180972317175/77371252455336267181195264)), (110251/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774806530374737/4835703278458516698824704), (21202079413/604462909807314587353088)), (103363/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258840926277807/604462909807314587353088), (148369659533/302231454903657293676544)), (45223/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887877054871133/75557863725914323419136), (60254137349/9444732965739290427392)), (73489/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648801655691803/2361183241434822606848), (180688816431/2361183241434822606848)), (110239/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810768041173193/295147905179352825856), (496655184283/590295810358705651712)), (151585/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823584821193343/73786976294838206464), (620460607357/73786976294838206464)), (47373/18446744073709551616), by norm_num⟩
  | 7 => ⟨((14240478060637/72057594037927936), (697525774989/9223372036854775808)), (213193/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797015045781167/576460752303423488), (696910796073/1152921504606846976)), (53303/288230376151711744), by norm_num⟩
  | 5 => ⟨((597309953311829/72057594037927936), (304552912659/72057594037927936)), (186581/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491696998508123/36028797018963968), (912278318479/36028797018963968)), (139957/18014398509481984), by norm_num⟩
  | 3 => ⟨((744666857185335/4503599627370496), (142242032495/1125899906842624)), (349967/9007199254740992), by norm_num⟩
  | 2 => ⟨((557026185271039/1125899906842624), (283581745087/562949953421312)), (700161/4503599627370496), by norm_num⟩
  | 1 => ⟨((1108175068554389/1125899906842624), (1692495828549/1125899906842624)), (1050813/2251799813685248), by norm_num⟩
  | 0 => ⟨((545317758192543/562949953421312), (418647989553/140737488355328)), (131497/140737488355328), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((545317758192543/562949953421312), (418647989553/140737488355328)), (501621246874761537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2112931363327521/2251799813685248), (6488567781129/1125899906842624)), (2044313/1125899906842624), by norm_num⟩
  | 2 => ⟨((1982552140271963/2251799813685248), (12176835866583/1125899906842624)), (965011/281474976710656), by norm_num⟩
  | 3 => ⟨((218154377205629/281474976710656), (10720851765915/562949953421312)), (1720123/281474976710656), by norm_num⟩
  | 4 => ⟨((1351810343758449/2251799813685248), (66472715050937/2251799813685248)), (21854759/2251799813685248), by norm_num⟩
  | 5 => ⟨((1619124908499441/4503599627370496), (311759312059/8796093022208)), (27530187/2251799813685248), by norm_num⟩
  | 6 => ⟨((288223520585717/2251799813685248), (229546125233981/9007199254740992)), (43493389/4503599627370496), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-68327237/33554432), (-183650801/4194304)), (1/16777216), by norm_num⟩, -7, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-69118709/33554432), (-1486225035/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1093161981865015/9007199254740992), (-350966120100467/9007199254740992)), (93616371/9007199254740992), by norm_num⟩
  | 1 => ⟨((-858994379/2147483648), (137892613/1073741824)), (75/2147483648), by norm_num⟩
  | 2 => ⟨((1415552671/2147483648), (-454471557/2147483648)), (63/1073741824), by norm_num⟩
  | 3 => ⟨((-194392945/268435456), (499288037/2147483648)), (141/2147483648), by norm_num⟩
  | 4 => ⟨((1281374869/2147483648), (-102848245/536870912)), (59/1073741824), by norm_num⟩
  | 5 => ⟨((-422320253/1073741824), (135588415/1073741824)), (79/2147483648), by norm_num⟩
  | 6 => ⟨((927932439/4294967296), (-148959099/2147483648)), (89/4294967296), by norm_num⟩
  | 7 => ⟨((-873803983/8589934592), (280539937/8589934592)), (85/8589934592), by norm_num⟩
  | 8 => ⟨((719978845/17179869184), (-462306933/34359738368)), (71/17179869184), by norm_num⟩
  | 9 => ⟨((-1054636809/68719476736), (338597385/68719476736)), (53/34359738368), by norm_num⟩
  | 10 => ⟨((695182175/137438953472), (-223192349/137438953472)), (71/137438953472), by norm_num⟩
  | 11 => ⟨((-833166197/549755813888), (267492935/549755813888)), (87/549755813888), by norm_num⟩
  | 12 => ⟨((457663311/1099511627776), (-146935513/1099511627776)), (49/1099511627776), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581292519908217/10141204801825835211973625643008), (-12645936411/316912650057057350374175801344)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778791656849947/633825300114114700748351602688), (-119729374971/158456325028528675187087900672)), (11531/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((236220954674483/4951760157141521099596496896), (-538685307517/39614081257132168796771975168)), (51891/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236193047231457/309485009821345068724781056), (-572232901443/2475880078570760549798248448)), (1723/38685626227668133590597632), by norm_num⟩
  | 14 => ⟨((1771210689654807/154742504910672534362390528), (-286048842059/77371252455336267181195264)), (27569/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774786121820193/4835703278458516698824704), (-536197955355/9671406556917033397649408)), (25847/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157350651961575/75557863725914323419136), (-234514818979/302231454903657293676544)), (90469/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471954758348551/18889465931478580854784), (-190476017419/18889465931478580854784)), (147019/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648779901236819/2361183241434822606848), (-142798176007/1180591620717411303424)), (110271/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202684533661833/73786976294838206464), (-785007728203/590295810358705651712)), (75817/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823510072433467/73786976294838206464), (-122585831513/9223372036854775808)), (23695/9223372036854775808), by norm_num⟩
  | 7 => ⟨((911348561776739/4611686018427387904), (-1102485168371/9223372036854775808)), (106639/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593946053551221/1152921504606846976), (-550750940027/576460752303423488)), (106653/576460752303423488), by norm_num⟩
  | 5 => ⟨((74659150459619/9007199254740992), (-120338640151/18014398509481984)), (186677/144115188075855872), by norm_num⟩
  | 4 => ⟨((745793408814617/18014398509481984), (-720928284773/18014398509481984)), (280081/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489196107419581/9007199254740992), (-449616215213/2251799813685248)), (350217/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227829885031513/4503599627370496), (-1792694251817/2251799813685248)), (350393/2251799813685248), by norm_num⟩
  | 1 => ⟨((1107969374532457/1125899906842624), (-2674660837521/1125899906842624)), (1052063/2251799813685248), by norm_num⟩
  | 0 => ⟨((545112962296465/562949953421312), (-5292074577025/1125899906842624)), (1053853/1125899906842624), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((545112962296465/562949953421312), (-5292074577025/1125899906842624)), (4020130161765670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((527828696573165/562949953421312), (-20497583714813/2251799813685248)), (2050831/1125899906842624), by norm_num⟩
  | 2 => ⟨((1979407738108507/2251799813685248), (-19218782823119/1125899906842624)), (3883105/1125899906842624), by norm_num⟩
  | 3 => ⟨((1739309828266323/2251799813685248), (-67575824824055/2251799813685248)), (6959327/1125899906842624), by norm_num⟩
  | 4 => ⟨((1341430160996271/2251799813685248), (-6524519606237/140737488355328)), (11168585/1125899906842624), by norm_num⟩
  | 5 => ⟨((794270037150329/2251799813685248), (-248752126760161/4503599627370496)), (1792765/140737488355328), by norm_num⟩
  | 6 => ⟨((1093161981865015/9007199254740992), (-350966120100467/9007199254740992)), (93616371/9007199254740992), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/33554432), (-1486225035/33554432)), (1/16777216), by norm_num⟩, -7, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile035Terms3

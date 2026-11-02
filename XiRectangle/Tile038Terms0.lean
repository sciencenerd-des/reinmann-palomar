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
namespace Reinmann.XiRectangle.Tile038Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨38,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((9/16), (35673/2560)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((9/16), (35673/2560))
  have he : value ((9/16), (35673/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-13082715/33554432), (-648194015/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-741589188197465/1125899906842624), (176821485100909/1125899906842624)), (63856545/2251799813685248), by norm_num⟩
  | 1 => ⟨((980435285/2147483648), (-233770969/2147483648)), (11/536870912), by norm_num⟩
  | 2 => ⟨((-1359171907/8589934592), (20254711/536870912)), (63/8589934592), by norm_num⟩
  | 3 => ⟨((1256141567/34359738368), (-74877311/8589934592)), (15/8589934592), by norm_num⟩
  | 4 => ⟨((-435345493/68719476736), (51900997/34359738368)), (43/137438953472), by norm_num⟩
  | 5 => ⟨((965627203/1099511627776), (-115120095/549755813888)), (25/549755813888), by norm_num⟩
  | 6 => ⟨((-892429031/8796093022208), (106393559/4398046511104)), (3/549755813888), by norm_num⟩
  | 7 => ⟨((706953905/70368744177664), (-337126379/140737488355328)), (39/70368744177664), by norm_num⟩
  | 8 => ⟨((-245011553/281474976710656), (233678199/1125899906842624)), (7/140737488355328), by norm_num⟩
  | 9 => ⟨((1207673367/18014398509481984), (-71988171/4503599627370496)), (71/18014398509481984), by norm_num⟩
  | 10 => ⟨((-1339352623/288230376151711744), (159674873/144115188075855872)), (81/288230376151711744), by norm_num⟩
  | 11 => ⟨((675177087/2305843009213693952), (-321972911/4611686018427387904)), (21/1152921504606846976), by norm_num⟩
  | 12 => ⟨((-1247992251/73786976294838206464), (148783077/36893488147419103232)), (5/4611686018427387904), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197933485619743/1267650600228229401496703205376), (946844672603/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890679533754271/316912650057057350374175801344), (4494628052065/633825300114114700748351602688)), (23161/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892655007005473/39614081257132168796771975168), (2528123706349/19807040628566084398385987584)), (26063/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892611035632291/2475880078570760549798248448), (2686022626659/1237940039285380274899124224)), (6925/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1774276028571633/154742504910672534362390528), (5371800159519/154742504910672534362390528)), (13855/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((388111149447681/2417851639229258349412352), (2517900985149/4835703278458516698824704)), (6497/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1261317124724613/604462909807314587353088), (1101516436137/151115727451828646838272)), (22749/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945949129738595/37778931862957161709568), (3579683430303/37778931862957161709568)), (36985/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((650308462351331/2361183241434822606848), (2684547890173/2361183241434822606848)), (27755/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812838040064665/295147905179352825856), (7381807784543/590295810358705651712)), (38189/590295810358705651712), by norm_num⟩
  | 8 => ⟨((457188559817701/18446744073709551616), (2306552317455/18446744073709551616)), (47775/73786976294838206464), by norm_num⟩
  | 7 => ⟨((914294559220263/4611686018427387904), (5189018824459/4611686018427387904)), (53801/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1599828436433909/1152921504606846976), (5188111416499/576460752303423488)), (13467/288230376151711744), by norm_num⟩
  | 5 => ⟨((599841342189505/72057594037927936), (9077146314451/144115188075855872)), (47211/144115188075855872), by norm_num⟩
  | 4 => ⟨((1499269630956939/36028797018963968), (13611604663989/36028797018963968)), (8871/4503599627370496), by norm_num⟩
  | 3 => ⟨((749380925634629/4503599627370496), (17007265623403/9007199254740992)), (5561/562949953421312), by norm_num⟩
  | 2 => ⟨((1123424089370959/2251799813685248), (8498163406577/1125899906842624)), (2793/70368744177664), by norm_num⟩
  | 1 => ⟨((1122091820574777/1125899906842624), (25466868830449/1125899906842624)), (67533/562949953421312), by norm_num⟩
  | 0 => ⟨((1117907032975065/1125899906842624), (50821609034605/1125899906842624)), (274147/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1117907032975065/1125899906842624), (50821609034605/1125899906842624)), (1045787815574264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1107676882155181/1125899906842624), (50460821447457/562949953421312)), (8893/17592186044416), by norm_num⟩
  | 2 => ⟨((270175636808737/281474976710656), (99288196103779/562949953421312)), (610957/562949953421312), by norm_num⟩
  | 3 => ⟨((1002296389936261/1125899906842624), (381209753327443/1125899906842624)), (2776747/1125899906842624), by norm_num⟩
  | 4 => ⟨((190797861342971/281474976710656), (678719586432999/1125899906842624)), (853017/140737488355328), by norm_num⟩
  | 5 => ⟨((216361871141125/2251799813685248), (460070188321289/562949953421312)), (17478991/1125899906842624), by norm_num⟩
  | 6 => ⟨((-741589188197465/1125899906842624), (176821485100909/1125899906842624)), (63856545/2251799813685248), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13082715/33554432), (-648194015/67108864)), (1/67108864), by norm_num⟩, -2, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-82942451/134217728), (-2054726415/134217728)), (3/134217728), by norm_num⟩
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
  | 0 => ⟨((-559216675582903/1125899906842624), (-235812653527631/1125899906842624)), (78907759/2251799813685248), by norm_num⟩
  | 1 => ⟨((292950779/536870912), (123532619/536870912)), (85/2147483648), by norm_num⟩
  | 2 => ⟨((-1287357303/4294967296), (-542857813/4294967296)), (3/134217728), by norm_num⟩
  | 3 => ⟨((235717759/2147483648), (198796755/4294967296)), (73/8589934592), by norm_num⟩
  | 4 => ⟨((-1035849707/34359738368), (-109200279/8589934592)), (41/17179869184), by norm_num⟩
  | 5 => ⟨((455198887/68719476736), (383900059/137438953472)), (37/68719476736), by norm_num⟩
  | 6 => ⟨((-166695697/137438953472), (-562343097/1099511627776)), (111/1099511627776), by norm_num⟩
  | 7 => ⟨((837183731/4398046511104), (176513439/2199023255552)), (9/549755813888), by norm_num⟩
  | 8 => ⟨((-919740335/35184372088832), (-193919833/17592186044416)), (81/35184372088832), by norm_num⟩
  | 9 => ⟨((449083571/140737488355328), (189371299/140737488355328)), (81/281474976710656), by norm_num⟩
  | 10 => ⟨((-49336873/140737488355328), (-166436509/1125899906842624)), (73/2251799813685248), by norm_num⟩
  | 11 => ⟨((630715287/18014398509481984), (8311327/562949953421312)), (119/36028797018963968), by norm_num⟩
  | 12 => ⟨((-923882087/288230376151711744), (-389586175/288230376151711744)), (89/288230376151711744), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583170792944291/10141204801825835211973625643008), (-1786228464843/5070602400912917605986812821504)), (29117/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890503874506745/316912650057057350374175801344), (-4237980750247/633825300114114700748351602688)), (8683/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1892259870909549/39614081257132168796771975168), (-2383718565475/19807040628566084398385987584)), (39083/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59130978556835/77371252455336267181195264), (-5065079274679/2475880078570760549798248448)), (41537/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886928215448853/77371252455336267181195264), (-5064716038445/154742504910672534362390528)), (20775/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1552051356913829/9671406556917033397649408), (-2373892573659/4835703278458516698824704)), (4871/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((39405411592163/18889465931478580854784), (-519240705013/75557863725914323419136)), (34111/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472834895545497/18889465931478580854784), (-3374702127481/37778931862957161709568)), (55455/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((325049533369317/1180591620717411303424), (-1265354604235/1180591620717411303424)), (20807/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((812550297301573/295147905179352825856), (-6958417919605/590295810358705651712)), (7157/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1828035411319507/73786976294838206464), (-8696472227869/73786976294838206464)), (35813/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1827781164867407/9223372036854775808), (-9781397227271/9223372036854775808)), (80655/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799510696767389/576460752303423488), (-9778725879527/1152921504606846976)), (80751/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1198977547494463/144115188075855872), (-534585915185/9007199254740992)), (70765/144115188075855872), by norm_num⟩
  | 4 => ⟨((749106989893255/18014398509481984), (-12824027888399/36028797018963968)), (106361/36028797018963968), by norm_num⟩
  | 3 => ⟨((374361472118813/2251799813685248), (-8009722928505/4503599627370496)), (133329/9007199254740992), by norm_num⟩
  | 2 => ⟨((35066048158343/70368744177664), (-2000437964927/281474976710656)), (66947/1125899906842624), by norm_num⟩
  | 1 => ⟨((140017447334679/140737488355328), (-2995649438817/140737488355328)), (101129/562949953421312), by norm_num⟩
  | 0 => ⟨((139257141932769/140737488355328), (-47768926313543/1125899906842624)), (410195/1125899906842624), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((139257141932769/140737488355328), (-47768926313543/1125899906842624)), (1564769749168014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((550156112112615/562949953421312), (-47266469150181/562949953421312)), (846569/1125899906842624), by norm_num⟩
  | 2 => ⟨((1067368872714323/1125899906842624), (-46192271165343/281474976710656)), (1796819/1125899906842624), by norm_num⟩
  | 3 => ⟨((490779282010953/562949953421312), (-175163678768323/562949953421312)), (3996565/1125899906842624), by norm_num⟩
  | 4 => ⟨((373358214196767/562949953421312), (-305415086999669/562949953421312)), (9455493/1125899906842624), by norm_num⟩
  | 5 => ⟨((163843981017861/1125899906842624), (-1620452841719763/2251799813685248)), (45603601/2251799813685248), by norm_num⟩
  | 6 => ⟨((-559216675582903/1125899906842624), (-235812653527631/1125899906842624)), (78907759/2251799813685248), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-82942451/134217728), (-2054726415/134217728)), (3/134217728), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-13082715/16777216), (-648194015/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((230344048927329/562949953421312), (-465863442371515/2251799813685248)), (23305639/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1218126893/2147483648), (615905631/2147483648)), (1/33554432), by norm_num⟩
  | 2 => ⟨((844341221/2147483648), (-106728313/536870912)), (47/2147483648), by norm_num⟩
  | 3 => ⟨((-390168491/2147483648), (394551623/4294967296)), (45/4294967296), by norm_num⟩
  | 4 => ⟨((540888379/8589934592), (-273482345/8589934592)), (1/268435456), by norm_num⟩
  | 5 => ⟨((-74983051/4294967296), (151650813/17179869184)), (73/68719476736), by norm_num⟩
  | 6 => ⟨((554392431/137438953472), (-560620445/274877906944)), (35/137438953472), by norm_num⟩
  | 7 => ⟨((-878344115/1099511627776), (111026423/274877906944)), (29/549755813888), by norm_num⟩
  | 8 => ⟨((608821747/4398046511104), (-615661217/8796093022208)), (83/8796093022208), by norm_num⟩
  | 9 => ⟨((-750227693/35184372088832), (379327855/35184372088832)), (53/35184372088832), by norm_num⟩
  | 10 => ⟨((52001821/17592186044416), (-420688053/281474976710656)), (61/281474976710656), by norm_num⟩
  | 11 => ⟨((-838863491/2251799813685248), (424143619/2251799813685248)), (1/35184372088832), by norm_num⟩
  | 12 => ⟨((775274485/18014398509481984), (-195995969/9007199254740992)), (61/18014398509481984), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791480001405253/5070602400912917605986812821504), (-609793003061/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780767012639845/633825300114114700748351602688), (-361600229513/316912650057057350374175801344)), (5767/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1891989624064703/39614081257132168796771975168), (-203385851017/9903520314283042199192993792)), (51905/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891904885161341/2475880078570760549798248448), (-864321053475/2475880078570760549798248448)), (3447/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1773570799345365/154742504910672534362390528), (-864243646397/154742504910672534362390528)), (55155/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775892212049393/4835703278458516698824704), (-810146182121/9671406556917033397649408)), (51711/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((315185112830689/151115727451828646838272), (-354397841351/302231454903657293676544)), (45251/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945481499879715/37778931862957161709568), (-575819415037/37778931862957161709568)), (36769/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299917084879663/4722366482869645213696), (-863594258185/4722366482869645213696)), (27579/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624716407925269/590295810358705651712), (-1187222989127/590295810358705651712)), (75851/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456889639860035/18446744073709551616), (-370925032587/18446744073709551616)), (47413/36893488147419103232), by norm_num⟩
  | 7 => ⟨((913624676996243/4611686018427387904), (-13036804089/72057594037927936)), (13337/1152921504606846976), by norm_num⟩
  | 6 => ⟨((199811923621915/144115188075855872), (-834073217209/576460752303423488)), (53359/576460752303423488), by norm_num⟩
  | 5 => ⟨((1198523821417035/144115188075855872), (-729496653477/72057594037927936)), (93403/144115188075855872), by norm_num⟩
  | 4 => ⟨((1497546435999967/36028797018963968), (-546805220315/9007199254740992)), (140153/36028797018963968), by norm_num⟩
  | 3 => ⟨((748317132210719/4503599627370496), (-2731806488615/9007199254740992)), (43819/2251799813685248), by norm_num⟩
  | 2 => ⟨((2242672156302123/4503599627370496), (-5456959238199/4503599627370496)), (43851/562949953421312), by norm_num⟩
  | 1 => ⟨((2238117241854281/2251799813685248), (-8168822347883/2251799813685248)), (526855/2251799813685248), by norm_num⟩
  | 0 => ⟨((2224470332085271/2251799813685248), (-16271285596663/2251799813685248)), (528141/1125899906842624), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2224470332085271/2251799813685248), (-16271285596663/2251799813685248)), (2014698032859420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1098677483122887/1125899906842624), (-32147610861933/2251799813685248)), (1051095/1125899906842624), by norm_num⟩
  | 2 => ⟨((535941888513229/562949953421312), (-15685167027525/562949953421312)), (4162749/2251799813685248), by norm_num⟩
  | 3 => ⟨((1019585068456923/1125899906842624), (-59730624275127/1125899906842624)), (2039511/562949953421312), by norm_num⟩
  | 4 => ⟨((920140376642575/1125899906842624), (-216361871141153/2251799813685248)), (7820505/1125899906842624), by norm_num⟩
  | 5 => ⟨((1483178376394915/2251799813685248), (-176821485100931/1125899906842624)), (1785681/140737488355328), by norm_num⟩
  | 6 => ⟨((230344048927329/562949953421312), (-465863442371515/2251799813685248)), (23305639/1125899906842624), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13082715/16777216), (-648194015/33554432)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-60754247/67108864), (-1505059895/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-825474849265819/2251799813685248), (192291409358199/1125899906842624)), (79700615/2251799813685248), by norm_num⟩
  | 1 => ⟨((1267004507/2147483648), (-590288323/2147483648)), (125/2147483648), by norm_num⟩
  | 2 => ⟨((-1019582545/2147483648), (475016203/2147483648)), (103/2147483648), by norm_num⟩
  | 3 => ⟨((1093969869/4294967296), (-127418181/1073741824)), (7/268435456), by norm_num⟩
  | 4 => ⟨((-880338291/8589934592), (410143303/8589934592)), (23/2147483648), by norm_num⟩
  | 5 => ⟨((1133479857/34359738368), (-528080145/34359738368)), (15/4294967296), by norm_num⟩
  | 6 => ⟨((-608088485/68719476736), (283304069/68719476736)), (131/137438953472), by norm_num⟩
  | 7 => ⟨((1118492185/549755813888), (-521097497/549755813888)), (123/549755813888), by norm_num⟩
  | 8 => ⟨((-112508983/274877906944), (209668517/1099511627776)), (101/2199023255552), by norm_num⟩
  | 9 => ⟨((321913285/4398046511104), (-299954187/8796093022208)), (73/8796093022208), by norm_num⟩
  | 10 => ⟨((-828959113/70368744177664), (386206113/70368744177664)), (3/2199023255552), by norm_num⟩
  | 11 => ⟨((970296891/562949953421312), (-452054371/562949953421312)), (57/281474976710656), by norm_num⟩
  | 12 => ⟨((-520544201/2251799813685248), (485035629/4503599627370496)), (31/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395699125319743/2535301200456458802993406410752), (3524347549759/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890282045205833/316912650057057350374175801344), (1044732757473/158456325028528675187087900672)), (23153/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891760812526411/39614081257132168796771975168), (2350445794157/19807040628566084398385987584)), (52107/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891661125425607/2475880078570760549798248448), (2497116419725/1237940039285380274899124224)), (55379/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773326311362747/154742504910672534362390528), (2496855053535/77371252455336267181195264)), (13849/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((96972152692101/604462909807314587353088), (1170261918113/2417851639229258349412352)), (3247/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((630269222316269/302231454903657293676544), (4095360992079/604462909807314587353088)), (45477/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890633289490741/75557863725914323419136), (6653919277099/75557863725914323419136)), (73933/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299668534483439/4722366482869645213696), (4989527057415/4722366482869645213696)), (6935/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1624372592116253/590295810358705651712), (3429558192031/295147905179352825856)), (76333/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827125702889885/73786976294838206464), (8571669330405/73786976294838206464)), (95489/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913379074427149/4611686018427387904), (9640065142313/9223372036854775808)), (53763/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597998886162929/1152921504606846976), (9636233730647/1152921504606846976)), (26913/288230376151711744), by norm_num⟩
  | 5 => ⟨((1198083427383633/144115188075855872), (8427390272987/144115188075855872)), (94337/144115188075855872), by norm_num⟩
  | 4 => ⟨((748436975668871/18014398509481984), (6316223594675/18014398509481984)), (35447/9007199254740992), by norm_num⟩
  | 3 => ⟨((747886438743641/4503599627370496), (246490941385/140737488355328)), (177731/9007199254740992), by norm_num⟩
  | 2 => ⟨((560221792512889/1125899906842624), (15752668577129/2251799813685248)), (44619/562949953421312), by norm_num⟩
  | 1 => ⟨((139705293134251/140737488355328), (23571971846729/1125899906842624)), (269577/1125899906842624), by norm_num⟩
  | 0 => ⟨((277273461730719/281474976710656), (46914913658345/1125899906842624)), (273315/562949953421312), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((277273461730719/281474976710656), (46914913658345/1125899906842624)), (1042613985301780523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1090583758552745/1125899906842624), (46214625075603/562949953421312)), (1122497/1125899906842624), by norm_num⟩
  | 2 => ⟨((1048787517397469/1125899906842624), (89530018092633/562949953421312)), (589719/281474976710656), by norm_num⟩
  | 3 => ⟨((474239652033005/562949953421312), (41699073264533/140737488355328)), (5144935/1125899906842624), by norm_num⟩
  | 4 => ⟨((43761049047231/70368744177664), (140512341282821/281474976710656)), (11717165/1125899906842624), by norm_num⟩
  | 5 => ⟨((309704335184237/2251799813685248), (174764166405873/281474976710656)), (26271807/1125899906842624), by norm_num⟩
  | 6 => ⟨((-825474849265819/2251799813685248), (192291409358199/1125899906842624)), (79700615/2251799813685248), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60754247/67108864), (-1505059895/67108864)), (1/33554432), by norm_num⟩, -4, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-67636655/67108864), (-1675557223/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((202684885782143/562949953421312), (134993506847891/2251799813685248)), (29094779/2251799813685248), by norm_num⟩
  | 1 => ⟨((-692677619/1073741824), (-57667707/536870912)), (51/2147483648), by norm_num⟩
  | 2 => ⟨((1241111683/2147483648), (25831665/268435456)), (47/2147483648), by norm_num⟩
  | 3 => ⟨((-1482515741/4294967296), (-246848695/4294967296)), (29/2147483648), by norm_num⟩
  | 4 => ⟨((1328155809/8589934592), (221146743/8589934592)), (27/4294967296), by norm_num⟩
  | 5 => ⟨((-951894299/17179869184), (-39624177/4294967296)), (5/2147483648), by norm_num⟩
  | 6 => ⟨((1137043749/68719476736), (94662659/34359738368)), (25/34359738368), by norm_num⟩
  | 7 => ⟨((-1164176517/274877906944), (-6057597/8589934592)), (53/274877906944), by norm_num⟩
  | 8 => ⟨((1042962149/1099511627776), (173660109/1099511627776)), (49/1099511627776), by norm_num⟩
  | 9 => ⟨((-415274957/2199023255552), (-276584129/8796093022208)), (5/549755813888), by norm_num⟩
  | 10 => ⟨((1190516539/35184372088832), (198228893/35184372088832)), (59/35184372088832), by norm_num⟩
  | 11 => ⟨((-775679739/140737488355328), (-129155817/140737488355328)), (79/281474976710656), by norm_num⟩
  | 12 => ⟨((926554345/1125899906842624), (154277439/1125899906842624)), (49/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582662910806559/10141204801825835211973625643008), (214921751021/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780414978678685/633825300114114700748351602688), (31849563617/79228162514264337593543950336)), (46113/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891593632315615/39614081257132168796771975168), (286620249679/39614081257132168796771975168)), (25939/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891484200390859/2475880078570760549798248448), (76125673027/618970019642690137449562112)), (55121/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773150178084741/154742504910672534362390528), (19029216195/9671406556917033397649408)), (27561/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551390159134917/9671406556917033397649408), (285400813599/9671406556917033397649408)), (25839/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630197768467337/302231454903657293676544), (62422072253/151115727451828646838272)), (11305/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1890402640330583/75557863725914323419136), (405673315409/75557863725914323419136)), (73483/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299496925926443/4722366482869645213696), (152096807639/2361183241434822606848)), (55115/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406034717267273/147573952589676412928), (209083259157/295147905179352825856)), (37893/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826836905338453/73786976294838206464), (522558638705/73786976294838206464)), (94737/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913218931752009/4611686018427387904), (293836483133/4611686018427387904)), (106585/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399421090310473/288230376151711744), (293708098831/576460752303423488)), (3331/36028797018963968), by norm_num⟩
  | 5 => ⟨((1197814692454387/144115188075855872), (128425114603/36028797018963968)), (23319/36028797018963968), by norm_num⟩
  | 4 => ⟨((1496483782426303/36028797018963968), (769973633667/36028797018963968)), (34983/9007199254740992), by norm_num⟩
  | 3 => ⟨((1495307765568235/9007199254740992), (961458041141/9007199254740992)), (174945/9007199254740992), by norm_num⟩
  | 2 => ⟨((1120012303153105/2251799813685248), (479973112609/1125899906842624)), (174991/2251799813685248), by norm_num⟩
  | 1 => ⟨((2234159512952405/2251799813685248), (359036422683/281474976710656)), (525201/2251799813685248), by norm_num⟩
  | 0 => ⟨((2216609119741879/2251799813685248), (5714464194637/2251799813685248)), (1051325/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((2216609119741879/2251799813685248), (5714464194637/2251799813685248)), (4010486611373137717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1090976938705043/1125899906842624), (703144956053/140737488355328)), (2075127/2251799813685248), by norm_num⟩
  | 2 => ⟨((528554550511887/562949953421312), (21802717686245/2251799813685248)), (4042259/2251799813685248), by norm_num⟩
  | 3 => ⟨((1984831520194535/2251799813685248), (40941208278123/2251799813685248)), (1917211/562949953421312), by norm_num⟩
  | 4 => ⟨((1748770009256651/2251799813685248), (9021827803187/281474976710656)), (6899075/1125899906842624), by norm_num⟩
  | 5 => ⟨((677899374224743/1125899906842624), (112103051399197/2251799813685248)), (5579019/562949953421312), by norm_num⟩
  | 6 => ⟨((202684885782143/562949953421312), (134993506847891/2251799813685248)), (29094779/2251799813685248), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-67636655/67108864), (-1675557223/67108864)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-73455649/67108864), (-1819710659/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-603941877563879/4503599627370496), (-690494069608055/2251799813685248)), (130911777/4503599627370496), by norm_num⟩
  | 1 => ⟨((280193479/1073741824), (320348601/536870912)), (31/536870912), by norm_num⟩
  | 2 => ⟨((-545231335/2147483648), (-311684797/536870912)), (61/1073741824), by norm_num⟩
  | 3 => ⟨((353657063/2147483648), (808680813/2147483648)), (81/2147483648), by norm_num⟩
  | 4 => ⟨((-172046217/2147483648), (-786810101/4294967296)), (5/268435456), by norm_num⟩
  | 5 => ⟨((4184831/134217728), (1224849409/17179869184)), (63/8589934592), by norm_num⟩
  | 6 => ⟨((-347447685/34359738368), (-794482299/34359738368)), (83/34359738368), by norm_num⟩
  | 7 => ⟨((386343987/137438953472), (883423525/137438953472)), (47/68719476736), by norm_num⟩
  | 8 => ⟨((-375895343/549755813888), (-429765701/274877906944)), (93/549755813888), by norm_num⟩
  | 9 => ⟨((650185389/4398046511104), (743364835/2199023255552)), (163/4398046511104), by norm_num⟩
  | 10 => ⟨((-506080939/17592186044416), (-578608471/8796093022208)), (129/17592186044416), by norm_num⟩
  | 11 => ⟨((89526185/17592186044416), (818850979/70368744177664)), (93/70368744177664), by norm_num⟩
  | 12 => ⟨((-464559765/562949953421312), (-1062273621/562949953421312)), (123/562949953421312), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791274980826545/5070602400912917605986812821504), (-1291578938401/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890138057796375/316912650057057350374175801344), (-1530988799259/316912650057057350374175801344)), (46251/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945718565464157/19807040628566084398385987584), (-430547352037/4951760157141521099596496896)), (26021/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472829392025575/618970019642690137449562112), (-1829621276401/1237940039285380274899124224)), (27653/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886491576335837/77371252455336267181195264), (-3658781337283/154742504910672534362390528)), (27659/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193904144407453/1208925819614629174706176), (-857404363801/2417851639229258349412352)), (25937/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((630128870577733/302231454903657293676544), (-1500212608453/302231454903657293676544)), (11351/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1890177939930919/75557863725914323419136), (-4874772105045/75557863725914323419136)), (73805/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299327716495151/4722366482869645213696), (-1827637524419/2361183241434822606848)), (3461/295147905179352825856), by norm_num⟩
  | 9 => ⟨((405976273758327/147573952589676412928), (-314043538291/36893488147419103232)), (76177/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826543022322341/73786976294838206464), (-3139455421545/36893488147419103232)), (95275/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913052478461969/4611686018427387904), (-3530539859351/4611686018427387904)), (53629/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597348597181589/1152921504606846976), (-1764427716627/288230376151711744)), (53675/576460752303423488), by norm_num⟩
  | 5 => ⟨((299379422005265/36028797018963968), (-6171706876727/144115188075855872)), (94035/144115188075855872), by norm_num⟩
  | 4 => ⟨((748015931736455/18014398509481984), (-1156247453483/4503599627370496)), (141259/36028797018963968), by norm_num⟩
  | 3 => ⟨((747365833307187/4503599627370496), (-11549207398359/9007199254740992)), (176937/9007199254740992), by norm_num⟩
  | 2 => ⟨((559709723158061/1125899906842624), (-11529304878017/2251799813685248)), (88741/1125899906842624), by norm_num⟩
  | 1 => ⟨((558074362586807/562949953421312), (-17244194895165/1125899906842624)), (66897/281474976710656), by norm_num⟩
  | 0 => ⟨((1106276404043155/1125899906842624), (-34289305243283/1125899906842624)), (270323/562949953421312), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1106276404043155/1125899906842624), (-34289305243283/1125899906842624)), (1031200411083030523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((542975320567057/562949953421312), (-67383342109077/1125899906842624)), (1095377/1125899906842624), by norm_num⟩
  | 2 => ⟨((260846517760217/281474976710656), (-129984882528887/1125899906842624)), (280517/140737488355328), by norm_num⟩
  | 3 => ⟨((951912702934311/1125899906842624), (-30114669841491/140737488355328)), (4677511/1125899906842624), by norm_num⟩
  | 4 => ⟨((753261115943837/1125899906842624), (-203687994590411/562949953421312)), (9911141/1125899906842624), by norm_num⟩
  | 5 => ⟨((356556661735309/1125899906842624), (-545093734095073/1125899906842624)), (319279/17592186044416), by norm_num⟩
  | 6 => ⟨((-603941877563879/4503599627370496), (-690494069608055/2251799813685248)), (130911777/4503599627370496), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-73455649/67108864), (-1819710659/67108864)), (1/33554432), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-39248145/33554432), (-972291023/33554432)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((-1067426949835357/4503599627370496), (451548494822287/2251799813685248)), (94007337/2251799813685248), by norm_num⟩
  | 1 => ⟨((264603131/536870912), (-895470331/2147483648)), (95/1073741824), by norm_num⟩
  | 2 => ⟨((-1100453485/2147483648), (931039103/2147483648)), (25/268435456), by norm_num⟩
  | 3 => ⟨((762776231/2147483648), (-645347129/2147483648)), (141/2147483648), by norm_num⟩
  | 4 => ⟨((-793074291/4294967296), (335490407/2147483648)), (149/4294967296), by norm_num⟩
  | 5 => ⟨((659660651/8589934592), (-558106151/8589934592)), (63/4294967296), by norm_num⟩
  | 6 => ⟨((-914483841/34359738368), (386849705/17179869184)), (177/34359738368), by norm_num⟩
  | 7 => ⟨((33957423/4294967296), (-919350111/137438953472)), (213/137438953472), by norm_num⟩
  | 8 => ⟨((-1129799617/549755813888), (477933703/274877906944)), (7/17179869184), by norm_num⟩
  | 9 => ⟨((1044156559/2199023255552), (-883409063/2199023255552)), (105/1099511627776), by norm_num⟩
  | 10 => ⟨((-434252505/4398046511104), (367399501/4398046511104)), (177/8796093022208), by norm_num⟩
  | 11 => ⟨((656729235/35184372088832), (-555626025/35184372088832)), (17/4398046511104), by norm_num⟩
  | 12 => ⟨((-910420035/281474976710656), (770261225/281474976710656)), (191/281474976710656), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395613030165767/2535301200456458802993406410752), (3177585667941/10141204801825835211973625643008)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((6953740541189/2475880078570760549798248448), (3766123650489/633825300114114700748351602688)), (17357/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1891303639358635/39614081257132168796771975168), (1059107451025/9903520314283042199192993792)), (19531/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891175560022851/2475880078570760549798248448), (4500667252573/2475880078570760549798248448)), (83027/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221605118714923/19342813113834066795298816), (4500060308207/154742504910672534362390528)), (83051/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387774908257007/2417851639229258349412352), (4218161610225/9671406556917033397649408)), (19471/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630070351169273/302231454903657293676544), (3690246423599/604462909807314587353088)), (68175/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944993682097227/37778931862957161709568), (5995440970701/75557863725914323419136)), (110829/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162398055712843/590295810358705651712), (1123880580991/1180591620717411303424)), (41581/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811853773615769/295147905179352825856), (3089811532307/295147905179352825856)), (57207/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826295262570911/73786976294838206464), (482621765197/4611686018427387904)), (143115/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825825093957545/9223372036854775808), (1085455353947/1152921504606846976)), (161141/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597067319349453/1152921504606846976), (4339602853275/576460752303423488)), (161311/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197269980520143/144115188075855872), (7589311930261/144115188075855872)), (70669/72057594037927936), by norm_num⟩
  | 4 => ⟨((186957141155143/4503599627370496), (11373978542891/36028797018963968)), (106195/18014398509481984), by norm_num⟩
  | 3 => ⟨((1494257709192633/9007199254740992), (7099992298975/4503599627370496)), (133079/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118937205612091/2251799813685248), (14173737414199/2251799813685248)), (267165/2251799813685248), by norm_num⟩
  | 1 => ⟨((69712796717787/70368744177664), (2649367322917/140737488355328)), (100817/281474976710656), by norm_num⟩
  | 0 => ⟨((34522079109529/35184372088832), (21063456832743/562949953421312)), (102081/140737488355328), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((34522079109529/35184372088832), (21063456832743/562949953421312)), (389408112109136537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((541167929977013/562949953421312), (82667875528853/1125899906842624)), (103979/70368744177664), by norm_num⟩
  | 2 => ⟨((517193814929747/562949953421312), (158938473317771/1125899906842624)), (3442891/1125899906842624), by norm_num⟩
  | 3 => ⟨((231969183973781/281474976710656), (18252509582501/70368744177664)), (7298149/1125899906842624), by norm_num⟩
  | 4 => ⟨((344465694130585/562949953421312), (120338079151633/281474976710656)), (7907573/562949953421312), by norm_num⟩
  | 5 => ⟨((215761990522079/1125899906842624), (1178146361704323/2251799813685248)), (16438591/562949953421312), by norm_num⟩
  | 6 => ⟨((-1067426949835357/4503599627370496), (451548494822287/2251799813685248)), (94007337/2251799813685248), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39248145/33554432), (-972291023/33554432)), (3/67108864), by norm_num⟩, -5, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile038Terms0

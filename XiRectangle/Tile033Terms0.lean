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
namespace Reinmann.XiRectangle.Tile033Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨33,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (8319/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (8319/640))
  have he : value ((5/8), (8319/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-7268175/16777216), (-1209278953/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-1336202705154035/2251799813685248), (-294316163638491/1125899906842624)), (3952599/140737488355328), by norm_num⟩
  | 1 => ⟨((441639489/1073741824), (194553775/1073741824)), (11/536870912), by norm_num⟩
  | 2 => ⟨((-1224484667/8589934592), (-269708801/4294967296)), (1/134217728), by norm_num⟩
  | 3 => ⟨((565832063/17179869184), (62315965/4294967296)), (61/34359738368), by norm_num⟩
  | 4 => ⟨((-392204899/68719476736), (-86388271/34359738368)), (11/34359738368), by norm_num⟩
  | 5 => ⟨((6796393/8589934592), (383230633/1099511627776)), (51/1099511627776), by norm_num⟩
  | 6 => ⟨((-401996855/4398046511104), (-177090155/4398046511104)), (49/8796093022208), by norm_num⟩
  | 7 => ⟨((636898255/70368744177664), (280570381/70368744177664)), (5/8796093022208), by norm_num⟩
  | 8 => ⟨((-220732115/281474976710656), (-388953137/1125899906842624)), (57/1125899906842624), by norm_num⟩
  | 9 => ⟨((1087998885/18014398509481984), (119823009/4503599627370496)), (9/2251799813685248), by norm_num⟩
  | 10 => ⟨((-1206629375/288230376151711744), (-265775939/144115188075855872)), (41/144115188075855872), by norm_num⟩
  | 11 => ⟨((608270363/2305843009213693952), (66989761/576460752303423488)), (85/4611686018427387904), by norm_num⟩
  | 12 => ⟨((-562161183/36893488147419103232), (-247646741/36893488147419103232)), (81/73786976294838206464), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583411453608229/10141204801825835211973625643008), (-1775879769595/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781293397046563/633825300114114700748351602688), (-4214709213387/633825300114114700748351602688)), (11577/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1892581211288217/39614081257132168796771975168), (-4741336762093/39614081257132168796771975168)), (26055/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892532727207969/2475880078570760549798248448), (-5037444396713/2475880078570760549798248448)), (27691/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((887098916065003/77371252455336267181195264), (-5037190023927/154742504910672534362390528)), (6925/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1552371407604957/9671406556917033397649408), (-1180523790319/2417851639229258349412352)), (12989/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1261253202286543/604462909807314587353088), (-4131562538197/604462909807314587353088)), (5685/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1891794608584365/75557863725914323419136), (-3356640498059/37778931862957161709568)), (36969/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((325134845427567/1180591620717411303424), (-2517257810627/2361183241434822606848)), (13871/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625569775662261/590295810358705651712), (-6921734687395/590295810358705651712)), (19085/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828621834380687/73786976294838206464), (-2162770059523/18446744073709551616)), (11937/18446744073709551616), by norm_num⟩
  | 7 => ⟨((457110204243175/2305843009213693952), (-4865483183521/4611686018427387904)), (53767/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99980059527435/72057594037927936), (-4864544320995/576460752303423488)), (53831/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599777277721823/72057594037927936), (-2127708622155/36028797018963968)), (47173/144115188075855872), by norm_num⟩
  | 4 => ⟨((749539638213497/18014398509481984), (-6381000758419/18014398509481984)), (35451/18014398509481984), by norm_num⟩
  | 3 => ⟨((749263562781713/4503599627370496), (-15945032391685/9007199254740992)), (88877/9007199254740992), by norm_num⟩
  | 2 => ⟨((1123194188670285/2251799813685248), (-15933764960275/2251799813685248)), (22313/562949953421312), by norm_num⟩
  | 1 => ⟨((280439756935217/281474976710656), (-23872258099553/1125899906842624)), (4213/35184372088832), by norm_num⟩
  | 0 => ⟨((1117289653068803/1125899906842624), (-47629637066881/1125899906842624)), (273395/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1117289653068803/1125899906842624), (-47629637066881/1125899906842624)), (1042919163230514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1106730339841529/1125899906842624), (-47265392199457/562949953421312)), (565741/1125899906842624), by norm_num⟩
  | 2 => ⟨((1079950329986687/1125899906842624), (-185842607335645/1125899906842624)), (603609/562949953421312), by norm_num⟩
  | 3 => ⟨((502600290513763/562949953421312), (-356516212316855/1125899906842624)), (1357215/562949953421312), by norm_num⟩
  | 4 => ⟨((784549668300833/1125899906842624), (-39787096258363/70368744177664)), (3282961/562949953421312), by norm_num⟩
  | 5 => ⟨((93377237804605/562949953421312), (-221795582235643/281474976710656)), (33150783/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1336202705154035/2251799813685248), (-294316163638491/1125899906842624)), (3952599/140737488355328), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7268175/16777216), (-1209278953/134217728)), (1/67108864), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-46079139/67108864), (-958330897/67108864)), (3/134217728), by norm_num⟩
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
  | 0 => ⟨((-40397432132865/562949953421312), (-1121678942503187/2251799813685248)), (17382573/562949953421312), by norm_num⟩
  | 1 => ⟨((169300519/2147483648), (1175203581/2147483648)), (75/2147483648), by norm_num⟩
  | 2 => ⟨((-185995631/4294967296), (-161386637/536870912)), (85/4294967296), by norm_num⟩
  | 3 => ⟨((34056181/2147483648), (945607161/8589934592)), (1/134217728), by norm_num⟩
  | 4 => ⟨((-37414539/8589934592), (-32464239/1073741824)), (9/4294967296), by norm_num⟩
  | 5 => ⟨((263066063/274877906944), (913039665/137438953472)), (129/274877906944), by norm_num⟩
  | 6 => ⟨((-48167935/274877906944), (-668717731/549755813888)), (97/1099511627776), by norm_num⟩
  | 7 => ⟨((241910333/8796093022208), (1679226325/8796093022208)), (31/2199023255552), by norm_num⟩
  | 8 => ⟨((-265765665/70368744177664), (-1844818677/70368744177664)), (139/70368744177664), by norm_num⟩
  | 9 => ⟨((129765967/281474976710656), (450386771/140737488355328)), (69/281474976710656), by norm_num⟩
  | 10 => ⟨((-114049989/2251799813685248), (-395840353/1125899906842624)), (31/1125899906842624), by norm_num⟩
  | 11 => ⟨((91124887/18014398509481984), (1265091131/36028797018963968)), (101/36028797018963968), by norm_num⟩
  | 12 => ⟨((-266962455/576460752303423488), (-926563109/288230376151711744)), (151/576460752303423488), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197885168922433/1267650600228229401496703205376), (-1116255181405/5070602400912917605986812821504)), (29117/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222613435312439/79228162514264337593543950336), (-2648112082069/633825300114114700748351602688)), (34673/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892147432750521/39614081257132168796771975168), (-2978935726439/39614081257132168796771975168)), (19507/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118254518015261/154742504910672534362390528), (-3164896609117/2475880078570760549798248448)), (41459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443434475063939/38685626227668133590597632), (-1582323072661/77371252455336267181195264)), (41467/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551940760209661/9671406556917033397649408), (-185411850857/604462909807314587353088)), (9721/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260876924500939/604462909807314587353088), (-2595499731019/604462909807314587353088)), (2127/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1891184167107959/75557863725914323419136), (-2108593951269/37778931862957161709568)), (27659/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300082434177593/4722366482869645213696), (-1581227045301/2361183241434822606848)), (41503/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406235727101761/147573952589676412928), (-4347664382619/590295810358705651712)), (28545/295147905179352825856), by norm_num⟩
  | 8 => ⟨((228480050419071/9223372036854775808), (-5433515257875/73786976294838206464)), (71397/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913782333453321/4611686018427387904), (-6111239609747/9223372036854775808)), (80369/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1598808501284579/1152921504606846976), (-6109407725343/1152921504606846976)), (20107/288230376151711744), by norm_num⟩
  | 5 => ⟨((1198795320731823/144115188075855872), (-2671835056907/72057594037927936)), (35221/72057594037927936), by norm_num⟩
  | 4 => ⟨((93621796335783/2251799813685248), (-2002844985741/9007199254740992)), (105797/36028797018963968), by norm_num⟩
  | 3 => ⟨((748564252270263/4503599627370496), (-2501750358581/2251799813685248)), (132481/9007199254740992), by norm_num⟩
  | 2 => ⟨((140227171910305/281474976710656), (-9996157526797/2251799813685248)), (132833/2251799813685248), by norm_num⟩
  | 1 => ⟨((1119748277087947/1125899906842624), (-7483548152979/562949953421312)), (200133/1125899906842624), by norm_num⟩
  | 0 => ⟨((1113485727878093/1125899906842624), (-29825452305309/1125899906842624)), (201901/562949953421312), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1113485727878093/1125899906842624), (-29825452305309/1125899906842624)), (770191194774436773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((68776146365967/70368744177664), (-29496596693575/562949953421312)), (410047/562949953421312), by norm_num⟩
  | 2 => ⟨((536211222191133/562949953421312), (-28829024522213/281474976710656)), (105563/70368744177664), by norm_num⟩
  | 3 => ⟨((1009674208006925/1125899906842624), (-219677736959539/1125899906842624)), (1781775/562949953421312), by norm_num⟩
  | 4 => ⟨((431292201152343/562949953421312), (-394001178494421/1125899906842624)), (7781967/1125899906842624), by norm_num⟩
  | 5 => ⟨((261486353656233/562949953421312), (-603711340579153/1125899906842624)), (17370475/1125899906842624), by norm_num⟩
  | 6 => ⟨((-40397432132865/562949953421312), (-1121678942503187/2251799813685248)), (17382573/562949953421312), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-46079139/67108864), (-958330897/67108864)), (3/134217728), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-7268175/8388608), (-1209278953/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((9984718972077/35184372088832), (43661302798131/140737488355328)), (27109719/1125899906842624), by norm_num⟩
  | 1 => ⟨((-844833961/2147483648), (-461787551/1073741824)), (37/1073741824), by norm_num⟩
  | 2 => ⟨((292797139/1073741824), (320086739/1073741824)), (53/2147483648), by norm_num⟩
  | 3 => ⟨((-270602015/2147483648), (-295822961/2147483648)), (51/4294967296), by norm_num⟩
  | 4 => ⟨((750268095/17179869184), (820195405/17179869184)), (73/17179869184), by norm_num⟩
  | 5 => ⟨((-104009243/8589934592), (-227406453/17179869184)), (83/68719476736), by norm_num⟩
  | 6 => ⟨((768999611/274877906944), (210168189/68719476736)), (39/137438953472), by norm_num⟩
  | 7 => ⟨((-609177043/1099511627776), (-665954229/1099511627776)), (1/17179869184), by norm_num⟩
  | 8 => ⟨((211124675/2199023255552), (57700537/549755813888)), (91/8796093022208), by norm_num⟩
  | 9 => ⟨((-520321683/35184372088832), (-568817273/35184372088832)), (29/17592186044416), by norm_num⟩
  | 10 => ⟨((144263803/70368744177664), (315419271/140737488355328)), (33/140737488355328), by norm_num⟩
  | 11 => ⟨((-290897595/1125899906842624), (-636020301/2251799813685248)), (17/562949953421312), by norm_num⟩
  | 12 => ⟨((2100363/70368744177664), (587807571/18014398509481984)), (65/18014398509481984), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582847140111075/10141204801825835211973625643008), (540515652753/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780632572283481/633825300114114700748351602688), (1281895295885/633825300114114700748351602688)), (11541/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945919177019035/19807040628566084398385987584), (1442019483445/39614081257132168796771975168)), (25969/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891744130059375/2475880078570760549798248448), (1532010128165/2475880078570760549798248448)), (55189/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((27709531401875/2417851639229258349412352), (765928810669/77371252455336267181195264)), (27597/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775816823578269/4835703278458516698824704), (717977248225/4835703278458516698824704)), (25875/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260608484844043/604462909807314587353088), (157037272207/75557863725914323419136)), (45287/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890748485535023/75557863725914323419136), (2041180811791/75557863725914323419136)), (73601/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649878069566065/2361183241434822606848), (765309941769/2361183241434822606848)), (55211/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624495009950283/590295810358705651712), (1052085301621/295147905179352825856)), (75929/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913640832856135/36893488147419103232), (2629565766357/73786976294838206464)), (94933/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456734411900803/2305843009213693952), (2957371382081/9223372036854775808)), (106831/9223372036854775808), by norm_num⟩
  | 6 => ⟨((799091715822751/576460752303423488), (1478129518247/576460752303423488)), (106869/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599125288388423/72057594037927936), (646368915259/36028797018963968)), (46777/72057594037927936), by norm_num⟩
  | 4 => ⟨((1497136005914731/36028797018963968), (3875712481921/36028797018963968)), (140417/36028797018963968), by norm_num⟩
  | 3 => ⟨((1496120243208283/9007199254740992), (4840266045241/9007199254740992)), (21959/1125899906842624), by norm_num⟩
  | 2 => ⟨((2241641170496793/4503599627370496), (9667417256953/4503599627370496)), (351799/4503599627370496), by norm_num⟩
  | 1 => ⟨((1118281715354075/1125899906842624), (14468369730663/2251799813685248)), (132209/562949953421312), by norm_num⟩
  | 0 => ⟨((34708336497341/35184372088832), (28805900386177/2251799813685248)), (1062237/2251799813685248), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((34708336497341/35184372088832), (28805900386177/2251799813685248)), (4052112587935637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2190910962653967/2251799813685248), (56832327783941/2251799813685248)), (2122909/2251799813685248), by norm_num⟩
  | 2 => ⟨((1065117090703003/1125899906842624), (55295576995009/1125899906842624)), (2119085/1125899906842624), by norm_num⟩
  | 3 => ⟨((2009799999442695/2251799813685248), (13077597693127/140737488355328)), (4217515/1125899906842624), by norm_num⟩
  | 4 => ⟨((887182328942581/1125899906842624), (186754475609223/1125899906842624)), (8312321/1125899906842624), by norm_num⟩
  | 5 => ⟨((1336202705154055/2251799813685248), (588632327277029/2251799813685248)), (7928687/562949953421312), by norm_num⟩
  | 6 => ⟨((9984718972077/35184372088832), (43661302798131/140737488355328)), (27109719/1125899906842624), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7268175/8388608), (-1209278953/67108864)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-67504719/67108864), (-350982347/16777216)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-789380194343755/4503599627370496), (-361387244211147/1125899906842624)), (144549687/4503599627370496), by norm_num⟩
  | 1 => ⟨((605801779/2147483648), (1109371819/2147483648)), (113/2147483648), by norm_num⟩
  | 2 => ⟨((-487500175/2147483648), (-223183133/536870912)), (93/2147483648), by norm_num⟩
  | 3 => ⟨((523067509/4294967296), (957865055/4294967296)), (51/2147483648), by norm_num⟩
  | 4 => ⟨((-105230585/2147483648), (-770812167/8589934592)), (21/2147483648), by norm_num⟩
  | 5 => ⟨((270979349/17179869184), (248114865/8589934592)), (55/17179869184), by norm_num⟩
  | 6 => ⟨((-290749625/68719476736), (-1064867921/137438953472)), (15/17179869184), by norm_num⟩
  | 7 => ⟨((534792537/549755813888), (979336459/549755813888)), (113/549755813888), by norm_num⟩
  | 8 => ⟨((-107589423/549755813888), (-788090613/2199023255552)), (93/2199023255552), by norm_num⟩
  | 9 => ⟨((307837327/8796093022208), (1127451477/17592186044416)), (135/17592186044416), by norm_num⟩
  | 10 => ⟨((-99089013/17592186044416), (-725825261/70368744177664)), (11/8796093022208), by norm_num⟩
  | 11 => ⟨((231967439/281474976710656), (424789343/281474976710656)), (105/562949953421312), by norm_num⟩
  | 12 => ⟨((-497782921/4503599627370496), (-911562765/4503599627370496)), (57/2251799813685248), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582665471740547/10141204801825835211973625643008), (-84288018551/316912650057057350374175801344)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((27818946802515/9903520314283042199192993792), (-199852851839/39614081257132168796771975168)), (23129/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945795314017251/19807040628566084398385987584), (-3597016920457/39614081257132168796771975168)), (26025/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891480607736161/2475880078570760549798248448), (-955359204445/618970019642690137449562112)), (55315/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443286533720391/38685626227668133590597632), (-3820993893801/154742504910672534362390528)), (1729/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1551385890072249/9671406556917033397649408), (-3581711139649/9671406556917033397649408)), (12971/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157548915388957/75557863725914323419136), (-391690822339/75557863725914323419136)), (45413/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945197448117377/37778931862957161709568), (-5091098117647/75557863725914323419136)), (18455/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324872583413521/1180591620717411303424), (-3817551267843/4722366482869645213696)), (13847/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((812064265516013/295147905179352825856), (-2623938921559/295147905179352825856)), (19049/147573952589676412928), by norm_num⟩
  | 8 => ⟨((228352759182343/9223372036854775808), (-819745544065/9223372036854775808)), (95301/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826418554191443/9223372036854775808), (-3687560236005/4611686018427387904)), (107291/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597661775447161/1152921504606846976), (-460742696465/72057594037927936)), (107387/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197791247728863/144115188075855872), (-3223377502743/72057594037927936)), (11759/18014398509481984), by norm_num⟩
  | 4 => ⟨((93527578796467/2251799813685248), (-1207855643871/4503599627370496)), (141323/36028797018963968), by norm_num⟩
  | 3 => ⟨((373810441194433/2251799813685248), (-12065799386287/9007199254740992)), (177033/9007199254740992), by norm_num⟩
  | 2 => ⟨((279981768255459/562949953421312), (-12046655513211/2251799813685248)), (88801/1125899906842624), by norm_num⟩
  | 1 => ⟨((1116903990763103/1125899906842624), (-18022094826243/1125899906842624)), (66957/281474976710656), by norm_num⟩
  | 0 => ⟨((1107762262765645/1125899906842624), (-4481558183415/140737488355328)), (541367/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1107762262765645/1125899906842624), (-4481558183415/140737488355328)), (2065151218894576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1088775142512667/1125899906842624), (-70549802927299/1125899906842624)), (1099771/1125899906842624), by norm_num⟩
  | 2 => ⟨((524226900227197/562949953421312), (-136447070062947/1125899906842624)), (1132421/562949953421312), by norm_num⟩
  | 3 => ⟨((959798968088509/1125899906842624), (-31765356826777/140737488355328)), (297941/70368744177664), by norm_num⟩
  | 4 => ⟨((95105660447735/140737488355328), (-216632803807953/562949953421312)), (5139741/562949953421312), by norm_num⟩
  | 5 => ⟨((347425607222017/1125899906842624), (-292786323268501/562949953421312)), (21804499/1125899906842624), by norm_num⟩
  | 6 => ⟨((-789380194343755/4503599627370496), (-361387244211147/1125899906842624)), (144549687/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-67504719/67108864), (-350982347/16777216)), (1/33554432), by norm_num⟩, -3, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-75151839/67108864), (-781485187/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-98663264695739/1125899906842624), (1415674136644213/4503599627370496)), (124582683/4503599627370496), by norm_num⟩
  | 1 => ⟨((337182691/2147483648), (-1209520121/2147483648)), (27/536870912), by norm_num⟩
  | 2 => ⟨((-75518785/536870912), (1083584565/2147483648)), (49/1073741824), by norm_num⟩
  | 3 => ⟨((180415331/2147483648), (-323587151/1073741824)), (119/4294967296), by norm_num⟩
  | 4 => ⟨((-161630439/4294967296), (289895171/2147483648)), (27/2147483648), by norm_num⟩
  | 5 => ⟨((463364591/34359738368), (-1662151737/34359738368)), (157/34359738368), by norm_num⟩
  | 6 => ⟨((-276745965/68719476736), (248181343/17179869184)), (3/2147483648), by norm_num⟩
  | 7 => ⟨((283349831/274877906944), (-1016414335/274877906944)), (25/68719476736), by norm_num⟩
  | 8 => ⟨((-253847371/1099511627776), (910585005/1099511627776)), (91/1099511627776), by norm_num⟩
  | 9 => ⟨((404296383/8796093022208), (-1450266049/8796093022208)), (147/8796093022208), by norm_num⟩
  | 10 => ⟨((-289760749/35184372088832), (1039411171/35184372088832)), (107/35184372088832), by norm_num⟩
  | 11 => ⟨((377586593/281474976710656), (-677227203/140737488355328)), (141/281474976710656), by norm_num⟩
  | 12 => ⟨((-451029569/2251799813685248), (1617904339/2251799813685248)), (85/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582517037882311/10141204801825835211973625643008), (2400280472181/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780237773054859/633825300114114700748351602688), (1422541575975/316912650057057350374175801344)), (1445/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1891394040739043/39614081257132168796771975168), (800097816551/9903520314283042199192993792)), (52029/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891271840520149/2475880078570760549798248448), (1700013102531/1237940039285380274899124224)), (55291/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886468743893595/77371252455336267181195264), (849896996695/38685626227668133590597632)), (55303/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551190411028215/9671406556917033397649408), (3186648139013/9671406556917033397649408)), (51859/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260220406530009/604462909807314587353088), (174240720775/37778931862957161709568)), (22695/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890117395952331/75557863725914323419136), (4529385780291/75557863725914323419136)), (18445/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324820604414093/1180591620717411303424), (3396275515381/4722366482869645213696)), (13839/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1623842986408093/590295810358705651712), (4668637664167/590295810358705651712)), (76147/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826465652313091/73786976294838206464), (2916967696203/36893488147419103232)), (95233/73786976294838206464), by norm_num⟩
  | 7 => ⟨((114126142554057/576460752303423488), (1640154401081/2305843009213693952)), (53603/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597262377270993/1152921504606846976), (3278709064105/576460752303423488)), (107291/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598721379140191/72057594037927936), (2867070839503/72057594037927936)), (93977/144115188075855872), by norm_num⟩
  | 4 => ⟨((186990061626129/4503599627370496), (4297007363207/18014398509481984)), (35289/9007199254740992), by norm_num⟩
  | 3 => ⟨((1494594243057287/9007199254740992), (5364961789705/4503599627370496)), (176783/9007199254740992), by norm_num⟩
  | 2 => ⟨((1119284701571535/2251799813685248), (5355516995125/1125899906842624)), (177289/2251799813685248), by norm_num⟩
  | 1 => ⟨((1115953285927585/1125899906842624), (8009668237077/562949953421312)), (133601/562949953421312), by norm_num⟩
  | 0 => ⟨((552956060997945/562949953421312), (15924936529471/562949953421312)), (269743/562949953421312), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((552956060997945/562949953421312), (15924936529471/562949953421312)), (1028987886668968023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1085378193689107/1125899906842624), (62568902414587/1125899906842624)), (1090341/1125899906842624), by norm_num⟩
  | 2 => ⟨((521418888415709/562949953421312), (15079253908613/140737488355328)), (2223385/1125899906842624), by norm_num⟩
  | 3 => ⟨((952978193501603/1125899906842624), (55867188643555/281474976710656)), (2297581/562949953421312), by norm_num⟩
  | 4 => ⟨((190565153217165/281474976710656), (94573615622459/281474976710656)), (9602923/1125899906842624), by norm_num⟩
  | 5 => ⟨((194482004536503/562949953421312), (1024456852939873/2251799813685248)), (38911675/2251799813685248), by norm_num⟩
  | 6 => ⟨((-98663264695739/1125899906842624), (1415674136644213/4503599627370496)), (124582683/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75151839/67108864), (-781485187/33554432)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-81617387/67108864), (-1697437611/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((658698693560765/2251799813685248), (-107010361575507/2251799813685248)), (5904221/562949953421312), by norm_num⟩
  | 1 => ⟨((-152798709/268435456), (99293017/1073741824)), (23/1073741824), by norm_num⟩
  | 2 => ⟨((1189330235/2147483648), (-96607645/1073741824)), (47/2147483648), by norm_num⟩
  | 3 => ⟨((-1542886517/4294967296), (250653063/4294967296)), (63/4294967296), by norm_num⟩
  | 4 => ⟨((750579633/4294967296), (-121937085/4294967296)), (63/8589934592), by norm_num⟩
  | 5 => ⟨((-1168448421/17179869184), (189822889/17179869184)), (51/17179869184), by norm_num⟩
  | 6 => ⟨((757898547/34359738368), (-246252191/68719476736)), (17/17179869184), by norm_num⟩
  | 7 => ⟨((-1685488543/274877906944), (273819793/274877906944)), (39/137438953472), by norm_num⟩
  | 8 => ⟨((1639904631/1099511627776), (-266414357/1099511627776)), (39/549755813888), by norm_num⟩
  | 9 => ⟨((-1418269807/4398046511104), (115204089/2199023255552)), (69/4398046511104), by norm_num⟩
  | 10 => ⟨((1103930245/17592186044416), (-179341445/17592186044416)), (55/17592186044416), by norm_num⟩
  | 11 => ⟨((-1562290231/140737488355328), (253805337/140737488355328)), (5/8796093022208), by norm_num⟩
  | 12 => ⟨((506679403/281474976710656), (-41156865/140737488355328)), (27/281474976710656), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791195769420077/5070602400912917605986812821504), (-209785905005/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((27813958054771/9903520314283042199192993792), (-248622441245/633825300114114700748351602688)), (46113/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891231797237801/39614081257132168796771975168), (-34958747991/4951760157141521099596496896)), (25939/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891099794369565/2475880078570760549798248448), (-74278120527/618970019642690137449562112)), (55121/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886382910636147/77371252455336267181195264), (-297071005007/154742504910672534362390528)), (27561/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775514938449445/4835703278458516698824704), (-278460005929/9671406556917033397649408)), (25839/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260080342243939/604462909807314587353088), (-30451056637/75557863725914323419136)), (45219/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944945273467779/37778931862957161709568), (-24736322381/4722366482869645213696)), (73483/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81194558849343/295147905179352825856), (-18547727009/295147905179352825856)), (27557/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623611029844183/590295810358705651712), (-50991580815/73786976294838206464)), (75785/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456544328774073/18446744073709551616), (-63717481315/9223372036854775808)), (94735/73786976294838206464), by norm_num⟩
  | 7 => ⟨((57053003482967/288230376151711744), (-71651936733/1152921504606846976)), (106583/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798471483871179/576460752303423488), (-572913351983/1152921504606846976)), (53295/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197166376280807/144115188075855872), (-125239871793/36028797018963968)), (23319/36028797018963968), by norm_num⟩
  | 4 => ⟨((1495512113869003/36028797018963968), (-187690093319/9007199254740992)), (69965/18014398509481984), by norm_num⟩
  | 3 => ⟨((93380911785097/562949953421312), (-117157958353/1125899906842624)), (87471/4503599627370496), by norm_num⟩
  | 2 => ⟨((2237602473205745/4503599627370496), (-467742933153/1125899906842624)), (349973/4503599627370496), by norm_num⟩
  | 1 => ⟨((1115268423778165/1125899906842624), (-2797585367805/2251799813685248)), (525185/2251799813685248), by norm_num⟩
  | 0 => ⟨((552351454493773/562949953421312), (-5559782260203/2251799813685248)), (65705/140737488355328), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((552351454493773/562949953421312), (-5559782260203/2251799813685248)), (250644684374761537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1083898117331873/1125899906842624), (-10910219636499/2251799813685248)), (258521/281474976710656), by norm_num⟩
  | 2 => ⟨((1043436777454731/1125899906842624), (-21006425974119/2251799813685248)), (4002071/2251799813685248), by norm_num⟩
  | 3 => ⟨((483457714334029/562949953421312), (-38935747824589/2251799813685248)), (1873143/562949953421312), by norm_num⟩
  | 4 => ⟨((415021993696771/562949953421312), (-33437763934007/1125899906842624)), (3282063/562949953421312), by norm_num⟩
  | 5 => ⟨((610937910884303/1125899906842624), (-98604910566661/2251799813685248)), (20136793/2251799813685248), by norm_num⟩
  | 6 => ⟨((658698693560765/2251799813685248), (-107010361575507/2251799813685248)), (5904221/562949953421312), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-81617387/67108864), (-1697437611/67108864)), (1/33554432), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-21804525/16777216), (-906959215/33554432)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((-196578613544191/2251799813685248), (-1163153685954579/4503599627370496)), (158189793/4503599627370496), by norm_num⟩
  | 1 => ⟨((389837013/2147483648), (36041589/67108864)), (159/2147483648), by norm_num⟩
  | 2 => ⟨((-50665205/268435456), (-599571019/1073741824)), (21/268435456), by norm_num⟩
  | 3 => ⟨((8779611/67108864), (831181923/2147483648)), (59/1073741824), by norm_num⟩
  | 4 => ⟨((-292107005/4294967296), (-432098555/2147483648)), (125/4294967296), by norm_num⟩
  | 5 => ⟨((485935553/17179869184), (1437637897/17179869184)), (211/17179869184), by norm_num⟩
  | 6 => ⟨((-336824859/34359738368), (-996494655/34359738368)), (37/8589934592), by norm_num⟩
  | 7 => ⟨((400232917/137438953472), (1184087075/137438953472)), (89/68719476736), by norm_num⟩
  | 8 => ⟨((-416130477/549755813888), (-615559963/274877906944)), (187/549755813888), by norm_num⟩
  | 9 => ⟨((384586223/2199023255552), (142224551/274877906944)), (11/137438953472), by norm_num⟩
  | 10 => ⟨((-319889827/8796093022208), (-946392447/8796093022208)), (149/8796093022208), by norm_num⟩
  | 11 => ⟨((241888071/35184372088832), (1431249287/70368744177664)), (57/17592186044416), by norm_num⟩
  | 12 => ⟨((-335328069/281474976710656), (-124008301/35184372088832)), (5/8796093022208), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791141413306961/5070602400912917605986812821504), (-1235364121695/5070602400912917605986812821504)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1779959943307133/633825300114114700748351602688), (-1463859069951/316912650057057350374175801344)), (34683/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472770375763369/9903520314283042199192993792), (-1646647196069/19807040628566084398385987584)), (78051/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890939791481957/2475880078570760549798248448), (-3498660273371/2475880078570760549798248448)), (82945/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886302731905211/77371252455336267181195264), (-3498137133385/154742504910672534362390528)), (82963/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550879165198595/9671406556917033397649408), (-819736939759/2417851639229258349412352)), (77797/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629974046550565/302231454903657293676544), (-2868523522417/604462909807314587353088)), (17023/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944837468345125/37778931862957161709568), (-2330154369757/37778931862957161709568)), (27671/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162368827132739/590295810358705651712), (-3494319896583/4722366482869645213696)), (83045/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623386831943541/590295810358705651712), (-2401604280243/295147905179352825856)), (57119/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825895566424529/73786976294838206464), (-6001789012293/73786976294838206464)), (71437/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825377081893829/9223372036854775808), (-6748958236793/9223372036854775808)), (160839/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596621363262865/1152921504606846976), (-6745140864571/1152921504606846976)), (80485/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196882079650239/144115188075855872), (-1474426145359/36028797018963968)), (70499/72057594037927936), by norm_num⟩
  | 4 => ⟨((1495079893674231/36028797018963968), (-4418985849855/18014398509481984)), (105897/18014398509481984), by norm_num⟩
  | 3 => ⟨((746772114750919/4503599627370496), (-11032445489035/9007199254740992)), (16579/562949953421312), by norm_num⟩
  | 2 => ⟨((1118235797507223/2251799813685248), (-5504963329431/1125899906842624)), (266047/2251799813685248), by norm_num⟩
  | 1 => ⟨((557191362364015/562949953421312), (-16458627652711/1125899906842624)), (401029/1125899906842624), by norm_num⟩
  | 0 => ⟨((275695576387137/281474976710656), (-32692415866163/1125899906842624)), (809913/1125899906842624), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((275695576387137/281474976710656), (-32692415866163/1125899906842624)), (3089572910789107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((539595043925003/562949953421312), (-64042314105775/1125899906842624)), (816801/562949953421312), by norm_num⟩
  | 2 => ⟨((515387655982771/562949953421312), (-122770825658465/1125899906842624)), (1658751/562949953421312), by norm_num⟩
  | 3 => ⟨((232575085440345/281474976710656), (-112398211732031/562949953421312)), (3398963/562949953421312), by norm_num⟩
  | 4 => ⟨((723799059691205/1125899906842624), (-185743144931785/562949953421312)), (27896841/2251799813685248), by norm_num⟩
  | 5 => ⟨((685465933353541/2251799813685248), (-955258724713653/2251799813685248)), (54276587/2251799813685248), by norm_num⟩
  | 6 => ⟨((-196578613544191/2251799813685248), (-1163153685954579/4503599627370496)), (158189793/4503599627370496), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21804525/16777216), (-906959215/33554432)), (3/67108864), by norm_num⟩, -4, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile033Terms0

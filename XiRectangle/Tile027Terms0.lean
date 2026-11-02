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
namespace Reinmann.XiRectangle.Tile027Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨27,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (7473/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (7473/640))
  have he : value ((5/8), (7473/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-232581599/536870912), (-2172602865/268435456)), (1/268435456), by norm_num⟩
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
  | 0 => ⟨((-346497555447725/2251799813685248), (-354600579700897/562949953421312)), (7602281/1125899906842624), by norm_num⟩
  | 1 => ⟨((57261897/536870912), (1875231873/4294967296)), (21/4294967296), by norm_num⟩
  | 2 => ⟨((-1270109519/34359738368), (-5199246743/34359738368)), (15/8589934592), by norm_num⟩
  | 3 => ⟨((1173830443/137438953472), (4805124295/137438953472)), (57/137438953472), by norm_num⟩
  | 4 => ⟨((-406818631/274877906944), (-6661316715/1099511627776)), (81/1099511627776), by norm_num⟩
  | 5 => ⟨((902352599/4398046511104), (230863645/274877906944)), (47/4398046511104), by norm_num⟩
  | 6 => ⟨((-26060965/1099511627776), (-6827626011/70368744177664)), (89/70368744177664), by norm_num⟩
  | 7 => ⟨((660629373/281474976710656), (5408628251/562949953421312)), (73/562949953421312), by norm_num⟩
  | 8 => ⟨((-915826775/4503599627370496), (-3748975423/4503599627370496)), (13/1125899906842624), by norm_num⟩
  | 9 => ⟨((1128538217/72057594037927936), (4619718657/72057594037927936)), (33/36028797018963968), by norm_num⟩
  | 10 => ⟨((-1251588933/1152921504606846976), (-1280857985/288230376151711744)), (75/1152921504606846976), by norm_num⟩
  | 11 => ⟨((630934793/9223372036854775808), (80711191/288230376151711744)), (39/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-145776891/36893488147419103232), (-1193487669/73786976294838206464)), (37/147573952589676412928), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583411453610655/10141204801825835211973625643008), (-589559124391/2535301200456458802993406410752)), (2427/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1781298685191125/633825300114114700748351602688), (-2798410473453/633825300114114700748351602688)), (5781/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946293742124023/19807040628566084398385987584), (-787020241831/9903520314283042199192993792)), (813/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((236567472977469/309485009821345068724781056), (-3344687182761/2475880078570760549798248448)), (27/9671406556917033397649408), by norm_num⟩
  | 14 => ⟨((887102664637873/77371252455336267181195264), (-836129918351/38685626227668133590597632)), (6913/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1552378904182929/9671406556917033397649408), (-3135309158755/9671406556917033397649408)), (6483/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78828764357795/37778931862957161709568), (-685804353865/151115727451828646838272)), (2837/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((945903452696439/37778931862957161709568), (-4457394230869/75557863725914323419136)), (9223/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162568671466673/590295810358705651712), (-1671376613971/2361183241434822606848)), (865/590295810358705651712), by norm_num⟩
  | 9 => ⟨((203198094838841/73786976294838206464), (-4595810212651/590295810358705651712)), (9519/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914321216420429/36893488147419103232), (-2872024555413/36893488147419103232)), (93/576460752303423488), by norm_num⟩
  | 7 => ⟨((1828466560193875/9223372036854775808), (-6461073257275/9223372036854775808)), (1675/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1599709906877325/1152921504606846976), (-6459844692217/1152921504606846976)), (6705/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199583501508405/144115188075855872), (-2825490246769/72057594037927936)), (5873/72057594037927936), by norm_num⟩
  | 4 => ⟨((187391239144179/4503599627370496), (-4236849913995/18014398509481984)), (8821/18014398509481984), by norm_num⟩
  | 3 => ⟨((1498603042763417/9007199254740992), (-5293633699527/4503599627370496)), (11047/4503599627370496), by norm_num⟩
  | 2 => ⟨((35102781831325/70368744177664), (-10579964763025/2251799813685248)), (5539/562949953421312), by norm_num⟩
  | 1 => ⟨((1121948486857641/1125899906842624), (-3962908175475/281474976710656)), (33389/1125899906842624), by norm_num⟩
  | 0 => ⟨((1117857019381605/1125899906842624), (-15814830648781/562949953421312)), (8425/140737488355328), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1117857019381605/1125899906842624), (-15814830648781/562949953421312)), (32138824999761537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1108983021242451/1125899906842624), (-62807428417497/1125899906842624)), (137625/1125899906842624), by norm_num⟩
  | 2 => ⟨((544408326570263/562949953421312), (-123727466890431/1125899906842624)), (143235/562949953421312), by norm_num⟩
  | 3 => ⟨((1039358126758051/1125899906842624), (-119652311526503/562949953421312)), (617031/1125899906842624), by norm_num⟩
  | 4 => ⟨((908605291488363/1125899906842624), (-441821165859071/1125899906842624)), (1401501/1125899906842624), by norm_num⟩
  | 5 => ⟨((34991877901879/70368744177664), (-44568909584165/70368744177664)), (420247/140737488355328), by norm_num⟩
  | 6 => ⟨((-346497555447725/2251799813685248), (-354600579700897/562949953421312)), (7602281/1125899906842624), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-232581599/536870912), (-2172602865/268435456)), (1/268435456), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-368633113/536870912), (-1721747035/134217728)), (3/536870912), by norm_num⟩
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
  | 0 => ⟨((1094689112832501/2251799813685248), (-146569635228153/1125899906842624)), (4070077/1125899906842624), by norm_num⟩
  | 1 => ⟨((-573462921/1073741824), (307127385/2147483648)), (9/2147483648), by norm_num⟩
  | 2 => ⟨((5040107297/17179869184), (-1349655677/17179869184)), (21/8589934592), by norm_num⟩
  | 3 => ⟨((-3691415875/34359738368), (988498875/34359738368)), (33/34359738368), by norm_num⟩
  | 4 => ⟨((4055434843/137438953472), (-1085977011/137438953472)), (19/68719476736), by norm_num⟩
  | 5 => ⟨((-891070111/137438953472), (119306769/68719476736)), (9/137438953472), by norm_num⟩
  | 6 => ⟨((5221016395/4398046511104), (-1398100081/4398046511104)), (55/4398046511104), by norm_num⟩
  | 7 => ⟨((-6555283167/35184372088832), (877697103/17592186044416)), (9/4398046511104), by norm_num⟩
  | 8 => ⟨((1800428661/70368744177664), (-964248823/140737488355328)), (21/70368744177664), by norm_num⟩
  | 9 => ⟨((-3516396537/1125899906842624), (470815825/562949953421312)), (43/1125899906842624), by norm_num⟩
  | 10 => ⟨((1545262579/4503599627370496), (-1655180963/18014398509481984)), (39/9007199254740992), by norm_num⟩
  | 11 => ⟨((-4938602061/144115188075855872), (82654643/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 12 => ⟨((3617072609/1152921504606846976), (-968591003/1152921504606846976)), (49/1152921504606846976), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583081351377037/10141204801825835211973625643008), (-340821092497/10141204801825835211973625643008)), (455/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1780911131973495/633825300114114700748351602688), (-50533497397/79228162514264337593543950336)), (8649/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946075879579849/19807040628566084398385987584), (-454773347285/39614081257132168796771975168)), (9729/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892077154995251/2475880078570760549798248448), (-483162812795/2475880078570760549798248448)), (5169/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886871535317035/77371252455336267181195264), (-120781178565/38685626227668133590597632)), (10339/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193993241246891/1208925819614629174706176), (-56611117997/1208925819614629174706176)), (2423/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260881770504883/604462909807314587353088), (-396237354893/604462909807314587353088)), (8481/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472798161578109/18889465931478580854784), (-643809828093/75557863725914323419136)), (13783/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162511165288769/590295810358705651712), (-482790991343/4722366482869645213696)), (10337/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812476619234449/295147905179352825856), (-331864882093/295147905179352825856)), (14215/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1827854603714863/73786976294838206464), (-1620118093/144115188075855872)), (17769/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456895603037539/2305843009213693952), (-932965678425/9223372036854775808)), (2499/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1598828457520359/1152921504606846976), (-466343913425/576460752303423488)), (9997/576460752303423488), by norm_num⟩
  | 5 => ⟨((1198815268013245/144115188075855872), (-101973671475/18014398509481984)), (8749/72057594037927936), by norm_num⟩
  | 4 => ⟨((1497983628966795/36028797018963968), (-1223059370043/36028797018963968)), (26251/36028797018963968), by norm_num⟩
  | 3 => ⟨((1497180795633533/9007199254740992), (-1527731606785/9007199254740992)), (32823/9007199254740992), by norm_num⟩
  | 2 => ⟨((560941334311369/1125899906842624), (-1526093892761/2251799813685248)), (65671/4503599627370496), by norm_num⟩
  | 1 => ⟨((2239757304355123/2251799813685248), (-142815670775/70368744177664)), (49287/1125899906842624), by norm_num⟩
  | 0 => ⟨((1113875795111667/1125899906842624), (-4553766084737/1125899906842624)), (197417/2251799813685248), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1113875795111667/1125899906842624), (-4553766084737/1125899906842624)), (753086098677825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1101961677596547/1125899906842624), (-9010267764589/1125899906842624)), (392215/2251799813685248), by norm_num⟩
  | 2 => ⟨((2156920604729973/2251799813685248), (-2204674172437/140737488355328)), (387015/1125899906842624), by norm_num⟩
  | 3 => ⟨((1032743265245233/1125899906842624), (-67576979024087/2251799813685248)), (376771/562949953421312), by norm_num⟩
  | 4 => ⟨((1892560756797011/2251799813685248), (-61985678787785/1125899906842624)), (1427617/1125899906842624), by norm_num⟩
  | 5 => ⟨((1583807449931449/2251799813685248), (-208387375190687/2251799813685248)), (319615/140737488355328), by norm_num⟩
  | 6 => ⟨((1094689112832501/2251799813685248), (-146569635228153/1125899906842624)), (4070077/1125899906842624), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-368633113/536870912), (-1721747035/134217728)), (3/536870912), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-232581599/268435456), (-2172602865/134217728)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-420065001018017/1125899906842624), (436515655716725/2251799813685248)), (650365/70368744177664), by norm_num⟩
  | 1 => ⟨((1110713467/2147483648), (-2308422821/8589934592)), (113/8589934592), by norm_num⟩
  | 2 => ⟨((-192471977/536870912), (800038385/4294967296)), (5/536870912), by norm_num⟩
  | 3 => ⟨((1423055021/8589934592), (-184848117/2147483648)), (19/4294967296), by norm_num⟩
  | 4 => ⟨((-3945546303/68719476736), (1025015609/34359738368)), (107/68719476736), by norm_num⟩
  | 5 => ⟨((4375750873/274877906944), (-1136778687/137438953472)), (121/274877906944), by norm_num⟩
  | 6 => ⟨((-1011013127/274877906944), (1050606589/549755813888)), (57/549755813888), by norm_num⟩
  | 7 => ⟨((1601784911/2199023255552), (-832257137/2199023255552)), (23/1099511627776), by norm_num⟩
  | 8 => ⟨((-1110272695/8796093022208), (36054793/549755813888)), (129/35184372088832), by norm_num⟩
  | 9 => ⟨((342036617/17592186044416), (-355431511/35184372088832)), (161/281474976710656), by norm_num⟩
  | 10 => ⟨((-1517322987/562949953421312), (788372319/562949953421312)), (91/1125899906842624), by norm_num⟩
  | 11 => ⟨((3059572801/9007199254740992), (-794848073/4503599627370496)), (47/4503599627370496), by norm_num⟩
  | 12 => ⟨((-2827645681/72057594037927936), (734595601/36028797018963968)), (11/9007199254740992), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197855892514491/1267650600228229401496703205376), (3468077388759/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((445156107848329/158456325028528675187087900672), (514059128977/79228162514264337593543950336)), (1447/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1891828707395333/39614081257132168796771975168), (1156537340259/9903520314283042199192993792)), (13027/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472933319725711/618970019642690137449562112), (4914846187603/2475880078570760549798248448)), (13845/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773398481902433/154742504910672534362390528), (1228588449767/38685626227668133590597632)), (13849/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551622121067695/9671406556917033397649408), (4606683377075/9671406556917033397649408)), (3247/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260597680972807/604462909807314587353088), (4030324480417/604462909807314587353088)), (11369/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890729582435087/75557863725914323419136), (6548295415631/75557863725914323419136)), (9241/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299740783809127/4722366482869645213696), (4910362079767/4722366482869645213696)), (13869/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((3172796841791/1152921504606846976), (3375175272883/295147905179352825856)), (9541/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1827250013454485/73786976294838206464), (1054480133123/9223372036854775808)), (11935/36893488147419103232), by norm_num⟩
  | 7 => ⟨((114181131061835/576460752303423488), (4743717900655/4611686018427387904)), (13439/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1598138957435141/1152921504606846976), (1185478283533/144115188075855872)), (26909/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1198206127863401/144115188075855872), (8294283434153/144115188075855872)), (23581/144115188075855872), by norm_num⟩
  | 4 => ⟨((1497058277259009/36028797018963968), (6216643252097/18014398509481984)), (2215/2251799813685248), by norm_num⟩
  | 3 => ⟨((748001882085671/4503599627370496), (15527344071601/9007199254740992)), (22211/4503599627370496), by norm_num⟩
  | 2 => ⟨((1120675185994455/2251799813685248), (15505905260729/2251799813685248)), (44605/2251799813685248), by norm_num⟩
  | 1 => ⟨((1117991516009075/1125899906842624), (11602555958789/562949953421312)), (33683/562949953421312), by norm_num⟩
  | 0 => ⟨((277449792351053/281474976710656), (46194350933571/1125899906842624)), (17071/140737488355328), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((277449792351053/281474976710656), (46194350933571/1125899906842624)), (65120697558355287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1092033377816031/1125899906842624), (22766878292499/281474976710656)), (140219/562949953421312), by norm_num⟩
  | 2 => ⟨((65738725924487/70368744177664), (176656492130321/1125899906842624)), (147343/281474976710656), by norm_num⟩
  | 3 => ⟨((477447852742047/562949953421312), (330066220582707/1125899906842624)), (160767/140737488355328), by norm_num⟩
  | 4 => ⟨((713102553346635/1125899906842624), (34991877901879/70368744177664)), (366959/140737488355328), by norm_num⟩
  | 5 => ⟨((346497555447713/2251799813685248), (1418402318803579/2251799813685248)), (13276599/2251799813685248), by norm_num⟩
  | 6 => ⟨((-420065001018017/1125899906842624), (436515655716725/2251799813685248)), (650365/70368744177664), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-232581599/268435456), (-2172602865/134217728)), (1/134217728), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-270018875/268435456), (-5044627631/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((1644376466057581/4503599627370496), (93589496025003/4503599627370496)), (13181659/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1261959947/2147483648), (-287297217/8589934592)), (21/4294967296), by norm_num⟩
  | 2 => ⟨((8124184731/17179869184), (462387033/17179869184)), (35/8589934592), by norm_num⟩
  | 3 => ⟨((-4358456971/17179869184), (-124030537/8589934592)), (39/17179869184), by norm_num⟩
  | 4 => ⟨((7014665889/68719476736), (399238897/68719476736)), (1/1073741824), by norm_num⟩
  | 5 => ⟨((-2257933845/68719476736), (-257020087/137438953472)), (43/137438953472), by norm_num⟩
  | 6 => ⟨((605667389/68719476736), (275771915/549755813888)), (3/34359738368), by norm_num⟩
  | 7 => ⟨((-4456155695/2199023255552), (-126810793/1099511627776)), (23/1099511627776), by norm_num⟩
  | 8 => ⟨((7171905919/17592186044416), (102047049/4398046511104)), (19/4398046511104), by norm_num⟩
  | 9 => ⟨((-5130105463/70368744177664), (-291979359/70368744177664)), (7/8796093022208), by norm_num⟩
  | 10 => ⟨((3302634491/281474976710656), (46992265/70368744177664)), (37/281474976710656), by norm_num⟩
  | 11 => ⟨((-7731469325/4503599627370496), (-220017841/2251799813685248)), (89/4503599627370496), by norm_num⟩
  | 12 => ⟨((1036943321/4503599627370496), (59017509/4503599627370496)), (25/9007199254740992), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197833183968175/1267650600228229401496703205376), (74058094551/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780418045274989/633825300114114700748351602688), (21949622337/158456325028528675187087900672)), (11527/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891597083746341/39614081257132168796771975168), (1543194079/618970019642690137449562112)), (1621/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((945743934708517/1237940039285380274899124224), (26231606297/618970019642690137449562112)), (6889/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886576924613135/77371252455336267181195264), (1639286069/2417851639229258349412352)), (13779/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775696801538451/4835703278458516698824704), (98344292051/9671406556917033397649408)), (6459/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260398552629853/604462909807314587353088), (43019192841/302231454903657293676544)), (11303/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((945203772522283/37778931862957161709568), (69894125237/37778931862957161709568)), (18367/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324875152035815/1180591620717411303424), (104820082109/4722366482869645213696)), (13775/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624143938095959/590295810358705651712), (36023331233/147573952589676412928)), (9471/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826843250584175/73786976294838206464), (11254077483/4611686018427387904)), (23677/73786976294838206464), by norm_num⟩
  | 7 => ⟨((28538203347167/144115188075855872), (202502722297/9223372036854775808)), (26637/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399422881833387/288230376151711744), (25301802449/144115188075855872)), (13319/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197820980063701/144115188075855872), (88506664269/72057594037927936)), (23309/144115188075855872), by norm_num⟩
  | 4 => ⟨((748246624174279/18014398509481984), (33165193171/4503599627370496)), (8741/9007199254740992), by norm_num⟩
  | 3 => ⟨((186914957281037/1125899906842624), (331304940473/9007199254740992)), (43707/9007199254740992), by norm_num⟩
  | 2 => ⟨((280006071506205/562949953421312), (165392518337/1125899906842624)), (43711/2251799813685248), by norm_num⟩
  | 1 => ⟨((2234195910959067/2251799813685248), (989759667843/2251799813685248)), (131153/2251799813685248), by norm_num⟩
  | 0 => ⟨((1108341851971231/1125899906842624), (1969161991379/2251799813685248)), (65597/562949953421312), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1108341851971231/1125899906842624), (1969161991379/2251799813685248)), (250232698680686773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2182113496884741/2251799813685248), (3876907059131/2251799813685248)), (129263/562949953421312), by norm_num⟩
  | 2 => ⟨((2114577083602057/2251799813685248), (7513857287387/2251799813685248)), (1003883/2251799813685248), by norm_num⟩
  | 3 => ⟨((992845757706561/1125899906842624), (14111938665953/2251799813685248)), (1892115/2251799813685248), by norm_num⟩
  | 4 => ⟨((437735586397231/562949953421312), (12444248687077/1125899906842624)), (1680371/1125899906842624), by norm_num⟩
  | 5 => ⟨((340303303344991/562949953421312), (38705326917285/2251799813685248)), (5300747/2251799813685248), by norm_num⟩
  | 6 => ⟨((1644376466057581/4503599627370496), (93589496025003/4503599627370496)), (13181659/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-270018875/268435456), (-5044627631/268435456)), (1/134217728), by norm_num⟩, -3, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-75151839/67108864), (-5616096935/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-706187572880243/4503599627370496), (-1288869042951823/4503599627370496)), (16154493/2251799813685248), by norm_num⟩
  | 1 => ⟨((1206701537/4294967296), (2202361405/4294967296)), (7/536870912), by norm_num⟩
  | 2 => ⟨((-1081059453/4294967296), (-1973050951/4294967296)), (51/4294967296), by norm_num⟩
  | 3 => ⟨((1291332341/8589934592), (4713643633/17179869184)), (31/4294967296), by norm_num⟩
  | 4 => ⟨((-1156878475/17179869184), (-4222857807/34359738368)), (113/34359738368), by norm_num⟩
  | 5 => ⟨((829139185/34359738368), (3026538185/68719476736)), (41/34359738368), by norm_num⟩
  | 6 => ⟨((-1980823981/274877906944), (-451902371/34359738368)), (25/68719476736), by norm_num⟩
  | 7 => ⟨((507022875/274877906944), (3701487325/1099511627776)), (13/137438953472), by norm_num⟩
  | 8 => ⟨((-1816926075/4398046511104), (-3316087483/4398046511104)), (95/4398046511104), by norm_num⟩
  | 9 => ⟨((2893772889/35184372088832), (2640724955/17592186044416)), (153/35184372088832), by norm_num⟩
  | 10 => ⟨((-1036988995/70368744177664), (-3785235155/140737488355328)), (111/140737488355328), by norm_num⟩
  | 11 => ⟨((2702596147/1125899906842624), (4932531587/1125899906842624)), (147/1125899906842624), by norm_num⟩
  | 12 => ⟨((-1614134079/4503599627370496), (-736492515/1125899906842624)), (45/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582517037882311/10141204801825835211973625643008), (-674764397515/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890118315422081/316912650057057350374175801344), (-3199227492213/633825300114114700748351602688)), (5783/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891392688111215/39614081257132168796771975168), (-1799380299661/19807040628566084398385987584)), (13013/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891270319048233/2475880078570760549798248448), (-1911622428717/1237940039285380274899124224)), (13829/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443233967875349/38685626227668133590597632), (-955687937585/38685626227668133590597632)), (13833/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775594397527667/4835703278458516698824704), (-3583305827829/9671406556917033397649408)), (3243/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630109445943951/302231454903657293676544), (-3134868647915/604462909807314587353088)), (5677/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1890114745993587/75557863725914323419136), (-636647389467/9444732965739290427392)), (2307/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((649640132594139/2361183241434822606848), (-3819024676263/4722366482869645213696)), (1731/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1623839758796879/590295810358705651712), (-5249761929167/590295810358705651712)), (9525/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456615304030109/18446744073709551616), (-6560106819427/73786976294838206464)), (11913/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1826012738283251/9223372036854775808), (-922154823251/1152921504606846976)), (26823/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798628072761491/576460752303423488), (-3686818192673/576460752303423488)), (839/36028797018963968), by norm_num⟩
  | 5 => ⟨((598718265551419/72057594037927936), (-1611969766051/36028797018963968)), (23519/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495909605731923/36028797018963968), (-9663712316293/36028797018963968)), (8833/9007199254740992), by norm_num⟩
  | 3 => ⟨((747288966354445/4503599627370496), (-6032726389225/4503599627370496)), (44259/9007199254740992), by norm_num⟩
  | 2 => ⟨((1119264349628843/2251799813685248), (-12044168161097/2251799813685248)), (22201/1125899906842624), by norm_num⟩
  | 1 => ⟨((1115912690020515/1125899906842624), (-18013029804081/1125899906842624)), (66959/1125899906842624), by norm_num⟩
  | 0 => ⟨((1105790874161587/1125899906842624), (-35813106710751/1125899906842624)), (135347/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1105790874161587/1125899906842624), (-35813106710751/1125899906842624)), (516307835105514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((271225459595297/281474976710656), (-70346939964103/1125899906842624)), (137235/562949953421312), by norm_num⟩
  | 2 => ⟨((260250333941185/281474976710656), (-135570709310333/1125899906842624)), (281625/562949953421312), by norm_num⟩
  | 3 => ⟨((946180346376005/1125899906842624), (-31336997326521/140737488355328)), (73575/70368744177664), by norm_num⟩
  | 4 => ⟨((739327509592073/1125899906842624), (-421358251185091/1125899906842624)), (1251411/562949953421312), by norm_num⟩
  | 5 => ⟨((655586501703913/2251799813685248), (-1106747570015701/2251799813685248)), (5160299/1125899906842624), by norm_num⟩
  | 6 => ⟨((-706187572880243/4503599627370496), (-1288869042951823/4503599627370496)), (16154493/2251799813685248), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75151839/67108864), (-5616096935/268435456)), (1/134217728), by norm_num⟩, -3, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-326469549/268435456), (-6099267347/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-994211227102229/4503599627370496), (111305096480669/562949953421312)), (467911/70368744177664), by norm_num⟩
  | 1 => ⟨((3690043863/8589934592), (-3304896803/8589934592)), (113/8589934592), by norm_num⟩
  | 2 => ⟨((-1795123451/4294967296), (3215516115/8589934592)), (7/536870912), by norm_num⟩
  | 3 => ⟨((2328765961/8589934592), (-1042850907/4294967296)), (37/4294967296), by norm_num⟩
  | 4 => ⟨((-2265784659/17179869184), (507323541/4294967296)), (73/17179869184), by norm_num⟩
  | 5 => ⟨((3527210691/68719476736), (-3159059287/68719476736)), (115/68719476736), by norm_num⟩
  | 6 => ⟨((-285984795/17179869184), (2049081843/137438953472)), (19/34359738368), by norm_num⟩
  | 7 => ⟨((2544003269/549755813888), (-2278473803/549755813888)), (43/274877906944), by norm_num⟩
  | 8 => ⟨((-1237600445/1099511627776), (2216852649/2199023255552)), (85/2199023255552), by norm_num⟩
  | 9 => ⟨((4281349807/17592186044416), (-1917242697/8796093022208)), (149/17592186044416), by norm_num⟩
  | 10 => ⟨((-208278051/4398046511104), (1492312809/35184372088832)), (59/35184372088832), by norm_num⟩
  | 11 => ⟨((2358053081/281474976710656), (-1055966051/140737488355328)), (85/281474976710656), by norm_num⟩
  | 12 => ⟨((-3059039615/2251799813685248), (42808647/35184372088832)), (7/140737488355328), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791195769417651/5070602400912917605986812821504), (785214222603/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((890042976379049/316912650057057350374175801344), (1861153416559/316912650057057350374175801344)), (2893/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945611540104877/19807040628566084398385987584), (2093562384441/19807040628566084398385987584)), (13021/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1891089989331729/2475880078570760549798248448), (4448265887605/2475880078570760549798248448)), (6919/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772755405364291/154742504910672534362390528), (4447642345697/154742504910672534362390528)), (6921/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1551019463178565/9671406556917033397649408), (4169002149105/9671406556917033397649408)), (12981/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630035290852643/302231454903657293676544), (1823607144579/302231454903657293676544)), (5681/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472468367660167/18889465931478580854784), (370342548349/4722366482869645213696)), (18471/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299099071456589/4722366482869645213696), (4443023352321/4722366482869645213696)), (3465/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811795116133977/295147905179352825856), (6107390200875/590295810358705651712)), (4767/147573952589676412928), by norm_num⟩
  | 8 => ⟨((28533573918977/1152921504606846976), (7631587103519/73786976294838206464)), (23851/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825660399677607/9223372036854775808), (33523009337/36028797018963968)), (26855/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199612852190973/144115188075855872), (8577333325967/1152921504606846976)), (26883/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197126257976749/144115188075855872), (3750019511273/72057594037927936)), (11777/72057594037927936), by norm_num⟩
  | 4 => ⟨((1495441978613435/36028797018963968), (11239800923879/36028797018963968)), (17697/18014398509481984), by norm_num⟩
  | 3 => ⟨((186748691147055/1125899906842624), (14031795129261/9007199254740992)), (44353/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118670163370791/2251799813685248), (3501212696487/562949953421312)), (44519/2251799813685248), by norm_num⟩
  | 1 => ⟨((278751757455761/281474976710656), (20939879754221/1125899906842624)), (67193/1125899906842624), by norm_num⟩
  | 0 => ⟨((275980621561539/281474976710656), (41609964410897/1125899906842624)), (136051/1125899906842624), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((275980621561539/281474976710656), (41609964410897/1125899906842624)), (518993381980514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1080836279589209/1125899906842624), (81595486571991/1125899906842624)), (17303/70368744177664), by norm_num⟩
  | 2 => ⟨((1031662968251477/1125899906842624), (78329664654701/562949953421312)), (571663/1125899906842624), by norm_num⟩
  | 3 => ⟨((923515783492391/1125899906842624), (143547066393189/562949953421312)), (301679/281474976710656), by norm_num⟩
  | 4 => ⟨((342152244882855/562949953421312), (470976081203887/1125899906842624)), (1297507/562949953421312), by norm_num⟩
  | 5 => ⟨((109447635686583/562949953421312), (1145007811018955/2251799813685248)), (10650927/2251799813685248), by norm_num⟩
  | 6 => ⟨((-994211227102229/4503599627370496), (111305096480669/562949953421312)), (467911/70368744177664), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-326469549/268435456), (-6099267347/268435456)), (1/134217728), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-348872399/268435456), (-6517808595/268435456)), (3/268435456), by norm_num⟩
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
  | 0 => ⟨((808471341900725/4503599627370496), (924052597484897/4503599627370496)), (26885181/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3206575191/8589934592), (-916248969/2147483648)), (109/8589934592), by norm_num⟩
  | 2 => ⟨((1666971415/4294967296), (1905286169/4294967296)), (29/2147483648), by norm_num⟩
  | 3 => ⟨((-2310913073/8589934592), (-2641287473/8589934592)), (83/8589934592), by norm_num⟩
  | 4 => ⟨((1201352161/8589934592), (343275181/2147483648)), (89/17179869184), by norm_num⟩
  | 5 => ⟨((-249814159/4294967296), (-4568452299/68719476736)), (151/68719476736), by norm_num⟩
  | 6 => ⟨((43289495/2147483648), (3166609831/137438953472)), (107/137438953472), by norm_num⟩
  | 7 => ⟨((-3292085915/549755813888), (-3762731445/549755813888)), (65/274877906944), by norm_num⟩
  | 8 => ⟨((3422850105/2199023255552), (3912190039/2199023255552)), (69/1099511627776), by norm_num⟩
  | 9 => ⟨((-197711575/549755813888), (-3615631327/8796093022208)), (65/4398046511104), by norm_num⟩
  | 10 => ⟨((2631229839/35184372088832), (375924699/4398046511104)), (55/17592186044416), by norm_num⟩
  | 11 => ⟨((-3979264461/281474976710656), (-4548150899/281474976710656)), (85/140737488355328), by norm_num⟩
  | 12 => ⟨((1379107971/562949953421312), (3152537973/1125899906842624)), (15/140737488355328), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582282826618775/10141204801825835211973625643008), (1109840891195/10141204801825835211973625643008)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779963596394091/633825300114114700748351602688), (657559429749/316912650057057350374175801344)), (17313/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891085827184511/39614081257132168796771975168), (1479337237015/39614081257132168796771975168)), (9739/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472736163819969/618970019642690137449562112), (392896823639/618970019642690137449562112)), (20697/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221576328820687/19342813113834066795298816), (392838187641/38685626227668133590597632)), (20699/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775442165397435/4835703278458516698824704), (1472894043169/9671406556917033397649408)), (1213/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1259952934616655/604462909807314587353088), (644266587551/302231454903657293676544)), (2123/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1889683406880979/75557863725914323419136), (2093399424869/75557863725914323419136)), (27603/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649478748392409/2361183241434822606848), (196205132329/590295810358705651712)), (10353/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623397147491587/590295810358705651712), (134849551077/36893488147419103232)), (7119/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1825909743745989/73786976294838206464), (2695995897065/73786976294838206464)), (35603/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912697396856625/4611686018427387904), (3031627629179/9223372036854775808)), (20033/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596641275545335/1152921504606846976), (757479686707/288230376151711744)), (2505/72057594037927936), by norm_num⟩
  | 5 => ⟨((1196901975047363/144115188075855872), (2649257526075/144115188075855872)), (35087/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495114672647839/36028797018963968), (3970046321055/36028797018963968)), (52663/36028797018963968), by norm_num⟩
  | 3 => ⟨((746798161035303/4503599627370496), (4955844223613/9007199254740992)), (65887/9007199254740992), by norm_num⟩
  | 2 => ⟨((1118300780521685/2251799813685248), (9891572460809/4503599627370496)), (65975/2251799813685248), by norm_num⟩
  | 1 => ⟨((2229024586239995/2251799813685248), (7393578151857/1125899906842624)), (49591/562949953421312), by norm_num⟩
  | 0 => ⟨((1103169025693619/1125899906842624), (29374027849757/2251799813685248)), (398491/2251799813685248), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1103169025693619/1125899906842624), (29374027849757/2251799813685248)), (1520122536666106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2161410945106075/2251799813685248), (57561986614931/2251799813685248)), (791289/2251799813685248), by norm_num⟩
  | 2 => ⟨((2073178913573627/2251799813685248), (110502813913947/2251799813685248)), (389877/562949953421312), by norm_num⟩
  | 3 => ⟨((1903304152418983/2251799813685248), (101737331313665/1125899906842624)), (3024665/2251799813685248), by norm_num⟩
  | 4 => ⟨((1590356627849249/2251799813685248), (171984280279713/1125899906842624)), (5659741/2251799813685248), by norm_num⟩
  | 5 => ⟨((1070663483689099/2251799813685248), (485862621297749/2251799813685248)), (9723583/2251799813685248), by norm_num⟩
  | 6 => ⟨((808471341900725/4503599627370496), (924052597484897/4503599627370496)), (26885181/4503599627370496), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-348872399/268435456), (-6517808595/268435456)), (3/268435456), by norm_num⟩, -4, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile027Terms0

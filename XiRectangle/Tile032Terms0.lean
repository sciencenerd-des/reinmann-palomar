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
namespace Reinmann.XiRectangle.Tile032Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨32,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (8037/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (8037/640))
  have he : value ((7/8), (8037/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-10175445/16777216), (-584143223/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-461386457987813/1125899906842624), (-404965817584051/1125899906842624)), (27282843/1125899906842624), by norm_num⟩
  | 1 => ⟨((304993365/1073741824), (267697253/1073741824)), (19/1073741824), by norm_num⟩
  | 2 => ⟨((-211405291/2147483648), (-742214385/8589934592)), (55/8589934592), by norm_num⟩
  | 3 => ⟨((781519901/34359738368), (2679499/134217728)), (53/34359738368), by norm_num⟩
  | 4 => ⟨((-135427079/34359738368), (-950931035/274877906944)), (19/68719476736), by norm_num⟩
  | 5 => ⟨((600773747/1099511627776), (527308133/1099511627776)), (11/274877906944), by norm_num⟩
  | 6 => ⟨((-1110465677/17592186044416), (-974672389/17592186044416)), (21/4398046511104), by norm_num⟩
  | 7 => ⟨((219918901/35184372088832), (386052239/70368744177664)), (69/140737488355328), by norm_num⟩
  | 8 => ⟨((-609744665/1125899906842624), (-267591021/562949953421312)), (49/1125899906842624), by norm_num⟩
  | 9 => ⟨((375682485/9007199254740992), (164871077/4503599627370496)), (63/18014398509481984), by norm_num⟩
  | 10 => ⟨((-833290417/288230376151711744), (-365695751/144115188075855872)), (9/36028797018963968), by norm_num⟩
  | 11 => ⟨((210033783/1152921504606846976), (737399211/4611686018427387904)), (37/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-776449731/73786976294838206464), (-681501579/73786976294838206464)), (35/36893488147419103232), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583185728209367/10141204801825835211973625643008), (-3153918523697/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222628447170005/79228162514264337593543950336), (-1870771092663/316912650057057350374175801344)), (23143/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((946141152269389/19807040628566084398385987584), (-4208987141073/39614081257132168796771975168)), (26041/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892215304340095/2475880078570760549798248448), (-558971225191/309485009821345068724781056)), (27675/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773880595546965/154742504910672534362390528), (-2235727868845/77371252455336267181195264)), (27683/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((388018549061297/2417851639229258349412352), (-523956991169/1208925819614629174706176)), (12981/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78812083768369/37778931862957161709568), (-1833682482575/302231454903657293676544)), (22725/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891372704019085/75557863725914323419136), (-2979420776967/37778931862957161709568)), (18471/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((325055819521047/1180591620717411303424), (-2234291325237/2361183241434822606848)), (3465/590295810358705651712), by norm_num⟩
  | 9 => ⟨((406283915253355/147573952589676412928), (-1535852304389/147573952589676412928)), (38137/590295810358705651712), by norm_num⟩
  | 8 => ⟨((914039991447733/36893488147419103232), (-7677922599815/73786976294838206464)), (47703/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913916161462813/4611686018427387904), (-8635820231313/9223372036854775808)), (26855/4611686018427387904), by norm_num⟩
  | 6 => ⟨((799536909826193/576460752303423488), (-8633514353287/1152921504606846976)), (53767/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599512422951041/72057594037927936), (-7551727496967/144115188075855872)), (47109/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498287775971443/36028797018963968), (-5661193754077/18014398509481984)), (35395/18014398509481984), by norm_num⟩
  | 3 => ⟨((1497543112988657/9007199254740992), (-14143858494531/9007199254740992)), (88709/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122218223022099/2251799813685248), (-7065065514911/1125899906842624)), (44521/1125899906842624), by norm_num⟩
  | 1 => ⟨((1120315204854301/1125899906842624), (-10580371503475/562949953421312)), (33599/281474976710656), by norm_num⟩
  | 0 => ⟨((1114482557241629/1125899906842624), (-42182865204867/1125899906842624)), (136065/562949953421312), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1114482557241629/1125899906842624), (-42182865204867/1125899906842624)), (519046785594749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((550800283729091/562949953421312), (-83510207611857/1125899906842624)), (559133/1125899906842624), by norm_num⟩
  | 2 => ⟨((1071631543901941/1125899906842624), (-40853938940165/281474976710656)), (1177077/1125899906842624), by norm_num⟩
  | 3 => ⟨((996260369005979/1125899906842624), (-311078236314619/1125899906842624)), (645593/281474976710656), by norm_num⟩
  | 4 => ⟨((49724949366021/70368744177664), (-275259742555295/562949953421312)), (5997043/1125899906842624), by norm_num⟩
  | 5 => ⟨((146507858029223/562949953421312), (-1556063211986159/2251799813685248)), (28680105/2251799813685248), by norm_num⟩
  | 6 => ⟨((-461386457987813/1125899906842624), (-404965817584051/1125899906842624)), (27282843/1125899906842624), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-10175445/16777216), (-584143223/67108864)), (1/67108864), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-64510795/67108864), (-57865319/4194304)), (3/134217728), by norm_num⟩
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
  | 0 => ⟨((287973984555051/2251799813685248), (-1623018706688013/4503599627370496)), (90342749/4503599627370496), by norm_num⟩
  | 1 => ⟨((-75428905/536870912), (850233219/2147483648)), (49/2147483648), by norm_num⟩
  | 2 => ⟨((41433561/536870912), (-934076663/4294967296)), (7/536870912), by norm_num⟩
  | 3 => ⟨((-60692559/2147483648), (1368250801/17179869184)), (85/17179869184), by norm_num⟩
  | 4 => ⟨((533420729/68719476736), (-187897143/8589934592)), (3/2147483648), by norm_num⟩
  | 5 => ⟨((-234409027/137438953472), (660563553/137438953472)), (87/274877906944), by norm_num⟩
  | 6 => ⟨((42920773/137438953472), (-241901079/274877906944)), (33/549755813888), by norm_num⟩
  | 7 => ⟨((-215557891/4398046511104), (1214882277/8796093022208)), (85/8796093022208), by norm_num⟩
  | 8 => ⟨((59203637/8796093022208), (-1334684599/70368744177664)), (3/2199023255552), by norm_num⟩
  | 9 => ⟨((-231259887/281474976710656), (325844645/140737488355328)), (3/17592186044416), by norm_num⟩
  | 10 => ⟨((203251963/2251799813685248), (-286381545/1125899906842624)), (43/2251799813685248), by norm_num⟩
  | 11 => ⟨((-324792879/36028797018963968), (228816207/9007199254740992)), (35/18014398509481984), by norm_num⟩
  | 12 => ⟨((475761931/576460752303423488), (-1340694917/576460752303423488)), (105/576460752303423488), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395680896270333/2535301200456458802993406410752), (-400486818985/2535301200456458802993406410752)), (29117/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890242511718609/316912650057057350374175801344), (-949652358081/316912650057057350374175801344)), (17323/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891672312781803/39614081257132168796771975168), (-534132937679/9903520314283042199192993792)), (38981/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945783825092869/1237940039285380274899124224), (-2269842003287/2475880078570760549798248448)), (20711/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886616730601959/77371252455336267181195264), (-2269591160569/154742504910672534362390528)), (10357/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387867015004229/2417851639229258349412352), (-2127475210589/9671406556917033397649408)), (38845/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630231761610613/302231454903657293676544), (-930637163501/302231454903657293676544)), (8499/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1890512786320155/75557863725914323419136), (-189004448127/4722366482869645213696)), (27627/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1299579245279447/4722366482869645213696), (-2267616260505/4722366482869645213696)), (41451/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812125793465195/295147905179352825856), (-3117262123521/590295810358705651712)), (57011/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913488548094357/36893488147419103232), (-3895512443293/73786976294838206464)), (71289/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826594607450885/9223372036854775808), (-2190493531249/4611686018427387904)), (40117/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597839892706737/1152921504606846976), (-136848651907/36028797018963968)), (80277/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197949419773611/144115188075855872), (-1914851874867/72057594037927936)), (70291/144115188075855872), by norm_num⟩
  | 4 => ⟨((374170787825635/9007199254740992), (-5740439800651/36028797018963968)), (26383/9007199254740992), by norm_num⟩
  | 3 => ⟨((186944027556755/1125899906842624), (-7168349723917/9007199254740992)), (132083/9007199254740992), by norm_num⟩
  | 2 => ⟨((280062409662815/562949953421312), (-7157555019653/2251799813685248)), (8271/140737488355328), by norm_num⟩
  | 1 => ⟨((139677251679563/140737488355328), (-5354682236127/562949953421312)), (199137/1125899906842624), by norm_num⟩
  | 0 => ⟨((1082920313721/1099511627776), (-10655484576403/562949953421312)), (100203/281474976710656), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((1082920313721/1099511627776), (-10655484576403/562949953421312)), (382244111181163699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((545886944800457/562949953421312), (-41978785521961/1125899906842624)), (402351/562949953421312), by norm_num⟩
  | 2 => ⟨((1057117067287203/1125899906842624), (-40706408865917/562949953421312)), (810315/562949953421312), by norm_num⟩
  | 3 => ⟨((986649381803471/1125899906842624), (-76439191971879/562949953421312)), (819405/281474976710656), by norm_num⟩
  | 4 => ⟨((421931468579791/562949953421312), (-267940981418531/1125899906842624)), (6634585/1125899906842624), by norm_num⟩
  | 5 => ⟨((1137423110698547/2251799813685248), (-803287973259837/2251799813685248)), (3275761/281474976710656), by norm_num⟩
  | 6 => ⟨((287973984555051/2251799813685248), (-1623018706688013/4503599627370496)), (90342749/4503599627370496), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-64510795/67108864), (-57865319/4194304)), (3/134217728), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-10175445/8388608), (-584143223/33554432)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((173657178248115/4503599627370496), (663809431178341/2251799813685248)), (50949837/2251799813685248), by norm_num⟩
  | 1 => ⟨((-229587523/4294967296), (-1755209487/4294967296)), (137/4294967296), by norm_num⟩
  | 2 => ⟨((19892243/536870912), (1216618507/4294967296)), (97/4294967296), by norm_num⟩
  | 3 => ⟨((-73537345/4294967296), (-1124394251/8589934592)), (23/2147483648), by norm_num⟩
  | 4 => ⟨((203888813/34359738368), (779370705/17179869184)), (65/17179869184), by norm_num⟩
  | 5 => ⟨((-226119929/137438953472), (-864349771/68719476736)), (147/137438953472), by norm_num⟩
  | 6 => ⟨((52244797/137438953472), (798828809/274877906944)), (69/274877906944), by norm_num⟩
  | 7 => ⟨((-165546669/2199023255552), (-632806785/1099511627776)), (7/137438953472), by norm_num⟩
  | 8 => ⟨((114748207/8796093022208), (438628239/4398046511104)), (79/8796093022208), by norm_num⟩
  | 9 => ⟨((-141399815/70368744177664), (-1081009519/70368744177664)), (99/70368744177664), by norm_num⟩
  | 10 => ⟨((156817413/562949953421312), (37464935/17592186044416)), (7/35184372088832), by norm_num⟩
  | 11 => ⟨((-39526381/1125899906842624), (-37772675/140737488355328)), (115/4503599627370496), by norm_num⟩
  | 12 => ⟨((146120531/36028797018963968), (139637457/4503599627370496)), (27/9007199254740992), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582395689313353/10141204801825835211973625643008), (469178334123/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780095626872097/633825300114114700748351602688), (556037715383/158456325028528675187087900672)), (23105/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472808560806591/9903520314283042199192993792), (312737001929/4951760157141521099596496896)), (51993/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236387775015233/309485009821345068724781056), (1328967525691/1237940039285380274899124224)), (55251/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886384004931735/77371252455336267181195264), (2657564431107/154742504910672534362390528)), (13815/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387757924513787/2417851639229258349412352), (2491072909091/9671406556917033397649408)), (6477/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1260081705204121/604462909807314587353088), (1089647547103/302231454903657293676544)), (45349/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472473082416639/18889465931478580854784), (3540616431387/75557863725914323419136)), (73709/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299113900773133/4722366482869645213696), (2654816582091/4722366482869645213696)), (27649/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623611735075541/590295810358705651712), (1824661822621/295147905179352825856)), (76061/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913088638418839/36893488147419103232), (2280040564849/36893488147419103232)), (95115/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912847402391275/4611686018427387904), (2563964153069/4611686018427387904)), (107057/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596940083165539/1152921504606846976), (2562612673089/576460752303423488)), (26781/288230376151711744), by norm_num⟩
  | 5 => ⟨((299290519845027/36028797018963968), (2240766187075/72057594037927936)), (93809/144115188075855872), by norm_num⟩
  | 4 => ⟨((11683610377639/281474976710656), (1679055380135/9007199254740992)), (140863/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494075923946601/9007199254740992), (4192323929235/4503599627370496)), (88171/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118773323134711/2251799813685248), (8368715862223/2251799813685248)), (88369/1125899906842624), by norm_num⟩
  | 1 => ⟨((557601759749699/562949953421312), (3128321082021/281474976710656)), (266099/1125899906842624), by norm_num⟩
  | 0 => ⟨((1104481491366249/1125899906842624), (3108456783891/140737488355328)), (67021/140737488355328), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1104481491366249/1125899906842624), (3108456783891/140737488355328)), (255664825976324037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1082921276688667/1125899906842624), (48789175146445/1125899906842624)), (1075623/1125899906842624), by norm_num⟩
  | 2 => ⟨((1039469051183721/1125899906842624), (23463380499933/281474976710656)), (2162349/1125899906842624), by norm_num⟩
  | 3 => ⟨((59490602709435/70368744177664), (173297521156911/1125899906842624)), (2176605/562949953421312), by norm_num⟩
  | 4 => ⟨((1556063211986149/2251799813685248), (36626964507305/140737488355328)), (17401199/2251799813685248), by norm_num⟩
  | 5 => ⟨((461386457987809/1125899906842624), (50620727198005/140737488355328)), (33106865/2251799813685248), by norm_num⟩
  | 6 => ⟨((173657178248115/4503599627370496), (663809431178341/2251799813685248)), (50949837/2251799813685248), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-10175445/8388608), (-584143223/33554432)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-47253303/33554432), (-1356338561/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((228887289755223/4503599627370496), (-1077395784426203/4503599627370496)), (81733699/4503599627370496), by norm_num⟩
  | 1 => ⟨((-686161/8388608), (413418203/1073741824)), (127/4294967296), by norm_num⟩
  | 2 => ⟨((282709383/4294967296), (-1330741859/4294967296)), (13/536870912), by norm_num⟩
  | 3 => ⟨((-151667733/4294967296), (1427830933/8589934592)), (57/4294967296), by norm_num⟩
  | 4 => ⟨((30512475/2147483648), (-574501309/8589934592)), (47/8589934592), by norm_num⟩
  | 5 => ⟨((-157145389/34359738368), (369849675/17179869184)), (123/68719476736), by norm_num⟩
  | 6 => ⟨((84305249/68719476736), (-1587333571/274877906944)), (67/137438953472), by norm_num⟩
  | 7 => ⟨((-310135003/1099511627776), (1459837045/1099511627776)), (125/1099511627776), by norm_num⟩
  | 8 => ⟨((62392879/1099511627776), (-1174758543/4398046511104)), (51/2199023255552), by norm_num⟩
  | 9 => ⟨((-357039875/35184372088832), (1680623055/35184372088832)), (37/8796093022208), by norm_num⟩
  | 10 => ⟨((57463351/35184372088832), (-1081943385/140737488355328)), (97/140737488355328), by norm_num⟩
  | 11 => ⟨((-134521739/562949953421312), (1266415057/1125899906842624)), (115/1125899906842624), by norm_num⟩
  | 12 => ⟨((72168129/2251799813685248), (-1358810937/9007199254740992)), (125/9007199254740992), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582141353606259/10141204801825835211973625643008), (-1773458359385/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((13904644819025/4951760157141521099596496896), (-525275974259/158456325028528675187087900672)), (11551/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890895574378193/39614081257132168796771975168), (-2363443942675/39614081257132168796771975168)), (25993/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472685608411387/618970019642690137449562112), (-1255399010919/1237940039285380274899124224)), (55243/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886204160602515/77371252455336267181195264), (-627597940977/38685626227668133590597632)), (55251/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550694572610839/9671406556917033397649408), (-147066293367/604462909807314587353088)), (51807/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259786803103761/604462909807314587353088), (-2058496594615/604462909807314587353088)), (45341/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889413268727023/75557863725914323419136), (-3344248033833/75557863725914323419136)), (73695/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((39634849263/144115188075855872), (-39179349423/73786976294838206464)), (55287/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811559055093977/295147905179352825856), (-1723316542949/295147905179352825856)), (76043/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825560576083909/73786976294838206464), (-4306567366215/73786976294838206464)), (95091/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825001470564847/9223372036854775808), (-2421259308917/4611686018427387904)), (26757/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1596247316447285/1152921504606846976), (-4839557759345/1152921504606846976)), (107091/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196556546713527/144115188075855872), (-4231283761949/144115188075855872)), (5861/9007199254740992), by norm_num⟩
  | 4 => ⟨((747297552599171/18014398509481984), (-6340271308427/36028797018963968)), (70403/18014398509481984), by norm_num⟩
  | 3 => ⟨((186618047063501/1125899906842624), (-7913703545219/9007199254740992)), (176257/9007199254740992), by norm_num⟩
  | 2 => ⟨((2235290240757123/4503599627370496), (-7896269147395/2251799813685248)), (353261/4503599627370496), by norm_num⟩
  | 1 => ⟨((2227039136264873/2251799813685248), (-23601768344197/2251799813685248)), (265883/1125899906842624), by norm_num⟩
  | 0 => ⟨((2202293891700473/2251799813685248), (-23428088730753/1125899906842624)), (1071051/2251799813685248), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2202293891700473/2251799813685248), (-23428088730753/1125899906842624)), (4085735329634856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2152901361209785/2251799813685248), (-22913021127537/562949953421312)), (1069791/1125899906842624), by norm_num⟩
  | 2 => ⟨((2054616106807523/2251799813685248), (-175253498379757/2251799813685248)), (2132697/1125899906842624), by norm_num⟩
  | 3 => ⟨((1861059554312731/2251799813685248), (-79953523922741/562949953421312)), (2111927/562949953421312), by norm_num⟩
  | 4 => ⟨((1492700011994007/2251799813685248), (-528637647780487/2251799813685248)), (16363253/2251799813685248), by norm_num⟩
  | 5 => ⟨((865394672880281/2251799813685248), (-43803706394475/140737488355328)), (459017/35184372088832), by norm_num⟩
  | 6 => ⟨((228887289755223/4503599627370496), (-1077395784426203/4503599627370496)), (81733699/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47253303/33554432), (-1356338561/67108864)), (1/33554432), by norm_num⟩, -3, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-105212575/67108864), (-1509988327/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((-3202305403353/17592186044416), (457944448699775/4503599627370496)), (83748505/4503599627370496), by norm_num⟩
  | 1 => ⟨((350205141/1073741824), (-195628715/1073741824)), (73/2147483648), by norm_num⟩
  | 2 => ⟨((-1254966755/4294967296), (701039205/4294967296)), (133/4294967296), by norm_num⟩
  | 3 => ⟨((93691607/536870912), (-209348939/2147483648)), (81/4294967296), by norm_num⟩
  | 4 => ⟨((-20984103/268435456), (11721967/268435456)), (147/17179869184), by norm_num⟩
  | 5 => ⟨((962520711/34359738368), (-268837701/17179869184)), (107/34359738368), by norm_num⟩
  | 6 => ⟨((-574868533/68719476736), (321128331/68719476736)), (65/68719476736), by norm_num⟩
  | 7 => ⟨((1177172729/549755813888), (-328791273/274877906944)), (135/549755813888), by norm_num⟩
  | 8 => ⟨((-131825649/274877906944), (589114877/2199023255552)), (123/2199023255552), by norm_num⟩
  | 9 => ⟨((419910853/4398046511104), (-469134293/8796093022208)), (25/2199023255552), by norm_num⟩
  | 10 => ⟨((-300951699/17592186044416), (336230325/35184372088832)), (73/35184372088832), by norm_num⟩
  | 11 => ⟨((784338991/281474976710656), (-438140995/281474976710656)), (97/281474976710656), by norm_num⟩
  | 12 => ⟨((-234224469/562949953421312), (523362185/2251799813685248)), (59/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790966773092659/5070602400912917605986812821504), (428585573031/1267650600228229401496703205376)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779541914049535/633825300114114700748351602688), (2030532003317/316912650057057350374175801344)), (11575/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890611037462187/39614081257132168796771975168), (2284021140495/19807040628566084398385987584)), (13025/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945219841261025/1237940039285380274899124224), (4852765977215/2475880078570760549798248448)), (13843/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772105085867845/154742504910672534362390528), (4851889589759/154742504910672534362390528)), (55389/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193801221909681/1208925819614629174706176), (4547715344577/9671406556917033397649408)), (6493/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((314884272884585/151115727451828646838272), (3978319798369/604462909807314587353088)), (22735/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889006524523411/75557863725914323419136), (6463023844983/75557863725914323419136)), (1155/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1298448840601305/4722366482869645213696), (4845740323029/4722366482869645213696)), (27735/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405674032689669/147573952589676412928), (1665102682611/147573952589676412928)), (38159/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825031053635673/73786976294838206464), (4160895110347/36893488147419103232)), (23867/18446744073709551616), by norm_num⟩
  | 7 => ⟨((114025184065709/576460752303423488), (4678447409949/4611686018427387904)), (26875/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199455660022125/144115188075855872), (9350496168405/1152921504606846976)), (53811/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196025822511343/144115188075855872), (8174486114281/144115188075855872)), (94307/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493791151791903/36028797018963968), (12247334253325/36028797018963968)), (141735/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491925707402507/9007199254740992), (7641989678693/4503599627370496)), (44413/2251799813685248), by norm_num⟩
  | 2 => ⟨((1116605940341907/2251799813685248), (15246202123673/2251799813685248)), (178377/2251799813685248), by norm_num⟩
  | 1 => ⟨((1111909800721101/1125899906842624), (22774879914509/1125899906842624)), (33673/140737488355328), by norm_num⟩
  | 0 => ⟨((1097725098673567/1125899906842624), (45172191368833/1125899906842624)), (273029/562949953421312), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1097725098673567/1125899906842624), (45172191368833/1125899906842624)), (1041522981883811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((534221496100087/562949953421312), (88083581722127/1125899906842624)), (1108605/1125899906842624), by norm_num⟩
  | 2 => ⟨((1007027093014179/1125899906842624), (167177002230719/1125899906842624)), (2277523/1125899906842624), by norm_num⟩
  | 3 => ⟨((875881958952485/1125899906842624), (74763204771611/281474976710656)), (4750471/1125899906842624), by norm_num⟩
  | 4 => ⟨((150487759457117/281474976710656), (232644986841011/562949953421312)), (9914725/1125899906842624), by norm_num⟩
  | 5 => ⟨((64770541078897/562949953421312), (497525190022461/1125899906842624)), (18796345/1125899906842624), by norm_num⟩
  | 6 => ⟨((-3202305403353/17592186044416), (457944448699775/4503599627370496)), (83748505/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-105212575/67108864), (-1509988327/67108864)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-57132171/33554432), (-1639897353/67108864)), (1/33554432), by norm_num⟩
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
  | 0 => ⟨((157374769443221/1125899906842624), (526321598413653/4503599627370496)), (21963625/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1168202061/4294967296), (-488364477/2147483648)), (21/1073741824), by norm_num⟩
  | 2 => ⟨((1136608123/4294967296), (59394587/268435456)), (21/1073741824), by norm_num⟩
  | 3 => ⟨((-737245761/4294967296), (-308204079/2147483648)), (7/536870912), by norm_num⟩
  | 4 => ⟨((179326751/2147483648), (599737445/8589934592)), (7/1073741824), by norm_num⟩
  | 5 => ⟨((-1116651983/34359738368), (-933628145/34359738368)), (89/34359738368), by norm_num⟩
  | 6 => ⟨((181075369/17179869184), (302792747/34359738368)), (15/17179869184), by norm_num⟩
  | 7 => ⟨((-805386053/274877906944), (-673379977/274877906944)), (69/274877906944), by norm_num⟩
  | 8 => ⟨((783604447/1099511627776), (327584233/549755813888)), (69/1099511627776), by norm_num⟩
  | 9 => ⟨((-677699487/4398046511104), (-566621763/4398046511104)), (61/4398046511104), by norm_num⟩
  | 10 => ⟨((131874231/4398046511104), (6891219/274877906944)), (97/35184372088832), by norm_num⟩
  | 11 => ⟨((-186629385/35184372088832), (-1219063/274877906944)), (71/140737488355328), by norm_num⟩
  | 12 => ⟨((242109343/281474976710656), (404853259/562949953421312)), (47/562949953421312), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581757847530181/10141204801825835211973625643008), (907095025183/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779342029511341/633825300114114700748351602688), (1074158770653/633825300114114700748351602688)), (23077/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890386675959027/39614081257132168796771975168), (151030898191/4951760157141521099596496896)), (25963/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945100971809615/1237940039285380274899124224), (1283539622583/2475880078570760549798248448)), (55175/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771868072451047/154742504910672534362390528), (641644401293/77371252455336267181195264)), (13795/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775094172834933/4835703278458516698824704), (1202816821741/9671406556917033397649408)), (6467/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((157418013837449/75557863725914323419136), (526099181051/302231454903657293676544)), (22637/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888694373682029/75557863725914323419136), (427330768971/18889465931478580854784)), (36789/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298215989258683/4722366482869645213696), (160194451105/590295810358705651712)), (6899/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1622378008965227/590295810358705651712), (13761168917/4611686018427387904)), (18975/147573952589676412928), by norm_num⟩
  | 8 => ⟨((456159117948169/18446744073709551616), (1100361764551/36893488147419103232)), (47447/36893488147419103232), by norm_num⟩
  | 7 => ⟨((113997703607487/576460752303423488), (2474352495105/9223372036854775808)), (53391/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398802714391533/288230376151711744), (2472526901571/1152921504606846976)), (53407/576460752303423488), by norm_num⟩
  | 5 => ⟨((149456452018679/18014398509481984), (540352241051/36028797018963968)), (93499/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493241645639621/36028797018963968), (404751698555/4503599627370496)), (140321/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491259427916327/9007199254740992), (4040351880039/9007199254740992)), (175529/9007199254740992), by norm_num⟩
  | 2 => ⟨((557985230156135/1125899906842624), (4029623488143/2251799813685248)), (175721/2251799813685248), by norm_num⟩
  | 1 => ⟨((1111033211085275/1125899906842624), (6017681571785/1125899906842624)), (528129/2251799813685248), by norm_num⟩
  | 0 => ⟨((1096276235578521/1125899906842624), (23857503030321/2251799813685248)), (1060133/2251799813685248), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1096276235578521/1125899906842624), (23857503030321/2251799813685248)), (4044086464888762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((266826403101717/281474976710656), (11614892875215/562949953421312)), (65217/70368744177664), by norm_num⟩
  | 2 => ⟨((505640705896399/562949953421312), (88083427508121/2251799813685248)), (4042787/2251799813685248), by norm_num⟩
  | 3 => ⟨((453304248043569/562949953421312), (39558193576799/562949953421312)), (7578733/2251799813685248), by norm_num⟩
  | 4 => ⟨((1448937969536857/2251799813685248), (254827585781823/2251799813685248)), (3317589/562949953421312), by norm_num⟩
  | 5 => ⟨((903492454669229/2251799813685248), (81985388417015/562949953421312)), (10040669/1125899906842624), by norm_num⟩
  | 6 => ⟨((157374769443221/1125899906842624), (526321598413653/4503599627370496)), (21963625/2251799813685248), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-57132171/33554432), (-1639897353/67108864)), (1/33554432), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-30526335/16777216), (-876214835/33554432)), (3/67108864), by norm_num⟩
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
  | 0 => ⟨((812713767364429/9007199254740992), (-1213021847317875/9007199254740992)), (34552477/2251799813685248), by norm_num⟩
  | 1 => ⟨((-201462599/1073741824), (75173617/268435456)), (35/1073741824), by norm_num⟩
  | 2 => ⟨((837859395/4294967296), (-78159571/268435456)), (37/1073741824), by norm_num⟩
  | 3 => ⟨((-580759877/4294967296), (216704345/1073741824)), (105/4294967296), by norm_num⟩
  | 4 => ⟨((603828107/8589934592), (-901248035/8589934592)), (111/8589934592), by norm_num⟩
  | 5 => ⟨((-125562525/4294967296), (749637041/17179869184)), (47/8589934592), by norm_num⟩
  | 6 => ⟨((348133241/34359738368), (-1039217603/68719476736)), (133/68719476736), by norm_num⟩
  | 7 => ⟨((-827340255/274877906944), (1234852717/274877906944)), (161/274877906944), by norm_num⟩
  | 8 => ⟨((26881339/34359738368), (-1283902019/1099511627776)), (85/549755813888), by norm_num⟩
  | 9 => ⟨((-397498119/2199023255552), (296644355/1099511627776)), (5/137438953472), by norm_num⟩
  | 10 => ⟨((661259281/17592186044416), (-123370919/2199023255552)), (135/17592186044416), by norm_num⟩
  | 11 => ⟨((-500018189/70368744177664), (373152893/35184372088832)), (13/8796093022208), by norm_num⟩
  | 12 => ⟨((173293099/140737488355328), (-1034599503/562949953421312)), (73/281474976710656), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790802825208669/5070602400912917605986812821504), (-159650650827/1267650600228229401496703205376)), (7279/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1779161212863933/633825300114114700748351602688), (-1512142336421/633825300114114700748351602688)), (34631/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890183254160627/39614081257132168796771975168), (-1700887376971/39614081257132168796771975168)), (77927/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889985802082119/2475880078570760549798248448), (-1806857315985/2475880078570760549798248448)), (41403/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771651924327881/154742504910672534362390528), (-1806479958139/154742504910672534362390528)), (82815/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549985699825881/9671406556917033397649408), (-1693174118913/9671406556917033397649408)), (77649/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629583394314581/302231454903657293676544), (-1481126625681/604462909807314587353088)), (67953/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888406212319127/75557863725914323419136), (-300759955263/9444732965739290427392)), (55221/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297999856908637/4722366482869645213696), (-1803902738511/4722366482869645213696)), (2589/147573952589676412928), by norm_num⟩
  | 9 => ⟨((12672506317671/4611686018427387904), (-2479299103395/590295810358705651712)), (56971/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824264944080397/73786976294838206464), (-774380981563/18446744073709551616)), (142467/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823545251703821/9223372036854775808), (-3482515764943/9223372036854775808)), (80165/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199349100655019/144115188075855872), (-3479769373637/1152921504606846976)), (80199/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195285768765927/144115188075855872), (-3041711155155/144115188075855872)), (70213/72057594037927936), by norm_num⟩
  | 4 => ⟨((373173193154169/9007199254740992), (-4556399242413/36028797018963968)), (26349/4503599627370496), by norm_num⟩
  | 3 => ⟨((186321645129081/1125899906842624), (-5684720787471/9007199254740992)), (16485/562949953421312), by norm_num⟩
  | 2 => ⟨((278820983902963/562949953421312), (-11337166074603/4503599627370496)), (528333/4503599627370496), by norm_num⟩
  | 1 => ⟨((1110002798987887/1125899906842624), (-16925267566505/2251799813685248)), (794535/2251799813685248), by norm_num⟩
  | 0 => ⟨((2188426055176489/2251799813685248), (-33529849534599/2251799813685248)), (199655/281474976710656), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((2188426055176489/2251799813685248), (-33529849534599/2251799813685248)), (761623383642101199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((531584148718069/562949953421312), (-32586198782731/1125899906842624)), (197009/140737488355328), by norm_num⟩
  | 2 => ⟨((501494387493539/562949953421312), (-61541196103135/1125899906842624)), (3067747/1125899906842624), by norm_num⟩
  | 3 => ⟨((1780263339292309/2251799813685248), (-219291709735795/2251799813685248)), (11602129/2251799813685248), by norm_num⟩
  | 4 => ⟨((346528217595105/562949953421312), (-173371091462367/1125899906842624)), (20604937/2251799813685248), by norm_num⟩
  | 5 => ⟨((799839638083649/2251799813685248), (-106719922333859/562949953421312)), (31712739/2251799813685248), by norm_num⟩
  | 6 => ⟨((812713767364429/9007199254740992), (-1213021847317875/9007199254740992)), (34552477/2251799813685248), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-30526335/16777216), (-876214835/33554432)), (3/67108864), by norm_num⟩, -4, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile032Terms0

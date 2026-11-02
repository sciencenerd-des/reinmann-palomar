/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 38 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile005Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨5,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (1551/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (1551/640))
  have he : value ((3/4), (1551/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-381061692393/549755813888), 0), (1/549755813888), by norm_num⟩
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
  | 0 => ⟨((-17862266831/34359738368), (-115434899395/68719476736)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-381061692393/549755813888), 0), (1/549755813888), by norm_num⟩
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
  | 0 => ⟨((-36414434230867/562949953421312), (-1330981778560049/2251799813685248)), (53391/2251799813685248), by norm_num⟩
  | 1 => ⟨((24648986737/549755813888), (450471810149/1099511627776)), (5/274877906944), by norm_num⟩
  | 2 => ⟨((-34170751321/2199023255552), (-312243265127/2199023255552)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((15790239957/4398046511104), (288574051829/8796093022208)), (17/8796093022208), by norm_num⟩
  | 4 => ⟨((-21889920613/35184372088832), (-25003036301/4398046511104)), (13/35184372088832), by norm_num⟩
  | 5 => ⟨((24276698809/281474976710656), (443668073407/562949953421312)), (31/562949953421312), by norm_num⟩
  | 6 => ⟨((-22436433777/2251799813685248), (-205018182791/2251799813685248)), (31/4503599627370496), by norm_num⟩
  | 7 => ⟨((8886714751/9007199254740992), (324817772263/36028797018963968)), (13/18014398509481984), by norm_num⟩
  | 8 => ⟨((-49278410193/576460752303423488), (-7035828845/9007199254740992)), (19/288230376151711744), by norm_num⟩
  | 9 => ⟨((15180973817/2305843009213693952), (69359856737/1152921504606846976)), (25/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-16836238719/36893488147419103232), (-38461271313/9223372036854775808)), (15/36893488147419103232), by norm_num⟩
  | 11 => ⟨((33949065889/1180591620717411303424), (155108781215/590295810358705651712)), (1/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-31375599071/18889465931478580854784), (-286701905011/18889465931478580854784)), (1/590295810358705651712), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((24739040482979/158456325028528675187087900672), (-2188125579203/10141204801825835211973625643008)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1781165345584779/633825300114114700748351602688), (-1298088703465/316912650057057350374175801344)), (3/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1892437520095757/39614081257132168796771975168), (-2920556529009/39614081257132168796771975168)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1892380497744965/2475880078570760549798248448), (-387865738147/309485009821345068724781056)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1774046100397531/154742504910672534362390528), (-3102739779497/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((776114843940899/4835703278458516698824704), (-1454310373033/4835703278458516698824704)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((315282431558591/151115727451828646838272), (-2544845312099/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891594951172657/75557863725914323419136), (-2067501294219/37778931862957161709568)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81274406611115/295147905179352825856), (-3100927185721/4722366482869645213696)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1625366480053635/590295810358705651712), (-1065811744859/147573952589676412928)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((914184913786735/36893488147419103232), (-2664133285105/36893488147419103232)), (3/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1828160213477397/9223372036854775808), (-2996605094045/4611686018427387904)), (27/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599403977937447/1152921504606846976), (-5991847322139/1152921504606846976)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299829070926207/36028797018963968), (-655166521333/18014398509481984)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498730026534893/36028797018963968), (-491182953527/2251799813685248)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((187263103718709/1125899906842624), (-9818279143133/9007199254740992)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((561396636842385/1125899906842624), (-4905098957737/1125899906842624)), (87/2251799813685248), by norm_num⟩
  | 1 => ⟨((70075690025621/70368744177664), (-7347527107613/562949953421312)), (33/281474976710656), by norm_num⟩
  | 0 => ⟨((279101703511131/281474976710656), (-7327225244541/281474976710656)), (33/140737488355328), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((279101703511131/281474976710656), (-7327225244541/281474976710656)), (125885546636537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1106230807196071/1125899906842624), (-58123562432717/1125899906842624)), (539/1125899906842624), by norm_num⟩
  | 2 => ⟨((135488092998215/140737488355328), (-114216325974069/1125899906842624)), (279/281474976710656), by norm_num⟩
  | 3 => ⟨((128986168958593/140737488355328), (-27489037171849/140737488355328)), (297/140737488355328), by norm_num⟩
  | 4 => ⟨((902774935296941/1125899906842624), (-100775014094471/281474976710656)), (1321/281474976710656), by norm_num⟩
  | 5 => ⟨((289773950767255/562949953421312), (-646431579047291/1125899906842624)), (6129/562949953421312), by norm_num⟩
  | 6 => ⟨((-36414434230867/562949953421312), (-1330981778560049/2251799813685248)), (53391/2251799813685248), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/34359738368), (-115434899395/68719476736)), (1/68719476736), by norm_num⟩, 0, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-75496061613/68719476736), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-28311023105/34359738368), (-365919973631/137438953472)), (3/137438953472), by norm_num⟩
  | 1 => ⟨((-75496061613/68719476736), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-876589859855049/2251799813685248), (-227721378351207/1125899906842624)), (31929/1125899906842624), by norm_num⟩
  | 1 => ⟨((235115330117/549755813888), (30539246173/137438953472)), (19/549755813888), by norm_num⟩
  | 2 => ⟨((-258300590921/1099511627776), (-134203164529/1099511627776)), (23/1099511627776), by norm_num⟩
  | 3 => ⟨((23647683613/274877906944), (98291497153/2199023255552)), (9/1099511627776), by norm_num⟩
  | 4 => ⟨((-103918543263/4398046511104), (-26996061661/2199023255552)), (11/4398046511104), by norm_num⟩
  | 5 => ⟨((182665901839/35184372088832), (94906256277/35184372088832)), (11/17592186044416), by norm_num⟩
  | 6 => ⟨((-267572005975/281474976710656), (-139020239223/281474976710656)), (35/281474976710656), by norm_num⟩
  | 7 => ⟨((167975939353/1125899906842624), (87273910391/1125899906842624)), (47/2251799813685248), by norm_num⟩
  | 8 => ⟨((-92270215587/4503599627370496), (-23970047609/2251799813685248)), (7/2251799813685248), by norm_num⟩
  | 9 => ⟨((360423796345/144115188075855872), (187262498583/144115188075855872)), (29/72057594037927936), by norm_num⟩
  | 10 => ⟨((-158386404717/576460752303423488), (-20572888215/144115188075855872)), (53/1152921504606846976), by norm_num⟩
  | 11 => ⟨((126549273149/4611686018427387904), (32875094991/2305843009213693952)), (45/9223372036854775808), by norm_num⟩
  | 12 => ⟨((-185371448805/73786976294838206464), (-96311955595/73786976294838206464)), (35/73786976294838206464), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197862808528795/1267650600228229401496703205376), (-3468096989903/10141204801825835211973625643008)), (29/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222586255261629/79228162514264337593543950336), (-4112783983169/633825300114114700748351602688)), (35/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891902512709045/39614081257132168796771975168), (-1156629112057/9903520314283042199192993792)), (39/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472952922534969/618970019642690137449562112), (-4915257476815/2475880078570760549798248448)), (21/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1773476885355849/154742504910672534362390528), (-4914789001723/154742504910672534362390528)), (21/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775847808012951/4835703278458516698824704), (-1151779195227/2417851639229258349412352)), (39/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630330990385719/302231454903657293676544), (-4030729102603/604462909807314587353088)), (35/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1890834054042343/75557863725914323419136), (-3274500262069/37778931862957161709568)), (55/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649909561936303/2361183241434822606848), (-4910932542935/4722366482869645213696)), (41/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1624579678374615/590295810358705651712), (-6751202554281/590295810358705651712)), (57/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913692299644757/36893488147419103232), (-8437007455573/73786976294838206464)), (71/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456762365007231/2305843009213693952), (-4744443651345/4611686018427387904)), (5/576460752303423488), by norm_num⟩
  | 6 => ⟨((799145131383635/576460752303423488), (-2371362945317/288230376151711744)), (5/72057594037927936), by norm_num⟩
  | 5 => ⟨((1198338454865945/144115188075855872), (-259246917013/4503599627370496)), (35/72057594037927936), by norm_num⟩
  | 4 => ⟨((187157079604017/4503599627370496), (-12436104099919/36028797018963968)), (105/36028797018963968), by norm_num⟩
  | 3 => ⟨((748125741575725/4503599627370496), (-15531548846935/9007199254740992)), (131/9007199254740992), by norm_num⟩
  | 2 => ⟨((560461278268265/1125899906842624), (-15511132207481/2251799813685248)), (33/562949953421312), by norm_num⟩
  | 1 => ⟨((559180845638413/562949953421312), (-23215500746175/1125899906842624)), (199/1125899906842624), by norm_num⟩
  | 0 => ⟨((555267970647505/562949953421312), (-11556319983295/281474976710656)), (401/1125899906842624), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((555267970647505/562949953421312), (-11556319983295/281474976710656)), (1529697898482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1093483792760613/1125899906842624), (-45594492414675/562949953421312)), (825/1125899906842624), by norm_num⟩
  | 2 => ⟨((527307697096159/562949953421312), (-177127072101491/1125899906842624)), (1737/1125899906842624), by norm_num⟩
  | 3 => ⟨((239994608629817/281474976710656), (-10369535062085/35184372088832)), (1901/562949953421312), by norm_num⟩
  | 4 => ⟨((90089123179267/140737488355328), (-141462380093927/281474976710656)), (8725/1125899906842624), by norm_num⟩
  | 5 => ⟨((353924050358441/2251799813685248), (-1448850274018023/2251799813685248)), (39881/2251799813685248), by norm_num⟩
  | 6 => ⟨((-876589859855049/2251799813685248), (-227721378351207/1125899906842624)), (31929/1125899906842624), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-28311023105/34359738368), (-365919973631/137438953472)), (3/137438953472), by norm_num⟩, 0, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-381061692393/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-17862266831/17179869184), (-115434899395/34359738368)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-381061692393/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-388643854550441/1125899906842624), (344378381369745/4503599627370496)), (16425/562949953421312), by norm_num⟩
  | 1 => ⟨((263073625023/549755813888), (-14569391119/137438953472)), (3/68719476736), by norm_num⟩
  | 2 => ⟨((-364697482929/1099511627776), (80789859013/1099511627776)), (35/1099511627776), by norm_num⟩
  | 3 => ⟨((337052042733/2199023255552), (-37332841995/1099511627776)), (17/1099511627776), by norm_num⟩
  | 4 => ⟨((-116813336561/2199023255552), (25877154171/2199023255552)), (25/4398046511104), by norm_num⟩
  | 5 => ⟨((259100271645/17592186044416), (-57397364655/17592186044416)), (15/8796093022208), by norm_num⟩
  | 6 => ⟨((-239459497031/70368744177664), (53046428643/70368744177664)), (29/70368744177664), by norm_num⟩
  | 7 => ⟨((379384400515/562949953421312), (-84043388463/562949953421312)), (3/35184372088832), by norm_num⟩
  | 8 => ⟨((-262969227565/2251799813685248), (29127218879/1125899906842624)), (35/2251799813685248), by norm_num⟩
  | 9 => ⟨((324046895397/18014398509481984), (-17946177461/4503599627370496)), (45/18014398509481984), by norm_num⟩
  | 10 => ⟨((-179689753531/72057594037927936), (79611790777/144115188075855872)), (13/36028797018963968), by norm_num⟩
  | 11 => ⟨((22645717461/72057594037927936), (-20066432115/288230376151711744)), (27/576460752303423488), by norm_num⟩
  | 12 => ⟨((-41858173893/1152921504606846976), (9272660563/1152921504606846976)), (13/2305843009213693952), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582621414715929/10141204801825835211973625643008), (476037403185/1267650600228229401496703205376)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780354946730343/633825300114114700748351602688), (2257310899693/316912650057057350374175801344)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236440682132231/4951760157141521099596496896), (5078446914041/39614081257132168796771975168)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891410970064891/2475880078570760549798248448), (5395273575233/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773076054616117/154742504910672534362390528), (2697312508315/77371252455336267181195264)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551319719724953/9671406556917033397649408), (5056771683469/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630166477068359/302231454903657293676544), (1105996438853/151115727451828646838272)), (23/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472574791481389/18889465931478580854784), (7187683680381/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299417765665041/4722366482869645213696), (2694815407351/2361183241434822606848)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((406006874771667/147573952589676412928), (3704451086083/295147905179352825856)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1826693908324913/73786976294838206464), (578647877727/4611686018427387904)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1826271792026443/9223372036854775808), (10411862270533/9223372036854775808)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1597511795817215/1152921504606846976), (10407109520635/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1197656400062255/144115188075855872), (1137608675657/18014398509481984)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((748115884332355/18014398509481984), (13640589832363/36028797018963968)), (35/9007199254740992), by norm_num⟩
  | 3 => ⟨((1494967287092077/9007199254740992), (17031961682585/9007199254740992)), (175/9007199254740992), by norm_num⟩
  | 2 => ⟨((1119633723360087/2251799813685248), (17003747220249/2251799813685248)), (11/140737488355328), by norm_num⟩
  | 1 => ⟨((1116416950734257/1125899906842624), (12717453450655/562949953421312)), (33/140737488355328), by norm_num⟩
  | 0 => ⟨((1106601108871207/1125899906842624), (50585898673003/1125899906842624)), (67/140737488355328), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((1106601108871207/1125899906842624), (50585898673003/1125899906842624)), (255585253667787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((542680159037103/562949953421312), (12429704280235/140737488355328)), (1103/1125899906842624), by norm_num⟩
  | 2 => ⟨((1037498244601771/1125899906842624), (95857244212739/562949953421312)), (1161/562949953421312), by norm_num⟩
  | 3 => ⟨((923393061995193/1125899906842624), (353323495272235/1125899906842624)), (5071/1125899906842624), by norm_num⟩
  | 4 => ⟨((323215789523643/562949953421312), (579547901534513/1125899906842624)), (11501/1125899906842624), by norm_num⟩
  | 5 => ⟨((72828868461725/1125899906842624), (1330981778560045/2251799813685248)), (25047/1125899906842624), by norm_num⟩
  | 6 => ⟨((-388643854550441/1125899906842624), (344378381369745/4503599627370496)), (16425/562949953421312), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/17179869184), (-115434899395/34359738368)), (1/34359738368), by norm_num⟩, -1, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-221199462363/137438953472), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-41474899193/34359738368), (-268031536035/68719476736)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-221199462363/137438953472), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-977406437483319/4503599627370496), (463354756322077/2251799813685248)), (59181/2251799813685248), by norm_num⟩
  | 1 => ⟨((48006438487/137438953472), (-91032801725/274877906944)), (25/549755813888), by norm_num⟩
  | 2 => ⟨((-38631691071/137438953472), (146511642371/549755813888)), (11/274877906944), by norm_num⟩
  | 3 => ⟨((82900410975/549755813888), (-157200927897/1099511627776)), (13/549755813888), by norm_num⟩
  | 4 => ⟨((-266846128759/4398046511104), (253005133227/4398046511104)), (11/1099511627776), by norm_num⟩
  | 5 => ⟨((42947227641/2199023255552), (-81439210691/4398046511104)), (15/4398046511104), by norm_num⟩
  | 6 => ⟨((-92161195199/17592186044416), (87380902163/17592186044416)), (17/17592186044416), by norm_num⟩
  | 7 => ⟨((42379349031/35184372088832), (-80362363865/70368744177664)), (33/140737488355328), by norm_num⟩
  | 8 => ⟨((-272827724139/1125899906842624), (129338235137/562949953421312)), (55/1125899906842624), by norm_num⟩
  | 9 => ⟨((195155236797/4503599627370496), (-185032763695/4503599627370496)), (41/4503599627370496), by norm_num⟩
  | 10 => ⟨((-251272189529/36028797018963968), (119119497973/18014398509481984)), (55/36028797018963968), by norm_num⟩
  | 11 => ⟨((147057086607/144115188075855872), (-139429408107/144115188075855872)), (17/72057594037927936), by norm_num⟩
  | 12 => ⟨((-157786166985/1152921504606846976), (149601983677/1152921504606846976)), (19/576460752303423488), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582403412673669/10141204801825835211973625643008), (3103880126407/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((445025049488595/158456325028528675187087900672), (1796162119/309485009821345068724781056)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891239114359077/39614081257132168796771975168), (4137896302375/39614081257132168796771975168)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1891107036283509/2475880078570760549798248448), (4395971291315/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886386232155703/77371252455336267181195264), (4395359734553/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551035468679481/9671406556917033397649408), (514999992209/1208925819614629174706176)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1260084599248667/604462909807314587353088), (450543761657/75557863725914323419136)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889896273000733/75557863725914323419136), (2927925173273/37778931862957161709568)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162389524260047/590295810358705651712), (4390821442409/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405903452432861/147573952589676412928), (6035646564337/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913089126686187/36893488147419103232), (7541958560115/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912846841108589/4611686018427387904), (8481128436037/9223372036854775808)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399234046752591/288230376151711744), (8476659111413/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((74822222118751/9007199254740992), (1853011962815/36028797018963968)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495486117288285/36028797018963968), (11108011847391/36028797018963968)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494045042363079/9007199254740992), (13867405054391/9007199254740992)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((1118726184244201/2251799813685248), (1730122596513/281474976710656)), (175/2251799813685248), by norm_num⟩
  | 1 => ⟨((1115092323081377/1125899906842624), (161682634029/8796093022208)), (263/1125899906842624), by norm_num⟩
  | 0 => ⟨((1104098076973817/1125899906842624), (41126182341167/1125899906842624)), (133/281474976710656), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1104098076973817/1125899906842624), (41126182341167/1125899906842624)), (507355810069949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1081216183876529/1125899906842624), (20164909225143/281474976710656)), (1083/1125899906842624), by norm_num⟩
  | 2 => ⟨((516263680361991/562949953421312), (77458488336737/562949953421312)), (559/281474976710656), by norm_num⟩
  | 3 => ⟨((462791352343387/562949953421312), (142069482450325/562949953421312)), (4717/1125899906842624), by norm_num⟩
  | 4 => ⟨((689198380002117/1125899906842624), (467171388933075/1125899906842624)), (10137/1125899906842624), by norm_num⟩
  | 5 => ⟨((57008908784769/281474976710656), (571940298563359/1125899906842624)), (20823/1125899906842624), by norm_num⟩
  | 6 => ⟨((-977406437483319/4503599627370496), (463354756322077/2251799813685248)), (59181/2251799813685248), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-41474899193/34359738368), (-268031536035/68719476736)), (1/34359738368), by norm_num⟩, -1, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-492515092649/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-2885830621/2147483648), (-149197443105/34359738368)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-492515092649/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-424996851187535/4503599627370496), (136897592370293/562949953421312)), (49799/2251799813685248), by norm_num⟩
  | 1 => ⟨((46477791291/274877906944), (-239538630317/549755813888)), (3/68719476736), by norm_num⟩
  | 2 => ⟨((-83277022655/549755813888), (107298902279/274877906944)), (23/549755813888), by norm_num⟩
  | 3 => ⟨((49737464637/549755813888), (-128169216131/549755813888)), (29/1099511627776), by norm_num⟩
  | 4 => ⟨((-89117573239/2199023255552), (114824203333/1099511627776)), (7/549755813888), by norm_num⟩
  | 5 => ⟨((127741804581/8796093022208), (-164589882895/4398046511104)), (21/4398046511104), by norm_num⟩
  | 6 => ⟨((-152588391983/35184372088832), (393207308289/35184372088832)), (13/8796093022208), by norm_num⟩
  | 7 => ⟨((78114770351/70368744177664), (-50323779857/17592186044416)), (7/17592186044416), by norm_num⟩
  | 8 => ⟨((-139962879463/562949953421312), (360672436345/562949953421312)), (13/140737488355328), by norm_num⟩
  | 9 => ⟨((55728847693/1125899906842624), (-287217001383/2251799813685248)), (43/2251799813685248), by norm_num⟩
  | 10 => ⟨((-79882152451/9007199254740992), (205849512781/9007199254740992)), (33/9007199254740992), by norm_num⟩
  | 11 => ⟨((104094256783/72057594037927936), (-67060511593/18014398509481984)), (11/18014398509481984), by norm_num⟩
  | 12 => ⟨((-15542655857/72057594037927936), (320416817755/576460752303423488)), (27/288230376151711744), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791112646017817/5070602400912917605986812821504), (2528327814789/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889945776825861/316912650057057350374175801344), (2995753310379/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1891004561636641/39614081257132168796771975168), (1684905852513/19807040628566084398385987584)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890858036369439/2475880078570760549798248448), (3579932945411/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772523703245723/154742504910672534362390528), (3579379463059/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550802508886881/9671406556917033397649408), (3355080209185/9671406556917033397649408)), (51/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629940506529015/302231454903657293676544), (733776796955/151115727451828646838272)), (23/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472391480206551/18889465931478580854784), (4768446778967/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324717211436127/1180591620717411303424), (3575370573029/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623274381123209/590295810358705651712), (4914567375967/590295810358705651712)), (19/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912877490046979/36893488147419103232), (6140858772749/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912609445524973/4611686018427387904), (1726308683931/2305843009213693952)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399115783398489/288230376151711744), (1725299057369/288230376151711744)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((598371792644945/72057594037927936), (6034004377931/144115188075855872)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((186859008253497/4503599627370496), (4520962209665/18014398509481984)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((746642147909471/4503599627370496), (11286517404571/9007199254740992)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((1117975643250629/2251799813685248), (2815674136723/562949953421312)), (87/1125899906842624), by norm_num⟩
  | 1 => ⟨((1113991952780679/1125899906842624), (8417266250729/562949953421312)), (131/562949953421312), by norm_num⟩
  | 0 => ⟨((275499666104821/281474976710656), (8357814067257/281474976710656)), (33/70368744177664), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((275499666104821/281474976710656), (8357814067257/281474976710656)), (125885278201081/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1077612139509441/1125899906842624), (4090194822651/70368744177664)), (533/562949953421312), by norm_num⟩
  | 2 => ⟨((513795726690605/562949953421312), (15659095687139/140737488355328)), (2165/1125899906842624), by norm_num⟩
  | 3 => ⟨((230982106616387/281474976710656), (228669036002069/1125899906842624)), (4435/1125899906842624), by norm_num⟩
  | 4 => ⟨((355872757575865/562949953421312), (750595399576019/2251799813685248)), (9081/1125899906842624), by norm_num⟩
  | 5 => ⟨((649672875270167/2251799813685248), (237247070585479/562949953421312)), (137/8796093022208), by norm_num⟩
  | 6 => ⟨((-424996851187535/4503599627370496), (136897592370293/562949953421312)), (49799/2251799813685248), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2885830621/2147483648), (-149197443105/34359738368)), (1/34359738368), by norm_num⟩, -1, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-534887708873/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((-50145722707/34359738368), (-324066732993/68719476736)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-534887708873/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((1780419076031/2251799813685248), (1046486741446987/4503599627370496)), (163247/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1691667749/1099511627776), (-248580221073/549755813888)), (41/1099511627776), by norm_num⟩
  | 2 => ⟨((1645916721/1099511627776), (236188855/536870912)), (21/549755813888), by norm_num⟩
  | 3 => ⟨((-1067602017/1099511627776), (-313755163333/1099511627776)), (29/1099511627776), by norm_num⟩
  | 4 => ⟨((32460275/68719476736), (76317419581/549755813888)), (29/2199023255552), by norm_num⟩
  | 5 => ⟨((-1617018331/8796093022208), (-475221892199/8796093022208)), (47/8796093022208), by norm_num⟩
  | 6 => ⟨((262214365/4398046511104), (154123183847/8796093022208)), (1/549755813888), by norm_num⟩
  | 7 => ⟨((-291568911/17592186044416), (-85688533615/17592186044416)), (37/70368744177664), by norm_num⟩
  | 8 => ⟨((567366903/140737488355328), (166742187219/140737488355328)), (37/281474976710656), by norm_num⟩
  | 9 => ⟨((-490686673/562949953421312), (-288413612787/1125899906842624)), (17/562949953421312), by norm_num⟩
  | 10 => ⟨((1527731483/9007199254740992), (224490790499/4503599627370496)), (27/4503599627370496), by norm_num⟩
  | 11 => ⟨((-270257109/9007199254740992), (-158850511855/18014398509481984)), (5/4503599627370496), by norm_num⟩
  | 12 => ⟨((701194735/144115188075855872), (412145097601/288230376151711744)), (27/144115188075855872), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693182021/10141204801825835211973625643008), (1020852634523/5070602400912917605986812821504)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111232174813717/39614081257132168796771975168), (604676304847/158456325028528675187087900672)), (47/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945402917021117/19807040628566084398385987584), (1360343646663/19807040628566084398385987584)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890647041847797/2475880078570760549798248448), (2890299272705/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886156440706223/77371252455336267181195264), (722453620145/38685626227668133590597632)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550605046840679/9671406556917033397649408), (2708686055079/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259708417123887/604462909807314587353088), (1184792678879/302231454903657293676544)), (23/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((29520090563837/1180591620717411303424), (3849610863111/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649329526372079/2361183241434822606848), (2886363642079/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202873300485759/73786976294838206464), (1983689002879/295147905179352825856)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825395740293565/73786976294838206464), (4957165062247/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824815751675475/9223372036854775808), (5573982615403/9223372036854775808)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798030624923077/576460752303423488), (5570448876835/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196393348044605/144115188075855872), (4870169182965/144115188075855872)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494349528364109/36028797018963968), (912163910735/4503599627370496)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((373159011726147/2251799813685248), (2276937571187/2251799813685248)), (173/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117334761707345/2251799813685248), (9086938121749/2251799813685248)), (87/1125899906842624), by norm_num⟩
  | 1 => ⟨((1113048988101113/1125899906842624), (13578450550615/1125899906842624)), (261/1125899906842624), by norm_num⟩
  | 0 => ⟨((550092900535829/562949953421312), (26949517442157/1125899906842624)), (263/562949953421312), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((550092900535829/562949953421312), (26949517442157/1125899906842624)), (1003267528343023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1074413909298251/1125899906842624), (13167012562751/281474976710656)), (527/562949953421312), by norm_num⟩
  | 2 => ⟨((2045637126315661/2251799813685248), (201038424184567/2251799813685248)), (4221/2251799813685248), by norm_num⟩
  | 3 => ⟨((7189066710965/8796093022208), (182632426660921/1125899906842624)), (1053/281474976710656), by norm_num⟩
  | 4 => ⟨((361228570928379/562949953421312), (597063580631031/2251799813685248)), (2063/281474976710656), by norm_num⟩
  | 5 => ⟨((192212064927077/562949953421312), (766236581685321/2251799813685248)), (29933/2251799813685248), by norm_num⟩
  | 6 => ⟨((1780419076031/2251799813685248), (1046486741446987/4503599627370496)), (163247/9007199254740992), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-50145722707/34359738368), (-324066732993/68719476736)), (1/34359738368), by norm_num⟩, -1, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-285796269295/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-53586800493/34359738368), (-346304698185/68719476736)), (3/68719476736), by norm_num⟩
  | 1 => ⟨((-285796269295/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((152055543228901/2251799813685248), (3502320272943/17592186044416)), (98585/4503599627370496), by norm_num⟩
  | 1 => ⟨((-38597486967/274877906944), (-113794847935/274877906944)), (27/549755813888), by norm_num⟩
  | 2 => ⟨((20065304451/137438953472), (236629734025/549755813888)), (15/274877906944), by norm_num⟩
  | 3 => ⟨((-55632836829/549755813888), (-328038465953/1099511627776)), (45/1099511627776), by norm_num⟩
  | 4 => ⟨((7230326999/137438953472), (170534203343/1099511627776)), (49/2199023255552), by norm_num⟩
  | 5 => ⟨((-96224270859/4398046511104), (-283692725367/4398046511104)), (43/4398046511104), by norm_num⟩
  | 6 => ⟨((133395164095/17592186044416), (393281625467/17592186044416)), (63/17592186044416), by norm_num⟩
  | 7 => ⟨((-19813388977/8796093022208), (-233658899879/35184372088832)), (39/35184372088832), by norm_num⟩
  | 8 => ⟨((82401568241/140737488355328), (30367501437/17592186044416)), (43/140737488355328), by norm_num⟩
  | 9 => ⟨((-4759701225/35184372088832), (-28065530669/70368744177664)), (21/281474976710656), by norm_num⟩
  | 10 => ⟨((63344130901/2251799813685248), (23344252145/281474976710656)), (73/4503599627370496), by norm_num⟩
  | 11 => ⟨((-95796667067/18014398509481984), (-17652002789/1125899906842624)), (29/9007199254740992), by norm_num⟩
  | 12 => ⟨((132802379369/144115188075855872), (195766975431/72057594037927936)), (83/144115188075855872), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238521203/10141204801825835211973625643008), (810086823139/5070602400912917605986812821504)), (29/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779561423952217/633825300114114700748351602688), (959510531883/316912650057057350374175801344)), (17/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890633380485415/39614081257132168796771975168), (134912445915/2475880078570760549798248448)), (77/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472615980933147/618970019642690137449562112), (573286600685/618970019642690137449562112)), (41/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772129891261519/154742504910672534362390528), (1146367827455/77371252455336267181195264)), (41/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193804203685997/1208925819614629174706176), (2149003339143/9671406556917033397649408)), (77/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629779281399895/302231454903657293676544), (1879941676907/604462909807314587353088)), (67/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472260634357551/18889465931478580854784), (1527043731205/37778931862957161709568)), (109/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298476831430995/4722366482869645213696), (1144925125525/2361183241434822606848)), (41/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405684052804185/147573952589676412928), (3147382026675/590295810358705651712)), (7/36893488147419103232), by norm_num⟩
  | 8 => ⟨((456270885383329/18446744073709551616), (1966242537511/36893488147419103232)), (35/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1824465272811285/9223372036854775808), (552706359523/1152921504606846976)), (79/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398927925246949/288230376151711744), (4418658904673/1152921504606846976)), (79/576460752303423488), by norm_num⟩
  | 5 => ⟨((299022134446269/36028797018963968), (965740682915/36028797018963968)), (69/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493894399797449/36028797018963968), (2893860935227/18014398509481984)), (207/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492070781030731/9007199254740992), (3611450284235/4503599627370496)), (259/9007199254740992), by norm_num⟩
  | 2 => ⟨((2233549897779063/4503599627370496), (14410594308337/4503599627370496)), (259/2251799813685248), by norm_num⟩
  | 1 => ⟨((1112222851895507/1125899906842624), (10764021966757/1125899906842624)), (779/2251799813685248), by norm_num⟩
  | 0 => ⟨((549293781778877/562949953421312), (42705713900079/2251799813685248)), (1567/2251799813685248), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((549293781778877/562949953421312), (42705713900079/2251799813685248)), (5977639205168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2143065618838295/2251799813685248), (20834874351775/562949953421312)), (1559/1125899906842624), by norm_num⟩
  | 2 => ⟨((1018248768595841/1125899906842624), (158630452404313/2251799813685248)), (3083/1125899906842624), by norm_num⟩
  | 3 => ⟨((915303077455085/1125899906842624), (143463252675329/1125899906842624)), (6011/1125899906842624), by norm_num⟩
  | 4 => ⟨((1451635289716371/2251799813685248), (14578600179887/70368744177664)), (22611/2251799813685248), by norm_num⟩
  | 5 => ⟨((839154779951561/2251799813685248), (601483250642031/2251799813685248)), (38523/2251799813685248), by norm_num⟩
  | 6 => ⟨((152055543228901/2251799813685248), (3502320272943/17592186044416)), (98585/4503599627370496), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-53586800493/34359738368), (-346304698185/68719476736)), (3/68719476736), by norm_num⟩, -1, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile005Terms0

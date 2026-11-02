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
namespace Reinmann.XiRectangle.Tile000Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨0,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (141/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (141/640))
  have he : value ((3/4), (141/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-381061692393/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-285796269295/137438953472), (-83952654105/137438953472)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-381061692393/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((922302122121641/9007199254740992), (-322881323303241/4503599627370496)), (439/140737488355328), by norm_num⟩
  | 1 => ⟨((-156076932513/549755813888), (54639716529/274877906944)), (3/274877906944), by norm_num⟩
  | 2 => ⟨((54092142861/137438953472), (-151493461835/549755813888)), (5/274877906944), by norm_num⟩
  | 3 => ⟨((-24995877543/68719476736), (70004843963/274877906944)), (11/549755813888), by norm_num⟩
  | 4 => ⟨((277213152713/1099511627776), (-97047320437/549755813888)), (17/1099511627776), by norm_num⟩
  | 5 => ⟨((-76859806087/549755813888), (107628922467/1099511627776)), (21/2199023255552), by norm_num⟩
  | 6 => ⟨((284134175401/4398046511104), (-198940491079/4398046511104)), (11/2199023255552), by norm_num⟩
  | 7 => ⟨((-225082060091/8796093022208), (157594331989/8796093022208)), (5/2199023255552), by norm_num⟩
  | 8 => ⟨((312029990693/35184372088832), (-218472133781/35184372088832)), (15/17592186044416), by norm_num⟩
  | 9 => ⟨((-96125648133/35184372088832), (134607416499/70368744177664)), (5/17592186044416), by norm_num⟩
  | 10 => ⟨((213213510345/281474976710656), (-74642200983/140737488355328)), (3/35184372088832), by norm_num⟩
  | 11 => ⟨((-107482431675/562949953421312), (37627659027/281474976710656)), (13/562949953421312), by norm_num⟩
  | 12 => ⟨((198669718601/4503599627370496), (-139101364083/4503599627370496)), (13/2251799813685248), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790633531163243/5070602400912917605986812821504), (-795682028797/10141204801825835211973625643008)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778761177008119/633825300114114700748351602688), (-941640818835/633825300114114700748351602688)), (3/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((236216666731533/4951760157141521099596496896), (-1059153507269/39614081257132168796771975168)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944753956040445/1237940039285380274899124224), (-1125111927583/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885587101684029/77371252455336267181195264), (-562421758517/77371252455336267181195264)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774769007982591/4835703278458516698824704), (-1054255699091/9671406556917033397649408)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258775244714395/604462909807314587353088), (-230547184421/151115727451828646838272)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887770289790415/75557863725914323419136), (-374505634023/18889465931478580854784)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297523209142381/4722366482869645213696), (-280762430045/1180591620717411303424)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621425895643447/590295810358705651712), (-1543434589025/590295810358705651712)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823447018770219/73786976294838206464), (-482038940413/18446744073709551616)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822626069322463/9223372036854775808), (-1083806162131/4611686018427387904)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593874851066069/1152921504606846976), (-2165660368477/1152921504606846976)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194483938833765/144115188075855872), (-473189794563/36028797018963968)), (23/72057594037927936), by norm_num⟩
  | 4 => ⟨((745746391628209/18014398509481984), (-354344654735/4503599627370496)), (69/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489077986632895/9007199254740992), (-3535791810517/9007199254740992)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227591919833931/4503599627370496), (-3524335540951/2251799813685248)), (43/1125899906842624), by norm_num⟩
  | 1 => ⟨((553894381628861/562949953421312), (-5257952865185/1125899906842624)), (259/2251799813685248), by norm_num⟩
  | 0 => ⟨((1089856254961759/1125899906842624), (-10402243736983/1125899906842624)), (259/1125899906842624), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1089856254961759/1125899906842624), (-10402243736983/1125899906842624)), (988010886764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2109740737318523/2251799813685248), (-20138469385223/1125899906842624)), (1013/2251799813685248), by norm_num⟩
  | 2 => ⟨((1975923312482569/2251799813685248), (-75471982884151/2251799813685248)), (1935/2251799813685248), by norm_num⟩
  | 3 => ⟨((1731315942437749/2251799813685248), (-132451250340963/2251799813685248)), (1763/1125899906842624), by norm_num⟩
  | 4 => ⟨((1323346569580431/2251799813685248), (-50918149987727/562949953421312)), (2919/1125899906842624), by norm_num⟩
  | 5 => ⟨((759287572926551/2251799813685248), (-239390228939983/2251799813685248)), (15837/4503599627370496), by norm_num⟩
  | 6 => ⟨((922302122121641/9007199254740992), (-322881323303241/4503599627370496)), (439/140737488355328), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-285796269295/137438953472), (-83952654105/137438953472)), (1/68719476736), by norm_num⟩, 0, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-194696938485/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-18252837983/8589934592), (-10723542315/17179869184)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-194696938485/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((109123191280765/1125899906842624), (-628773972733911/9007199254740992)), (13559/4503599627370496), by norm_num⟩
  | 1 => ⟨((-301923126643/1099511627776), (217462257073/1099511627776)), (3/274877906944), by norm_num⟩
  | 2 => ⟨((213853157821/549755813888), (-77014621071/274877906944)), (5/274877906944), by norm_num⟩
  | 3 => ⟨((-201963873469/549755813888), (36366475351/137438953472)), (11/549755813888), by norm_num⟩
  | 4 => ⟨((286103370665/1099511627776), (-206067966481/1099511627776)), (9/549755813888), by norm_num⟩
  | 5 => ⟨((-81059188755/549755813888), (116766902483/1099511627776)), (3/274877906944), by norm_num⟩
  | 6 => ⟨((76552658413/1099511627776), (-220550364173/4398046511104)), (25/4398046511104), by norm_num⟩
  | 7 => ⟨((-247874300959/8796093022208), (89266604973/4398046511104)), (11/4398046511104), by norm_num⟩
  | 8 => ⟨((175570194281/17592186044416), (-63227834097/8796093022208)), (17/17592186044416), by norm_num⟩
  | 9 => ⟨((-221079029891/70368744177664), (159233727359/70368744177664)), (3/8796093022208), by norm_num⟩
  | 10 => ⟨((250545623031/281474976710656), (-180457248471/281474976710656)), (29/281474976710656), by norm_num⟩
  | 11 => ⟨((-258126982715/1125899906842624), (185917776145/1125899906842624)), (1/35184372088832), by norm_num⟩
  | 12 => ⟨((121888135315/2251799813685248), (-175581574757/4503599627370496)), (1/140737488355328), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572467/10141204801825835211973625643008), (-813080181543/10141204801825835211973625643008)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444672766561161/158456325028528675187087900672), (-962158258131/633825300114114700748351602688)), (3/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((472413618143875/9903520314283042199192993792), (-1082227338235/39614081257132168796771975168)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889424138396949/2475880078570760549798248448), (-574808673743/1237940039285380274899124224)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885545224077143/77371252455336267181195264), (-1149337102829/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774729757535851/4835703278458516698824704), (-538602933961/4835703278458516698824704)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629353288023133/302231454903657293676544), (-942257574189/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887658739968083/75557863725914323419136), (-1530610857199/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297439578931345/4722366482869645213696), (-1147470379143/4722366482869645213696)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621310956333359/590295810358705651712), (-197122446991/73786976294838206464)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((3561139497925/144115188075855872), (-985018456311/36893488147419103232)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455616157903733/2305843009213693952), (-1107329915145/4611686018427387904)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593713547766005/1152921504606846976), (-553155500159/288230376151711744)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194342949520307/144115188075855872), (-1933754152295/144115188075855872)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491281601098933/36028797018963968), (-1448028587597/18014398509481984)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((744407268177071/4503599627370496), (-3612080679011/9007199254740992)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((556766649629469/1125899906842624), (-225007628287/140737488355328)), (173/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214793482116413/2251799813685248), (-671297844103/140737488355328)), (259/2251799813685248), by norm_num⟩
  | 0 => ⟨((272270013548179/281474976710656), (-21244279850439/2251799813685248)), (259/1125899906842624), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((272270013548179/281474976710656), (-21244279850439/2251799813685248)), (988010886764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1053364093358605/1125899906842624), (-41099073390429/2251799813685248)), (1013/2251799813685248), by norm_num⟩
  | 2 => ⟨((1970252636096617/2251799813685248), (-76902552201453/2251799813685248)), (1933/2251799813685248), by norm_num⟩
  | 3 => ⟨((1721281538418471/2251799813685248), (-33643633700613/562949953421312)), (879/562949953421312), by norm_num⟩
  | 4 => ⟨((1307709420343067/2251799813685248), (-102869118688493/1125899906842624)), (1449/562949953421312), by norm_num⟩
  | 5 => ⟨((1481282390733983/4503599627370496), (-238960701131197/2251799813685248)), (15583/4503599627370496), by norm_num⟩
  | 6 => ⟨((109123191280765/1125899906842624), (-628773972733911/9007199254740992)), (13559/4503599627370496), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-18252837983/8589934592), (-10723542315/17179869184)), (1/68719476736), by norm_num⟩, 0, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-198624834775/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-148968626081/68719476736), (-87519067823/137438953472)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-198624834775/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((828700675877059/9007199254740992), (-612872679183223/9007199254740992)), (26209/9007199254740992), by norm_num⟩
  | 1 => ⟨((-73097321451/274877906944), (216238999401/1099511627776)), (3/274877906944), by norm_num⟩
  | 2 => ⟨((52819608375/137438953472), (-78126387103/274877906944)), (5/274877906944), by norm_num⟩
  | 3 => ⟨((-25444717385/68719476736), (150542868553/549755813888)), (3/137438953472), by norm_num⟩
  | 4 => ⟨((294178770069/1099511627776), (-217562427809/1099511627776)), (19/1099511627776), by norm_num⟩
  | 5 => ⟨((-42514300439/274877906944), (15720907423/137438953472)), (13/1099511627776), by norm_num⟩
  | 6 => ⟨((81921422197/1099511627776), (-121171378197/2199023255552)), (7/1099511627776), by norm_num⟩
  | 7 => ⟨((-270609560097/8796093022208), (200131616803/8796093022208)), (25/8796093022208), by norm_num⟩
  | 8 => ⟨((24442569685/2199023255552), (-144613693267/17592186044416)), (5/4398046511104), by norm_num⟩
  | 9 => ⟨((-125596645525/35184372088832), (185772148811/70368744177664)), (7/17592186044416), by norm_num⟩
  | 10 => ⟨((290416797689/281474976710656), (-214780228931/281474976710656)), (35/281474976710656), by norm_num⟩
  | 11 => ⟨((-76310228187/281474976710656), (112871765065/562949953421312)), (5/140737488355328), by norm_num⟩
  | 12 => ⟨((294086571187/4503599627370496), (-108747120669/2251799813685248)), (41/4503599627370496), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581151993160631/10141204801825835211973625643008), (-414741798137/5070602400912917605986812821504)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889312484230075/316912650057057350374175801344), (-490749892153/316912650057057350374175801344)), (23/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889580125390707/39614081257132168796771975168), (-1103978589595/39614081257132168796771975168)), (27/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889345160320729/2475880078570760549798248448), (-1172717921375/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771011487856435/154742504910672534362390528), (-1172426286701/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549385508676947/9671406556917033397649408), (-549419940849/4835703278458516698824704)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629320919664835/302231454903657293676544), (-961175246651/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471888394547339/18889465931478580854784), (-3049471525/147573952589676412928)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297360738547793/4722366482869645213696), (-1170489493289/4722366482869645213696)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202650325134747/73786976294838206464), (-50268709215/18446744073709551616)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911584027118463/36893488147419103232), (-2009512612113/73786976294838206464)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822312445394367/9223372036854775808), (-1129501895929/4611686018427387904)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593561490909009/1152921504606846976), (-2256883321945/1152921504606846976)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194210045172471/144115188075855872), (-986194994735/72057594037927936)), (23/72057594037927936), by norm_num⟩
  | 4 => ⟨((1491082535051571/36028797018963968), (-184614104421/2251799813685248)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488566211384077/9007199254740992), (-920991985333/2251799813685248)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226571468384639/4503599627370496), (-1835762985929/1125899906842624)), (173/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214054576088429/2251799813685248), (-10952572360777/2251799813685248)), (259/2251799813685248), by norm_num⟩
  | 0 => ⟨((2176697391076495/2251799813685248), (-21658344541633/2251799813685248)), (259/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2176697391076495/2251799813685248), (-21658344541633/2251799813685248)), (988010886764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2103891482554825/2251799813685248), (-41871983266269/2251799813685248)), (253/562949953421312), by norm_num⟩
  | 2 => ⟨((1964919830125961/2251799813685248), (-39121643236753/1125899906842624)), (965/1125899906842624), by norm_num⟩
  | 3 => ⟨((1711869724616149/2251799813685248), (-68275067895315/1125899906842624)), (219/140737488355328), by norm_num⟩
  | 4 => ⟨((1293122060307597/2251799813685248), (-103808536589957/1125899906842624)), (5753/2251799813685248), by norm_num⟩
  | 5 => ⟨((723447885499327/2251799813685248), (-476906012326317/4503599627370496)), (7669/2251799813685248), by norm_num⟩
  | 6 => ⟨((828700675877059/9007199254740992), (-612872679183223/9007199254740992)), (26209/9007199254740992), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-148968626081/68719476736), (-87519067823/137438953472)), (1/68719476736), by norm_num⟩, 0, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-404680611859/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-151755229447/68719476736), (-22289049325/34359738368)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-404680611859/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((197175552182639/2251799813685248), (-597954549781973/9007199254740992)), (6345/2251799813685248), by norm_num⟩
  | 1 => ⟨((-283482119915/1099511627776), (107460979257/549755813888)), (11/1099511627776), by norm_num⟩
  | 2 => ⟨((6521060967/17179869184), (-2471971063/8589934592)), (5/274877906944), by norm_num⟩
  | 3 => ⟨((-204809238365/549755813888), (9704757271/34359738368)), (3/137438953472), by norm_num⟩
  | 4 => ⟨((18845259523/68719476736), (-228600524737/1099511627776)), (5/274877906944), by norm_num⟩
  | 5 => ⟨((-177563893479/1099511627776), (134620059139/1099511627776)), (7/549755813888), by norm_num⟩
  | 6 => ⟨((174275349751/2199023255552), (-33031712459/549755813888)), (1/137438953472), by norm_num⟩
  | 7 => ⟨((-73306161845/2199023255552), (13894265959/549755813888)), (29/8796093022208), by norm_num⟩
  | 8 => ⟨((107922760175/8796093022208), (-81821636553/8796093022208)), (3/2199023255552), by norm_num⟩
  | 9 => ⟨((-282463983821/70368744177664), (13384378667/4398046511104)), (33/70368744177664), by norm_num⟩
  | 10 => ⟨((166339592835/140737488355328), (-126110356029/140737488355328)), (21/140737488355328), by norm_num⟩
  | 11 => ⟨((-22262580951/70368744177664), (135026999261/562949953421312)), (3/70368744177664), by norm_num⟩
  | 12 => ⟨((174802163011/2251799813685248), (-16565781661/281474976710656)), (25/2251799813685248), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790549585858185/5070602400912917605986812821504), (-844999895521/10141204801825835211973625643008)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778562449251367/633825300114114700748351602688), (-999792770517/633825300114114700748351602688)), (23/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236188725454451/4951760157141521099596496896), (-562275264831/19807040628566084398385987584)), (27/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889270458697999/2475880078570760549798248448), (-597282920033/1237940039285380274899124224)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770936803375889/154742504910672534362390528), (-1194263223727/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549315510185055/9671406556917033397649408), (-279825086957/2417851639229258349412352)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314645152213079/151115727451828646838272), (-489533249293/302231454903657293676544)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887454112782549/75557863725914323419136), (-397595215981/18889465931478580854784)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324321542333723/1180591620717411303424), (-1192258978109/4722366482869645213696)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810550058440827/295147905179352825856), (-1638500728493/590295810358705651712)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823040021659877/73786976294838206464), (-2046843686625/73786976294838206464)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822168508601199/9223372036854775808), (-2300937430139/9223372036854775808)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796708839420725/576460752303423488), (-1149368646419/576460752303423488)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194084349799947/144115188075855872), (-1004461368449/72057594037927936)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((745447136020967/18014398509481984), (-1504223104431/18014398509481984)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488331371979709/9007199254740992), (-3751931927303/9007199254740992)), (43/4503599627370496), by norm_num⟩
  | 2 => ⟨((2226103254739263/4503599627370496), (-7478048182009/4503599627370496)), (43/1125899906842624), by norm_num⟩
  | 1 => ⟨((2213355908361433/2251799813685248), (-11152748990887/2251799813685248)), (259/2251799813685248), by norm_num⟩
  | 0 => ⟨((2175314605714685/2251799813685248), (-22049496248751/2251799813685248)), (259/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2175314605714685/2251799813685248), (-22049496248751/2251799813685248)), (988010886764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1050605703223531/1125899906842624), (-21300557423913/1125899906842624)), (253/562949953421312), by norm_num⟩
  | 2 => ⟨((979943797129615/1125899906842624), (-79504357271543/2251799813685248)), (241/281474976710656), by norm_num⟩
  | 3 => ⟨((13304768534485/17592186044416), (-8649725575019/140737488355328)), (3493/2251799813685248), by norm_num⟩
  | 4 => ⟨((319865354637019/562949953421312), (-104667011930763/1125899906842624)), (2857/1125899906842624), by norm_num⟩
  | 5 => ⟨((1415046558157049/4503599627370496), (-237885095728747/2251799813685248)), (1889/562949953421312), by norm_num⟩
  | 6 => ⟨((197175552182639/2251799813685248), (-597954549781973/9007199254740992)), (6345/2251799813685248), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-151755229447/68719476736), (-22289049325/34359738368)), (1/68719476736), by norm_num⟩, 0, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-25733144285/8589934592), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-77199432855/34359738368), (-90709333605/137438953472)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((188096634074169/2251799813685248), (-583927591761437/9007199254740992)), (24617/9007199254740992), by norm_num⟩
  | 1 => ⟨((-137570106749/549755813888), (53384116579/274877906944)), (11/1099511627776), by norm_num⟩
  | 2 => ⟨((51515401083/137438953472), (-159924520931/549755813888)), (5/274877906944), by norm_num⟩
  | 3 => ⟨((-102884233073/274877906944), (159697016229/549755813888)), (3/137438953472), by norm_num⟩
  | 4 => ⟨((308213617457/1099511627776), (-119602376377/549755813888)), (5/274877906944), by norm_num⟩
  | 5 => ⟨((-184665096193/1099511627776), (143318679563/1099511627776)), (7/549755813888), by norm_num⟩
  | 6 => ⟨((184402396155/2199023255552), (-143114797923/2199023255552)), (1/137438953472), by norm_num⟩
  | 7 => ⟨((-157834345567/4398046511104), (122495319703/4398046511104)), (1/274877906944), by norm_num⟩
  | 8 => ⟨((236414721445/17592186044416), (-183481591297/17592186044416)), (13/8796093022208), by norm_num⟩
  | 9 => ⟨((-157385602439/35184372088832), (122147049923/35184372088832)), (19/35184372088832), by norm_num⟩
  | 10 => ⟨((23574256431/17592186044416), (-73183971915/70368744177664)), (25/140737488355328), by norm_num⟩
  | 11 => ⟨((-205446286009/562949953421312), (159446972053/562949953421312)), (29/562949953421312), by norm_num⟩
  | 12 => ⟨((25644252895/281474976710656), (-39805036675/562949953421312)), (31/2251799813685248), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197631132535527/1267650600228229401496703205376), (-859720128721/10141204801825835211973625643008)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222312892641661/79228162514264337593543950336), (-508572480235/316912650057057350374175801344)), (23/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889443093925983/39614081257132168796771975168), (-572032173417/19807040628566084398385987584)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889199594351565/2475880078570760549798248448), (-1215289838255/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770865955584435/154742504910672534362390528), (-607488308565/77371252455336267181195264)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774624553982683/4835703278458516698824704), (-1138707892151/9671406556917033397649408)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258522524489413/604462909807314587353088), (-498018422085/302231454903657293676544)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887359758642433/75557863725914323419136), (-808968292215/37778931862957161709568)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162151929068635/590295810358705651712), (-606453663581/2361183241434822606848)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621002900610693/590295810358705651712), (-1666862266313/590295810358705651712)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822918571497351/73786976294838206464), (-2082250739473/73786976294838206464)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822031973598687/9223372036854775808), (-2340708740179/9223372036854775808)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398320316071009/288230376151711744), (-584607919703/288230376151711744)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193965122435417/144115188075855872), (-510892232807/36028797018963968)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490715701422999/36028797018963968), (-1530121539215/18014398509481984)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((744054315619389/4503599627370496), (-954094273811/2251799813685248)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225659187995235/4503599627370496), (-1901509757577/1125899906842624)), (43/1125899906842624), by norm_num⟩
  | 1 => ⟨((2212693335095159/2251799813685248), (-2835624487961/562949953421312)), (259/2251799813685248), by norm_num⟩
  | 0 => ⟨((2174003506744375/2251799813685248), (-22420113084825/2251799813685248)), (259/1125899906842624), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2174003506744375/2251799813685248), (-22420113084825/2251799813685248)), (988010886764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2098671719015723/2251799813685248), (-21645531797183/1125899906842624)), (253/562949953421312), by norm_num⟩
  | 2 => ⟨((122195278007533/140737488355328), (-80694323091641/2251799813685248)), (963/1125899906842624), by norm_num⟩
  | 3 => ⟨((1694644439824425/2251799813685248), (-70062819502061/1125899906842624)), (3483/2251799813685248), by norm_num⟩
  | 4 => ⟨((1266624397687333/2251799813685248), (-52727407998705/562949953421312)), (5677/2251799813685248), by norm_num⟩
  | 5 => ⟨((1385429097621057/4503599627370496), (-474541802461019/4503599627370496)), (14901/4503599627370496), by norm_num⟩
  | 6 => ⟨((188096634074169/2251799813685248), (-583927591761437/9007199254740992)), (24617/9007199254740992), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-77199432855/34359738368), (-90709333605/137438953472)), (1/68719476736), by norm_num⟩, 0, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-418435977663/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-313826983247/137438953472), (-92186676329/137438953472)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-418435977663/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((89907429529055/1125899906842624), (-285355285266053/4503599627370496)), (11975/4503599627370496), by norm_num⟩
  | 1 => ⟨((-66827438115/274877906944), (53025547407/274877906944)), (11/1099511627776), by norm_num⟩
  | 2 => ⟨((203457634797/549755813888), (-161437468853/549755813888)), (5/274877906944), by norm_num⟩
  | 3 => ⟨((-103238555711/274877906944), (163833332071/549755813888)), (3/137438953472), by norm_num⟩
  | 4 => ⟨((78578024825/274877906944), (-31174640971/137438953472)), (11/549755813888), by norm_num⟩
  | 5 => ⟨((-191386047753/1099511627776), (151859030279/1099511627776)), (15/1099511627776), by norm_num⟩
  | 6 => ⟨((194226372217/2199023255552), (-154112741685/2199023255552)), (17/2199023255552), by norm_num⟩
  | 7 => ⟨((-84475221173/2199023255552), (134057057143/4398046511104)), (17/4398046511104), by norm_num⟩
  | 8 => ⟨((257186706293/17592186044416), (-51017464801/4398046511104)), (7/4398046511104), by norm_num⟩
  | 9 => ⟨((-43500594333/8796093022208), (138065614491/35184372088832)), (5/8796093022208), by norm_num⟩
  | 10 => ⟨((105950828401/70368744177664), (-84068772239/70368744177664)), (13/70368744177664), by norm_num⟩
  | 11 => ⟨((-234596126809/562949953421312), (11634057427/35184372088832)), (31/562949953421312), by norm_num⟩
  | 12 => ⟨((119038861979/1125899906842624), (-47226865171/562949953421312)), (33/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581001394307009/10141204801825835211973625643008), (-218430502381/2535301200456458802993406410752)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778446730464133/633825300114114700748351602688), (-1033648304871/633825300114114700748351602688)), (23/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472344910861759/9903520314283042199192993792), (-1162623465095/39614081257132168796771975168)), (27/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472283048113563/618970019642690137449562112), (-154374972395/309485009821345068724781056)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442699642424565/38685626227668133590597632), (-1234676302271/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549185950704125/9671406556917033397649408), (-1157165455719/9671406556917033397649408)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258467278887491/604462909807314587353088), (-1012176327229/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887270016405991/75557863725914323419136), (-1644142848053/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297148153743661/4722366482869645213696), (-616272095605/2361183241434822606848)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620910437523669/590295810358705651712), (-1693833999279/590295810358705651712)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822803060506725/73786976294838206464), (-1057961008031/36893488147419103232)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455475529248015/2305843009213693952), (-2378529335479/9223372036854775808)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796575762079211/576460752303423488), (-2376177890203/1152921504606846976)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193851730741233/144115188075855872), (-2076513328031/144115188075855872)), (23/72057594037927936), by norm_num⟩
  | 4 => ⟨((372636468849981/9007199254740992), (-1554746478025/18014398509481984)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((185987100707837/1125899906842624), (-969412123021/2251799813685248)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((556309226222165/1125899906842624), (-3863856093921/2251799813685248)), (43/1125899906842624), by norm_num⟩
  | 1 => ⟨((2212063320721361/2251799813685248), (-2880711203133/562949953421312)), (259/2251799813685248), by norm_num⟩
  | 0 => ⟨((2172757060305643/2251799813685248), (-22772222307669/2251799813685248)), (519/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2172757060305643/2251799813685248), (-22772222307669/2251799813685248)), (1979836470793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((65508080473997/70368744177664), (-43945741976825/2251799813685248)), (1013/2251799813685248), by norm_num⟩
  | 2 => ⟨((1950603583423617/2251799813685248), (-81820451268509/2251799813685248)), (1927/2251799813685248), by norm_num⟩
  | 3 => ⟨((843360881890137/1125899906842624), (-70876311682651/1125899906842624)), (3479/2251799813685248), by norm_num⟩
  | 4 => ⟨((1254523819129313/2251799813685248), (-212361004250997/2251799813685248)), (5651/2251799813685248), by norm_num⟩
  | 5 => ⟨((1357787497223755/4503599627370496), (-473242668318891/4503599627370496)), (7363/2251799813685248), by norm_num⟩
  | 6 => ⟨((89907429529055/1125899906842624), (-285355285266053/4503599627370496)), (11975/4503599627370496), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-313826983247/137438953472), (-92186676329/137438953472)), (1/68719476736), by norm_num⟩, 0, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile000Terms2

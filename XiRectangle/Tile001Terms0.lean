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
namespace Reinmann.XiRectangle.Tile001Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨1,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (423/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (423/640))
  have he : value ((3/4), (423/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-285796269295/549755813888), (-62964490579/137438953472)), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((1200861194140667/2251799813685248), (-592166415459457/2251799813685248)), (1855/562949953421312), by norm_num⟩
  | 1 => ⟨((-203216198965/549755813888), (100209590161/549755813888)), (3/549755813888), by norm_num⟩
  | 2 => ⟨((281717470713/2199023255552), (-69459994885/1099511627776)), (7/2199023255552), by norm_num⟩
  | 3 => ⟨((-130181113693/4398046511104), (64194666155/4398046511104)), (1/1099511627776), by norm_num⟩
  | 4 => ⟨((180469343837/35184372088832), (-177985407409/70368744177664)), (13/70368744177664), by norm_num⟩
  | 5 => ⟨((-200146906973/281474976710656), (98696066661/281474976710656)), (9/281474976710656), by norm_num⟩
  | 6 => ⟨((92487509511/1125899906842624), (-91214533785/2251799813685248)), (5/1125899906842624), by norm_num⟩
  | 7 => ⟨((-146531329039/18014398509481984), (36128626811/9007199254740992)), (9/18014398509481984), by norm_num⟩
  | 8 => ⟨((101567777587/144115188075855872), (-50084911623/144115188075855872)), (7/144115188075855872), by norm_num⟩
  | 9 => ⟨((-31289519409/576460752303423488), (123435432107/4611686018427387904)), (19/4611686018427387904), by norm_num⟩
  | 10 => ⟨((277609499641/73786976294838206464), (-68447137397/36893488147419103232)), (23/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-139944903253/590295810358705651712), (69009367715/590295810358705651712)), (25/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((64668276749/4722366482869645213696), (-127556396437/18889465931478580854784)), (25/18889465931478580854784), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791649295455329/5070602400912917605986812821504), (-9324398775/158456325028528675187087900672)), (5/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890584334031811/316912650057057350374175801344), (-708048383707/633825300114114700748351602688)), (7/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118277591279947/2475880078570760549798248448), (-199129225861/9903520314283042199192993792)), (7/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59137029073611/77371252455336267181195264), (-211563570431/618970019642690137449562112)), (1/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1774050809670177/154742504910672534362390528), (-846203740253/154742504910672534362390528)), (1/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1552234396731275/9671406556917033397649408), (-793262309345/9671406556917033397649408)), (7/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1261134140331091/604462909807314587353088), (-347025413551/302231454903657293676544)), (7/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891602674942521/75557863725914323419136), (-1127731926167/75557863725914323419136)), (5/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1300396780497561/4722366482869645213696), (-845710867817/4722366482869645213696)), (1/590295810358705651712), by norm_num⟩
  | 9 => ⟨((812687945328629/295147905179352825856), (-1162709332645/590295810358705651712)), (5/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1828382764754653/73786976294838206464), (-1453172024771/73786976294838206464)), (13/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1828176381355039/9223372036854775808), (-817261718427/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99963885115647/72057594037927936), (-1634154633699/1152921504606846976)), (7/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199334461429375/144115188075855872), (-89341905267/9007199254740992)), (3/36028797018963968), by norm_num⟩
  | 4 => ⟨((1498761823624771/36028797018963968), (-2143376294295/36028797018963968)), (9/18014398509481984), by norm_num⟩
  | 3 => ⟨((1498152497517669/9007199254740992), (-2677769330337/9007199254740992)), (11/4503599627370496), by norm_num⟩
  | 2 => ⟨((1122852809603899/2251799813685248), (-2675593711237/2251799813685248)), (11/1125899906842624), by norm_num⟩
  | 1 => ⟨((1121329965780149/1125899906842624), (-8015909597441/2251799813685248)), (65/2251799813685248), by norm_num⟩
  | 0 => ⟨((2233525714298983/2251799813685248), (-1998546549489/281474976710656)), (65/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((2233525714298983/2251799813685248), (-1998546549489/281474976710656)), (247959617232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2215286393606647/2251799813685248), (-31717242944091/2251799813685248)), (261/2251799813685248), by norm_num⟩
  | 2 => ⟨((1089459150049603/1125899906842624), (-62405882005799/2251799813685248)), (261/1125899906842624), by norm_num⟩
  | 3 => ⟨((2106666159028899/2251799813685248), (-120772119714967/2251799813685248)), (65/140737488355328), by norm_num⟩
  | 4 => ⟨((982204628895895/1125899906842624), (-56494040014445/562949953421312)), (2059/2251799813685248), by norm_num⟩
  | 5 => ⟨((1691019993891821/2251799813685248), (-49283872633781/281474976710656)), (2003/1125899906842624), by norm_num⟩
  | 6 => ⟨((1200861194140667/2251799813685248), (-592166415459457/2251799813685248)), (1855/562949953421312), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-285796269295/549755813888), (-62964490579/137438953472)), (1/274877906944), by norm_num⟩, 0, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-226488184839/274877906944), (-199592712889/274877906944)), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((738671214337411/2251799813685248), (-655898409930807/2251799813685248)), (6533/1125899906842624), by norm_num⟩
  | 1 => ⟨((-198123357753/549755813888), (87961188143/274877906944)), (5/549755813888), by norm_num⟩
  | 2 => ⟨((54415188875/274877906944), (-193270484439/1099511627776)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-79708260251/1099511627776), (141552886161/2199023255552)), (7/2199023255552), by norm_num⟩
  | 4 => ⟨((21892118555/1099511627776), (-155511740233/8796093022208)), (5/4398046511104), by norm_num⟩
  | 5 => ⟨((-153926083005/35184372088832), (68338843541/17592186044416)), (11/35184372088832), by norm_num⟩
  | 6 => ⟨((440377829/549755813888), (-200207715487/281474976710656)), (19/281474976710656), by norm_num⟩
  | 7 => ⟨((-283094744267/2251799813685248), (3927690295/35184372088832)), (27/2251799813685248), by norm_num⟩
  | 8 => ⟨((155505682455/9007199254740992), (-138080282373/9007199254740992)), (17/9007199254740992), by norm_num⟩
  | 9 => ⟨((-151858181069/72057594037927936), (33710376675/18014398509481984)), (9/36028797018963968), by norm_num⟩
  | 10 => ⟨((266933222171/1152921504606846976), (-237021658053/1152921504606846976)), (17/576460752303423488), by norm_num⟩
  | 11 => ⟨((-106638588411/4611686018427387904), (189378113613/9223372036854775808)), (15/4611686018427387904), by norm_num⟩
  | 12 => ⟨((78102975783/36893488147419103232), (-17337760235/9223372036854775808)), (23/73786976294838206464), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582902468230365/10141204801825835211973625643008), (-945844633607/10141204801825835211973625643008)), (5/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780698388512493/633825300114114700748351602688), (-1121668359043/633825300114114700748351602688)), (3/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945956201967187/19807040628566084398385987584), (-157722891445/4951760157141521099596496896)), (7/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891822816480939/2475880078570760549798248448), (-167566471933/309485009821345068724781056)), (15/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773488705594561/154742504910672534362390528), (-1340404884467/154742504910672534362390528)), (7/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387926858644551/2417851639229258349412352), (-628247385063/4835703278458516698824704)), (7/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260673058872155/604462909807314587353088), (-549649064499/302231454903657293676544)), (3/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((945426718566943/37778931862957161709568), (-1786106749425/75557863725914323419136)), (19/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649917434636603/2361183241434822606848), (-1339358970815/4722366482869645213696)), (15/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812301645296027/295147905179352825856), (-460314842037/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 8 => ⟨((228427132065697/9223372036854775808), (-1150517742039/36893488147419103232)), (25/73786976294838206464), by norm_num⟩
  | 7 => ⟨((913545008612811/4611686018427387904), (-161745270751/576460752303423488)), (27/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199791983734755/144115188075855872), (-1293499419383/576460752303423488)), (27/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1198384037297603/144115188075855872), (-2262583135643/144115188075855872)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((748668175266441/18014398509481984), (-3391793835869/36028797018963968)), (35/36028797018963968), by norm_num⟩
  | 3 => ⟨((748185471263413/4503599627370496), (-4236102641371/9007199254740992)), (11/2251799813685248), by norm_num⟩
  | 2 => ⟨((280267921512331/562949953421312), (-8461293780021/4503599627370496)), (87/4503599627370496), by norm_num⟩
  | 1 => ⟨((1118659365590543/1125899906842624), (-6332344003875/1125899906842624)), (65/1125899906842624), by norm_num⟩
  | 0 => ⟨((2222852073109795/2251799813685248), (-25220521874609/2251799813685248)), (65/562949953421312), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((2222852073109795/2251799813685248), (-25220521874609/2251799813685248)), (247957469749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2193993992796133/2251799813685248), (-24896302501303/1125899906842624)), (65/281474976710656), by norm_num⟩
  | 2 => ⟨((1068285534902585/1125899906842624), (-24257190980623/562949953421312)), (1037/2251799813685248), by norm_num⟩
  | 3 => ⟨((505764469782575/562949953421312), (-184127246725787/2251799813685248)), (1029/1125899906842624), by norm_num⟩
  | 4 => ⟨((450624020245579/562949953421312), (-330846529951121/2251799813685248)), (4035/2251799813685248), by norm_num⟩
  | 5 => ⟨((1394232594076743/2251799813685248), (-264832410953761/1125899906842624)), (3823/1125899906842624), by norm_num⟩
  | 6 => ⟨((738671214337411/2251799813685248), (-655898409930807/2251799813685248)), (6533/1125899906842624), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-226488184839/274877906944), (-199592712889/274877906944)), (1/137438953472), by norm_num⟩, 0, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-285796269295/274877906944), (-62964490579/68719476736)), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((484681869747859/2251799813685248), (-631592261867057/2251799813685248)), (11817/2251799813685248), by norm_num⟩
  | 1 => ⟨((-164040952873/549755813888), (213762888465/549755813888)), (3/274877906944), by norm_num⟩
  | 2 => ⟨((227409047961/1099511627776), (-18521142931/68719476736)), (11/1099511627776), by norm_num⟩
  | 3 => ⟨((-210170587237/2199023255552), (273874730739/2199023255552)), (13/2199023255552), by norm_num⟩
  | 4 => ⟨((36419787495/1099511627776), (-94917748719/2199023255552)), (11/4398046511104), by norm_num⟩
  | 5 => ⟨((-20195418415/2199023255552), (210534303711/17592186044416)), (7/8796093022208), by norm_num⟩
  | 6 => ⟨((37329059559/17592186044416), (-97287506019/35184372088832)), (15/70368744177664), by norm_num⟩
  | 7 => ⟨((-118283576623/281474976710656), (308272276575/562949953421312)), (13/281474976710656), by norm_num⟩
  | 8 => ⟨((81987927643/1125899906842624), (-213678059353/2251799813685248)), (5/562949953421312), by norm_num⟩
  | 9 => ⟨((-202061158705/18014398509481984), (4114176233/281474976710656)), (27/18014398509481984), by norm_num⟩
  | 10 => ⟨((224092995931/144115188075855872), (-146008558399/72057594037927936)), (1/4503599627370496), by norm_num⟩
  | 11 => ⟨((-112966856955/576460752303423488), (294415768995/1152921504606846976)), (35/1152921504606846976), by norm_num⟩
  | 12 => ⟨((104403544527/4611686018427387904), (-136048973461/4611686018427387904)), (35/9223372036854775808), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791310707357967/5070602400912917605986812821504), (-9324398775/79228162514264337593543950336)), (5/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780364751736293/633825300114114700748351602688), (-1414884921029/633825300114114700748351602688)), (3/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945768535317903/19807040628566084398385987584), (-1591596791143/39614081257132168796771975168)), (7/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945712016723153/1237940039285380274899124224), (-845446023999/1237940039285380274899124224)), (15/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773089932239161/154742504910672534362390528), (-211336260625/19342813113834066795298816)), (15/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551333594850289/9671406556917033397649408), (-1584807394359/9671406556917033397649408)), (7/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260345959412663/604462909807314587353088), (-1386491938257/604462909807314587353088)), (3/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((472580479962449/18889465931478580854784), (-2252647213137/75557863725914323419136)), (19/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324859062062759/1180591620717411303424), (-1689133557239/4722366482869645213696)), (15/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812027607126981/295147905179352825856), (-2321986994325/590295810358705651712)), (19/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913366001260635/36893488147419103232), (-2901626471401/73786976294838206464)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1826319388530103/9223372036854775808), (-3263151355043/9223372036854775808)), (27/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597565312670261/1152921504606846976), (-3261678807931/1152921504606846976)), (27/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598854940194599/72057594037927936), (-2852313007515/144115188075855872)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((748162638514061/18014398509481984), (-4275159277315/36028797018963968)), (35/36028797018963968), by norm_num⟩
  | 3 => ⟨((186888423144695/1125899906842624), (-5338159932395/9007199254740992)), (11/2251799813685248), by norm_num⟩
  | 2 => ⟨((2239617115927439/4503599627370496), (-10658967348599/4503599627370496)), (87/4503599627370496), by norm_num⟩
  | 1 => ⟨((279191438864097/281474976710656), (-3986280532919/562949953421312)), (65/1125899906842624), by norm_num⟩
  | 0 => ⟨((2215286393606647/2251799813685248), (-31717242944091/2251799813685248)), (261/2251799813685248), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((2215286393606647/2251799813685248), (-31717242944091/2251799813685248)), (995644576262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1089459150049603/1125899906842624), (-62405882005799/2251799813685248)), (261/1125899906842624), by norm_num⟩
  | 2 => ⟨((2106666159028899/2251799813685248), (-120772119714967/2251799813685248)), (65/140737488355328), by norm_num⟩
  | 3 => ⟨((982204628895895/1125899906842624), (-56494040014445/562949953421312)), (2059/2251799813685248), by norm_num⟩
  | 4 => ⟨((1691019993891821/2251799813685248), (-49283872633781/281474976710656)), (2003/1125899906842624), by norm_num⟩
  | 5 => ⟨((1200861194140667/2251799813685248), (-592166415459457/2251799813685248)), (1855/562949953421312), by norm_num⟩
  | 6 => ⟨((484681869747859/2251799813685248), (-631592261867057/2251799813685248)), (11817/2251799813685248), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-285796269295/274877906944), (-62964490579/68719476736)), (1/137438953472), by norm_num⟩, 0, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-41474899193/34359738368), (-18274877457/17179869184)), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((654060669983735/4503599627370496), (-294355068841129/1125899906842624)), (42939/4503599627370496), by norm_num⟩
  | 1 => ⟨((-128499760657/549755813888), (115660695193/274877906944)), (5/274877906944), by norm_num⟩
  | 2 => ⟨((51703096635/274877906944), (-93074353911/274877906944)), (9/549755813888), by norm_num⟩
  | 3 => ⟨((-110950565219/1099511627776), (199729858479/1099511627776)), (3/274877906944), by norm_num⟩
  | 4 => ⟨((178568046069/4398046511104), (-321452806481/4398046511104)), (21/4398046511104), by norm_num⟩
  | 5 => ⟨((-114957673317/8796093022208), (206943333523/8796093022208)), (15/8796093022208), by norm_num⟩
  | 6 => ⟨((61672412587/17592186044416), (-55510407783/8796093022208)), (9/17592186044416), by norm_num⟩
  | 7 => ⟨((-113437621679/140737488355328), (204206982447/140737488355328)), (9/70368744177664), by norm_num⟩
  | 8 => ⟨((91285404513/562949953421312), (-164329229767/562949953421312)), (31/1125899906842624), by norm_num⟩
  | 9 => ⟨((-32648486861/1125899906842624), (235091282229/4503599627370496)), (3/562949953421312), by norm_num⟩
  | 10 => ⟨((168146280121/36028797018963968), (-151345929001/18014398509481984)), (33/36028797018963968), by norm_num⟩
  | 11 => ⟨((-98407635659/144115188075855872), (44287613823/36028797018963968)), (21/144115188075855872), by norm_num⟩
  | 12 => ⟨((52793659901/576460752303423488), (-11879694123/72057594037927936)), (3/144115188075855872), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582403412673669/10141204801825835211973625643008), (-692818671477/5070602400912917605986812821504)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222513247646075/79228162514264337593543950336), (-821088800353/316912650057057350374175801344)), (3/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1891245961474419/39614081257132168796771975168), (-1847249910219/39614081257132168796771975168)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472778684505177/618970019642690137449562112), (-490615277259/618970019642690137449562112)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((27699697592043/2417851639229258349412352), (-490547245933/38685626227668133590597632)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1551043648552809/9671406556917033397649408), (-1839263078787/9671406556917033397649408)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260092266067369/604462909807314587353088), (-402266536275/151115727451828646838272)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((7382459712143/295147905179352825856), (-2614190614033/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162390886124371/590295810358705651712), (-490042229387/1180591620717411303424)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811815073078611/295147905179352825856), (-336807764943/73786976294838206464)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826200706296309/73786976294838206464), (-841730686833/18446744073709551616)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((228215216735181/1152921504606846976), (-3786200605723/9223372036854775808)), (27/4611686018427387904), by norm_num⟩
  | 6 => ⟨((798483862605329/576460752303423488), (-3784217007369/1152921504606846976)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197187067201757/144115188075855872), (-3308959375267/144115188075855872)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495541209555523/36028797018963968), (-4958980654909/36028797018963968)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((373531892192447/2251799813685248), (-3095464731489/4503599627370496)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((2237658292650001/4503599627370496), (-1544811660591/562949953421312)), (173/4503599627370496), by norm_num⟩
  | 1 => ⟨((278824414927679/281474976710656), (-9239703890043/1125899906842624)), (65/562949953421312), by norm_num⟩
  | 0 => ⟨((2209422301940695/2251799813685248), (-36725978435399/2251799813685248)), (521/2251799813685248), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((2209422301940695/2251799813685248), (-36725978435399/2251799813685248)), (1987465865325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1083621661473107/1125899906842624), (-72069635429063/2251799813685248)), (65/140737488355328), by norm_num⟩
  | 2 => ⟨((2083555367573129/2251799813685248), (-69363375563649/1125899906842624)), (2069/2251799813685248), by norm_num⟩
  | 3 => ⟨((959667425140967/1125899906842624), (-64180853284693/562949953421312)), (4085/2251799813685248), by norm_num⟩
  | 4 => ⟨((1606687830181543/2251799813685248), (-54704928778079/281474976710656)), (987/281474976710656), by norm_num⟩
  | 5 => ⟨((1061336579851139/2251799813685248), (-624522608338563/2251799813685248)), (7169/1125899906842624), by norm_num⟩
  | 6 => ⟨((654060669983735/4503599627370496), (-294355068841129/1125899906842624)), (42939/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-41474899193/34359738368), (-18274877457/17179869184)), (1/68719476736), by norm_num⟩, 0, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-184693159743/137438953472), (-10172552939/8589934592)), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((442881807857227/4503599627370496), (-1088071173592351/4503599627370496)), (39775/4503599627370496), by norm_num⟩
  | 1 => ⟨((-96867391721/549755813888), (237983621641/549755813888)), (5/274877906944), by norm_num⟩
  | 2 => ⟨((21695383297/137438953472), (-106602351899/274877906944)), (11/549755813888), by norm_num⟩
  | 3 => ⟨((-103661089229/1099511627776), (127337182305/549755813888)), (15/1099511627776), by norm_num⟩
  | 4 => ⟨((23216967277/549755813888), (-57039400545/549755813888)), (15/2199023255552), by norm_num⟩
  | 5 => ⟨((-133117507089/8796093022208), (163521417673/4398046511104)), (23/8796093022208), by norm_num⟩
  | 6 => ⟨((159009702565/35184372088832), (-390654731383/35184372088832)), (15/17592186044416), by norm_num⟩
  | 7 => ⟨((-81402040077/70368744177664), (199988375473/70368744177664)), (17/70368744177664), by norm_num⟩
  | 8 => ⟨((145852876123/562949953421312), (-179165532745/281474976710656)), (33/562949953421312), by norm_num⟩
  | 9 => ⟨((-7259257553/140737488355328), (2229316249/17592186044416)), (7/562949953421312), by norm_num⟩
  | 10 => ⟨((83243798145/9007199254740992), (-12782075197/562949953421312)), (11/4503599627370496), by norm_num⟩
  | 11 => ⟨((-108474809877/72057594037927936), (16656294015/4503599627370496)), (15/36028797018963968), by norm_num⟩
  | 12 => ⟨((32393461295/144115188075855872), (-159168386793/288230376151711744)), (19/288230376151711744), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582225292035643/10141204801825835211973625643008), (-385651538803/2535301200456458802993406410752)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889947281018465/316912650057057350374175801344), (-913898005839/316912650057057350374175801344)), (23/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472752030562537/9903520314283042199192993792), (-2056023370115/39614081257132168796771975168)), (27/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890862041335641/2475880078570760549798248448), (-2184225069285/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((443131989411333/38685626227668133590597632), (-2183887886699/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775403381149993/4835703278458516698824704), (-1023518346009/4835703278458516698824704)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629942499792403/302231454903657293676544), (-1790798965315/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944786447576193/37778931862957161709568), (-1454688468285/37778931862957161709568)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298874510420195/4722366482869645213696), (-545361343479/1180591620717411303424)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811641437349939/295147905179352825856), (-1499266612761/295147905179352825856)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456441663294585/18446744073709551616), (-1873367857781/36893488147419103232)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912616737016247/4611686018427387904), (-4213111004695/9223372036854775808)), (27/4611686018427387904), by norm_num⟩
  | 6 => ⟨((24944992624069/18014398509481984), (-2105326853057/576460752303423488)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149594995657003/18014398509481984), (-115048717791/4503599627370496)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494900698628961/36028797018963968), (-5516815999461/36028797018963968)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((746663590040453/4503599627370496), (-6886363784899/9007199254740992)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((2236058271097953/4503599627370496), (-6871895619365/2251799813685248)), (173/4503599627370496), by norm_num⟩
  | 1 => ⟨((278524649662659/281474976710656), (-10271729535367/1125899906842624)), (65/562949953421312), by norm_num⟩
  | 0 => ⟨((1102316910923199/1125899906842624), (-40798684813289/2251799813685248)), (523/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((1102316910923199/1125899906842624), (-40798684813289/2251799813685248)), (1995095259856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((539429140882959/562949953421312), (-79888238625461/2251799813685248)), (261/562949953421312), by norm_num⟩
  | 2 => ⟨((2064730003800789/2251799813685248), (-38275199834801/562949953421312)), (519/562949953421312), by norm_num⟩
  | 3 => ⟨((1882791759760539/2251799813685248), (-140381845704213/1125899906842624)), (4091/2251799813685248), by norm_num⟩
  | 4 => ⟨((769623600451497/1125899906842624), (-469508489530077/2251799813685248)), (3931/1125899906842624), by norm_num⟩
  | 5 => ⟨((477139155685011/1125899906842624), (-320938666002741/1125899906842624)), (3507/562949953421312), by norm_num⟩
  | 6 => ⟨((442881807857227/4503599627370496), (-1088071173592351/4503599627370496)), (39775/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-184693159743/137438953472), (-10172552939/8589934592)), (1/68719476736), by norm_num⟩, 0, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-200582890827/137438953472), (-88381836271/68719476736)), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((146949581875483/2251799813685248), (-1004375657388785/4503599627370496)), (2311/281474976710656), by norm_num⟩
  | 1 => ⟨((-69812178411/549755813888), (59644311071/137438953472)), (5/274877906944), by norm_num⟩
  | 2 => ⟨((67924113249/549755813888), (-232124940493/549755813888)), (11/549755813888), by norm_num⟩
  | 3 => ⟨((-44058073779/549755813888), (301129518369/1099511627776)), (1/68719476736), by norm_num⟩
  | 4 => ⟨((42866526457/1099511627776), (-292985492987/2199023255552)), (17/2199023255552), by norm_num⟩
  | 5 => ⟨((-33365763555/2199023255552), (57012344433/1099511627776)), (15/4398046511104), by norm_num⟩
  | 6 => ⟨((86569037243/17592186044416), (-73960599769/4398046511104)), (21/17592186044416), by norm_num⟩
  | 7 => ⟨((-48130162333/35184372088832), (328961558219/70368744177664)), (25/70368744177664), by norm_num⟩
  | 8 => ⟨((93656971359/281474976710656), (-320064817393/281474976710656)), (13/140737488355328), by norm_num⟩
  | 9 => ⟨((-80999133821/1125899906842624), (138403861449/562949953421312)), (3/140737488355328), by norm_num⟩
  | 10 => ⟨((63046814627/4503599627370496), (-215457182929/4503599627370496)), (5/1125899906842624), by norm_num⟩
  | 11 => ⟨((-89224317417/36028797018963968), (304916595599/36028797018963968)), (15/18014398509481984), by norm_num⟩
  | 12 => ⟨((14468542067/36028797018963968), (-395560198661/288230376151711744)), (41/288230376151711744), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582074693182031/10141204801825835211973625643008), (-104707587185/633825300114114700748351602688)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1779715817999195/633825300114114700748351602688), (-1984668729407/633825300114114700748351602688)), (3/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1890807042090271/39614081257132168796771975168), (-1116230711345/19807040628566084398385987584)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945324200318721/1237940039285380274899124224), (-2371636776831/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772314324803503/154742504910672534362390528), (-2371239169617/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((96912905616781/604462909807314587353088), (-555653583489/2417851639229258349412352)), (27/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157463721197075/75557863725914323419136), (-1944365233501/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889288162106263/75557863725914323419136), (-3158801843143/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324665243603207/1180591620717411303424), (-2368408846243/4722366482869645213696)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811494642561975/295147905179352825856), (-3255437106463/590295810358705651712)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912699849970259/36893488147419103232), (-2033804673467/36893488147419103232)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456205174538175/2305843009213693952), (-2286870866733/4611686018427387904)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596066810398013/1152921504606846976), (-2285422297613/576460752303423488)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196398903305683/144115188075855872), (-3996231581111/144115188075855872)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494359238174969/36028797018963968), (-2993918546545/18014398509481984)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((373162646962351/2251799813685248), (-7473413727523/9007199254740992)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117352896334575/2251799813685248), (-7456360458503/2251799813685248)), (173/4503599627370496), by norm_num⟩
  | 1 => ⟨((2226170265758689/2251799813685248), (-22283959782013/2251799813685248)), (65/562949953421312), by norm_num⟩
  | 0 => ⟨((1100293614320961/1125899906842624), (-44228301113339/2251799813685248)), (523/2251799813685248), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1100293614320961/1125899906842624), (-44228301113339/2251799813685248)), (1995095259856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1074835333679261/1125899906842624), (-86444837576621/2251799813685248)), (261/562949953421312), by norm_num⟩
  | 2 => ⟨((2048854982631625/2251799813685248), (-41262089674595/562949953421312)), (1037/1125899906842624), by norm_num⟩
  | 3 => ⟨((1852103261488395/2251799813685248), (-37543318686589/281474976710656)), (4079/2251799813685248), by norm_num⟩
  | 4 => ⟨((185411599486139/281474976710656), (-247034758823367/1125899906842624)), (7799/2251799813685248), by norm_num⟩
  | 5 => ⟨((217165488932565/562949953421312), (-650901338333839/2251799813685248)), (6849/1125899906842624), by norm_num⟩
  | 6 => ⟨((146949581875483/2251799813685248), (-1004375657388785/4503599627370496)), (2311/281474976710656), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-200582890827/137438953472), (-88381836271/68719476736)), (1/68719476736), by norm_num⟩, 0, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-214347201971/137438953472), (-188893471737/137438953472)), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((184765912030119/4503599627370496), (-928561195263071/4503599627370496)), (69321/9007199254740992), by norm_num⟩
  | 1 => ⟨((-46900624141/549755813888), (235704189871/549755813888)), (5/274877906944), by norm_num⟩
  | 2 => ⟨((48763553085/549755813888), (-245066541983/549755813888)), (3/137438953472), by norm_num⟩
  | 3 => ⟨((-33800319335/549755813888), (339734365251/1099511627776)), (19/1099511627776), by norm_num⟩
  | 4 => ⟨((70285788147/2199023255552), (-44153609515/274877906944)), (11/1099511627776), by norm_num⟩
  | 5 => ⟨((-58462075065/4398046511104), (146903759745/2199023255552)), (5/1099511627776), by norm_num⟩
  | 6 => ⟨((40522822501/8796093022208), (-101825926881/4398046511104)), (15/8796093022208), by norm_num⟩
  | 7 => ⟨((-24075668713/17592186044416), (241989785573/35184372088832)), (5/8796093022208), by norm_num⟩
  | 8 => ⟨((25031972833/70368744177664), (-31450225799/17592186044416)), (23/140737488355328), by norm_num⟩
  | 9 => ⟨((-23134455191/281474976710656), (232529443633/562949953421312)), (23/562949953421312), by norm_num⟩
  | 10 => ⟨((76970795469/4503599627370496), (-96706276951/1125899906842624)), (41/4503599627370496), by norm_num⟩
  | 11 => ⟨((-58202279853/18014398509481984), (36562736297/2251799813685248)), (33/18014398509481984), by norm_num⟩
  | 12 => ⟨((80685492365/144115188075855872), (-202746860623/72057594037927936)), (49/144115188075855872), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238521213/10141204801825835211973625643008), (-27973196325/158456325028528675187087900672)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889780494505785/316912650057057350374175801344), (-1060254805983/316912650057057350374175801344)), (23/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945316432990339/19807040628566084398385987584), (-2385241714933/39614081257132168796771975168)), (27/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945231672517167/1237940039285380274899124224), (-1266957866433/1237940039285380274899124224)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772129276541543/154742504910672534362390528), (-2533461772371/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387608253733311/2417851639229258349412352), (-2374638164117/9671406556917033397649408)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259557986830257/604462909807314587353088), (-2077326242331/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118065095614655/4722366482869645213696), (-1687375657289/37778931862957161709568)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298476013088393/4722366482869645213696), (-2530272839779/4722366482869645213696)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622734984278247/590295810358705651712), (-1738920368951/295147905179352825856)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825081855427547/73786976294838206464), (-4345374967703/73786976294838206464)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824463166580393/9223372036854775808), (-2442949870201/4611686018427387904)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398927333350941/288230376151711744), (-4882592501377/1152921504606846976)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196086172606563/144115188075855872), (-4268550040773/144115188075855872)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((746945133071487/18014398509481984), (-6395393878693/36028797018963968)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((1492064591353631/9007199254740992), (-3990625202483/4503599627370496)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((2233534461351935/4503599627370496), (-3980893865561/1125899906842624)), (173/4503599627370496), by norm_num⟩
  | 1 => ⟨((2224414944031653/2251799813685248), (-23788226417497/2251799813685248)), (261/2251799813685248), by norm_num⟩
  | 0 => ⟨((549270852974813/562949953421312), (-23594482262829/1125899906842624)), (131/562949953421312), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((549270852974813/562949953421312), (-23594482262829/1125899906842624)), (499727489280523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((133919229052533/140737488355328), (-92084643185353/2251799813685248)), (1045/2251799813685248), by norm_num⟩
  | 2 => ⟨((508783743519789/562949953421312), (-87623451058221/1125899906842624)), (2075/2251799813685248), by norm_num⟩
  | 3 => ⟨((456419667173997/562949953421312), (-316769810023663/2251799813685248)), (4075/2251799813685248), by norm_num⟩
  | 4 => ⟨((179454200876457/281474976710656), (-513651241582275/2251799813685248)), (7755/2251799813685248), by norm_num⟩
  | 5 => ⟨((798119905988009/2251799813685248), (-81869509471619/281474976710656)), (3357/562949953421312), by norm_num⟩
  | 6 => ⟨((184765912030119/4503599627370496), (-928561195263071/4503599627370496)), (69321/9007199254740992), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-214347201971/137438953472), (-188893471737/137438953472)), (1/68719476736), by norm_num⟩, 0, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile001Terms0

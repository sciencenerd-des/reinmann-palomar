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
namespace Reinmann.XiRectangle.Tile000Terms0
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
  | 0 => ⟨((-285796269295/549755813888), (-83952654105/549755813888)), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((41354580299389/70368744177664), (-101836299975461/1125899906842624)), (5767/2251799813685248), by norm_num⟩
  | 1 => ⟨((-223943833889/549755813888), (68933148639/1099511627776)), (1/274877906944), by norm_num⟩
  | 2 => ⟨((19403254633/137438953472), (-23890408813/1099511627776)), (1/549755813888), by norm_num⟩
  | 3 => ⟨((-286918639841/8796093022208), (22079426015/4398046511104)), (5/8796093022208), by norm_num⟩
  | 4 => ⟨((12429802891/2199023255552), (-61217167563/70368744177664)), (9/70368744177664), by norm_num⟩
  | 5 => ⟨((-441122960835/562949953421312), (67892011357/562949953421312)), (3/140737488355328), by norm_num⟩
  | 6 => ⟨((407684182111/4503599627370496), (-62745541673/4503599627370496)), (13/4503599627370496), by norm_num⟩
  | 7 => ⟨((-161477223651/18014398509481984), (12426255801/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 8 => ⟨((447709929193/576460752303423488), (-68905793387/576460752303423488)), (19/576460752303423488), by norm_num⟩
  | 9 => ⟨((-275847889003/4611686018427387904), (10613745869/1152921504606846976)), (7/2305843009213693952), by norm_num⟩
  | 10 => ⟨((305925098441/73786976294838206464), (-47084083355/73786976294838206464)), (9/36893488147419103232), by norm_num⟩
  | 11 => ⟨((-308437991923/1180591620717411303424), (47470835821/1180591620717411303424)), (5/295147905179352825856), by norm_num⟩
  | 12 => ⟨((285057232639/18889465931478580854784), (-43872368011/18889465931478580854784)), (5/4722366482869645213696), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791649295455329/5070602400912917605986812821504), (-198920507199/10141204801825835211973625643008)), (5/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1781168905383539/633825300114114700748351602688), (-236016127901/633825300114114700748351602688)), (7/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1892441741935109/39614081257132168796771975168), (-16594104367/2475880078570760549798248448)), (7/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1892385246971227/2475880078570760549798248448), (-282084802529/2475880078570760549798248448)), (1/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1774051146047545/154742504910672534362390528), (-70516990153/38685626227668133590597632)), (7/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((776117366539255/4835703278458516698824704), (-264420819921/9671406556917033397649408)), (1/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1261134455624611/604462909807314587353088), (-115675162917/302231454903657293676544)), (7/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1891603226642161/75557863725914323419136), (-375910736043/75557863725914323419136)), (5/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((325099307173377/1180591620717411303424), (-1101186347/18446744073709551616)), (1/590295810358705651712), by norm_num⟩
  | 9 => ⟨((406344140711543/147573952589676412928), (-193784955571/295147905179352825856)), (5/295147905179352825856), by norm_num⟩
  | 8 => ⟨((914191844421901/36893488147419103232), (-484390875273/73786976294838206464)), (3/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1828177536210607/9223372036854775808), (-544841421031/9223372036854775808)), (7/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1599423460711123/1152921504606846976), (-272359277699/576460752303423488)), (7/576460752303423488), by norm_num⟩
  | 5 => ⟨((1199335759850579/144115188075855872), (-238245274235/72057594037927936)), (13/144115188075855872), by norm_num⟩
  | 4 => ⟨((1498764094873157/36028797018963968), (-357229769255/18014398509481984)), (9/18014398509481984), by norm_num⟩
  | 3 => ⟨((749077951206785/4503599627370496), (-13946736407/140737488355328)), (11/4503599627370496), by norm_num⟩
  | 2 => ⟨((1122857062266307/2251799813685248), (-1783733197495/4503599627370496)), (11/1125899906842624), by norm_num⟩
  | 1 => ⟨((2242676921478875/2251799813685248), (-2671979996511/2251799813685248)), (65/2251799813685248), by norm_num⟩
  | 0 => ⟨((1116788290247815/1125899906842624), (-5329497922263/2251799813685248)), (129/2251799813685248), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((1116788290247815/1125899906842624), (-5329497922263/2251799813685248)), (492104537200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2215488209507321/2251799813685248), (-10572735349405/2251799813685248)), (129/1125899906842624), by norm_num⟩
  | 2 => ⟨((34058007967555/35184372088832), (-20804487473967/2251799813685248)), (511/2251799813685248), by norm_num⟩
  | 3 => ⟨((2109740737318527/2251799813685248), (-2517308673153/140737488355328)), (125/281474976710656), by norm_num⟩
  | 4 => ⟨((123495207030161/140737488355328), (-75471982884155/2251799813685248)), (1911/2251799813685248), by norm_num⟩
  | 5 => ⟨((1731315942437761/2251799813685248), (-132451250340971/2251799813685248)), (3483/2251799813685248), by norm_num⟩
  | 6 => ⟨((41354580299389/70368744177664), (-101836299975461/1125899906842624)), (5767/2251799813685248), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-285796269295/549755813888), (-83952654105/549755813888)), (1/274877906944), by norm_num⟩, 0, term2ValuePoly, term2ValueSquares⟩

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
  | 0 => ⟨((-226488184839/274877906944), (-8316363037/34359738368)), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((239762721347311/562949953421312), (-29596052913179/281474976710656)), (2293/562949953421312), by norm_num⟩
  | 1 => ⟨((-16077042971/34359738368), (63505053567/549755813888)), (5/549755813888), by norm_num⟩
  | 2 => ⟨((141299495787/549755813888), (-69767432241/1099511627776)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-413955633211/4398046511104), (51098238939/2199023255552)), (7/2199023255552), by norm_num⟩
  | 4 => ⟨((56847093201/2199023255552), (-14034288307/2199023255552)), (5/4398046511104), by norm_num⟩
  | 5 => ⟨((-99924664265/17592186044416), (98676746219/70368744177664)), (5/17592186044416), by norm_num⟩
  | 6 => ⟨((73185642735/70368744177664), (-72271657335/281474976710656)), (17/281474976710656), by norm_num⟩
  | 7 => ⟨((-183777477629/1125899906842624), (45370589069/1125899906842624)), (3/281474976710656), by norm_num⟩
  | 8 => ⟨((403800390607/18014398509481984), (-99689373391/18014398509481984)), (29/18014398509481984), by norm_num⟩
  | 9 => ⟨((-197164476129/72057594037927936), (24337771257/36028797018963968)), (31/144115188075855872), by norm_num⟩
  | 10 => ⟨((346571706183/1152921504606846976), (-42780439331/576460752303423488)), (15/576460752303423488), by norm_num⟩
  | 11 => ⟨((-138453794661/4611686018427387904), (34181175537/4611686018427387904)), (13/4611686018427387904), by norm_num⟩
  | 12 => ⟨((405618773939/147573952589676412928), (-100138291963/147573952589676412928)), (41/147573952589676412928), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582902468230365/10141204801825835211973625643008), (-157640772267/5070602400912917605986812821504)), (5/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780698984685311/633825300114114700748351602688), (-93472363253/158456325028528675187087900672)), (3/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472978277612617/9903520314283042199192993792), (-420594518099/39614081257132168796771975168)), (13/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945911805611791/1237940039285380274899124224), (-446844092035/2475880078570760549798248448)), (15/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773489549902055/154742504910672534362390528), (-446801815869/154742504910672534362390528)), (15/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1551708278765831/9671406556917033397649408), (-209415894727/4835703278458516698824704)), (13/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1260673850170715/604462909807314587353088), (-22902056815/37778931862957161709568)), (3/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1890854821651725/75557863725914323419136), (-297684645111/37778931862957161709568)), (19/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299835993955269/4722366482869645213696), (-446453317221/4722366482869645213696)), (7/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624604977197543/590295810358705651712), (-306876826929/295147905179352825856)), (19/590295810358705651712), by norm_num⟩
  | 8 => ⟨((114213710933105/4611686018427387904), (-767012624477/73786976294838206464)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((913546457106687/4611686018427387904), (-215660634675/2305843009213693952)), (27/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1598339127590835/1152921504606846976), (-1684246707/2251799813685248)), (27/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1198387293263065/144115188075855872), (-754195916363/144115188075855872)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((1497342044542869/36028797018963968), (-1130601018723/36028797018963968)), (35/36028797018963968), by norm_num⟩
  | 3 => ⟨((1496379475687481/9007199254740992), (-1412039587355/9007199254740992)), (11/2251799813685248), by norm_num⟩
  | 2 => ⟨((2242164677531801/4503599627370496), (-176277960059/281474976710656)), (87/4503599627370496), by norm_num⟩
  | 1 => ⟨((2237361259728533/2251799813685248), (-4221602852497/2251799813685248)), (129/2251799813685248), by norm_num⟩
  | 0 => ⟨((2222979247763521/2251799813685248), (-2101750235957/562949953421312)), (129/1125899906842624), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((2222979247763521/2251799813685248), (-2101750235957/562949953421312)), (492100242232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2194496166262283/2251799813685248), (-16598801119423/2251799813685248)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((2138528422586663/2251799813685248), (-16176395965461/1125899906842624)), (503/1125899906842624), by norm_num⟩
  | 3 => ⟨((507622511921077/562949953421312), (-61450724592679/2251799813685248)), (1941/2251799813685248), by norm_num⟩
  | 4 => ⟨((1829253922643685/2251799813685248), (-110822537554277/2251799813685248)), (451/281474976710656), by norm_num⟩
  | 5 => ⟨((1480543811406205/2251799813685248), (-11253362771551/140737488355328)), (3109/1125899906842624), by norm_num⟩
  | 6 => ⟨((239762721347311/562949953421312), (-29596052913179/281474976710656)), (2293/562949953421312), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-226488184839/274877906944), (-8316363037/34359738368)), (1/137438953472), by norm_num⟩, 0, term3ValuePoly, term3ValueSquares⟩

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
  | 0 => ⟨((-285796269295/274877906944), (-83952654105/274877906944)), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((1518575145853109/4503599627370496), (-478780457879941/4503599627370496)), (15633/4503599627370496), by norm_num⟩
  | 1 => ⟨((-256981465043/549755813888), (10127725967/68719476736)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((178125977951/549755813888), (-14040009399/137438953472)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-329246718403/2199023255552), (103805791253/2199023255552)), (5/1099511627776), by norm_num⟩
  | 4 => ⟨((114108217285/2199023255552), (-71952691533/4398046511104)), (9/4398046511104), by norm_num⟩
  | 5 => ⟨((-253100125087/17592186044416), (4987380527/1099511627776)), (3/4398046511104), by norm_num⟩
  | 6 => ⟨((116957092069/35184372088832), (-18437273337/17592186044416)), (13/70368744177664), by norm_num⟩
  | 7 => ⟨((-370598759379/562949953421312), (116843373995/562949953421312)), (23/562949953421312), by norm_num⟩
  | 8 => ⟨((256879485183/2251799813685248), (-20247413813/562949953421312)), (9/1125899906842624), by norm_num⟩
  | 9 => ⟨((-316542739375/18014398509481984), (24950111641/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 10 => ⟨((351057131719/144115188075855872), (-110682237047/144115188075855872)), (29/144115188075855872), by norm_num⟩
  | 11 => ⟨((-176970371685/576460752303423488), (111591389887/1152921504606846976)), (1/36028797018963968), by norm_num⟩
  | 12 => ⟨((163555352235/4611686018427387904), (-103132343033/9223372036854775808)), (1/288230376151711744), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791310707357967/5070602400912917605986812821504), (-198920507199/5070602400912917605986812821504)), (5/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780365701015961/633825300114114700748351602688), (-7369192297/9903520314283042199192993792)), (3/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472884548753463/9903520314283042199192993792), (-132633136711/9903520314283042199192993792)), (7/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1891425298195913/2475880078570760549798248448), (-563631017733/2475880078570760549798248448)), (15/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1773091275821633/154742504910672534362390528), (-140890934637/38685626227668133590597632)), (7/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193916867274009/1208925819614629174706176), (-528269531805/9671406556917033397649408)), (7/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((315086804634975/151115727451828646838272), (-115541094919/151115727451828646838272)), (3/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1890324122811195/75557863725914323419136), (-750883154657/75557863725914323419136)), (19/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299438037677971/4722366482869645213696), (-281522587685/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1624057897555987/590295810358705651712), (-773996730867/590295810358705651712)), (5/147573952589676412928), by norm_num⟩
  | 8 => ⟨((456683922674901/18446744073709551616), (-483605211137/36893488147419103232)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1826323996710827/9223372036854775808), (-33991228599/288230376151711744)), (7/2305843009213693952), by norm_num⟩
  | 6 => ⟨((399392623516685/288230376151711744), (-543614506857/576460752303423488)), (27/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197715058278911/144115188075855872), (-237693521933/36028797018963968)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((93520895653111/2251799813685248), (-1425059257327/36028797018963968)), (35/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495120949531549/9007199254740992), (-1779397420171/9007199254740992)), (11/2251799813685248), by norm_num⟩
  | 2 => ⟨((1119825485881269/2251799813685248), (-3553021394307/4503599627370496)), (87/4503599627370496), by norm_num⟩
  | 1 => ⟨((2233599057502589/2251799813685248), (-2657560615505/1125899906842624)), (65/1125899906842624), by norm_num⟩
  | 0 => ⟨((276936026188415/281474976710656), (-2643183837351/562949953421312)), (129/1125899906842624), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((276936026188415/281474976710656), (-2643183837351/562949953421312)), (492100242232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1089856254961759/1125899906842624), (-20804487473965/2251799813685248)), (511/2251799813685248), by norm_num⟩
  | 2 => ⟨((2109740737318523/2251799813685248), (-10069234692611/562949953421312)), (125/281474976710656), by norm_num⟩
  | 3 => ⟨((1975923312482569/2251799813685248), (-75471982884147/2251799813685248)), (955/1125899906842624), by norm_num⟩
  | 4 => ⟨((1731315942437749/2251799813685248), (-33112812585239/562949953421312)), (3481/2251799813685248), by norm_num⟩
  | 5 => ⟨((82709160598777/140737488355328), (-203672599950897/2251799813685248)), (5763/2251799813685248), by norm_num⟩
  | 6 => ⟨((1518575145853109/4503599627370496), (-478780457879941/4503599627370496)), (15633/4503599627370496), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-285796269295/274877906944), (-83952654105/274877906944)), (1/137438953472), by norm_num⟩, 0, term4ValuePoly, term4ValueSquares⟩

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
  | 0 => ⟨((-41474899193/34359738368), (-6091625819/17179869184)), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((1263103944866123/4503599627370496), (-467634781985547/4503599627370496)), (13783/4503599627370496), by norm_num⟩
  | 1 => ⟨((-248155197291/549755813888), (11484209401/68719476736)), (5/549755813888), by norm_num⟩
  | 2 => ⟨((12480949459/34359738368), (-73932488017/549755813888)), (11/1099511627776), by norm_num⟩
  | 3 => ⟨((-107132337293/549755813888), (39663249725/549755813888)), (1/137438953472), by norm_num⟩
  | 4 => ⟨((172422845287/2199023255552), (-127671075675/4398046511104)), (15/4398046511104), by norm_num⟩
  | 5 => ⟨((-55500772835/2199023255552), (82191467805/8796093022208)), (11/8796093022208), by norm_num⟩
  | 6 => ⟨((14887507995/2199023255552), (-88188042909/35184372088832)), (13/35184372088832), by norm_num⟩
  | 7 => ⟨((-109533804749/70368744177664), (81104674103/140737488355328)), (7/70368744177664), by norm_num⟩
  | 8 => ⟨((22035982257/70368744177664), (-130532937377/1125899906842624)), (3/140737488355328), by norm_num⟩
  | 9 => ⟨((-252199433117/4503599627370496), (5835684951/281474976710656)), (19/4503599627370496), by norm_num⟩
  | 10 => ⟨((162359731661/18014398509481984), (-60109904673/18014398509481984)), (13/18014398509481984), by norm_num⟩
  | 11 => ⟨((-190042114609/144115188075855872), (35179330725/72057594037927936)), (33/288230376151711744), by norm_num⟩
  | 12 => ⟨((203907322807/1152921504606846976), (-37745965735/576460752303423488)), (19/1152921504606846976), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582403412673669/10141204801825835211973625643008), (-230939557159/5070602400912917605986812821504)), (11/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780107260643353/633825300114114700748351602688), (-547392533569/633825300114114700748351602688)), (3/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1891247476326003/39614081257132168796771975168), (-615750413115/39614081257132168796771975168)), (7/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236389555244385/309485009821345068724781056), (-163538556759/618970019642690137449562112)), (15/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886391227993167/77371252455336267181195264), (-654063583979/154742504910672534362390528)), (7/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96940341141997/604462909807314587353088), (-306544159507/4835703278458516698824704)), (13/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((630046981139591/302231454903657293676544), (-536356007611/604462909807314587353088)), (3/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((236239081734963/9444732965739290427392), (-871398044559/75557863725914323419136)), (19/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649564749698541/2361183241434822606848), (-653390665377/4722366482869645213696)), (7/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623633760449345/590295810358705651712), (-898155706723/590295810358705651712)), (5/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1826205673818281/73786976294838206464), (-280577520387/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1825727940090691/9223372036854775808), (-1262070302879/9223372036854775808)), (27/9223372036854775808), by norm_num⟩
  | 6 => ⟨((399243675701881/288230376151711744), (-315352489765/288230376151711744)), (27/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598597019658091/72057594037927936), (-1102991280557/144115188075855872)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((747776699214567/18014398509481984), (-1653003185803/36028797018963968)), (35/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494145827449077/9007199254740992), (-128978749463/562949953421312)), (11/2251799813685248), by norm_num⟩
  | 2 => ⟨((1118851926619411/2251799813685248), (-2059774091045/2251799813685248)), (87/4503599627370496), by norm_num⟩
  | 1 => ⟨((1115343091334357/1125899906842624), (-6159928327579/2251799813685248)), (129/2251799813685248), by norm_num⟩
  | 0 => ⟨((1104846802406253/1125899906842624), (-6121246925077/1125899906842624)), (129/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1104846802406253/1125899906842624), (-6121246925077/1125899906842624)), (492100242232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2168308176783647/2251799813685248), (-12013572522403/1125899906842624)), (255/1125899906842624), by norm_num⟩
  | 2 => ⟨((2087655846331335/2251799813685248), (-23136272926569/1125899906842624)), (497/1125899906842624), by norm_num⟩
  | 3 => ⟨((1934526221090881/2251799813685248), (-21449764381329/562949953421312)), (1885/2251799813685248), by norm_num⟩
  | 4 => ⟨((1658686619972341/2251799813685248), (-73710160876143/1125899906842624)), (3383/2251799813685248), by norm_num⟩
  | 5 => ⟨((606072648070493/1125899906842624), (-108590521109579/1125899906842624)), (1357/562949953421312), by norm_num⟩
  | 6 => ⟨((1263103944866123/4503599627370496), (-467634781985547/4503599627370496)), (13783/4503599627370496), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-41474899193/34359738368), (-6091625819/17179869184)), (1/137438953472), by norm_num⟩, 0, term5ValuePoly, term5ValueSquares⟩

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
  | 0 => ⟨((-369386319487/274877906944), (-108507231349/274877906944)), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((542203375028599/2251799813685248), (-112945001813345/1125899906842624)), (12467/4503599627370496), by norm_num⟩
  | 1 => ⟨((-118591068293/274877906944), (98813611573/549755813888)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((53121667395/137438953472), (-5532819507/34359738368)), (5/549755813888), by norm_num⟩
  | 3 => ⟨((-253816668203/1099511627776), (105743805261/1099511627776)), (1/137438953472), by norm_num⟩
  | 4 => ⟨((227389209351/2199023255552), (-47366866097/1099511627776)), (9/2199023255552), by norm_num⟩
  | 5 => ⟨((-81485353811/2199023255552), (135792049371/8796093022208)), (15/8796093022208), by norm_num⟩
  | 6 => ⟨((194669539059/17592186044416), (-40551115051/8796093022208)), (5/8796093022208), by norm_num⟩
  | 7 => ⟨((-199314851417/70368744177664), (83037536435/70368744177664)), (3/17592186044416), by norm_num⟩
  | 8 => ⟨((357124272385/562949953421312), (-148783292209/562949953421312)), (3/70368744177664), by norm_num⟩
  | 9 => ⟨((-284391465217/2251799813685248), (118481721191/2251799813685248)), (21/2251799813685248), by norm_num⟩
  | 10 => ⟨((50956110077/2251799813685248), (-42458149175/4503599627370496)), (17/9007199254740992), by norm_num⟩
  | 11 => ⟨((-16600198681/4503599627370496), (13831780151/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 12 => ⟨((39658084237/72057594037927936), (-132177189663/576460752303423488)), (31/576460752303423488), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582225292035639/10141204801825835211973625643008), (-64275256467/1267650600228229401496703205376)), (11/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889948073907999/316912650057057350374175801344), (-76158167153/79228162514264337593543950336)), (3/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1891009999119625/39614081257132168796771975168), (-85667716835/4951760157141521099596496896)), (7/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890864152437635/2475880078570760549798248448), (-728075745815/2475880078570760549798248448)), (7/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886265100114787/77371252455336267181195264), (-727963441769/154742504910672534362390528)), (15/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550809004365027/9671406556917033397649408), (-341173213721/4835703278458516698824704)), (7/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259887100969261/604462909807314587353088), (-74616731451/75557863725914323419136)), (3/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944788285736215/37778931862957161709568), (-242448482517/18889465931478580854784)), (19/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162359687049589/590295810358705651712), (-363574936525/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811643675928307/295147905179352825856), (-62469585851/36893488147419103232)), (5/147573952589676412928), by norm_num⟩
  | 8 => ⟨((456443201582987/18446744073709551616), (-1248915350995/73786976294838206464)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1825241161071181/9223372036854775808), (-1404375069871/9223372036854775808)), (27/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798244084903835/576460752303423488), (-1403557149571/1152921504606846976)), (27/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196768599564141/144115188075855872), (-1227192970373/144115188075855872)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((186864473959213/4503599627370496), (-1838951945523/36028797018963968)), (9/9007199254740992), by norm_num⟩
  | 3 => ⟨((746674892846539/4503599627370496), (-1147738899217/4503599627370496)), (11/2251799813685248), by norm_num⟩
  | 2 => ⟨((1118057333219439/2251799813685248), (-1145333304363/1125899906842624)), (43/2251799813685248), by norm_num⟩
  | 1 => ⟨((2228309632525175/2251799813685248), (-3423996440953/1125899906842624)), (65/1125899906842624), by norm_num⟩
  | 0 => ⟨((137810584656067/140737488355328), (-13600251459541/2251799813685248)), (259/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((137810584656067/140737488355328), (-13600251459541/2251799813685248)), (988015181731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1079515340991815/1125899906842624), (-26634816735919/2251799813685248)), (511/2251799813685248), by norm_num⟩
  | 2 => ⟨((1034884194402817/1125899906842624), (-25537521671497/1125899906842624)), (993/2251799813685248), by norm_num⟩
  | 3 => ⟨((1901293577353949/2251799813685248), (-93892458402151/2251799813685248)), (1871/2251799813685248), by norm_num⟩
  | 4 => ⟨((800715377012335/1125899906842624), (-158555060744787/2251799813685248)), (3317/2251799813685248), by norm_num⟩
  | 5 => ⟨((1127738237304605/2251799813685248), (-28190222432273/281474976710656)), (2593/1125899906842624), by norm_num⟩
  | 6 => ⟨((542203375028599/2251799813685248), (-112945001813345/1125899906842624)), (12467/4503599627370496), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-369386319487/274877906944), (-108507231349/274877906944)), (1/137438953472), by norm_num⟩, 0, term6ValuePoly, term6ValueSquares⟩

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
  | 0 => ⟨((-401165781655/274877906944), (-117842448361/274877906944)), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((951788812561113/4503599627370496), (-435023259015141/4503599627370496)), (5719/2251799813685248), by norm_num⟩
  | 1 => ⟨((-56521469425/137438953472), (103334493993/549755813888)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((219971401987/549755813888), (-6283738769/34359738368)), (5/549755813888), by norm_num⟩
  | 3 => ⟨((-35670381969/137438953472), (130427637809/1099511627776)), (1/137438953472), by norm_num⟩
  | 4 => ⟨((34705679147/274877906944), (-126900232065/2199023255552)), (5/1099511627776), by norm_num⟩
  | 5 => ⟨((-108054613251/2199023255552), (98774579797/4398046511104)), (9/4398046511104), by norm_num⟩
  | 6 => ⟨((280352758103/17592186044416), (-128137638197/17592186044416)), (13/17592186044416), by norm_num⟩
  | 7 => ⟨((-311737872747/70368744177664), (142482474653/70368744177664)), (1/4398046511104), by norm_num⟩
  | 8 => ⟨((303306945211/281474976710656), (-138629046745/281474976710656)), (9/140737488355328), by norm_num⟩
  | 9 => ⟨((-262314694651/1125899906842624), (119893186229/1125899906842624)), (17/1125899906842624), by norm_num⟩
  | 10 => ⟨((204176330627/4503599627370496), (-46660273577/2251799813685248)), (15/4503599627370496), by norm_num⟩
  | 11 => ⟨((-288951850155/36028797018963968), (132067927143/36028797018963968)), (23/36028797018963968), by norm_num⟩
  | 12 => ⟨((46856194817/36028797018963968), (-171328213195/288230376151711744)), (1/9007199254740992), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791037346591013/5070602400912917605986812821504), (-558440464985/10141204801825835211973625643008)), (5/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889858844187403/316912650057057350374175801344), (-330778121567/316912650057057350374175801344)), (3/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890809255164179/39614081257132168796771975168), (-372077295307/19807040628566084398385987584)), (7/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945325444932643/1237940039285380274899124224), (-790546517685/2475880078570760549798248448)), (15/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((13846226320445/1208925819614629174706176), (-790414097359/154742504910672534362390528)), (7/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550609133417115/9671406556917033397649408), (-370436275097/4835703278458516698824704)), (7/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259712247197221/604462909807314587353088), (-81015356209/75557863725914323419136)), (3/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((59040390516573/2361183241434822606848), (-1052936019125/75557863725914323419136)), (19/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40583265462783/147573952589676412928), (-98683928389/590295810358705651712)), (15/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622994563403323/590295810358705651712), (-1085148644689/590295810358705651712)), (5/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912703476907223/36893488147419103232), (-677937096767/36893488147419103232)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1824829759857621/9223372036854775808), (-190573329883/1152921504606846976)), (27/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798038498534545/576460752303423488), (-1523622435349/1152921504606846976)), (27/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196409080299941/144115188075855872), (-666042850817/72057594037927936)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((1494377026160989/36028797018963968), (-1995962692009/36028797018963968)), (35/36028797018963968), by norm_num⟩
  | 3 => ⟨((746338613183905/4503599627370496), (-2491167600791/9007199254740992)), (11/2251799813685248), by norm_num⟩
  | 2 => ⟨((279346529633175/562949953421312), (-2485497926871/2251799813685248)), (87/4503599627370496), by norm_num⟩
  | 1 => ⟨((2226302699700651/2251799813685248), (-7428208121715/2251799813685248)), (129/2251799813685248), by norm_num⟩
  | 0 => ⟨((2200982262148393/2251799813685248), (-3685912275955/562949953421312)), (259/2251799813685248), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((2200982262148393/2251799813685248), (-3685912275955/562949953421312)), (988015181731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1075607501533451/1125899906842624), (-7205460707393/562949953421312)), (511/2251799813685248), by norm_num⟩
  | 2 => ⟨((513688568437147/562949953421312), (-6883602655773/281474976710656)), (991/2251799813685248), by norm_num⟩
  | 3 => ⟨((1873604627184841/2251799813685248), (-25124990045343/562949953421312)), (929/1125899906842624), by norm_num⟩
  | 4 => ⟨((1554442822021325/2251799813685248), (-83620750514029/1125899906842624)), (3259/2251799813685248), by norm_num⟩
  | 5 => ⟨((265157092645685/562949953421312), (-230897390822393/2251799813685248)), (4985/2251799813685248), by norm_num⟩
  | 6 => ⟨((951788812561113/4503599627370496), (-435023259015141/4503599627370496)), (5719/2251799813685248), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-401165781655/274877906944), (-117842448361/274877906944)), (1/137438953472), by norm_num⟩, 0, term7ValuePoly, term7ValueSquares⟩

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
  | 0 => ⟨((-214347201971/137438953472), (-62964490579/137438953472)), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((849137093641211/4503599627370496), (-52340610995321/562949953421312)), (5265/1125899906842624), by norm_num⟩
  | 1 => ⟨((-26942916063/68719476736), (53144160557/274877906944)), (7/549755813888), by norm_num⟩
  | 2 => ⟨((112052437831/274877906944), (-13813771895/68719476736)), (9/549755813888), by norm_num⟩
  | 3 => ⟨((-155337662715/549755813888), (153199632671/1099511627776)), (15/1099511627776), by norm_num⟩
  | 4 => ⟨((323015588837/2199023255552), (-159284840173/2199023255552)), (9/1099511627776), by norm_num⟩
  | 5 => ⟨((-268676813615/4398046511104), (66244702723/2199023255552)), (9/2199023255552), by norm_num⟩
  | 6 => ⟨((186232575839/8796093022208), (-91834657839/8796093022208)), (7/4398046511104), by norm_num⟩
  | 7 => ⟨((-221291288351/35184372088832), (6820171517/2199023255552)), (19/35184372088832), by norm_num⟩
  | 8 => ⟨((230081148905/140737488355328), (-113457183791/140737488355328)), (11/70368744177664), by norm_num⟩
  | 9 => ⟨((-212640132885/562949953421312), (104856702745/562949953421312)), (23/562949953421312), by norm_num⟩
  | 10 => ⟨((44217272575/562949953421312), (-174434706889/4503599627370496)), (41/4503599627370496), by norm_num⟩
  | 11 => ⟨((-33435357619/2251799813685248), (131900645751/18014398509481984)), (33/18014398509481984), by norm_num⟩
  | 12 => ⟨((185404990917/72057594037927936), (-22856640179/18014398509481984)), (25/72057594037927936), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581944238521213/10141204801825835211973625643008), (-9324398775/158456325028528675187087900672)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222445390611353/79228162514264337593543950336), (-353418268661/316912650057057350374175801344)), (23/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890635392578277/39614081257132168796771975168), (-795081527215/39614081257132168796771975168)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945233093436073/1237940039285380274899124224), (-211159926635/618970019642690137449562112)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772132295273055/154742504910672534362390528), (-422244263573/77371252455336267181195264)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775218016426843/4835703278458516698824704), (-791547403321/9671406556917033397649408)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259560815269145/604462909807314587353088), (-692443428909/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889046477880011/75557863725914323419136), (-1124919631581/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649240015880541/2361183241434822606848), (-421713244891/2361183241434822606848)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622741009463371/590295810358705651712), (-1159283835061/590295810358705651712)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825090135470345/73786976294838206464), (-724231851423/36893488147419103232)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456118377439363/2305843009213693952), (-814320319611/4611686018427387904)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595720960028835/1152921504606846976), (-1627540066135/1152921504606846976)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598048893714601/72057594037927936), (-1422860388731/144115188075855872)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((186738820693971/4503599627370496), (-1065909340881/18014398509481984)), (69/36028797018963968), by norm_num⟩
  | 3 => ⟨((728562005599/4398046511104), (-332556625299/1125899906842624)), (43/4503599627370496), by norm_num⟩
  | 2 => ⟨((1116805133205665/2251799813685248), (-5307966837579/4503599627370496)), (173/4503599627370496), by norm_num⟩
  | 1 => ⟨((2224565999586347/2251799813685248), (-7929678800839/2251799813685248)), (129/1125899906842624), by norm_num⟩
  | 0 => ⟨((1098766906737227/1125899906842624), (-15730729553505/2251799813685248)), (517/2251799813685248), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((1098766906737227/1125899906842624), (-15730729553505/2251799813685248)), (1972207076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2144465674152625/2251799813685248), (-30703271129483/2251799813685248)), (1017/2251799813685248), by norm_num⟩
  | 2 => ⟨((2041829077708367/2251799813685248), (-58479542116687/2251799813685248)), (983/1125899906842624), by norm_num⟩
  | 3 => ⟨((1849918496490065/2251799813685248), (-26513287020285/562949953421312)), (917/562949953421312), by norm_num⟩
  | 4 => ⟨((1514766611449289/2251799813685248), (-21781430020329/281474976710656)), (6373/2251799813685248), by norm_num⟩
  | 5 => ⟨((251371626043585/562949953421312), (-117217463981993/1125899906842624)), (9561/2251799813685248), by norm_num⟩
  | 6 => ⟨((849137093641211/4503599627370496), (-52340610995321/562949953421312)), (5265/1125899906842624), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-214347201971/137438953472), (-62964490579/137438953472)), (1/68719476736), by norm_num⟩, 0, term8ValuePoly, term8ValueSquares⟩

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
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile000Terms0

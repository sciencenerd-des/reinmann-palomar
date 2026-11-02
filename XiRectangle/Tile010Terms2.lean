/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile010Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨10,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (2961/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (2961/640))
  have he : value ((3/4), (2961/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-47632711549/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-17862266831/8589934592), (-110187858513/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-47632711549/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((1087714803474349/9007199254740992), (-72683864486309/2251799813685248)), (86099/2251799813685248), by norm_num⟩
  | 1 => ⟨((-5752154917/17179869184), (12299955015/137438953472)), (31/274877906944), by norm_num⟩
  | 2 => ⟨((31896719703/68719476736), (-17051358279/137438953472)), (23/137438953472), by norm_num⟩
  | 3 => ⟨((-58957656883/137438953472), (15758801221/137438953472)), (23/137438953472), by norm_num⟩
  | 4 => ⟨((40866333641/137438953472), (-21846337271/274877906944)), (17/137438953472), by norm_num⟩
  | 5 => ⟨((-45322214309/274877906944), (3028545417/68719476736)), (5/68719476736), by norm_num⟩
  | 6 => ⟨((83773240173/1099511627776), (-22391762315/1099511627776)), (39/1099511627776), by norm_num⟩
  | 7 => ⟨((-518457011/17179869184), (8869021095/1099511627776)), (33/2199023255552), by norm_num⟩
  | 8 => ⟨((45998977973/4398046511104), (-24590147865/8796093022208)), (3/549755813888), by norm_num⟩
  | 9 => ⟨((-28341388347/8796093022208), (946921759/1099511627776)), (31/17592186044416), by norm_num⟩
  | 10 => ⟨((62863210963/70368744177664), (-16802717375/70368744177664)), (9/17592186044416), by norm_num⟩
  | 11 => ⟨((-31689787229/140737488355328), (16940736253/281474976710656)), (19/140737488355328), by norm_num⟩
  | 12 => ⟨((29287582227/562949953421312), (-1957070595/140737488355328)), (37/1125899906842624), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581267062326477/10141204801825835211973625643008), (-340221836987/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778761564869979/633825300114114700748351602688), (-402631651303/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472433448018831/9903520314283042199192993792), (-452878433305/39614081257132168796771975168)), (203/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944754213721793/1237940039285380274899124224), (-481081293533/2475880078570760549798248448)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1771174750766699/154742504910672534362390528), (-480966539701/154742504910672534362390528)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((774769281583963/4835703278458516698824704), (-450784243579/9671406556917033397649408)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258775757508913/604462909807314587353088), (-197157184565/302231454903657293676544)), (177/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471942796691227/18889465931478580854784), (-320266242245/37778931862957161709568)), (575/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297523937544445/4722366482869645213696), (-480199635807/4722366482869645213696)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1621426987564961/590295810358705651712), (-164987528643/147573952589676412928)), (593/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911724259527753/36893488147419103232), (-412225684065/36893488147419103232)), (371/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911313971510119/4611686018427387904), (-926839651159/9223372036854775808)), (417/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398469239174343/288230376151711744), (-463002606727/576460752303423488)), (417/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194486041620003/144115188075855872), (-404658414345/72057594037927936)), (365/72057594037927936), by norm_num⟩
  | 4 => ⟨((745748228370005/18014398509481984), (-1212102297269/36028797018963968)), (1095/36028797018963968), by norm_num⟩
  | 3 => ⟨((744541742048141/4503599627370496), (-1511855879297/9007199254740992)), (1369/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227605618927139/4503599627370496), (-753479598139/1125899906842624)), (2737/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107802395706091/1125899906842624), (-4496473130221/2251799813685248)), (1027/562949953421312), by norm_num⟩
  | 0 => ⟨((136237102562509/140737488355328), (-8895800716793/2251799813685248)), (2057/562949953421312), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((136237102562509/140737488355328), (-8895800716793/2251799813685248)), (7846834422874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1055027439206107/1125899906842624), (-8611338235407/1125899906842624)), (3999/562949953421312), by norm_num⟩
  | 2 => ⟨((1977100691752993/2251799813685248), (-32277107659123/2251799813685248)), (1889/140737488355328), by norm_num⟩
  | 3 => ⟨((1735449710005865/2251799813685248), (-56679187459563/2251799813685248)), (53941/2251799813685248), by norm_num⟩
  | 4 => ⟨((668037439958883/1125899906842624), (-21841168749163/562949953421312)), (21465/562949953421312), by norm_num⟩
  | 5 => ⟨((789352360501817/2251799813685248), (-103673290090717/2251799813685248)), (217101/4503599627370496), by norm_num⟩
  | 6 => ⟨((1087714803474349/9007199254740992), (-72683864486309/2251799813685248)), (86099/2251799813685248), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/8589934592), (-110187858513/8589934592)), (1/4294967296), by norm_num⟩, -2, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-48674234621/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-18252837983/8589934592), (-112597194307/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-48674234621/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((921844852751991/9007199254740992), (-17333541823015/281474976710656)), (204363/4503599627370496), by norm_num⟩
  | 1 => ⟨((-39852647979/137438953472), (47958615227/274877906944)), (37/274877906944), by norm_num⟩
  | 2 => ⟨((56455527025/137438953472), (-8492311789/34359738368)), (7/34359738368), by norm_num⟩
  | 3 => ⟨((-53316850837/137438953472), (16040354055/68719476736)), (7/34359738368), by norm_num⟩
  | 4 => ⟨((75529006627/274877906944), (-88761221/536870912)), (21/137438953472), by norm_num⟩
  | 5 => ⟨((-85595915775/549755813888), (25751498319/274877906944)), (25/274877906944), by norm_num⟩
  | 6 => ⟨((40418581795/549755813888), (-48639659111/1099511627776)), (49/1099511627776), by norm_num⟩
  | 7 => ⟨((-16359209327/549755813888), (39373294641/2199023255552)), (41/2199023255552), by norm_num⟩
  | 8 => ⟨((46349130163/4398046511104), (-3486029493/549755813888)), (31/4398046511104), by norm_num⟩
  | 9 => ⟨((-58363099583/17592186044416), (35117032097/17592186044416)), (41/17592186044416), by norm_num⟩
  | 10 => ⟨((66142045015/70368744177664), (-4974702197/8796093022208)), (3/4398046511104), by norm_num⟩
  | 11 => ⟨((-68143463469/281474976710656), (41001869519/281474976710656)), (13/70368744177664), by norm_num⟩
  | 12 => ⟨((64354990003/1125899906842624), (-38722347951/1125899906842624)), (51/1125899906842624), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572467/10141204801825835211973625643008), (-705583044551/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778691188633947/633825300114114700748351602688), (-104368943021/79228162514264337593543950336)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472413654287721/9903520314283042199192993792), (-939146384553/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889424300999719/2475880078570760549798248448), (-997626788345/2475880078570760549798248448)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((442772655215889/38685626227668133590597632), (-997383604279/154742504910672534362390528)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1549459687717811/9671406556917033397649408), (-116848603509/1208925819614629174706176)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258706737834913/604462909807314587353088), (-408841008021/302231454903657293676544)), (177/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943829511482059/37778931862957161709568), (-1328249331397/75557863725914323419136)), (575/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297439808739975/4722366482869645213696), (-124470467897/590295810358705651712)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1621311300826555/590295810358705651712), (-342121931149/147573952589676412928)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823303896258907/73786976294838206464), (-6678043615/288230376151711744)), (371/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227808152841469/1152921504606846976), (-120116292579/576460752303423488)), (835/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593714212037781/1152921504606846976), (-60002887395/36028797018963968)), (835/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194343612874851/144115188075855872), (-1678093676935/144115188075855872)), (731/144115188075855872), by norm_num⟩
  | 4 => ⟨((745641379954291/18014398509481984), (-1256585772077/18014398509481984)), (137/4503599627370496), by norm_num⟩
  | 3 => ⟨((1488816270454407/9007199254740992), (-3134530793743/9007199254740992)), (1371/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113535459701027/2251799813685248), (-6248308846143/4503599627370496)), (2743/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107401040459003/1125899906842624), (-2330187405563/562949953421312)), (4121/2251799813685248), by norm_num⟩
  | 0 => ⟨((2178185690882617/2251799813685248), (-18435650848721/2251799813685248)), (1033/281474976710656), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2178185690882617/2251799813685248), (-18435650848721/2251799813685248)), (3940583349132449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2106827170830691/2251799813685248), (-2229120825747/140737488355328)), (4031/562949953421312), by norm_num⟩
  | 2 => ⟨((1970623073148025/2251799813685248), (-2085608273971/70368744177664)), (7671/562949953421312), by norm_num⟩
  | 3 => ⟨((861289071233611/1125899906842624), (-116811741754523/2251799813685248)), (55525/2251799813685248), by norm_num⟩
  | 4 => ⟨((1311675423340697/2251799813685248), (-178716910719127/2251799813685248)), (90713/2251799813685248), by norm_num⟩
  | 5 => ⟨((1499736052696051/4503599627370496), (-104102761755721/1125899906842624)), (240161/4503599627370496), by norm_num⟩
  | 6 => ⟨((921844852751991/9007199254740992), (-17333541823015/281474976710656)), (204363/4503599627370496), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-18252837983/8589934592), (-112597194307/8589934592)), (1/4294967296), by norm_num⟩, -2, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-24828104347/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-4655269565/2147483648), (-57434388259/4294967296)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-24828104347/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((713566045018879/9007199254740992), (-743761541433371/9007199254740992)), (14511/281474976710656), by norm_num⟩
  | 1 => ⟨((-62941624265/274877906944), (8200635353/34359738368)), (43/274877906944), by norm_num⟩
  | 2 => ⟨((45481173293/137438953472), (-23702884821/68719476736)), (33/137438953472), by norm_num⟩
  | 3 => ⟨((-10954791567/34359738368), (22836716289/68719476736)), (17/68719476736), by norm_num⟩
  | 4 => ⟨((31663420159/137438953472), (-66006599805/274877906944)), (51/274877906944), by norm_num⟩
  | 5 => ⟨((-36607622155/274877906944), (19078361191/137438953472)), (1/8589934592), by norm_num⟩
  | 6 => ⟨((35269879067/549755813888), (-9190592729/137438953472)), (1/17179869184), by norm_num⟩
  | 7 => ⟨((-58253178491/2199023255552), (15179559807/549755813888)), (55/2199023255552), by norm_num⟩
  | 8 => ⟨((5261666935/549755813888), (-10968642741/1099511627776)), (21/2199023255552), by norm_num⟩
  | 9 => ⟨((-3379594113/1099511627776), (56361698135/17592186044416)), (7/2199023255552), by norm_num⟩
  | 10 => ⟨((62517013615/70368744177664), (-65162504207/70368744177664)), (67/70368744177664), by norm_num⟩
  | 11 => ⟨((-8213518661/35184372088832), (68488677031/281474976710656)), (73/281474976710656), by norm_num⟩
  | 12 => ⟨((63306992989/1125899906842624), (-65985912609/1125899906842624)), (9/140737488355328), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790575996580325/5070602400912917605986812821504), (-1050054754039/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778624657657317/633825300114114700748351602688), (-1242494148441/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889579758286225/39614081257132168796771975168), (-174692689617/4951760157141521099596496896)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472336186860877/618970019642690137449562112), (-46392485741/77371252455336267181195264)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1771011049319905/154742504910672534362390528), (-1484190323405/154742504910672534362390528)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1549385070304037/9671406556917033397649408), (-1391036255687/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157330178566105/75557863725914323419136), (-1216764690823/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887552859635285/75557863725914323419136), (-988253928715/37778931862957161709568)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((648680077524051/2361183241434822606848), (-370434567491/1180591620717411303424)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((810600863198849/295147905179352825856), (-2036346414121/590295810358705651712)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823166852475929/73786976294838206464), (-2543868428545/73786976294838206464)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822310944578541/9223372036854775808), (-2859702249737/9223372036854775808)), (835/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796779902197139/576460752303423488), (-2857017448881/1152921504606846976)), (209/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194208361033765/144115188075855872), (-2496873115139/144115188075855872)), (183/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491079593147161/36028797018963968), (-934820869811/9007199254740992)), (549/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488561809184801/9007199254740992), (-4663576737241/9007199254740992)), (1373/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113280250050187/2251799813685248), (-2323910855545/1125899906842624)), (2749/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214032750815367/2251799813685248), (-13864944187085/2251799813685248)), (1033/562949953421312), by norm_num⟩
  | 0 => ⟨((544158117329281/562949953421312), (-27417325254243/2251799813685248)), (4149/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((544158117329281/562949953421312), (-27417325254243/2251799813685248)), (15827183250045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2103640460387563/2251799813685248), (-53004214679765/2251799813685248)), (16245/2251799813685248), by norm_num⟩
  | 2 => ⟨((1963981750477197/2251799813685248), (-24758375476757/562949953421312)), (15559/1125899906842624), by norm_num⟩
  | 3 => ⟨((427149058535859/562949953421312), (-172750694132919/2251799813685248)), (57019/2251799813685248), by norm_num⟩
  | 4 => ⟨((1283177248459267/2251799813685248), (-131077897620977/1125899906842624)), (47639/1125899906842624), by norm_num⟩
  | 5 => ⟨((1401384066554593/4503599627370496), (-149388213802047/1125899906842624)), (261545/4503599627370496), by norm_num⟩
  | 6 => ⟨((713566045018879/9007199254740992), (-743761541433371/9007199254740992)), (14511/281474976710656), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4655269565/2147483648), (-57434388259/4294967296)), (1/4294967296), by norm_num⟩, -2, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-101170152965/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-18969403681/8589934592), (-117017508957/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-101170152965/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((487085562112165/9007199254740992), (-215399116875921/2251799813685248)), (510007/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1367753711/8589934592), (38710300037/137438953472)), (3/17179869184), by norm_num⟩
  | 2 => ⟨((32218138725/137438953472), (-28495029081/68719476736)), (37/137438953472), by norm_num⟩
  | 3 => ⟨((-31621447833/137438953472), (55934582893/137438953472)), (19/68719476736), by norm_num⟩
  | 4 => ⟨((46553711789/274877906944), (-82347983077/274877906944)), (29/137438953472), by norm_num⟩
  | 5 => ⟨((-27414912723/274877906944), (24246861123/137438953472)), (9/68719476736), by norm_num⟩
  | 6 => ⟨((26907179211/549755813888), (-47595602009/549755813888)), (37/549755813888), by norm_num⟩
  | 7 => ⟨((-1414759773/68719476736), (80081340453/2199023255552)), (1/34359738368), by norm_num⟩
  | 8 => ⟨((16662695287/2199023255552), (-14737163771/1099511627776)), (49/4398046511104), by norm_num⟩
  | 9 => ⟨((-43610924001/17592186044416), (19285635311/4398046511104)), (33/8796093022208), by norm_num⟩
  | 10 => ⟨((25681940909/35184372088832), (-22714150539/17592186044416)), (41/35184372088832), by norm_num⟩
  | 11 => ⟨((-27497784681/140737488355328), (12160078223/35184372088832)), (23/70368744177664), by norm_num⟩
  | 12 => ⟨((26355973/549755813888), (-23869738873/281474976710656)), (47/562949953421312), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581099171716351/10141204801825835211973625643008), (-687948519145/5070602400912917605986812821504)), (305/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444640391327281/158456325028528675187087900672), (-101746455765/39614081257132168796771975168)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944754379836525/19807040628566084398385987584), (-1831083034337/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472317321143545/618970019642690137449562112), (-972543725639/1237940039285380274899124224)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770935556290933/154742504910672534362390528), (-972297286509/77371252455336267181195264)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((387328565893537/2417851639229258349412352), (-227816736563/1208925819614629174706176)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314644860164513/151115727451828646838272), (-1594193820141/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((29491438585141/1180591620717411303424), (-2589584093743/75557863725914323419136)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1297284510069425/4722366482869645213696), (-970665102397/2361183241434822606848)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1621097629632715/590295810358705651712), (-166745983245/36893488147419103232)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911518302185355/36893488147419103232), (-3332830995319/73786976294838206464)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822164241003561/9223372036854775808), (-1873282513811/4611686018427387904)), (209/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796706441653823/576460752303423488), (-3742980840523/1152921504606846976)), (209/288230376151711744), by norm_num⟩
  | 5 => ⟨((149259945143735/18014398509481984), (-817770076275/36028797018963968)), (733/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490885907370235/36028797018963968), (-153080477689/1125899906842624)), (275/9007199254740992), by norm_num⟩
  | 3 => ⟨((93019928490491/562949953421312), (-6109164076953/9007199254740992)), (1375/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113036036111185/2251799813685248), (-12176258987047/4503599627370496)), (1377/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106646932879627/1125899906842624), (-18159550609489/2251799813685248)), (2071/1125899906842624), by norm_num⟩
  | 0 => ⟨((2175130083039365/2251799813685248), (-35901754490195/2251799813685248)), (4165/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2175130083039365/2251799813685248), (-35901754490195/2251799813685248)), (15888218406295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((525124604041345/562949953421312), (-17339682184651/562949953421312)), (16359/2251799813685248), by norm_num⟩
  | 2 => ⟨((978613404325709/1125899906842624), (-129396848669467/2251799813685248)), (3941/281474976710656), by norm_num⟩
  | 3 => ⟨((1693753242574581/2251799813685248), (-112469580835613/1125899906842624)), (913/35184372088832), by norm_num⟩
  | 4 => ⟨((1251533286019037/2251799813685248), (-169194185090159/1125899906842624)), (99577/2251799813685248), by norm_num⟩
  | 5 => ⟨((644741538797929/2251799813685248), (-752294775598727/4503599627370496)), (281233/4503599627370496), by norm_num⟩
  | 6 => ⟨((487085562112165/9007199254740992), (-215399116875921/2251799813685248)), (510007/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-18969403681/8589934592), (-117017508957/8589934592)), (1/4294967296), by norm_num⟩, -2, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-25733144285/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-9649929107/4294967296), (-29764000089/2147483648)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((260658257475089/9007199254740992), (-916031770834435/9007199254740992)), (545227/9007199254740992), by norm_num⟩
  | 1 => ⟨((-11915013951/137438953472), (41872954399/137438953472)), (13/68719476736), by norm_num⟩
  | 2 => ⟨((4461773979/34359738368), (-62720080441/137438953472)), (41/137438953472), by norm_num⟩
  | 3 => ⟨((-17821707075/137438953472), (7828857049/17179869184)), (43/137438953472), by norm_num⟩
  | 4 => ⟨((26694531527/274877906944), (-93812638907/274877906944)), (33/137438953472), by norm_num⟩
  | 5 => ⟨((-15993933925/274877906944), (7025938751/34359738368)), (41/274877906944), by norm_num⟩
  | 6 => ⟨((15971181347/549755813888), (-28063775291/274877906944)), (43/549755813888), by norm_num⟩
  | 7 => ⟨((-13670109545/1099511627776), (96081779837/2199023255552)), (19/549755813888), by norm_num⟩
  | 8 => ⟨((10237997087/2199023255552), (-35979411095/2199023255552)), (59/4398046511104), by norm_num⟩
  | 9 => ⟨((-27262487369/17592186044416), (11976075889/2199023255552)), (5/1099511627776), by norm_num⟩
  | 10 => ⟨((8167111327/17592186044416), (-28701693641/17592186044416)), (49/35184372088832), by norm_num⟩
  | 11 => ⟨((-17793802897/140737488355328), (3908299543/8796093022208)), (55/140737488355328), by norm_num⟩
  | 12 => ⟨((17768489869/562949953421312), (-31221917535/281474976710656)), (57/562949953421312), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790524530142089/5070602400912917605986812821504), (-421255483821/2535301200456458802993406410752)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444625391659231/158456325028528675187087900672), (-996784600301/316912650057057350374175801344)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944720617287775/19807040628566084398385987584), (-17518162901/309485009821345068724781056)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889197503187767/2475880078570760549798248448), (-2381924013629/2475880078570760549798248448)), (433/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442715933621737/38685626227668133590597632), (-2381309818921/154742504910672534362390528)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1549246887726979/9671406556917033397649408), (-1115912786509/4835703278458516698824704)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258520443928329/604462909807314587353088), (-1952195218783/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887356119484467/75557863725914323419136), (-1585547456073/37778931862957161709568)), (577/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297212477442237/4722366482869645213696), (-18572282285/36893488147419103232)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620998470939327/590295810358705651712), (-1633492683577/295147905179352825856)), (595/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822912485552695/73786976294838206464), (-4081128799953/73786976294838206464)), (93/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1822024373441981/9223372036854775808), (-4587693439333/9223372036854775808)), (837/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593272724099751/1152921504606846976), (-4583226669855/1152921504606846976)), (837/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596978297363157/72057594037927936), (-4005303449917/144115188075855872)), (733/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490700805960497/36028797018963968), (-2998964231769/18014398509481984)), (1101/36028797018963968), by norm_num⟩
  | 3 => ⟨((372021586000049/2251799813685248), (-7479893187477/9007199254740992)), (1377/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225603665285063/4503599627370496), (-3726837859549/1125899906842624)), (2759/4503599627370496), by norm_num⟩
  | 1 => ⟨((276572859251281/281474976710656), (-86837302253/8796093022208)), (4153/2251799813685248), by norm_num⟩
  | 0 => ⟨((2173675032437217/2251799813685248), (-43940438804611/2251799813685248)), (8361/2251799813685248), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2173675032437217/2251799813685248), (-43940438804611/2251799813685248)), (31894692427825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2097403310798371/2251799813685248), (-84831905716881/2251799813685248)), (16469/2251799813685248), by norm_num⟩
  | 2 => ⟨((975198632051735/1125899906842624), (-158030672913797/2251799813685248)), (15961/1125899906842624), by norm_num⟩
  | 3 => ⟨((104890423964241/140737488355328), (-136878327381629/1125899906842624)), (14945/562949953421312), by norm_num⟩
  | 4 => ⟨((1217501459675485/2251799813685248), (-12751778113951/70368744177664)), (103643/2251799813685248), by norm_num⟩
  | 5 => ⟨((292166151486057/1125899906842624), (-882511612143915/4503599627370496)), (299277/4503599627370496), by norm_num⟩
  | 6 => ⟨((260658257475089/9007199254740992), (-916031770834435/9007199254740992)), (545227/9007199254740992), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9649929107/4294967296), (-29764000089/2147483648)), (1/4294967296), by norm_num⟩, -2, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-4903546613/2147483648), (-60497506341/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((5907403344393/1125899906842624), (-458478804743743/4503599627370496)), (2279303/18014398509481984), by norm_num⟩
  | 1 => ⟨((-4390923347/274877906944), (85195862321/274877906944)), (27/68719476736), by norm_num⟩
  | 2 => ⟨((3342066163/137438953472), (-129690357219/274877906944)), (83/137438953472), by norm_num⟩
  | 3 => ⟨((-3391665141/137438953472), (8225941719/17179869184)), (43/68719476736), by norm_num⟩
  | 4 => ⟨((645375039/34359738368), (-25044064135/68719476736)), (133/274877906944), by norm_num⟩
  | 5 => ⟨((-3143774059/274877906944), (60997772153/274877906944)), (41/137438953472), by norm_num⟩
  | 6 => ⟨((6380860441/1099511627776), (-61903028657/549755813888)), (169/1099511627776), by norm_num⟩
  | 7 => ⟨((-2775238969/1099511627776), (107694376977/2199023255552)), (149/2199023255552), by norm_num⟩
  | 8 => ⟨((66009979/68719476736), (-81969486781/4398046511104)), (115/4398046511104), by norm_num⟩
  | 9 => ⟨((-5716447635/17592186044416), (55457320381/8796093022208)), (79/8796093022208), by norm_num⟩
  | 10 => ⟨((1740385309/17592186044416), (-67536422495/35184372088832)), (49/17592186044416), by norm_num⟩
  | 11 => ⟨((-963389477/35184372088832), (37384755209/70368744177664)), (55/70368744177664), by norm_num⟩
  | 12 => ⟨((3910747839/562949953421312), (-75879150709/562949953421312)), (57/281474976710656), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581001394307151/10141204801825835211973625643008), (-989530716129/5070602400912917605986812821504)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778444366452991/633825300114114700748351602688), (-292663666531/79228162514264337593543950336)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889376851998143/39614081257132168796771975168), (-2633446531475/39614081257132168796771975168)), (813/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944564526499161/1237940039285380274899124224), (-1398692486465/1237940039285380274899124224)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770795235192197/154742504910672534362390528), (-2796651752819/154742504910672534362390528)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((96823913594311/604462909807314587353088), (-655270551047/2417851639229258349412352)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258464155409293/604462909807314587353088), (-1146334187937/302231454903657293676544)), (355/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887264553102327/75557863725914323419136), (-1862063439691/37778931862957161709568)), (1153/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162142964677157/590295810358705651712), (-2791818886929/4722366482869645213696)), (865/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620903787594925/590295810358705651712), (-1918339033265/295147905179352825856)), (595/295147905179352825856), by norm_num⟩
  | 8 => ⟨((113924620266301/4611686018427387904), (-149773126495/2305843009213693952)), (93/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1821890707784589/9223372036854775808), (-1346890661847/2305843009213693952)), (1675/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593138704047367/1152921504606846976), (-2691114846821/576460752303423488)), (419/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193838929666835/144115188075855872), (-2351728747465/72057594037927936)), (1467/144115188075855872), by norm_num⟩
  | 4 => ⟨((745261758145153/18014398509481984), (-7043214470315/36028797018963968)), (2203/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487863352384853/9007199254740992), (-2195775413869/2251799813685248)), (1379/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112576784926293/2251799813685248), (-8751795255261/2251799813685248)), (691/562949953421312), by norm_num⟩
  | 1 => ⟨((2211897542352127/2251799813685248), (-26099330702779/2251799813685248)), (2081/562949953421312), by norm_num⟩
  | 0 => ⟨((1086132082176367/1125899906842624), (-51577296379999/2251799813685248)), (16779/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1086132082176367/1125899906842624), (-51577296379999/2251799813685248)), (64006814009856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2094356413730663/2251799813685248), (-99511077263223/2251799813685248)), (16571/1125899906842624), by norm_num⟩
  | 2 => ⟨((1943523712294083/2251799813685248), (-185106741404687/2251799813685248)), (16145/562949953421312), by norm_num⟩
  | 3 => ⟨((831117378149651/1125899906842624), (-319530483162021/2251799813685248)), (7631/140737488355328), by norm_num⟩
  | 4 => ⟨((1181687927678097/2251799813685248), (-471742356119815/2251799813685248)), (107455/1125899906842624), by norm_num⟩
  | 5 => ⟨((1042584248145567/4503599627370496), (-990234111954903/4503599627370496)), (631209/4503599627370496), by norm_num⟩
  | 6 => ⟨((5907403344393/1125899906842624), (-458478804743743/4503599627370496)), (2279303/18014398509481984), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4903546613/2147483648), (-60497506341/4294967296)), (1/2147483648), by norm_num⟩, -2, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨10,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile010Terms2

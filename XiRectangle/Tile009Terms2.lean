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
namespace Reinmann.XiRectangle.Tile009Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨9,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (2679/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (2679/640))
  have he : value ((3/4), (2679/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-17862266831/8589934592), (-49846888375/4294967296)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((322638189155769/4503599627370496), (461321199327819/4503599627370496)), (34485/562949953421312), by norm_num⟩
  | 1 => ⟨((-54598572059/274877906944), (-39033628985/137438953472)), (49/274877906944), by norm_num⟩
  | 2 => ⟨((37844846285/137438953472), (13528024939/34359738368)), (9/34359738368), by norm_num⟩
  | 3 => ⟨((-8744016167/34359738368), (-50010199173/137438953472)), (35/137438953472), by norm_num⟩
  | 4 => ⟨((48487121223/274877906944), (8666107139/34359738368)), (51/274877906944), by norm_num⟩
  | 5 => ⟨((-53773938191/549755813888), (-38444081471/274877906944)), (59/549755813888), by norm_num⟩
  | 6 => ⟨((24848835763/549755813888), (71059751149/1099511627776)), (57/1099511627776), by norm_num⟩
  | 7 => ⟨((-39368915313/2199023255552), (-14072818903/549755813888)), (47/2199023255552), by norm_num⟩
  | 8 => ⟨((27288452651/4398046511104), (78036277961/8796093022208)), (67/8796093022208), by norm_num⟩
  | 9 => ⟨((-2101657113/1099511627776), (-48080556489/17592186044416)), (43/17592186044416), by norm_num⟩
  | 10 => ⟨((37292997181/70368744177664), (3332690217/4398046511104)), (49/70368744177664), by norm_num⟩
  | 11 => ⟨((-18799662437/140737488355328), (-13440260815/70368744177664)), (13/70368744177664), by norm_num⟩
  | 12 => ⟨((34749154703/1125899906842624), (49685754079/1125899906842624)), (25/562949953421312), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581267062326477/10141204801825835211973625643008), (1251142220587/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889380239053231/316912650057057350374175801344), (740324993173/316912650057057350374175801344)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889732508164335/39614081257132168796771975168), (1665428024583/39614081257132168796771975168)), (203/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944753491715827/1237940039285380274899124224), (110571369071/154742504910672534362390528)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1771173216992249/154742504910672534362390528), (1768719756073/154742504910672534362390528)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1549537029942453/9671406556917033397649408), (1657726370501/9671406556917033397649408)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258774320693083/604462909807314587353088), (725031161257/302231454903657293676544)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887768673502771/75557863725914323419136), (2355511119011/75557863725914323419136)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1297521896611107/4722366482869645213696), (27592164379/73786976294838206464)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202677991009385/73786976294838206464), (2426916977989/590295810358705651712)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227930539419843/9223372036854775808), (189491064347/4611686018427387904)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822622693048295/9223372036854775808), (1704190351935/4611686018427387904)), (209/2305843009213693952), by norm_num⟩
  | 6 => ⟨((778257351985/562949953421312), (1702655081489/576460752303423488)), (837/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194480149761779/144115188075855872), (2976195505937/144115188075855872)), (183/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491486163904429/36028797018963968), (4457400156473/36028797018963968)), (1099/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489068080613389/9007199254740992), (5559706752007/9007199254740992)), (1375/9007199254740992), by norm_num⟩
  | 2 => ⟨((556891808784349/1125899906842624), (5541680498393/2251799813685248)), (43/70368744177664), by norm_num⟩
  | 1 => ⟨((1107764198735375/1125899906842624), (16535182073879/2251799813685248)), (2069/1125899906842624), by norm_num⟩
  | 0 => ⟨((2179566319586051/2251799813685248), (32712553265919/2251799813685248)), (4159/1125899906842624), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2179566319586051/2251799813685248), (32712553265919/2251799813685248)), (15865330222701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1054587357514671/1125899906842624), (63326392419737/2251799813685248)), (16345/2251799813685248), by norm_num⟩
  | 2 => ⟨((493450585563849/562949953421312), (59315408445275/1125899906842624)), (7885/562949953421312), by norm_num⟩
  | 3 => ⟨((430968862327937/562949953421312), (51992584513769/562949953421312)), (58617/2251799813685248), by norm_num⟩
  | 4 => ⟨((1300512987624919/2251799813685248), (318425250574537/2251799813685248)), (100577/2251799813685248), by norm_num⟩
  | 5 => ⟨((1412149855519861/4503599627370496), (183904524479985/1125899906842624)), (144621/2251799813685248), by norm_num⟩
  | 6 => ⟨((322638189155769/4503599627370496), (461321199327819/4503599627370496)), (34485/562949953421312), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/8589934592), (-49846888375/4294967296)), (1/4294967296), by norm_num⟩, -2, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-18252837983/8589934592), (-12734206499/1073741824)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((818184320051161/9007199254740992), (349297460350455/4503599627370496)), (114011/2251799813685248), by norm_num⟩
  | 1 => ⟨((-70742515059/274877906944), (-15100619899/68719476736)), (21/137438953472), by norm_num⟩
  | 2 => ⟨((25053579707/68719476736), (42783277801/137438953472)), (31/137438953472), by norm_num⟩
  | 3 => ⟨((-11830356057/34359738368), (-1262647433/4294967296)), (31/137438953472), by norm_num⟩
  | 4 => ⟨((67035845291/274877906944), (894337389/4294967296)), (23/137438953472), by norm_num⟩
  | 5 => ⟨((-18992685141/137438953472), (-32433262395/274877906944)), (7/68719476736), by norm_num⟩
  | 6 => ⟨((17936776327/274877906944), (61260234539/1099511627776)), (55/1099511627776), by norm_num⟩
  | 7 => ⟨((-29039265165/1099511627776), (-49589518273/2199023255552)), (23/1099511627776), by norm_num⟩
  | 8 => ⟨((41137216783/4398046511104), (4390552653/549755813888)), (17/2199023255552), by norm_num⟩
  | 9 => ⟨((-51800227345/17592186044416), (-44228879517/17592186044416)), (11/4398046511104), by norm_num⟩
  | 10 => ⟨((58704438135/70368744177664), (3132746291/4398046511104)), (13/17592186044416), by norm_num⟩
  | 11 => ⟨((-60480799083/281474976710656), (-51640660917/281474976710656)), (7/35184372088832), by norm_num⟩
  | 12 => ⟨((57118335673/1125899906842624), (12192417467/281474976710656)), (55/1125899906842624), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572467/10141204801825835211973625643008), (920577318535/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((222336365816115/79228162514264337593543950336), (544682486047/316912650057057350374175801344)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889654307532853/39614081257132168796771975168), (1225308260233/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889423952774841/2475880078570760549798248448), (81350491829/154742504910672534362390528)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1771090250994925/154742504910672534362390528), (10166332495/1208925819614629174706176)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((24210301843507/151115727451828646838272), (304905715787/2417851639229258349412352)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629353195676773/302231454903657293676544), (1066833087733/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943829208454457/37778931862957161709568), (216621537427/9444732965739290427392)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1297439316589215/4722366482869645213696), (1299176942021/4722366482869645213696)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((25332977547985/9223372036854775808), (55795978393/18446744073709551616)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911651441304649/36893488147419103232), (1115247240965/36893488147419103232)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822463956815131/9223372036854775808), (2507458734985/9223372036854775808)), (835/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398428197363739/288230376151711744), (152902301/70368744177664)), (209/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194342192256443/144115188075855872), (2189414284983/144115188075855872)), (183/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491280278239983/36028797018963968), (1639471061077/18014398509481984)), (1097/36028797018963968), by norm_num⟩
  | 3 => ⟨((186101569595369/1125899906842624), (2044814684985/4503599627370496)), (1373/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227061665942557/4503599627370496), (4076087896309/2251799813685248)), (2747/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214783666023401/2251799813685248), (190012070305/35184372088832)), (4127/2251799813685248), by norm_num⟩
  | 0 => ⟨((2178130904345041/2251799813685248), (24052873530109/2251799813685248)), (8285/2251799813685248), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2178130904345041/2251799813685248), (24052873530109/2251799813685248)), (31604775435637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1053307595752593/1125899906842624), (46531940233615/2251799813685248)), (8103/1125899906842624), by norm_num⟩
  | 2 => ⟨((492457446334807/562949953421312), (87063593833343/2251799813685248)), (30993/2251799813685248), by norm_num⟩
  | 3 => ⟨((1719801773808887/2251799813685248), (38080751963231/562949953421312)), (28311/1125899906842624), by norm_num⟩
  | 4 => ⟨((1303186821777139/2251799813685248), (232671996422841/2251799813685248)), (94151/2251799813685248), by norm_num⟩
  | 5 => ⟨((730153552967665/2251799813685248), (33663636271311/281474976710656)), (256867/4503599627370496), by norm_num⟩
  | 6 => ⟨((818184320051161/9007199254740992), (349297460350455/4503599627370496)), (114011/2251799813685248), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-18252837983/8589934592), (-12734206499/1073741824)), (1/4294967296), by norm_num⟩, -2, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-4655269565/2147483648), (-6495555815/536870912)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((460065499496057/4503599627370496), (464453093232257/9007199254740992)), (185747/4503599627370496), by norm_num⟩
  | 1 => ⟨((-81162129305/274877906944), (-40968081773/274877906944)), (35/274877906944), by norm_num⟩
  | 2 => ⟨((58647181589/137438953472), (29603246633/137438953472)), (27/137438953472), by norm_num⟩
  | 3 => ⟨((-56504052449/137438953472), (-14260731335/68719476736)), (7/34359738368), by norm_num⟩
  | 4 => ⟨((81658858703/274877906944), (20609407549/137438953472)), (21/137438953472), by norm_num⟩
  | 5 => ⟨((-11801222949/68719476736), (-23827539811/274877906944)), (13/137438953472), by norm_num⟩
  | 6 => ⟨((45479895361/549755813888), (45913632087/1099511627776)), (53/1099511627776), by norm_num⟩
  | 7 => ⟨((-75116460059/2199023255552), (-37916418711/2199023255552)), (23/1099511627776), by norm_num⟩
  | 8 => ⟨((54278623677/4398046511104), (27398136451/4398046511104)), (35/4398046511104), by norm_num⟩
  | 9 => ⟨((-17431711215/4398046511104), (-17597955515/8796093022208)), (47/17592186044416), by norm_num⟩
  | 10 => ⟨((80614601261/70368744177664), (20345853447/35184372088832)), (7/8796093022208), by norm_num⟩
  | 11 => ⟨((-84729515185/281474976710656), (-42768785595/281474976710656)), (31/140737488355328), by norm_num⟩
  | 12 => ⟨((81633265917/1125899906842624), (10301474167/281474976710656)), (31/562949953421312), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790575996580325/5070602400912917605986812821504), (608912438529/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444656301578793/158456325028528675187087900672), (720505420193/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472395101583237/9903520314283042199192993792), (810415526189/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889345476292591/2475880078570760549798248448), (860876138611/2475880078570760549798248448)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((885505911732591/77371252455336267181195264), (860662069579/154742504910672534362390528)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((193673230520061/1208925819614629174706176), (6301900907/75557863725914323419136)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258642153712515/604462909807314587353088), (352792805479/302231454903657293676544)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887554128093519/75557863725914323419136), (1146150625265/75557863725914323419136)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((648680592547929/2361183241434822606848), (429620201385/2361183241434822606848)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1621203270464483/590295810358705651712), (36901577063/18446744073709551616)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455792243484013/18446744073709551616), (368789007975/18446744073709551616)), (371/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455578398489549/2305843009213693952), (414576071211/2305843009213693952)), (835/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796781390793585/576460752303423488), (1656747885191/1152921504606846976)), (835/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597105667016319/72057594037927936), (1447905392457/144115188075855872)), (365/72057594037927936), by norm_num⟩
  | 4 => ⟨((372771196618099/9007199254740992), (1084182462523/18014398509481984)), (137/4503599627370496), by norm_num⟩
  | 3 => ⟨((1488569580361395/9007199254740992), (2704354017743/9007199254740992)), (1371/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226579862356653/4503599627370496), (5390445131691/4503599627370496)), (1371/2251799813685248), by norm_num⟩
  | 1 => ⟨((553517819721937/562949953421312), (8040162373369/2251799813685248)), (4117/2251799813685248), by norm_num⟩
  | 0 => ⟨((1088373537814627/1125899906842624), (15899212217873/2251799813685248)), (8255/2251799813685248), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1088373537814627/1125899906842624), (15899212217873/2251799813685248)), (31490334517668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1052041797302863/1125899906842624), (15369289707607/1125899906842624)), (16077/2251799813685248), by norm_num⟩
  | 2 => ⟨((1965637835976469/2251799813685248), (7180538460387/281474976710656)), (30485/2251799813685248), by norm_num⟩
  | 3 => ⟨((857188154620895/1125899906842624), (25072100982763/562949953421312)), (27389/1125899906842624), by norm_num⟩
  | 4 => ⟨((650374946281943/1125899906842624), (152706348713731/2251799813685248)), (88289/2251799813685248), by norm_num⟩
  | 5 => ⟨((741021046332105/2251799813685248), (44105334203339/562949953421312)), (227951/4503599627370496), by norm_num⟩
  | 6 => ⟨((460065499496057/4503599627370496), (464453093232257/9007199254740992)), (185747/4503599627370496), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4655269565/2147483648), (-6495555815/536870912)), (1/4294967296), by norm_num⟩, -2, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-18969403681/8589934592), (-52936492147/4294967296)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((961112486934173/9007199254740992), (118177414394741/4503599627370496)), (149135/4503599627370496), by norm_num⟩
  | 1 => ⟨((-21590706405/68719476736), (-165923207/2147483648)), (29/274877906944), by norm_num⟩
  | 2 => ⟨((63572517527/137438953472), (1954203033/17179869184)), (23/137438953472), by norm_num⟩
  | 3 => ⟨((-31197566435/68719476736), (-15344084223/137438953472)), (3/17179869184), by norm_num⟩
  | 4 => ⟨((91859330667/274877906944), (22589859843/274877906944)), (37/274877906944), by norm_num⟩
  | 5 => ⟨((-108189677527/549755813888), (-13302892771/274877906944)), (23/274877906944), by norm_num⟩
  | 6 => ⟨((106185967885/1099511627776), (6528259335/274877906944)), (47/1099511627776), by norm_num⟩
  | 7 => ⟨((-44665443269/1099511627776), (-10984035001/1099511627776)), (21/1099511627776), by norm_num⟩
  | 8 => ⟨((16439334023/1099511627776), (16170910403/4398046511104)), (33/4398046511104), by norm_num⟩
  | 9 => ⟨((-86052650469/17592186044416), (-21161892853/17592186044416)), (45/17592186044416), by norm_num⟩
  | 10 => ⟨((101350711321/70368744177664), (6230990219/17592186044416)), (55/70368744177664), by norm_num⟩
  | 11 => ⟨((-108516721811/281474976710656), (-26686211607/281474976710656)), (61/281474976710656), by norm_num⟩
  | 12 => ⟨((53253477599/562949953421312), (26191973887/1125899906842624)), (63/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581099171716351/10141204801825835211973625643008), (314102752829/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778562910587371/633825300114114700748351602688), (371642248883/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944755174243701/19807040628566084398385987584), (418017221933/39614081257132168796771975168)), (203/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889271071482387/2475880078570760549798248448), (444043282143/2475880078570760549798248448)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1770937454239321/154742504910672534362390528), (221965404885/77371252455336267181195264)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((387329040200287/2417851639229258349412352), (416065672441/9671406556917033397649408)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629290609271111/302231454903657293676544), (363938046881/604462909807314587353088)), (177/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((29491487175231/1180591620717411303424), (591175516269/75557863725914323419136)), (575/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297287035319079/4722366482869645213696), (110796474879/1180591620717411303424)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((810550707498741/295147905179352825856), (38066419873/36893488147419103232)), (593/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911520902585973/36893488147419103232), (380425935617/36893488147419103232)), (741/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822170735897315/9223372036854775808), (427651821187/4611686018427387904)), (417/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398355045418331/288230376151711744), (53405376059/72057594037927936)), (417/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194086849040931/144115188075855872), (186689121931/36028797018963968)), (365/72057594037927936), by norm_num⟩
  | 4 => ⟨((93181164852895/2251799813685248), (559149901441/18014398509481984)), (1095/36028797018963968), by norm_num⟩
  | 3 => ⟨((744168952140991/4503599627370496), (697334763387/4503599627370496)), (1369/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226119529266293/4503599627370496), (2779746921899/4503599627370496)), (2737/4503599627370496), by norm_num⟩
  | 1 => ⟨((2213388289273957/2251799813685248), (4145722273491/2251799813685248)), (1027/562949953421312), by norm_num⟩
  | 0 => ⟨((543852727886089/562949953421312), (8196343822761/2251799813685248)), (4113/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((543852727886089/562949953421312), (8196343822761/2251799813685248)), (15689854148482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2101583553410695/2251799813685248), (15836590516119/2251799813685248)), (15955/2251799813685248), by norm_num⟩
  | 2 => ⟨((980638378137921/1125899906842624), (7390070371377/562949953421312)), (30007/2251799813685248), by norm_num⟩
  | 3 => ⟨((853924199010511/1125899906842624), (51492937013451/2251799813685248)), (13265/562949953421312), by norm_num⟩
  | 4 => ⟨((323529495200947/562949953421312), (78108302037645/2251799813685248)), (82913/2251799813685248), by norm_num⟩
  | 5 => ⟨((1482050430283683/4503599627370496), (179556561826945/4503599627370496)), (101053/2251799813685248), by norm_num⟩
  | 6 => ⟨((961112486934173/9007199254740992), (118177414394741/4503599627370496)), (149135/4503599627370496), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-18969403681/8589934592), (-52936492147/4294967296)), (1/4294967296), by norm_num⟩, -2, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-9649929107/4294967296), (-107717333655/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((59503932933923/562949953421312), (50323573370805/18014398509481984)), (235877/9007199254740992), by norm_num⟩
  | 1 => ⟨((-21759991735/68719476736), (-2300353285/274877906944)), (3/34359738368), by norm_num⟩
  | 2 => ⟨((65187109513/137438953472), (430702661/34359738368)), (19/137438953472), by norm_num⟩
  | 3 => ⟨((-130188751859/274877906944), (-215044977/17179869184)), (5/34359738368), by norm_num⟩
  | 4 => ⟨((12187832675/34359738368), (2576868711/274877906944)), (1/8589934592), by norm_num⟩
  | 5 => ⟨((-116836747805/549755813888), (-3087843505/549755813888)), (41/549755813888), by norm_num⟩
  | 6 => ⟨((14583817339/137438953472), (3083450815/1099511627776)), (43/1099511627776), by norm_num⟩
  | 7 => ⟨((-99861056627/2199023255552), (-1319599017/1099511627776)), (39/2199023255552), by norm_num⟩
  | 8 => ⟨((1168581993/68719476736), (988291341/2199023255552)), (31/4398046511104), by norm_num⟩
  | 9 => ⟨((-12447142367/2199023255552), (-2631694459/17592186044416)), (43/17592186044416), by norm_num⟩
  | 10 => ⟨((14915322441/8796093022208), (1576770405/35184372088832)), (27/35184372088832), by norm_num⟩
  | 11 => ⟨((-4062028437/8796093022208), (-3435332357/281474976710656)), (61/281474976710656), by norm_num⟩
  | 12 => ⟨((64899998319/562949953421312), (3430445337/1125899906842624)), (63/1125899906842624), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790524530142089/5070602400912917605986812821504), (17209161107/5070602400912917605986812821504)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444625923589833/158456325028528675187087900672), (40720720405/633825300114114700748351602688)), (361/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889443747240347/39614081257132168796771975168), (45801867701/39614081257132168796771975168)), (203/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472300082279595/618970019642690137449562112), (48653335319/2475880078570760549798248448)), (431/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442716684001455/38685626227668133590597632), (6080099727/19342813113834066795298816)), (431/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549249888085025/9671406556917033397649408), (22793715715/4835703278458516698824704)), (101/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629261627765577/302231454903657293676544), (19937845563/302231454903657293676544)), (177/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943680518662463/37778931862957161709568), (32386525093/37778931862957161709568)), (575/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40538014714951/147573952589676412928), (48557969161/4722366482869645213696)), (431/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810502228527553/295147905179352825856), (33365886523/295147905179352825856)), (593/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822920709904091/73786976294838206464), (83361600295/73786976294838206464)), (741/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113877165253305/576460752303423488), (46854411983/4611686018427387904)), (833/9223372036854775808), by norm_num⟩
  | 6 => ⟨((24895066641197/18014398509481984), (46808845329/576460752303423488)), (833/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193968118808001/144115188075855872), (81813074057/144115188075855872)), (729/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490720935235171/36028797018963968), (61257549711/18014398509481984)), (1093/36028797018963968), by norm_num⟩
  | 3 => ⟨((744058231157547/4503599627370496), (152786650287/9007199254740992)), (1367/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225678697108817/4503599627370496), (76126077265/1125899906842624)), (683/1125899906842624), by norm_num⟩
  | 1 => ⟨((2212732148267525/2251799813685248), (454093342923/2251799813685248)), (2049/1125899906842624), by norm_num⟩
  | 0 => ⟨((2174118925711097/2251799813685248), (448795082267/1125899906842624)), (4099/1125899906842624), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2174118925711097/2251799813685248), (448795082267/1125899906842624)), (15636448386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1049558728253757/1125899906842624), (1733251554943/2251799813685248)), (7919/1125899906842624), by norm_num⟩
  | 2 => ⟨((1956786329439463/2251799813685248), (807864574237/562949953421312)), (14777/1125899906842624), by norm_num⟩
  | 3 => ⟨((1700418604481531/2251799813685248), (5616194993171/2251799813685248)), (25725/1125899906842624), by norm_num⟩
  | 4 => ⟨((160504492409159/281474976710656), (2120499876309/562949953421312)), (77961/2251799813685248), by norm_num⟩
  | 5 => ⟨((183039844284781/562949953421312), (4836660939143/1125899906842624)), (89499/2251799813685248), by norm_num⟩
  | 6 => ⟨((59503932933923/562949953421312), (50323573370805/18014398509481984)), (235877/9007199254740992), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9649929107/4294967296), (-107717333655/8589934592)), (1/4294967296), by norm_num⟩, -2, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-19614186453/8589934592), (-109471678141/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((903698162555927/9007199254740992), (-162401733079677/9007199254740992)), (262119/9007199254740992), by norm_num⟩
  | 1 => ⟨((-83963907863/274877906944), (7544490361/137438953472)), (27/274877906944), by norm_num⟩
  | 2 => ⟨((31953750181/68719476736), (-11484685093/137438953472)), (11/68719476736), by norm_num⟩
  | 3 => ⟨((-64855939597/137438953472), (728445447/8589934592)), (3/17179869184), by norm_num⟩
  | 4 => ⟨((49363840831/137438953472), (-554442127/8589934592)), (39/274877906944), by norm_num⟩
  | 5 => ⟨((-60115728409/274877906944), (10803273575/274877906944)), (25/274877906944), by norm_num⟩
  | 6 => ⟨((61007894667/549755813888), (-10963602933/549755813888)), (27/549755813888), by norm_num⟩
  | 7 => ⟨((-53068544055/1099511627776), (596052413/68719476736)), (49/2199023255552), by norm_num⟩
  | 8 => ⟨((80784186557/4398046511104), (-3629389891/1099511627776)), (5/549755813888), by norm_num⟩
  | 9 => ⟨((-109310786039/17592186044416), (9822007963/8796093022208)), (7/2199023255552), by norm_num⟩
  | 10 => ⟨((16639957039/8796093022208), (-11961329451/35184372088832)), (9/8796093022208), by norm_num⟩
  | 11 => ⟨((-73688323735/140737488355328), (6621188345/70368744177664)), (21/70368744177664), by norm_num⟩
  | 12 => ⟨((74781918337/562949953421312), (-13438904321/562949953421312)), (45/562949953421312), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197625174288375/1267650600228229401496703205376), (-231617413229/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889223631277935/316912650057057350374175801344), (-274012722529/633825300114114700748351602688)), (361/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118086266984155/2475880078570760549798248448), (-154101600587/19807040628566084398385987584)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889132899084289/2475880078570760549798248448), (-327389657365/2475880078570760549798248448)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((221349915028799/19342813113834066795298816), (-20456494971/9671406556917033397649408)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1549186700941363/9671406556917033397649408), (-38344544981/1208925819614629174706176)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258467981921721/604462909807314587353088), (-134160392927/302231454903657293676544)), (177/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((14744306610077/590295810358705651712), (-108962668363/18889465931478580854784)), (575/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297149152275233/4722366482869645213696), (-163369401385/2361183241434822606848)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((810455967147609/295147905179352825856), (-224511771039/295147905179352825856)), (593/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822805116901951/73786976294838206464), (-560916208395/73786976294838206464)), (741/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910952342494929/4611686018427387904), (-315265855685/4611686018427387904)), (417/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593154409727269/1152921504606846976), (-629908536969/1152921504606846976)), (833/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193854612029701/144115188075855872), (-137617432215/36028797018963968)), (729/144115188075855872), by norm_num⟩
  | 4 => ⟨((372637727009725/9007199254740992), (-824306184173/36028797018963968)), (547/18014398509481984), by norm_num⟩
  | 3 => ⟨((371976083856735/2251799813685248), (-1027940170839/9007199254740992)), (171/1125899906842624), by norm_num⟩
  | 2 => ⟨((1112627831143893/2251799813685248), (-1024285626583/2251799813685248)), (171/281474976710656), by norm_num⟩
  | 1 => ⟨((138256289697293/140737488355328), (-1527324528653/1125899906842624)), (4105/2251799813685248), by norm_num⟩
  | 0 => ⟨((2172868006483289/2251799813685248), (-6036854902569/2251799813685248)), (8217/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2172868006483289/2251799813685248), (-6036854902569/2251799813685248)), (31345376021575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2096686793065649/2251799813685248), (-5825246453017/1125899906842624)), (15903/2251799813685248), by norm_num⟩
  | 2 => ⟨((244024787833861/281474976710656), (-169499377095/17592186044416)), (29781/2251799813685248), by norm_num⟩
  | 3 => ⟨((1692249673721419/2251799813685248), (-37618564905259/2251799813685248)), (13053/562949953421312), by norm_num⟩
  | 4 => ⟨((1271113792793307/2251799813685248), (-56541441916729/2251799813685248)), (80221/2251799813685248), by norm_num⟩
  | 5 => ⟨((358054328314453/1125899906842624), (-127667843736347/4503599627370496)), (189193/4503599627370496), by norm_num⟩
  | 6 => ⟨((903698162555927/9007199254740992), (-162401733079677/9007199254740992)), (262119/9007199254740992), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19614186453/8589934592), (-109471678141/8589934592)), (1/4294967296), by norm_num⟩, -2, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨9,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile009Terms2

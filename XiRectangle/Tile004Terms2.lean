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
namespace Reinmann.XiRectangle.Tile004Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨4,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (1269/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (1269/640))
  have he : value ((3/4), (1269/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-142898134647/68719476736), (-188893471737/34359738368)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((397960798335481/4503599627370496), (398170633081329/4503599627370496)), (15667/2251799813685248), by norm_num⟩
  | 1 => ⟨((-67345069663/274877906944), (-269522316115/1099511627776)), (3/137438953472), by norm_num⟩
  | 2 => ⟨((93360090323/274877906944), (186818633513/549755813888)), (9/274877906944), by norm_num⟩
  | 3 => ⟨((-172566089025/549755813888), (-86328539397/274877906944)), (19/549755813888), by norm_num⟩
  | 4 => ⟨((29903424517/137438953472), (59838383685/274877906944)), (29/1099511627776), by norm_num⟩
  | 5 => ⟨((-265311672231/2199023255552), (-265451564419/2199023255552)), (35/2199023255552), by norm_num⟩
  | 6 => ⟨((122600025051/2199023255552), (15333083621/274877906944)), (35/4398046511104), by norm_num⟩
  | 7 => ⟨((-194239683887/8796093022208), (-194342101599/8796093022208)), (15/4398046511104), by norm_num⟩
  | 8 => ⟨((134636689239/17592186044416), (269415359575/35184372088832)), (11/8796093022208), by norm_num⟩
  | 9 => ⟨((-165907629415/70368744177664), (-82997554173/35184372088832)), (29/70368744177664), by norm_num⟩
  | 10 => ⟨((45999362225/70368744177664), (184094466139/281474976710656)), (17/140737488355328), by norm_num⟩
  | 11 => ⟨((-185508818815/1125899906842624), (-185606632961/1125899906842624)), (9/281474976710656), by norm_num⟩
  | 12 => ⟨((85723276487/2251799813685248), (21442119055/562949953421312)), (35/4503599627370496), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49414595697703/316912650057057350374175801344), (1023412124687/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778760866437279/633825300114114700748351602688), (1211145402585/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118108310433839/2475880078570760549798248448), (1362290855411/39614081257132168796771975168)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889507499417055/2475880078570760549798248448), (1447127021897/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55349180157883/4835703278458516698824704), (723390877621/77371252455336267181195264)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193692197225783/1208925819614629174706176), (677995580425/4835703278458516698824704)), (51/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629387417053515/302231454903657293676544), (593062828047/302231454903657293676544)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235971196445077/9444732965739290427392), (1926767063665/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648761312946389/2361183241434822606848), (1444474326691/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405356255328727/147573952589676412928), (496294029697/147573952589676412928)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823445817454903/73786976294838206464), (620001724527/18446744073709551616)), (93/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911312284503445/4611686018427387904), (1393998602167/4611686018427387904)), (105/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796936582518055/576460752303423488), (696371531887/288230376151711744)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194482255082541/144115188075855872), (2434478310247/144115188075855872)), (23/36028797018963968), by norm_num⟩
  | 4 => ⟨((372872460452955/9007199254740992), (3646080629995/36028797018963968)), (69/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489073584688329/9007199254740992), (2273876327931/4503599627370496)), (173/9007199254740992), by norm_num⟩
  | 2 => ⟨((139223809416931/281474976710656), (9066026131859/4503599627370496)), (43/562949953421312), by norm_num⟩
  | 1 => ⟨((553888923741515/562949953421312), (6762784512097/1125899906842624)), (517/2251799813685248), by norm_num⟩
  | 0 => ⟨((1089823773467749/1125899906842624), (6689655051299/562949953421312)), (519/1125899906842624), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1089823773467749/1125899906842624), (6689655051299/562949953421312)), (1979832175826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2109489207805137/2251799813685248), (51802438684975/2251799813685248)), (2035/2251799813685248), by norm_num⟩
  | 2 => ⟨((987490361746309/1125899906842624), (48528596849425/1125899906842624)), (3907/2251799813685248), by norm_num⟩
  | 3 => ⟨((1728008296150709/2251799813685248), (170251445502883/2251799813685248)), (7191/2251799813685248), by norm_num⟩
  | 4 => ⟨((1313183835835943/2251799813685248), (32662307332191/281474976710656)), (12125/2251799813685248), by norm_num⟩
  | 5 => ⟨((1470978807386559/4503599627370496), (609526495477141/4503599627370496)), (33913/4503599627370496), by norm_num⟩
  | 6 => ⟨((397960798335481/4503599627370496), (398170633081329/4503599627370496)), (15667/2251799813685248), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-142898134647/68719476736), (-188893471737/34359738368)), (1/34359738368), by norm_num⟩, -1, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-18252837983/8589934592), (-96511880835/17179869184)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((423152634065151/4503599627370496), (664249830968425/9007199254740992)), (55621/9007199254740992), by norm_num⟩
  | 1 => ⟨((-292695724953/1099511627776), (-229731626573/1099511627776)), (11/549755813888), by norm_num⟩
  | 2 => ⟨((207317358421/549755813888), (81359838745/274877906944)), (9/274877906944), by norm_num⟩
  | 3 => ⟨((-48947858861/137438953472), (-76836593601/274877906944)), (19/549755813888), by norm_num⟩
  | 4 => ⟨((17334965861/68719476736), (108847231151/549755813888)), (29/1099511627776), by norm_num⟩
  | 5 => ⟨((-39290925277/274877906944), (-3854842847/34359738368)), (9/549755813888), by norm_num⟩
  | 6 => ⟨((296852196787/4398046511104), (29124245849/549755813888)), (9/1099511627776), by norm_num⟩
  | 7 => ⟨((-30037343041/1099511627776), (-188606175943/8796093022208)), (31/8796093022208), by norm_num⟩
  | 8 => ⟨((21275550281/2199023255552), (133590383613/17592186044416)), (3/2199023255552), by norm_num⟩
  | 9 => ⟨((-214322392741/70368744177664), (-168217803329/70368744177664)), (1/2199023255552), by norm_num⟩
  | 10 => ⟨((121444212609/140737488355328), (23829846255/35184372088832)), (39/281474976710656), by norm_num⟩
  | 11 => ⟨((-250238082707/1125899906842624), (-98203692213/562949953421312)), (21/562949953421312), by norm_num⟩
  | 12 => ⟨((59081489593/1125899906842624), (46372001869/1125899906842624)), (21/2251799813685248), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572467/10141204801825835211973625643008), (866828750001/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778690998552585/633825300114114700748351602688), (1025761615067/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889654392612585/39614081257132168796771975168), (576883901703/19807040628566084398385987584)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((118089003028957/154742504910672534362390528), (1225612613301/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771090352630867/154742504910672534362390528), (38291057395/4835703278458516698824704)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774729709791609/4835703278458516698824704), (1148414371431/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258706486562915/604462909807314587353088), (1004545336861/604462909807314587353088)), (23/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887658583446389/75557863725914323419136), (1631791589375/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648719725913483/2361183241434822606848), (1223323670269/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621310765798337/590295810358705651712), (1681225457995/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911651580574659/36893488147419103232), (262533215111/9223372036854775808)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822464304675397/9223372036854775808), (2361059315095/9223372036854775808)), (105/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398428295091345/288230376151711744), (1179443345329/576460752303423488)), (105/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298585645656757/36028797018963968), (1030792132107/72057594037927936)), (23/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491280960175593/36028797018963968), (1543749869851/18014398509481984)), (69/18014398509481984), by norm_num⟩
  | 3 => ⟨((744406788622429/4503599627370496), (3850855183479/9007199254740992)), (43/2251799813685248), by norm_num⟩
  | 2 => ⟨((278383026086427/562949953421312), (479763151533/281474976710656)), (43/562949953421312), by norm_num⟩
  | 1 => ⟨((553697181557689/562949953421312), (11450770186727/2251799813685248)), (129/562949953421312), by norm_num⟩
  | 0 => ⟨((1089072979527627/1125899906842624), (1415536337275/140737488355328)), (259/562949953421312), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1089072979527627/1125899906842624), (1415536337275/140737488355328)), (988008739280523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2106673440453771/2251799813685248), (43815543235317/2251799813685248)), (1013/1125899906842624), by norm_num⟩
  | 2 => ⟨((1970047761760939/2251799813685248), (81983345634825/2251799813685248)), (1935/1125899906842624), by norm_num⟩
  | 3 => ⟨((860282270899805/1125899906842624), (143450679396971/2251799813685248)), (3527/1125899906842624), by norm_num⟩
  | 4 => ⟨((1305517580742443/2251799813685248), (109608390127521/1125899906842624)), (365/70368744177664), by norm_num⟩
  | 5 => ⟨((367776954864277/1125899906842624), (508377980808757/4503599627370496)), (7909/1125899906842624), by norm_num⟩
  | 6 => ⟨((423152634065151/4503599627370496), (664249830968425/9007199254740992)), (55621/9007199254740992), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-18252837983/8589934592), (-96511880835/17179869184)), (1/34359738368), by norm_num⟩, -1, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-148968626081/68719476736), (-196917902601/34359738368)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((877559200332149/9007199254740992), (33787454969027/562949953421312)), (49413/9007199254740992), by norm_num⟩
  | 1 => ⟨((-154813984895/549755813888), (-23842359769/137438953472)), (5/274877906944), by norm_num⟩
  | 2 => ⟨((111867492417/274877906944), (34456641659/137438953472)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((-107779546903/274877906944), (-132790005231/549755813888)), (17/549755813888), by norm_num⟩
  | 4 => ⟨((311522958447/1099511627776), (191906240425/1099511627776)), (27/1099511627776), by norm_num⟩
  | 5 => ⟨((-90041716103/549755813888), (-55468037749/549755813888)), (17/1099511627776), by norm_num⟩
  | 6 => ⟨((86751344419/1099511627776), (106882166517/2199023255552)), (9/1099511627776), by norm_num⟩
  | 7 => ⟨((-143282077639/4398046511104), (-88265484435/4398046511104)), (1/274877906944), by norm_num⟩
  | 8 => ⟨((103534617655/8796093022208), (15945003963/2199023255552)), (25/17592186044416), by norm_num⟩
  | 9 => ⟨((-266003142075/70368744177664), (-163864850255/70368744177664)), (17/35184372088832), by norm_num⟩
  | 10 => ⟨((153769593873/140737488355328), (189452134115/281474976710656)), (21/140737488355328), by norm_num⟩
  | 11 => ⟨((-161618651401/562949953421312), (-199122581061/1125899906842624)), (47/1125899906842624), by norm_num⟩
  | 12 => ⟨((155712661853/2251799813685248), (95923047443/2251799813685248)), (3/281474976710656), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581151993160631/10141204801825835211973625643008), (179799504361/2535301200456458802993406410752)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444656274126533/158456325028528675187087900672), (212750650575/158456325028528675187087900672)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944790138316051/19807040628566084398385987584), (478598536349/19807040628566084398385987584)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889345330419829/2475880078570760549798248448), (1016797047443/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771011668526781/154742504910672534362390528), (1016544197757/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549385689279889/9671406556917033397649408), (952741619723/9671406556917033397649408)), (51/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258642008573343/604462909807314587353088), (833380449613/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943776937111341/37778931862957161709568), (1353740062015/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648680489470393/2361183241434822606848), (1014864982107/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810601480716483/295147905179352825856), (174340579471/73786976294838206464)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455792137336063/18446744073709551616), (871167202447/36893488147419103232)), (93/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822313063707829/9223372036854775808), (1958654152179/9223372036854775808)), (105/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593562185727731/1152921504606846976), (122300984103/72057594037927936)), (105/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74638171188279/9007199254740992), (1710147850535/144115188075855872)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491083747072649/36028797018963968), (2561095616383/36028797018963968)), (69/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488568025025927/9007199254740992), (3194161535477/9007199254740992)), (43/2251799813685248), by norm_num⟩
  | 2 => ⟨((2226575987161265/4503599627370496), (6366750199959/4503599627370496)), (43/562949953421312), by norm_num⟩
  | 1 => ⟨((553515891950529/562949953421312), (4748185751795/1125899906842624)), (129/562949953421312), by norm_num⟩
  | 0 => ⟨((544181034506951/562949953421312), (18778794812669/2251799813685248)), (517/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((544181034506951/562949953421312), (18778794812669/2251799813685248)), (1972202781295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1051997451359703/1125899906842624), (36305408414535/2251799813685248)), (2017/2251799813685248), by norm_num⟩
  | 2 => ⟨((491326586969831/562949953421312), (33922373463703/1125899906842624)), (3835/2251799813685248), by norm_num⟩
  | 3 => ⟨((856609479200437/1125899906842624), (7401618862629/140737488355328)), (3463/1125899906842624), by norm_num⟩
  | 4 => ⟨((648613275357267/1125899906842624), (180202075601891/2251799813685248)), (11269/2251799813685248), by norm_num⟩
  | 5 => ⟨((732891052658279/2251799813685248), (103811589087073/1125899906842624)), (3697/562949953421312), by norm_num⟩
  | 6 => ⟨((877559200332149/9007199254740992), (33787454969027/562949953421312)), (49413/9007199254740992), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-148968626081/68719476736), (-196917902601/34359738368)), (1/34359738368), by norm_num⟩, -1, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-18969403681/8589934592), (-200601443925/34359738368)), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((893393226314081/9007199254740992), (425968732196467/9007199254740992)), (87847/9007199254740992), by norm_num⟩
  | 1 => ⟨((-160555532183/549755813888), (-4784541851/34359738368)), (17/549755813888), by norm_num⟩
  | 2 => ⟨((29546622955/68719476736), (28175583047/137438953472)), (27/549755813888), by norm_num⟩
  | 3 => ⟨((-231995275551/549755813888), (-55307523323/274877906944)), (7/137438953472), by norm_num⟩
  | 4 => ⟨((170773983079/549755813888), (162849627513/1099511627776)), (11/274877906944), by norm_num⟩
  | 5 => ⟨((-100566714481/549755813888), (-47950079099/549755813888)), (7/274877906944), by norm_num⟩
  | 6 => ⟨((24676046177/274877906944), (23531013659/549755813888)), (15/1099511627776), by norm_num⟩
  | 7 => ⟨((-332146798699/8796093022208), (-9897947691/549755813888)), (53/8796093022208), by norm_num⟩
  | 8 => ⟨((30562061903/2199023255552), (116575611981/17592186044416)), (41/17592186044416), by norm_num⟩
  | 9 => ⟨((-319957782581/70368744177664), (-38138863993/17592186044416)), (7/8796093022208), by norm_num⟩
  | 10 => ⟨((2944050521/2199023255552), (44919023105/70368744177664)), (35/140737488355328), by norm_num⟩
  | 11 => ⟨((-201741430939/562949953421312), (-48095026377/281474976710656)), (39/562949953421312), by norm_num⟩
  | 12 => ⟨((99002555495/1125899906842624), (47204290123/1125899906842624)), (5/281474976710656), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581099171716351/10141204801825835211973625643008), (289775662097/5070602400912917605986812821504)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444640683186283/158456325028528675187087900672), (685717509723/633825300114114700748351602688)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889510138450331/39614081257132168796771975168), (771283944679/39614081257132168796771975168)), (51/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889270835257675/2475880078570760549798248448), (3200408759/9671406556917033397649408)), (27/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885468601667681/77371252455336267181195264), (819097108061/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387328977498133/2417851639229258349412352), (767683107107/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258580983510401/604462909807314587353088), (671502369653/604462909807314587353088)), (89/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887454768111507/75557863725914323419136), (8521706029/590295810358705651712)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297286701487319/4722366482869645213696), (817722597617/4722366482869645213696)), (27/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810550457290759/295147905179352825856), (561890990543/295147905179352825856)), (149/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455760279409641/18446744073709551616), (701924082681/36893488147419103232)), (93/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455542469321933/2305843009213693952), (1578121067035/9223372036854775808)), (209/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593419216846221/1152921504606846976), (98538269845/72057594037927936)), (209/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194085885597953/144115188075855872), (688920178307/72057594037927936)), (23/18014398509481984), by norm_num⟩
  | 4 => ⟨((745448477365331/18014398509481984), (2063374491607/36028797018963968)), (275/36028797018963968), by norm_num⟩
  | 3 => ⟨((46510480816119/281474976710656), (643325830161/2251799813685248)), (43/1125899906842624), by norm_num⟩
  | 2 => ⟨((278264156940433/562949953421312), (5128905307157/4503599627370496)), (343/2251799813685248), by norm_num⟩
  | 1 => ⟨((276671975824335/281474976710656), (7649254930945/2251799813685248)), (515/1125899906842624), by norm_num⟩
  | 0 => ⟨((543843446515699/562949953421312), (7561498348971/1125899906842624)), (129/140737488355328), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((543843446515699/562949953421312), (7561498348971/1125899906842624)), (492096484136537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2101440090411825/2251799813685248), (29219445159805/2251799813685248)), (4017/2251799813685248), by norm_num⟩
  | 2 => ⟨((1960741203894495/2251799813685248), (6817092832279/281474976710656)), (7603/2251799813685248), by norm_num⟩
  | 3 => ⟨((852991413580165/1125899906842624), (11871885525337/281474976710656)), (6805/1125899906842624), by norm_num⟩
  | 4 => ⟨((644230699885871/1125899906842624), (4497121082689/70368744177664)), (21771/2251799813685248), by norm_num⟩
  | 5 => ⟨((1456100397871131/4503599627370496), (10292863317475/140737488355328)), (55395/4503599627370496), by norm_num⟩
  | 6 => ⟨((893393226314081/9007199254740992), (425968732196467/9007199254740992)), (87847/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-18969403681/8589934592), (-200601443925/34359738368)), (1/17179869184), by norm_num⟩, -1, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-77199432855/34359738368), (-102048000305/17179869184)), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((896851046411111/9007199254740992), (160246008508859/4503599627370496)), (39095/4503599627370496), by norm_num⟩
  | 1 => ⟨((-327969436561/1099511627776), (-117200717627/1099511627776)), (31/1099511627776), by norm_num⟩
  | 2 => ⟨((122813578231/274877906944), (43887746535/274877906944)), (25/549755813888), by norm_num⟩
  | 3 => ⟨((-61319433323/137438953472), (-43825312903/274877906944)), (27/549755813888), by norm_num⟩
  | 4 => ⟨((91848302701/274877906944), (65644452131/549755813888)), (43/1099511627776), by norm_num⟩
  | 5 => ⟨((-110061169869/549755813888), (-19665320383/274877906944)), (7/274877906944), by norm_num⟩
  | 6 => ⟨((219809199095/2199023255552), (39274689961/1099511627776)), (15/1099511627776), by norm_num⟩
  | 7 => ⟨((-188139860501/4398046511104), (-134464521429/8796093022208)), (53/8796093022208), by norm_num⟩
  | 8 => ⟨((281808326023/17592186044416), (100704926623/17592186044416)), (21/8796093022208), by norm_num⟩
  | 9 => ⟨((-375209909877/70368744177664), (-134082221685/70368744177664)), (29/35184372088832), by norm_num⟩
  | 10 => ⟨((224805687275/140737488355328), (40167443881/70368744177664)), (37/140737488355328), by norm_num⟩
  | 11 => ⟨((-7652927871/17592186044416), (-43756693811/281474976710656)), (21/281474976710656), by norm_num⟩
  | 12 => ⟨((244545312111/2251799813685248), (87388893223/2251799813685248)), (11/562949953421312), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197631132535527/1267650600228229401496703205376), (111767306361/2535301200456458802993406410752)), (19/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778503545405111/633825300114114700748351602688), (528932840409/633825300114114700748351602688)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889443571337687/39614081257132168796771975168), (594933235597/39614081257132168796771975168)), (51/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944600065642439/1237940039285380274899124224), (631971738055/2475880078570760549798248448)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885433262939985/77371252455336267181195264), (315904438795/77371252455336267181195264)), (27/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549249678040405/9671406556917033397649408), (592147842461/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629261529350295/302231454903657293676544), (517956448229/604462909807314587353088)), (89/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943680346521943/37778931862957161709568), (841355155707/75557863725914323419136)), (145/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297216191311663/4722366482869645213696), (157683236017/1180591620717411303424)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621004037987523/590295810358705651712), (866797500165/590295810358705651712)), (149/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822920134144991/73786976294838206464), (1082806889977/73786976294838206464)), (187/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822033925041631/9223372036854775808), (1217209771163/9223372036854775808)), (209/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796641728546721/576460752303423488), (608012959769/576460752303423488)), (209/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596983656021975/72057594037927936), (66418274353/9007199254740992)), (183/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490719526046983/36028797018963968), (397845464391/9007199254740992)), (275/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488114353820351/9007199254740992), (496146676449/2251799813685248)), (343/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112836722166123/2251799813685248), (3955286120483/4503599627370496)), (343/2251799813685248), by norm_num⟩
  | 1 => ⟨((553180424477803/562949953421312), (2949165802861/1125899906842624)), (1029/2251799813685248), by norm_num⟩
  | 0 => ⟨((2174087849341879/2251799813685248), (5829497224813/1125899906842624)), (2061/2251799813685248), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2174087849341879/2251799813685248), (5829497224813/1125899906842624)), (7862099654387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2098997440082871/2251799813685248), (22513260738745/2251799813685248)), (2001/1125899906842624), by norm_num⟩
  | 2 => ⟨((1956338827187201/2251799813685248), (20985558472539/1125899906842624)), (3771/1125899906842624), by norm_num⟩
  | 3 => ⟨((849431643268911/1125899906842624), (18232021603575/562949953421312)), (13387/2251799813685248), by norm_num⟩
  | 4 => ⟨((159917521478261/281474976710656), (110040730808969/2251799813685248)), (5267/562949953421312), by norm_num⟩
  | 5 => ⟨((1442936714833671/4503599627370496), (250074676452909/4503599627370496)), (25999/2251799813685248), by norm_num⟩
  | 6 => ⟨((896851046411111/9007199254740992), (160246008508859/4503599627370496)), (39095/4503599627370496), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-77199432855/34359738368), (-102048000305/17179869184)), (1/17179869184), by norm_num⟩, -1, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-19614186453/8589934592), (-51855005435/8589934592)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((890427568237327/9007199254740992), (112008300626769/4503599627370496)), (69703/18014398509481984), by norm_num⟩
  | 1 => ⟨((-20682729421/68719476736), (-83254830193/1099511627776)), (15/1099511627776), by norm_num⟩
  | 2 => ⟨((251876135183/549755813888), (63367799643/549755813888)), (13/549755813888), by norm_num⟩
  | 3 => ⟨((-255614181697/549755813888), (-64308229281/549755813888)), (15/549755813888), by norm_num⟩
  | 4 => ⟨((389111555789/1099511627776), (3059185109/34359738368)), (25/1099511627776), by norm_num⟩
  | 5 => ⟨((-59232943119/274877906944), (-59608049315/1099511627776)), (17/1099511627776), by norm_num⟩
  | 6 => ⟨((30056004063/274877906944), (60492681203/2199023255552)), (19/2199023255552), by norm_num⟩
  | 7 => ⟨((-418313960037/8796093022208), (-3288773665/274877906944)), (9/2199023255552), by norm_num⟩
  | 8 => ⟨((318391559337/17592186044416), (40050980863/8796093022208)), (15/8796093022208), by norm_num⟩
  | 9 => ⟨((-215411165863/35184372088832), (-27096913309/17592186044416)), (43/70368744177664), by norm_num⟩
  | 10 => ⟨((262329651123/140737488355328), (32998864225/70368744177664)), (7/35184372088832), by norm_num⟩
  | 11 => ⟨((-18151557021/35184372088832), (-73066023675/562949953421312)), (33/562949953421312), by norm_num⟩
  | 12 => ⟨((294735054027/2251799813685248), (37075191419/1125899906842624)), (35/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197625174288375/1267650600228229401496703205376), (321052298181/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778447225499941/633825300114114700748351602688), (189908895605/316912650057057350374175801344)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889380227990455/39614081257132168796771975168), (427210297353/39614081257132168796771975168)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889132849873151/2475880078570760549798248448), (113451313955/618970019642690137449562112)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770799267961823/154742504910672534362390528), (226843205283/77371252455336267181195264)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549186648693329/9671406556917033397649408), (425204780719/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258467932960997/604462909807314587353088), (371928003343/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887271160452183/75557863725914323419136), (302073261631/37778931862957161709568)), (9/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297149082735469/4722366482869645213696), (113225768855/1180591620717411303424)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620911830057003/590295810358705651712), (311202923777/295147905179352825856)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822804973690389/73786976294838206464), (777503831399/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821904506149223/9223372036854775808), (218500021515/2305843009213693952)), (105/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199144276096287/144115188075855872), (27285508345/36028797018963968)), (105/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193854411370771/144115188075855872), (190755896489/36028797018963968)), (23/36028797018963968), by norm_num⟩
  | 4 => ⟨((372637639388827/9007199254740992), (285649237893/9007199254740992)), (137/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487903811037983/9007199254740992), (1424860384549/9007199254740992)), (43/2251799813685248), by norm_num⟩
  | 2 => ⟨((139078397248815/281474976710656), (2839589075635/4503599627370496)), (343/4503599627370496), by norm_num⟩
  | 1 => ⟨((553024509123201/562949953421312), (4234144177083/2251799813685248)), (257/1125899906842624), by norm_num⟩
  | 0 => ⟨((2172860279909399/2251799813685248), (1045983447407/281474976710656)), (1029/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2172860279909399/2251799813685248), (1045983447407/281474976710656)), (3925332076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2096656970174195/2251799813685248), (16149043960307/2251799813685248)), (1995/2251799813685248), by norm_num⟩
  | 2 => ⟨((1952087229177481/2251799813685248), (15036419034787/1125899906842624)), (3745/2251799813685248), by norm_num⟩
  | 3 => ⟨((1691864503929111/2251799813685248), (52140339282347/2251799813685248)), (3297/1125899906842624), by norm_num⟩
  | 4 => ⟨((1269956089033827/2251799813685248), (78350116842983/2251799813685248)), (10215/2251799813685248), by norm_num⟩
  | 5 => ⟨((1426991615773673/4503599627370496), (176749651290567/4503599627370496)), (24467/4503599627370496), by norm_num⟩
  | 6 => ⟨((890427568237327/9007199254740992), (112008300626769/4503599627370496)), (69703/18014398509481984), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19614186453/8589934592), (-51855005435/8589934592)), (1/34359738368), by norm_num⟩, -1, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨4,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile004Terms2

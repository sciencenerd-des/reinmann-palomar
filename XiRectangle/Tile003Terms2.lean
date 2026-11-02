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
namespace Reinmann.XiRectangle.Tile003Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨3,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (987/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (987/640))
  have he : value ((3/4), (987/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-142898134647/68719476736), (-293834289369/68719476736)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-476035033202483/9007199254740992), (510157144271413/4503599627370496)), (24361/2251799813685248), by norm_num⟩
  | 1 => ⟨((161114424371/1099511627776), (-345326158393/1099511627776)), (35/1099511627776), by norm_num⟩
  | 2 => ⟨((-13959501125/68719476736), (29920231633/68719476736)), (13/274877906944), by norm_num⟩
  | 3 => ⟨((103210547699/549755813888), (-55304331195/137438953472)), (13/274877906944), by norm_num⟩
  | 4 => ⟨((-143080200283/1099511627776), (306672329925/1099511627776)), (19/549755813888), by norm_num⟩
  | 5 => ⟨((4958781871/68719476736), (-340110497349/2199023255552)), (11/549755813888), by norm_num⟩
  | 6 => ⟨((-36663100511/1099511627776), (19645552693/274877906944)), (43/4398046511104), by norm_num⟩
  | 7 => ⟨((116173370285/8796093022208), (-124500657917/4398046511104)), (9/2199023255552), by norm_num⟩
  | 8 => ⟨((-80525244069/17592186044416), (86297280013/8796093022208)), (13/8796093022208), by norm_num⟩
  | 9 => ⟨((12403521309/8796093022208), (-106340829033/35184372088832)), (17/35184372088832), by norm_num⟩
  | 10 => ⟨((-13755945319/35184372088832), (29483938329/35184372088832)), (5/35184372088832), by norm_num⟩
  | 11 => ⟨((27737875531/281474976710656), (-237808974249/1125899906842624)), (21/562949953421312), by norm_num⟩
  | 12 => ⟨((-6408810073/281474976710656), (219782160017/4503599627370496)), (41/4503599627370496), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49414595697703/316912650057057350374175801344), (2614776182281/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778756525936847/633825300114114700748351602688), (6043802813/1237940039285380274899124224)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118107989939999/2475880078570760549798248448), (217536811925/2475880078570760549798248448)), (51/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889501732092451/2475880078570760549798248448), (3697340405197/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771167639221565/154742504910672534362390528), (1848228506321/77371252455336267181195264)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549531454170391/9671406556917033397649408), (1732245025817/4835703278458516698824704)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258769095529579/604462909807314587353088), (3030490630037/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887759533710605/75557863725914323419136), (4922788708367/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297514474506945/4722366482869645213696), (1845276640343/2361183241434822606848)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621412801875047/590295810358705651712), (317000751891/36893488147419103232)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823429028130999/73786976294838206464), (6336268563093/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911301800474061/4611686018427387904), (3561576682571/4611686018427387904)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((49807800047467/36028797018963968), (1779180338993/288230376151711744)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194458723470523/144115188075855872), (777487576067/18014398509481984)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((745724366596037/18014398509481984), (4657701668033/18014398509481984)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((744506032474111/4503599627370496), (11619001458843/9007199254740992)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((2227427651526137/4503599627370496), (23162366950811/4503599627370496)), (87/1125899906842624), by norm_num⟩
  | 1 => ⟨((1107625296733429/1125899906842624), (34554887977045/2251799813685248)), (131/562949953421312), by norm_num⟩
  | 0 => ⟨((1089369849825145/1125899906842624), (68357690020815/2251799813685248)), (1057/2251799813685248), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1089369849825145/1125899906842624), (68357690020815/2251799813685248)), (4032143599700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((526493726954153/562949953421312), (66139810528271/1125899906842624)), (1055/1125899906842624), by norm_num⟩
  | 2 => ⟨((1961822888232911/2251799813685248), (247426579456593/2251799813685248)), (1049/562949953421312), by norm_num⟩
  | 3 => ⟨((841000409884203/1125899906842624), (107782033683695/562949953421312)), (4117/1125899906842624), by norm_num⟩
  | 4 => ⟨((146730144098367/281474976710656), (322034788191205/1125899906842624)), (7727/1125899906842624), by norm_num⟩
  | 5 => ⟨((213846148068241/1125899906842624), (671494303730677/2251799813685248)), (24953/2251799813685248), by norm_num⟩
  | 6 => ⟨((-476035033202483/9007199254740992), (510157144271413/4503599627370496)), (24361/2251799813685248), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-142898134647/68719476736), (-293834289369/68719476736)), (1/34359738368), by norm_num⟩, -1, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-18252837983/8589934592), (-75064796205/17179869184)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-180933862843967/4503599627370496), (1013169380662529/9007199254740992)), (91869/9007199254740992), by norm_num⟩
  | 1 => ⟨((62576200513/549755813888), (-175202942449/549755813888)), (17/549755813888), by norm_num⟩
  | 2 => ⟨((-88645863157/549755813888), (15512103577/34359738368)), (13/274877906944), by norm_num⟩
  | 3 => ⟨((10464693433/68719476736), (-58598798465/137438953472)), (13/274877906944), by norm_num⟩
  | 4 => ⟨((-118594836303/1099511627776), (332045795513/1099511627776)), (39/1099511627776), by norm_num⟩
  | 5 => ⟨((33600447275/549755813888), (-188151315737/1099511627776)), (23/1099511627776), by norm_num⟩
  | 6 => ⟨((-15866205931/549755813888), (355381878965/4398046511104)), (23/2199023255552), by norm_num⟩
  | 7 => ⟨((102748220259/8796093022208), (-287677909063/8796093022208)), (39/8796093022208), by norm_num⟩
  | 8 => ⟨((-72776907179/17592186044416), (203763222687/17592186044416)), (29/17592186044416), by norm_num⟩
  | 9 => ⟨((91641113137/70368744177664), (-8018120577/2199023255552)), (19/35184372088832), by norm_num⟩
  | 10 => ⟨((-51927764921/140737488355328), (290778191527/281474976710656)), (23/140737488355328), by norm_num⟩
  | 11 => ⟨((106998135637/1125899906842624), (-299576964507/1125899906842624)), (49/1125899906842624), by norm_num⟩
  | 12 => ⟨((-101049515225/4503599627370496), (70730454451/1125899906842624)), (3/281474976710656), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572467/10141204801825835211973625643008), (1246494556543/5070602400912917605986812821504)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889343451256283/316912650057057350374175801344), (2950078131329/633825300114114700748351602688)), (47/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236206194258029/4951760157141521099596496896), (103694210685/1237940039285380274899124224)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889418606600323/2475880078570760549798248448), (1762419091839/1237940039285380274899124224)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885542286266467/77371252455336267181195264), (3523977780839/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549453641601075/9671406556917033397649408), (3302815209207/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258701071951855/604462909807314587353088), (2889049592487/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887649112369569/75557863725914323419136), (4692992891159/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648715880393411/2361183241434822606848), (439780822351/590295810358705651712)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621299236601267/590295810358705651712), (1208788906291/147573952589676412928)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823287320461043/73786976294838206464), (6040296106095/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822444521738627/9223372036854775808), (3395159652843/4611686018427387904)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199211368648171/144115188075855872), (6784056194447/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194320382195259/144115188075855872), (92640763793/2251799813685248)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((372810544629199/9007199254740992), (4439723513301/18014398509481984)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((744377771366793/4503599627370496), (11074724873613/9007199254740992)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((2226919604358623/4503599627370496), (22075826398283/4503599627370496)), (87/1125899906842624), by norm_num⟩
  | 1 => ⟨((1107250479755865/1125899906842624), (32930130265015/2251799813685248)), (523/2251799813685248), by norm_num⟩
  | 0 => ⟨((2177289841456087/2251799813685248), (65128515107643/2251799813685248)), (33/70368744177664), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2177289841456087/2251799813685248), (65128515107643/2251799813685248)), (125885278201081/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((2103361631634713/2251799813685248), (62973472806589/1125899906842624)), (263/281474976710656), by norm_num⟩
  | 2 => ⟨((978832019954135/1125899906842624), (235289097560403/2251799813685248)), (4167/2251799813685248), by norm_num⟩
  | 3 => ⟨((3276101207781/4398046511104), (409110083833459/2251799813685248)), (8117/2251799813685248), by norm_num⟩
  | 4 => ⟨((1175139238597957/2251799813685248), (304745763005981/1125899906842624)), (15043/2251799813685248), by norm_num⟩
  | 5 => ⟨((896591520860031/4503599627370496), (39759163062403/140737488355328)), (23845/2251799813685248), by norm_num⟩
  | 6 => ⟨((-180933862843967/4503599627370496), (1013169380662529/9007199254740992)), (91869/9007199254740992), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-18252837983/8589934592), (-75064796205/17179869184)), (1/34359738368), by norm_num⟩, -1, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-148968626081/68719476736), (-76579184345/17179869184)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-259885269725633/9007199254740992), (15584458166543/140737488355328)), (43315/4503599627370496), by norm_num⟩
  | 1 => ⟨((91694951649/1099511627776), (-87978276849/274877906944)), (33/1099511627776), by norm_num⟩
  | 2 => ⟨((-66258124647/549755813888), (254289926713/549755813888)), (13/274877906944), by norm_num⟩
  | 3 => ⟨((63836870737/549755813888), (-244997474163/549755813888)), (27/549755813888), by norm_num⟩
  | 4 => ⟨((-92256144145/1099511627776), (177033445019/549755813888)), (41/1099511627776), by norm_num⟩
  | 5 => ⟨((26665455353/549755813888), (-409353975749/2199023255552)), (25/1099511627776), by norm_num⟩
  | 6 => ⟨((-51382052709/2199023255552), (394395056829/4398046511104)), (25/2199023255552), by norm_num⟩
  | 7 => ⟨((42432352575/4398046511104), (-162849761959/4398046511104)), (43/8796093022208), by norm_num⟩
  | 8 => ⟨((-3832664797/1099511627776), (235348176373/17592186044416)), (1/549755813888), by norm_num⟩
  | 9 => ⟨((19693913043/17592186044416), (-302330543227/70368744177664)), (43/70368744177664), by norm_num⟩
  | 10 => ⟨((-91076368099/281474976710656), (349539065477/281474976710656)), (13/70368744177664), by norm_num⟩
  | 11 => ⟨((95725295333/1125899906842624), (-367381033867/1125899906842624)), (57/1125899906842624), by norm_num⟩
  | 12 => ⟨((-92227230049/4503599627370496), (176977960779/2251799813685248)), (57/4503599627370496), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581151993160631/10141204801825835211973625643008), (1189082604987/5070602400912917605986812821504)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222327655531399/79228162514264337593543950336), (1407001085445/316912650057057350374175801344)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944787863272351/19807040628566084398385987584), (197821721433/2475880078570760549798248448)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889340213010369/2475880078570760549798248448), (3362224980119/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771006233083963/154742504910672534362390528), (1680693937801/77371252455336267181195264)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774690127933241/4835703278458516698824704), (3150411935775/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629318458451845/302231454903657293676544), (2755721500277/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887544968109753/75557863725914323419136), (4476381208661/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297353746761697/4722366482869645213696), (3355828495587/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621192120226275/590295810358705651712), (576487112557/73786976294838206464)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113947103384579/4611686018427387904), (5761321974229/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822294461908395/9223372036854775808), (202394062923/288230376151711744)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593541282317511/1152921504606846976), (1617629454045/288230376151711744)), (105/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597094932544117/72057594037927936), (5654855293749/144115188075855872)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((745523641980825/18014398509481984), (264643817477/1125899906842624)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488513462654801/9007199254740992), (10561844633463/9007199254740992)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((1113220021645041/2251799813685248), (21052098179407/4503599627370496)), (347/4503599627370496), by norm_num⟩
  | 1 => ⟨((276724132790931/281474976710656), (7849908748095/562949953421312)), (523/2251799813685248), by norm_num⟩
  | 0 => ⟨((2175919505685381/2251799813685248), (62088009997049/2251799813685248)), (1055/2251799813685248), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2175919505685381/2251799813685248), (62088009997049/2251799813685248)), (4024514205168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1050442127556277/1125899906842624), (29997895727833/562949953421312)), (1049/1125899906842624), by norm_num⟩
  | 2 => ⟨((976844532687485/1125899906842624), (223899500970193/2251799813685248)), (4139/2251799813685248), by norm_num⟩
  | 3 => ⟨((1672781903053099/2251799813685248), (388515892158717/2251799813685248)), (4003/1125899906842624), by norm_num⟩
  | 4 => ⟨((36738038954349/70368744177664), (288614622624031/1125899906842624)), (7329/1125899906842624), by norm_num⟩
  | 5 => ⟨((232898657868283/1125899906842624), (602718458182857/2251799813685248)), (45641/4503599627370496), by norm_num⟩
  | 6 => ⟨((-259885269725633/9007199254740992), (15584458166543/140737488355328)), (43315/4503599627370496), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-148968626081/68719476736), (-76579184345/17179869184)), (1/34359738368), by norm_num⟩, -1, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-151755229447/68719476736), (-312046690551/68719476736)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-10557662124623/562949953421312), (975226114754811/9007199254740992)), (81741/9007199254740992), by norm_num⟩
  | 1 => ⟨((60715609157/1099511627776), (-350524143773/1099511627776)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((-44693351561/549755813888), (4031628719/8589934592)), (25/549755813888), by norm_num⟩
  | 3 => ⟨((21932807741/274877906944), (-15827846333/34359738368)), (13/274877906944), by norm_num⟩
  | 4 => ⟨((-64579814035/1099511627776), (372833021593/1099511627776)), (5/137438953472), by norm_num⟩
  | 5 => ⟨((76060528685/2199023255552), (-54889204075/274877906944)), (49/2199023255552), by norm_num⟩
  | 6 => ⟨((-18662965453/1099511627776), (26936318669/274877906944)), (25/2199023255552), by norm_num⟩
  | 7 => ⟨((7850280421/1099511627776), (-362570727517/8796093022208)), (11/2199023255552), by norm_num⟩
  | 8 => ⟨((-23114671669/8796093022208), (133445922851/8796093022208)), (17/8796093022208), by norm_num⟩
  | 9 => ⟨((60497546891/70368744177664), (-174632611935/35184372088832)), (47/70368744177664), by norm_num⟩
  | 10 => ⟨((-17813133521/70368744177664), (102839013923/70368744177664)), (57/281474976710656), by norm_num⟩
  | 11 => ⟨((19072612611/281474976710656), (-220220509945/562949953421312)), (63/1125899906842624), by norm_num⟩
  | 12 => ⟨((-37438762671/2251799813685248), (216141951165/2251799813685248)), (1/70368744177664), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790549585858185/5070602400912917605986812821504), (1134775557609/5070602400912917605986812821504)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444639780743229/158456325028528675187087900672), (1342651525367/316912650057057350374175801344)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889505875200019/39614081257132168796771975168), (1510189610615/19807040628566084398385987584)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889266040471111/2475880078570760549798248448), (12532927755/9671406556917033397649408)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770932110596997/154742504910672534362390528), (3207615889085/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549310819190895/9671406556917033397649408), (3006275660857/9671406556917033397649408)), (51/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258576212940815/604462909807314587353088), (1314813614525/302231454903657293676544)), (23/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887446423726771/75557863725914323419136), (2135762425003/37778931862957161709568)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648639962763893/2361183241434822606848), (1601113609621/2361183241434822606848)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810545378690571/295147905179352825856), (4400761785783/590295810358705651712)), (19/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823027162431411/73786976294838206464), (5497503088899/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822152449680917/9223372036854775808), (3089975677793/4611686018427387904)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593399633320497/1152921504606846976), (3087015629199/576460752303423488)), (105/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194066330205715/144115188075855872), (2697811662975/72057594037927936)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((372715699002051/9007199254740992), (8080142139897/36028797018963968)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488284274244327/9007199254740992), (10076949366605/9007199254740992)), (173/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112992958309091/2251799813685248), (10042175195925/2251799813685248)), (347/4503599627370496), by norm_num⟩
  | 1 => ⟨((2213122447234137/2251799813685248), (29953132205879/2251799813685248)), (261/1125899906842624), by norm_num⟩
  | 0 => ⟨((1087310136601227/1125899906842624), (59215551144469/2251799813685248)), (527/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1087310136601227/1125899906842624), (59215551144469/2251799813685248)), (2010349753951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((524632210022277/562949953421312), (57185961747139/1125899906842624)), (523/562949953421312), by norm_num⟩
  | 2 => ⟨((1949881303443293/2251799813685248), (213174171603121/2251799813685248)), (257/140737488355328), by norm_num⟩
  | 3 => ⟨((1668262803490989/2251799813685248), (369184089153707/2251799813685248)), (7901/2251799813685248), by norm_num⟩
  | 4 => ⟨((1175417048061505/2251799813685248), (547025610209877/2251799813685248)), (14299/2251799813685248), by norm_num⟩
  | 5 => ⟨((961336093972539/4503599627370496), (1142167654618719/4503599627370496)), (43751/4503599627370496), by norm_num⟩
  | 6 => ⟨((-10557662124623/562949953421312), (975226114754811/9007199254740992)), (81741/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-151755229447/68719476736), (-312046690551/68719476736)), (1/34359738368), by norm_num⟩, -1, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-77199432855/34359738368), (-9921333363/2147483648)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-43941929170509/4503599627370496), (1896663765524985/18014398509481984)), (9643/1125899906842624), by norm_num⟩
  | 1 => ⟨((16069122971/549755813888), (-346795462309/1099511627776)), (15/549755813888), by norm_num⟩
  | 2 => ⟨((-12034697573/274877906944), (259726589691/549755813888)), (3/68719476736), by norm_num⟩
  | 3 => ⟨((24035154615/549755813888), (-259357109013/549755813888)), (13/274877906944), by norm_num⟩
  | 4 => ⟨((-18000722095/549755813888), (388482230923/1099511627776)), (41/1099511627776), by norm_num⟩
  | 5 => ⟨((21570137651/1099511627776), (-14547359461/68719476736)), (51/2199023255552), by norm_num⟩
  | 6 => ⟨((-10769726251/1099511627776), (116213317953/1099511627776)), (53/4398046511104), by norm_num⟩
  | 7 => ⟨((36872247437/8796093022208), (-397878842525/8796093022208)), (3/549755813888), by norm_num⟩
  | 8 => ⟨((-27614845411/17592186044416), (297984622379/17592186044416)), (19/8796093022208), by norm_num⟩
  | 9 => ⟨((36767414945/70368744177664), (-396747622349/70368744177664)), (53/70368744177664), by norm_num⟩
  | 10 => ⟨((-22029066313/140737488355328), (475419862691/281474976710656)), (33/140737488355328), by norm_num⟩
  | 11 => ⟨((11998760893/281474976710656), (-258951022937/562949953421312)), (19/281474976710656), by norm_num⟩
  | 12 => ⟨((-5990845875/562949953421312), (258582645561/2251799813685248)), (39/2251799813685248), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197631132535527/1267650600228229401496703205376), (2166509482867/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778500176352761/633825300114114700748351602688), (1281611380663/316912650057057350374175801344)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889439592764537/39614081257132168796771975168), (720764244569/9903520314283042199192993792)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944597828344033/1237940039285380274899124224), (3062545578721/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770861773256019/154742504910672534362390528), (3061755549023/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387311231813771/2417851639229258349412352), (44836822765/151115727451828646838272)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314629651698021/151115727451828646838272), (627505792591/151115727451828646838272)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887352906107645/75557863725914323419136), (1019303817643/18889465931478580854784)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297209868083695/4722366482869645213696), (3056536183781/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405248639885681/147573952589676412928), (1050125874589/147573952589676412928)), (19/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911453555835755/36893488147419103232), (5247280592281/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822017662519267/9223372036854775808), (2949294549621/4611686018427387904)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593265183143223/1152921504606846976), (5892841647647/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((37310908274911/4503599627370496), (5149776752441/144115188075855872)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490687653362959/36028797018963968), (963970152953/4503599627370496)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((93004166536141/562949953421312), (9617154480695/9007199254740992)), (173/9007199254740992), by norm_num⟩
  | 2 => ⟨((556388659879791/1125899906842624), (9583403401619/2251799813685248)), (347/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106242669681159/1125899906842624), (7145485146645/562949953421312)), (261/1125899906842624), by norm_num⟩
  | 0 => ⟨((1086692501276555/1125899906842624), (56493711904881/2251799813685248)), (263/562949953421312), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1086692501276555/1125899906842624), (56493711904881/2251799813685248)), (1003267528343023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2096283515590431/2251799813685248), (27263210842815/562949953421312)), (2085/2251799813685248), by norm_num⟩
  | 2 => ⟨((121639144731423/140737488355328), (50760657430135/562949953421312)), (4085/2251799813685248), by norm_num⟩
  | 3 => ⟨((831905780362993/1125899906842624), (175489360452911/1125899906842624)), (7799/2251799813685248), by norm_num⟩
  | 4 => ⟨((587326375773135/1125899906842624), (129665712258903/562949953421312)), (13957/2251799813685248), by norm_num⟩
  | 5 => ⟨((493293377588293/2251799813685248), (1082243171070213/4503599627370496)), (41983/4503599627370496), by norm_num⟩
  | 6 => ⟨((-43941929170509/4503599627370496), (1896663765524985/18014398509481984)), (9643/1125899906842624), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-77199432855/34359738368), (-9921333363/2147483648)), (1/34359738368), by norm_num⟩, -1, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-19614186453/8589934592), (-322653367151/68719476736)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-31518531347659/18014398509481984), (1836078797284733/18014398509481984)), (145755/18014398509481984), by norm_num⟩
  | 1 => ⟨((732108123/137438953472), (-341185491685/1099511627776)), (29/1099511627776), by norm_num⟩
  | 2 => ⟨((-8915678429/1099511627776), (519373442431/1099511627776)), (23/549755813888), by norm_num⟩
  | 3 => ⟨((4523997171/549755813888), (-527081366347/1099511627776)), (49/1099511627776), by norm_num⟩
  | 4 => ⟨((-860838181/137438953472), (100294440397/274877906944)), (5/137438953472), by norm_num⟩
  | 5 => ⟨((8386691703/2199023255552), (-122139469667/549755813888)), (51/2199023255552), by norm_num⟩
  | 6 => ⟨((-8511157023/4398046511104), (495808474577/4398046511104)), (27/2199023255552), by norm_num⟩
  | 7 => ⟨((3701772647/4398046511104), (-215642860809/4398046511104)), (49/8796093022208), by norm_num⟩
  | 8 => ⟨((-2817532471/8796093022208), (164132382067/8796093022208)), (39/17592186044416), by norm_num⟩
  | 9 => ⟨((1906231295/17592186044416), (-222090986649/35184372088832)), (55/70368744177664), by norm_num⟩
  | 10 => ⟨((-4642851159/140737488355328), (67616099207/35184372088832)), (35/140737488355328), by norm_num⟩
  | 11 => ⟨((80314003/8796093022208), (-299430881727/562949953421312)), (5/70368744177664), by norm_num⟩
  | 12 => ⟨((-1304094849/562949953421312), (151937339661/1125899906842624)), (21/1125899906842624), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197625174288375/1267650600228229401496703205376), (517124079307/2535301200456458802993406410752)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778444095068279/633825300114114700748351602688), (2447114400951/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889376531544269/39614081257132168796771975168), (2752453021569/39614081257132168796771975168)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944564346297173/1237940039285380274899124224), (2923799857063/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221349356549611/19342813113834066795298816), (2923033440543/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549182234864251/9671406556917033397649408), (1369764885971/4835703278458516698824704)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629231898419897/302231454903657293676544), (1198137370345/302231454903657293676544)), (23/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887263925925421/75557863725914323419136), (1946210565687/37778931862957161709568)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81071450508475/295147905179352825856), (2917981762431/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620903024196401/590295810358705651712), (4010058103415/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455698218859677/18446744073709551616), (5009324271059/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910944699016125/4611686018427387904), (5631026352413/9223372036854775808)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796568616163951/576460752303423488), (5625451594187/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193837460134847/144115188075855872), (4916004804189/144115188075855872)), (23/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490520949524511/36028797018963968), (7361492167961/36028797018963968)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487859512049973/9007199254740992), (9179999055347/9007199254740992)), (173/9007199254740992), by norm_num⟩
  | 2 => ⟨((139071500205587/281474976710656), (18294540123913/4503599627370496)), (347/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105939255875539/1125899906842624), (13639328055565/1125899906842624)), (261/1125899906842624), by norm_num⟩
  | 0 => ⟨((543051895776201/562949953421312), (53907635060001/2251799813685248)), (1051/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((543051895776201/562949953421312), (53907635060001/2251799813685248)), (4009255416106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2094138085597775/2251799813685248), (52002213053273/1125899906842624)), (2079/2251799813685248), by norm_num⟩
  | 2 => ⟨((1942711503178423/2251799813685248), (193444930989679/2251799813685248)), (1015/562949953421312), by norm_num⟩
  | 3 => ⟨((1659431278280795/2251799813685248), (333784282582533/2251799813685248)), (963/281474976710656), by norm_num⟩
  | 4 => ⟨((1173417016903099/2251799813685248), (15373593473699/70368744177664)), (1705/281474976710656), by norm_num⟩
  | 5 => ⟨((62998927309995/281474976710656), (8011207782927/35184372088832)), (1261/140737488355328), by norm_num⟩
  | 6 => ⟨((-31518531347659/18014398509481984), (1836078797284733/18014398509481984)), (145755/18014398509481984), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19614186453/8589934592), (-322653367151/68719476736)), (1/34359738368), by norm_num⟩, -1, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile003Terms2

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
namespace Reinmann.XiRectangle.Tile002Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨2,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (141/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (141/128))
  have he : value ((3/4), (141/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-53103704991/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-39827778743/17179869184), (-58497050029/17179869184)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-53103704991/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-856113956709833/9007199254740992), (461698972528025/18014398509481984)), (602397/18014398509481984), by norm_num⟩
  | 1 => ⟨((80758196567/274877906944), (-21776292797/274877906944)), (15/137438953472), by norm_num⟩
  | 2 => ⟨((-62406753511/137438953472), (8413930689/68719476736)), (25/137438953472), by norm_num⟩
  | 3 => ⟨((64300641493/137438953472), (-33864345/268435456)), (7/34359738368), by norm_num⟩
  | 4 => ⟨((-99378006317/274877906944), (26797088781/274877906944)), (45/274877906944), by norm_num⟩
  | 5 => ⟨((61436327291/274877906944), (-8283093905/137438953472)), (15/137438953472), by norm_num⟩
  | 6 => ⟨((-31650382639/274877906944), (17068929937/549755813888)), (33/549755813888), by norm_num⟩
  | 7 => ⟨((13976096629/274877906944), (-15074510591/1099511627776)), (31/1099511627776), by norm_num⟩
  | 8 => ⟨((-86401416025/4398046511104), (5824494025/1099511627776)), (25/2199023255552), by norm_num⟩
  | 9 => ⟨((29674493885/4398046511104), (-2000417589/1099511627776)), (9/2199023255552), by norm_num⟩
  | 10 => ⟨((-73380096305/35184372088832), (19786802215/35184372088832)), (47/35184372088832), by norm_num⟩
  | 11 => ⟨((41240180529/70368744177664), (-11120335575/70368744177664)), (55/140737488355328), by norm_num⟩
  | 12 => ⟨((-84983432533/562949953421312), (5728904893/140737488355328)), (29/281474976710656), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790477973085629/5070602400912917605986812821504), (1874594193437/5070602400912917605986812821504)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778382999314769/633825300114114700748351602688), (4435185280991/633825300114114700748351602688)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889307402866745/39614081257132168796771975168), (2494275237353/19807040628566084398385987584)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472263680128071/618970019642690137449562112), (5299078545039/2475880078570760549798248448)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110670018288897/9671406556917033397649408), (5297665298773/154742504910672534362390528)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96819481944211/604462909807314587353088), (1241264976583/2417851639229258349412352)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157300183136993/75557863725914323419136), (542865800237/75557863725914323419136)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943580734473663/37778931862957161709568), (7054441625269/75557863725914323419136)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297065344580653/4722366482869645213696), (5288369791185/4722366482869645213696)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620794305008929/590295810358705651712), (1816877455169/147573952589676412928)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822654494814533/73786976294838206464), (9078391375409/73786976294838206464)), (375/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910865156677215/4611686018427387904), (637809330577/576460752303423488)), (421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796486949108027/576460752303423488), (10194653066547/1152921504606846976)), (211/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193689774068521/144115188075855872), (8908745117203/144115188075855872)), (185/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490289912685057/36028797018963968), (3334995600987/9007199254740992)), (139/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487554144163593/9007199254740992), (16634530405225/9007199254740992)), (87/1125899906842624), by norm_num⟩
  | 2 => ⟨((1112241909142819/2251799813685248), (4143484355227/562949953421312)), (699/2251799813685248), by norm_num⟩
  | 1 => ⟨((1105382770333997/1125899906842624), (24709698853681/1125899906842624)), (33/35184372088832), by norm_num⟩
  | 0 => ⟨((1084748211893237/1125899906842624), (48816225488001/1125899906842624)), (1071/562949953421312), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1084748211893237/1125899906842624), (48816225488001/1125899906842624)), (4085542918968023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((65186503935537/70368744177664), (47031990133105/562949953421312)), (2157/562949953421312), by norm_num⟩
  | 2 => ⟨((479157923659801/562949953421312), (43568363280255/281474976710656)), (8715/1125899906842624), by norm_num⟩
  | 3 => ⟨((1577401368211117/2251799813685248), (593335201035157/2251799813685248)), (8767/562949953421312), by norm_num⟩
  | 4 => ⟨((948640462027083/2251799813685248), (415635418491733/1125899906842624)), (16903/562949953421312), by norm_num⟩
  | 5 => ⟨((185547152554269/4503599627370496), (700397207667467/2251799813685248)), (106887/2251799813685248), by norm_num⟩
  | 6 => ⟨((-856113956709833/9007199254740992), (461698972528025/18014398509481984)), (602397/18014398509481984), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-39827778743/17179869184), (-58497050029/17179869184)), (1/8589934592), by norm_num⟩, -1, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-53867380457/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-40400535343/17179869184), (-59338286285/17179869184)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-53867380457/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1632242600955621/18014398509481984), (527085100433689/18014398509481984)), (294271/9007199254740992), by norm_num⟩
  | 1 => ⟨((39046380877/137438953472), (-25217777767/274877906944)), (15/137438953472), by norm_num⟩
  | 2 => ⟨((-61214850697/137438953472), (9883774541/68719476736)), (25/137438953472), by norm_num⟩
  | 3 => ⟨((31989801715/68719476736), (-10330172635/68719476736)), (27/137438953472), by norm_num⟩
  | 4 => ⟨((-50151919123/137438953472), (32390196547/274877906944)), (45/274877906944), by norm_num⟩
  | 5 => ⟨((62900420931/274877906944), (-20311854785/274877906944)), (15/137438953472), by norm_num⟩
  | 6 => ⟨((-65741302003/549755813888), (10614617199/274877906944)), (33/549755813888), by norm_num⟩
  | 7 => ⟨((58894706337/1099511627776), (-9509163095/549755813888)), (31/1099511627776), by norm_num⟩
  | 8 => ⟨((-92332005535/4398046511104), (29815925883/4398046511104)), (51/4398046511104), by norm_num⟩
  | 9 => ⟨((16083692739/2199023255552), (-20775036255/8796093022208)), (37/8796093022208), by norm_num⟩
  | 10 => ⟨((-40344260443/17592186044416), (26056002405/35184372088832)), (49/35184372088832), by norm_num⟩
  | 11 => ⟨((45999707369/70368744177664), (-29708525393/140737488355328)), (29/70368744177664), by norm_num⟩
  | 12 => ⟨((-24038636065/140737488355328), (15525151589/281474976710656)), (63/562949953421312), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790456259316679/5070602400912917605986812821504), (3685404190603/10141204801825835211973625643008)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889165991337793/316912650057057350374175801344), (544936297667/79228162514264337593543950336)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944625020823925/19807040628566084398385987584), (1225849727919/9903520314283042199192993792)), (205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888993815038111/2475880078570760549798248448), (325538055483/154742504910672534362390528)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770659433056865/154742504910672534362390528), (2603600017453/77371252455336267181195264)), (109/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774527352011585/4835703278458516698824704), (4880253409045/9671406556917033397649408)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258351632633769/604462909807314587353088), (2134362713185/302231454903657293676544)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943540291265313/37778931862957161709568), (433367119829/4722366482869645213696)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324251189909763/1180591620717411303424), (5197951824421/4722366482869645213696)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810355565208529/295147905179352825856), (3571598950951/295147905179352825856)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822550720975931/73786976294838206464), (4461510403961/36893488147419103232)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455403458709755/2305843009213693952), (10030184228587/9223372036854775808)), (421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796428876571909/576460752303423488), (10019921911371/1152921504606846976)), (211/576460752303423488), by norm_num⟩
  | 5 => ⟨((596794260870377/72057594037927936), (8755894008599/144115188075855872)), (185/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490138782131115/36028797018963968), (3277696078235/9007199254740992)), (555/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487366536974071/9007199254740992), (8174086566969/4503599627370496)), (87/1125899906842624), by norm_num⟩
  | 2 => ⟨((1112056255179185/2251799813685248), (4071949080213/562949953421312)), (699/2251799813685248), by norm_num⟩
  | 1 => ⟨((552554576109283/562949953421312), (6070261829301/281474976710656)), (1055/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084220305496873/1125899906842624), (11990320014583/281474976710656)), (535/281474976710656), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1084220305496873/1125899906842624), (11990320014583/281474976710656)), (2040864110851199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1042040575131597/1125899906842624), (23092902575457/281474976710656)), (4305/1125899906842624), by norm_num⟩
  | 2 => ⟨((239212215775905/281474976710656), (170983167046665/1125899906842624)), (2169/281474976710656), by norm_num⟩
  | 3 => ⟨((1574428593559287/2251799813685248), (581241895497647/2251799813685248)), (8691/562949953421312), by norm_num⟩
  | 4 => ⟨((950787562075285/2251799813685248), (812793263845619/2251799813685248)), (66561/2251799813685248), by norm_num⟩
  | 5 => ⟨((27018842545995/562949953421312), (1372757420275743/4503599627370496)), (26065/562949953421312), by norm_num⟩
  | 6 => ⟨((-1632242600955621/18014398509481984), (527085100433689/18014398509481984)), (294271/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40400535343/17179869184), (-59338286285/17179869184)), (1/8589934592), by norm_num⟩, -1, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-54598549065/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-40948911799/17179869184), (-15035928551/4294967296)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-54598549065/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-388825439210605/4503599627370496), (584057183984061/18014398509481984)), (35949/1125899906842624), by norm_num⟩
  | 1 => ⟨((75421641627/274877906944), (-28322832805/274877906944)), (15/137438953472), by norm_num⟩
  | 2 => ⟨((-29961754633/68719476736), (22502871821/137438953472)), (13/68719476736), by norm_num⟩
  | 3 => ⟨((31740023025/68719476736), (-23838445995/137438953472)), (29/137438953472), by norm_num⟩
  | 4 => ⟨((-50435750875/137438953472), (18939966151/137438953472)), (3/17179869184), by norm_num⟩
  | 5 => ⟨((32057506251/137438953472), (-24076892789/274877906944)), (1/8589934592), by norm_num⟩
  | 6 => ⟨((-67920320355/549755813888), (25505887117/549755813888)), (35/549755813888), by norm_num⟩
  | 7 => ⟨((3854543469/68719476736), (-23159737785/1099511627776)), (17/549755813888), by norm_num⟩
  | 8 => ⟨((-97999573087/4398046511104), (36801446689/4398046511104)), (7/549755813888), by norm_num⟩
  | 9 => ⟨((34605324291/4398046511104), (-6497609923/2199023255552)), (21/4398046511104), by norm_num⟩
  | 10 => ⟨((-87982066731/35184372088832), (16519803283/17592186044416)), (7/4398046511104), by norm_num⟩
  | 11 => ⟨((50838498941/70368744177664), (-4772802191/17592186044416)), (17/35184372088832), by norm_num⟩
  | 12 => ⟨((-53855828763/281474976710656), (20224296379/281474976710656)), (19/140737488355328), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580870939646181/10141204801825835211973625643008), (906083763311/2535301200456458802993406410752)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889141567280439/316912650057057350374175801344), (1071756329809/158456325028528675187087900672)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944597559200257/19807040628566084398385987584), (1205470275509/9903520314283042199192993792)), (205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888935497938749/2475880078570760549798248448), (640250062031/309485009821345068724781056)), (109/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((13832821559763/1208925819614629174706176), (40004660063/1208925819614629174706176)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774500059553873/4835703278458516698824704), (4799067749297/9671406556917033397649408)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314575979303791/151115727451828646838272), (262355822485/37778931862957161709568)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943501565948413/37778931862957161709568), (6818456250145/75557863725914323419136)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296946747674401/4722366482869645213696), (5111397162377/4722366482869645213696)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620631487397629/590295810358705651712), (3512099638983/295147905179352825856)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822451352200093/73786976294838206464), (2193573430759/18446744073709551616)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910751149548057/4611686018427387904), (2465723907277/2305843009213693952)), (421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398186633674707/288230376151711744), (9852670366701/1152921504606846976)), (421/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596745781030169/72057594037927936), (4304795530705/72057594037927936)), (185/72057594037927936), by norm_num⟩
  | 4 => ⟨((11640578549025/281474976710656), (1611426920841/4503599627370496)), (555/36028797018963968), by norm_num⟩
  | 3 => ⟨((743593434873649/4503599627370496), (8037057072441/4503599627370496)), (87/1125899906842624), by norm_num⟩
  | 2 => ⟨((555939223100385/1125899906842624), (16013970824355/2251799813685248)), (699/2251799813685248), by norm_num⟩
  | 1 => ⟨((1104847064622641/1125899906842624), (11935455450551/562949953421312)), (1055/1125899906842624), by norm_num⟩
  | 0 => ⟨((67732157203929/70368744177664), (47143522248577/1125899906842624)), (2139/1125899906842624), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((67732157203929/70368744177664), (47143522248577/1125899906842624)), (8159641746139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((520567872764409/562949953421312), (90754282953399/1125899906842624)), (2149/562949953421312), by norm_num⟩
  | 2 => ⟨((1910875548005219/2251799813685248), (335687133353063/2251799813685248)), (4321/562949953421312), by norm_num⟩
  | 3 => ⟨((1571524913963817/2251799813685248), (569727673841967/2251799813685248)), (4311/281474976710656), by norm_num⟩
  | 4 => ⟨((476308089162903/1125899906842624), (795222761966577/2251799813685248)), (65591/2251799813685248), by norm_num⟩
  | 5 => ⟨((244336410711477/4503599627370496), (168208129296919/562949953421312)), (203647/4503599627370496), by norm_num⟩
  | 6 => ⟨((-388825439210605/4503599627370496), (584057183984061/18014398509481984)), (35949/1125899906842624), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-40948911799/17179869184), (-15035928551/4294967296)), (1/8589934592), by norm_num⟩, -1, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55299865591/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-41474899193/17179869184), (-30458129095/8589934592)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-55299865591/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1481417235834907/18014398509481984), (633680836591497/18014398509481984)), (562127/18014398509481984), by norm_num⟩
  | 1 => ⟨((72761507065/274877906944), (-31123961267/274877906944)), (29/274877906944), by norm_num⟩
  | 2 => ⟨((-29276282009/68719476736), (3130755203/17179869184)), (25/137438953472), by norm_num⟩
  | 3 => ⟨((62824477601/137438953472), (-6718341491/34359738368)), (29/137438953472), by norm_num⟩
  | 4 => ⟨((-6319506005/17179869184), (21625507009/137438953472)), (25/137438953472), by norm_num⟩
  | 5 => ⟨((65093456335/274877906944), (-27843928685/274877906944)), (17/137438953472), by norm_num⟩
  | 6 => ⟨((-34921292159/274877906944), (29875382971/549755813888)), (19/274877906944), by norm_num⟩
  | 7 => ⟨((64232744631/1099511627776), (-27475756573/1099511627776)), (37/1099511627776), by norm_num⟩
  | 8 => ⟨((-51689307215/2199023255552), (22110262151/2199023255552)), (1/68719476736), by norm_num⟩
  | 9 => ⟨((73947316177/8796093022208), (-31631194809/8796093022208)), (3/549755813888), by norm_num⟩
  | 10 => ⟨((-95210891343/35184372088832), (40726755313/35184372088832)), (1/549755813888), by norm_num⟩
  | 11 => ⟨((27861094219/35184372088832), (-23835339655/70368744177664)), (39/70368744177664), by norm_num⟩
  | 12 => ⟨((-29893800879/140737488355328), (399598951/4398046511104)), (11/70368744177664), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580831058241955/10141204801825835211973625643008), (1782879620353/5070602400912917605986812821504)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778236277993855/633825300114114700748351602688), (4217526008177/633825300114114700748351602688)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472285608542169/9903520314283042199192993792), (4743699916675/39614081257132168796771975168)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888879557993709/2475880078570760549798248448), (2519468807641/1237940039285380274899124224)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885272630685979/77371252455336267181195264), (2518769420257/77371252455336267181195264)), (109/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774473879362641/4835703278458516698824704), (4721206781803/9671406556917033397649408)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629129073056223/302231454903657293676544), (4129570408955/604462909807314587353088)), (179/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943464418372639/37778931862957161709568), (1676941827937/18889465931478580854784)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296891098795299/4722366482869645213696), (5028389713359/4722366482869645213696)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202569385986601/73786976294838206464), (6910079148683/590295810358705651712)), (75/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455589007307229/18446744073709551616), (4315833180285/36893488147419103232)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455348825769931/2305843009213693952), (9702471405127/9223372036854775808)), (421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398159960308531/288230376151711744), (9692285905481/1152921504606846976)), (211/576460752303423488), by norm_num⟩
  | 5 => ⟨((596699272579901/72057594037927936), (1058662477743/18014398509481984)), (369/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489855207462627/36028797018963968), (6340534954919/18014398509481984)), (555/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487014495919619/9007199254740992), (15811344685265/9007199254740992)), (87/1125899906842624), by norm_num⟩
  | 2 => ⟨((1111707843897403/2251799813685248), (15751449698717/2251799813685248)), (349/1125899906842624), by norm_num⟩
  | 1 => ⟨((1104595570701475/1125899906842624), (23477766714615/1125899906842624)), (527/562949953421312), by norm_num⟩
  | 0 => ⟨((1083229049898753/1125899906842624), (46359883055299/1125899906842624)), (1069/562949953421312), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1083229049898753/1125899906842624), (46359883055299/1125899906842624)), (4077913524436773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((260066620635969/281474976710656), (89205748699699/1125899906842624)), (4291/1125899906842624), by norm_num⟩
  | 2 => ⟨((1908156635549457/2251799813685248), (329683837288033/2251799813685248)), (17219/2251799813685248), by norm_num⟩
  | 3 => ⟨((1568687541296781/2251799813685248), (558742742522049/2251799813685248)), (34225/2251799813685248), by norm_num⟩
  | 4 => ⟨((954164369692503/2251799813685248), (194620492829219/562949953421312)), (64671/2251799813685248), by norm_num⟩
  | 5 => ⟨((135178741411793/2251799813685248), (1319477433054573/4503599627370496)), (199045/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1481417235834907/18014398509481984), (633680836591497/18014398509481984)), (562127/18014398509481984), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-41474899193/17179869184), (-30458129095/8589934592)), (1/8589934592), by norm_num⟩, -1, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6996709039/2147483648), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-20990127117/8589934592), (-30829249203/8589934592)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1410557196321095/18014398509481984), (338433364904649/9007199254740992)), (549109/18014398509481984), by norm_num⟩
  | 1 => ⟨((70125297821/274877906944), (-16825082009/137438953472)), (29/274877906944), by norm_num⟩
  | 2 => ⟨((-57118747515/137438953472), (27408870723/137438953472)), (13/68719476736), by norm_num⟩
  | 3 => ⟨((62032797845/137438953472), (-29766915605/137438953472)), (15/68719476736), by norm_num⟩
  | 4 => ⟨((-1578975343/4294967296), (12122935585/68719476736)), (13/68719476736), by norm_num⟩
  | 5 => ⟨((65849012463/274877906944), (-1974884723/17179869184)), (9/68719476736), by norm_num⟩
  | 6 => ⟨((-71514146513/549755813888), (34316613755/549755813888)), (41/549755813888), by norm_num⟩
  | 7 => ⟨((66571426621/1099511627776), (-31944811563/1099511627776)), (5/137438953472), by norm_num⟩
  | 8 => ⟨((-54224033651/2199023255552), (13009909995/1099511627776)), (17/1099511627776), by norm_num⟩
  | 9 => ⟨((78518727251/8796093022208), (-18838907873/4398046511104)), (13/2199023255552), by norm_num⟩
  | 10 => ⟨((-51164318685/17592186044416), (1534474513/1099511627776)), (9/4398046511104), by norm_num⟩
  | 11 => ⟨((30308779923/35184372088832), (-29087802755/70368744177664)), (45/70368744177664), by norm_num⟩
  | 12 => ⟨((-32916310313/140737488355328), (15795144909/140737488355328)), (51/281474976710656), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792741223529/10141204801825835211973625643008), (438685139991/1267650600228229401496703205376)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778191256820469/633825300114114700748351602688), (518844934009/79228162514264337593543950336)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889091813404181/39614081257132168796771975168), (2334296615371/19807040628566084398385987584)), (51/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944412904416311/1237940039285380274899124224), (1239785422459/618970019642690137449562112)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885245776010841/77371252455336267181195264), (4957748484161/154742504910672534362390528)), (217/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548897448490153/9671406556917033397649408), (1161602313797/2417851639229258349412352)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258214166916991/604462909807314587353088), (4064128522869/604462909807314587353088)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886857449747195/75557863725914323419136), (6601435439133/75557863725914323419136)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296837627798451/4722366482869645213696), (4948650638673/4722366482869645213696)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810240838862309/295147905179352825856), (3400226981389/295147905179352825856)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822264435054673/73786976294838206464), (8494659060375/73786976294838206464)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((56915390348087/288230376151711744), (2387092909183/2305843009213693952)), (421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592537318326699/1152921504606846976), (2384557058139/288230376151711744)), (211/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193309162300271/144115188075855872), (8334547113309/144115188075855872)), (369/144115188075855872), by norm_num⟩
  | 4 => ⟨((744860890673393/18014398509481984), (12479037348443/36028797018963968)), (555/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486848844888895/9007199254740992), (15558975082659/9007199254740992)), (695/9007199254740992), by norm_num⟩
  | 2 => ⟨((555771942454887/1125899906842624), (1937417645705/281474976710656)), (349/1125899906842624), by norm_num⟩
  | 1 => ⟨((1104353843509039/1125899906842624), (5775067990731/281474976710656)), (527/562949953421312), by norm_num⟩
  | 0 => ⟨((135345290974321/140737488355328), (22803828600113/562949953421312)), (267/140737488355328), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((135345290974321/140737488355328), (22803828600113/562949953421312)), (1018524706792787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((519715026612663/562949953421312), (43860251497717/562949953421312)), (2141/562949953421312), by norm_num⟩
  | 2 => ⟨((1905533417993567/2251799813685248), (80983510650775/562949953421312)), (4287/562949953421312), by norm_num⟩
  | 3 => ⟨((1565913773375031/2251799813685248), (548243355963115/2251799813685248)), (33957/2251799813685248), by norm_num⟩
  | 4 => ⟨((955464671065411/2251799813685248), (381251395904055/1125899906842624)), (63763/2251799813685248), by norm_num⟩
  | 5 => ⟨((294433126891899/4503599627370496), (647077484182817/2251799813685248)), (48647/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1410557196321095/18014398509481984), (338433364904649/9007199254740992)), (549109/18014398509481984), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20990127117/8589934592), (-30829249203/8589934592)), (1/8589934592), by norm_num⟩, -1, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-28311023105/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-21233267329/8589934592), (-31186361389/8589934592)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-167832453486623/2251799813685248), (178599121142815/4503599627370496)), (67089/2251799813685248), by norm_num⟩
  | 1 => ⟨((67522996523/274877906944), (-35927341779/274877906944)), (29/274877906944), by norm_num⟩
  | 2 => ⟨((-55636195311/137438953472), (29602664383/137438953472)), (13/68719476736), by norm_num⟩
  | 3 => ⟨((7640325983/17179869184), (-32521850869/137438953472)), (31/137438953472), by norm_num⟩
  | 4 => ⟨((-25181268043/68719476736), (26796678761/137438953472)), (27/137438953472), by norm_num⟩
  | 5 => ⟨((66394681239/274877906944), (-35326992699/274877906944)), (37/274877906944), by norm_num⟩
  | 6 => ⟨((-9117751589/68719476736), (38810668301/549755813888)), (21/274877906944), by norm_num⟩
  | 7 => ⟨((34343567797/549755813888), (-36546751823/1099511627776)), (21/549755813888), by norm_num⟩
  | 8 => ⟨((-14148849607/549755813888), (15056516499/1099511627776)), (9/549755813888), by norm_num⟩
  | 9 => ⟨((82901866927/8796093022208), (-22055032067/4398046511104)), (55/8796093022208), by norm_num⟩
  | 10 => ⟨((-1707693933/549755813888), (29075915107/17592186044416)), (19/8796093022208), by norm_num⟩
  | 11 => ⟨((65492719945/70368744177664), (-34847081063/70368744177664)), (47/70368744177664), by norm_num⟩
  | 12 => ⟨((-35975553475/140737488355328), (4785428935/35184372088832)), (53/281474976710656), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580755870480279/10141204801825835211973625643008), (3455327215837/10141204801825835211973625643008)), (153/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444536983141343/158456325028528675187087900672), (4086519142797/633825300114114700748351602688)), (91/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889043100432503/39614081257132168796771975168), (4596328632465/39614081257132168796771975168)), (205/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888774085183287/2475880078570760549798248448), (4882365741917/2475880078570760549798248448)), (217/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442609966618793/38685626227668133590597632), (4880978395603/154742504910672534362390528)), (109/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548849033756733/9671406556917033397649408), (4574443536883/9671406556917033397649408)), (51/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258171844471673/604462909807314587353088), (4001164775005/604462909807314587353088)), (89/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943394375784041/37778931862957161709568), (812391389003/9444732965739290427392)), (145/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296786170441815/4722366482869645213696), (2435966359945/2361183241434822606848)), (109/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810205515740399/295147905179352825856), (836872958541/73786976294838206464)), (299/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822176288542761/73786976294838206464), (8362846568593/73786976294838206464)), (187/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910596773931977/4611686018427387904), (9400117655011/9223372036854775808)), (421/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199054831456355/144115188075855872), (9390018358351/1152921504606846976)), (421/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193223139665491/144115188075855872), (2051228365487/36028797018963968)), (369/144115188075855872), by norm_num⟩
  | 4 => ⟨((744796683819971/18014398509481984), (3071171941131/9007199254740992)), (555/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486689410557637/9007199254740992), (15316216718317/9007199254740992)), (695/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111386069529637/2251799813685248), (7628427404455/1125899906842624)), (349/1125899906842624), by norm_num⟩
  | 1 => ⟨((276030287360369/281474976710656), (22737236647997/1125899906842624)), (527/562949953421312), by norm_num⟩
  | 0 => ⟨((541156472742419/562949953421312), (44884447909329/1125899906842624)), (2135/1125899906842624), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((541156472742419/562949953421312), (44884447909329/1125899906842624)), (8144382957076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2077248059428777/2251799813685248), (21573418173307/281474976710656)), (8551/2251799813685248), by norm_num⟩
  | 2 => ⟨((1902999139874717/2251799813685248), (39802242422613/281474976710656)), (267/35184372088832), by norm_num⟩
  | 3 => ⟨((1563201009633067/2251799813685248), (269095441379781/1125899906842624)), (8429/562949953421312), by norm_num⟩
  | 4 => ⟨((956545052158619/2251799813685248), (747224976387403/2251799813685248)), (62929/2251799813685248), by norm_num⟩
  | 5 => ⟨((316753975468469/4503599627370496), (1269658785241587/4503599627370496)), (23807/562949953421312), by norm_num⟩
  | 6 => ⟨((-167832453486623/2251799813685248), (178599121142815/4503599627370496)), (67089/2251799813685248), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21233267329/8589934592), (-31186361389/8589934592)), (1/8589934592), by norm_num⟩, -1, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 12 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨2,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile002Terms3

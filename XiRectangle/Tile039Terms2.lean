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
namespace Reinmann.XiRectangle.Tile039Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨39,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((17/32), (7191/512)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((17/32), (7191/512))
  have he : value ((17/32), (7191/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-24711795/16777216), (-1306636157/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((83424091367483/1125899906842624), (-977041233812349/4503599627370496)), (146320025/4503599627370496), by norm_num⟩
  | 1 => ⟨((-55146383/268435456), (1291720155/2147483648)), (195/2147483648), by norm_num⟩
  | 2 => ⟨((305796479/1073741824), (-111919023/134217728)), (137/1073741824), by norm_num⟩
  | 3 => ⟨((-70653989/268435456), (827481123/1073741824)), (129/1073741824), by norm_num⟩
  | 4 => ⟨((195894453/1073741824), (-1147132415/2147483648)), (181/2147483648), by norm_num⟩
  | 5 => ⟨((-434507801/4294967296), (1272210559/4294967296)), (203/4294967296), by norm_num⟩
  | 6 => ⟨((100392619/2147483648), (-146971527/1073741824)), (95/4294967296), by norm_num⟩
  | 7 => ⟨((-79527841/4294967296), (931409367/17179869184)), (153/17179869184), by norm_num⟩
  | 8 => ⟨((220497995/34359738368), (-1291207553/68719476736)), (107/34359738368), by norm_num⟩
  | 9 => ⟨((-33963903/17179869184), (1591105555/274877906944)), (133/137438953472), by norm_num⟩
  | 10 => ⟨((150668695/274877906944), (-110287033/68719476736)), (149/549755813888), by norm_num⟩
  | 11 => ⟨((-37976575/274877906944), (889543517/2199023255552)), (19/274877906944), by norm_num⟩
  | 12 => ⟨((280782463/8796093022208), (-411056387/4398046511104)), (71/4398046511104), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582057101215061/10141204801825835211973625643008), (-202178378915/1267650600228229401496703205376)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779695120831223/633825300114114700748351602688), (-958020767275/316912650057057350374175801344)), (92389/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890783769215443/39614081257132168796771975168), (-2155263571183/39614081257132168796771975168)), (103949/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472655921868687/618970019642690137449562112), (-2289623151805/2475880078570760549798248448)), (27615/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886144813842479/77371252455336267181195264), (-2289235775223/154742504910672534362390528)), (27619/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550583353360839/9671406556917033397649408), (-2145747022609/9671406556917033397649408)), (25897/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259689542166713/604462909807314587353088), (-1877117207927/604462909807314587353088)), (2833/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((1889255324490367/75557863725914323419136), (-381193023543/9444732965739290427392)), (147347/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298636374121271/4722366482869645213696), (-1143241722793/2361183241434822606848)), (55269/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622955505067109/590295810358705651712), (-3142818675067/590295810358705651712)), (76017/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825357542839115/73786976294838206464), (-3926879806065/73786976294838206464)), (95055/36893488147419103232), by norm_num⟩
  | 7 => ⟨((228096670599559/1152921504606846976), (-4415480820961/9223372036854775808)), (106983/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399004898414321/288230376151711744), (-2206329237467/576460752303423488)), (214081/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196357719694615/144115188075855872), (-964475722245/36028797018963968)), (187451/144115188075855872), by norm_num⟩
  | 4 => ⟨((373574431111093/9007199254740992), (-1445128108883/9007199254740992)), (70359/9007199254740992), by norm_num⟩
  | 3 => ⟨((1492574152764143/9007199254740992), (-7214552693183/9007199254740992)), (176125/4503599627370496), by norm_num⟩
  | 2 => ⟨((1117277145123205/2251799813685248), (-3598970923167/1125899906842624)), (705865/4503599627370496), by norm_num⟩
  | 1 => ⟨((1112973209655001/1125899906842624), (-10755458860873/1125899906842624)), (265555/562949953421312), by norm_num⟩
  | 0 => ⟨((1100076545761359/1125899906842624), (-42691081931133/2251799813685248)), (534541/562949953421312), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1100076545761359/1125899906842624), (-42691081931133/2251799813685248)), (2039112093211936773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1074440780271085/1125899906842624), (-83423859723581/2251799813685248)), (4259321/2251799813685248), by norm_num⟩
  | 2 => ⟨((127973532350805/140737488355328), (-159221963497611/2251799813685248)), (8444895/2251799813685248), by norm_num⟩
  | 3 => ⟨((1850616531937479/2251799813685248), (-289563176588391/2251799813685248)), (16552255/2251799813685248), by norm_num⟩
  | 4 => ⟨((741836528882343/1125899906842624), (-475948526488075/2251799813685248)), (3932943/281474976710656), by norm_num⟩
  | 5 => ⟨((876969049588291/2251799813685248), (-627188972431333/2251799813685248)), (27381049/1125899906842624), by norm_num⟩
  | 6 => ⟨((83424091367483/1125899906842624), (-977041233812349/4503599627370496)), (146320025/4503599627370496), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-24711795/16777216), (-1306636157/33554432)), (1/16777216), by norm_num⟩, -6, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-3156517/2097152), (-1335206685/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-498786300918505/4503599627370496), (-433208138608135/2251799813685248)), (88660937/2251799813685248), by norm_num⟩
  | 1 => ⟨((673851015/2147483648), (1170512275/2147483648)), (241/2147483648), by norm_num⟩
  | 2 => ⟨((-238645461/536870912), (-829077749/1073741824)), (43/268435456), by norm_num⟩
  | 3 => ⟨((225377835/536870912), (391492357/536870912)), (41/268435456), by norm_num⟩
  | 4 => ⟨((-319271745/1073741824), (-554590685/1073741824)), (117/1073741824), by norm_num⟩
  | 5 => ⟨((723651975/4294967296), (1257018983/4294967296)), (67/1073741824), by norm_num⟩
  | 6 => ⟨((-42713759/536870912), (-1187134319/8589934592)), (255/8589934592), by norm_num⟩
  | 7 => ⟨((553221449/17179869184), (480486399/8589934592)), (13/1073741824), by norm_num⟩
  | 8 => ⟨((-195924299/17179869184), (-1361320477/68719476736)), (297/68719476736), by norm_num⟩
  | 9 => ⟨((493418079/137438953472), (857091409/137438953472)), (189/137438953472), by norm_num⟩
  | 10 => ⟨((-279591737/274877906944), (-971329127/549755813888)), (27/68719476736), by norm_num⟩
  | 11 => ⟨((576104029/2199023255552), (500360481/1099511627776)), (225/2199023255552), by norm_num⟩
  | 12 => ⟨((-68009401/1099511627776), (-59067833/549755813888)), (215/8796093022208), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582015148218695/10141204801825835211973625643008), (-2726559280557/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779641811583357/633825300114114700748351602688), (-807443445611/158456325028528675187087900672)), (46259/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945361797014643/19807040628566084398385987584), (-908250206235/9903520314283042199192993792)), (104103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236319936783135/309485009821345068724781056), (-1929734651797/1237940039285380274899124224)), (110633/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772225145415681/154742504910672534362390528), (-3858800990177/154742504910672534362390528)), (27665/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775261297126983/4835703278458516698824704), (-1808457952207/4835703278458516698824704)), (25943/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629818035566707/302231454903657293676544), (-1582045729461/302231454903657293676544)), (22707/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((472291964783325/18889465931478580854784), (-5140317591839/75557863725914323419136)), (147649/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298570272391169/4722366482869645213696), (-1927036842499/2361183241434822606848)), (110783/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405715949734029/147573952589676412928), (-2648729627679/295147905179352825856)), (76201/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825241686943695/73786976294838206464), (-6618986441937/73786976294838206464)), (190615/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912320673416373/4611686018427387904), (-930307345791/1152921504606846976)), (214597/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595885478383621/1152921504606846976), (-7437583676945/1152921504606846976)), (214791/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196238013192781/144115188075855872), (-6502402807517/144115188075855872)), (94081/72057594037927936), by norm_num⟩
  | 4 => ⟨((747056731500195/18014398509481984), (-2435660578609/9007199254740992)), (282681/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492335619542571/9007199254740992), (-3039782105733/2251799813685248)), (177059/4503599627370496), by norm_num⟩
  | 2 => ⟨((1117026345313133/2251799813685248), (-12130384474073/2251799813685248)), (355271/2251799813685248), by norm_num⟩
  | 1 => ⟨((1112566493872067/1125899906842624), (-18123779244467/1125899906842624)), (535793/1125899906842624), by norm_num⟩
  | 0 => ⟨((549570975275721/562949953421312), (-35960745114959/1125899906842624)), (1083163/1125899906842624), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((549570975275721/562949953421312), (-35960745114959/1125899906842624)), (4131938938621139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1071871349254399/1125899906842624), (-17553053912129/281474976710656)), (1092017/562949953421312), by norm_num⟩
  | 2 => ⟨((1016056957793207/1125899906842624), (-133685884267215/1125899906842624)), (4430855/1125899906842624), by norm_num⟩
  | 3 => ⟨((901056852089681/1125899906842624), (-241286942192505/1125899906842624)), (4524687/562949953421312), by norm_num⟩
  | 4 => ⟨((334702959670155/562949953421312), (-772407036401729/2251799813685248)), (36726165/2251799813685248), by norm_num⟩
  | 5 => ⟨((531043879762763/2251799813685248), (-918472129120971/2251799813685248)), (17216667/562949953421312), by norm_num⟩
  | 6 => ⟨((-498786300918505/4503599627370496), (-433208138608135/2251799813685248)), (88660937/2251799813685248), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3156517/2097152), (-1335206685/33554432)), (1/16777216), by norm_num⟩, -6, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-25761583/16777216), (-1362143695/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-940714448931307/4503599627370496), (-117929345414573/2251799813685248)), (165842243/4503599627370496), by norm_num⟩
  | 1 => ⟨((40516473/67108864), (325069093/2147483648)), (115/1073741824), by norm_num⟩
  | 2 => ⟨((-936861355/1073741824), (-234892631/1073741824)), (21/134217728), by norm_num⟩
  | 3 => ⟨((902625867/1073741824), (226309009/1073741824)), (163/1073741824), by norm_num⟩
  | 4 => ⟨((-1304462157/2147483648), (-40882323/268435456)), (237/2147483648), by norm_num⟩
  | 5 => ⟨((1508152231/4294967296), (189064179/2147483648)), (69/1073741824), by norm_num⟩
  | 6 => ⟨((-1453040205/8589934592), (-364310509/8589934592)), (67/2147483648), by norm_num⟩
  | 7 => ⟨((149993799/2147483648), (18803443/1073741824)), (223/17179869184), by norm_num⟩
  | 8 => ⟨((-867075681/34359738368), (-108697881/17179869184)), (163/34359738368), by norm_num⟩
  | 9 => ⟨((1113853805/137438953472), (139634349/68719476736)), (211/137438953472), by norm_num⟩
  | 10 => ⟨((-160972579/68719476736), (-322876143/549755813888)), (123/274877906944), by norm_num⟩
  | 11 => ⟨((676757231/1099511627776), (169678561/1099511627776)), (65/549755813888), by norm_num⟩
  | 12 => ⟨((-1304053325/8796093022208), (-20434755/549755813888)), (253/8796093022208), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790987796942577/5070602400912917605986812821504), (-1886138484347/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889794931685359/316912650057057350374175801344), (-2234132839789/316912650057057350374175801344)), (2895/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((472666216088477/9903520314283042199192993792), (-1256521772367/9903520314283042199192993792)), (104247/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890496727450615/2475880078570760549798248448), (-5339377419075/2475880078570760549798248448)), (27699/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772161966439203/154742504910672534362390528), (-5338432132201/154742504910672534362390528)), (110833/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96903932891013/604462909807314587353088), (-2501887858069/4835703278458516698824704)), (103945/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629791712084727/302231454903657293676544), (-4377299298123/604462909807314587353088)), (90991/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944540744040591/37778931862957161709568), (-3555613956241/37778931862957161709568)), (147933/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649252388673119/2361183241434822606848), (-166617900691/147573952589676412928)), (55507/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811386289741329/295147905179352825856), (-7328509268779/590295810358705651712)), (152749/590295810358705651712), by norm_num⟩
  | 8 => ⟨((57035184958107/2305843009213693952), (-572288670753/4611686018427387904)), (47773/18446744073709551616), by norm_num⟩
  | 7 => ⟨((912254356145775/4611686018427387904), (-1286958877781/1152921504606846976)), (107597/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595749853915895/1152921504606846976), (-5144381980945/576460752303423488)), (215463/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299028995938257/36028797018963968), (-8994897009083/144115188075855872)), (188833/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493923716869077/36028797018963968), (-13476800095937/36028797018963968)), (17741/2251799813685248), by norm_num⟩
  | 3 => ⟨((1492086740121029/9007199254740992), (-16818790101969/9007199254740992)), (88971/2251799813685248), by norm_num⟩
  | 2 => ⟨((139594998015197/281474976710656), (-16777964234995/2251799813685248)), (357481/2251799813685248), by norm_num⟩
  | 1 => ⟨((556061734674667/562949953421312), (-12532422397843/562949953421312)), (270111/562949953421312), by norm_num⟩
  | 0 => ⟨((1098083299952657/1125899906842624), (-12430267603509/281474976710656)), (68531/70368744177664), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1098083299952657/1125899906842624), (-12430267603509/281474976710656)), (261425018578982331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((534379095991877/562949953421312), (-96985312363215/1125899906842624)), (1117829/562949953421312), by norm_num⟩
  | 2 => ⟨((503081097721655/562949953421312), (-184126220208983/1125899906842624)), (4629549/1125899906842624), by norm_num⟩
  | 3 => ⟨((869046966452607/1125899906842624), (-5142021307751/17592186044416)), (9788613/1125899906842624), by norm_num⟩
  | 4 => ⟨((1149201304078315/2251799813685248), (-254013799516069/562949953421312)), (41666557/2251799813685248), by norm_num⟩
  | 5 => ⟨((128028908266959/2251799813685248), (-259270817844163/562949953421312)), (40065189/1125899906842624), by norm_num⟩
  | 6 => ⟨((-940714448931307/4503599627370496), (-117929345414573/2251799813685248)), (165842243/4503599627370496), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-25761583/16777216), (-1362143695/33554432)), (1/16777216), by norm_num⟩, -6, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-52486957/33554432), (-86726495/2097152)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-820736284678411/4503599627370496), (463092957688561/4503599627370496)), (168154669/4503599627370496), by norm_num⟩
  | 1 => ⟨((1152328447/2147483648), (-650190809/2147483648)), (119/1073741824), by norm_num⟩
  | 2 => ⟨((-848240199/1073741824), (239305895/536870912)), (177/1073741824), by norm_num⟩
  | 3 => ⟨((416265251/536870912), (-469747737/1073741824)), (175/1073741824), by norm_num⟩
  | 4 => ⟨((-1225667631/2147483648), (345785887/1073741824)), (65/536870912), by norm_num⟩
  | 5 => ⟨((360890355/1073741824), (-203629089/1073741824)), (155/2147483648), by norm_num⟩
  | 6 => ⟨((-354206543/2147483648), (199857809/2147483648)), (77/2147483648), by norm_num⟩
  | 7 => ⟨((297982729/4294967296), (-672536141/17179869184)), (131/8589934592), by norm_num⟩
  | 8 => ⟨((-438695981/17179869184), (495060407/34359738368)), (195/34359738368), by norm_num⟩
  | 9 => ⟨((1148189819/137438953472), (-323927813/68719476736)), (257/137438953472), by norm_num⟩
  | 10 => ⟨((-1352309943/549755813888), (763028543/549755813888)), (305/549755813888), by norm_num⟩
  | 11 => ⟨((723962565/1099511627776), (-204244635/549755813888)), (165/1099511627776), by norm_num⟩
  | 12 => ⟨((-177638633/1099511627776), (200461955/2199023255552)), (41/1099511627776), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98871136168565/633825300114114700748351602688), (3423109362455/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889773714813357/316912650057057350374175801344), (1013621069831/158456325028528675187087900672)), (92599/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890617243200293/39614081257132168796771975168), (4560642602841/39614081257132168796771975168)), (104199/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890446277169395/2475880078570760549798248448), (605613355699/309485009821345068724781056)), (110741/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443027920423787/38685626227668133590597632), (1211008465773/38685626227668133590597632)), (110775/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775207980058747/4835703278458516698824704), (4540354218225/9671406556917033397649408)), (103887/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259542504523355/604462909807314587353088), (992970607449/151115727451828646838272)), (11367/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((944507661481785/37778931862957161709568), (806571237753/9444732965739290427392)), (73919/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298455441474303/4722366482869645213696), (4837905798279/4722366482869645213696)), (110937/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202838151283859/73786976294838206464), (3324823948761/295147905179352825856)), (19079/73786976294838206464), by norm_num⟩
  | 8 => ⟨((912521203989957/36893488147419103232), (4154175567275/36893488147419103232)), (190933/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824415725478051/9223372036854775808), (9341795718887/9223372036854775808)), (107497/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398914517264267/288230376151711744), (4667710949441/576460752303423488)), (215239/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299009255561377/36028797018963968), (1020165506751/18014398509481984)), (188609/144115188075855872), by norm_num⟩
  | 4 => ⟨((46681499068959/1125899906842624), (764227936827/2251799813685248)), (35433/4503599627370496), by norm_num⟩
  | 3 => ⟨((372986690771761/2251799813685248), (1907433489637/1125899906842624)), (177647/4503599627370496), by norm_num⟩
  | 2 => ⟨((1116627044511215/2251799813685248), (15221837029653/2251799813685248)), (356743/2251799813685248), by norm_num⟩
  | 1 => ⟨((1111941576391217/1125899906842624), (11369348868721/562949953421312)), (538743/1125899906842624), by norm_num⟩
  | 0 => ⟨((548894558469181/562949953421312), (45101286423833/1125899906842624)), (1092043/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((548894558469181/562949953421312), (45101286423833/1125899906842624)), (4165813450339889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1068573513435233/1125899906842624), (43975224702567/562949953421312)), (1108523/562949953421312), by norm_num⟩
  | 2 => ⟨((503647822143073/562949953421312), (166944717124287/1125899906842624)), (4554699/1125899906842624), by norm_num⟩
  | 3 => ⟨((876431350979819/1125899906842624), (74679234527809/281474976710656)), (9500511/1125899906842624), by norm_num⟩
  | 4 => ⟨((1205968842771481/2251799813685248), (930117812563173/2251799813685248)), (19832153/1125899906842624), by norm_num⟩
  | 5 => ⟨((130837941478453/1125899906842624), (498131803387181/1125899906842624)), (75252157/2251799813685248), by norm_num⟩
  | 6 => ⟨((-820736284678411/4503599627370496), (463092957688561/4503599627370496)), (168154669/4503599627370496), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-52486957/33554432), (-86726495/2097152)), (1/16777216), by norm_num⟩, -7, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-13350325/8388608), (-1411796879/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-302944309558553/4503599627370496), (216388605042997/1125899906842624)), (158565405/4503599627370496), by norm_num⟩
  | 1 => ⟨((27046801/134217728), (-618212059/1073741824)), (57/536870912), by norm_num⟩
  | 2 => ⟨((-324099899/1073741824), (925998909/1073741824)), (173/1073741824), by norm_num⟩
  | 3 => ⟨((161819421/536870912), (-462340803/536870912)), (175/1073741824), by norm_num⟩
  | 4 => ⟨((-242383831/1073741824), (1385049265/2147483648)), (33/268435456), by norm_num⟩
  | 5 => ⟨((145223413/1073741824), (-829847357/2147483648)), (5/67108864), by norm_num⟩
  | 6 => ⟨((-72508411/1073741824), (828666837/4294967296)), (81/2147483648), by norm_num⟩
  | 7 => ⟨((496493227/17179869184), (-709275425/8589934592)), (35/2147483648), by norm_num⟩
  | 8 => ⟨((-92960049/8589934592), (1062399641/34359738368)), (211/34359738368), by norm_num⟩
  | 9 => ⟨((247540817/68719476736), (-707258865/68719476736)), (283/137438953472), by norm_num⟩
  | 10 => ⟨((-148313203/137438953472), (847503283/274877906944)), (171/274877906944), by norm_num⟩
  | 11 => ⟨((80783027/274877906944), (-923233795/1099511627776)), (47/274877906944), by norm_num⟩
  | 12 => ⟨((-80668107/1099511627776), (921920425/4398046511104)), (95/2199023255552), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790951341561217/5070602400912917605986812821504), (2484694490095/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779509544312337/633825300114114700748351602688), (2942851370189/633825300114114700748351602688)), (46245/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890574869896209/39614081257132168796771975168), (1655117233249/19807040628566084398385987584)), (104069/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472600392443903/618970019642690137449562112), (1758276046743/1237940039285380274899124224)), (110595/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772067327661955/154742504910672534362390528), (3515908620857/154742504910672534362390528)), (27655/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550374753481579/9671406556917033397649408), (3295480729907/9671406556917033397649408)), (103731/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629753411894985/302231454903657293676544), (2882862134907/604462909807314587353088)), (90791/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888958044614857/75557863725914323419136), (4683369608795/75557863725914323419136)), (147583/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649206548640785/2361183241434822606848), (3511406225407/4722366482869645213696)), (55365/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622647984894939/590295810358705651712), (150823823683/18446744073709551616)), (76161/295147905179352825856), by norm_num⟩
  | 8 => ⟨((228121546464965/9223372036854775808), (6030221831089/73786976294838206464)), (190505/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456084747177589/2305843009213693952), (6780245391841/9223372036854775808)), (53615/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199447987059169/144115188075855872), (6775554357561/1152921504606846976)), (214637/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597987500670285/72057594037927936), (5923334955045/144115188075855872)), (188007/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493720687562145/36028797018963968), (138663406023/562949953421312)), (282409/36028797018963968), by norm_num⟩
  | 3 => ⟨((93240480885507/562949953421312), (11074632690121/9007199254740992)), (22107/562949953421312), by norm_num⟩
  | 2 => ⟨((1116542975479685/2251799813685248), (5523499506251/1125899906842624)), (177381/1125899906842624), by norm_num⟩
  | 1 => ⟨((277963197942145/281474976710656), (16501505487499/1125899906842624)), (267387/562949953421312), by norm_num⟩
  | 0 => ⟨((1097759739683897/1125899906842624), (32727586844099/1125899906842624)), (270025/281474976710656), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1097759739683897/1125899906842624), (32727586844099/1125899906842624)), (1030063630224132449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1069371570077333/1125899906842624), (63819220511725/1125899906842624)), (2169003/1125899906842624), by norm_num⟩
  | 2 => ⟨((63253994374731/70368744177664), (121230066056439/1125899906842624)), (2183049/562949953421312), by norm_num⟩
  | 3 => ⟨((448342087455579/562949953421312), (54486448536169/281474976710656)), (8789543/1125899906842624), by norm_num⟩
  | 4 => ⟨((20998262582915/35184372088832), (694301663621303/2251799813685248)), (17403125/1125899906842624), by norm_num⟩
  | 5 => ⟨((146991565688313/562949953421312), (25897734880109/70368744177664)), (15752237/562949953421312), by norm_num⟩
  | 6 => ⟨((-302944309558553/4503599627370496), (216388605042997/1125899906842624)), (158565405/4503599627370496), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13350325/8388608), (-1411796879/33554432)), (1/16777216), by norm_num⟩, -7, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-3391939/2097152), (-717395095/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((305211625015897/4503599627370496), (839834069708905/4503599627370496)), (125894947/4503599627370496), by norm_num⟩
  | 1 => ⟨((-55386045/268435456), (-1219221911/2147483648)), (185/2147483648), by norm_num⟩
  | 2 => ⟨((168624057/536870912), (231996779/268435456)), (143/1073741824), by norm_num⟩
  | 3 => ⟨((-171126575/536870912), (-941759199/1073741824)), (147/1073741824), by norm_num⟩
  | 4 => ⟨((520998697/2147483648), (716801753/1073741824)), (113/1073741824), by norm_num⟩
  | 5 => ⟨((-317238445/2147483648), (-109115951/268435456)), (139/2147483648), by norm_num⟩
  | 6 => ⟨((321946521/4294967296), (885882563/4294967296)), (143/4294967296), by norm_num⟩
  | 7 => ⟨((-280049545/8589934592), (-1541193909/17179869184)), (251/17179869184), by norm_num⟩
  | 8 => ⟨((213154281/17179869184), (1173049859/34359738368)), (193/34359738368), by norm_num⟩
  | 9 => ⟨((-2253309/536870912), (-49602453/4294967296)), (33/17179869184), by norm_num⟩
  | 10 => ⟨((175622395/137438953472), (966500999/274877906944)), (163/274877906944), by norm_num⟩
  | 11 => ⟨((-97215695/274877906944), (-267503089/274877906944)), (91/549755813888), by norm_num⟩
  | 12 => ⟨((98658455/1099511627776), (1085892209/4398046511104)), (93/2199023255552), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581868919695439/10141204801825835211973625643008), (99504659911/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779472284193499/633825300114114700748351602688), (942779595857/316912650057057350374175801344)), (46193/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890533116559951/39614081257132168796771975168), (2120949404165/39614081257132168796771975168)), (51973/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945178707805429/1237940039285380274899124224), (2253136665299/2475880078570760549798248448)), (13807/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1772023408222223/154742504910672534362390528), (2252718164555/154742504910672534362390528)), (110471/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550333828283789/9671406556917033397649408), (2111478711485/9671406556917033397649408)), (3237/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1259471263385733/604462909807314587353088), (1847099405157/604462909807314587353088)), (22663/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944450362909919/37778931862957161709568), (3000703370317/75557863725914323419136)), (147341/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298370516406725/4722366482869645213696), (140612420207/295147905179352825856)), (110533/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622590099021963/590295810358705651712), (3092289337127/590295810358705651712)), (76013/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824901007696557/73786976294838206464), (1931793254837/36893488147419103232)), (95049/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912130034245653/4611686018427387904), (4344095112199/9223372036854775808)), (3343/144115188075855872), by norm_num⟩
  | 6 => ⟨((398876669845373/288230376151711744), (1085261794233/288230376151711744)), (214065/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298977337325697/36028797018963968), (3794989694287/144115188075855872)), (187435/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493626027596295/36028797018963968), (5685637221623/36028797018963968)), (4397/562949953421312), by norm_num⟩
  | 3 => ⟨((1491736033463803/9007199254740992), (7095076874789/9007199254740992)), (22013/562949953421312), by norm_num⟩
  | 2 => ⟨((2232882552780487/4503599627370496), (442321793221/140737488355328)), (352881/2251799813685248), by norm_num⟩
  | 1 => ⟨((2223450051415795/2251799813685248), (10570994523227/1125899906842624)), (8297/17592186044416), by norm_num⟩
  | 0 => ⟨((2195205221549655/2251799813685248), (41927251887379/2251799813685248)), (2137561/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2195205221549655/2251799813685248), (41927251887379/2251799813685248)), (8154148110396575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1069626181020143/1125899906842624), (20436746132813/562949953421312)), (1061819/562949953421312), by norm_num⟩
  | 2 => ⟨((2029362499829097/2251799813685248), (155322359194933/2251799813685248)), (8378363/2251799813685248), by norm_num⟩
  | 3 => ⟨((113636520206093/140737488355328), (139979304207919/1125899906842624)), (4064323/562949953421312), by norm_num⟩
  | 4 => ⟨((716630623966677/1125899906842624), (452097340003605/2251799813685248)), (7573969/562949953421312), by norm_num⟩
  | 5 => ⟨((410748279830817/1125899906842624), (575516166031169/2251799813685248)), (50731501/2251799813685248), by norm_num⟩
  | 6 => ⟨((305211625015897/4503599627370496), (839834069708905/4503599627370496)), (125894947/4503599627370496), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-3391939/2097152), (-717395095/16777216)), (1/16777216), by norm_num⟩, -7, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile039Terms2

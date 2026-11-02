/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile020Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨20,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (5781/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (5781/640))
  have he : value ((3/4), (5781/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-372130559/134217728), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-279097919/134217728), (-3361385565/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((560748444255559/4503599627370496), (12434411482697/1125899906842624)), (9444843/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1482701123/4294967296), (-65756815/2147483648)), (13/4294967296), by norm_num⟩
  | 2 => ⟨((1027730103/2147483648), (364633207/8589934592)), (19/4294967296), by norm_num⟩
  | 3 => ⟨((-3799297191/8589934592), (-336992639/8589934592)), (73/17179869184), by norm_num⟩
  | 4 => ⟨((329184017/1073741824), (467170995/17179869184)), (53/17179869184), by norm_num⟩
  | 5 => ⟨((-1460307029/8589934592), (-518109213/34359738368)), (61/34359738368), by norm_num⟩
  | 6 => ⟨((2699220533/34359738368), (478834587/68719476736)), (29/34359738368), by norm_num⟩
  | 7 => ⟨((-4276473377/137438953472), (-11853673/4294967296)), (3/8589934592), by norm_num⟩
  | 8 => ⟨((370528183/34359738368), (525845761/549755813888)), (69/549755813888), by norm_num⟩
  | 9 => ⟨((-7305402749/2199023255552), (-647979567/2199023255552)), (11/274877906944), by norm_num⟩
  | 10 => ⟨((4050975455/4398046511104), (44914521/549755813888)), (25/2199023255552), by norm_num⟩
  | 11 => ⟨((-4084250495/17592186044416), (-90566905/4398046511104)), (13/4398046511104), by norm_num⟩
  | 12 => ⟨((1887324477/35184372088832), (669612745/140737488355328)), (49/70368744177664), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98829191395547/633825300114114700748351602688), (57619176231/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778761641694765/633825300114114700748351602688), (68188756719/316912650057057350374175801344)), (1441/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889733882836581/39614081257132168796771975168), (76698437761/19807040628566084398385987584)), (12969/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944754264761227/1237940039285380274899124224), (162949617877/2475880078570760549798248448)), (13779/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771174859190791/154742504910672534362390528), (81455374985/77371252455336267181195264)), (13779/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549538671553019/9671406556917033397649408), (76343772033/4835703278458516698824704)), (12919/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78673491192409/37778931862957161709568), (66780165895/302231454903657293676544)), (1413/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887771364429063/75557863725914323419136), (216958190641/75557863725914323419136)), (18369/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648762040909561/2361183241434822606848), (162650994373/4722366482869645213696)), (13777/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202678400480199/73786976294838206464), (223535247015/590295810358705651712)), (18943/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455862204054033/18446744073709551616), (8726698629/2305843009213693952)), (23679/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822628314141817/9223372036854775808), (313934851331/9223372036854775808)), (1665/576460752303423488), by norm_num⟩
  | 6 => ⟨((199234671719639/144115188075855872), (156826113605/576460752303423488)), (26641/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194486458115555/144115188075855872), (267703213/140737488355328)), (1457/9007199254740992), by norm_num⟩
  | 4 => ⟨((1491497184340015/36028797018963968), (102639443841/9007199254740992)), (34971/36028797018963968), by norm_num⟩
  | 3 => ⟨((744542286483549/4503599627370496), (512089016343/9007199254740992)), (21859/4503599627370496), by norm_num⟩
  | 2 => ⟨((1113804166137245/2251799813685248), (1020861117413/4503599627370496)), (87447/4503599627370496), by norm_num⟩
  | 1 => ⟨((69237818490765/70368744177664), (1523026252231/2251799813685248)), (131205/2251799813685248), by norm_num⟩
  | 0 => ⟨((1089904855227327/1125899906842624), (3013151497353/2251799813685248)), (262553/2251799813685248), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1089904855227327/1125899906842624), (3013151497353/2251799813685248)), (1001560219771575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2110117100922107/2251799813685248), (5833641918863/2251799813685248)), (254511/1125899906842624), by norm_num⟩
  | 2 => ⟨((1977333918035509/2251799813685248), (10933181092597/2251799813685248)), (956627/2251799813685248), by norm_num⟩
  | 3 => ⟨((1736268857117575/2251799813685248), (2400141175409/281474976710656)), (1689343/2251799813685248), by norm_num⟩
  | 4 => ⟨((83662545247887/140737488355328), (1850648690093/140737488355328)), (2633975/2251799813685248), by norm_num⟩
  | 5 => ⟨((795352727525437/2251799813685248), (17602130784877/1125899906842624)), (200053/140737488355328), by norm_num⟩
  | 6 => ⟨((560748444255559/4503599627370496), (12434411482697/1125899906842624)), (9444843/9007199254740992), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-279097919/134217728), (-3361385565/134217728)), (1/134217728), by norm_num⟩, -4, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-190133729/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-570401187/268435456), (-429360581/16777216)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((964429730560801/9007199254740992), (-476797377664387/9007199254740992)), (6160287/4503599627370496), by norm_num⟩
  | 1 => ⟨((-5211706509/17179869184), (1288288777/8589934592)), (69/17179869184), by norm_num⟩
  | 2 => ⟨((3691469107/8589934592), (-1824998477/8589934592)), (51/8589934592), by norm_num⟩
  | 3 => ⟨((-3486239845/8589934592), (1723536679/8589934592)), (25/4294967296), by norm_num⟩
  | 4 => ⟨((4938630625/17179869184), (-2441573559/17179869184)), (73/17179869184), by norm_num⟩
  | 5 => ⟨((-1399219419/8589934592), (2766999515/34359738368)), (85/34359738368), by norm_num⟩
  | 6 => ⟨((5285716173/68719476736), (-1306583325/34359738368)), (83/68719476736), by norm_num⟩
  | 7 => ⟨((-1069682971/34359738368), (2115331035/137438953472)), (69/137438953472), by norm_num⟩
  | 8 => ⟨((757660017/68719476736), (-1498296029/274877906944)), (51/274877906944), by norm_num⟩
  | 9 => ⟨((-954049987/274877906944), (943331623/549755813888)), (33/549755813888), by norm_num⟩
  | 10 => ⟨((4324843447/4398046511104), (-1069063897/2199023255552)), (77/4398046511104), by norm_num⟩
  | 11 => ⟨((-2227855303/8796093022208), (1101413127/8796093022208)), (41/8796093022208), by norm_num⟩
  | 12 => ⟨((1051998229/17592186044416), (-2080358913/70368744177664)), (5/4398046511104), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572315/10141204801825835211973625643008), (-598085909909/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889345646848323/316912650057057350374175801344), (-353872416493/316912650057057350374175801344)), (5767/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118103421328675/2475880078570760549798248448), (-796065406503/39614081257132168796771975168)), (12977/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889424440582923/2475880078570760549798248448), (-845636200105/2475880078570760549798248448)), (13789/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885545384561253/77371252455336267181195264), (-845430072589/154742504910672534362390528)), (13789/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549459835922557/9671406556917033397649408), (-198092938153/2417851639229258349412352)), (101/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((629353438359647/302231454903657293676544), (-693106421913/604462909807314587353088)), (11313/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471914816474175/18889465931478580854784), (-1125887737487/75557863725914323419136)), (18385/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648720003007431/2361183241434822606848), (-844057047099/4722366482869645213696)), (6895/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810655798275143/295147905179352825856), (-1159995774829/590295810358705651712)), (18963/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455826075643193/18446744073709551616), (-1449121269595/73786976294838206464)), (23707/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822465730165063/9223372036854775808), (-814530663305/4611686018427387904)), (13337/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593714782269711/1152921504606846976), (-1627562534323/1152921504606846976)), (3335/144115188075855872), by norm_num⟩
  | 5 => ⟨((597172091159761/72057594037927936), (-1422432909797/144115188075855872)), (23351/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491283754667957/36028797018963968), (-532571331961/9007199254740992)), (35039/36028797018963968), by norm_num⟩
  | 3 => ⟨((744408879531111/4503599627370496), (-1328489941253/4503599627370496)), (43819/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227074628590809/4503599627370496), (-5296370508501/4503599627370496)), (87701/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214809462417473/2251799813685248), (-3950363027817/1125899906842624)), (1029/17592186044416), by norm_num⟩
  | 0 => ⟨((2178207651789659/2251799813685248), (-15626991256139/2251799813685248)), (264077/2251799813685248), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2178207651789659/2251799813685248), (-15626991256139/2251799813685248)), (1007373818404387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2106912143177953/2251799813685248), (-30232555950757/2251799813685248)), (514559/2251799813685248), by norm_num⟩
  | 2 => ⟨((492735271654543/562949953421312), (-28287301057953/1125899906842624)), (976719/2251799813685248), by norm_num⟩
  | 3 => ⟨((1723691447936847/2251799813685248), (-24759129806221/562949953421312)), (219859/281474976710656), by norm_num⟩
  | 4 => ⟨((657541571314023/1125899906842624), (-18952439753291/281474976710656)), (2847453/2251799813685248), by norm_num⟩
  | 5 => ⟨((1515636677298745/4503599627370496), (-22136989158407/281474976710656)), (7418719/4503599627370496), by norm_num⟩
  | 6 => ⟨((964429730560801/9007199254740992), (-476797377664387/9007199254740992)), (6160287/4503599627370496), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-570401187/268435456), (-429360581/16777216)), (1/134217728), by norm_num⟩, -4, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-6207026087/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-72738587/33554432), (-7008362853/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6207026087/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((144505109502923/2251799813685248), (-426687854699369/4503599627370496)), (16307855/9007199254740992), by norm_num⟩
  | 1 => ⟨((-3186595821/17179869184), (2352307367/8589934592)), (93/17179869184), by norm_num⟩
  | 2 => ⟨((2302611641/8589934592), (-1699760695/4294967296)), (69/8589934592), by norm_num⟩
  | 3 => ⟨((-1109233943/4294967296), (3275293539/8589934592)), (17/2147483648), by norm_num⟩
  | 4 => ⟨((1603049231/8589934592), (-1183351993/4294967296)), (25/4294967296), by norm_num⟩
  | 5 => ⟨((-926681645/8589934592), (171016359/1073741824)), (15/4294967296), by norm_num⟩
  | 6 => ⟨((111602269/2147483648), (-1318135611/17179869184)), (15/8589934592), by norm_num⟩
  | 7 => ⟨((-2949230139/137438953472), (4354173649/137438953472)), (101/137438953472), by norm_num⟩
  | 8 => ⟨((2131092875/274877906944), (-98321723/8589934592)), (75/274877906944), by norm_num⟩
  | 9 => ⟨((-2737622515/1099511627776), (4041761157/1099511627776)), (49/549755813888), by norm_num⟩
  | 10 => ⟨((3165098721/4398046511104), (-584109615/549755813888)), (29/1099511627776), by norm_num⟩
  | 11 => ⟨((-3326658893/17592186044416), (2455700269/8796093022208)), (125/17592186044416), by norm_num⟩
  | 12 => ⟨((1602546819/35184372088832), (-4731924469/70368744177664)), (123/70368744177664), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790575996579415/5070602400912917605986812821504), (-635312955821/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889312136952227/316912650057057350374175801344), (-751744256191/316912650057057350374175801344)), (11545/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889579305017003/39614081257132168796771975168), (-422776067945/9903520314283042199192993792)), (3247/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889344237658375/2475880078570760549798248448), (-1796400962695/2475880078570760549798248448)), (6901/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771010507853061/154742504910672534362390528), (-224494266431/19342813113834066795298816)), (13803/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549384529039409/9671406556917033397649408), (-420808096715/2417851639229258349412352)), (6471/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314660230326999/151115727451828646838272), (-736176946163/302231454903657293676544)), (5663/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887551972428059/75557863725914323419136), (-2391685839361/75557863725914323419136)), (18407/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297359434594407/4722366482869645213696), (-112061665567/295147905179352825856)), (13809/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810600323210241/295147905179352825856), (-1232046743927/295147905179352825856)), (18991/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911582684324639/36893488147419103232), (-3078223277633/73786976294838206464)), (23745/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455577272876687/2305843009213693952), (-1730199689491/4611686018427387904)), (13361/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796778861019719/576460752303423488), (-3457149917179/1152921504606846976)), (26733/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597103140807009/72057594037927936), (-1510677188879/72057594037927936)), (23405/144115188075855872), by norm_num⟩
  | 4 => ⟨((745537980378441/18014398509481984), (-4524737568853/36028797018963968)), (8783/9007199254740992), by norm_num⟩
  | 3 => ⟨((1488556373764005/9007199254740992), (-5643179041099/9007199254740992)), (5495/1125899906842624), by norm_num⟩
  | 2 => ⟨((2226546957517851/4503599627370496), (-11248215488007/4503599627370496)), (88055/4503599627370496), by norm_num⟩
  | 1 => ⟨((138375362695951/140737488355328), (-16777267702353/2251799813685248)), (33105/562949953421312), by norm_num⟩
  | 0 => ⟨((2176552310756677/2251799813685248), (-4147014254567/281474976710656)), (133101/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2176552310756677/2251799813685248), (-4147014254567/281474976710656)), (507740025046920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((525832633759567/562949953421312), (-32067480967579/1125899906842624)), (261229/1125899906842624), by norm_num⟩
  | 2 => ⟨((1962823701920665/2251799813685248), (-119812625422475/2251799813685248)), (1005783/2251799813685248), by norm_num⟩
  | 3 => ⟨((1704557304021267/2251799813685248), (-6527308165321/70368744177664)), (930225/1125899906842624), by norm_num⟩
  | 4 => ⟨((635466637702185/1125899906842624), (-316224793800631/2251799813685248)), (3161777/2251799813685248), by norm_num⟩
  | 5 => ⟨((1345833018642953/4503599627370496), (-178479725642825/1125899906842624)), (4457093/2251799813685248), by norm_num⟩
  | 6 => ⟨((144505109502923/2251799813685248), (-426687854699369/4503599627370496)), (16307855/9007199254740992), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-72738587/33554432), (-7008362853/268435456)), (1/134217728), by norm_num⟩, -4, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-197597955/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-592793865/268435456), (-892432639/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((105673834450041/9007199254740992), (-492045185570795/4503599627370496)), (38559295/18014398509481984), by norm_num⟩
  | 1 => ⟨((-593471827/17179869184), (5526722045/17179869184)), (55/8589934592), by norm_num⟩
  | 2 => ⟨((436860395/8589934592), (-2034136977/4294967296)), (41/4294967296), by norm_num⟩
  | 3 => ⟨((-53596199/1073741824), (499116017/1073741824)), (41/4294967296), by norm_num⟩
  | 4 => ⟨((315621475/8589934592), (-2939233311/8589934592)), (61/8589934592), by norm_num⟩
  | 5 => ⟨((-743462539/34359738368), (6923514503/34359738368)), (73/17179869184), by norm_num⟩
  | 6 => ⟨((45605835/4294967296), (-3397644329/34359738368)), (145/68719476736), by norm_num⟩
  | 7 => ⟨((-306933939/68719476736), (89322825/2147483648)), (31/34359738368), by norm_num⟩
  | 8 => ⟨((451874127/274877906944), (-2104044861/137438953472)), (93/274877906944), by norm_num⟩
  | 9 => ⟨((-591340353/1099511627776), (344179539/68719476736)), (31/274877906944), by norm_num⟩
  | 10 => ⟨((348233117/2199023255552), (-6485860163/4398046511104)), (37/1099511627776), by norm_num⟩
  | 11 => ⟨((-745709937/17592186044416), (3472221723/8796093022208)), (5/549755813888), by norm_num⟩
  | 12 => ⟨((731899135/70368744177664), (-3407914995/35184372088832)), (159/70368744177664), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790549585858251/5070602400912917605986812821504), (-1906794181247/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778560258760891/633825300114114700748351602688), (-564023453547/158456325028528675187087900672)), (5777/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944753608300003/19807040628566084398385987584), (-1268807115753/19807040628566084398385987584)), (1625/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889267549112907/2475880078570760549798248448), (-673901880269/618970019642690137449562112)), (6907/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770933712986725/154742504910672534362390528), (-84216380901/4835703278458516698824704)), (13817/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549312420970925/9671406556917033397649408), (-1262882798079/4835703278458516698824704)), (12955/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258577713962031/604462909807314587353088), (-276164912697/75557863725914323419136)), (5669/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887449049219321/75557863725914323419136), (-3588783875265/75557863725914323419136)), (18429/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40540064297731/147573952589676412928), (-672599604039/1180591620717411303424)), (6913/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810546976629399/295147905179352825856), (-1848682919547/295147905179352825856)), (19017/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911515776658749/36893488147419103232), (-2309405483017/36893488147419103232)), (23781/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911078966561885/4611686018427387904), (-5192182545811/9223372036854775808)), (1673/576460752303423488), by norm_num⟩
  | 6 => ⟨((398351448774575/288230376151711744), (-648401475595/144115188075855872)), (837/36028797018963968), by norm_num⟩
  | 5 => ⟨((597036241561725/72057594037927936), (-1133305934623/36028797018963968)), (733/4503599627370496), by norm_num⟩
  | 4 => ⟨((372718385926083/9007199254740992), (-3394338073775/18014398509481984)), (17611/18014398509481984), by norm_num⟩
  | 3 => ⟨((744150178015869/4503599627370496), (-2116586742619/2251799813685248)), (22047/4503599627370496), by norm_num⟩
  | 2 => ⟨((2226025982221269/4503599627370496), (-16874322508415/4503599627370496)), (88389/4503599627370496), by norm_num⟩
  | 1 => ⟨((2213202162975413/2251799813685248), (-25165985711871/2251799813685248)), (133091/2251799813685248), by norm_num⟩
  | 0 => ⟨((543714337751697/562949953421312), (-24876278395593/1125899906842624)), (134109/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((543714337751697/562949953421312), (-24876278395593/1125899906842624)), (511585239890670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((524861174557967/562949953421312), (-1501642058875/35184372088832)), (66245/281474976710656), by norm_num⟩
  | 2 => ⟨((488324031463501/562949953421312), (-179205384207939/2251799813685248)), (258361/562949953421312), by norm_num⟩
  | 3 => ⟨((1680101029653945/2251799813685248), (-155449512242687/1125899906842624)), (1957387/2251799813685248), by norm_num⟩
  | 4 => ⟨((302655818897689/562949953421312), (-463932688848953/2251799813685248)), (865343/562949953421312), by norm_num⟩
  | 5 => ⟨((1110556247513969/4503599627370496), (-997686753528531/4503599627370496)), (10296229/4503599627370496), by norm_num⟩
  | 6 => ⟨((105673834450041/9007199254740992), (-492045185570795/4503599627370496)), (38559295/18014398509481984), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-592793865/268435456), (-892432639/33554432)), (1/134217728), by norm_num⟩, -4, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-6433286071/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-603120569/268435456), (-7263833355/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6433286071/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-166124523249805/4503599627370496), (-892562325406599/9007199254740992)), (10435197/4503599627370496), by norm_num⟩
  | 1 => ⟨((474609943/4294967296), (2550008549/8589934592)), (121/17179869184), by norm_num⟩
  | 2 => ⟨((-355451081/2147483648), (-1909785727/4294967296)), (23/2147483648), by norm_num⟩
  | 3 => ⟨((354945425/2147483648), (3814137825/8589934592)), (93/8589934592), by norm_num⟩
  | 4 => ⟨((-1063321465/8589934592), (-5713067889/17179869184)), (141/17179869184), by norm_num⟩
  | 5 => ⟨((318542643/4294967296), (3422964371/17179869184)), (43/8589934592), by norm_num⟩
  | 6 => ⟨((-79522373/2147483648), (-1709047473/17179869184)), (11/4294967296), by norm_num⟩
  | 7 => ⟨((2178082187/137438953472), (5851255625/137438953472)), (153/137438953472), by norm_num⟩
  | 8 => ⟨((-1631237775/274877906944), (-4382198829/274877906944)), (29/68719476736), by norm_num⟩
  | 9 => ⟨((2171889621/1099511627776), (364663735/68719476736)), (157/1099511627776), by norm_num⟩
  | 10 => ⟨((-650639983/1099511627776), (-27310873/17179869184)), (3/68719476736), by norm_num⟩
  | 11 => ⟨((44298709/274877906944), (238010367/549755813888)), (107/8796093022208), by norm_num⟩
  | 12 => ⟨((-176942763/4398046511104), (-950687117/8796093022208)), (109/35184372088832), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49407783133909/316912650057057350374175801344), (-313790467699/1267650600228229401496703205376)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778498970871453/633825300114114700748351602688), (-1484996720217/316912650057057350374175801344)), (5781/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889438169190409/39614081257132168796771975168), (-835145371279/9903520314283042199192993792)), (6505/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944597027817833/1237940039285380274899124224), (-1774276813275/1237940039285380274899124224)), (6913/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770860072723315/154742504910672534362390528), (-886909472489/38685626227668133590597632)), (13829/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549243227380789/9671406556917033397649408), (-831234451251/2417851639229258349412352)), (1621/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629258506929625/302231454903657293676544), (-1454174073685/302231454903657293676544)), (11351/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943675059936633/37778931862957161709568), (-2362121517303/37778931862957161709568)), (9225/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162150950697297/590295810358705651712), (-1770794007115/2361183241434822606848)), (13843/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620991168076263/590295810358705651712), (-4867093978469/590295810358705651712)), (9521/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911451226063307/36893488147419103232), (-6079985145829/73786976294838206464)), (23815/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822011843666473/9223372036854775808), (-3417324156409/4611686018427387904)), (13405/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398314661149415/288230376151711744), (-6827984426575/1152921504606846976)), (26833/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74621408488863/9007199254740992), (-5966996145523/144115188075855872)), (1469/9007199254740992), by norm_num⟩
  | 4 => ⟨((1490676249162735/36028797018963968), (-8935530365955/36028797018963968)), (17653/18014398509481984), by norm_num⟩
  | 3 => ⟨((372012400306305/2251799813685248), (-11143263551957/9007199254740992)), (44221/9007199254740992), by norm_num⟩
  | 2 => ⟨((556378032788793/1125899906842624), (-1388014257927/281474976710656)), (88707/4503599627370496), by norm_num⟩
  | 1 => ⟨((2212400771502505/2251799813685248), (-16558558305897/1125899906842624)), (4179/70368744177664), by norm_num⟩
  | 0 => ⟨((2173133535007441/2251799813685248), (-65456458294917/2251799813685248)), (270135/2251799813685248), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2173133535007441/2251799813685248), (-65456458294917/2251799813685248)), (1030483254439543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2095312729118525/2251799813685248), (-63169747034797/1125899906842624)), (537101/2251799813685248), by norm_num⟩
  | 2 => ⟨((1942612188907393/2251799813685248), (-235119257498453/2251799813685248)), (529911/1125899906842624), by norm_num⟩
  | 3 => ⟨((1651328430105603/2251799813685248), (-202835763946463/1125899906842624)), (512481/562949953421312), by norm_num⟩
  | 4 => ⟨((1137896974659849/2251799813685248), (-594987994245925/2251799813685248)), (3745177/2251799813685248), by norm_num⟩
  | 5 => ⟨((13056206277829/70368744177664), (-1202655821350919/4503599627370496)), (11528487/4503599627370496), by norm_num⟩
  | 6 => ⟨((-166124523249805/4503599627370496), (-892562325406599/9007199254740992)), (10435197/4503599627370496), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-603120569/268435456), (-7263833355/268435456)), (1/134217728), by norm_num⟩, -4, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-612943327/268435456), (-3691068095/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-656776401658829/9007199254740992), (-641630304754339/9007199254740992)), (20951241/9007199254740992), by norm_num⟩
  | 1 => ⟨((3813878043/17179869184), (1862962589/8589934592)), (31/4294967296), by norm_num⟩
  | 2 => ⟨((-2902859319/8589934592), (-2835915701/8589934592)), (3/268435456), by norm_num⟩
  | 3 => ⟨((1472970055/4294967296), (1439001497/4294967296)), (99/8589934592), by norm_num⟩
  | 4 => ⟨((-2242245191/8589934592), (-2190536173/8589934592)), (77/8589934592), by norm_num⟩
  | 5 => ⟨((1365313159/8589934592), (666913653/4294967296)), (95/17179869184), by norm_num⟩
  | 6 => ⟨((-2771151031/34359738368), (-1353622387/17179869184)), (49/17179869184), by norm_num⟩
  | 7 => ⟨((2410523283/68719476736), (294366695/8589934592)), (87/68719476736), by norm_num⟩
  | 8 => ⟨((-3669446111/274877906944), (-3584824031/274877906944)), (135/274877906944), by norm_num⟩
  | 9 => ⟨((2482602449/549755813888), (303168811/68719476736)), (93/549755813888), by norm_num⟩
  | 10 => ⟨((-377916943/274877906944), (-369201699/274877906944)), (115/2199023255552), by norm_num⟩
  | 11 => ⟨((836782991/2199023255552), (408742857/1099511627776)), (129/8796093022208), by norm_num⟩
  | 12 => ⟨((-1698403061/17592186044416), (-3318471465/35184372088832)), (133/35184372088832), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581001394305331/10141204801825835211973625643008), (-1542200426477/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222305021314997/79228162514264337593543950336), (-1824485178603/316912650057057350374175801344)), (11571/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((59042871793657/1237940039285380274899124224), (-4104261441109/39614081257132168796771975168)), (3255/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889123480733031/2475880078570760549798248448), (-4359760553633/2475880078570760549798248448)), (13837/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770789316732171/154742504910672534362390528), (-2179308196619/77371252455336267181195264)), (13841/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549176701378921/9671406556917033397649408), (-4084987472615/9671406556917033397649408)), (3245/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314614652878019/151115727451828646838272), (-1786574475419/302231454903657293676544)), (5681/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887254856229633/75557863725914323419136), (-5804089410945/75557863725914323419136)), (18469/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162141980418039/590295810358705651712), (-4351074783619/4722366482869645213696)), (13859/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620891984594533/590295810358705651712), (-747436451255/73786976294838206464)), (9533/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911388854152307/36893488147419103232), (-14588891283/144115188075855872)), (2981/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1821870457579675/9223372036854775808), (-8396533132325/9223372036854775808)), (26851/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593115949687651/1152921504606846976), (-4194101533353/576460752303423488)), (26879/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193816209174965/144115188075855872), (-7330313569071/144115188075855872)), (11775/72057594037927936), by norm_num⟩
  | 4 => ⟨((745241915770563/18014398509481984), (-10976760151075/36028797018963968)), (35387/36028797018963968), by norm_num⟩
  | 3 => ⟨((185975497157123/1125899906842624), (-13688247899125/9007199254740992)), (22171/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112502831498635/2251799813685248), (-3409818902195/562949953421312)), (22253/1125899906842624), by norm_num⟩
  | 1 => ⟨((17278150917619/17592186044416), (-20336766756801/1125899906842624)), (67169/1125899906842624), by norm_num⟩
  | 0 => ⟨((2171389405218333/2251799813685248), (-40186651802591/1125899906842624)), (67991/562949953421312), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2171389405218333/2251799813685248), (-40186651802591/1125899906842624)), (259365083934593023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2090981646124319/2251799813685248), (-19375805394649/281474976710656)), (33995/140737488355328), by norm_num⟩
  | 2 => ⟨((482744649478009/562949953421312), (-143936252993227/1125899906842624)), (542517/1125899906842624), by norm_num⟩
  | 3 => ⟨((1619063890019939/2251799813685248), (-493716754579007/2251799813685248)), (534579/562949953421312), by norm_num⟩
  | 4 => ⟨((527935838648845/1125899906842624), (-709973386069779/2251799813685248)), (4012607/2251799813685248), by norm_num⟩
  | 5 => ⟨((271250928381783/2251799813685248), (-1331629544385425/4503599627370496)), (6293315/2251799813685248), by norm_num⟩
  | 6 => ⟨((-656776401658829/9007199254740992), (-641630304754339/9007199254740992)), (20951241/9007199254740992), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-612943327/268435456), (-3691068095/134217728)), (1/134217728), by norm_num⟩, -4, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨20,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile020Terms2

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
namespace Reinmann.XiRectangle.Tile026Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨26,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (7191/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (7191/640))
  have he : value ((7/8), (7191/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-325614239/134217728), (-4181235703/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((1537390657795979/18014398509481984), (414404596686617/18014398509481984)), (15694867/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1016271591/4294967296), (-34242079/536870912)), (85/17179869184), by norm_num⟩
  | 2 => ⟨((176106447/536870912), (1519027233/17179869184)), (15/2147483648), by norm_num⟩
  | 3 => ⟨((-2604110661/8589934592), (-701939629/8589934592)), (113/17179869184), by norm_num⟩
  | 4 => ⟨((3610063925/17179869184), (486547475/8589934592)), (5/1073741824), by norm_num⟩
  | 5 => ⟨((-2001844505/17179869184), (-539598417/17179869184)), (91/34359738368), by norm_num⟩
  | 6 => ⟨((925048583/17179869184), (997389657/68719476736)), (43/34359738368), by norm_num⟩
  | 7 => ⟨((-5862352615/274877906944), (-1580200751/274877906944)), (139/274877906944), by norm_num⟩
  | 8 => ⟨((4063473187/549755813888), (1095311695/549755813888)), (49/274877906944), by norm_num⟩
  | 9 => ⟨((-312953887/137438953472), (-1349710601/2199023255552)), (123/2199023255552), by norm_num⟩
  | 10 => ⟨((5553231473/8796093022208), (374219239/2199023255552)), (139/8796093022208), by norm_num⟩
  | 11 => ⟨((-5598846165/35184372088832), (-188646553/4398046511104)), (143/35184372088832), by norm_num⟩
  | 12 => ⟨((5174432579/140737488355328), (1394771481/140737488355328)), (67/70368744177664), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580815611531029/10141204801825835211973625643008), (171484222949/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444556862990981/158456325028528675187087900672), (101412484603/158456325028528675187087900672)), (23061/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889133032643641/39614081257132168796771975168), (228130182493/19807040628566084398385987584)), (3243/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944435133537529/1237940039285380274899124224), (242328363299/1237940039285380274899124224)), (13783/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885268377586905/77371252455336267181195264), (242260944197/77371252455336267181195264)), (27567/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548940617314163/9671406556917033397649408), (28381003605/604462909807314587353088)), (25845/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258252729834431/604462909807314587353088), (397190897319/604462909807314587353088)), (2827/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1886921594678223/75557863725914323419136), (322583461223/37778931862957161709568)), (36751/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296887030235977/4722366482869645213696), (483640568237/4722366482869645213696)), (27565/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620551705728623/590295810358705651712), (166156188703/147573952589676412928)), (2369/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1822355114863081/73786976294838206464), (830209817903/73786976294838206464)), (5923/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1821398822438353/9223372036854775808), (466600709937/4611686018427387904)), (53311/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592649033899193/1152921504606846976), (932221645997/1152921504606846976)), (26659/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193412955119895/144115188075855872), (6364008427/1125899906842624)), (11665/36028797018963968), by norm_num⟩
  | 4 => ⟨((372472378748845/9007199254740992), (76230709383/2251799813685248)), (17501/9007199254740992), by norm_num⟩
  | 3 => ⟨((743539751091811/4503599627370496), (1520774980429/9007199254740992)), (43765/4503599627370496), by norm_num⟩
  | 2 => ⟨((34743932906353/70368744177664), (3030063320497/4503599627370496)), (5473/140737488355328), by norm_num⟩
  | 1 => ⟨((2209648927443851/2251799813685248), (2258243261905/1125899906842624)), (16431/140737488355328), by norm_num⟩
  | 0 => ⟨((1084010603002299/1125899906842624), (557449110257/140737488355328)), (263287/1125899906842624), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1084010603002299/1125899906842624), (557449110257/140737488355328)), (1004360203269576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((521831067003091/562949953421312), (8587345890771/1125899906842624)), (509069/1125899906842624), by norm_num⟩
  | 2 => ⟨((1934731321726861/2251799813685248), (7960110559867/562949953421312)), (1903075/2251799813685248), by norm_num⟩
  | 3 => ⟨((1661857972794039/2251799813685248), (27357094766571/1125899906842624)), (3324039/2251799813685248), by norm_num⟩
  | 4 => ⟨((1225143666162707/2251799813685248), (80759587551263/2251799813685248)), (2533953/1125899906842624), by norm_num⟩
  | 5 => ⟨((663671292036993/2251799813685248), (87878235506571/2251799813685248)), (11756277/4503599627370496), by norm_num⟩
  | 6 => ⟨((1537390657795979/18014398509481984), (414404596686617/18014398509481984)), (15694867/9007199254740992), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-325614239/134217728), (-4181235703/134217728)), (1/67108864), by norm_num⟩, -5, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-166367013/67108864), (-4272661391/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((1380065627667639/18014398509481984), (-306398018897217/9007199254740992)), (33718047/18014398509481984), by norm_num⟩
  | 1 => ⟨((-3728885987/17179869184), (827876049/8589934592)), (93/17179869184), by norm_num⟩
  | 2 => ⟨((5282364769/17179869184), (-2345549469/17179869184)), (67/8589934592), by norm_num⟩
  | 3 => ⟨((-311793049/1073741824), (276893419/2147483648)), (129/17179869184), by norm_num⟩
  | 4 => ⟨((883376227/4294967296), (-1568996259/17179869184)), (93/17179869184), by norm_num⟩
  | 5 => ⟨((-4004469303/34359738368), (1778120455/34359738368)), (107/34359738368), by norm_num⟩
  | 6 => ⟨((1890919311/34359738368), (-1679264867/68719476736)), (103/68719476736), by norm_num⟩
  | 7 => ⟨((-3061358757/137438953472), (1359347323/137438953472)), (85/137438953472), by norm_num⟩
  | 8 => ⟨((4336741241/549755813888), (-1925660487/549755813888)), (123/549755813888), by norm_num⟩
  | 9 => ⟨((-5460850291/2199023255552), (1212401553/1099511627776)), (157/2199023255552), by norm_num⟩
  | 10 => ⟨((3094350783/4398046511104), (-1373996903/4398046511104)), (91/4398046511104), by norm_num⟩
  | 11 => ⟨((-3187983975/17592186044416), (707786611/8796093022208)), (95/17592186044416), by norm_num⟩
  | 12 => ⟨((1505373123/35184372088832), (-1336873647/70368744177664)), (23/17592186044416), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580746512481045/10141204801825835211973625643008), (-544337337963/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778145593881913/633825300114114700748351602688), (-160941238109/158456325028528675187087900672)), (23067/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889040954413789/39614081257132168796771975168), (-362040162357/19807040628566084398385987584)), (25951/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888772448553557/2475880078570760549798248448), (-769140886415/2475880078570760549798248448)), (13787/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885219476537057/77371252455336267181195264), (-768922222793/154742504910672534362390528)), (27575/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387212236322989/2417851639229258349412352), (-180158085237/2417851639229258349412352)), (25853/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258172534259117/604462909807314587353088), (-630321153527/604462909807314587353088)), (707/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((943395654785749/37778931862957161709568), (-511918405685/37778931862957161709568)), (36765/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296789345016641/4722366482869645213696), (-767497136583/4722366482869645213696)), (3447/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1620417435035879/590295810358705651712), (-1054690686169/590295810358705651712)), (37921/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455546836551981/18446744073709551616), (-1317437225249/73786976294838206464)), (47407/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821210178529225/9223372036854775808), (-370211138597/2305843009213693952)), (13335/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199057563717291/144115188075855872), (-184906976241/144115188075855872)), (26675/576460752303423488), by norm_num⟩
  | 5 => ⟨((596624065572735/72057594037927936), (-1292563776817/144115188075855872)), (46693/144115188075855872), by norm_num⟩
  | 4 => ⟨((744821274119991/18014398509481984), (-967640622621/18014398509481984)), (70061/36028797018963968), by norm_num⟩
  | 3 => ⟨((743385632282567/4503599627370496), (-603219152735/2251799813685248)), (87615/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222996642102743/4503599627370496), (-2403564717353/2251799813685248)), (43837/1125899906842624), by norm_num⟩
  | 1 => ⟨((552182463975149/562949953421312), (-7164312873955/2251799813685248)), (32915/281474976710656), by norm_num⟩
  | 0 => ⟨((2166197135921281/2251799813685248), (-3536041478181/562949953421312)), (527849/2251799813685248), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2166197135921281/2251799813685248), (-3536041478181/562949953421312)), (2013584145552825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2083759819912687/2251799813685248), (-27212944511257/2251799813685248)), (511099/1125899906842624), by norm_num⟩
  | 2 => ⟨((1927930900584221/2251799813685248), (-25182185383197/1125899906842624)), (1916541/2251799813685248), by norm_num⟩
  | 3 => ⟨((1649516517858625/2251799813685248), (-86241260079067/2251799813685248)), (3367515/2251799813685248), by norm_num⟩
  | 4 => ⟨((1205021499361267/2251799813685248), (-63174524732085/1125899906842624)), (5191573/2251799813685248), by norm_num⟩
  | 5 => ⟨((1275524336483593/4503599627370496), (-135228114064909/2251799813685248)), (12278015/4503599627370496), by norm_num⟩
  | 6 => ⟨((1380065627667639/18014398509481984), (-306398018897217/9007199254740992)), (33718047/18014398509481984), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-166367013/67108864), (-4272661391/134217728)), (1/67108864), by norm_num⟩, -5, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-339446739/134217728), (-4358859823/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((175511832488011/4503599627370496), (-1253073540665317/18014398509481984)), (23844787/9007199254740992), by norm_num⟩
  | 1 => ⟨((-241896841/2147483648), (3454063771/17179869184)), (133/17179869184), by norm_num⟩
  | 2 => ⟨((1398343595/8589934592), (-4991764187/17179869184)), (97/8589934592), by norm_num⟩
  | 3 => ⟨((-2694488557/17179869184), (2404675705/8589934592)), (189/17179869184), by norm_num⟩
  | 4 => ⟨((1947018407/17179869184), (-868800843/4294967296)), (139/17179869184), by norm_num⟩
  | 5 => ⟨((-1125521403/17179869184), (125557871/1073741824)), (163/34359738368), by norm_num⟩
  | 6 => ⟨((1084391759/34359738368), (-1935514263/34359738368)), (159/68719476736), by norm_num⟩
  | 7 => ⟨((-895512947/68719476736), (1598387361/68719476736)), (133/137438953472), by norm_num⟩
  | 8 => ⟨((2588365331/549755813888), (-4619933687/549755813888)), (97/274877906944), by norm_num⟩
  | 9 => ⟨((-1662519567/1099511627776), (2967405745/1099511627776)), (63/549755813888), by norm_num⟩
  | 10 => ⟨((1922119841/4398046511104), (-53605661/68719476736)), (37/1099511627776), by norm_num⟩
  | 11 => ⟨((-63132283/549755813888), (3605883081/17592186044416)), (157/17592186044416), by norm_num⟩
  | 12 => ⟨((973204095/35184372088832), (-3474114207/70368744177664)), (153/70368744177664), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790340682085487/5070602400912917605986812821504), (-1380911488473/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778067341418249/633825300114114700748351602688), (-1633011241937/633825300114114700748351602688)), (23091/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888952872649727/39614081257132168796771975168), (-1836735115563/39614081257132168796771975168)), (6495/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944339398323669/1237940039285380274899124224), (-487756927051/618970019642690137449562112)), (27607/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770345228104931/154742504910672534362390528), (-1950461687451/154742504910672534362390528)), (13805/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548761000575363/9671406556917033397649408), (-1827956653901/9671406556917033397649408)), (809/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1258095505154547/604462909807314587353088), (-799430570239/302231454903657293676544)), (177/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((1886665992176953/75557863725914323419136), (-1298511564863/37778931862957161709568)), (36821/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296695230179199/4722366482869645213696), (-1946782424781/4722366482869645213696)), (13811/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810143910708887/295147905179352825856), (-2675226315225/590295810358705651712)), (18995/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911012510584525/36893488147419103232), (-417704416255/9223372036854775808)), (47501/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821027140244829/9223372036854775808), (-1878022939699/4611686018427387904)), (53459/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796138472271129/576460752303423488), (-937983179365/288230376151711744)), (13371/288230376151711744), by norm_num⟩
  | 5 => ⟨((596543460343491/72057594037927936), (-3278319550653/144115188075855872)), (46827/144115188075855872), by norm_num⟩
  | 4 => ⟨((372349888844363/9007199254740992), (-4908250478851/36028797018963968)), (70295/36028797018963968), by norm_num⟩
  | 3 => ⟨((743232736931703/4503599627370496), (-3059597378817/4503599627370496)), (87967/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222378953418031/4503599627370496), (-12190162811601/4503599627370496)), (44057/1125899906842624), by norm_num⟩
  | 1 => ⟨((275973524950719/281474976710656), (-18165125465375/2251799813685248)), (265081/2251799813685248), by norm_num⟩
  | 0 => ⟨((1082127097434311/1125899906842624), (-8963113776627/562949953421312)), (533137/2251799813685248), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1082127097434311/1125899906842624), (-8963113776627/562949953421312)), (2033756264693450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2079541348662623/2251799813685248), (-68917162075443/2251799813685248)), (1041797/2251799813685248), by norm_num⟩
  | 2 => ⟨((1918351098226369/2251799813685248), (-15911282088373/281474976710656)), (1987973/2251799813685248), by norm_num⟩
  | 3 => ⟨((1627084301342745/2251799813685248), (-108440991185503/1125899906842624)), (1805969/1125899906842624), by norm_num⟩
  | 4 => ⟨((1154794273272067/2251799813685248), (-313425080342673/2251799813685248)), (5915529/2251799813685248), by norm_num⟩
  | 5 => ⟨((1097179709392071/4503599627370496), (-642937237457553/4503599627370496)), (15428183/4503599627370496), by norm_num⟩
  | 6 => ⟨((175511832488011/4503599627370496), (-1253073540665317/18014398509481984)), (23844787/9007199254740992), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-339446739/134217728), (-4358859823/134217728)), (1/67108864), by norm_num⟩, -5, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-345796421/134217728), (-4440396545/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-132418803503111/18014398509481984), (-170444138961649/2251799813685248)), (57053793/18014398509481984), by norm_num⟩
  | 1 => ⟨((371836745/17179869184), (7657811989/34359738368)), (323/34359738368), by norm_num⟩
  | 2 => ⟨((-547425303/17179869184), (-5636990029/17179869184)), (15/1073741824), by norm_num⟩
  | 3 => ⟨((33580425/1073741824), (5532591055/17179869184)), (237/17179869184), by norm_num⟩
  | 4 => ⟨((-395502049/17179869184), (-4072594189/17179869184)), (11/1073741824), by norm_num⟩
  | 5 => ⟨((116453165/8589934592), (2398301015/17179869184)), (209/34359738368), by norm_num⟩
  | 6 => ⟨((-457185651/68719476736), (-147117729/2147483648)), (103/34359738368), by norm_num⟩
  | 7 => ⟨((192307893/68719476736), (3960495321/137438953472)), (175/137438953472), by norm_num⟩
  | 8 => ⟨((-70779857/68719476736), (-91104975/8589934592)), (65/137438953472), by norm_num⟩
  | 9 => ⟨((11578165/34359738368), (7630308681/2199023255552)), (343/2199023255552), by norm_num⟩
  | 10 => ⟨((-109091841/1099511627776), (-1123348915/1099511627776)), (51/1099511627776), by norm_num⟩
  | 11 => ⟨((467220755/17592186044416), (2405550787/8796093022208)), (55/4398046511104), by norm_num⟩
  | 12 => ⟨((-114641917/17592186044416), (-9222653/137438953472)), (109/35184372088832), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580619739154115/10141204801825835211973625643008), (-271530343759/1267650600228229401496703205376)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222249045128065/79228162514264337593543950336), (-642151884937/158456325028528675187087900672)), (11557/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944434211061897/19807040628566084398385987584), (-180564737715/2475880078570760549798248448)), (26007/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888588936118471/2475880078570760549798248448), (-3068793632377/2475880078570760549798248448)), (27637/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770255219433453/154742504910672534362390528), (-1533943106375/77371252455336267181195264)), (27643/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548676460181273/9671406556917033397649408), (-2875179518413/9671406556917033397649408)), (25921/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258021375199329/604462909807314587353088), (-628704660191/151115727451828646838272)), (22687/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((29477269324143/1180591620717411303424), (-2042387313703/37778931862957161709568)), (36875/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162075550807467/590295810358705651712), (-3062001796515/4722366482869645213696)), (13833/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620162521554699/590295810358705651712), (-2103843888817/295147905179352825856)), (4757/73786976294838206464), by norm_num⟩
  | 8 => ⟨((910933885769121/36893488147419103232), (-2627882623009/36893488147419103232)), (5949/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820849377046093/9223372036854775808), (-5907453909351/9223372036854775808)), (13393/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796049056121291/576460752303423488), (-184401801801/36028797018963968)), (53611/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596464621630393/72057594037927936), (-5155838238505/144115188075855872)), (46953/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489160649828251/36028797018963968), (-7718954340797/36028797018963968)), (70517/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486162680474695/9007199254740992), (-9622835753331/9007199254740992)), (88299/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221760962092539/4503599627370496), (-19168292124587/4503599627370496)), (177061/4503599627370496), by norm_num⟩
  | 1 => ⟨((2206830479446249/2251799813685248), (-1784978805859/140737488355328)), (133375/1125899906842624), by norm_num⟩
  | 0 => ⟨((1081108741018399/1125899906842624), (-7044028636033/281474976710656)), (538157/2251799813685248), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1081108741018399/1125899906842624), (-7044028636033/281474976710656)), (2052906044966887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2074788725671055/2251799813685248), (-1651318173/34359738368)), (66277/140737488355328), by norm_num⟩
  | 2 => ⟨((953245597404341/1125899906842624), (-99713690806999/1125899906842624)), (2056075/2251799813685248), by norm_num⟩
  | 3 => ⟨((1596472907359479/2251799813685248), (-337691250119255/2251799813685248)), (961437/562949953421312), by norm_num⟩
  | 4 => ⟨((270304929941925/562949953421312), (-239415124111517/1125899906842624)), (3303273/1125899906842624), by norm_num⟩
  | 5 => ⟨((834672487394183/4503599627370496), (-229914179605831/1125899906842624)), (18308097/4503599627370496), by norm_num⟩
  | 6 => ⟨((-132418803503111/18014398509481984), (-170444138961649/2251799813685248)), (57053793/18014398509481984), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-345796421/134217728), (-4440396545/134217728)), (1/67108864), by norm_num⟩, -5, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-87955083/33554432), (-4517750013/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-816610228793705/18014398509481984), (-256031089448581/4503599627370496)), (59861013/18014398509481984), by norm_num⟩
  | 1 => ⟨((291627123/2147483648), (2925875083/17179869184)), (173/17179869184), by norm_num⟩
  | 2 => ⟨((-3494547137/17179869184), (-4382569207/17179869184)), (261/17179869184), by norm_num⟩
  | 3 => ⟨((436196985/2147483648), (4376334671/17179869184)), (263/17179869184), by norm_num⟩
  | 4 => ⟨((-2613458771/17179869184), (-3277581753/17179869184)), (199/17179869184), by norm_num⟩
  | 5 => ⟨((1565844557/17179869184), (3927502975/34359738368)), (241/34359738368), by norm_num⟩
  | 6 => ⟨((-1563617025/34359738368), (-3921915805/68719476736)), (243/68719476736), by norm_num⟩
  | 7 => ⟨((1338336567/68719476736), (3356859929/137438953472)), (105/68719476736), by norm_num⟩
  | 8 => ⟨((-2004649023/274877906944), (-2514063407/274877906944)), (159/274877906944), by norm_num⟩
  | 9 => ⟨((2669063011/1099511627776), (3347315949/1099511627776)), (107/549755813888), by norm_num⟩
  | 10 => ⟨((-3198319281/4398046511104), (-4011064967/4398046511104)), (129/2199023255552), by norm_num⟩
  | 11 => ⟨((1742056053/8796093022208), (4369482463/17592186044416)), (283/17592186044416), by norm_num⟩
  | 12 => ⟨((-3479155693/70368744177664), (-272704159/4398046511104)), (285/70368744177664), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790280637907115/5070602400912917605986812821504), (-730743660049/2535301200456458802993406410752)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444480091216325/158456325028528675187087900672), (-3456067749919/633825300114114700748351602688)), (723/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1888787287118577/39614081257132168796771975168), (-971796088317/9903520314283042199192993792)), (26033/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944251270970353/1237940039285380274899124224), (-4129028094461/2475880078570760549798248448)), (13833/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770168613745209/154742504910672534362390528), (-4127785041615/154742504910672534362390528)), (13837/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548595042814461/9671406556917033397649408), (-967119533671/2417851639229258349412352)), (811/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((157243738836205/75557863725914323419136), (-3383598477769/604462909807314587353088)), (22715/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943214343398301/37778931862957161709568), (-5495873692261/75557863725914323419136)), (36927/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296516626860633/4722366482869645213696), (-4119741623925/4722366482869645213696)), (6927/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405010307220783/147573952589676412928), (-1415282652025/147573952589676412928)), (19059/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821715263645967/73786976294838206464), (-1767786304971/18446744073709551616)), (47677/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820676581580317/9223372036854775808), (-3973899964589/4611686018427387904)), (53679/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591923790391599/1152921504606846976), (-7938759540483/1152921504606846976)), (53731/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596387499784773/72057594037927936), (-3468127347839/72057594037927936)), (23537/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488925872903217/36028797018963968), (-5192044281183/18014398509481984)), (8841/4503599627370496), by norm_num⟩
  | 3 => ⟨((1485863268021475/9007199254740992), (-12944656299181/9007199254740992)), (88617/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110572213746239/2251799813685248), (-25783185943163/4503599627370496)), (177853/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102930900754609/1125899906842624), (-4801286166877/281474976710656)), (134169/1125899906842624), by norm_num⟩
  | 0 => ⟨((1080053499640085/1125899906842624), (-37883787785289/1125899906842624)), (542935/2251799813685248), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1080053499640085/1125899906842624), (-37883787785289/1125899906842624)), (2071132668502043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2069598502721409/2251799813685248), (-18170583960641/281474976710656)), (1078191/2251799813685248), by norm_num⟩
  | 2 => ⟨((1892755763096587/2251799813685248), (-267205375042439/2251799813685248)), (530277/562949953421312), by norm_num⟩
  | 3 => ⟨((1559253022824235/2251799813685248), (-449200244593905/2251799813685248)), (254325/140737488355328), by norm_num⟩
  | 4 => ⟨((990092065863775/2251799813685248), (-622095121404371/2251799813685248)), (907363/281474976710656), by norm_num⟩
  | 5 => ⟨((526938456256757/4503599627370496), (-1094114033000135/4503599627370496)), (10394097/2251799813685248), by norm_num⟩
  | 6 => ⟨((-816610228793705/18014398509481984), (-256031089448581/4503599627370496)), (59861013/18014398509481984), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-87955083/33554432), (-4517750013/134217728)), (1/67108864), by norm_num⟩, -5, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-178775137/67108864), (-2295664303/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-1179239699055887/18014398509481984), (-214864200995331/9007199254740992)), (55736641/18014398509481984), by norm_num⟩
  | 1 => ⟨((427987781/2147483648), (1247709047/17179869184)), (41/4294967296), by norm_num⟩
  | 2 => ⟨((-5212073609/17179869184), (-1899339095/17179869184)), (63/4294967296), by norm_num⟩
  | 3 => ⟨((5289425017/17179869184), (1927526831/17179869184)), (129/8589934592), by norm_num⟩
  | 4 => ⟨((-4025943287/17179869184), (-183387459/2147483648)), (99/8589934592), by norm_num⟩
  | 5 => ⟨((1225707467/8589934592), (446661787/8589934592)), (243/34359738368), by norm_num⟩
  | 6 => ⟨((-4975591847/68719476736), (-1813162443/68719476736)), (249/68719476736), by norm_num⟩
  | 7 => ⟨((4328086005/137438953472), (788601963/68719476736)), (109/68719476736), by norm_num⟩
  | 8 => ⟨((-3294238739/274877906944), (-1200458185/274877906944)), (21/34359738368), by norm_num⟩
  | 9 => ⟨((1114375973/274877906944), (50761415/34359738368)), (229/1099511627776), by norm_num⟩
  | 10 => ⟨((-2714194123/2199023255552), (-1978166617/4398046511104)), (281/4398046511104), by norm_num⟩
  | 11 => ⟨((6009763569/17592186044416), (2190026419/17592186044416)), (157/8796093022208), by norm_num⟩
  | 12 => ⟨((-47648073/549755813888), (-2222528191/70368744177664)), (321/70368744177664), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395126416376533/2535301200456458802993406410752), (-909267641015/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777851102697533/633825300114114700748351602688), (-4300097466549/633825300114114700748351602688)), (23157/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118044324545073/2475880078570760549798248448), (-4836473715533/39614081257132168796771975168)), (13029/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472104832644185/618970019642690137449562112), (-2568677347867/1237940039285380274899124224)), (27695/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885042568557785/77371252455336267181195264), (-5135781581539/154742504910672534362390528)), (3463/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548516501878291/9671406556917033397649408), (-601640529291/1208925819614629174706176)), (12991/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257880906054549/604462909807314587353088), (-2104906597919/302231454903657293676544)), (22743/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943158013695853/37778931862957161709568), (-1709453819513/18889465931478580854784)), (36975/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296431671887309/4722366482869645213696), (-2562811364327/2361183241434822606848)), (27747/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619923668725973/590295810358705651712), (-7043282765365/590295810358705651712)), (38177/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821567194792457/73786976294838206464), (-8797434138951/73786976294838206464)), (47759/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227563558640749/1152921504606846976), (-9887948639665/9223372036854775808)), (53781/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591753763927961/1152921504606846976), (-9876501000413/1152921504606846976)), (26923/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192624079652543/144115188075855872), (-1078633902727/18014398509481984)), (11797/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488695215725417/36028797018963968), (-12917901132771/36028797018963968)), (70929/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485567497690241/9007199254740992), (-16102455822241/9007199254740992)), (44459/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110265342777355/2251799813685248), (-16035203731061/2251799813685248)), (89305/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102443096134085/1125899906842624), (-2985640791079/140737488355328)), (67463/562949953421312), by norm_num⟩
  | 0 => ⟨((1078969411490227/1125899906842624), (-47102242597123/1125899906842624)), (273747/1125899906842624), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1078969411490227/1125899906842624), (-47102242597123/1125899906842624)), (1044261936668014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1032024572177449/1125899906842624), (-180555584616427/2251799813685248)), (273789/562949953421312), by norm_num⟩
  | 2 => ⟨((1877475309076007/2251799813685248), (-331002425411983/2251799813685248)), (2183315/2251799813685248), by norm_num⟩
  | 3 => ⟨((1516720496113703/2251799813685248), (-8624335703301/35184372088832)), (2141311/1125899906842624), by norm_num⟩
  | 4 => ⟨((27697066835467/70368744177664), (-371776045726671/1125899906842624)), (7868699/2251799813685248), by norm_num⟩
  | 5 => ⟨((51662864842729/1125899906842624), (-1170645417268729/4503599627370496)), (711923/140737488355328), by norm_num⟩
  | 6 => ⟨((-1179239699055887/18014398509481984), (-214864200995331/9007199254740992)), (55736641/18014398509481984), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-178775137/67108864), (-2295664303/67108864)), (1/67108864), by norm_num⟩, -5, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile026Terms2

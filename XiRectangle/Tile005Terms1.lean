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
namespace Reinmann.XiRectangle.Tile005Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨5,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (1551/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (1551/640))
  have he : value ((3/4), (1551/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-75496061613/34359738368), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-28311023105/17179869184), (-365919973631/68719476736)), (3/68719476736), by norm_num⟩
  | 1 => ⟨((-75496061613/34359738368), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((62281477505093/562949953421312), (709186491345101/4503599627370496)), (79133/4503599627370496), by norm_num⟩
  | 1 => ⟨((-133639055749/549755813888), (-190215086511/549755813888)), (23/549755813888), by norm_num⟩
  | 2 => ⟨((36704377223/137438953472), (208972631531/549755813888)), (27/549755813888), by norm_num⟩
  | 3 => ⟨((-107530346307/549755813888), (-76526633665/274877906944)), (21/549755813888), by norm_num⟩
  | 4 => ⟨((59067079929/549755813888), (84073100155/549755813888)), (25/1099511627776), by norm_num⟩
  | 5 => ⟨((-103826911785/2199023255552), (-295563971125/4398046511104)), (47/4398046511104), by norm_num⟩
  | 6 => ⟨((152087361575/8796093022208), (54118368461/2199023255552)), (37/8796093022208), by norm_num⟩
  | 7 => ⟨((-190954336431/35184372088832), (-271794764041/35184372088832)), (49/35184372088832), by norm_num⟩
  | 8 => ⟨((104892390289/70368744177664), (298597067771/140737488355328)), (57/140737488355328), by norm_num⟩
  | 9 => ⟨((-102432061297/281474976710656), (-291593251567/562949953421312)), (59/562949953421312), by norm_num⟩
  | 10 => ⟨((180052994071/2251799813685248), (256278343571/2251799813685248)), (27/1125899906842624), by norm_num⟩
  | 11 => ⟨((-8991292359/562949953421312), (-204764027321/9007199254740992)), (45/9007199254740992), by norm_num⟩
  | 12 => ⟨((210729477901/72057594037927936), (18746356391/4503599627370496)), (17/18014398509481984), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677669/5070602400912917605986812821504), (1248356404079/10141204801825835211973625643008)), (29/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111214121209619/39614081257132168796771975168), (1478405281545/633825300114114700748351602688)), (17/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890481028616523/39614081257132168796771975168), (831481712825/19807040628566084398385987584)), (77/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890302135452691/2475880078570760549798248448), (883300747295/1237940039285380274899124224)), (41/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885984099609331/77371252455336267181195264), (220783410805/19342813113834066795298816)), (41/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96892634088183/604462909807314587353088), (1655520564381/9671406556917033397649408)), (77/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259426116401941/604462909807314587353088), (362056391653/151115727451828646838272)), (67/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888827503509103/75557863725914323419136), (2352701247207/75557863725914323419136)), (109/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298315723438647/4722366482869645213696), (440985997283/1180591620717411303424)), (41/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202814369957209/73786976294838206464), (37882463725/9223372036854775808)), (7/36893488147419103232), by norm_num⟩
  | 8 => ⟨((456201846169215/18446744073709551616), (1514589880427/36893488147419103232)), (35/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1824155156294819/9223372036854775808), (3405879404071/9223372036854775808)), (79/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797701141833459/576460752303423488), (3403446137237/1152921504606846976)), (79/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195818583210099/144115188075855872), (1487640014625/72057594037927936)), (69/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493491036563359/36028797018963968), (278590910591/2251799813685248)), (207/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491569316394701/9007199254740992), (5562265337873/9007199254740992)), (259/9007199254740992), by norm_num⟩
  | 2 => ⟨((2232555163987577/4503599627370496), (1386989853625/562949953421312)), (517/4503599627370496), by norm_num⟩
  | 1 => ⟨((2222974012367105/2251799813685248), (1035782007151/140737488355328)), (777/2251799813685248), by norm_num⟩
  | 0 => ⟨((2194312905882953/2251799813685248), (32860538840409/2251799813685248)), (1561/2251799813685248), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2194312905882953/2251799813685248), (32860538840409/2251799813685248)), (5954751021575217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((534453516322265/562949953421312), (64043263556159/2251799813685248)), (3089/2251799813685248), by norm_num⟩
  | 2 => ⟨((1013888403931421/1125899906842624), (7600175467713/140737488355328)), (3021/1125899906842624), by norm_num⟩
  | 3 => ⟨((454868536139249/562949953421312), (54752503150427/562949953421312)), (11535/2251799813685248), by norm_num⟩
  | 4 => ⟨((724425137009013/1125899906842624), (88481012589605/562949953421312)), (10443/1125899906842624), by norm_num⟩
  | 5 => ⟨((876589859855059/2251799813685248), (113860689175597/562949953421312)), (33443/2251799813685248), by norm_num⟩
  | 6 => ⟨((62281477505093/562949953421312), (709186491345101/4503599627370496)), (79133/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-28311023105/17179869184), (-365919973631/68719476736)), (3/68719476736), by norm_num⟩, -1, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-316464885461/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-7417145753/4294967296), (-191733217715/34359738368)), (3/68719476736), by norm_num⟩
  | 1 => ⟨((-316464885461/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((610978061515291/4503599627370496), (129443983103487/1125899906842624)), (31583/2251799813685248), by norm_num⟩
  | 1 => ⟨((-85866026403/274877906944), (-145535051695/549755813888)), (5/137438953472), by norm_num⟩
  | 2 => ⟨((98856916195/274877906944), (83776710135/274877906944)), (25/549755813888), by norm_num⟩
  | 3 => ⟨((-37937743595/137438953472), (-64301001299/274877906944)), (21/549755813888), by norm_num⟩
  | 4 => ⟨((174709765727/1099511627776), (9253657941/68719476736)), (13/549755813888), by norm_num⟩
  | 5 => ⟨((-160913640865/2199023255552), (-34091735729/549755813888)), (13/1099511627776), by norm_num⟩
  | 6 => ⟨((247011567143/8796093022208), (104665496645/4398046511104)), (21/4398046511104), by norm_num⟩
  | 7 => ⟨((-162504329229/17592186044416), (-17214372309/2199023255552)), (15/8796093022208), by norm_num⟩
  | 8 => ⟨((187090023015/70368744177664), (4954694633/2199023255552)), (37/70368744177664), by norm_num⟩
  | 9 => ⟨((-191462532463/281474976710656), (-81127864905/140737488355328)), (5/35184372088832), by norm_num⟩
  | 10 => ⟨((88171754623/562949953421312), (149443049885/1125899906842624)), (39/1125899906842624), by norm_num⟩
  | 11 => ⟨((-9228316719/281474976710656), (-250258428303/9007199254740992)), (17/2251799813685248), by norm_num⟩
  | 12 => ⟨((226655834779/36028797018963968), (192080442135/36028797018963968)), (55/36028797018963968), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790863118239471/5070602400912917605986812821504), (915754547205/10141204801825835211973625643008)), (29/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889652292713341/316912650057057350374175801344), (542184875609/316912650057057350374175801344)), (69/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236293069634873/4951760157141521099596496896), (609865151901/19807040628566084398385987584)), (77/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945078599634225/1237940039285380274899124224), (647867555485/1237940039285380274899124224)), (41/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221477916991009/19342813113834066795298816), (5060462123/604462909807314587353088)), (41/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550146413495117/9671406556917033397649408), (303559529923/2417851639229258349412352)), (77/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157413428545067/75557863725914323419136), (531092820771/302231454903657293676544)), (67/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472158695116485/18889465931478580854784), (1725540493085/75557863725914323419136)), (109/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298171307979793/4722366482869645213696), (1293708254947/4722366482869645213696)), (41/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622316594353935/590295810358705651712), (444530648483/147573952589676412928)), (7/36893488147419103232), by norm_num⟩
  | 8 => ⟨((456139934184389/18446744073709551616), (1110782195529/36893488147419103232)), (35/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455969244106503/2305843009213693952), (2497763635927/9223372036854775808)), (79/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595124633297695/1152921504606846976), (1247947277511/576460752303423488)), (157/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298894058507153/36028797018963968), (1090903402307/72057594037927936)), (69/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493128700587921/36028797018963968), (3268512803467/36028797018963968)), (207/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491118470606629/9007199254740992), (2039152784765/4503599627370496)), (259/9007199254740992), by norm_num⟩
  | 2 => ⟨((2231659677133337/4503599627370496), (508415304161/281474976710656)), (129/1125899906842624), by norm_num⟩
  | 1 => ⟨((17356611184789/17592186044416), (12147191491967/2251799813685248)), (387/1125899906842624), by norm_num⟩
  | 0 => ⟨((1095859385203177/1125899906842624), (6019029271935/562949953421312)), (777/1125899906842624), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1095859385203177/1125899906842624), (6019029271935/562949953421312)), (2964024070357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2132983349562031/2251799813685248), (46867467897461/2251799813685248)), (3059/2251799813685248), by norm_num⟩
  | 2 => ⟨((126216298800323/140737488355328), (88789001627825/2251799813685248)), (1481/562949953421312), by norm_num⟩
  | 3 => ⟨((1807593345404325/2251799813685248), (79627818363121/1125899906842624)), (11093/2251799813685248), by norm_num⟩
  | 4 => ⟨((1439751138097431/2251799813685248), (31959926834411/281474976710656)), (19379/2251799813685248), by norm_num⟩
  | 5 => ⟨((891514140983385/2251799813685248), (326951557620375/2251799813685248)), (29183/2251799813685248), by norm_num⟩
  | 6 => ⟨((610978061515291/4503599627370496), (129443983103487/1125899906842624)), (31583/2251799813685248), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7417145753/4294967296), (-191733217715/34359738368)), (3/68719476736), by norm_num⟩, -1, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-329564216829/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-123586581311/68719476736), (-399339140861/68719476736)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-329564216829/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1328157516883325/9007199254740992), (21189502949833/281474976710656)), (67139/9007199254740992), by norm_num⟩
  | 1 => ⟨((-97191852761/274877906944), (-12404836171/68719476736)), (3/137438953472), by norm_num⟩
  | 2 => ⟨((116527942145/274877906944), (118981992057/549755813888)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((-186281201079/549755813888), (-95102118767/549755813888)), (7/274877906944), by norm_num⟩
  | 4 => ⟨((223341405739/1099511627776), (3563201891/34359738368)), (19/1099511627776), by norm_num⟩
  | 5 => ⟨((-214219720417/2199023255552), (-54682783811/1099511627776)), (5/549755813888), by norm_num⟩
  | 6 => ⟨((10701592811/274877906944), (174831451739/8796093022208)), (35/8796093022208), by norm_num⟩
  | 7 => ⟨((-234617589147/17592186044416), (-59889644523/8796093022208)), (13/8796093022208), by norm_num⟩
  | 8 => ⟨((140647101983/35184372088832), (143609095491/70368744177664)), (17/35184372088832), by norm_num⟩
  | 9 => ⟨((-299784018647/281474976710656), (-153048698315/281474976710656)), (19/140737488355328), by norm_num⟩
  | 10 => ⟨((143770136235/562949953421312), (146797900079/1125899906842624)), (39/1125899906842624), by norm_num⟩
  | 11 => ⟨((-250724167307/4503599627370496), (-32000544605/1125899906842624)), (9/1125899906842624), by norm_num⟩
  | 12 => ⟨((100201715927/9007199254740992), (51155969757/9007199254740992)), (15/9007199254740992), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581633122365965/10141204801825835211973625643008), (38429973103/633825300114114700748351602688)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779194678241745/633825300114114700748351602688), (728009698703/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236277618824335/4951760157141521099596496896), (102360185407/4951760157141521099596496896)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945012958244129/1237940039285380274899124224), (869901961509/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442923027092391/38685626227668133590597632), (869722450339/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550023446308903/9671406556917033397649408), (203793529459/2417851639229258349412352)), (51/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78699993168527/37778931862957161709568), (713086731427/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236057517703265/9444732965739290427392), (579204322719/37778931862957161709568)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40563763278935/147573952589676412928), (868493975061/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622136786174697/590295810358705651712), (1193671618085/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912167605180997/36893488147419103232), (745664263823/36893488147419103232)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823624705500829/9223372036854775808), (1676698877545/9223372036854775808)), (105/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594872763490535/1152921504606846976), (837696354911/576460752303423488)), (105/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195356298599195/144115188075855872), (1464500525171/144115188075855872)), (23/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492799697234551/36028797018963968), (2193817949555/36028797018963968)), (69/18014398509481984), by norm_num⟩
  | 3 => ⟨((745354393824889/4503599627370496), (2737147506827/9007199254740992)), (43/2251799813685248), by norm_num⟩
  | 2 => ⟨((139427813209633/281474976710656), (1364737581359/1125899906842624)), (343/4503599627370496), by norm_num⟩
  | 1 => ⟨((2220435935940817/2251799813685248), (8150168923771/2251799813685248)), (129/562949953421312), by norm_num⟩
  | 0 => ⟨((1094672353727349/1125899906842624), (16147940919407/2251799813685248)), (1033/2251799813685248), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1094672353727349/1125899906842624), (16147940919407/2251799813685248)), (3940590865325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((532126508641535/562949953421312), (31400134926147/2251799813685248)), (253/281474976710656), by norm_num⟩
  | 2 => ⟨((502881288911971/562949953421312), (3710108702287/140737488355328)), (971/562949953421312), by norm_num⟩
  | 3 => ⟨((448830931944927/562949953421312), (106055281674435/2251799813685248)), (7145/2251799813685248), by norm_num⟩
  | 4 => ⟨((713193851699719/1125899906842624), (169112336264797/2251799813685248)), (12067/2251799813685248), by norm_num⟩
  | 5 => ⟨((890835360204261/2251799813685248), (107123091260267/1125899906842624)), (34201/4503599627370496), by norm_num⟩
  | 6 => ⟨((1328157516883325/9007199254740992), (21189502949833/281474976710656)), (67139/9007199254740992), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-123586581311/68719476736), (-399339140861/68719476736)), (1/34359738368), by norm_num⟩, -1, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-170761484711/68719476736), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-128071113533/68719476736), (-103457446401/17179869184)), (3/68719476736), by norm_num⟩
  | 1 => ⟨((-170761484711/68719476736), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1349649003533519/9007199254740992), (360726130694449/9007199254740992)), (79941/9007199254740992), by norm_num⟩
  | 1 => ⟨((-204696764145/549755813888), (-109420258901/1099511627776)), (27/1099511627776), by norm_num⟩
  | 2 => ⟨((254326175207/549755813888), (67974782241/549755813888)), (19/549755813888), by norm_num⟩
  | 3 => ⟨((-105329467331/274877906944), (-56303662803/549755813888)), (17/549755813888), by norm_num⟩
  | 4 => ⟨((261733893789/1099511627776), (69954673053/1099511627776)), (23/1099511627776), by norm_num⟩
  | 5 => ⟨((-65038429315/549755813888), (-69532332901/2199023255552)), (25/2199023255552), by norm_num⟩
  | 6 => ⟨((107742950331/2199023255552), (57593785467/4398046511104)), (11/2199023255552), by norm_num⟩
  | 7 => ⟨((-38247310535/2199023255552), (-81780103139/17592186044416)), (33/17592186044416), by norm_num⟩
  | 8 => ⟨((380163985139/70368744177664), (101607961055/70368744177664)), (43/70368744177664), by norm_num⟩
  | 9 => ⟨((-419854228747/281474976710656), (-112216132487/281474976710656)), (25/140737488355328), by norm_num⟩
  | 10 => ⟨((417319425981/1125899906842624), (27884661383/281474976710656)), (13/281474976710656), by norm_num⟩
  | 11 => ⟨((-188545421219/2251799813685248), (-100786589815/4503599627370496)), (49/4503599627370496), by norm_num⟩
  | 12 => ⟨((312345180649/18014398509481984), (83481755747/18014398509481984)), (21/9007199254740992), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581548115840927/10141204801825835211973625643008), (340202235605/10141204801825835211973625643008)), (29/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111193389604645/39614081257132168796771975168), (100687954663/158456325028528675187087900672)), (69/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945053989956873/19807040628566084398385987584), (453021758503/39614081257132168796771975168)), (77/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944952961037853/1237940039285380274899124224), (60155515303/309485009821345068724781056)), (41/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885786077745261/77371252455336267181195264), (481141223235/154742504910672534362390528)), (41/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774955517298633/4835703278458516698824704), (450960597351/9671406556917033397649408)), (77/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314775393635553/151115727451828646838272), (12327539315/18889465931478580854784)), (67/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944150230255195/37778931862957161709568), (160206811809/18889465931478580854784)), (109/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297920736354299/4722366482869645213696), (480441311881/4722366482869645213696)), (41/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810986165872015/295147905179352825856), (330157933337/295147905179352825856)), (7/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1824129818224421/73786976294838206464), (824958670013/73786976294838206464)), (35/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823393880994935/9223372036854775808), (3622965519/36028797018963968)), (157/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797321120362011/576460752303423488), (926730599317/1152921504606846976)), (157/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149394366274177/18014398509481984), (810047939817/144115188075855872)), (69/72057594037927936), by norm_num⟩
  | 4 => ⟨((746249160776219/18014398509481984), (1213391265075/36028797018963968)), (103/18014398509481984), by norm_num⟩
  | 3 => ⟨((46572914068441/281474976710656), (1513802502571/9007199254740992)), (257/9007199254740992), by norm_num⟩
  | 2 => ⟨((557524368242305/1125899906842624), (1509406718635/2251799813685248)), (257/2251799813685248), by norm_num⟩
  | 1 => ⟨((2219323435156217/2251799813685248), (4506304695465/2251799813685248)), (771/2251799813685248), by norm_num⟩
  | 0 => ⟨((546788681623721/562949953421312), (8925327264035/2251799813685248)), (193/281474976710656), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((546788681623721/562949953421312), (8925327264035/2251799813685248)), (736237646007449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1062165052836881/1125899906842624), (17338194623171/2251799813685248)), (753/562949953421312), by norm_num⟩
  | 2 => ⟨((2003942693952923/2251799813685248), (16356715455871/1125899906842624)), (2865/1125899906842624), by norm_num⟩
  | 3 => ⟨((445723030937959/562949953421312), (14556320786445/562949953421312)), (5183/1125899906842624), by norm_num⟩
  | 4 => ⟨((705061374026467/1125899906842624), (92201267708553/2251799813685248)), (2119/281474976710656), by norm_num⟩
  | 5 => ⟨((439636125462005/1125899906842624), (230953220983475/4503599627370496)), (5655/562949953421312), by norm_num⟩
  | 6 => ⟨((1349649003533519/9007199254740992), (360726130694449/9007199254740992)), (79941/9007199254740992), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-128071113533/68719476736), (-103457446401/17179869184)), (3/68719476736), by norm_num⟩, -1, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-176261977699/68719476736), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-66098241637/34359738368), (-106789971645/17179869184)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-176261977699/68719476736), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((656328384288895/4503599627370496), (44165744891119/4503599627370496)), (21105/4503599627370496), by norm_num⟩
  | 1 => ⟨((-410998307511/1099511627776), (-27656957759/1099511627776)), (15/1099511627776), by norm_num⟩
  | 2 => ⟨((32943432649/68719476736), (2216834251/68719476736)), (11/549755813888), by norm_num⟩
  | 3 => ⟨((-225328630415/549755813888), (-30325693801/1099511627776)), (21/1099511627776), by norm_num⟩
  | 4 => ⟨((72244565725/274877906944), (19445967207/1099511627776)), (15/1099511627776), by norm_num⟩
  | 5 => ⟨((-148242921949/1099511627776), (-19951168437/2199023255552)), (17/2199023255552), by norm_num⟩
  | 6 => ⟨((506980783201/8796093022208), (17057912221/4398046511104)), (1/274877906944), by norm_num⟩
  | 7 => ⟨((-371537152605/17592186044416), (-25001531995/17592186044416)), (13/8796093022208), by norm_num⟩
  | 8 => ⟨((476486990423/70368744177664), (32063831713/70368744177664)), (9/17592186044416), by norm_num⟩
  | 9 => ⟨((-271592222205/140737488355328), (-18276023233/140737488355328)), (11/70368744177664), by norm_num⟩
  | 10 => ⟨((139324059167/281474976710656), (18750829619/562949953421312)), (25/562949953421312), by norm_num⟩
  | 11 => ⟨((-64974392007/562949953421312), (-17489064867/2251799813685248)), (25/2251799813685248), by norm_num⟩
  | 12 => ⟨((222208033373/9007199254740992), (14952855231/9007199254740992)), (45/18014398509481984), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917418255/10141204801825835211973625643008), (21880895585/2535301200456458802993406410752)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779001743299051/633825300114114700748351602688), (51802703023/316912650057057350374175801344)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890003950138537/39614081257132168796771975168), (116536455099/39614081257132168796771975168)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472448854441817/618970019642690137449562112), (123795690325/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771461681912691/154742504910672534362390528), (123768369871/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549807498257873/9671406556917033397649408), (116003827307/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157376376609023/75557863725914323419136), (101474339049/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888153358944747/75557863725914323419136), (20605178487/9444732965739290427392)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297810463657351/4722366482869645213696), (61791757443/2361183241434822606848)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621820793635067/590295810358705651712), (10615630789/36893488147419103232)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823940525772601/73786976294838206464), (13262301381/4611686018427387904)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911590552922317/4611686018427387904), (119281158539/4611686018427387904)), (105/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594429688928113/1152921504606846976), (238363595029/1152921504606846976)), (105/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194969198346107/144115188075855872), (104172403411/72057594037927936)), (23/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492220224981681/36028797018963968), (312071090659/36028797018963968)), (69/18014398509481984), by norm_num⟩
  | 3 => ⟨((372496626224145/2251799813685248), (194654704041/4503599627370496)), (43/2251799813685248), by norm_num⟩
  | 2 => ⟨((2229406601932957/4503599627370496), (776285458135/4503599627370496)), (343/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218293654055329/2251799813685248), (1158612281525/2251799813685248)), (513/2251799813685248), by norm_num⟩
  | 0 => ⟨((2185121126027361/2251799813685248), (1147032788521/1125899906842624)), (513/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2185121126027361/2251799813685248), (1147032788521/1125899906842624)), (1956943992232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2120414542916209/2251799813685248), (4452270691579/2251799813685248)), (997/1125899906842624), by norm_num⟩
  | 2 => ⟨((1996686376724563/2251799813685248), (8384990056441/2251799813685248)), (941/562949953421312), by norm_num⟩
  | 3 => ⟨((885222157562641/1125899906842624), (14870056665709/2251799813685248)), (419/140737488355328), by norm_num⟩
  | 4 => ⟨((1391887473889047/2251799813685248), (23382724458361/2251799813685248)), (10631/2251799813685248), by norm_num⟩
  | 5 => ⟨((1720227505478299/4503599627370496), (57813525129887/4503599627370496)), (3341/562949953421312), by norm_num⟩
  | 6 => ⟨((656328384288895/4503599627370496), (44165744891119/4503599627370496)), (21105/4503599627370496), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66098241637/34359738368), (-106789971645/17179869184)), (1/34359738368), by norm_num⟩, -1, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-362709277535/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-34003994769/17179869184), (-109875408097/17179869184)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-362709277535/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((309160723853425/2251799813685248), (-139593493365839/9007199254740992)), (83375/9007199254740992), by norm_num⟩
  | 1 => ⟨((-49798149067/137438953472), (44970121073/1099511627776)), (15/549755813888), by norm_num⟩
  | 2 => ⟨((262840340593/549755813888), (-7417420477/137438953472)), (21/549755813888), by norm_num⟩
  | 3 => ⟨((-3612764205/8589934592), (26099997169/549755813888)), (5/137438953472), by norm_num⟩
  | 4 => ⟨((76274334843/274877906944), (-2152480901/68719476736)), (7/274877906944), by norm_num⟩
  | 5 => ⟨((-161033873943/1099511627776), (36355331191/2199023255552)), (1/68719476736), by norm_num⟩
  | 6 => ⟨((283318416897/4398046511104), (-15990633875/2199023255552)), (15/2199023255552), by norm_num⟩
  | 7 => ⟨((-213626727065/8796093022208), (24114399733/8796093022208)), (3/1099511627776), by norm_num⟩
  | 8 => ⟨((281886589931/35184372088832), (-15909820841/17592186044416)), (17/17592186044416), by norm_num⟩
  | 9 => ⟨((-330628831679/140737488355328), (4665214367/17592186044416)), (21/70368744177664), by norm_num⟩
  | 10 => ⟨((174509688325/281474976710656), (-19698829071/281474976710656)), (23/281474976710656), by norm_num⟩
  | 11 => ⟨((-83734740375/562949953421312), (37808246723/2251799813685248)), (23/1125899906842624), by norm_num⟩
  | 12 => ⟨((36830130055/1125899906842624), (-16629688439/4503599627370496)), (21/4503599627370496), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581397516987295/10141204801825835211973625643008), (-146420310157/10141204801825835211973625643008)), (19/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889458016706937/316912650057057350374175801344), (-173308085705/633825300114114700748351602688)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944953771195647/19807040628566084398385987584), (-194937858745/39614081257132168796771975168)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472423251040263/618970019642690137449562112), (-207079665389/2475880078570760549798248448)), (27/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885679645188755/77371252455336267181195264), (-207032646441/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774855764818703/4835703278458516698824704), (-194043163507/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629463531882745/302231454903657293676544), (-169737842531/604462909807314587353088)), (89/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888016985573235/75557863725914323419136), (-275730419825/75557863725914323419136)), (9/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((648854111024347/2361183241434822606848), (-206715973447/4722366482869645213696)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621680273825581/590295810358705651712), (-142050769397/295147905179352825856)), (149/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823764969561825/73786976294838206464), (-354927654705/73786976294838206464)), (93/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911491866827457/4611686018427387904), (-99754952249/2305843009213693952)), (209/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594232477294741/1152921504606846976), (-398677843639/1152921504606846976)), (209/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298699204654271/36028797018963968), (-348458797549/144115188075855872)), (183/144115188075855872), by norm_num⟩
  | 4 => ⟨((745981007924841/18014398509481984), (-521920552427/36028797018963968)), (137/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489664373303195/9007199254740992), (-162764883065/2251799813685248)), (343/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228764224273111/4503599627370496), (-1298104448695/4503599627370496)), (171/1125899906842624), by norm_num⟩
  | 1 => ⟨((69291712113399/70368744177664), (-1937151071735/2251799813685248)), (513/1125899906842624), by norm_num⟩
  | 0 => ⟨((2183222111130963/2251799813685248), (-1917232411547/1125899906842624)), (2053/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2183222111130963/2251799813685248), (-1917232411547/1125899906842624)), (7831582076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1058363193398173/1125899906842624), (-7435375325333/2251799813685248)), (3989/2251799813685248), by norm_num⟩
  | 2 => ⟨((1989730740949407/2251799813685248), (-13978733856549/2251799813685248)), (7527/2251799813685248), by norm_num⟩
  | 3 => ⟨((879037513108215/1125899906842624), (-24703720379483/2251799813685248)), (13397/2251799813685248), by norm_num⟩
  | 4 => ⟨((1372332258500337/2251799813685248), (-38574471487077/2251799813685248)), (21215/2251799813685248), by norm_num⟩
  | 5 => ⟨((104461319476175/281474976710656), (-94034987043865/4503599627370496)), (13293/1125899906842624), by norm_num⟩
  | 6 => ⟨((309160723853425/2251799813685248), (-139593493365839/9007199254740992)), (83375/9007199254740992), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34003994769/17179869184), (-109875408097/17179869184)), (1/17179869184), by norm_num⟩, -1, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-372191585589/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-34892961149/17179869184), (-225495761425/34359738368)), (1/17179869184), by norm_num⟩
  | 1 => ⟨((-372191585589/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1135844935581245/9007199254740992), (-163065773994711/4503599627370496)), (91755/9007199254740992), by norm_num⟩
  | 1 => ⟨((-375479138943/1099511627776), (107810132339/1099511627776)), (33/1099511627776), by norm_num⟩
  | 2 => ⟨((254204089431/549755813888), (-2280900395/17179869184)), (3/68719476736), by norm_num⟩
  | 3 => ⟨((-229465811835/549755813888), (65885789583/549755813888)), (3/68719476736), by norm_num⟩
  | 4 => ⟨((310702468943/1099511627776), (-89211012865/1099511627776)), (17/549755813888), by norm_num⟩
  | 5 => ⟨((-168279576701/1099511627776), (24158790133/549755813888)), (39/2199023255552), by norm_num⟩
  | 6 => ⟨((151903180509/2199023255552), (-10903869413/549755813888)), (37/4398046511104), by norm_num⟩
  | 7 => ⟨((-235063679157/8796093022208), (16873271861/2199023255552)), (15/4398046511104), by norm_num⟩
  | 8 => ⟨((159141060903/17592186044416), (-91387334513/35184372088832)), (43/35184372088832), by norm_num⟩
  | 9 => ⟨((-383077317317/140737488355328), (54995886579/70368744177664)), (27/70368744177664), by norm_num⟩
  | 10 => ⟨((414957042479/562949953421312), (-14893162171/70368744177664)), (15/140737488355328), by norm_num⟩
  | 11 => ⟨((-204313545879/1125899906842624), (58663899363/1125899906842624)), (31/1125899906842624), by norm_num⟩
  | 12 => ⟨((184430446335/4503599627370496), (-13238732039/1125899906842624)), (29/4503599627370496), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798647/10141204801825835211973625643008), (-182108431743/5070602400912917605986812821504)), (77/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778836172723627/633825300114114700748351602688), (-431062724291/633825300114114700748351602688)), (91/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944908855062595/19807040628566084398385987584), (-484859536107/39614081257132168796771975168)), (103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889597570747385/2475880078570760549798248448), (-515056548549/2475880078570760549798248448)), (109/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885631936000921/77371252455336267181195264), (-514936545265/154742504910672534362390528)), (109/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549622090885523/9671406556917033397649408), (-482625547041/9671406556917033397649408)), (51/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629424410415005/302231454903657293676544), (-211084966893/302231454903657293676544)), (89/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943944935372613/37778931862957161709568), (-685787324175/75557863725914323419136)), (9/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((40550403503779/147573952589676412928), (-514131621177/4722366482869645213696)), (109/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621549265227413/590295810358705651712), (-353295869169/295147905179352825856)), (149/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911800636311373/36893488147419103232), (-220682779957/18446744073709551616)), (93/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227849957787825/1152921504606846976), (-992373749575/9223372036854775808)), (209/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398512128880885/288230376151711744), (-991501049097/1152921504606846976)), (105/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194635975278565/144115188075855872), (-27080708123/4503599627370496)), (183/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491720997095801/36028797018963968), (-648957522979/18014398509481984)), (275/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489363530425709/9007199254740992), (-1618971434729/9007199254740992)), (343/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114081914347555/2251799813685248), (-3227698827877/4503599627370496)), (685/4503599627370496), by norm_num⟩
  | 1 => ⟨((277054676799179/281474976710656), (-4816018725405/2251799813685248)), (257/562949953421312), by norm_num⟩
  | 0 => ⟨((2181440213329879/2251799813685248), (-9530401469859/2251799813685248)), (1029/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2181440213329879/2251799813685248), (-9530401469859/2251799813685248)), (3925327781295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2113238728798331/2251799813685248), (-1154076890471/140737488355328)), (2003/1125899906842624), by norm_num⟩
  | 2 => ⟨((1983052371274981/2251799813685248), (-17329000321485/1125899906842624)), (7585/2251799813685248), by norm_num⟩
  | 3 => ⟨((872922962849189/1125899906842624), (-61043286300137/2251799813685248)), (6797/1125899906842624), by norm_num⟩
  | 4 => ⟨((337979834505487/562949953421312), (-94655103913451/2251799813685248)), (21817/2251799813685248), by norm_num⟩
  | 5 => ⟨((807676728973677/2251799813685248), (-227313395525413/4503599627370496)), (56063/4503599627370496), by norm_num⟩
  | 6 => ⟨((1135844935581245/9007199254740992), (-163065773994711/4503599627370496)), (91755/9007199254740992), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34892961149/17179869184), (-225495761425/34359738368)), (1/17179869184), by norm_num⟩, -1, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 12 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨5,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile005Terms1

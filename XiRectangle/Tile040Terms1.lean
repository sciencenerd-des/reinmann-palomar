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
namespace Reinmann.XiRectangle.Tile040Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨40,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/32), (7191/512)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((19/32), (7191/512))
  have he : value ((19/32), (7191/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-21887591/16777216), (-64717791/2097152)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1179625963/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((1037660910568639/4503599627370496), (322453479562637/2251799813685248)), (3701525/140737488355328), by norm_num⟩
  | 1 => ⟨((-543588175/1073741824), (-337840419/1073741824)), (63/1073741824), by norm_num⟩
  | 2 => ⟨((597192649/1073741824), (92788909/268435456)), (141/2147483648), by norm_num⟩
  | 3 => ⟨((-874777577/2147483648), (-543674857/2147483648)), (105/2147483648), by norm_num⟩
  | 4 => ⟨((240260349/1073741824), (597287879/4294967296)), (117/4294967296), by norm_num⟩
  | 5 => ⟨((-422324755/4294967296), (-524950243/8589934592)), (105/8589934592), by norm_num⟩
  | 6 => ⟨((618628221/17179869184), (768955717/34359738368)), (39/8589934592), by norm_num⟩
  | 7 => ⟨((-194180733/17179869184), (-482733829/68719476736)), (25/17179869184), by norm_num⟩
  | 8 => ⟨((426658679/137438953472), (530337317/274877906944)), (7/17179869184), by norm_num⟩
  | 9 => ⟨((-833302165/1099511627776), (-517897861/1099511627776)), (111/1099511627776), by norm_num⟩
  | 10 => ⟨((732380799/4398046511104), (113793791/1099511627776)), (25/1099511627776), by norm_num⟩
  | 11 => ⟨((-36572843/1099511627776), (-90920187/4398046511104)), (81/17592186044416), by norm_num⟩
  | 12 => ⟨((857159995/140737488355328), (532725519/140737488355328)), (121/140737488355328), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582276377228079/10141204801825835211973625643008), (362177485687/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779956484222263/633825300114114700748351602688), (858325835133/633825300114114700748351602688)), (92285/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1891077858102295/39614081257132168796771975168), (241376130567/9903520314283042199192993792)), (51913/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890936228438193/2475880078570760549798248448), (1025711979149/2475880078570760549798248448)), (110321/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772602249050197/154742504910672534362390528), (1025558361909/154742504910672534362390528)), (13791/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((193859565158089/1208925819614629174706176), (60081111037/604462909807314587353088)), (103441/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157493268674625/75557863725914323419136), (840972401269/604462909807314587353088)), (45259/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472418117769389/18889465931478580854784), (170784289113/9444732965739290427392)), (147105/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649474686896715/2361183241434822606848), (256109549645/1180591620717411303424)), (55171/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623386106443463/590295810358705651712), (1408167914033/590295810358705651712)), (151739/590295810358705651712), by norm_num⟩
  | 8 => ⟨((14264813549889/576460752303423488), (439889554735/18446744073709551616)), (189703/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456344936718633/2305843009213693952), (989303667413/4611686018427387904)), (106729/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199578319745213/144115188075855872), (123593021393/72057594037927936)), (213509/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299222366770011/36028797018963968), (216130529487/18014398509481984)), (186879/144115188075855872), by norm_num⟩
  | 4 => ⟨((1495096649300759/36028797018963968), (2591052232835/36028797018963968)), (140217/18014398509481984), by norm_num⟩
  | 3 => ⟨((1493575082673087/9007199254740992), (404302511209/1125899906842624)), (350747/9007199254740992), by norm_num⟩
  | 2 => ⟨((2236562940542099/4503599627370496), (3227836299507/2251799813685248)), (351053/2251799813685248), by norm_num⟩
  | 1 => ⟨((2228976262569477/2251799813685248), (4825326475463/1125899906842624)), (527347/1125899906842624), by norm_num⟩
  | 0 => ⟨((2206279601054721/2251799813685248), (19170259491537/2251799813685248)), (528887/562949953421312), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2206279601054721/2251799813685248), (19170259491537/2251799813685248)), (2017543794872093023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1080758189427035/1125899906842624), (37565464039971/2251799813685248)), (2090793/1125899906842624), by norm_num⟩
  | 2 => ⟨((2074226076216711/2251799813685248), (72118636219943/2251799813685248)), (4083689/1125899906842624), by norm_num⟩
  | 3 => ⟨((1908345800302035/2251799813685248), (132862925842219/2251799813685248)), (973111/140737488355328), by norm_num⟩
  | 4 => ⟨((804718766393333/1125899906842624), (225196223044257/2251799813685248)), (1764209/140737488355328), by norm_num⟩
  | 5 => ⟨((1127798225061941/2251799813685248), (160955361753967/1125899906842624)), (45995953/2251799813685248), by norm_num⟩
  | 6 => ⟨((1037660910568639/4503599627370496), (322453479562637/2251799813685248)), (3701525/140737488355328), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-21887591/16777216), (-64717791/2097152)), (1/16777216), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-22937137/16777216), (-67821115/2097152)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1236190959/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((172971443950723/1125899906842624), (-915639932809051/4503599627370496)), (139582521/4503599627370496), by norm_num⟩
  | 1 => ⟨((-379830807/1073741824), (1005334311/2147483648)), (39/536870912), by norm_num⟩
  | 2 => ⟨((437296377/1073741824), (-1157433899/2147483648)), (91/1073741824), by norm_num⟩
  | 3 => ⟨((-335637373/1073741824), (888363347/2147483648)), (71/1073741824), by norm_num⟩
  | 4 => ⟨((193208403/1073741824), (-255691525/1073741824)), (83/2147483648), by norm_num⟩
  | 5 => ⟨((-355903031/4294967296), (471001195/4294967296)), (155/8589934592), by norm_num⟩
  | 6 => ⟨((546331343/17179869184), (-361506777/8589934592)), (121/17179869184), by norm_num⟩
  | 7 => ⟨((-359421259/34359738368), (475657209/34359738368)), (161/68719476736), by norm_num⟩
  | 8 => ⟨((827598033/274877906944), (-1095241199/274877906944)), (47/68719476736), by norm_num⟩
  | 9 => ⟨((-846939953/1099511627776), (140104781/137438953472)), (195/1099511627776), by norm_num⟩
  | 10 => ⟨((195015131/1099511627776), (-1032330177/4398046511104)), (91/2199023255552), by norm_num⟩
  | 11 => ⟨((-163286885/4398046511104), (432186923/8796093022208)), (77/8796093022208), by norm_num⟩
  | 12 => ⟨((501309263/70368744177664), (-165857861/17592186044416)), (15/8796093022208), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197774361085933/1267650600228229401496703205376), (-1203223953723/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779859237182967/633825300114114700748351602688), (-89100972207/39614081257132168796771975168)), (23085/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945484213824233/19807040628566084398385987584), (-1603622149433/39614081257132168796771975168)), (25973/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890819923297909/2475880078570760549798248448), (-1703610752801/2475880078570760549798248448)), (27599/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((886242952120653/77371252455336267181195264), (-1703343297667/154742504910672534362390528)), (110407/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96922962867553/604462909807314587353088), (-798300110473/4835703278458516698824704)), (103519/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259850631335753/604462909807314587353088), (-1396741129475/604462909807314587353088)), (2831/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((1889517175343297/75557863725914323419136), (-2269171836275/75557863725914323419136)), (147235/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324708208255505/1180591620717411303424), (-425353265263/1180591620717411303424)), (110447/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623225750905485/590295810358705651712), (-2338686233727/590295810358705651712)), (151897/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825695522172497/73786976294838206464), (-1461111549891/36893488147419103232)), (189921/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825153827706553/9223372036854775808), (-1642970713825/4611686018427387904)), (106865/4611686018427387904), by norm_num⟩
  | 6 => ⟨((399100087796225/288230376151711744), (-820998235357/288230376151711744)), (213815/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196691213175887/144115188075855872), (-2871303100713/144115188075855872)), (93593/72057594037927936), by norm_num⟩
  | 4 => ⟨((1494798623957645/36028797018963968), (-4302576513249/36028797018963968)), (280971/36028797018963968), by norm_num⟩
  | 3 => ⟨((373300356606793/2251799813685248), (-5370566339405/9007199254740992)), (5493/140737488355328), by norm_num⟩
  | 2 => ⟨((2235812267466523/4503599627370496), (-5359099752867/2251799813685248)), (88015/562949953421312), by norm_num⟩
  | 1 => ⟨((2227841897305207/2251799813685248), (-16020070290587/2251799813685248)), (1058725/2251799813685248), by norm_num⟩
  | 0 => ⟨((1101988860978633/1125899906842624), (-31811847679839/2251799813685248)), (2127657/2251799813685248), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1101988860978633/1125899906842624), (-31811847679839/2251799813685248)), (8116367348677825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2156721825677337/2251799813685248), (-62272501449335/2251799813685248)), (1056265/562949953421312), by norm_num⟩
  | 2 => ⟨((515984052031485/562949953421312), (-119286325719607/2251799813685248)), (8327015/2251799813685248), by norm_num⟩
  | 3 => ⟨((1885426678653701/2251799813685248), (-109334482262025/1125899906842624)), (8073421/1125899906842624), by norm_num⟩
  | 4 => ⟨((1557428694690935/2251799813685248), (-366182017603499/2251799813685248)), (15087709/1125899906842624), by norm_num⟩
  | 5 => ⟨((1017628145763245/2251799813685248), (-15829070878923/70368744177664)), (25777495/1125899906842624), by norm_num⟩
  | 6 => ⟨((172971443950723/1125899906842624), (-915639932809051/4503599627370496)), (139582521/4503599627370496), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-22937137/16777216), (-67821115/2097152)), (1/16777216), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-47773133/33554432), (-1130054609/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-691607850570899/4503599627370496), (-417683128479521/2251799813685248)), (194723255/4503599627370496), by norm_num⟩
  | 1 => ⟨((790788267/2147483648), (955162429/2147483648)), (225/2147483648), by norm_num⟩
  | 2 => ⟨((-237028431/536870912), (-1145189737/2147483648)), (273/2147483648), by norm_num⟩
  | 3 => ⟨((378912903/1073741824), (7151159/16777216)), (221/2147483648), by norm_num⟩
  | 4 => ⟨((-908593459/4294967296), (-1097454743/4294967296)), (267/4294967296), by norm_num⟩
  | 5 => ⟨((54467799/536870912), (131579077/1073741824)), (129/4294967296), by norm_num⟩
  | 6 => ⟨((-696576415/17179869184), (-841367591/17179869184)), (209/17179869184), by norm_num⟩
  | 7 => ⟨((59654189/4294967296), (144107955/8589934592)), (289/68719476736), by norm_num⟩
  | 8 => ⟨((-572177991/137438953472), (-43194473/8589934592)), (175/137438953472), by norm_num⟩
  | 9 => ⟨((609787955/549755813888), (736539183/549755813888)), (189/549755813888), by norm_num⟩
  | 10 => ⟨((-292441531/1099511627776), (-353228765/1099511627776)), (183/2199023255552), by norm_num⟩
  | 11 => ⟨((127498939/2199023255552), (308002031/4398046511104)), (81/4398046511104), by norm_num⟩
  | 12 => ⟨((-101909701/8796093022208), (-123092769/8796093022208)), (261/70368744177664), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582121173362579/10141204801825835211973625643008), (-2946931211405/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779766475855193/633825300114114700748351602688), (-3491286098253/633825300114114700748351602688)), (723/4951760157141521099596496896), by norm_num⟩
  | 16 => ⟨((1890863767029871/39614081257132168796771975168), (-3927187397479/39614081257132168796771975168)), (104133/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945354168205665/1237940039285380274899124224), (-4172028794941/2475880078570760549798248448)), (110667/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772373884458163/154742504910672534362390528), (-4171344978899/154742504910672534362390528)), (13837/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((775330963794327/4835703278458516698824704), (-3909909389541/9671406556917033397649408)), (811/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((1259757878317461/604462909807314587353088), (-1710222108629/302231454903657293676544)), (90863/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944682795298577/37778931862957161709568), (-5556859731225/75557863725914323419136)), (36927/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298718391502043/4722366482869645213696), (-1041613251263/1180591620717411303424)), (6927/295147905179352825856), by norm_num⟩
  | 9 => ⟨((811533585591031/295147905179352825856), (-178966760521/18446744073709551616)), (152475/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825495465189997/73786976294838206464), (-7155765811873/73786976294838206464)), (190715/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912463123392305/4611686018427387904), (-2011560760513/2305843009213693952)), (214723/9223372036854775808), by norm_num⟩
  | 6 => ⟨((798084814096201/576460752303423488), (-8041251685807/1152921504606846976)), (214933/1152921504606846976), by norm_num⟩
  | 5 => ⟨((299121450289189/36028797018963968), (-7030480660461/144115188075855872)), (188303/144115188075855872), by norm_num⟩
  | 4 => ⟨((93405216293161/2251799813685248), (-1316811706497/4503599627370496)), (17683/2251799813685248), by norm_num⟩
  | 3 => ⟨((746397586834543/4503599627370496), (-6574236642803/4503599627370496)), (354489/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117481493889815/2251799813685248), (-6559507914965/1125899906842624)), (355735/2251799813685248), by norm_num⟩
  | 1 => ⟨((556619117072819/562949953421312), (-19604909241287/1125899906842624)), (268361/562949953421312), by norm_num⟩
  | 0 => ⟨((137555211083485/140737488355328), (-38915538383047/1125899906842624)), (271489/281474976710656), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((137555211083485/140737488355328), (-38915538383047/1125899906842624)), (1035648347021007449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1074214043078013/1125899906842624), (-76071204044687/1125899906842624)), (2197873/1125899906842624), by norm_num⟩
  | 2 => ⟨((509880574322531/562949953421312), (-36289529451963/281474976710656)), (561369/140737488355328), by norm_num⟩
  | 3 => ⟨((904913407424937/1125899906842624), (-65737019805785/281474976710656)), (9293183/1125899906842624), by norm_num⟩
  | 4 => ⟨((665890971314439/1125899906842624), (-845351317286905/2251799813685248)), (38558137/2251799813685248), by norm_num⟩
  | 5 => ⟨((470301261523095/2251799813685248), (-999932243264321/2251799813685248)), (74559207/2251799813685248), by norm_num⟩
  | 6 => ⟨((-691607850570899/4503599627370496), (-417683128479521/2251799813685248)), (194723255/4503599627370496), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47773133/33554432), (-1130054609/33554432)), (1/16777216), by norm_num⟩, -5, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1547083/1048576), (-585530203/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1334074099/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-969979248716473/4503599627370496), (173088437221781/2251799813685248)), (89667843/4503599627370496), by norm_num⟩
  | 1 => ⟨((574662181/1073741824), (-410183533/2147483648)), (27/536870912), by norm_num⟩
  | 2 => ⟨((-1427981875/2147483648), (254816947/1073741824)), (137/2147483648), by norm_num⟩
  | 3 => ⟨((147850069/268435456), (-105532721/536870912)), (115/2147483648), by norm_num⟩
  | 4 => ⟨((-734787239/2147483648), (16389935/134217728)), (145/4294967296), by norm_num⟩
  | 5 => ⟨((1460702157/8589934592), (-130327867/2147483648)), (147/8589934592), by norm_num⟩
  | 6 => ⟨((-604951417/8589934592), (107950861/4294967296)), (31/4294967296), by norm_num⟩
  | 7 => ⟨((429499371/17179869184), (-9580279/1073741824)), (45/17179869184), by norm_num⟩
  | 8 => ⟨((-1067265843/137438953472), (23806099/8589934592)), (57/68719476736), by norm_num⟩
  | 9 => ⟨((1178691551/549755813888), (-420664417/549755813888)), (1/4294967296), by norm_num⟩
  | 10 => ⟨((-1171575389/2199023255552), (418124723/2199023255552)), (129/2199023255552), by norm_num⟩
  | 11 => ⟨((529319177/4398046511104), (-377818511/8796093022208)), (119/8796093022208), by norm_num⟩
  | 12 => ⟨((-876872495/35184372088832), (156473955/17592186044416)), (25/8796093022208), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582053876522139/10141204801825835211973625643008), (911434795345/2535301200456458802993406410752)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889841648766197/316912650057057350374175801344), (1079702368223/158456325028528675187087900672)), (46313/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945385001484515/19807040628566084398385987584), (4857999514889/39614081257132168796771975168)), (13029/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890608471830385/2475880078570760549798248448), (1290211076009/618970019642690137449562112)), (55389/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221534218712933/19342813113834066795298816), (40312237961/1208925819614629174706176)), (27703/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775283882170219/4835703278458516698824704), (4836535805843/9671406556917033397649408)), (51963/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259675198721313/604462909807314587353088), (2115518018253/302231454903657293676544)), (22743/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889230698933387/75557863725914323419136), (214802639935/2361183241434822606848)), (36975/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298616752942819/4722366482869645213696), (2576866409633/2361183241434822606848)), (27747/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622926655363853/590295810358705651712), (3541947663495/295147905179352825856)), (76353/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228164834668207/9223372036854775808), (8851137908001/73786976294838206464)), (95517/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912362895284017/4611686018427387904), (2488099797581/2305843009213693952)), (107561/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797983606179237/576460752303423488), (4972992385797/576460752303423488)), (107691/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196306486509493/144115188075855872), (8695519469179/144115188075855872)), (11797/18014398509481984), by norm_num⟩
  | 4 => ⟨((747105048287623/18014398509481984), (6514421179679/18014398509481984)), (141857/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492445803509167/9007199254740992), (4065195770031/2251799813685248)), (177835/9007199254740992), by norm_num⟩
  | 2 => ⟨((279280167167141/562949953421312), (16222867697815/2251799813685248)), (178607/2251799813685248), by norm_num⟩
  | 1 => ⟨((8692722712693/8796093022208), (24239476981885/1125899906842624)), (134921/562949953421312), by norm_num⟩
  | 0 => ⟨((1099189169414145/1125899906842624), (24049723182181/562949953421312)), (136859/281474976710656), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1099189169414145/1125899906842624), (24049723182181/562949953421312)), (522075654149913699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1071057263694541/1125899906842624), (46958339881907/562949953421312)), (139459/140737488355328), by norm_num⟩
  | 2 => ⟨((126381496309833/140737488355328), (44670996698629/281474976710656)), (2308783/1125899906842624), by norm_num⟩
  | 3 => ⟨((219890354784981/281474976710656), (320914489544995/1125899906842624)), (4879373/1125899906842624), by norm_num⟩
  | 4 => ⟨((1191299824014025/2251799813685248), (501401593749691/1125899906842624)), (20810269/2251799813685248), by norm_num⟩
  | 5 => ⟨((183666876301969/2251799813685248), (1061052810759049/2251799813685248)), (10138529/562949953421312), by norm_num⟩
  | 6 => ⟨((-969979248716473/4503599627370496), (173088437221781/2251799813685248)), (89667843/4503599627370496), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1547083/1048576), (-585530203/16777216)), (1/33554432), by norm_num⟩, -6, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-25550671/16777216), (-1208782083/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1377046701/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-25440299151505/1125899906842624), (1953628390692287/9007199254740992)), (322394351/9007199254740992), by norm_num⟩
  | 1 => ⟨((124460371/2147483648), (-1194705459/2147483648)), (199/2147483648), by norm_num⟩
  | 2 => ⟨((-79808637/1073741824), (383044875/536870912)), (257/2147483648), by norm_num⟩
  | 3 => ⟨((136470075/2147483648), (-163748451/268435456)), (111/1073741824), by norm_num⟩
  | 4 => ⟨((-21877427/536870912), (1680025937/4294967296)), (287/4294967296), by norm_num⟩
  | 5 => ⟨((179566375/8589934592), (-1723672579/8589934592)), (297/8589934592), by norm_num⟩
  | 6 => ⟨((-153526219/17179869184), (736855479/8589934592)), (1/67108864), by norm_num⟩
  | 7 => ⟨((112510565/34359738368), (-1079998279/34359738368)), (189/34359738368), by norm_num⟩
  | 8 => ⟨((-144291951/137438953472), (692535223/68719476736)), (61/34359738368), by norm_num⟩
  | 9 => ⟨((20561197/68719476736), (-789474567/274877906944)), (281/549755813888), by norm_num⟩
  | 10 => ⟨((-168762973/2199023255552), (1619969827/2199023255552)), (145/1099511627776), by norm_num⟩
  | 11 => ⟨((307435/17179869184), (-755480103/4398046511104)), (273/8796093022208), by norm_num⟩
  | 12 => ⟨((-16822511/4398046511104), (645922735/17592186044416)), (235/35184372088832), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790995984726189/5070602400912917605986812821504), (1090675763961/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889808180699945/316912650057057350374175801344), (2583866532001/633825300114114700748351602688)), (46227/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890695083423505/39614081257132168796771975168), (363306620509/4951760157141521099596496896)), (26007/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945264677315365/1237940039285380274899124224), (1543812899485/1237940039285380274899124224)), (27637/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1772195177696615/154742504910672534362390528), (48235708219/2417851639229258349412352)), (110569/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193811835261977/1208925819614629174706176), (2893568320981/9671406556917033397649408)), (51841/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259611830481857/604462909807314587353088), (2531298199051/604462909807314587353088)), (11343/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((236141101255325/9444732965739290427392), (4112283362083/75557863725914323419136)), (147501/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298541284600543/4722366482869645213696), (3083271028649/4722366482869645213696)), (110663/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622824426278619/590295810358705651712), (2118984049263/295147905179352825856)), (152221/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912596599407671/36893488147419103232), (5295166404665/73786976294838206464)), (95183/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456146949307475/2305843009213693952), (2976954683373/4611686018427387904)), (214287/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595833176652793/1152921504606846976), (2974984927785/576460752303423488)), (107221/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196193650897343/144115188075855872), (2600896893683/72057594037927936)), (187813/144115188075855872), by norm_num⟩
  | 4 => ⟨((747024858827975/18014398509481984), (7793836294579/36028797018963968)), (282069/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492260822529779/9007199254740992), (607925755603/562949953421312)), (22075/562949953421312), by norm_num⟩
  | 2 => ⟨((139619856414175/281474976710656), (4851805488779/1125899906842624)), (354121/2251799813685248), by norm_num⟩
  | 1 => ⟨((1112483426541699/1125899906842624), (14497497052237/1125899906842624)), (266745/562949953421312), by norm_num⟩
  | 0 => ⟨((549524004081095/562949953421312), (28763817008745/1125899906842624)), (538119/562949953421312), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((549524004081095/562949953421312), (28763817008745/1125899906842624)), (2052761080028343023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1072101667066829/1125899906842624), (28077820771169/562949953421312)), (539033/281474976710656), by norm_num⟩
  | 2 => ⟨((254518301645677/281474976710656), (213889552870043/2251799813685248)), (8642587/2251799813685248), by norm_num⟩
  | 3 => ⟨((910414738046637/1125899906842624), (193405489796691/1125899906842624)), (17271635/2251799813685248), by norm_num⟩
  | 4 => ⟨((1405896397999535/2251799813685248), (312779505993241/1125899906842624)), (16932927/1125899906842624), by norm_num⟩
  | 5 => ⟨((87997420707451/281474976710656), (781127306559831/2251799813685248)), (15275997/562949953421312), by norm_num⟩
  | 6 => ⟨((-25440299151505/1125899906842624), (1953628390692287/9007199254740992)), (322394351/9007199254740992), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-25550671/16777216), (-1208782083/33554432)), (1/16777216), by norm_num⟩, -6, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-52577791/33554432), (-1243706901/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1416833115/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((757317133834607/4503599627370496), (278270911087887/2251799813685248)), (6027105/281474976710656), by norm_num⟩
  | 1 => ⟨((-953008333/2147483648), (-700352561/2147483648)), (31/536870912), by norm_num⟩
  | 2 => ⟨((314380453/536870912), (57758455/134217728)), (21/268435456), by norm_num⟩
  | 3 => ⟨((-1106224051/2147483648), (-812948661/2147483648)), (75/1073741824), by norm_num⟩
  | 4 => ⟨((182461793/536870912), (268177265/1073741824)), (101/2147483648), by norm_num⟩
  | 5 => ⟨((-770443411/4294967296), (-566188141/4294967296)), (109/4294967296), by norm_num⟩
  | 6 => ⟨((338874055/4294967296), (249033827/4294967296)), (49/4294967296), by norm_num⟩
  | 7 => ⟨((-63879147/2147483648), (-751102339/34359738368)), (75/17179869184), by norm_num⟩
  | 8 => ⟨((168580731/17179869184), (495550533/68719476736)), (101/68719476736), by norm_num⟩
  | 9 => ⟨((-790923047/274877906944), (-145309585/68719476736)), (121/274877906944), by norm_num⟩
  | 10 => ⟨((417458253/549755813888), (76696065/137438953472)), (65/549755813888), by norm_num⟩
  | 11 => ⟨((-801233645/4398046511104), (-294407727/2199023255552)), (127/4398046511104), by norm_num⟩
  | 12 => ⟨((704833841/17592186044416), (129493145/4398046511104)), (113/17592186044416), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581934652443737/10141204801825835211973625643008), (206385081191/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889775763373523/316912650057057350374175801344), (977802627091/633825300114114700748351602688)), (92297/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472655583076957/9903520314283042199192993792), (274968882907/9903520314283042199192993792)), (3245/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((1890452294530893/2475880078570760549798248448), (1168430913517/2475880078570760549798248448)), (110337/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772118385163677/154742504910672534362390528), (584110385977/77371252455336267181195264)), (110345/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775211486628625/4835703278458516698824704), (1094983748919/9671406556917033397649408)), (103457/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259549369264331/604462909807314587353088), (957887612467/604462909807314587353088)), (45267/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1889027842786843/75557863725914323419136), (778074525775/37778931862957161709568)), (147133/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298466024546047/4722366482869645213696), (1166745880739/4722366482869645213696)), (27591/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622721699381665/590295810358705651712), (1603681212337/590295810358705651712)), (37943/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912532961351455/36893488147419103232), (1001855175727/36893488147419103232)), (189749/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912223083582801/4611686018427387904), (1126474719511/4611686018427387904)), (53379/2305843009213693952), by norm_num⟩
  | 6 => ⟨((49865421518341/36028797018963968), (2251419521667/1152921504606846976)), (106787/576460752303423488), by norm_num⟩
  | 5 => ⟨((1196073605216019/144115188075855872), (15377126963/1125899906842624)), (2921/2251799813685248), by norm_num⟩
  | 4 => ⟨((1493874003465233/36028797018963968), (2948972030967/36028797018963968)), (280549/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492048780945999/9007199254740992), (3680208883695/9007199254740992)), (350919/9007199254740992), by norm_num⟩
  | 2 => ⟨((2233516347337579/4503599627370496), (7342429067947/4503599627370496)), (702537/4503599627370496), by norm_num⟩
  | 1 => ⟨((556105343953211/562949953421312), (5484387935881/1125899906842624)), (1055561/2251799813685248), by norm_num⟩
  | 0 => ⟨((2197229704370899/2251799813685248), (10879351823105/1125899906842624)), (2118167/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2197229704370899/2251799813685248), (10879351823105/1125899906842624)), (8080165871627043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2143771796785583/2251799813685248), (42462806586535/2251799813685248)), (2087303/1125899906842624), by norm_num⟩
  | 2 => ⟨((2040125591462641/2251799813685248), (631651447623/17592186044416)), (8106111/2251799813685248), by norm_num⟩
  | 3 => ⟨((461361558116885/562949953421312), (18312793531267/281474976710656)), (15270341/2251799813685248), by norm_num⟩
  | 4 => ⟨((93930664881887/140737488355328), (60032469356899/562949953421312)), (3377047/281474976710656), by norm_num⟩
  | 5 => ⟨((61090519090253/140737488355328), (320533772605531/2251799813685248)), (20912205/1125899906842624), by norm_num⟩
  | 6 => ⟨((757317133834607/4503599627370496), (278270911087887/2251799813685248)), (6027105/281474976710656), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-52577791/33554432), (-1243706901/33554432)), (1/16777216), by norm_num⟩, -6, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-13488083/8388608), (-159527641/4194304)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1453873381/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((851882637025485/4503599627370496), (-296789159203923/4503599627370496)), (37250759/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1100035165/2147483648), (383243533/2147483648)), (49/1073741824), by norm_num⟩
  | 2 => ⟨((1489475225/2147483648), (-518921363/2147483648)), (135/2147483648), by norm_num⟩
  | 3 => ⟨((-1344524561/2147483648), (117105425/536870912)), (31/536870912), by norm_num⟩
  | 4 => ⟨((455130001/1073741824), (-158563685/1073741824)), (43/1073741824), by norm_num⟩
  | 5 => ⟨((-123251489/536870912), (343518735/4294967296)), (95/4294967296), by norm_num⟩
  | 6 => ⟨((890056585/8589934592), (-77522165/2147483648)), (11/1073741824), by norm_num⟩
  | 7 => ⟨((-688662261/17179869184), (479848947/34359738368)), (69/17179869184), by norm_num⟩
  | 8 => ⟨((932465987/68719476736), (-324863759/68719476736)), (95/68719476736), by norm_num⟩
  | 9 => ⟨((-8767933/2147483648), (195499415/137438953472)), (29/68719476736), by norm_num⟩
  | 10 => ⟨((1215692939/1099511627776), (-52942223/137438953472)), (1/8589934592), by norm_num⟩
  | 11 => ⟨((-1197148185/4398046511104), (417076939/4398046511104)), (129/4398046511104), by norm_num⟩
  | 12 => ⟨((540322897/8796093022208), (-376488429/17592186044416)), (119/17592186044416), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790940645795259/5070602400912917605986812821504), (-218344840545/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889744347070299/316912650057057350374175801344), (-517197598969/633825300114114700748351602688)), (92251/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890551676906729/39614081257132168796771975168), (-581764769795/39614081257132168796771975168)), (51893/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890377262504591/2475880078570760549798248448), (-309011837977/1237940039285380274899124224)), (110277/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221505424671313/19342813113834066795298816), (-617909640953/154742504910672534362390528)), (110281/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550352719179915/9671406556917033397649408), (-72396144447/1208925819614629174706176)), (103393/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314871985976029/151115727451828646838272), (-126662977839/151115727451828646838272)), (45237/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472232028644115/18889465931478580854784), (-823082364075/75557863725914323419136)), (147027/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324597826335747/1180591620717411303424), (-77139153167/590295810358705651712)), (55139/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405654771361029/147573952589676412928), (-424104088155/295147905179352825856)), (37911/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824937842582689/73786976294838206464), (-529888343825/36893488147419103232)), (189573/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824302334329451/9223372036854775808), (-595792144863/4611686018427387904)), (213295/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595549977013799/1152921504606846976), (-1190754244977/1152921504606846976)), (106663/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195948393514813/144115188075855872), (-65061058349/9007199254740992)), (23337/18014398509481984), by norm_num⟩
  | 4 => ⟨((1493686906526327/36028797018963968), (-1559601261057/36028797018963968)), (140057/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491816168064373/9007199254740992), (-1946243652837/9007199254740992)), (175133/4503599627370496), by norm_num⟩
  | 2 => ⟨((558263721337133/1125899906842624), (-3882730793127/4503599627370496)), (700905/4503599627370496), by norm_num⟩
  | 1 => ⟨((2223738553500409/2251799813685248), (-5799765205903/2251799813685248)), (1052297/2251799813685248), by norm_num⟩
  | 0 => ⟨((548975327644667/562949953421312), (-11502567422841/2251799813685248)), (1054185/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((548975327644667/562949953421312), (-11502567422841/2251799813685248)), (4021396641257857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2141331670532673/2251799813685248), (-5608514292729/562949953421312)), (4133605/2251799813685248), by norm_num⟩
  | 2 => ⟨((2036059337264851/2251799813685248), (-42666987381977/2251799813685248)), (7944005/2251799813685248), by norm_num⟩
  | 3 => ⟨((460045019085157/562949953421312), (-19289573949707/562949953421312)), (7333429/1125899906842624), by norm_num⟩
  | 4 => ⟨((375289722714991/562949953421312), (-7881759614603/140737488355328)), (24976759/2251799813685248), by norm_num⟩
  | 5 => ⟨((993682802328071/2251799813685248), (-168139614531275/2251799813685248)), (18049499/1125899906842624), by norm_num⟩
  | 6 => ⟨((851882637025485/4503599627370496), (-296789159203923/4503599627370496)), (37250759/2251799813685248), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13488083/8388608), (-159527641/4194304)), (1/16777216), by norm_num⟩, -6, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile040Terms1

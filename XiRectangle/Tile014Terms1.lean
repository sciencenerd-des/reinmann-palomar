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
namespace Reinmann.XiRectangle.Tile014Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨14,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (4089/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (4089/640))
  have he : value ((3/4), (4089/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-55294967/33554432), (-120587264037/8589934592)), (3/8589934592), by norm_num⟩
  | 1 => ⟨((-75496061613/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((2676001499407/140737488355328), (-1724955081300719/9007199254740992)), (1573301/9007199254740992), by norm_num⟩
  | 1 => ⟨((-11483938015/274877906944), (115665090925/274877906944)), (27/68719476736), by norm_num⟩
  | 2 => ⟨((6308197713/137438953472), (-31767772565/68719476736)), (61/137438953472), by norm_num⟩
  | 3 => ⟨((-9240351369/274877906944), (93067907529/274877906944)), (23/68719476736), by norm_num⟩
  | 4 => ⟨((5075781783/274877906944), (-25561386723/137438953472)), (103/549755813888), by norm_num⟩
  | 5 => ⟨((-4461052993/549755813888), (44931285711/549755813888)), (93/1099511627776), by norm_num⟩
  | 6 => ⟨((3267311759/1099511627776), (-4113505219/137438953472)), (35/1099511627776), by norm_num⟩
  | 7 => ⟨((-1025573957/1099511627776), (41317918931/4398046511104)), (45/4398046511104), by norm_num⟩
  | 8 => ⟨((9013665217/35184372088832), (-5674046685/2199023255552)), (101/35184372088832), by norm_num⟩
  | 9 => ⟨((-8802242999/140737488355328), (44327661615/70368744177664)), (101/140737488355328), by norm_num⟩
  | 10 => ⟨((7736201861/562949953421312), (-77918262045/562949953421312)), (91/562949953421312), by norm_num⟩
  | 11 => ⟨((-6181153769/2251799813685248), (124511942101/4503599627370496)), (37/1125899906842624), by norm_num⟩
  | 12 => ⟨((4527127659/9007199254740992), (-22798391613/4503599627370496)), (111/18014398509481984), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677707/5070602400912917605986812821504), (-1917228815281/10141204801825835211973625643008)), (57/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((55607010999019/19807040628566084398385987584), (-567634610833/158456325028528675187087900672)), (543/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945239575630097/19807040628566084398385987584), (-1276990505169/19807040628566084398385987584)), (305/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236287502985725/309485009821345068724781056), (-1356574098351/1237940039285380274899124224)), (81/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885982978122577/77371252455336267181195264), (-1356317291517/77371252455336267181195264)), (649/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387569975768585/2417851639229258349412352), (-317818663549/1208925819614629174706176)), (609/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259424014887935/604462909807314587353088), (-2224185145589/604462909807314587353088)), (133/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888823827212267/75557863725914323419136), (-903319573149/18889465931478580854784)), (865/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298312737715159/4722366482869645213696), (-1354532106837/2361183241434822606848)), (649/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405627620822505/147573952589676412928), (-3723510175785/590295810358705651712)), (223/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912400616636627/36893488147419103232), (-2326104418429/36893488147419103232)), (279/18446744073709551616), by norm_num⟩
  | 7 => ⟨((456036868110073/2305843009213693952), (-5230740267807/9223372036854775808)), (157/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1595393646750849/1152921504606846976), (-5226998860811/1152921504606846976)), (157/144115188075855872), by norm_num⟩
  | 5 => ⟨((1195809955562327/144115188075855872), (-4569417580485/144115188075855872)), (1101/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493475959014051/36028797018963968), (-3422860086939/18014398509481984)), (413/9007199254740992), by norm_num⟩
  | 3 => ⟨((1491546741690911/9007199254740992), (-2135613581839/2251799813685248)), (517/2251799813685248), by norm_num⟩
  | 2 => ⟨((2232498872680967/4503599627370496), (-4260220194591/1125899906842624)), (4145/4503599627370496), by norm_num⟩
  | 1 => ⟨((2222861865242285/2251799813685248), (-25451460644465/2251799813685248)), (195/70368744177664), by norm_num⟩
  | 0 => ⟨((2193978635866131/2251799813685248), (-50464733320615/2251799813685248)), (6287/1125899906842624), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2193978635866131/2251799813685248), (-50464733320615/2251799813685248)), (23983006003951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2136511219198617/2251799813685248), (-24584455975443/562949953421312)), (25067/2251799813685248), by norm_num⟩
  | 2 => ⟨((2022830730542247/2251799813685248), (-46651541305057/562949953421312)), (24879/1125899906842624), by norm_num⟩
  | 3 => ⟨((900839914558889/1125899906842624), (-335263093301671/2251799813685248)), (97645/2251799813685248), by norm_num⟩
  | 4 => ⟨((695809824184859/1125899906842624), (-67061551051101/281474976710656)), (92665/1125899906842624), by norm_num⟩
  | 5 => ⟨((732205914321493/2251799813685248), (-663108125514079/2251799813685248)), (79345/562949953421312), by norm_num⟩
  | 6 => ⟨((2676001499407/140737488355328), (-1724955081300719/9007199254740992)), (1573301/9007199254740992), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/33554432), (-120587264037/8589934592)), (3/8589934592), by norm_num⟩, -2, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-7417145753/4294967296), (-63184810383/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-79116221365/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-108749071909353/1125899906842624), (-1344863320314403/9007199254740992)), (559863/2251799813685248), by norm_num⟩
  | 1 => ⟨((30566893537/137438953472), (23625657909/68719476736)), (5/8589934592), by norm_num⟩
  | 2 => ⟨((-35191436699/137438953472), (-54400087713/137438953472)), (47/68719476736), by norm_num⟩
  | 3 => ⟨((3376303231/17179869184), (20876805171/68719476736)), (37/68719476736), by norm_num⟩
  | 4 => ⟨((-7774225489/68719476736), (-6008827547/34359738368)), (87/274877906944), by norm_num⟩
  | 5 => ⟨((28641305153/549755813888), (44274677555/549755813888)), (41/274877906944), by norm_num⟩
  | 6 => ⟨((-43966028193/2199023255552), (-33982070845/1099511627776)), (1/17179869184), by norm_num⟩
  | 7 => ⟨((7231108651/1099511627776), (2794521777/274877906944)), (43/2199023255552), by norm_num⟩
  | 8 => ⟨((-33300485971/17592186044416), (-25738496743/8796093022208)), (101/17592186044416), by norm_num⟩
  | 9 => ⟨((34078756705/70368744177664), (13170017537/17592186044416)), (105/70368744177664), by norm_num⟩
  | 10 => ⟨((-31387694871/281474976710656), (-6065017211/35184372088832)), (99/281474976710656), by norm_num⟩
  | 11 => ⟨((13140516057/562949953421312), (81252178727/2251799813685248)), (21/281474976710656), by norm_num⟩
  | 12 => ⟨((-40342875183/9007199254740992), (-15590837959/2251799813685248)), (33/2251799813685248), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790863118239471/5070602400912917605986812821504), (-2794088256099/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1779299361304263/633825300114114700748351602688), (-1654277773665/316912650057057350374175801344)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945169189932245/19807040628566084398385987584), (-3721547555195/39614081257132168796771975168)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945075125745155/1237940039285380274899124224), (-3953446297495/2475880078570760549798248448)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885907977933765/77371252455336267181195264), (-3952661133121/154742504910672534362390528)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550139035631993/9671406556917033397649408), (-3704785683419/9671406556917033397649408)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629650256974011/302231454903657293676544), (-3240853465777/604462909807314587353088)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888622684911041/75557863725914323419136), (-2632411688501/37778931862957161709568)), (1155/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298161484715339/4722366482869645213696), (-1973624862365/2361183241434822606848)), (433/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622301867108757/590295810358705651712), (-2712623084433/295147905179352825856)), (149/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1824539499203837/73786976294838206464), (-3389112628523/36893488147419103232)), (745/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911925849071101/4611686018427387904), (-7620922671877/9223372036854775808)), (839/4611686018427387904), by norm_num⟩
  | 6 => ⟨((199387027604275/144115188075855872), (-7615198818549/1152921504606846976)), (105/72057594037927936), by norm_num⟩
  | 5 => ⟨((597773926774893/72057594037927936), (-6656862486237/144115188075855872)), (23/2251799813685248), by norm_num⟩
  | 4 => ⟨((1493079106653433/36028797018963968), (-1246553489295/4503599627370496)), (1105/18014398509481984), by norm_num⟩
  | 3 => ⟨((745522111678363/4503599627370496), (-12443035813457/9007199254740992)), (173/562949953421312), by norm_num⟩
  | 2 => ⟨((278934320136539/562949953421312), (-6204659719413/1125899906842624)), (2777/2251799813685248), by norm_num⟩
  | 1 => ⟨((555319375758155/562949953421312), (-18529801306757/1125899906842624)), (4189/1125899906842624), by norm_num⟩
  | 0 => ⟨((547655020584305/562949953421312), (-36723571539377/1125899906842624)), (4235/562949953421312), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((547655020584305/562949953421312), (-36723571539377/1125899906842624)), (16155245067405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1064353463656231/1125899906842624), (-71451638658455/1125899906842624)), (17033/1125899906842624), by norm_num⟩
  | 2 => ⟨((125204619886303/140737488355328), (-2110805949197/17592186044416)), (34367/1125899906842624), by norm_num⟩
  | 3 => ⟨((874879602210003/1125899906842624), (-480727351756209/2251799813685248)), (138791/2251799813685248), by norm_num⟩
  | 4 => ⟨((157127560225567/281474976710656), (-46693599462071/140737488355328)), (274955/2251799813685248), by norm_num⟩
  | 5 => ⟨((453835049812083/2251799813685248), (-417051715068343/1125899906842624)), (489425/2251799813685248), by norm_num⟩
  | 6 => ⟨((-108749071909353/1125899906842624), (-1344863320314403/9007199254740992)), (559863/2251799813685248), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7417145753/4294967296), (-63184810383/4294967296)), (1/2147483648), by norm_num⟩, -2, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1931040333/1073741824), (-32900099673/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-82391054207/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-1380576720801583/9007199254740992), (-563720873905641/9007199254740992)), (2054373/9007199254740992), by norm_num⟩
  | 1 => ⟨((1578559109/4294967296), (20625970745/137438953472)), (77/137438953472), by norm_num⟩
  | 2 => ⟨((-60563510805/137438953472), (-24729458873/137438953472)), (47/68719476736), by norm_num⟩
  | 3 => ⟨((96816637509/274877906944), (9883108755/68719476736)), (153/274877906944), by norm_num⟩
  | 4 => ⟨((-58039039353/274877906944), (-5924664941/68719476736)), (47/137438953472), by norm_num⟩
  | 5 => ⟨((55668615241/549755813888), (2841345211/68719476736)), (23/137438953472), by norm_num⟩
  | 6 => ⟨((-44495836443/1099511627776), (-36337323999/2199023255552)), (149/2199023255552), by norm_num⟩
  | 7 => ⟨((60969346209/4398046511104), (12447585349/2199023255552)), (13/549755813888), by norm_num⟩
  | 8 => ⟨((-36549526765/8796093022208), (-14924003033/8796093022208)), (127/17592186044416), by norm_num⟩
  | 9 => ⟨((38951972201/35184372088832), (994061009/2199023255552)), (69/35184372088832), by norm_num⟩
  | 10 => ⟨((-74722200005/281474976710656), (-3813846711/35184372088832)), (135/281474976710656), by norm_num⟩
  | 11 => ⟨((65154912787/1125899906842624), (13302116363/562949953421312)), (15/140737488355328), by norm_num⟩
  | 12 => ⟨((-13019554781/1125899906842624), (-21264721297/4503599627370496)), (49/2251799813685248), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790816561182973/5070602400912917605986812821504), (-1793652053001/5070602400912917605986812821504)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889592657017915/316912650057057350374175801344), (-1061830767471/158456325028528675187087900672)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472552469984601/9903520314283042199192993792), (-4777458167597/39614081257132168796771975168)), (51/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1890013464980007/2475880078570760549798248448), (-5075115116189/2475880078570760549798248448)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442919720572705/38685626227668133590597632), (-5074064114127/154742504910672534362390528)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550010224334317/9671406556917033397649408), (-2377909243681/4835703278458516698824704)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629593749727481/302231454903657293676544), (-4160224635353/604462909807314587353088)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((944219232835393/37778931862957161709568), (-1689567921293/18889465931478580854784)), (289/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((81126426336395/295147905179352825856), (-633359031585/590295810358705651712)), (217/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202763799394047/73786976294838206464), (-870496682121/73786976294838206464)), (597/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824298945923915/73786976294838206464), (-8700503538875/73786976294838206464)), (1493/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823579409764519/9223372036854775808), (-9781930370447/9223372036854775808)), (1681/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199352731703515/144115188075855872), (-4887130795595/576460752303423488)), (1683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195305448501053/144115188075855872), (-8543853393647/144115188075855872)), (1475/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492710843930925/36028797018963968), (-3199633453855/9007199254740992)), (2217/36028797018963968), by norm_num⟩
  | 3 => ⟨((372643944044187/2251799813685248), (-7983998493797/4503599627370496)), (2779/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115256710608589/2251799813685248), (-1990345393809/281474976710656)), (2791/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109887783364887/1125899906842624), (-23771136516611/1125899906842624)), (4215/1125899906842624), by norm_num⟩
  | 0 => ⟨((1093688811546369/1125899906842624), (-47090705151921/1125899906842624)), (8549/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1093688811546369/1125899906842624), (-47090705151921/1125899906842624)), (32611851218795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((132553710451289/140737488355328), (-91486955526827/1125899906842624)), (17325/1125899906842624), by norm_num⟩
  | 2 => ⟨((991332572342339/1125899906842624), (-172334117294397/1125899906842624)), (8863/281474976710656), by norm_num⟩
  | 3 => ⟨((846470645579735/1125899906842624), (-151736777631407/562949953421312)), (73283/1125899906842624), by norm_num⟩
  | 4 => ⟨((1109186262987409/2251799813685248), (-57039141463309/140737488355328)), (299393/2251799813685248), by norm_num⟩
  | 5 => ⟨((176484369042785/2251799813685248), (-899078602340323/2251799813685248)), (1075259/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1380576720801583/9007199254740992), (-563720873905641/9007199254740992)), (2054373/9007199254740992), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1931040333/1073741824), (-32900099673/2147483648)), (1/2147483648), by norm_num⟩, -2, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2001111149/1073741824), (-68187862401/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-688647247613739/4503599627370496), (116978253695209/4503599627370496)), (921063/4503599627370496), by norm_num⟩
  | 1 => ⟨((52222415923/137438953472), (-8870850845/137438953472)), (71/137438953472), by norm_num⟩
  | 2 => ⟨((-32441957149/68719476736), (11021618127/137438953472)), (45/68719476736), by norm_num⟩
  | 3 => ⟨((107486980069/274877906944), (-9129230725/137438953472)), (19/34359738368), by norm_num⟩
  | 4 => ⟨((-66773777885/274877906944), (2835660767/68719476736)), (3/8589934592), by norm_num⟩
  | 5 => ⟨((66370641879/549755813888), (-5637081837/274877906944)), (49/274877906944), by norm_num⟩
  | 6 => ⟨((-109949899571/2199023255552), (18676829523/2199023255552)), (41/549755813888), by norm_num⟩
  | 7 => ⟨((9757687021/549755813888), (-13260050823/4398046511104)), (119/4398046511104), by norm_num⟩
  | 8 => ⟨((-96987765461/17592186044416), (16474994233/17592186044416)), (75/8796093022208), by norm_num⟩
  | 9 => ⟨((107113574819/70368744177664), (-9097516161/35184372088832)), (21/8796093022208), by norm_num⟩
  | 10 => ⟨((-106466893741/281474976710656), (4521295681/70368744177664)), (169/281474976710656), by norm_num⟩
  | 11 => ⟨((96203742633/1125899906842624), (-16341814841/1125899906842624)), (155/1125899906842624), by norm_num⟩
  | 12 => ⟨((-19921443317/1125899906842624), (845997591/281474976710656)), (65/2251799813685248), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790774057920435/5070602400912917605986812821504), (3873096942451/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1779083074345351/633825300114114700748351602688), (2292602273193/316912650057057350374175801344)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890094789140535/39614081257132168796771975168), (2578739909103/19807040628566084398385987584)), (51/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((472472771534249/618970019642690137449562112), (684847104871/309485009821345068724781056)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771556396811729/154742504910672534362390528), (1369400149319/38685626227668133590597632)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549895280987009/9671406556917033397649408), (2567000430565/4835703278458516698824704)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629543405458365/302231454903657293676544), (4491001119541/604462909807314587353088)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((472068658732851/18889465931478580854784), (7295533893943/75557863725914323419136)), (1157/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324474940790325/1180591620717411303424), (5469600499709/4722366482869645213696)), (217/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621940889606245/590295810358705651712), (1879342456875/147573952589676412928)), (1195/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912043306979195/36893488147419103232), (4695858227583/36893488147419103232)), (747/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911669959326977/4611686018427387904), (5279406249565/4611686018427387904)), (1683/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594581592173613/1152921504606846976), (10550227994041/1152921504606846976)), (1685/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149386794431461/18014398509481984), (9221793501209/144115188075855872)), (1477/144115188075855872), by norm_num⟩
  | 4 => ⟨((746196240849635/18014398509481984), (1726672779855/4503599627370496)), (555/9007199254740992), by norm_num⟩
  | 3 => ⟨((93135926374263/562949953421312), (17232947820839/9007199254740992)), (1391/4503599627370496), by norm_num⟩
  | 2 => ⟨((139356410098907/281474976710656), (4295574050337/562949953421312)), (2795/2251799813685248), by norm_num⟩
  | 1 => ⟨((554634271028551/562949953421312), (12823440310747/562949953421312)), (4225/1125899906842624), by norm_num⟩
  | 0 => ⟨((273101624077591/281474976710656), (50787907923067/1125899906842624)), (4289/562949953421312), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((273101624077591/281474976710656), (50787907923067/1125899906842624)), (16361238719749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((264404618552901/281474976710656), (98554125836563/1125899906842624)), (17421/1125899906842624), by norm_num⟩
  | 2 => ⟨((984851241691473/1125899906842624), (185154405930853/1125899906842624)), (8945/281474976710656), by norm_num⟩
  | 3 => ⟨((831023973391635/1125899906842624), (161958932119475/562949953421312)), (18591/281474976710656), by norm_num⟩
  | 4 => ⟨((520186615185823/1125899906842624), (59770746261819/140737488355328)), (152565/1125899906842624), by norm_num⟩
  | 5 => ⟨((149041382478357/4503599627370496), (1767372292821751/4503599627370496)), (1082255/4503599627370496), by norm_num⟩
  | 6 => ⟨((-688647247613739/4503599627370496), (116978253695209/4503599627370496)), (921063/4503599627370496), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2001111149/1073741824), (-68187862401/4294967296)), (1/2147483648), by norm_num⟩, -3, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-8262280205/4294967296), (-35192149747/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-44065494425/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-255819223426035/2251799813685248), (826906671087711/9007199254740992)), (233043/1125899906842624), by norm_num⟩
  | 1 => ⟨((40049032761/137438953472), (-32363490825/137438953472)), (37/68719476736), by norm_num⟩
  | 2 => ⟨((-6420233803/17179869184), (41505357499/137438953472)), (97/137438953472), by norm_num⟩
  | 3 => ⟨((43913532181/137438953472), (-2217898751/8589934592)), (85/137438953472), by norm_num⟩
  | 4 => ⟨((-14079498269/68719476736), (45510383811/274877906944)), (111/274877906944), by norm_num⟩
  | 5 => ⟨((28890560031/274877906944), (-23346365943/274877906944)), (29/137438953472), by norm_num⟩
  | 6 => ⟨((-49401882259/1099511627776), (19960748775/549755813888)), (101/1099511627776), by norm_num⟩
  | 7 => ⟨((18101903737/1099511627776), (-29256176997/2199023255552)), (151/4398046511104), by norm_num⟩
  | 8 => ⟨((-46430466359/8796093022208), (37520306195/8796093022208)), (99/8796093022208), by norm_num⟩
  | 9 => ⟨((26464843301/17592186044416), (-42772304563/35184372088832)), (115/35184372088832), by norm_num⟩
  | 10 => ⟨((-3394049141/8796093022208), (43883518043/140737488355328)), (15/17592186044416), by norm_num⟩
  | 11 => ⟨((50650555133/562949953421312), (-40930545967/562949953421312)), (57/281474976710656), by norm_num⟩
  | 12 => ⟨((-43305369615/2251799813685248), (8748731465/562949953421312)), (99/2251799813685248), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917418141/10141204801825835211973625643008), (3206944129187/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778994038802295/633825300114114700748351602688), (3796196862467/633825300114114700748351602688)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472498711117557/9903520314283042199192993792), (4269983806531/39614081257132168796771975168)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889785176485701/2475880078570760549798248448), (4535965492493/2475880078570760549798248448)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771450803759001/154742504910672534362390528), (4534961722043/154742504910672534362390528)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774898311856071/4835703278458516698824704), (4250460252895/9671406556917033397649408)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629500410908959/302231454903657293676544), (1859043261081/302231454903657293676544)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944067766131011/37778931862957161709568), (188746619389/2361183241434822606848)), (1155/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648897993329181/2361183241434822606848), (2264085140011/2361183241434822606848)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621799090697601/590295810358705651712), (3111696666067/295147905179352825856)), (1193/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823910704635397/73786976294838206464), (3887490798061/36893488147419103232)), (373/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823143860008627/9223372036854775808), (8740998547207/9223372036854775808)), (105/576460752303423488), by norm_num⟩
  | 6 => ⟨((398596957347423/288230376151711744), (8528985971/1125899906842624)), (841/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194927391299601/144115188075855872), (7633743720035/144115188075855872)), (1473/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492147180641797/36028797018963968), (11434169716619/36028797018963968)), (1107/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489877174081605/9007199254740992), (14263953425185/9007199254740992)), (1387/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114567049265717/2251799813685248), (14220858520343/2251799813685248)), (87/70368744177664), by norm_num⟩
  | 1 => ⟨((554437778244683/562949953421312), (1326481378811/70368744177664)), (4203/1125899906842624), by norm_num⟩
  | 0 => ⟨((136469112199191/140737488355328), (42017973890559/1125899906842624)), (133/17592186044416), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((136469112199191/140737488355328), (42017973890559/1125899906842624)), (507354803436989/67108864000000000000000000), by norm_num⟩
  | 1 => ⟨((1057073432585651/1125899906842624), (81487252050087/1125899906842624)), (2143/140737488355328), by norm_num⟩
  | 2 => ⟨((246639169006299/281474976710656), (153011841839681/1125899906842624)), (34675/1125899906842624), by norm_num⟩
  | 3 => ⟨((421832103144265/562949953421312), (536299374963707/2251799813685248)), (140385/2251799813685248), by norm_num⟩
  | 4 => ⟨((1136628636679119/2251799813685248), (401862175990955/1125899906842624)), (277259/2251799813685248), by norm_num⟩
  | 5 => ⟨((143430117505237/1125899906842624), (1622766124958387/4503599627370496)), (477823/2251799813685248), by norm_num⟩
  | 6 => ⟨((-255819223426035/2251799813685248), (826906671087711/9007199254740992)), (233043/1125899906842624), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8262280205/4294967296), (-35192149747/2147483648)), (1/2147483648), by norm_num⟩, -3, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-2125249673/1073741824), (-36208941305/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-504793131412545/9007199254740992), (17773778422735/140737488355328)), (1714219/9007199254740992), by norm_num⟩
  | 1 => ⟨((5081855825/34359738368), (-91613320745/274877906944)), (141/274877906944), by norm_num⟩
  | 2 => ⟨((-13411308863/68719476736), (60443201401/137438953472)), (95/137438953472), by norm_num⟩
  | 3 => ⟨((23595475303/137438953472), (-53171024561/137438953472)), (85/137438953472), by norm_num⟩
  | 4 => ⟨((-15567453011/137438953472), (35080345523/137438953472)), (57/137438953472), by norm_num⟩
  | 5 => ⟨((16433360389/274877906944), (-74063234383/549755813888)), (123/549755813888), by norm_num⟩
  | 6 => ⟨((-14456193395/549755813888), (65152373851/1099511627776)), (55/549755813888), by norm_num⟩
  | 7 => ⟨((21800413221/2199023255552), (-49125957073/2199023255552)), (85/2199023255552), by norm_num⟩
  | 8 => ⟨((-14383135075/4398046511104), (1012861071/137438953472)), (57/4398046511104), by norm_num⟩
  | 9 => ⟨((33740371593/35184372088832), (-19007988859/8796093022208)), (17/4398046511104), by norm_num⟩
  | 10 => ⟨((-35617109983/140737488355328), (313519827/549755813888)), (73/70368744177664), by norm_num⟩
  | 11 => ⟨((17090108211/281474976710656), (-77023120051/562949953421312)), (71/281474976710656), by norm_num⟩
  | 12 => ⟨((-15033925113/1125899906842624), (33878071587/1125899906842624)), (127/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581397516987371/10141204801825835211973625643008), (2590182958085/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778911019741613/633825300114114700748351602688), (3065829116261/633825300114114700748351602688)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944950808864155/19807040628566084398385987584), (3448451198799/39614081257132168796771975168)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((59052698144963/77371252455336267181195264), (1831619322143/1237940039285380274899124224)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885676106265689/77371252455336267181195264), (3662405445251/154742504910672534362390528)), (865/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549704454204901/9671406556917033397649408), (3432620009809/9671406556917033397649408)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258920433111133/604462909807314587353088), (3002657614547/604462909807314587353088)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944002693526703/37778931862957161709568), (1219414968653/18889465931478580854784)), (577/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648849401527119/2361183241434822606848), (3656793927853/4722366482869645213696)), (433/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621666153734863/590295810358705651712), (1256433653137/147573952589676412928)), (1191/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911872784040469/36893488147419103232), (196207315949/2305843009213693952)), (1489/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822959502256077/9223372036854775808), (7058606188945/9223372036854775808)), (1677/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398551311267747/288230376151711744), (7052538124937/1152921504606846976)), (839/576460752303423488), by norm_num⟩
  | 5 => ⟨((597384810742685/72057594037927936), (6164148986393/144115188075855872)), (735/72057594037927936), by norm_num⟩
  | 4 => ⟨((745957249867949/18014398509481984), (9232591481419/36028797018963968)), (2209/36028797018963968), by norm_num⟩
  | 3 => ⟨((372398314160049/2251799813685248), (5758454893575/4503599627370496)), (1383/4503599627370496), by norm_num⟩
  | 2 => ⟨((2228586982877605/4503599627370496), (22962436608275/4503599627370496)), (1387/1125899906842624), by norm_num⟩
  | 1 => ⟨((1108490975784669/1125899906842624), (17132783769621/1125899906842624)), (2091/562949953421312), by norm_num⟩
  | 0 => ⟨((2182171808276291/2251799813685248), (67821005776025/2251799813685248)), (4225/562949953421312), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2182171808276291/2251799813685248), (67821005776025/2251799813685248)), (16117098094749273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2112654101443277/2251799813685248), (131447818686135/2251799813685248)), (16887/1125899906842624), by norm_num⟩
  | 2 => ⟨((987216713556673/1125899906842624), (123325249245203/1125899906842624)), (33659/1125899906842624), by norm_num⟩
  | 3 => ⟨((426053735591235/562949953421312), (432538439761767/2251799813685248)), (2075/35184372088832), by norm_num⟩
  | 4 => ⟨((1206705432425355/2251799813685248), (654710483329187/2251799813685248)), (252031/2251799813685248), by norm_num⟩
  | 5 => ⟨((456298191970339/2251799813685248), (701698874027521/2251799813685248)), (104169/562949953421312), by norm_num⟩
  | 6 => ⟨((-504793131412545/9007199254740992), (17773778422735/140737488355328)), (1714219/9007199254740992), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2125249673/1073741824), (-36208941305/2147483648)), (1/2147483648), by norm_num⟩, -3, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-8723240287/4294967296), (-74311103197/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-93047896397/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((13672906144745/4503599627370496), (295355475549413/2251799813685248)), (368473/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1129971809/137438953472), (-24409102019/68719476736)), (31/68719476736), by norm_num⟩
  | 2 => ⟨((3060020385/274877906944), (66101073631/137438953472)), (85/137438953472), by norm_num⟩
  | 3 => ⟨((-1381114803/137438953472), (-59668341913/137438953472)), (39/68719476736), by norm_num⟩
  | 4 => ⟨((935032055/137438953472), (40396216329/137438953472)), (107/274877906944), by norm_num⟩
  | 5 => ⟨((-506422749/137438953472), (-87515985403/549755813888)), (59/274877906944), by norm_num⟩
  | 6 => ⟨((457139409/274877906944), (39499613645/549755813888)), (27/274877906944), by norm_num⟩
  | 7 => ⟨((-2829614785/4398046511104), (-30561981907/1099511627776)), (169/4398046511104), by norm_num⟩
  | 8 => ⟨((957842361/4398046511104), (82763381249/8796093022208)), (29/2199023255552), by norm_num⟩
  | 9 => ⟨((-576418933/8796093022208), (-49806086941/17592186044416)), (141/35184372088832), by norm_num⟩
  | 10 => ⟨((624388563/35184372088832), (107901907005/140737488355328)), (155/140737488355328), by norm_num⟩
  | 11 => ⟨((-614863845/140737488355328), (-53127960175/281474976710656)), (155/562949953421312), by norm_num⟩
  | 12 => ⟨((2220109545/2251799813685248), (47957727745/1125899906842624)), (71/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798723/10141204801825835211973625643008), (2015992044911/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778833225242149/633825300114114700748351602688), (2385993374139/633825300114114700748351602688)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944907113764673/19807040628566084398385987584), (2683761909963/39614081257132168796771975168)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889593653860585/2475880078570760549798248448), (2850905860775/2475880078570760549798248448)), (27/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1771259711603623/154742504910672534362390528), (712560242693/38685626227668133590597632)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1549617931942421/9671406556917033397649408), (2671394641875/9671406556917033397649408)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629422461683169/302231454903657293676544), (2336764242945/604462909807314587353088)), (355/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887883053273475/75557863725914323419136), (1897959219943/37778931862957161709568)), (1153/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324401843955081/1180591620717411303424), (1422890615339/2361183241434822606848)), (865/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810770482920171/295147905179352825856), (1955534443915/295147905179352825856)), (595/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823589869189091/73786976294838206464), (4886017043033/73786976294838206464)), (1487/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911392710168427/4611686018427387904), (5492895214179/9223372036854775808)), (837/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797016255123053/576460752303423488), (5488056150027/1152921504606846976)), (419/288230376151711744), by norm_num⟩
  | 5 => ⟨((597309995573343/72057594037927936), (4796609835981/144115188075855872)), (367/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491693072382113/36028797018963968), (1796011946509/9007199254740992)), (2203/36028797018963968), by norm_num⟩
  | 3 => ⟨((93082608639909/562949953421312), (8961068670259/9007199254740992)), (1379/4503599627370496), by norm_num⟩
  | 2 => ⟨((69626864988785/140737488355328), (4466317145799/1125899906842624)), (5529/4503599627370496), by norm_num⟩
  | 1 => ⟨((1108115053910165/1125899906842624), (26656096048843/2251799813685248)), (4163/1125899906842624), by norm_num⟩
  | 0 => ⟨((2180823232378133/2251799813685248), (52747151708235/2251799813685248)), (8393/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2180823232378133/2251799813685248), (52747151708235/2251799813685248)), (32016758445357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1055424127841959/1125899906842624), (102169129944845/2251799813685248)), (33301/2251799813685248), by norm_num⟩
  | 2 => ⟨((1974083930727023/2251799813685248), (95773846510747/1125899906842624)), (4091/140737488355328), by norm_num⟩
  | 3 => ⟨((107145316143109/140737488355328), (167923995935821/1125899906842624)), (125903/2251799813685248), by norm_num⟩
  | 4 => ⟨((1255047857567213/2251799813685248), (511371059490037/2251799813685248)), (57315/562949953421312), by norm_num⟩
  | 5 => ⟨((291687732700849/1125899906842624), (570028604438419/2251799813685248)), (179843/1125899906842624), by norm_num⟩
  | 6 => ⟨((13672906144745/4503599627370496), (295355475549413/2251799813685248)), (368473/2251799813685248), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8723240287/4294967296), (-74311103197/4294967296)), (1/2147483648), by norm_num⟩, -3, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile014Terms1

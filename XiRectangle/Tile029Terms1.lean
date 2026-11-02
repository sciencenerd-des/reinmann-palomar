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
namespace Reinmann.XiRectangle.Tile029Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨29,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (1551/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (1551/128))
  have he : value ((5/8), (1551/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-368633113/268435456), (-7146874485/268435456)), (3/268435456), by norm_num⟩
  | 1 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((90422941774827/4503599627370496), (-1137075581332831/4503599627370496)), (16597095/2251799813685248), by norm_num⟩
  | 1 => ⟨((-94737773/2147483648), (4765339687/8589934592)), (141/8589934592), by norm_num⟩
  | 2 => ⟨((208160163/4294967296), (-1308815185/2147483648)), (157/8589934592), by norm_num⟩
  | 3 => ⟨((-609832835/17179869184), (7668695711/17179869184)), (233/17179869184), by norm_num⟩
  | 4 => ⟨((334984923/17179869184), (-4212461673/17179869184)), (65/8589934592), by norm_num⟩
  | 5 => ⟨((-588829685/68719476736), (7404579455/68719476736)), (231/68719476736), by norm_num⟩
  | 6 => ⟨((431263685/137438953472), (-5423174655/137438953472)), (43/34359738368), by norm_num⟩
  | 7 => ⟨((-2115141/2147483648), (6809104365/549755813888)), (219/549755813888), by norm_num⟩
  | 8 => ⟨((594872293/2199023255552), (-7480565731/2199023255552)), (243/2199023255552), by norm_num⟩
  | 9 => ⟨((-580919121/8796093022208), (7305103501/8796093022208)), (15/549755813888), by norm_num⟩
  | 10 => ⟨((127640977/8796093022208), (-6420381181/35184372088832)), (213/35184372088832), by norm_num⟩
  | 11 => ⟨((-407935843/140737488355328), (2564912605/70368744177664)), (43/35184372088832), by norm_num⟩
  | 12 => ⟨((597551107/1125899906842624), (-1878563005/281474976710656)), (255/1125899906842624), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582186935648693/10141204801825835211973625643008), (-30355755681/158456325028528675187087900672)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779848069990271/633825300114114700748351602688), (-2301826618289/633825300114114700748351602688)), (17331/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890955763865935/39614081257132168796771975168), (-2589235630615/39614081257132168796771975168)), (4875/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236350792626705/309485009821345068724781056), (-1375338457971/1237940039285380274899124224)), (10361/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221559022391539/19342813113834066795298816), (-1375121389081/77371252455336267181195264)), (20725/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193844298363057/1208925819614629174706176), (-2577891392255/9671406556917033397649408)), (9717/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259839088117317/604462909807314587353088), (-2255193822431/604462909807314587353088)), (1063/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((236187266686397/9444732965739290427392), (-3663825454375/75557863725914323419136)), (27645/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298818303180247/4722366482869645213696), (-2747112788385/4722366482869645213696)), (5185/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811602684463233/295147905179352825856), (-3776051357591/590295810358705651712)), (1783/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1825669440034425/73786976294838206464), (-4718221571057/73786976294838206464)), (17837/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1825123654708939/9223372036854775808), (-663183301305/1152921504606846976)), (20077/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1596369141177877/1152921504606846976), (-5302301469849/1152921504606846976)), (10045/288230376151711744), by norm_num⟩
  | 5 => ⟨((598331369737745/72057594037927936), (-4635954782893/144115188075855872)), (35187/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494753587743237/36028797018963968), (-868352257011/4503599627370496)), (52839/36028797018963968), by norm_num⟩
  | 3 => ⟨((1493141070743037/9007199254740992), (-8671081613929/9007199254740992)), (33075/4503599627370496), by norm_num⟩
  | 2 => ⟨((1117839706391009/2251799813685248), (-4326218843471/1125899906842624)), (259/8796093022208), by norm_num⟩
  | 1 => ⟨((1113806194762621/1125899906842624), (-12932108014163/1125899906842624)), (99841/1125899906842624), by norm_num⟩
  | 0 => ⟨((550849649202235/562949953421312), (-12839194987257/562949953421312)), (25153/140737488355328), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((550849649202235/562949953421312), (-12839194987257/562949953421312)), (95951080859136537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((269358305525373/281474976710656), (-1570402930977/35184372088832)), (402977/1125899906842624), by norm_num⟩
  | 2 => ⟨((1028809921480451/1125899906842624), (-192358617132433/2251799813685248)), (807233/1125899906842624), by norm_num⟩
  | 3 => ⟨((931876260726071/1125899906842624), (-87885456151729/562949953421312)), (3226321/2251799813685248), by norm_num⟩
  | 4 => ⟨((1487695214473231/2251799813685248), (-581922920523527/2251799813685248)), (6348035/2251799813685248), by norm_num⟩
  | 5 => ⟨((832490861018407/2251799813685248), (-192229331131863/562949953421312)), (11668897/2251799813685248), by norm_num⟩
  | 6 => ⟨((90422941774827/4503599627370496), (-1137075581332831/4503599627370496)), (16597095/2251799813685248), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-368633113/268435456), (-7146874485/268435456)), (3/268435456), by norm_num⟩, -4, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-386309675/268435456), (-117024669/4194304)), (3/268435456), by norm_num⟩
  | 1 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-497174927916153/2251799813685248), (-48707043664951/562949953421312)), (17513399/2251799813685248), by norm_num⟩
  | 1 => ⟨((2183509021/4294967296), (855652715/4294967296)), (39/2147483648), by norm_num⟩
  | 2 => ⟨((-2513857661/4294967296), (-985106593/4294967296)), (91/4294967296), by norm_num⟩
  | 3 => ⟨((3858914117/8589934592), (189024313/1073741824)), (71/4294967296), by norm_num⟩
  | 4 => ⟨((-1110684765/4294967296), (-1740978261/17179869184)), (83/8589934592), by norm_num⟩
  | 5 => ⟨((1022978473/8589934592), (400875059/8589934592)), (155/34359738368), by norm_num⟩
  | 6 => ⟨((-392582497/8589934592), (-1230731913/68719476736)), (121/68719476736), by norm_num⟩
  | 7 => ⟨((2066181955/137438953472), (404837851/68719476736)), (161/274877906944), by norm_num⟩
  | 8 => ⟨((-4757559769/1099511627776), (-1864347201/1099511627776)), (47/274877906944), by norm_num⟩
  | 9 => ⟨((4868749423/4398046511104), (238489893/549755813888)), (195/4398046511104), by norm_num⟩
  | 10 => ⟨((-4484283937/17592186044416), (-219657309/2199023255552)), (91/8796093022208), by norm_num⟩
  | 11 => ⟨((1877353699/35184372088832), (183919871/8796093022208)), (77/35184372088832), by norm_num⟩
  | 12 => ⟨((-5763688855/562949953421312), (-564654871/140737488355328)), (239/562949953421312), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((791050579124123/5070602400912917605986812821504), (-3605777643047/10141204801825835211973625643008)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779739527256143/633825300114114700748351602688), (-533965741165/79228162514264337593543950336)), (17367/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945416632443535/19807040628566084398385987584), (-2402526623941/19807040628566084398385987584)), (19543/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890675693548077/2475880078570760549798248448), (-2552308176173/1237940039285380274899124224)), (10385/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1772340978074423/154742504910672534362390528), (-2551884698925/77371252455336267181195264)), (20777/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193828849748969/1208925819614629174706176), (-298992742365/604462909807314587353088)), (19485/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629865180101133/302231454903657293676544), (-2092499205723/302231454903657293676544)), (17057/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889320349495399/75557863725914323419136), (-6798934849187/75557863725914323419136)), (13865/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298684002338237/4722366482869645213696), (-5097724410281/4722366482869645213696)), (20809/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623019141858095/590295810358705651712), (-7006971190463/590295810358705651712)), (28631/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825434313205123/73786976294838206464), (-4377556920857/36893488147419103232)), (35817/73786976294838206464), by norm_num⟩
  | 7 => ⟨((456213979714299/2305843009213693952), (-2461138082063/2305843009213693952)), (10083/2305843009213693952), by norm_num⟩
  | 6 => ⟨((798048693892845/576460752303423488), (-4919181545427/576460752303423488)), (10095/288230376151711744), by norm_num⟩
  | 5 => ⟨((1196420442632021/144115188075855872), (-134400057987/2251799813685248)), (35387/144115188075855872), by norm_num⟩
  | 4 => ⟨((747190567495637/18014398509481984), (-3222118713837/9007199254740992)), (53189/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492659781655021/9007199254740992), (-16086208771539/9007199254740992)), (16669/2251799813685248), by norm_num⟩
  | 2 => ⟨((1117334912450941/2251799813685248), (-8024809832195/1125899906842624)), (33481/1125899906842624), by norm_num⟩
  | 1 => ⟨((278247630274325/281474976710656), (-23982915915947/1125899906842624)), (101159/1125899906842624), by norm_num⟩
  | 0 => ⟨((1099835694925861/1125899906842624), (-23799769807239/562949953421312)), (25649/140737488355328), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1099835694925861/1125899906842624), (-23799769807239/562949953421312)), (97843170702886537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((67022656294965/70368744177664), (-92995251908051/1125899906842624)), (418235/1125899906842624), by norm_num⟩
  | 2 => ⟨((1013689768633527/1125899906842624), (-177146512376595/1125899906842624)), (865785/1125899906842624), by norm_num⟩
  | 3 => ⟨((442395480331249/562949953421312), (-159491626257295/562949953421312)), (1831439/1125899906842624), by norm_num⟩
  | 4 => ⟨((302471260786987/562949953421312), (-1002694810479569/2251799813685248)), (1958113/562949953421312), by norm_num⟩
  | 5 => ⟨((25447695876671/281474976710656), (-538744806118395/1125899906842624)), (15392067/2251799813685248), by norm_num⟩
  | 6 => ⟨((-497174927916153/2251799813685248), (-48707043664951/562949953421312)), (17513399/2251799813685248), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-386309675/268435456), (-117024669/4194304)), (3/268435456), by norm_num⟩, -4, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-402300069/268435456), (-7799592595/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-714329054524155/4503599627370496), (354328912351645/2251799813685248)), (22676005/4503599627370496), by norm_num⟩
  | 1 => ⟨((408383909/1073741824), (-3241133209/8589934592)), (53/4294967296), by norm_num⟩
  | 2 => ⟨((-979261845/2147483648), (485743625/1073741824)), (65/4294967296), by norm_num⟩
  | 3 => ⟨((3130889799/8589934592), (-3106032913/8589934592)), (53/4294967296), by norm_num⟩
  | 4 => ⟨((-938443231/4294967296), (930992705/4294967296)), (65/8589934592), by norm_num⟩
  | 5 => ⟨((900115435/8589934592), (-1785938405/17179869184)), (127/34359738368), by norm_num⟩
  | 6 => ⟨((-2877843395/68719476736), (1427497753/34359738368)), (13/8589934592), by norm_num⟩
  | 7 => ⟨((1971647735/137438953472), (-1955994351/137438953472)), (145/274877906944), by norm_num⟩
  | 8 => ⟨((-295487799/68719476736), (586283701/137438953472)), (89/549755813888), by norm_num⟩
  | 9 => ⟨((2519284609/2199023255552), (-2499283405/2199023255552)), (97/2199023255552), by norm_num⟩
  | 10 => ⟨((-1208196131/4398046511104), (2397207945/8796093022208)), (95/8796093022208), by norm_num⟩
  | 11 => ⟨((1053501015/17592186044416), (-522568509/8796093022208)), (21/8796093022208), by norm_num⟩
  | 12 => ⟨((-3368246805/281474976710656), (3341505487/281474976710656)), (137/281474976710656), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197752945394709/1267650600228229401496703205376), (768599461989/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889825133452555/316912650057057350374175801344), (3641848318399/633825300114114700748351602688)), (11571/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118170813548023/2475880078570760549798248448), (512065042067/4951760157141521099596496896)), (3255/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890569392639363/2475880078570760549798248448), (4351885438709/2475880078570760549798248448)), (13837/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1772234916398941/154742504910672534362390528), (271945910347/9671406556917033397649408)), (13841/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550531619258897/9671406556917033397649408), (4078390885731/9671406556917033397649408)), (12979/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259643832789511/604462909807314587353088), (1783897146427/302231454903657293676544)), (11361/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472295054606701/18889465931478580854784), (5796170057571/75557863725914323419136)), (18469/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649289660142107/2361183241434822606848), (4345818913107/4722366482869645213696)), (6929/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((6339358906249/2305843009213693952), (2986687315787/295147905179352825856)), (9533/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1825256249067727/73786976294838206464), (1865882247959/18446744073709551616)), (2981/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1824656988592067/9223372036854775808), (1049010657647/1152921504606846976)), (13425/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595900195520933/1152921504606846976), (4193302420173/576460752303423488)), (13439/576460752303423488), by norm_num⟩
  | 5 => ⟨((598124926045329/72057594037927936), (7332114657119/144115188075855872)), (23549/144115188075855872), by norm_num⟩
  | 4 => ⟨((1494129148157589/36028797018963968), (1373230635293/4503599627370496)), (35385/36028797018963968), by norm_num⟩
  | 3 => ⟨((1492351606914725/9007199254740992), (13710739382355/9007199254740992)), (44339/9007199254740992), by norm_num⟩
  | 2 => ⟨((1117036922079699/2251799813685248), (1709799906143/281474976710656)), (22251/1125899906842624), by norm_num⟩
  | 1 => ⟨((1112568895487671/1125899906842624), (10218392564227/562949953421312)), (67159/1125899906842624), by norm_num⟩
  | 0 => ⟨((1099093277192425/1125899906842624), (20275269229553/562949953421312)), (67975/562949953421312), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1099093277192425/1125899906842624), (20275269229553/562949953421312)), (259304048778343023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1071464415680855/1125899906842624), (79170135704019/1125899906842624)), (68805/281474976710656), by norm_num⟩
  | 2 => ⟨((1014093772229539/1125899906842624), (37671192028679/281474976710656)), (562533/1125899906842624), by norm_num⟩
  | 3 => ⟨((223305880349789/281474976710656), (271442397297125/1125899906842624)), (1163917/1125899906842624), by norm_num⟩
  | 4 => ⟨((160797438504345/281474976710656), (861386460722595/2251799813685248)), (4815969/2251799813685248), by norm_num⟩
  | 5 => ⟨((405358237632015/2251799813685248), (246040941303457/562949953421312)), (2296735/562949953421312), by norm_num⟩
  | 6 => ⟨((-714329054524155/4503599627370496), (354328912351645/2251799813685248)), (22676005/4503599627370496), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-402300069/268435456), (-7799592595/268435456)), (1/134217728), by norm_num⟩, -5, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-104224539/67108864), (-1010326625/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((249540865530975/4503599627370496), (919700405583723/4503599627370496)), (8673393/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1182719719/8589934592), (-1089749171/2147483648)), (21/2147483648), by norm_num⟩
  | 2 => ⟨((1469474047/8589934592), (5415849923/8589934592)), (53/4294967296), by norm_num⟩
  | 3 => ⟨((-608584305/4294967296), (-280372531/536870912)), (45/4294967296), by norm_num⟩
  | 4 => ⟨((756137593/8589934592), (5573596533/17179869184)), (57/8589934592), by norm_num⟩
  | 5 => ⟨((-751572533/17179869184), (-5539946835/34359738368)), (115/34359738368), by norm_num⟩
  | 6 => ⟨((622529195/34359738368), (4588750243/68719476736)), (97/68719476736), by norm_num⟩
  | 7 => ⟨((-1767916499/274877906944), (-6515780567/274877906944)), (35/68719476736), by norm_num⟩
  | 8 => ⟨((549138433/274877906944), (4047776615/549755813888)), (89/549755813888), by norm_num⟩
  | 9 => ⟨((-1212940217/2199023255552), (-558797057/274877906944)), (101/2199023255552), by norm_num⟩
  | 10 => ⟨((301404321/2199023255552), (4443387273/8796093022208)), (51/4398046511104), by norm_num⟩
  | 11 => ⟨((-1089398693/35184372088832), (-1003763871/8796093022208)), (47/17592186044416), by norm_num⟩
  | 12 => ⟨((112793919/17592186044416), (3325679357/140737488355328)), (79/140737488355328), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581952724385157/10141204801825835211973625643008), (1701011178407/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889785636922801/316912650057057350374175801344), (2014791040485/633825300114114700748351602688)), (11551/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890644448360645/39614081257132168796771975168), (1133163204661/19807040628566084398385987584)), (3249/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945237833306125/1237940039285380274899124224), (601897493867/618970019642690137449562112)), (6905/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((886070807660215/77371252455336267181195264), (2407160488329/154742504910672534362390528)), (3453/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550444600804801/9671406556917033397649408), (1128128355405/4835703278458516698824704)), (12951/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259568142723331/604462909807314587353088), (246721058551/75557863725914323419136)), (11335/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944529033683293/37778931862957161709568), (3206518671807/75557863725914323419136)), (9211/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649244223072239/2361183241434822606848), (2404140999195/4722366482869645213696)), (3455/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811376064142959/295147905179352825856), (3304478738497/590295810358705651712)), (19009/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228137919774335/9223372036854775808), (4128776371221/73786976294838206464)), (11885/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912243728555985/4611686018427387904), (4642369154229/9223372036854775808)), (209/72057594037927936), by norm_num⟩
  | 6 => ⟨((199466718581133/144115188075855872), (2319620205779/576460752303423488)), (1673/72057594037927936), by norm_num⟩
  | 5 => ⟨((1196107675995723/144115188075855872), (4055817705521/144115188075855872)), (23439/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493922800692905/36028797018963968), (3038348349755/18014398509481984)), (4399/4503599627370496), by norm_num⟩
  | 3 => ⟨((373026436796209/2251799813685248), (947947609977/1125899906842624)), (22025/4503599627370496), by norm_num⟩
  | 2 => ⟨((2233618230266933/4503599627370496), (15130340783255/4503599627370496)), (44139/2251799813685248), by norm_num⟩
  | 1 => ⟨((2224544220702081/2251799813685248), (22603630143493/2251799813685248)), (132867/2251799813685248), by norm_num⟩
  | 0 => ⟨((17166846404437/17592186044416), (44840763688049/2251799813685248)), (267539/2251799813685248), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((17166846404437/17592186044416), (44840763688049/2251799813685248)), (1020580300337981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2143336259510337/2251799813685248), (43756614496169/1125899906842624)), (532797/2251799813685248), by norm_num⟩
  | 2 => ⟨((127293502296763/140737488355328), (166595872107419/2251799813685248)), (1055681/2251799813685248), by norm_num⟩
  | 3 => ⟨((1829814771482419/2251799813685248), (37670439263481/281474976710656)), (258235/281474976710656), by norm_num⟩
  | 4 => ⟨((1446577138208761/2251799813685248), (489776583468063/2251799813685248)), (977609/562949953421312), by norm_num⟩
  | 5 => ⟨((822765995367281/2251799813685248), (314637031306695/1125899906842624)), (6725277/2251799813685248), by norm_num⟩
  | 6 => ⟨((249540865530975/4503599627370496), (919700405583723/4503599627370496)), (8673393/2251799813685248), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-104224539/67108864), (-1010326625/33554432)), (1/134217728), by norm_num⟩, -5, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-215163547/134217728), (-4171483267/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((855778570716163/4503599627370496), (74707620873703/1125899906842624)), (4681143/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1046671245/2147483648), (-1461954225/8589934592)), (47/4294967296), by norm_num⟩
  | 2 => ⟨((5369317475/8589934592), (1874919275/8589934592)), (123/8589934592), by norm_num⟩
  | 3 => ⟨((-2295337901/4294967296), (-801512165/4294967296)), (107/8589934592), by norm_num⟩
  | 4 => ⟨((2943712737/8589934592), (2055838113/17179869184)), (35/4294967296), by norm_num⟩
  | 5 => ⟨((-6040379275/34359738368), (-2109248259/34359738368)), (73/17179869184), by norm_num⟩
  | 6 => ⟨((5164422313/68719476736), (225421457/8589934592)), (127/68719476736), by norm_num⟩
  | 7 => ⟨((-3784709055/137438953472), (-660793853/68719476736)), (95/137438953472), by norm_num⟩
  | 8 => ⟨((4853793529/549755813888), (1694902769/549755813888)), (31/137438953472), by norm_num⟩
  | 9 => ⟨((-5533215375/2199023255552), (-60379719/68719476736)), (9/137438953472), by norm_num⟩
  | 10 => ⟨((709620861/1099511627776), (1982347795/8796093022208)), (75/4398046511104), by norm_num⟩
  | 11 => ⟨((-5294957299/35184372088832), (-1848953347/35184372088832)), (71/17592186044416), by norm_num⟩
  | 12 => ⟨((4527099107/140737488355328), (395205975/35184372088832)), (123/140737488355328), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395471889758183/2535301200456458802993406410752), (54702239427/1267650600228229401496703205376)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889748058233365/316912650057057350374175801344), (518301074617/633825300114114700748351602688)), (2883/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1890560025804347/39614081257132168796771975168), (583006241959/39614081257132168796771975168)), (25947/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890386131710317/2475880078570760549798248448), (619342827447/2475880078570760549798248448)), (13785/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443013066222861/38685626227668133590597632), (619228890535/154742504910672534362390528)), (27571/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550361030691143/9671406556917033397649408), (580406056161/9671406556917033397649408)), (25849/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629747607343639/302231454903657293676544), (253867151669/302231454903657293676544)), (22619/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888939926245453/75557863725914323419136), (51552590357/4722366482869645213696)), (18379/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298400161161333/4722366482869645213696), (309216353307/2361183241434822606848)), (13785/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622631257429509/590295810358705651712), (850022738875/590295810358705651712)), (4739/73786976294838206464), by norm_num⟩
  | 8 => ⟨((912476525210293/36893488147419103232), (1062045303649/73786976294838206464)), (23697/36893488147419103232), by norm_num⟩
  | 7 => ⟨((57009982291557/288230376151711744), (597068524413/4611686018427387904)), (53325/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797783531875439/576460752303423488), (596653854735/576460752303423488)), (13333/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195963330624931/144115188075855872), (1043212005515/144115188075855872)), (46675/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493709284650281/36028797018963968), (1562955442303/36028797018963968)), (35015/18014398509481984), by norm_num⟩
  | 3 => ⟨((372961023146517/2251799813685248), (975219557783/4503599627370496)), (87567/9007199254740992), by norm_num⟩
  | 2 => ⟨((2233110590247415/4503599627370496), (1945564929263/2251799813685248)), (43807/1125899906842624), by norm_num⟩
  | 1 => ⟨((1111910875689641/1125899906842624), (363273994663/140737488355328)), (65769/562949953421312), by norm_num⟩
  | 0 => ⟨((549016568449367/562949953421312), (5763941926641/1125899906842624)), (527099/2251799813685248), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((549016568449367/562949953421312), (5763941926641/1125899906842624)), (2010723122603606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1070826580030673/1125899906842624), (22485122153923/2251799813685248)), (32297/70368744177664), by norm_num⟩
  | 2 => ⟨((2036669800490319/2251799813685248), (21385263744429/1125899906842624)), (993271/1125899906842624), by norm_num⟩
  | 3 => ⟨((1841280265239043/2251799813685248), (77368726259051/2251799813685248)), (3668973/2251799813685248), by norm_num⟩
  | 4 => ⟨((46966973301585/70368744177664), (126527685047037/2251799813685248)), (1563077/562949953421312), by norm_num⟩
  | 5 => ⟨((62251005571865/140737488355328), (168899487264171/2251799813685248)), (9048721/2251799813685248), by norm_num⟩
  | 6 => ⟨((855778570716163/4503599627370496), (74707620873703/1125899906842624)), (4681143/1125899906842624), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-215163547/134217728), (-4171483267/134217728)), (1/67108864), by norm_num⟩, -5, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-110690087/67108864), (-67062627/2097152)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((366151726735691/2251799813685248), (-461186701762627/4503599627370496)), (21177383/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3686124413/8589934592), (580357621/2147483648)), (27/2147483648), by norm_num⟩
  | 2 => ⟨((4863946825/8589934592), (-3063194067/8589934592)), (145/8589934592), by norm_num⟩
  | 3 => ⟨((-4278744839/8589934592), (2694648251/8589934592)), (65/4294967296), by norm_num⟩
  | 4 => ⟨((88217601/268435456), (-444458201/2147483648)), (87/8589934592), by norm_num⟩
  | 5 => ⟨((-2979984723/17179869184), (1876721077/17179869184)), (47/8589934592), by norm_num⟩
  | 6 => ⟨((2621450175/34359738368), (-825462419/17179869184)), (21/8589934592), by norm_num⟩
  | 7 => ⟨((-1976616371/68719476736), (2489648739/137438953472)), (129/137438953472), by norm_num⟩
  | 8 => ⟨((5216403921/549755813888), (-821290719/137438953472)), (173/549755813888), by norm_num⟩
  | 9 => ⟨((-764799389/274877906944), (963303685/549755813888)), (103/1099511627776), by norm_num⟩
  | 10 => ⟨((3229359093/4398046511104), (-254221365/549755813888)), (111/4398046511104), by norm_num⟩
  | 11 => ⟨((-3099077739/17592186044416), (121982683/1099511627776)), (109/17592186044416), by norm_num⟩
  | 12 => ⟨((2726214607/70368744177664), (-1716902899/70368744177664)), (49/35184372088832), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581827225343001/10141204801825835211973625643008), (-732101543127/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1779424403603841/633825300114114700748351602688), (-433506056649/316912650057057350374175801344)), (721/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((945239672740765/19807040628566084398385987584), (-975246700965/39614081257132168796771975168)), (12979/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890300404022167/2475880078570760549798248448), (-1036025251053/2475880078570760549798248448)), (13791/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771966531761715/154742504910672534362390528), (-258957284799/38685626227668133590597632)), (27583/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550280650107789/9671406556917033397649408), (-970881499699/9671406556917033397649408)), (25861/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259424875910987/604462909807314587353088), (-849313050811/604462909807314587353088)), (22631/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236103201867599/9444732965739290427392), (-344935834553/18889465931478580854784)), (36777/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((20286162785259/73786976294838206464), (-1034466051245/4722366482869645213696)), (27587/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622513345651107/590295810358705651712), (-1421836186651/590295810358705651712)), (2371/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1824805637829287/73786976294838206464), (-888231839275/36893488147419103232)), (47427/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824153562815259/9223372036854775808), (-249672361707/1152921504606846976)), (26683/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797700577095643/576460752303423488), (-1995951426813/1152921504606846976)), (13345/288230376151711744), by norm_num⟩
  | 5 => ⟨((597909058014577/72057594037927936), (-1744852922877/144115188075855872)), (23361/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493491375779843/36028797018963968), (-2614073541827/36028797018963968)), (2191/1125899906842624), by norm_num⟩
  | 3 => ⟨((745785777689413/4503599627370496), (-3261989139631/9007199254740992)), (87691/9007199254740992), by norm_num⟩
  | 2 => ⟨((2232565066824939/4503599627370496), (-6507199623971/4503599627370496)), (175537/4503599627370496), by norm_num⟩
  | 1 => ⟨((1111501179449787/1125899906842624), (-2429739149671/562949953421312)), (16481/140737488355328), by norm_num⟩
  | 0 => ⟨((2194423150102325/2251799813685248), (-19271163249133/2251799813685248)), (528959/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2194423150102325/2251799813685248), (-19271163249133/2251799813685248)), (2017818459517668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((534585884889531/562949953421312), (-9390063562997/562949953421312)), (1040017/2251799813685248), by norm_num⟩
  | 2 => ⟨((2029977217641529/2251799813685248), (-71335583683573/2251799813685248)), (251241/281474976710656), by norm_num⟩
  | 3 => ⟨((1827746282609585/2251799813685248), (-64308385143625/1125899906842624)), (3751211/2251799813685248), by norm_num⟩
  | 4 => ⟨((1476203248526723/2251799813685248), (-208791938204353/2251799813685248)), (6518103/2251799813685248), by norm_num⟩
  | 5 => ⟨((948388904076989/2251799813685248), (-273753764051549/2251799813685248)), (1219355/281474976710656), by norm_num⟩
  | 6 => ⟨((366151726735691/2251799813685248), (-461186701762627/4503599627370496)), (21177383/4503599627370496), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-110690087/67108864), (-67062627/2097152)), (1/67108864), by norm_num⟩, -5, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-56791929/33554432), (-2202107045/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((284997055814295/9007199254740992), (-1633121268871451/9007199254740992)), (62616399/9007199254740992), by norm_num⟩
  | 1 => ⟨((-736032805/8589934592), (4217695599/8589934592)), (41/2147483648), by norm_num⟩
  | 2 => ⟨((996606893/8589934592), (-1427716427/2147483648)), (7/268435456), by norm_num⟩
  | 3 => ⟨((-899620499/8589934592), (1288775919/2147483648)), (51/2147483648), by norm_num⟩
  | 4 => ⟨((1218108737/17179869184), (-6980139773/17179869184)), (279/17179869184), by norm_num⟩
  | 5 => ⟨((-329869961/8589934592), (3780513783/17179869184)), (153/17179869184), by norm_num⟩
  | 6 => ⟨((148884069/8589934592), (-3412607037/34359738368)), (279/68719476736), by norm_num⟩
  | 7 => ⟨((-921566933/137438953472), (5280863527/137438953472)), (109/68719476736), by norm_num⟩
  | 8 => ⟨((1247824759/549755813888), (-893802721/68719476736)), (149/274877906944), by norm_num⟩
  | 9 => ⟨((-750927131/1099511627776), (4303044691/1099511627776)), (181/1099511627776), by norm_num⟩
  | 10 => ⟨((813419347/4398046511104), (-145660763/137438953472)), (99/2199023255552), by norm_num⟩
  | 11 => ⟨((-100126383/2199023255552), (2295020559/8796093022208)), (197/17592186044416), by norm_num⟩
  | 12 => ⟨((723059391/70368744177664), (-1035838481/17592186044416)), (45/17592186044416), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581771056014629/10141204801825835211973625643008), (-1821084314209/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779355801405683/633825300114114700748351602688), (-2156517618549/633825300114114700748351602688)), (361/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((1890402059126451/39614081257132168796771975168), (-606429400391/9903520314283042199192993792)), (25995/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890218147384319/2475880078570760549798248448), (-2576879585369/2475880078570760549798248448)), (3453/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771884117857487/154742504910672534362390528), (-2576378648155/154742504910672534362390528)), (6907/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550203220068517/9671406556917033397649408), (-1207411421801/4835703278458516698824704)), (12953/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259356957725483/604462909807314587353088), (-1056218984583/302231454903657293676544)), (1417/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((472178733792077/18889465931478580854784), (-1715857209691/37778931862957161709568)), (36851/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649115567507395/2361183241434822606848), (-2572913449131/4722366482869645213696)), (27647/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622398387307883/590295810358705651712), (-884084719223/147573952589676412928)), (19013/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912330637393807/36893488147419103232), (-4418298759155/73786976294838206464)), (47551/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911995120513055/4611686018427387904), (-4967665812269/9223372036854775808)), (26761/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595236692435411/1152921504606846976), (-4964017485531/1152921504606846976)), (26777/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195672931923387/144115188075855872), (-4339413733555/144115188075855872)), (2931/9007199254740992), by norm_num⟩
  | 4 => ⟨((1493271045457781/36028797018963968), (-6500924468197/36028797018963968)), (70417/36028797018963968), by norm_num⟩
  | 3 => ⟨((372822921528451/2251799813685248), (-8111828097261/9007199254740992)), (88149/9007199254740992), by norm_num⟩
  | 2 => ⟨((2231992012796839/4503599627370496), (-16180736664917/4503599627370496)), (176683/4503599627370496), by norm_num⟩
  | 1 => ⟨((2222109676203717/2251799813685248), (-24164026269413/2251799813685248)), (265989/2251799813685248), by norm_num⟩
  | 0 => ⟨((34257914013789/35184372088832), (-47901056807869/2251799813685248)), (535847/2251799813685248), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((34257914013789/35184372088832), (-47901056807869/2251799813685248)), (2044094094283293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2133755495682907/2251799813685248), (-93279498133461/2251799813685248)), (1066273/2251799813685248), by norm_num⟩
  | 2 => ⟨((1009017636240945/1125899906842624), (-176779161777333/2251799813685248)), (1054547/1125899906842624), by norm_num⟩
  | 3 => ⟨((1794660193318247/2251799813685248), (-19803413570465/140737488355328)), (4111441/2251799813685248), by norm_num⟩
  | 4 => ⟨((346434920871065/562949953421312), (-505059432878339/2251799813685248)), (7710605/2251799813685248), by norm_num⟩
  | 5 => ⟨((739492662502025/2251799813685248), (-621619110547983/2251799813685248)), (1618617/281474976710656), by norm_num⟩
  | 6 => ⟨((284997055814295/9007199254740992), (-1633121268871451/9007199254740992)), (62616399/9007199254740992), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56791929/33554432), (-2202107045/67108864)), (1/67108864), by norm_num⟩, -5, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile029Terms1

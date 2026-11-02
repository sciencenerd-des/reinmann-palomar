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
namespace Reinmann.XiRectangle.Tile022Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨22,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (1269/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (1269/128))
  have he : value ((3/4), (1269/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-55294967/33554432), (-5847442761/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-1696171343855423/9007199254740992), (-357497126358333/9007199254740992)), (18398645/4503599627370496), by norm_num⟩
  | 1 => ⟨((3554219593/8589934592), (187278145/2147483648)), (79/8589934592), by norm_num⟩
  | 2 => ⟨((-1952354661/4294967296), (-411492143/4294967296)), (89/8589934592), by norm_num⟩
  | 3 => ⟨((5719682193/17179869184), (1205520867/17179869184)), (133/17179869184), by norm_num⟩
  | 4 => ⟨((-6283713145/34359738368), (-1324400039/34359738368)), (149/34359738368), by norm_num⟩
  | 5 => ⟨((10786507/134217728), (582000863/34359738368)), (133/68719476736), by norm_num⟩
  | 6 => ⟨((-4044864561/137438953472), (-53282775/8589934592)), (99/137438953472), by norm_num⟩
  | 7 => ⟨((5078557615/549755813888), (535196447/274877906944)), (63/274877906944), by norm_num⟩
  | 8 => ⟨((-5579365805/2199023255552), (-1175946787/2199023255552)), (141/2199023255552), by norm_num⟩
  | 9 => ⟨((5448497633/8796093022208), (1148364081/8796093022208)), (35/2199023255552), by norm_num⟩
  | 10 => ⟨((-1197157291/8796093022208), (-1009285513/35184372088832)), (125/35184372088832), by norm_num⟩
  | 11 => ⟨((3826070433/140737488355328), (403204897/70368744177664)), (51/70368744177664), by norm_num⟩
  | 12 => ⟨((-1401122665/281474976710656), (-1181242279/1125899906842624)), (19/140737488355328), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677707/5070602400912917605986812821504), (-3821687859367/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889708079072205/316912650057057350374175801344), (-1131488471009/158456325028528675187087900672)), (5791/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236308682581601/4951760157141521099596496896), (-2545463831263/19807040628566084398385987584)), (13033/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236286140547723/309485009821345068724781056), (-2704098822925/1237940039285380274899124224)), (13851/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885977189226209/77371252455336267181195264), (-2703585191341/77371252455336267181195264)), (433/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((775134164289075/4835703278458516698824704), (-5068130754659/9671406556917033397649408)), (12995/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259413167299927/604462909807314587353088), (-4433522917525/604462909807314587353088)), (711/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1888804850936673/75557863725914323419136), (-7202428163347/75557863725914323419136)), (9247/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298297326055969/4722366482869645213696), (-2700015169495/2361183241434822606848)), (13879/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622487377287555/590295810358705651712), (-7422131641353/590295810358705651712)), (2387/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1824769481181457/73786976294838206464), (-9273299351633/73786976294838206464)), (11945/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824107810311493/9223372036854775808), (-10426459481891/9223372036854775808)), (3363/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1595349065326135/1152921504606846976), (-10418956420533/1152921504606846976)), (13469/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195765422209569/144115188075855872), (-9108145660343/144115188075855872)), (23609/144115188075855872), by norm_num⟩
  | 4 => ⟨((93337383360321/2251799813685248), (-3411333863113/9007199254740992)), (17745/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491430219945277/9007199254740992), (-8513561348475/4503599627370496)), (44497/9007199254740992), by norm_num⟩
  | 2 => ⟨((1116104162135597/2251799813685248), (-16982800412881/2251799813685248)), (11175/562949953421312), by norm_num⟩
  | 1 => ⟨((555570758576269/562949953421312), (-25363387775535/1125899906842624)), (67555/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096126729258335/1125899906842624), (-50283490252337/1125899906842624)), (17143/140737488355328), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1096126729258335/1125899906842624), (-50283490252337/1125899906842624)), (65395355761480287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((532447586999493/562949953421312), (-48953798975393/562949953421312)), (279285/1125899906842624), by norm_num⟩
  | 2 => ⟨((998681878412311/1125899906842624), (-185205324064741/1125899906842624)), (576879/1125899906842624), by norm_num⟩
  | 3 => ⟨((855373089876125/1125899906842624), (-41069636786725/140737488355328)), (1213181/1125899906842624), by norm_num⟩
  | 4 => ⟨((1107937490504875/2251799813685248), (-998450733457933/2251799813685248)), (637855/281474976710656), by norm_num⟩
  | 5 => ⟨((204833142202037/4503599627370496), (-982521619636975/2251799813685248)), (19093283/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1696171343855423/9007199254740992), (-357497126358333/9007199254740992)), (18398645/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/33554432), (-5847442761/268435456)), (1/134217728), by norm_num⟩, -3, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-231785805/134217728), (-6127837213/268435456)), (3/268435456), by norm_num⟩
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
  | 0 => ⟨((-536439552201617/4503599627370496), (594658483991567/4503599627370496)), (27137313/4503599627370496), by norm_num⟩
  | 1 => ⟨((2355952675/8589934592), (-2611640473/8589934592)), (121/8589934592), by norm_num⟩
  | 2 => ⟨((-1356195377/4294967296), (1503381105/4294967296)), (71/4294967296), by norm_num⟩
  | 3 => ⟨((2081836839/8589934592), (-2307775281/8589934592)), (111/8589934592), by norm_num⟩
  | 4 => ⟨((-599200809/4294967296), (41514445/268435456)), (65/8589934592), by norm_num⟩
  | 5 => ⟨((2207537361/34359738368), (-305889735/4294967296)), (61/17179869184), by norm_num⟩
  | 6 => ⟨((-423586885/17179869184), (3756464767/137438953472)), (95/68719476736), by norm_num⟩
  | 7 => ⟨((1114679825/137438953472), (-2471308507/274877906944)), (127/274877906944), by norm_num⟩
  | 8 => ⟨((-641661287/274877906944), (355649883/137438953472)), (37/274877906944), by norm_num⟩
  | 9 => ⟨((2626630603/4398046511104), (-2911694645/4398046511104)), (153/4398046511104), by norm_num⟩
  | 10 => ⟨((-604804047/4398046511104), (1340884937/8796093022208)), (143/17592186044416), by norm_num⟩
  | 11 => ⟨((2025618593/70368744177664), (-1122727879/35184372088832)), (121/70368744177664), by norm_num⟩
  | 12 => ⟨((-3109439451/562949953421312), (1723450985/281474976710656)), (47/140737488355328), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581726236476819/10141204801825835211973625643008), (3002218571683/10141204801825835211973625643008)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444824614219585/158456325028528675187087900672), (888752072159/158456325028528675187087900672)), (8677/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236292163804337/4951760157141521099596496896), (3998761840631/39614081257132168796771975168)), (19527/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945074524330537/1237940039285380274899124224), (2123967121427/1237940039285380274899124224)), (20753/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771814678200379/154742504910672534362390528), (4247090292327/154742504910672534362390528)), (10379/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550137758346067/9671406556917033397649408), (3980750549421/9671406556917033397649408)), (19467/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629649658448715/302231454903657293676544), (870565060243/151115727451828646838272)), (17039/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472155147720561/18889465931478580854784), (2828496103437/37778931862957161709568)), (27699/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298159784075877/4722366482869645213696), (4241273789827/4722366482869645213696)), (1299/295147905179352825856), by norm_num⟩
  | 9 => ⟨((405574829369333/147573952589676412928), (5829362556073/590295810358705651712)), (28593/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912267997808787/36893488147419103232), (3641560303089/36893488147419103232)), (35765/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113990457618353/576460752303423488), (4094292936185/4611686018427387904)), (40267/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595091301999889/1152921504606846976), (1022803967257/144115188075855872)), (40307/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195542940269453/144115188075855872), (7152706955369/144115188075855872)), (35315/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493070520902099/36028797018963968), (10715225278017/36028797018963968)), (26531/18014398509481984), by norm_num⟩
  | 3 => ⟨((745515684845233/4503599627370496), (3342458669687/2251799813685248)), (33243/4503599627370496), by norm_num⟩
  | 2 => ⟨((69732578569067/140737488355328), (6666784292627/1125899906842624)), (16681/562949953421312), by norm_num⟩
  | 1 => ⟨((1110606835402175/1125899906842624), (19909790497273/1125899906842624)), (50341/562949953421312), by norm_num⟩
  | 0 => ⟨((273803736392401/281474976710656), (39457951431717/1125899906842624)), (101879/562949953421312), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((273803736392401/281474976710656), (39457951431717/1125899906842624)), (388637544872093023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1063983432086107/1125899906842624), (76765150910731/1125899906842624)), (102673/281474976710656), by norm_num⟩
  | 2 => ⟨((1000237986090177/1125899906842624), (72543614431637/562949953421312)), (832217/1125899906842624), by norm_num⟩
  | 3 => ⟨((869904792500717/1125899906842624), (257788026668503/1125899906842624)), (52911/35184372088832), by norm_num⟩
  | 4 => ⟨((1226183033015493/2251799813685248), (796699736754055/2251799813685248)), (3391697/1125899906842624), by norm_num⟩
  | 5 => ⟨((96455550203777/562949953421312), (216915307852557/562949953421312)), (12187595/2251799813685248), by norm_num⟩
  | 6 => ⟨((-536439552201617/4503599627370496), (594658483991567/4503599627370496)), (27137313/4503599627370496), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-231785805/134217728), (-6127837213/268435456)), (3/268435456), by norm_num⟩, -4, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-482760083/268435456), (-3190742425/134217728)), (3/268435456), by norm_num⟩
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
  | 0 => ⟨((78057758155933/2251799813685248), (729089345023143/4503599627370496)), (41728041/9007199254740992), by norm_num⟩
  | 1 => ⟨((-357006701/4294967296), (-6669158531/17179869184)), (193/17179869184), by norm_num⟩
  | 2 => ⟨((856064681/8589934592), (3997985929/8589934592)), (59/4294967296), by norm_num⟩
  | 3 => ⟨((-1368502301/17179869184), (-6391167707/17179869184)), (191/17179869184), by norm_num⟩
  | 4 => ⟨((205095325/4294967296), (957834427/4294967296)), (29/4294967296), by norm_num⟩
  | 5 => ⟨((-49179711/2147483648), (-3674858631/34359738368)), (57/17179869184), by norm_num⟩
  | 6 => ⟨((78618531/8589934592), (2937308713/68719476736)), (185/137438953472), by norm_num⟩
  | 7 => ⟨((-107725145/34359738368), (-4024776387/274877906944)), (129/274877906944), by norm_num⟩
  | 8 => ⟨((16144601/17179869184), (603187017/137438953472)), (157/1099511627776), by norm_num⟩
  | 9 => ⟨((-1101171553/4398046511104), (-642835243/549755813888)), (85/2199023255552), by norm_num⟩
  | 10 => ⟨((1056197625/17592186044416), (4932645089/17592186044416)), (165/17592186044416), by norm_num⟩
  | 11 => ⟨((-460482053/35184372088832), (-2150539335/35184372088832)), (73/35184372088832), by norm_num⟩
  | 12 => ⟨((1472250317/562949953421312), (6875690807/562949953421312)), (59/140737488355328), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581633122367159/10141204801825835211973625643008), (885683194181/5070602400912917605986812821504)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444798152334029/158456325028528675187087900672), (1048637793759/316912650057057350374175801344)), (17327/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118138656541865/2475880078570760549798248448), (2359059428427/39614081257132168796771975168)), (19495/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890023165469805/2475880078570760549798248448), (1253020247863/1237940039285380274899124224)), (20717/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771689186217189/154742504910672534362390528), (2505522949431/154742504910672534362390528)), (1295/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((387505131265381/2417851639229258349412352), (587094498715/2417851639229258349412352)), (4857/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629598576494135/302231454903657293676544), (513570278321/151115727451828646838272)), (17003/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236056919069833/9444732965739290427392), (3337176541901/75557863725914323419136)), (6909/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((649018267804797/2361183241434822606848), (2501981215797/4722366482869645213696)), (20733/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622130955350453/590295810358705651712), (1719380143241/295147905179352825856)), (28517/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456081799523759/18446744073709551616), (4296255491657/73786976294838206464)), (8915/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911807348918415/4611686018427387904), (4830271048533/9223372036854775808)), (5017/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1594861515406441/1152921504606846976), (4826502915829/1152921504606846976)), (40159/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597672531837779/72057594037927936), (2109477060267/72057594037927936)), (35167/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492780065696377/36028797018963968), (3159983680489/18014398509481984)), (52803/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490679399416725/9007199254740992), (7885165598547/9007199254740992)), (4131/562949953421312), by norm_num⟩
  | 2 => ⟨((2230771747161359/4503599627370496), (15726022656841/4503599627370496)), (66237/2251799813685248), by norm_num⟩
  | 1 => ⟨((555072506311499/562949953421312), (23478515300493/2251799813685248)), (199415/2251799813685248), by norm_num⟩
  | 0 => ⟨((2188910053483503/2251799813685248), (23258234842813/1125899906842624)), (401655/2251799813685248), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2188910053483503/2251799813685248), (23258234842813/1125899906842624)), (1532192238814543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2126815808040811/2251799813685248), (90434653674467/2251799813685248)), (398735/1125899906842624), by norm_num⟩
  | 2 => ⟨((2005136969683659/2251799813685248), (85415164287973/1125899906842624)), (785235/1125899906842624), by norm_num⟩
  | 3 => ⟨((443133448383515/562949953421312), (304235043709543/2251799813685248)), (3035165/2251799813685248), by norm_num⟩
  | 4 => ⟨((1354168815925449/2251799813685248), (239482609810649/1125899906842624)), (699811/281474976710656), by norm_num⟩
  | 5 => ⟨((356240703695677/1125899906842624), (576072313695205/2251799813685248)), (2278795/562949953421312), by norm_num⟩
  | 6 => ⟨((78057758155933/2251799813685248), (729089345023143/4503599627370496)), (41728041/9007199254740992), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-482760083/268435456), (-3190742425/134217728)), (3/268435456), by norm_num⟩, -4, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-500277787/268435456), (-826630875/33554432)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((153482512570507/1125899906842624), (666359775956243/9007199254740992)), (16382689/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1454886307/4294967296), (-1579133833/8589934592)), (41/8589934592), by norm_num⟩
  | 2 => ⟨((3615256659/8589934592), (1962000081/8589934592)), (53/8589934592), by norm_num⟩
  | 3 => ⟨((-187157819/536870912), (-203141127/1073741824)), (45/8589934592), by norm_num⟩
  | 4 => ⟨((465069709/2147483648), (2019146949/17179869184)), (29/8589934592), by norm_num⟩
  | 5 => ⟨((-462261925/4294967296), (-15679349/268435456)), (59/34359738368), by norm_num⟩
  | 6 => ⟨((3063140617/68719476736), (415591665/17179869184)), (25/34359738368), by norm_num⟩
  | 7 => ⟨((-4349496279/274877906944), (-1180235991/137438953472)), (73/274877906944), by norm_num⟩
  | 8 => ⟨((5404046113/1099511627776), (1466388131/549755813888)), (93/1099511627776), by norm_num⟩
  | 9 => ⟨((-2984122249/2199023255552), (-809741693/1099511627776)), (53/2199023255552), by norm_num⟩
  | 10 => ⟨((370763261/1099511627776), (804853007/4398046511104)), (27/4398046511104), by norm_num⟩
  | 11 => ⟨((-5360361267/70368744177664), (-2909068493/70368744177664)), (25/17592186044416), by norm_num⟩
  | 12 => ⟨((4439999119/281474976710656), (2409587881/281474976710656)), (85/281474976710656), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581548115842083/10141204801825835211973625643008), (323843191899/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779094005948021/633825300114114700748351602688), (191692500585/158456325028528675187087900672)), (11535/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890107710732073/39614081257132168796771975168), (862475187461/39614081257132168796771975168)), (12977/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944952809659741/1237940039285380274899124224), (458102840541/1237940039285380274899124224)), (13789/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885785916951835/77371252455336267181195264), (229002440627/38685626227668133590597632)), (6895/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549910713113471/9671406556917033397649408), (858551046795/9671406556917033397649408)), (6465/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78693829578789/37778931862957161709568), (751024125569/604462909807314587353088)), (5657/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944149966743241/37778931862957161709568), (1220024266795/75557863725914323419136)), (9193/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297920308352487/4722366482869645213696), (914677143397/4722366482869645213696)), (13791/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621971690100101/590295810358705651712), (1257127114411/590295810358705651712)), (18965/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912064468273367/36893488147419103232), (1570578410041/73786976294838206464)), (11855/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911696389885663/4611686018427387904), (1765759533973/9223372036854775808)), (13339/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797320501523785/576460752303423488), (220541770835/144115188075855872)), (26683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195153694015637/144115188075855872), (771095187431/72057594037927936)), (23355/144115188075855872), by norm_num⟩
  | 4 => ⟨((186562020201155/4503599627370496), (2310085309567/36028797018963968)), (35045/36028797018963968), by norm_num⟩
  | 3 => ⟨((186291252125097/1125899906842624), (1441007354995/4503599627370496)), (43829/9007199254740992), by norm_num⟩
  | 2 => ⟨((8711286771437/17592186044416), (5747287647917/4503599627370496)), (43863/2251799813685248), by norm_num⟩
  | 1 => ⟨((2219307386479823/2251799813685248), (4289597918689/1125899906842624)), (65881/1125899906842624), by norm_num⟩
  | 0 => ⟨((2187106930565085/2251799813685248), (16992160031935/2251799813685248)), (264221/2251799813685248), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2187106930565085/2251799813685248), (16992160031935/2251799813685248)), (1007923134810637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((531036103115587/562949953421312), (33007970553381/2251799813685248)), (517249/2251799813685248), by norm_num⟩
  | 2 => ⟨((2003241998449461/2251799813685248), (62273471905959/2251799813685248)), (991017/2251799813685248), by norm_num⟩
  | 3 => ⟨((890199140856877/1125899906842624), (110799222518025/2251799813685248)), (454517/562949953421312), by norm_num⟩
  | 4 => ⟨((1402230142585865/2251799813685248), (175208066176601/2251799813685248)), (381731/281474976710656), by norm_num⟩
  | 5 => ⟨((1719115078134187/4503599627370496), (218209478590311/2251799813685248)), (534823/281474976710656), by norm_num⟩
  | 6 => ⟨((153482512570507/1125899906842624), (666359775956243/9007199254740992)), (16382689/9007199254740992), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-500277787/268435456), (-826630875/33554432)), (1/134217728), by norm_num⟩, -4, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-516392513/268435456), (-853257941/33554432)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((629142261719083/4503599627370496), (-192087414694491/4503599627370496)), (6612167/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3077922897/8589934592), (1879480327/17179869184)), (67/17179869184), by norm_num⟩
  | 2 => ⟨((1973679089/4294967296), (-301298241/2147483648)), (45/8589934592), by norm_num⟩
  | 3 => ⟨((-3374924607/8589934592), (128802455/1073741824)), (41/8589934592), by norm_num⟩
  | 4 => ⟨((4328255351/17179869184), (-1321487097/17179869184)), (27/8589934592), by norm_num⟩
  | 5 => ⟨((-4440702313/34359738368), (84738687/2147483648)), (29/17179869184), by norm_num⟩
  | 6 => ⟨((3796725515/68719476736), (-1159202351/68719476736)), (51/68719476736), by norm_num⟩
  | 7 => ⟨((-2782402477/137438953472), (424756475/68719476736)), (77/274877906944), by norm_num⟩
  | 8 => ⟨((3568360723/549755813888), (-17023107/8589934592)), (51/549755813888), by norm_num⟩
  | 9 => ⟨((-1016962727/549755813888), (1241981365/2199023255552)), (15/549755813888), by norm_num⟩
  | 10 => ⟨((4173532629/8796093022208), (-637123861/4398046511104)), (63/8796093022208), by norm_num⟩
  | 11 => ⟨((-3892690849/35184372088832), (1188502137/35184372088832)), (61/35184372088832), by norm_num⟩
  | 12 => ⟨((832046241/35184372088832), (-63509329/8796093022208)), (27/70368744177664), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917417231/10141204801825835211973625643008), (-385999014077/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889500818669843/316912650057057350374175801344), (-228461767203/316912650057057350374175801344)), (11531/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945001912454517/19807040628566084398385987584), (-513952387297/39614081257132168796771975168)), (12973/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944897638459625/1237940039285380274899124224), (-68245908657/309485009821345068724781056)), (1723/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771461532305811/154742504910672534362390528), (-1066106983/302231454903657293676544)), (13785/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549807348700615/9671406556917033397649408), (-511603364369/9671406556917033397649408)), (3231/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629505436357473/302231454903657293676544), (-447524998393/604462909807314587353088)), (11309/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944076556887447/37778931862957161709568), (-363494157003/37778931862957161709568)), (9189/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297810264555511/4722366482869645213696), (-34064468277/295147905179352825856)), (13785/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621820495154841/590295810358705651712), (-749077636885/590295810358705651712)), (9477/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823940115642429/73786976294838206464), (-935836340873/73786976294838206464)), (23695/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113948787100109/576460752303423488), (-131514267365/1152921504606846976)), (26659/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594429113231519/1152921504606846976), (-1051237670381/1152921504606846976)), (13331/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194968623369465/144115188075855872), (-114855989103/18014398509481984)), (11667/72057594037927936), by norm_num⟩
  | 4 => ⟨((373054805097531/9007199254740992), (-1376304214957/36028797018963968)), (547/562949953421312), by norm_num⟩
  | 3 => ⟨((1489985001238699/9007199254740992), (-1716942363785/9007199254740992)), (21887/4503599627370496), by norm_num⟩
  | 2 => ⟨((2229402854066305/4503599627370496), (-855898234277/1125899906842624)), (87589/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218286192057583/2251799813685248), (-2554868251289/1125899906842624)), (131487/2251799813685248), by norm_num⟩
  | 0 => ⟨((2185098908030493/2251799813685248), (-5058659769425/1125899906842624)), (32925/281474976710656), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2185098908030493/2251799813685248), (-5058659769425/1125899906842624)), (125598908544444949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((530082075758265/562949953421312), (-9817632874015/1125899906842624)), (128391/562949953421312), by norm_num⟩
  | 2 => ⟨((249545193896753/281474976710656), (-9244429600291/562949953421312)), (244029/562949953421312), by norm_num⟩
  | 3 => ⟨((110580769301033/140737488355328), (-65566126098403/2251799813685248)), (1762835/2251799813685248), by norm_num⟩
  | 4 => ⟨((173533207645003/281474976710656), (-12879213542849/281474976710656)), (2872861/2251799813685248), by norm_num⟩
  | 5 => ⟨((1702341024502029/4503599627370496), (-254086812451027/4503599627370496)), (7610439/4503599627370496), by norm_num⟩
  | 6 => ⟨((629142261719083/4503599627370496), (-192087414694491/4503599627370496)), (6612167/4503599627370496), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-516392513/268435456), (-853257941/33554432)), (1/134217728), by norm_num⟩, -4, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-265656209/134217728), (-1755821507/67108864)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((319791236347687/4503599627370496), (-266892564744369/2251799813685248)), (20191915/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1609701931/8589934592), (2686862103/8589934592)), (13/2147483648), by norm_num⟩
  | 2 => ⟨((66376495/268435456), (-3545391563/8589934592)), (71/8589934592), by norm_num⟩
  | 3 => ⟨((-1868494673/8589934592), (1559415265/4294967296)), (1/134217728), by norm_num⟩
  | 4 => ⟨((2465532281/17179869184), (-4115386285/17179869184)), (87/17179869184), by norm_num⟩
  | 5 => ⟨((-2602672415/34359738368), (4344296135/34359738368)), (47/17179869184), by norm_num⟩
  | 6 => ⟨((143095869/4294967296), (-3821615519/68719476736)), (85/68719476736), by norm_num⟩
  | 7 => ⟨((-863173033/68719476736), (2881560699/137438953472)), (33/68719476736), by norm_num⟩
  | 8 => ⟨((2277963119/549755813888), (-3802301941/549755813888)), (89/549755813888), by norm_num⟩
  | 9 => ⟨((-2671855673/2199023255552), (1114943645/549755813888)), (107/2199023255552), by norm_num⟩
  | 10 => ⟨((2820472119/8796093022208), (-4707840317/8796093022208)), (115/8796093022208), by norm_num⟩
  | 11 => ⟨((-2706686407/35184372088832), (4517912907/35184372088832)), (113/35184372088832), by norm_num⟩
  | 12 => ⟨((1190516767/70368744177664), (-993585931/35184372088832)), (51/70368744177664), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197674689623573/1267650600228229401496703205376), (-1343042208313/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778914697214961/633825300114114700748351602688), (-794835340447/316912650057057350374175801344)), (11545/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472476490850807/9903520314283042199192993792), (-1788068711377/39614081257132168796771975168)), (6495/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889691228255051/2475880078570760549798248448), (-474859837407/618970019642690137449562112)), (13803/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771357404048845/154742504910672534362390528), (-1899007869903/154742504910672534362390528)), (13805/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549709643951347/9671406556917033397649408), (-1779861557151/9671406556917033397649408)), (12943/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629462648308665/302231454903657293676544), (-389230170935/151115727451828646838272)), (11327/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944006947214215/37778931862957161709568), (-2529137327787/75557863725914323419136)), (9205/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648852855886065/2361183241434822606848), (-948050931125/2361183241434822606848)), (13811/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621676510647049/590295810358705651712), (-162870002133/36893488147419103232)), (9497/295147905179352825856), by norm_num⟩
  | 8 => ⟨((113984987426441/4611686018427387904), (-1627785496165/36893488147419103232)), (23749/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822977275674981/9223372036854775808), (-915001007253/2305843009213693952)), (3341/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1594225219545577/1152921504606846976), (-3656864766049/1152921504606846976)), (26739/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194789570205835/144115188075855872), (-399528538623/18014398509481984)), (11705/72057594037927936), by norm_num⟩
  | 4 => ⟨((46623417253531/1125899906842624), (-4787294007211/36028797018963968)), (17571/18014398509481984), by norm_num⟩
  | 3 => ⟨((744822709797895/4503599627370496), (-5971801289347/9007199254740992)), (43975/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228716986338587/4503599627370496), (-1488341016561/562949953421312)), (88091/4503599627370496), by norm_num⟩
  | 1 => ⟨((1108620374765735/1125899906842624), (-17768165367769/2251799813685248)), (66247/1125899906842624), by norm_num⟩
  | 0 => ⟨((2182942177099149/2251799813685248), (-17585087721127/1125899906842624)), (133211/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2182942177099149/2251799813685248), (-17585087721127/1125899906842624)), (508159641746139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2115640821339741/2251799813685248), (-34094708988907/1125899906842624)), (262437/1125899906842624), by norm_num⟩
  | 2 => ⟨((1985649994737911/2251799813685248), (-128132452432493/2251799813685248)), (1018063/2251799813685248), by norm_num⟩
  | 3 => ⟨((1743666533931565/2251799813685248), (-112987931676727/1125899906842624)), (1911329/2251799813685248), by norm_num⟩
  | 4 => ⟨((331879844798719/562949953421312), (-349965878859235/2251799813685248)), (835917/562949953421312), by norm_num⟩
  | 5 => ⟨((364115756606383/1125899906842624), (-412635691164987/2251799813685248)), (4981753/2251799813685248), by norm_num⟩
  | 6 => ⟨((319791236347687/4503599627370496), (-266892564744369/2251799813685248)), (20191915/9007199254740992), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-265656209/134217728), (-1755821507/67108864)), (1/134217728), by norm_num⟩, -4, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-272601259/134217728), (-900861973/33554432)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-169865124920071/9007199254740992), (-1169466264211009/9007199254740992)), (6173043/2251799813685248), by norm_num⟩
  | 1 => ⟨((438693319/8589934592), (6040522293/17179869184)), (65/8589934592), by norm_num⟩
  | 2 => ⟨((-594001765/8589934592), (-4089509403/8589934592)), (45/4294967296), by norm_num⟩
  | 3 => ⟨((536195533/8589934592), (1845766127/4294967296)), (165/17179869184), by norm_num⟩
  | 4 => ⟨((-726022211/17179869184), (-1249606833/4294967296)), (57/8589934592), by norm_num⟩
  | 5 => ⟨((393220919/17179869184), (5414396857/34359738368)), (125/34359738368), by norm_num⟩
  | 6 => ⟨((-709907993/68719476736), (-2443743083/34359738368)), (115/68719476736), by norm_num⟩
  | 7 => ⟨((274638069/68719476736), (1890793985/68719476736)), (45/68719476736), by norm_num⟩
  | 8 => ⟨((-371866839/274877906944), (-5120365031/549755813888)), (31/137438953472), by norm_num⟩
  | 9 => ⟨((447570697/1099511627776), (6162758023/2199023255552)), (151/2199023255552), by norm_num⟩
  | 10 => ⟨((-969635133/8796093022208), (-3337811621/4398046511104)), (83/4398046511104), by norm_num⟩
  | 11 => ⟨((954843861/35184372088832), (1643447533/8796093022208)), (83/17592186044416), by norm_num⟩
  | 12 => ⟨((-861921703/140737488355328), (-2967025615/70368744177664)), (19/17592186044416), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798419/10141204801825835211973625643008), (-2234028111925/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222354066316301/79228162514264337593543950336), (-1322023141447/316912650057057350374175801344)), (11559/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236226675836615/4951760157141521099596496896), (-185876142903/2475880078570760549798248448)), (13005/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236199091333141/309485009821345068724781056), (-1579619593893/1237940039285380274899124224)), (3455/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885629365506845/77371252455336267181195264), (-789625554189/38685626227668133590597632)), (13823/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549616951695761/9671406556917033397649408), (-2960312982535/9671406556917033397649408)), (6481/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314711001187425/151115727451828646838272), (-2589491223263/604462909807314587353088)), (11345/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943940723211647/37778931862957161709568), (-4206456238967/75557863725914323419136)), (18441/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162200758867205/590295810358705651712), (-1576779499843/2361183241434822606848)), (13835/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202692376213893/73786976294838206464), (-4334059290973/590295810358705651712)), (19031/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823587181451961/73786976294838206464), (-1353612267753/18446744073709551616)), (2975/9223372036854775808), by norm_num⟩
  | 7 => ⟨((28480969743349/144115188075855872), (-6086960639283/9223372036854775808)), (13395/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797014368942477/576460752303423488), (-1520398995835/288230376151711744)), (26811/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149327027972103/18014398509481984), (-5315366128399/144115188075855872)), (23481/144115188075855872), by norm_num⟩
  | 4 => ⟨((745843245351369/18014398509481984), (-7961000675433/36028797018963968)), (35267/36028797018963968), by norm_num⟩
  | 3 => ⟨((744655944062005/4503599627370496), (-9930193367359/9007199254740992)), (44163/9007199254740992), by norm_num⟩
  | 2 => ⟨((278504391578789/562949953421312), (-19797323941859/4503599627370496)), (88561/4503599627370496), by norm_num⟩
  | 1 => ⟨((1108090624032495/1125899906842624), (-29538712327609/2251799813685248)), (66717/1125899906842624), by norm_num⟩
  | 0 => ⟨((2180677820528497/2251799813685248), (-7306328500433/281474976710656)), (269247/2251799813685248), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2180677820528497/2251799813685248), (-7306328500433/281474976710656)), (1027095803267668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1055142480284247/1125899906842624), (-56604493573749/1125899906842624)), (535465/2251799813685248), by norm_num⟩
  | 2 => ⟨((1971972070094189/2251799813685248), (-212188687046361/2251799813685248)), (1057469/2251799813685248), by norm_num⟩
  | 3 => ⟨((1706923405429485/2251799813685248), (-185820321105981/1125899906842624)), (2051411/2251799813685248), by norm_num⟩
  | 4 => ⟨((154069576266917/281474976710656), (-281713368455369/1125899906842624)), (236699/140737488355328), by norm_num⟩
  | 5 => ⟨((66710310016173/281474976710656), (-154200063585977/562949953421312)), (6041141/2251799813685248), by norm_num⟩
  | 6 => ⟨((-169865124920071/9007199254740992), (-1169466264211009/9007199254740992)), (6173043/2251799813685248), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-272601259/134217728), (-900861973/33554432)), (1/134217728), by norm_num⟩, -4, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨22,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile022Terms1

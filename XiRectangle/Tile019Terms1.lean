/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile019Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨19,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (5499/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (5499/640))
  have he : value ((3/4), (5499/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-18874015403/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-55294967/33554432), (-20271134903/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-18874015403/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((866343355860491/4503599627370496), (-25486183003029/4503599627370496)), (1705709/4503599627370496), by norm_num⟩
  | 1 => ⟨((-29045881865/68719476736), (427237455/34359738368)), (15/17179869184), by norm_num⟩
  | 2 => ⟨((498596293/1073741824), (-234684159/17179869184)), (69/68719476736), by norm_num⟩
  | 3 => ⟨((-11685632311/34359738368), (687538403/68719476736)), (53/68719476736), by norm_num⟩
  | 4 => ⟨((25675958515/137438953472), (-377669069/68719476736)), (61/137438953472), by norm_num⟩
  | 5 => ⟨((-11283169419/137438953472), (10372797/4294967296)), (7/34359738368), by norm_num⟩
  | 6 => ⟨((8263885719/274877906944), (-15194243/17179869184)), (85/1099511627776), by norm_num⟩
  | 7 => ⟨((-5187889373/549755813888), (610471573/2199023255552)), (55/2199023255552), by norm_num⟩
  | 8 => ⟨((22797916069/8796093022208), (-167667893/2199023255552)), (63/8796093022208), by norm_num⟩
  | 9 => ⟨((-22263173999/35184372088832), (81867559/4398046511104)), (1/549755813888), by norm_num⟩
  | 10 => ⟨((1222929827/8796093022208), (-575620521/140737488355328)), (29/70368744177664), by norm_num⟩
  | 11 => ⟨((-3908438505/140737488355328), (459915475/562949953421312)), (95/1125899906842624), by norm_num⟩
  | 12 => ⟨((11450289523/2251799813685248), (-673691723/4503599627370496)), (9/562949953421312), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677707/5070602400912917605986812821504), (-9577330595/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779427106574977/633825300114114700748351602688), (-22684509149/316912650057057350374175801344)), (1441/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472620602264083/9903520314283042199192993792), (-51032736821/39614081257132168796771975168)), (3243/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890303688112383/2475880078570760549798248448), (-54213168113/2475880078570760549798248448)), (3445/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771969848503439/154742504910672534362390528), (-54202916933/154742504910672534362390528)), (3445/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550283794227713/9671406556917033397649408), (-12701086373/2417851639229258349412352)), (1615/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629713830835297/302231454903657293676544), (-44442916261/604462909807314587353088)), (1413/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944415103367719/37778931862957161709568), (-9024916769/9444732965739290427392)), (4593/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649158959439363/2361183241434822606848), (-13532913249/1180591620717411303424)), (861/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622518251188741/590295810358705651712), (-37201016391/295147905179352825856)), (37/4611686018427387904), by norm_num⟩
  | 8 => ⟨((1824811907886291/73786976294838206464), (-92959077347/73786976294838206464)), (5919/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824160806340399/9223372036854775808), (-13064904305/1152921504606846976)), (6659/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398852158629669/288230376151711744), (-6527789207/72057594037927936)), (6659/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298956231813995/36028797018963968), (-91305187793/144115188075855872)), (5827/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493502123346967/36028797018963968), (-136790239095/36028797018963968)), (8741/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491585916018037/9007199254740992), (-170695003001/9007199254740992)), (5463/4503599627370496), by norm_num⟩
  | 2 => ⟨((2232596556299213/4503599627370496), (-340513230785/4503599627370496)), (5463/1125899906842624), by norm_num⟩
  | 1 => ⟨((1111528238745611/1125899906842624), (-508583541131/2251799813685248)), (32781/2251799813685248), by norm_num⟩
  | 0 => ⟨((2194558708935233/2251799813685248), (-1008455577279/2251799813685248)), (65575/2251799813685248), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2194558708935233/2251799813685248), (-1008455577279/2251799813685248)), (250148781783293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1069386115211307/1125899906842624), (-491410239099/562949953421312)), (31969/562949953421312), by norm_num⟩
  | 2 => ⟨((1015708137571137/1125899906842624), (-3733953850579/2251799813685248)), (243139/2251799813685248), by norm_num⟩
  | 3 => ⟨((916297735576233/1125899906842624), (-6737023936673/2251799813685248)), (439493/2251799813685248), by norm_num⟩
  | 4 => ⟨((1491411782249321/2251799813685248), (-2741415884387/562949953421312)), (717981/2251799813685248), by norm_num⟩
  | 5 => ⟨((987738272708717/2251799813685248), (-29051107830613/4503599627370496)), (1916119/4503599627370496), by norm_num⟩
  | 6 => ⟨((866343355860491/4503599627370496), (-25486183003029/4503599627370496)), (1705709/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/33554432), (-20271134903/1073741824)), (1/536870912), by norm_num⟩, -3, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-19779055341/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-927143219/536870912), (-1327698063/67108864)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-19779055341/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((951541216779429/9007199254740992), (-322113503415817/2251799813685248)), (6158649/9007199254740992), by norm_num⟩
  | 1 => ⟨((-8358019337/34359738368), (11317348499/34359738368)), (7/4294967296), by norm_num⟩
  | 2 => ⟨((4811262683/17179869184), (-13029578973/34359738368)), (33/17179869184), by norm_num⟩
  | 3 => ⟨((-7385561155/34359738368), (10000571437/34359738368)), (13/8589934592), by norm_num⟩
  | 4 => ⟨((8502941509/68719476736), (-2878395839/17179869184)), (31/34359738368), by norm_num⟩
  | 5 => ⟨((-3915749273/68719476736), (10604402161/137438953472)), (59/137438953472), by norm_num⟩
  | 6 => ⟨((6010897269/274877906944), (-8139179445/274877906944)), (93/549755813888), by norm_num⟩
  | 7 => ⟨((-1977228921/274877906944), (5354615217/549755813888)), (63/1099511627776), by norm_num⟩
  | 8 => ⟨((4552737839/2199023255552), (-12329457177/4398046511104)), (75/4398046511104), by norm_num⟩
  | 9 => ⟨((-4659140569/8796093022208), (788600675/1099511627776)), (39/8796093022208), by norm_num⟩
  | 10 => ⟨((536403381/4398046511104), (-11621249015/70368744177664)), (37/35184372088832), by norm_num⟩
  | 11 => ⟨((-14372240627/562949953421312), (2432628613/70368744177664)), (127/562949953421312), by norm_num⟩
  | 12 => ⟨((2757775585/562949953421312), (-14936891683/2251799813685248)), (25/562949953421312), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790863118239623/5070602400912917605986812821504), (-1217534087247/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444826025696431/158456325028528675187087900672), (-90107192159/39614081257132168796771975168)), (2887/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236292998298087/4951760157141521099596496896), (-810841083579/19807040628566084398385987584)), (3247/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890156557382361/2475880078570760549798248448), (-1722733667129/2475880078570760549798248448)), (3451/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771822654104375/154742504910672534362390528), (-215299020745/19342813113834066795298816)), (3451/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775072865937077/4835703278458516698824704), (-807189948579/4835703278458516698824704)), (809/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259306789556221/604462909807314587353088), (-353054937241/151115727451828646838272)), (177/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((944316831494457/37778931862957161709568), (-2294177309473/75557863725914323419136)), (2301/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324542600108291/1180591620717411303424), (-860019189573/2361183241434822606848)), (863/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622315233739711/590295810358705651712), (-1182043464575/295147905179352825856)), (1187/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824557867039179/73786976294838206464), (-2953660576257/73786976294838206464)), (371/4611686018427387904), by norm_num⟩
  | 7 => ⟨((113992165063827/576460752303423488), (-830219533135/2305843009213693952)), (835/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1595122008328069/1152921504606846976), (-3318392264017/1152921504606846976)), (6683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597786806003639/72057594037927936), (-2900798897821/144115188075855872)), (5851/144115188075855872), by norm_num⟩
  | 4 => ⟨((186640514834619/4503599627370496), (-543201918527/4503599627370496)), (4391/18014398509481984), by norm_num⟩
  | 3 => ⟨((372777902743663/2251799813685248), (-5422261678583/9007199254740992)), (2747/2251799813685248), by norm_num⟩
  | 2 => ⟨((278955321786485/562949953421312), (-2703825435009/1125899906842624)), (22007/4503599627370496), by norm_num⟩
  | 1 => ⟨((2221612164356937/2251799813685248), (-2018759557255/281474976710656)), (16545/1125899906842624), by norm_num⟩
  | 0 => ⟨((2191617258154849/2251799813685248), (-32009713499791/2251799813685248)), (8313/281474976710656), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2191617258154849/2251799813685248), (-32009713499791/2251799813685248)), (31711579442882449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2132588143625753/2251799813685248), (-62308416679299/2251799813685248)), (131345/2251799813685248), by norm_num⟩
  | 2 => ⟨((2017963508091493/2251799813685248), (-14752442673945/281474976710656)), (256053/2251799813685248), by norm_num⟩
  | 3 => ⟨((901112097792789/1125899906842624), (-52881949434949/562949953421312)), (60721/281474976710656), by norm_num⟩
  | 4 => ⟨((1422536773681953/2251799813685248), (-338591834681517/2251799813685248)), (27151/70368744177664), by norm_num⟩
  | 5 => ⟨((211937849710571/562949953421312), (-106949856993421/562949953421312)), (1359025/2251799813685248), by norm_num⟩
  | 6 => ⟨((951541216779429/9007199254740992), (-322113503415817/2251799813685248)), (6158649/9007199254740992), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-927143219/536870912), (-1327698063/67108864)), (1/536870912), by norm_num⟩, -3, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1931040333/1073741824), (-22122480815/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-271101449327439/9007199254740992), (-1466382388692927/9007199254740992)), (979159/1125899906842624), by norm_num⟩
  | 1 => ⟨((4959662505/68719476736), (13413358299/34359738368)), (73/34359738368), by norm_num⟩
  | 2 => ⟨((-2973187819/34359738368), (-16081914229/34359738368)), (89/34359738368), by norm_num⟩
  | 3 => ⟨((2376464339/34359738368), (25708497405/68719476736)), (145/68719476736), by norm_num⟩
  | 4 => ⟨((-1424628151/34359738368), (-3852892775/17179869184)), (89/68719476736), by norm_num⟩
  | 5 => ⟨((2732887287/137438953472), (14782133395/137438953472)), (87/137438953472), by norm_num⟩
  | 6 => ⟨((-1092196251/137438953472), (-5907667965/137438953472)), (141/549755813888), by norm_num⟩
  | 7 => ⟨((2993111117/1099511627776), (4047419739/274877906944)), (49/549755813888), by norm_num⟩
  | 8 => ⟨((-3588583499/4398046511104), (-19410577319/4398046511104)), (15/549755813888), by norm_num⟩
  | 9 => ⟨((3824465515/17592186044416), (20686458487/17592186044416)), (65/8796093022208), by norm_num⟩
  | 10 => ⟨((-458533389/8796093022208), (-19841584407/70368744177664)), (127/70368744177664), by norm_num⟩
  | 11 => ⟨((399823653/35184372088832), (270329781/4398046511104)), (113/281474976710656), by norm_num⟩
  | 12 => ⟨((-5113254653/2251799813685248), (-13828746751/1125899906842624)), (183/2251799813685248), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790816561182973/5070602400912917605986812821504), (-571068161147/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222398881230683/79228162514264337593543950336), (-2704550162065/633825300114114700748351602688)), (1445/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945108330495719/19807040628566084398385987584), (-1521065947741/19807040628566084398385987584)), (813/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890021091823707/2475880078570760549798248448), (-3231671439497/2475880078570760549798248448)), (27/19342813113834066795298816), by norm_num⟩
  | 14 => ⟨((442921745893869/38685626227668133590597632), (-3231003642617/154742504910672534362390528)), (3457/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((24219036298481/151115727451828646838272), (-3028356514725/9671406556917033397649408)), (1621/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259195089377397/604462909807314587353088), (-1324551350389/302231454903657293676544)), (2837/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888451742690055/75557863725914323419136), (-4303462365815/75557863725914323419136)), (4611/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649016801975309/2361183241434822606848), (-403304220229/590295810358705651712)), (865/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811063280119861/295147905179352825856), (-4434457127233/590295810358705651712)), (4759/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824321158679757/73786976294838206464), (-5540238516197/73786976294838206464)), (93/1152921504606846976), by norm_num⟩
  | 7 => ⟨((227950894294687/1152921504606846976), (-3114437404681/4611686018427387904)), (6699/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398713259236987/288230376151711744), (-6224010466961/1152921504606846976)), (419/72057594037927936), by norm_num⟩
  | 5 => ⟨((1195336595154047/144115188075855872), (-340033768261/9007199254740992)), (367/9007199254740992), by norm_num⟩
  | 4 => ⟨((746382634060403/18014398509481984), (-1018735187705/4503599627370496)), (8819/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490657247674861/9007199254740992), (-5084123013657/4503599627370496)), (2761/2251799813685248), by norm_num⟩
  | 2 => ⟨((1115358261872817/2251799813685248), (-20279253652111/4503599627370496)), (22147/4503599627370496), by norm_num⟩
  | 1 => ⟨((2220180045288453/2251799813685248), (-30276061436167/2251799813685248)), (8343/562949953421312), by norm_num⟩
  | 0 => ⟨((2188582441393771/2251799813685248), (-59982508088073/2251799813685248)), (33675/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2188582441393771/2251799813685248), (-59982508088073/2251799813685248)), (128459934714889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((531385513535885/562949953421312), (-14574637496025/281474976710656)), (134507/2251799813685248), by norm_num⟩
  | 2 => ⟨((2000326189227295/2251799813685248), (-55029767270473/562949953421312)), (267861/2251799813685248), by norm_num⟩
  | 3 => ⟨((877709562526777/1125899906842624), (-48884223184147/281474976710656)), (66033/281474976710656), by norm_num⟩
  | 4 => ⟨((650270415052271/1125899906842624), (-609733066105193/2251799813685248)), (62945/140737488355328), by norm_num⟩
  | 5 => ⟨((586034349433261/2251799813685248), (-704310163910047/2251799813685248)), (1708745/2251799813685248), by norm_num⟩
  | 6 => ⟨((-271101449327439/9007199254740992), (-1466382388692927/9007199254740992)), (979159/1125899906842624), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1931040333/1073741824), (-22122480815/1073741824)), (1/536870912), by norm_num⟩, -3, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-21345185589/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2001111149/1073741824), (-716413425/33554432)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-21345185589/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-280060645879023/2251799813685248), (-834704934699441/9007199254740992)), (3948969/4503599627370496), by norm_num⟩
  | 1 => ⟨((2654741521/8589934592), (1978076785/8589934592)), (77/34359738368), by norm_num⟩
  | 2 => ⟨((-6596784859/17179869184), (-4915336157/17179869184)), (49/17179869184), by norm_num⟩
  | 3 => ⟨((5464131521/17179869184), (2035691917/8589934592)), (83/34359738368), by norm_num⟩
  | 4 => ⟨((-848616047/4294967296), (-10117008763/68719476736)), (105/68719476736), by norm_num⟩
  | 5 => ⟨((13495882613/137438953472), (10055928941/137438953472)), (107/137438953472), by norm_num⟩
  | 6 => ⟨((-11178669483/274877906944), (-1041168529/34359738368)), (91/274877906944), by norm_num⟩
  | 7 => ⟨((7936557181/549755813888), (11827230177/1099511627776)), (33/274877906944), by norm_num⟩
  | 8 => ⟨((-4930400929/1099511627776), (-7347390729/2199023255552)), (21/549755813888), by norm_num⟩
  | 9 => ⟨((10890298715/8796093022208), (2028620009/2199023255552)), (47/4398046511104), by norm_num⟩
  | 10 => ⟨((-5412275139/17592186044416), (-504093135/2199023255552)), (95/35184372088832), by norm_num⟩
  | 11 => ⟨((4890544903/70368744177664), (1821999103/35184372088832)), (87/140737488355328), by norm_num⟩
  | 12 => ⟨((-8101698367/562949953421312), (-12073327165/1125899906842624)), (73/562949953421312), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790774057920435/5070602400912917605986812821504), (-1629064323261/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779086362119581/633825300114114700748351602688), (-120536505611/19807040628566084398385987584)), (1447/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890098675421185/39614081257132168796771975168), (-542323239421/4951760157141521099596496896)), (3257/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944947728549391/1237940039285380274899124224), (-1152217252855/618970019642690137449562112)), (3461/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771561039628791/154742504910672534362390528), (-143996272313/4835703278458516698824704)), (1731/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549899922307927/9671406556917033397649408), (-4318838225185/9671406556917033397649408)), (1623/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314772790141403/151115727451828646838272), (-3777933639597/604462909807314587353088)), (1421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236035280454797/9444732965739290427392), (-6137174066239/75557863725914323419136)), (4619/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297905942256219/4722366482869645213696), (-575144844365/590295810358705651712)), (3467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621950153035337/590295810358705651712), (-3161897958913/295147905179352825856)), (4769/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912049671351679/36893488147419103232), (-7900549799039/73786976294838206464)), (5965/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911677908441425/4611686018427387904), (-8882351820943/9223372036854775808)), (6717/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594599460219897/1152921504606846976), (-4437572890617/576460752303423488)), (1681/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195112201678157/144115188075855872), (-3878824492739/72057594037927936)), (1473/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492423663519549/36028797018963968), (-11620274402201/36028797018963968)), (4427/18014398509481984), by norm_num⟩
  | 3 => ⟨((186277687076643/1125899906842624), (-14497012822223/9007199254740992)), (11095/9007199254740992), by norm_num⟩
  | 2 => ⟨((139363681561667/281474976710656), (-14454554067527/2251799813685248)), (5569/1125899906842624), by norm_num⟩
  | 1 => ⟨((554692185574647/562949953421312), (-2696976564849/140737488355328)), (16815/1125899906842624), by norm_num⟩
  | 0 => ⟨((68296963439603/70368744177664), (-42728324496155/1125899906842624)), (34063/1125899906842624), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((68296963439603/70368744177664), (-42728324496155/1125899906842624)), (129940037253951671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((66184832355975/70368744177664), (-41470326777207/562949953421312)), (68707/1125899906842624), by norm_num⟩
  | 2 => ⟨((989885017234317/1125899906842624), (-78009254181579/562949953421312)), (139367/1125899906842624), by norm_num⟩
  | 3 => ⟨((848681633763277/1125899906842624), (-34292654014209/140737488355328)), (283687/1125899906842624), by norm_num⟩
  | 4 => ⟨((1145745549723389/2251799813685248), (-206793129357107/562949953421312)), (1131849/2251799813685248), by norm_num⟩
  | 5 => ⟨((558236560197105/4503599627370496), (-420876325212089/1125899906842624)), (1983343/2251799813685248), by norm_num⟩
  | 6 => ⟨((-280060645879023/2251799813685248), (-834704934699441/9007199254740992)), (3948969/4503599627370496), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2001111149/1073741824), (-716413425/33554432)), (1/536870912), by norm_num⟩, -3, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-5508186803/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2065570051/1073741824), (-11831843449/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-657074583992733/4503599627370496), (31153687451003/4503599627370496)), (6704281/9007199254740992), by norm_num⟩
  | 1 => ⟨((25716598999/68719476736), (-76205855/4294967296)), (133/68719476736), by norm_num⟩
  | 2 => ⟨((-16490443519/34359738368), (781856635/34359738368)), (87/34359738368), by norm_num⟩
  | 3 => ⟨((3524762709/8589934592), (-1336948449/68719476736)), (151/68719476736), by norm_num⟩
  | 4 => ⟨((-18081675691/68719476736), (428650633/34359738368)), (49/34359738368), by norm_num⟩
  | 5 => ⟨((9275716489/68719476736), (-879573733/137438953472)), (103/137438953472), by norm_num⟩
  | 6 => ⟨((-991322627/17179869184), (376010347/137438953472)), (179/549755813888), by norm_num⟩
  | 7 => ⟨((11623736389/549755813888), (-68889107/68719476736)), (133/1099511627776), by norm_num⟩
  | 8 => ⟨((-14907147591/2199023255552), (706788283/2199023255552)), (173/4398046511104), by norm_num⟩
  | 9 => ⟨((8496906363/4398046511104), (-402861367/4398046511104)), (101/8796093022208), by norm_num⟩
  | 10 => ⟨((-17435307613/35184372088832), (206663801/8796093022208)), (53/17592186044416), by norm_num⟩
  | 11 => ⟨((32524131679/281474976710656), (-1542057261/281474976710656)), (25/35184372088832), by norm_num⟩
  | 12 => ⟨((-13903791775/562949953421312), (1318432927/1125899906842624)), (173/1125899906842624), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917418445/10141204801825835211973625643008), (2015280529037/5070602400912917605986812821504)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222373696239631/79228162514264337593543950336), (2385573715393/316912650057057350374175801344)), (2897/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889989562855055/39614081257132168796771975168), (5366600243285/39614081257132168796771975168)), (815/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889779236214741/2475880078570760549798248448), (5700889706427/2475880078570760549798248448)), (3465/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771444494086529/154742504910672534362390528), (2849813079487/77371252455336267181195264)), (1733/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((12107736844831/75557863725914323419136), (1335514265977/2417851639229258349412352)), (3251/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78687181918569/37778931862957161709568), (4672957536771/604462909807314587353088)), (1423/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944062596129601/37778931862957161709568), (1897759787255/18889465931478580854784)), (2313/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((40555862174543/147573952589676412928), (2845538630505/2361183241434822606848)), (217/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1621786502400631/590295810358705651712), (488853317923/36893488147419103232)), (4777/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823893407607487/73786976294838206464), (1221462450889/9223372036854775808)), (747/9223372036854775808), by norm_num⟩
  | 7 => ⟨((455780564135039/2305843009213693952), (5492891771381/4611686018427387904)), (6731/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797181774989177/576460752303423488), (1372070194949/144115188075855872)), (1685/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194903142491261/144115188075855872), (4797059122261/72057594037927936)), (5907/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492104814055305/36028797018963968), (1796304399755/4503599627370496)), (8881/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489813761786089/9007199254740992), (17926754484237/9007199254740992)), (87/70368744177664), by norm_num⟩
  | 2 => ⟨((278622006126437/562949953421312), (8936169540137/1125899906842624)), (11189/2251799813685248), by norm_num⟩
  | 1 => ⟨((554359114070501/562949953421312), (13336268748275/562949953421312)), (8459/562949953421312), by norm_num⟩
  | 0 => ⟨((545642256883377/562949953421312), (13200401403169/281474976710656)), (8593/281474976710656), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((545642256883377/562949953421312), (13200401403169/281474976710656)), (32779694677257449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1055257108745757/1125899906842624), (102356477972757/1125899906842624)), (69855/1125899906842624), by norm_num⟩
  | 2 => ⟨((244935342447287/281474976710656), (191868567268703/1125899906842624)), (71823/562949953421312), by norm_num⟩
  | 3 => ⟨((409929692222453/562949953421312), (166961176364673/562949953421312)), (298957/1125899906842624), by norm_num⟩
  | 4 => ⟨((995941591615119/2251799813685248), (486312100919897/1125899906842624)), (612721/1125899906842624), by norm_num⟩
  | 5 => ⟨((40769002311301/4503599627370496), (860357914355089/2251799813685248)), (4285219/4503599627370496), by norm_num⟩
  | 6 => ⟨((-657074583992733/4503599627370496), (31153687451003/4503599627370496)), (6704281/9007199254740992), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2065570051/1073741824), (-11831843449/536870912)), (1/536870912), by norm_num⟩, -4, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-11334664923/4294967296), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2125249673/1073741824), (-24347391567/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-11334664923/4294967296), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-964449071189579/9007199254740992), (786517630717283/9007199254740992)), (3529821/4503599627370496), by norm_num⟩
  | 1 => ⟨((9709306299/34359738368), (-7918034051/34359738368)), (73/34359738368), by norm_num⟩
  | 2 => ⟨((-12811707977/34359738368), (10448072899/34359738368)), (49/17179869184), by norm_num⟩
  | 3 => ⟨((11270277281/34359738368), (-4595510561/17179869184)), (89/34359738368), by norm_num⟩
  | 4 => ⟨((-14871453933/68719476736), (12127815829/68719476736)), (15/8589934592), by norm_num⟩
  | 5 => ⟨((7849323901/68719476736), (-6401200251/68719476736)), (129/137438953472), by norm_num⟩
  | 6 => ⟨((-6904938591/137438953472), (11262089627/274877906944)), (29/68719476736), by norm_num⟩
  | 7 => ⟨((81350575/4294967296), (-8491800051/549755813888)), (45/274877906944), by norm_num⟩
  | 8 => ⟨((-6870042599/1099511627776), (11205173583/2199023255552)), (121/2199023255552), by norm_num⟩
  | 9 => ⟨((4028985839/2199023255552), (-3285677275/2199023255552)), (9/549755813888), by norm_num⟩
  | 10 => ⟨((-17012359375/35184372088832), (13873745113/35184372088832)), (77/17592186044416), by norm_num⟩
  | 11 => ⟨((8163016673/70368744177664), (-6657019769/70368744177664)), (75/70368744177664), by norm_num⟩
  | 12 => ⟨((-7180889661/281474976710656), (5856085605/281474976710656)), (67/281474976710656), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581397516987371/10141204801825835211973625643008), (1600561810119/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778908367209365/633825300114114700748351602688), (1894479687051/316912650057057350374175801344)), (2893/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889898483227531/39614081257132168796771975168), (2130911652949/19807040628566084398385987584)), (407/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944841407626293/1237940039285380274899124224), (4527271041487/2475880078570760549798248448)), (3461/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771348467945761/154742504910672534362390528), (4526240381797/154742504910672534362390528)), (1731/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549700710898477/9671406556917033397649408), (4242255445303/9671406556917033397649408)), (1623/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157364615640023/75557863725914323419136), (927719696359/151115727451828646838272)), (2841/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887999250786175/75557863725914323419136), (3014062899515/37778931862957161709568)), (4619/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297693819883473/4722366482869645213696), (282456190033/295147905179352825856)), (1733/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621658683433323/590295810358705651712), (6211119535945/590295810358705651712)), (4769/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823735303652201/73786976294838206464), (3879762867221/36893488147419103232)), (5965/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822946682568975/9223372036854775808), (2129749687/2251799813685248)), (1679/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594190837831997/1152921504606846976), (136186612193/18014398509481984)), (6723/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298688808217607/36028797018963968), (59515657107/1125899906842624)), (2945/72057594037927936), by norm_num⟩
  | 4 => ⟨((745944680765147/18014398509481984), (11410124597859/36028797018963968)), (8851/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489555632988911/9007199254740992), (1779142161839/1125899906842624)), (2773/2251799813685248), by norm_num⟩
  | 2 => ⟨((139280826010699/281474976710656), (7094454140701/1125899906842624)), (5567/1125899906842624), by norm_num⟩
  | 1 => ⟨((1108397646953955/1125899906842624), (330827509529/17592186044416)), (2101/140737488355328), by norm_num⟩
  | 0 => ⟨((1090808101719361/1125899906842624), (20952670703733/562949953421312)), (34041/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1090808101719361/1125899906842624), (20952670703733/562949953421312)), (129856113914107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((527625168950383/562949953421312), (10149811194311/140737488355328)), (68495/1125899906842624), by norm_num⟩
  | 2 => ⟨((983178055354861/1125899906842624), (152206662454911/1125899906842624)), (138275/1125899906842624), by norm_num⟩
  | 3 => ⟨((837971665777551/1125899906842624), (531650280793177/2251799813685248)), (557761/2251799813685248), by norm_num⟩
  | 4 => ⟨((17528576017865/35184372088832), (791380954381113/2251799813685248)), (136703/281474976710656), by norm_num⟩
  | 5 => ⟨((140380193627649/1125899906842624), (24641233441187/70368744177664)), (1858365/2251799813685248), by norm_num⟩
  | 6 => ⟨((-964449071189579/9007199254740992), (786517630717283/9007199254740992)), (3529821/4503599627370496), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2125249673/1073741824), (-24347391567/1073741824)), (1/536870912), by norm_num⟩, -4, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-23261974099/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-272601259/134217728), (-24983905385/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-23261974099/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-85575079953535/2251799813685248), (1131077360239779/9007199254740992)), (3189603/4503599627370496), by norm_num⟩
  | 1 => ⟨((7072192763/68719476736), (-11684472171/34359738368)), (67/34359738368), by norm_num⟩
  | 2 => ⟨((-2393981629/17179869184), (7910534303/17179869184)), (93/34359738368), by norm_num⟩
  | 3 => ⟨((4322014955/34359738368), (-14281416007/34359738368)), (43/17179869184), by norm_num⟩
  | 4 => ⟨((-2926058367/34359738368), (19337395745/68719476736)), (59/34359738368), by norm_num⟩
  | 5 => ⟨((6339130359/137438953472), (-10473327687/68719476736)), (65/68719476736), by norm_num⟩
  | 6 => ⟨((-1430556937/68719476736), (18908198099/274877906944)), (119/274877906944), by norm_num⟩
  | 7 => ⟨((2213725715/274877906944), (-7314907095/274877906944)), (47/274877906944), by norm_num⟩
  | 8 => ⟨((-374680023/137438953472), (19809135629/2199023255552)), (65/1099511627776), by norm_num⟩
  | 9 => ⟨((7215305327/8796093022208), (-11920918605/4398046511104)), (159/8796093022208), by norm_num⟩
  | 10 => ⟨((-7815763617/35184372088832), (6456489205/8796093022208)), (175/35184372088832), by norm_num⟩
  | 11 => ⟨((7696538267/140737488355328), (-6357998869/35184372088832)), (87/70368744177664), by norm_num⟩
  | 12 => ⟨((-3473768667/281474976710656), (11478520077/281474976710656)), (159/562949953421312), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798419/10141204801825835211973625643008), (303616980063/1267650600228229401496703205376)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778831849171083/633825300114114700748351602688), (179670377305/39614081257132168796771975168)), (2891/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889812601633019/39614081257132168796771975168), (3233485199171/39614081257132168796771975168)), (3253/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472397956303555/618970019642690137449562112), (858716367693/618970019642690137449562112)), (3457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221407221158941/19342813113834066795298816), (3434064020355/154742504910672534362390528)), (1729/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549615990290351/9671406556917033397649408), (3218583669047/9671406556917033397649408)), (1621/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157355387973727/75557863725914323419136), (1407704787587/302231454903657293676544)), (1419/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471969967614657/18889465931478580854784), (2286722568737/37778931862957161709568)), (1153/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297604791136519/4722366482869645213696), (1714344157521/2361183241434822606848)), (3461/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621537091181733/590295810358705651712), (1178044884845/147573952589676412928)), (595/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1823584545377975/73786976294838206464), (5886825580527/73786976294838206464)), (2977/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911389385668027/4611686018427387904), (6618007800257/9223372036854775808)), (3351/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99626564877413/72057594037927936), (206630397677/36028797018963968)), (6707/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194612528828419/144115188075855872), (2889545845263/72057594037927936)), (5875/144115188075855872), by norm_num⟩
  | 4 => ⟨((372920008887957/9007199254740992), (8655531179837/36028797018963968)), (8825/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489302227386325/9007199254740992), (10796506041775/9007199254740992)), (2763/2251799813685248), by norm_num⟩
  | 2 => ⟨((1114005528808221/2251799813685248), (84079691399/17592186044416)), (11083/2251799813685248), by norm_num⟩
  | 1 => ⟨((138508333000529/140737488355328), (501804188651/35184372088832)), (33411/2251799813685248), by norm_num⟩
  | 0 => ⟨((2180535206579539/2251799813685248), (63548766518673/2251799813685248)), (67467/2251799813685248), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2180535206579539/2251799813685248), (63548766518673/2251799813685248)), (257366189009856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((527433135100933/562949953421312), (61537585129243/1125899906842624)), (16809/281474976710656), by norm_num⟩
  | 2 => ⟨((1969901528344411/2251799813685248), (57655145460091/562949953421312)), (266677/2251799813685248), by norm_num⟩
  | 3 => ⟨((1699674258495269/2251799813685248), (403499310972509/2251799813685248)), (260605/1125899906842624), by norm_num⟩
  | 4 => ⟨((75663944305475/140737488355328), (609128207589783/2251799813685248)), (486809/1125899906842624), by norm_num⟩
  | 5 => ⟨((121521808004303/562949953421312), (327482345411789/1125899906842624)), (196703/281474976710656), by norm_num⟩
  | 6 => ⟨((-85575079953535/2251799813685248), (1131077360239779/9007199254740992)), (3189603/4503599627370496), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-272601259/134217728), (-24983905385/1073741824)), (1/536870912), by norm_num⟩, -4, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨19,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile019Terms1

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
namespace Reinmann.XiRectangle.Tile037Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨37,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (3525/256)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (3525/256))
  have he : value ((5/8), (3525/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-7268175/4194304), (-40031745/1048576)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1413697796419335/9007199254740992), (-366319435981485/4503599627370496)), (147015433/9007199254740992), by norm_num⟩
  | 1 => ⟨((-934506075/2147483648), (121075289/536870912)), (99/2147483648), by norm_num⟩
  | 2 => ⟨((647750251/1073741824), (-335691981/1073741824)), (35/536870912), by norm_num⟩
  | 3 => ⟨((-598648347/1073741824), (310245267/1073741824)), (131/2147483648), by norm_num⟩
  | 4 => ⟨((207475707/536870912), (-420011/2097152)), (93/2147483648), by norm_num⟩
  | 5 => ⟨((-920391689/4294967296), (476986475/4294967296)), (105/4294967296), by norm_num⟩
  | 6 => ⟨((850622539/8589934592), (-440829107/8589934592)), (99/8589934592), by norm_num⟩
  | 7 => ⟨((-673836131/17179869184), (349210803/17179869184)), (159/34359738368), by norm_num⟩
  | 8 => ⟨((934135229/68719476736), (-484108967/68719476736)), (7/4294967296), by norm_num⟩
  | 9 => ⟨((-1151099023/274877906944), (596548917/274877906944)), (35/68719476736), by norm_num⟩
  | 10 => ⟨((319152417/274877906944), (-10337405/17179869184)), (157/1099511627776), by norm_num⟩
  | 11 => ⟨((-1287095843/4398046511104), (333514153/2199023255552)), (5/137438953472), by norm_num⟩
  | 12 => ⟨((297382285/4398046511104), (-616465053/17592186044416)), (75/8796093022208), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581718513116769/10141204801825835211973625643008), (-622824487735/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444823944478525/158456325028528675187087900672), (-368748062447/316912650057057350374175801344)), (92273/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945167334802757/19807040628566084398385987584), (-829556608363/39614081257132168796771975168)), (103811/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472536680156589/618970019642690137449562112), (-440624043687/1237940039285380274899124224)), (110305/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221476610926889/19342813113834066795298816), (-881072853457/154742504910672534362390528)), (13789/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((387534162502535/2417851639229258349412352), (-825819662181/9671406556917033397649408)), (101/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((1259298917288781/604462909807314587353088), (-361203060297/302231454903657293676544)), (45251/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944310504946711/37778931862957161709568), (-1173561153777/75557863725914323419136)), (73539/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324540258110177/1180591620717411303424), (-879865787091/4722366482869645213696)), (110319/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622302550549055/590295810358705651712), (-604659960247/295147905179352825856)), (151705/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912271154723025/36893488147419103232), (-1510906972227/73786976294838206464)), (94829/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911928772889977/4611686018427387904), (-1698749429081/9223372036854775808)), (26675/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1595105421162653/1152921504606846976), (-1697474202929/1152921504606846976)), (213445/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597779834404731/72057594037927936), (-370964139575/36028797018963968)), (186815/144115188075855872), by norm_num⟩
  | 4 => ⟨((746552171247001/18014398509481984), (-2222921246381/36028797018963968)), (280323/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491088877636971/9007199254740992), (-2773647347315/9007199254740992)), (87645/2251799813685248), by norm_num⟩
  | 2 => ⟨((139475190350305/281474976710656), (-2766155158587/2251799813685248)), (701691/4503599627370496), by norm_num⟩
  | 1 => ⟨((2221567637115521/2251799813685248), (-2065275810467/562949953421312)), (1053869/2251799813685248), by norm_num⟩
  | 0 => ⟨((2191586793449473/2251799813685248), (-16373348360189/2251799813685248)), (2113099/2251799813685248), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2191586793449473/2251799813685248), (-16373348360189/2251799813685248)), (8060832985884856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((533216203045319/562949953421312), (-15935525801475/1125899906842624)), (258995/140737488355328), by norm_num⟩
  | 2 => ⟨((2019760600151873/2251799813685248), (-60375388680663/2251799813685248)), (3983699/1125899906842624), by norm_num⟩
  | 3 => ⟨((1810013336708277/2251799813685248), (-27076969838737/562949953421312)), (14720023/2251799813685248), by norm_num⟩
  | 4 => ⟨((1449692669167153/2251799813685248), (-87058674093331/1125899906842624)), (12540073/1125899906842624), by norm_num⟩
  | 5 => ⟨((229959605146649/562949953421312), (-224191015299827/2251799813685248)), (4521427/281474976710656), by norm_num⟩
  | 6 => ⟨((1413697796419335/9007199254740992), (-366319435981485/4503599627370496)), (147015433/9007199254740992), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7268175/4194304), (-40031745/1048576)), (1/16777216), by norm_num⟩, -6, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-29708395/16777216), (-654513081/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((195495390910463/4503599627370496), (-1482362867118815/9007199254740992)), (224637291/9007199254740992), by norm_num⟩
  | 1 => ⟨((-264110637/2147483648), (500661165/1073741824)), (77/1073741824), by norm_num⟩
  | 2 => ⟨((374140891/2147483648), (-709239947/1073741824)), (221/2147483648), by norm_num⟩
  | 3 => ⟨((-176670161/1073741824), (1339618721/2147483648)), (211/2147483648), by norm_num⟩
  | 4 => ⟨((250272129/2147483648), (-948856409/2147483648)), (151/2147483648), by norm_num⟩
  | 5 => ⟨((-141814867/2147483648), (8400977/33554432)), (173/4294967296), by norm_num⟩
  | 6 => ⟨((133930591/4294967296), (-507770883/4294967296)), (165/8589934592), by norm_num⟩
  | 7 => ⟨((-433661643/34359738368), (1644140847/34359738368)), (269/34359738368), by norm_num⟩
  | 8 => ⟨((76790997/17179869184), (-1164550447/68719476736)), (193/68719476736), by norm_num⟩
  | 9 => ⟨((-386782715/274877906944), (733204415/137438953472)), (123/137438953472), by norm_num⟩
  | 10 => ⟨((109583795/274877906944), (-830929813/549755813888)), (281/1099511627776), by norm_num⟩
  | 11 => ⟨((-225799469/2199023255552), (856073249/2199023255552)), (73/1099511627776), by norm_num⟩
  | 12 => ⟨((213246023/8796093022208), (-101059923/1099511627776)), (139/8796093022208), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581669156673291/10141204801825835211973625643008), (-427552265639/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779235434104211/633825300114114700748351602688), (-506239620649/158456325028528675187087900672)), (92399/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890266683970375/39614081257132168796771975168), (-2277721150105/39614081257132168796771975168)), (103963/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236259294802355/309485009821345068724781056), (-1209820642451/1237940039285380274899124224)), (110475/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771740381905609/154742504910672534362390528), (-151196830063/9671406556917033397649408)), (110491/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550068523923683/9671406556917033397649408), (-1133714906345/4835703278458516698824704)), (103603/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629619577444899/302231454903657293676544), (-991739289095/302231454903657293676544)), (90671/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888523611065651/75557863725914323419136), (-3222173264141/75557863725914323419136)), (147373/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298087734214591/4722366482869645213696), (-603943306931/1180591620717411303424)), (110559/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622201361081725/590295810358705651712), (-3320296536475/590295810358705651712)), (152065/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456103804170925/18446744073709551616), (-2074142050535/36893488147419103232)), (23769/9223372036854775808), by norm_num⟩
  | 7 => ⟨((111310652733/562949953421312), (-4663952055517/9223372036854775808)), (214019/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594960571362141/1152921504606846976), (-291273113705/72057594037927936)), (214141/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195431759313391/144115188075855872), (-509224576937/18014398509481984)), (187511/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492910152093711/36028797018963968), (-6102648564735/36028797018963968)), (281541/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490842081633135/9007199254740992), (-3807123326949/4503599627370496)), (44051/1125899906842624), by norm_num⟩
  | 2 => ⟨((1115548665279337/2251799813685248), (-15186369394883/4503599627370496)), (88283/562949953421312), by norm_num⟩
  | 1 => ⟨((138798683429271/140737488355328), (-11337241449259/1125899906842624)), (1063023/2251799813685248), by norm_num⟩
  | 0 => ⟨((2189889933897095/2251799813685248), (-44930110452069/2251799813685248)), (1070299/1125899906842624), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2189889933897095/2251799813685248), (-44930110452069/2251799813685248)), (4082866672996139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2128785684511397/2251799813685248), (-87389648058319/2251799813685248)), (4248915/2251799813685248), by norm_num⟩
  | 2 => ⟨((31392191207575/35184372088832), (-82615617352139/1125899906842624)), (8363391/2251799813685248), by norm_num⟩
  | 3 => ⟨((1780434645286961/2251799813685248), (-294845137506195/2251799813685248)), (8075667/1125899906842624), by norm_num⟩
  | 4 => ⟨((684566596970595/1125899906842624), (-466251479922899/2251799813685248)), (14885221/1125899906842624), by norm_num⟩
  | 5 => ⟨((91989486040795/281474976710656), (-566977911630535/2251799813685248)), (12132565/562949953421312), by norm_num⟩
  | 6 => ⟨((195495390910463/4503599627370496), (-1482362867118815/9007199254740992)), (224637291/9007199254740992), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-29708395/16777216), (-654513081/16777216)), (1/16777216), by norm_num⟩, -6, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-60615489/33554432), (-1335434995/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-746737774992257/9007199254740992), (-319236614995769/2251799813685248)), (131910637/4503599627370496), by norm_num⟩
  | 1 => ⟨((514590687/2147483648), (879967209/2147483648)), (23/268435456), by norm_num⟩
  | 2 => ⟨((-371839597/1073741824), (-1271716185/2147483648)), (269/2147483648), by norm_num⟩
  | 3 => ⟨((716503113/2147483648), (612622091/1073741824)), (261/2147483648), by norm_num⟩
  | 4 => ⟨((-517740091/2147483648), (-885352795/2147483648)), (191/2147483648), by norm_num⟩
  | 5 => ⟨((598584535/4294967296), (511799743/2147483648)), (111/2147483648), by norm_num⟩
  | 6 => ⟨((-144177653/2147483648), (-986194349/8589934592)), (27/1073741824), by norm_num⟩
  | 7 => ⟨((476259447/17179869184), (814419513/17179869184)), (45/4294967296), by norm_num⟩
  | 8 => ⟨((-172070857/17179869184), (-294246895/17179869184)), (131/34359738368), by norm_num⟩
  | 9 => ⟨((221043887/68719476736), (377992407/68719476736)), (85/68719476736), by norm_num⟩
  | 10 => ⟨((-511119207/549755813888), (-437015431/274877906944)), (199/549755813888), by norm_num⟩
  | 11 => ⟨((537208917/2199023255552), (459322567/1099511627776)), (211/2199023255552), by norm_num⟩
  | 12 => ⟨((-517577827/8796093022208), (-885075317/8796093022208)), (205/8796093022208), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197702827769549/1267650600228229401496703205376), (-1367711234679/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779176920024647/633825300114114700748351602688), (-1619331415013/316912650057057350374175801344)), (92519/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890200670121845/39614081257132168796771975168), (-1821453254975/19807040628566084398385987584)), (13013/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((945001989681577/1237940039285380274899124224), (-3869873631081/2475880078570760549798248448)), (55317/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885834866886005/77371252455336267181195264), (-120908433377/4835703278458516698824704)), (110661/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550002005568045/9671406556917033397649408), (-1813199566979/4835703278458516698824704)), (103773/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((9837348951435/4722366482869645213696), (-1586122760965/302231454903657293676544)), (45415/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888428031265389/75557863725914323419136), (-5153298560201/75557863725914323419136)), (147651/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298015581630689/4722366482869645213696), (-3863573871507/4722366482869645213696)), (110785/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811050695974761/295147905179352825856), (-5310139580711/590295810358705651712)), (38101/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912144558782543/36893488147419103232), (-6634263763573/73786976294838206464)), (190619/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823570310622827/9223372036854775808), (-3729429336723/4611686018427387904)), (214603/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398703799485299/288230376151711744), (-3726500551065/576460752303423488)), (107399/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195302368511041/144115188075855872), (-3257394820989/72057594037927936)), (23521/18014398509481984), by norm_num⟩
  | 4 => ⟨((1492711698549255/36028797018963968), (-4879510218461/18014398509481984)), (282693/36028797018963968), by norm_num⟩
  | 3 => ⟨((745293198036005/4503599627370496), (-760984869213/562949953421312)), (44267/1125899906842624), by norm_num⟩
  | 2 => ⟨((1115281600123443/2251799813685248), (-3035317574877/562949953421312)), (177647/1125899906842624), by norm_num⟩
  | 1 => ⟨((138745073697173/140737488355328), (-2265727821091/140737488355328)), (267921/562949953421312), by norm_num⟩
  | 0 => ⟨((546987550505083/562949953421312), (-17954065874093/562949953421312)), (135415/140737488355328), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((546987550505083/562949953421312), (-17954065874093/562949953421312)), (516567230761480287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((530905154374287/562949953421312), (-69779918832161/1125899906842624)), (2174307/1125899906842624), by norm_num⟩
  | 2 => ⟨((997044131427777/1125899906842624), (-131615673310441/1125899906842624)), (4370593/1125899906842624), by norm_num⟩
  | 3 => ⟨((433774933551949/562949953421312), (-466210660043809/2251799813685248)), (17525227/2251799813685248), by norm_num⟩
  | 4 => ⟨((38763696531961/70368744177664), (-359233528402771/1125899906842624)), (2141535/140737488355328), by norm_num⟩
  | 5 => ⟨((454077769677707/2251799813685248), (-791557083579767/2251799813685248)), (14903863/562949953421312), by norm_num⟩
  | 6 => ⟨((-746737774992257/9007199254740992), (-319236614995769/2251799813685248)), (131910637/4503599627370496), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60615489/33554432), (-1335434995/33554432)), (1/16777216), by norm_num⟩, -6, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-61749361/33554432), (-170051951/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-683714452131443/4503599627370496), (-209371947682129/4503599627370496)), (124182247/4503599627370496), by norm_num⟩
  | 1 => ⟨((239986835/536870912), (293961965/2147483648)), (11/134217728), by norm_num⟩
  | 2 => ⟨((-1413253183/2147483648), (-216388267/1073741824)), (261/2147483648), by norm_num⟩
  | 3 => ⟨((1387079253/2147483648), (424761365/2147483648)), (129/1073741824), by norm_num⟩
  | 4 => ⟨((-1021042555/2147483648), (-78167745/536870912)), (191/2147483648), by norm_num⟩
  | 5 => ⟨((1202558999/4294967296), (46032031/536870912)), (227/4294967296), by norm_num⟩
  | 6 => ⟨((-1180287197/8589934592), (-361436017/8589934592)), (7/268435456), by norm_num⟩
  | 7 => ⟨((248234545/4294967296), (19004041/1073741824)), (95/8589934592), by norm_num⟩
  | 8 => ⟨((-365455735/17179869184), (-447649913/68719476736)), (141/34359738368), by norm_num⟩
  | 9 => ⟨((478249827/68719476736), (146453095/68719476736)), (187/137438953472), by norm_num⟩
  | 10 => ⟨((-563270973/274877906944), (-344977761/549755813888)), (111/274877906944), by norm_num⟩
  | 11 => ⟨((301548547/549755813888), (184684721/1099511627776)), (15/137438953472), by norm_num⟩
  | 12 => ⟨((-1183855061/8796093022208), (-181264297/4398046511104)), (237/8796093022208), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581578604278889/10141204801825835211973625643008), (-3705191158407/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889560061513103/316912650057057350374175801344), (-4386596984395/633825300114114700748351602688)), (11579/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((472534129005051/9903520314283042199192993792), (-4934096573699/39614081257132168796771975168)), (52119/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944967741434071/1237940039285380274899124224), (-2620745116759/1237940039285380274899124224)), (110785/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885800431576659/77371252455336267181195264), (-1310094845015/38685626227668133590597632)), (55411/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387484260522845/2417851639229258349412352), (-4911675458049/9671406556917033397649408)), (51967/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629561712866903/302231454903657293676544), (-4296535894643/604462909807314587353088)), (90981/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118020892022205/4722366482869645213696), (-3489829126231/37778931862957161709568)), (147915/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297944612158071/4722366482869645213696), (-5232807855091/4722366482869645213696)), (13875/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1622002753253781/590295810358705651712), (-898995673735/73786976294838206464)), (152727/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912082118763331/36893488147419103232), (-8985239182637/73786976294838206464)), (191061/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911713824384971/4611686018427387904), (-10101908358985/9223372036854775808)), (53789/2305843009213693952), by norm_num⟩
  | 6 => ⟨((797334912900711/576460752303423488), (-10093802587901/1152921504606846976)), (215421/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195172124965915/144115188075855872), (-8822960180875/144115188075855872)), (23599/18014398509481984), by norm_num⟩
  | 4 => ⟨((93281891421897/2251799813685248), (-6608105453821/18014398509481984)), (283783/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490324012522599/9007199254740992), (-4122093285265/2251799813685248)), (355773/9007199254740992), by norm_num⟩
  | 2 => ⟨((557501701191885/1125899906842624), (-16440559399327/2251799813685248)), (11167/70368744177664), by norm_num⟩
  | 1 => ⟨((1109503998706149/1125899906842624), (-24541382693361/1125899906842624)), (539949/1125899906842624), by norm_num⟩
  | 0 => ⟨((1092906186898241/1125899906842624), (-24302707529163/562949953421312)), (1095687/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1092906186898241/1125899906842624), (-24302707529163/562949953421312)), (4179714207175826671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1058781015739161/1125899906842624), (-94362133811645/1125899906842624)), (2221761/1125899906842624), by norm_num⟩
  | 2 => ⟨((493877395420911/562949953421312), (-88736871969893/562949953421312)), (2275521/562949953421312), by norm_num⟩
  | 3 => ⟨((209646210845397/281474976710656), (-311396314645333/1125899906842624)), (2355007/281474976710656), by norm_num⟩
  | 4 => ⟨((538464272969665/1125899906842624), (-231932011148981/562949953421312)), (38486033/2251799813685248), by norm_num⟩
  | 5 => ⟨((66412601713411/1125899906842624), (-1774752458938569/4503599627370496)), (137048205/4503599627370496), by norm_num⟩
  | 6 => ⟨((-683714452131443/4503599627370496), (-209371947682129/4503599627370496)), (124182247/4503599627370496), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-61749361/33554432), (-170051951/4194304)), (1/16777216), by norm_num⟩, -6, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-62825059/33554432), (-346028647/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1270684133730559/9007199254740992), (275478553922425/4503599627370496)), (1915929/70368744177664), by norm_num⟩
  | 1 => ⟨((907571189/2147483648), (-393514631/2147483648)), (177/2147483648), by norm_num⟩
  | 2 => ⟨((-1359420151/2147483648), (36839515/134217728)), (267/2147483648), by norm_num⟩
  | 3 => ⟨((1357486273/2147483648), (-9196777/33554432)), (269/2147483648), by norm_num⟩
  | 4 => ⟨((-127083295/268435456), (440817307/2147483648)), (203/2147483648), by norm_num⟩
  | 5 => ⟨((1218264091/4294967296), (-528228253/4294967296)), (123/2147483648), by norm_num⟩
  | 6 => ⟨((-1216531019/8589934592), (527476809/8589934592)), (31/1073741824), by norm_num⟩
  | 7 => ⟨((130157187/2147483648), (-56434975/2147483648)), (107/8589934592), by norm_num⟩
  | 8 => ⟨((-194958043/8589934592), (42266019/4294967296)), (81/17179869184), by norm_num⟩
  | 9 => ⟨((1038297069/137438953472), (-225098093/68719476736)), (109/68719476736), by norm_num⟩
  | 10 => ⟨((-77761501/34359738368), (269733449/274877906944)), (263/549755813888), by norm_num⟩
  | 11 => ⟨((338840201/549755813888), (-36729509/137438953472)), (289/2199023255552), by norm_num⟩
  | 12 => ⟨((-1353432701/8796093022208), (73354517/1099511627776)), (145/4398046511104), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581536844765651/10141204801825835211973625643008), (3559344621897/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889535739657737/316912650057057350374175801344), (263356598257/39614081257132168796771975168)), (92615/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472520461787617/9903520314283042199192993792), (4739615613039/39614081257132168796771975168)), (52109/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889877466906423/2475880078570760549798248448), (5034876937937/2475880078570760549798248448)), (110763/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((13840179106173/1208925819614629174706176), (1258447923475/38685626227668133590597632)), (55399/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774941404444489/4835703278458516698824704), (589753342499/1208925819614629174706176)), (51955/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259076054905047/604462909807314587353088), (4127120535241/604462909807314587353088)), (45479/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((236032181339735/9444732965739290427392), (3352204744403/37778931862957161709568)), (147875/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297887132309997/4722366482869645213696), (1256604036101/1180591620717411303424)), (110967/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405480984980451/147573952589676412928), (6908249812295/590295810358705651712)), (76339/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824066052773255/73786976294838206464), (4315352231911/36893488147419103232)), (190995/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823317646850395/9223372036854775808), (9703208061675/9223372036854775808)), (215073/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797280196558143/576460752303423488), (9695291892271/1152921504606846976)), (215327/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597538505413003/72057594037927936), (8474477344085/144115188075855872)), (188697/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492368868136447/36028797018963968), (6346958245323/18014398509481984)), (283619/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490149498069881/9007199254740992), (15836261358783/9007199254740992)), (44441/1125899906842624), by norm_num⟩
  | 2 => ⟨((1114832220693981/2251799813685248), (15789589981559/2251799813685248)), (89259/562949953421312), by norm_num⟩
  | 1 => ⟨((277313880365273/281474976710656), (23567812327461/1125899906842624)), (134833/281474976710656), by norm_num⟩
  | 0 => ⟨((1092442193777097/1125899906842624), (46669975095151/1125899906842624)), (546915/562949953421312), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1092442193777097/1125899906842624), (46669975095151/1125899906842624)), (2086315157176780523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((33063881082183/35184372088832), (90566221147393/1125899906842624)), (2213333/1125899906842624), by norm_num⟩
  | 2 => ⟨((246748239036037/281474976710656), (170215956022735/1125899906842624)), (4515957/1125899906842624), by norm_num⟩
  | 3 => ⟨((839489920950447/1125899906842624), (149215706118061/562949953421312)), (9283075/1125899906842624), by norm_num⟩
  | 4 => ⟨((1093670966355627/2251799813685248), (890061935859991/2251799813685248)), (37528769/2251799813685248), by norm_num⟩
  | 5 => ⟨((358740533263827/4503599627370496), (1729167737899851/4503599627370496)), (132244535/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1270684133730559/9007199254740992), (275478553922425/4503599627370496)), (1915929/70368744177664), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-62825059/33554432), (-346028647/8388608)), (1/16777216), by norm_num⟩, -7, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-63848263/33554432), (-1406657049/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-632061878358655/9007199254740992), (1185411101677967/9007199254740992)), (119433191/4503599627370496), by norm_num⟩
  | 1 => ⟨((458795207/2147483648), (-430227601/1073741824)), (175/2147483648), by norm_num⟩
  | 2 => ⟨((-698406151/2147483648), (1309837585/2147483648)), (67/536870912), by norm_num⟩
  | 3 => ⟨((354385533/1073741824), (-1329276639/2147483648)), (137/1073741824), by norm_num⟩
  | 4 => ⟨((-539467353/2147483648), (1011753139/2147483648)), (211/2147483648), by norm_num⟩
  | 5 => ⟨((82121023/536870912), (-1232122053/4294967296)), (259/4294967296), by norm_num⟩
  | 6 => ⟨((-333359063/4294967296), (625203873/4294967296)), (265/8589934592), by norm_num⟩
  | 7 => ⟨((289976899/8589934592), (-543842063/8589934592)), (233/17179869184), by norm_num⟩
  | 8 => ⟨((-110355147/8589934592), (413934841/17179869184)), (179/34359738368), by norm_num⟩
  | 9 => ⟨((37330969/8589934592), (-1120207921/137438953472)), (61/34359738368), by norm_num⟩
  | 10 => ⟨((-363695913/274877906944), (341049815/137438953472)), (75/137438953472), by norm_num⟩
  | 11 => ⟨((201323703/549755813888), (-755151865/1099511627776)), (21/137438953472), by norm_num⟩
  | 12 => ⟨((-408623021/4398046511104), (191589733/1099511627776)), (43/1099511627776), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395374280778559/2535301200456458802993406410752), (2684227071663/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889514276263865/316912650057057350374175801344), (3177543830311/633825300114114700748351602688)), (92513/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890033797289719/39614081257132168796771975168), (1787065128295/19807040628566084398385987584)), (104097/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236228340756273/309485009821345068724781056), (474596891731/309485009821345068724781056)), (55313/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771492535663323/154742504910672534362390528), (3795944708081/154742504910672534362390528)), (110653/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774917970494001/4835703278458516698824704), (3557815993989/9671406556917033397649408)), (103765/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629517708957181/302231454903657293676544), (3112207001987/604462909807314587353088)), (45411/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472048028351511/18889465931478580854784), (1263920754541/18889465931478580854784)), (147637/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297838739405053/4722366482869645213696), (947578987489/1180591620717411303424)), (55387/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621858390129167/590295810358705651712), (651166859663/73786976294838206464)), (38097/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911992799794485/36893488147419103232), (3254072750591/36893488147419103232)), (47649/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823229174962763/9223372036854775808), (1829205360107/2305843009213693952)), (107287/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398618616177971/288230376151711744), (3655385821147/576460752303423488)), (214765/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597502339732937/72057594037927936), (6390123307093/144115188075855872)), (23517/18014398509481984), by norm_num⟩
  | 4 => ⟨((1492266069530657/36028797018963968), (4785795780603/18014398509481984)), (70659/9007199254740992), by norm_num⟩
  | 3 => ⟨((745015470802027/4503599627370496), (11940724321369/9007199254740992)), (177025/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114728516041619/2251799813685248), (5952561641849/1125899906842624)), (355187/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109136881247263/1125899906842624), (17768845720821/1125899906842624)), (535629/1125899906842624), by norm_num⟩
  | 0 => ⟨((546175653057525/562949953421312), (35183315654291/1125899906842624)), (1082685/1125899906842624), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((546175653057525/562949953421312), (35183315654291/1125899906842624)), (4130115513328170421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1058702912245147/1125899906842624), (68269906720571/1125899906842624)), (2168515/1125899906842624), by norm_num⟩
  | 2 => ⟨((991376826171759/1125899906842624), (256781437229041/2251799813685248)), (8682327/2251799813685248), by norm_num⟩
  | 3 => ⟨((1716571480237471/2251799813685248), (226101063436301/1125899906842624)), (4317519/562949953421312), by norm_num⟩
  | 4 => ⟨((1217750737233095/2251799813685248), (344718597796605/1125899906842624)), (16633311/1125899906842624), by norm_num⟩
  | 5 => ⟨((223730636542533/1125899906842624), (745681430566901/2251799813685248)), (56351103/2251799813685248), by norm_num⟩
  | 6 => ⟨((-632061878358655/9007199254740992), (1185411101677967/9007199254740992)), (119433191/4503599627370496), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-63848263/33554432), (-1406657049/33554432)), (1/16777216), by norm_num⟩, -7, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨37,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile037Terms2

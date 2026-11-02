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
namespace Reinmann.XiRectangle.Tile042Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨42,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (3525/256)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (3525/256))
  have he : value ((7/8), (3525/256))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-64510795/33554432), (-1015181035/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((262281349506215/4503599627370496), (302040650003417/2251799813685248)), (90793569/4503599627370496), by norm_num⟩
  | 1 => ⟨((-17174811/134217728), (-632907047/2147483648)), (193/4294967296), by norm_num⟩
  | 2 => ⟨((301895335/2147483648), (1390638919/4294967296)), (215/4294967296), by norm_num⟩
  | 3 => ⟨((-442221233/4294967296), (-1018515337/4294967296)), (5/134217728), by norm_num⟩
  | 4 => ⟨((485829681/8589934592), (559476733/4294967296)), (89/4294967296), by norm_num⟩
  | 5 => ⟨((-213495383/8589934592), (-983436823/17179869184)), (159/17179869184), by norm_num⟩
  | 6 => ⟨((312731535/34359738368), (360138593/17179869184)), (59/17179869184), by norm_num⟩
  | 7 => ⟨((-392652237/137438953472), (-14130453/2147483648)), (75/68719476736), by norm_num⟩
  | 8 => ⟨((431372573/549755813888), (248382229/137438953472)), (167/549755813888), by norm_num⟩
  | 9 => ⟨((-421254409/2199023255552), (-970224957/2199023255552)), (165/2199023255552), by norm_num⟩
  | 10 => ⟨((46279527/1099511627776), (852720849/8796093022208)), (147/8796093022208), by norm_num⟩
  | 11 => ⟨((-147907657/17592186044416), (-1362632151/70368744177664)), (237/70368744177664), by norm_num⟩
  | 12 => ⟨((433315119/281474976710656), (998002951/281474976710656)), (175/281474976710656), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581471403057283/10141204801825835211973625643008), (756279422259/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444750448119581/158456325028528675187087900672), (1790483935401/633825300114114700748351602688)), (92377/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890003907920813/39614081257132168796771975168), (2013953497133/39614081257132168796771975168)), (103935/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472448811699011/618970019642690137449562112), (2139405781917/2475880078570760549798248448)), (27611/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771461369169515/154742504910672534362390528), (2138933630675/154742504910672534362390528)), (110459/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193725881814631/1208925819614629174706176), (501187186949/2417851639229258349412352)), (103571/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629505237077289/302231454903657293676544), (438413442325/151115727451828646838272)), (5665/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1888152201657195/75557863725914323419136), (1424373794115/37778931862957161709568)), (147319/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297809349265819/4722366482869645213696), (2135738687585/4722366482869645213696)), (27629/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621818861301229/590295810358705651712), (1467652760257/295147905179352825856)), (2375/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1823937510980491/73786976294838206464), (916782538613/18446744073709551616)), (190063/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911588445594443/4611686018427387904), (1030692668313/2305843009213693952)), (213907/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594424447190867/1152921504606846976), (514916838687/144115188075855872)), (214015/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597481729337841/72057594037927936), (1800277905803/72057594037927936)), (187385/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492209314957343/36028797018963968), (5393118092337/36028797018963968)), (281321/36028797018963968), by norm_num⟩
  | 3 => ⟨((744984427221685/4503599627370496), (3363957181525/4503599627370496)), (176039/4503599627370496), by norm_num⟩
  | 2 => ⟨((2229359314075747/4503599627370496), (3353863810649/1125899906842624)), (705437/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218192935705183/2251799813685248), (1251407231081/140737488355328)), (530685/1125899906842624), by norm_num⟩
  | 0 => ⟨((2184801623565525/2251799813685248), (19821979330263/1125899906842624)), (1067821/1125899906842624), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2184801623565525/2251799813685248), (19821979330263/1125899906842624)), (4073413853171920421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2119098892306449/2251799813685248), (76928850175479/2251799813685248)), (4219399/2251799813685248), by norm_num⟩
  | 2 => ⟨((497897508487399/562949953421312), (144790704930801/2251799813685248)), (8229789/2251799813685248), by norm_num⟩
  | 3 => ⟨((219017388397191/281474976710656), (64029609380949/562949953421312)), (15615921/2251799813685248), by norm_num⟩
  | 4 => ⟨((1334219311415745/2251799813685248), (99643655649883/562949953421312)), (27853979/2251799813685248), by norm_num⟩
  | 5 => ⟨((359996352988633/1125899906842624), (236160406125191/1125899906842624)), (10717029/562949953421312), by norm_num⟩
  | 6 => ⟨((262281349506215/4503599627370496), (302040650003417/2251799813685248)), (90793569/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-64510795/33554432), (-1015181035/33554432)), (1/16777216), by norm_num⟩, -5, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-67604193/33554432), (-265965157/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((575557622697611/4503599627370496), (-171497341413205/4503599627370496)), (96189283/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1263876345/4294967296), (376593801/4294967296)), (27/1073741824), by norm_num⟩
  | 2 => ⟨((181886427/536870912), (-108392409/1073741824)), (127/4294967296), by norm_num⟩
  | 3 => ⟨((-1116823935/4294967296), (166388497/2147483648)), (25/1073741824), by norm_num⟩
  | 4 => ⟨((40180971/268435456), (-383123673/8589934592)), (117/8589934592), by norm_num⟩
  | 5 => ⟨((-592128671/8589934592), (352869943/17179869184)), (55/8589934592), by norm_num⟩
  | 6 => ⟨((908951101/34359738368), (-135418845/17179869184)), (43/17179869184), by norm_num⟩
  | 7 => ⟨((-597982073/68719476736), (356358187/137438953472)), (115/137438953472), by norm_num⟩
  | 8 => ⟨((1376904607/549755813888), (-410272525/549755813888)), (135/549755813888), by norm_num⟩
  | 9 => ⟨((-1409084455/2199023255552), (419861067/2199023255552)), (141/2199023255552), by norm_num⟩
  | 10 => ⟨((1297814745/8796093022208), (-193353167/4398046511104)), (133/8796093022208), by norm_num⟩
  | 11 => ⟨((-1086665049/35184372088832), (323790633/35184372088832)), (57/17592186044416), by norm_num⟩
  | 12 => ⟨((104255781/17592186044416), (-248518495/140737488355328)), (89/140737488355328), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581351314710245/10141204801825835211973625643008), (-23576528007/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444715314452879/158456325028528675187087900672), (-446469623019/633825300114114700748351602688)), (23061/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889845925448051/39614081257132168796771975168), (-502189901111/39614081257132168796771975168)), (51889/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944813771404701/1237940039285380274899124224), (-533467131533/2475880078570760549798248448)), (27567/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885646918254247/77371252455336267181195264), (-533343832907/154742504910672534362390528)), (110271/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549650174585567/9671406556917033397649408), (-249939439319/4835703278458516698824704)), (103383/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314718346511393/151115727451828646838272), (-437263099193/604462909807314587353088)), (2827/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((943964887092803/37778931862957161709568), (-355153578851/37778931862957161709568)), (147011/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648821413275981/2361183241434822606848), (-266257878925/2361183241434822606848)), (110265/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810795188107175/295147905179352825856), (-731860604537/590295810358705651712)), (151625/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823652629343443/73786976294838206464), (-914303225741/73786976294838206464)), (189547/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822857394629043/9223372036854775808), (-1027873159927/9223372036854775808)), (106631/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594106192919765/1152921504606846976), (-1026976462467/1152921504606846976)), (213289/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194686381272731/144115188075855872), (-448798334647/72057594037927936)), (186659/144115188075855872), by norm_num⟩
  | 4 => ⟨((745898241402099/18014398509481984), (-168047769181/4503599627370496)), (140025/18014398509481984), by norm_num⟩
  | 3 => ⟨((744728836101559/4503599627370496), (-1676961090861/9007199254740992)), (350171/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228351467720469/4503599627370496), (-1671697943989/2251799813685248)), (700669/4503599627370496), by norm_num⟩
  | 1 => ⟨((1108358633500977/1125899906842624), (-4988860197305/2251799813685248)), (1051829/2251799813685248), by norm_num⟩
  | 0 => ⟨((2181993527092559/2251799813685248), (-9873276999955/2251799813685248)), (1053499/1125899906842624), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2181993527092559/2251799813685248), (-9873276999955/2251799813685248)), (4018779758933639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2114307960121623/2251799813685248), (-4783601627055/562949953421312)), (4101839/2251799813685248), by norm_num⟩
  | 2 => ⟨((1985048580941945/2251799813685248), (-4491521376219/281474976710656)), (1943121/562949953421312), by norm_num⟩
  | 3 => ⟨((1749323684923601/2251799813685248), (-63351195465585/2251799813685248)), (1743943/281474976710656), by norm_num⟩
  | 4 => ⟨((1357189907421737/2251799813685248), (-49214741924507/1125899906842624)), (11230845/1125899906842624), by norm_num⟩
  | 5 => ⟨((1627388074535787/4503599627370496), (-237299072965081/4503599627370496)), (58079181/4503599627370496), by norm_num⟩
  | 6 => ⟨((575557622697611/4503599627370496), (-171497341413205/4503599627370496)), (96189283/9007199254740992), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-67604193/33554432), (-265965157/8388608)), (1/16777216), by norm_num⟩, -5, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-4400157/2097152), (-1107896675/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-34439102566161/9007199254740992), (-1104485836523029/9007199254740992)), (179432167/9007199254740992), by norm_num⟩
  | 1 => ⟨((19688931/2147483648), (1262875255/4294967296)), (207/4294967296), by norm_num⟩
  | 2 => ⟨((-47211995/4294967296), (-757060651/2147483648)), (125/2147483648), by norm_num⟩
  | 3 => ⟨((37736473/4294967296), (1210234771/4294967296)), (101/2147483648), by norm_num⟩
  | 4 => ⟨((-45244055/8589934592), (-725504059/4294967296)), (61/2147483648), by norm_num⟩
  | 5 => ⟨((21698101/8589934592), (1391746203/17179869184)), (59/4294967296), by norm_num⟩
  | 6 => ⟨((-8671629/8589934592), (-1112420547/34359738368)), (95/17179869184), by norm_num⟩
  | 7 => ⟨((23764181/68719476736), (381066853/34359738368)), (263/137438953472), by norm_num⟩
  | 8 => ⟨((-56984017/549755813888), (-1827516811/549755813888)), (159/274877906944), by norm_num⟩
  | 9 => ⟨((60729647/2199023255552), (1947641743/2199023255552)), (341/2199023255552), by norm_num⟩
  | 10 => ⟨((-58249333/8796093022208), (-1868096371/8796093022208)), (165/4398046511104), by norm_num⟩
  | 11 => ⟨((1587225/1099511627776), (814454447/17592186044416)), (145/17592186044416), by norm_num⟩
  | 12 => ⟨((-20298663/70368744177664), (-162748039/17592186044416)), (117/70368744177664), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581242681581499/10141204801825835211973625643008), (-2086741327065/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778729534436655/633825300114114700748351602688), (-617363482957/158456325028528675187087900672)), (23111/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889697584678137/39614081257132168796771975168), (-2777622386547/39614081257132168796771975168)), (52007/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889469730949567/2475880078570760549798248448), (-368823966113/309485009821345068724781056)), (110533/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771135800088635/154742504910672534362390528), (-1474940429245/77371252455336267181195264)), (55277/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549501777013307/9671406556917033397649408), (-2764758200783/9671406556917033397649408)), (51833/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258743299928459/604462909807314587353088), (-151150533863/37778931862957161709568)), (45365/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471929484485095/18889465931478580854784), (-1964249470465/37778931862957161709568)), (147475/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324370889812165/1180591620717411303424), (-736284150319/1180591620717411303424)), (55321/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810685375236455/295147905179352825856), (-1011888149039/147573952589676412928)), (76095/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823377148669467/73786976294838206464), (-2528213466413/36893488147419103232)), (190325/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455636544200181/2305843009213693952), (-2842169399235/4611686018427387904)), (107117/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796896675335213/576460752303423488), (-1419791414301/288230376151711744)), (214383/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597205410589507/72057594037927936), (-4963455298999/144115188075855872)), (187753/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491379507264881/36028797018963968), (-7433566470573/36028797018963968)), (140983/18014398509481984), by norm_num⟩
  | 3 => ⟨((372232528799947/2251799813685248), (-9271658084271/9007199254740992)), (176523/4503599627370496), by norm_num⟩
  | 2 => ⟨((2227277438205239/4503599627370496), (-4620632844113/1125899906842624)), (707861/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215059273156575/2251799813685248), (-13786118929283/1125899906842624)), (1066227/2251799813685248), by norm_num⟩
  | 0 => ⟨((1089245883752839/1125899906842624), (-54540651575549/2251799813685248)), (1075129/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1089245883752839/1125899906842624), (-54540651575549/2251799813685248)), (4101291660789107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((526562315796367/562949953421312), (-105530127260537/2251799813685248)), (4264675/2251799813685248), by norm_num⟩
  | 2 => ⟨((1965161078714007/2251799813685248), (-197417862312199/2251799813685248)), (4188881/1125899906842624), by norm_num⟩
  | 3 => ⟨((1697701647233033/2251799813685248), (-172287916936955/1125899906842624)), (8045819/1125899906842624), by norm_num⟩
  | 4 => ⟨((613611023709349/1125899906842624), (-519572794356933/2251799813685248)), (7297183/562949953421312), by norm_num⟩
  | 5 => ⟨((1097893389565269/4503599627370496), (-1132660522660291/4503599627370496)), (45285311/2251799813685248), by norm_num⟩
  | 6 => ⟨((-34439102566161/9007199254740992), (-1104485836523029/9007199254740992)), (179432167/9007199254740992), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4400157/2097152), (-1107896675/33554432)), (1/16777216), by norm_num⟩, -5, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-72957177/33554432), (-1148098437/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-964874624466545/9007199254740992), (-171481070327697/4503599627370496)), (45061829/2251799813685248), by norm_num⟩
  | 1 => ⟨((571637957/2147483648), (406374409/4294967296)), (27/536870912), by norm_num⟩
  | 2 => ⟨((-88779185/268435456), (-504901235/4294967296)), (271/4294967296), by norm_num⟩
  | 3 => ⟨((1176575931/4294967296), (104552703/1073741824)), (113/2147483648), by norm_num⟩
  | 4 => ⟨((-1461840677/8589934592), (-259803707/4294967296)), (283/8589934592), by norm_num⟩
  | 5 => ⟨((1453015047/17179869184), (516470367/17179869184)), (71/4294967296), by norm_num⟩
  | 6 => ⟨((-37610487/1073741824), (-213896775/17179869184)), (237/34359738368), by norm_num⟩
  | 7 => ⟨((213619541/17179869184), (303722011/68719476736)), (85/34359738368), by norm_num⟩
  | 8 => ⟨((-265412309/68719476736), (-188680211/137438953472)), (213/274877906944), by norm_num⟩
  | 9 => ⟨((586244277/549755813888), (416757965/1099511627776)), (119/549755813888), by norm_num⟩
  | 10 => ⟨((-582704921/2199023255552), (-414241855/4398046511104)), (239/4398046511104), by norm_num⟩
  | 11 => ⟨((1053067151/17592186044416), (187154971/8796093022208)), (109/8796093022208), by norm_num⟩
  | 12 => ⟨((-872257855/70368744177664), (-310041755/70368744177664)), (183/70368744177664), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790571753654357/5070602400912917605986812821504), (-3647407994141/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778605469674555/633825300114114700748351602688), (-67434494801/9903520314283042199192993792)), (92625/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944778830266927/19807040628566084398385987584), (-2427168801961/19807040628566084398385987584)), (52115/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889320599469883/2475880078570760549798248448), (-5156586955373/2475880078570760549798248448)), (110777/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770986149212471/154742504910672534362390528), (-5155296948461/154742504910672534362390528)), (27703/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774680463923329/4835703278458516698824704), (-4831720464195/9671406556917033397649408)), (25981/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258619505874255/604462909807314587353088), (-1056596303491/151115727451828646838272)), (22743/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((58984866885707/2361183241434822606848), (-6865307357275/75557863725914323419136)), (36975/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324332752187647/1180591620717411303424), (-2573366737395/2361183241434822606848)), (110987/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810579764519487/295147905179352825856), (-7073108012165/590295810358705651712)), (38177/147573952589676412928), by norm_num⟩
  | 8 => ⟨((113944433010499/4611686018427387904), (-8835910869769/73786976294838206464)), (47759/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822243667322227/9223372036854775808), (-9932875426905/9223372036854775808)), (53781/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796743542160525/576460752303423488), (-9923474027367/1152921504606846976)), (215385/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597069310902031/72057594037927936), (-4336234338163/72057594037927936)), (188755/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490962800933895/36028797018963968), (-12987574534943/36028797018963968)), (35465/4503599627370496), by norm_num⟩
  | 3 => ⟨((1488394576562389/9007199254740992), (-8098762127157/4503599627370496)), (11115/281474976710656), by norm_num⟩
  | 2 => ⟨((278270327664291/562949953421312), (-4035542598271/562949953421312)), (357227/2251799813685248), by norm_num⟩
  | 1 => ⟨((553319623321281/562949953421312), (-24075088691753/1125899906842624)), (67465/140737488355328), by norm_num⟩
  | 0 => ⟨((1087250370577347/1125899906842624), (-371865797175/8796093022208)), (547505/562949953421312), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((1087250370577347/1125899906842624), (-371865797175/8796093022208)), (2088565828563499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((523957641922983/562949953421312), (-45964864714683/562949953421312)), (551857/281474976710656), by norm_num⟩
  | 2 => ⟨((967826145417141/1125899906842624), (-42781142410345/281474976710656)), (2234769/562949953421312), by norm_num⟩
  | 3 => ⟨((1611872998484737/2251799813685248), (-588396292123803/2251799813685248)), (18085387/2251799813685248), by norm_num⟩
  | 4 => ⟨((1000055312631759/2251799813685248), (-210591565448869/562949953421312)), (17671519/1125899906842624), by norm_num⟩
  | 5 => ⟨((258042218092421/4503599627370496), (-1496425837093655/4503599627370496)), (14458829/562949953421312), by norm_num⟩
  | 6 => ⟨((-964874624466545/9007199254740992), (-171481070327697/4503599627370496)), (45061829/2251799813685248), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-72957177/33554432), (-1148098437/33554432)), (1/16777216), by norm_num⟩, -5, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-75307241/33554432), (-592540237/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-345810694070949/4503599627370496), (658183907839247/9007199254740992)), (174189855/9007199254740992), by norm_num⟩
  | 1 => ⟨((422948321/2147483648), (-201250123/1073741824)), (215/4294967296), by norm_num⟩
  | 2 => ⟨((-16950641/67108864), (258098187/1073741824)), (279/4294967296), by norm_num⟩
  | 3 => ⟨((927520763/4294967296), (-220669593/1073741824)), (241/4294967296), by norm_num⟩
  | 4 => ⟨((-297380473/2147483648), (566006331/4294967296)), (39/1073741824), by norm_num⟩
  | 5 => ⟨((610212683/8589934592), (-290355515/4294967296)), (81/4294967296), by norm_num⟩
  | 6 => ⟨((-521721543/17179869184), (31031133/1073741824)), (35/4294967296), by norm_num⟩
  | 7 => ⟨((764679621/68719476736), (-727710031/68719476736)), (207/68719476736), by norm_num⟩
  | 8 => ⟨((-980682251/274877906944), (116658711/34359738368)), (67/68719476736), by norm_num⟩
  | 9 => ⟨((558977847/549755813888), (-531953219/549755813888)), (155/549755813888), by norm_num⟩
  | 10 => ⟨((-143374987/549755813888), (545773227/2199023255552)), (5/68719476736), by norm_num⟩
  | 11 => ⟨((534908481/8796093022208), (-509047523/8796093022208)), (301/17592186044416), by norm_num⟩
  | 12 => ⟨((-914675443/70368744177664), (435227039/35184372088832)), (65/17592186044416), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581052275821141/10141204801825835211973625643008), (3101468191523/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222312536023995/79228162514264337593543950336), (1834699160399/316912650057057350374175801344)), (46281/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236179938902541/4951760157141521099596496896), (4127251341311/39614081257132168796771975168)), (104155/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889195297908167/2475880078570760549798248448), (4384199041961/2475880078570760549798248448)), (27673/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885430554290647/77371252455336267181195264), (2191534023861/77371252455336267181195264)), (55361/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774621989666435/4835703278458516698824704), (4107924873131/9671406556917033397649408)), (51917/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258517452821975/604462909807314587353088), (3593233134301/604462909807314587353088)), (90887/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471837605732823/18889465931478580854784), (1459188086365/18889465931478580854784)), (147751/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648603737128609/2361183241434822606848), (2187797409491/2361183241434822606848)), (55433/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620990405434801/590295810358705651712), (6013243699375/590295810358705651712)), (152527/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822900626891135/73786976294838206464), (3755878947717/36893488147419103232)), (190787/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822008593281561/9223372036854775808), (8444135439739/9223372036854775808)), (214813/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796626950418489/576460752303423488), (8435900163947/1152921504606846976)), (107517/576460752303423488), by norm_num⟩
  | 5 => ⟨((74621044307661/9007199254740992), (7372154786347/144115188075855872)), (188405/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490664166431303/36028797018963968), (2759933384891/9007199254740992)), (141553/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488028670733483/9007199254740992), (13767332732101/9007199254740992)), (177379/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112726438563941/2251799813685248), (3429727081141/562949953421312)), (356075/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106134357851529/1125899906842624), (5114392666453/281474976710656)), (268705/562949953421312), by norm_num⟩
  | 0 => ⟨((1086349282506441/1125899906842624), (40433590128681/1125899906842624)), (272015/281474976710656), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1086349282506441/1125899906842624), (40433590128681/1125899906842624)), (1037654877782726199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((261683983014197/281474976710656), (78026477058039/1125899906842624)), (2177827/1125899906842624), by norm_num⟩
  | 2 => ⟨((967730766931311/1125899906842624), (290161200625697/2251799813685248)), (2175627/562949953421312), by norm_num⟩
  | 3 => ⟨((813086892639993/1125899906842624), (498797307840021/2251799813685248)), (4300671/562949953421312), by norm_num⟩
  | 4 => ⟨((1063878951878377/2251799813685248), (180107286013625/562949953421312)), (32467547/2251799813685248), by norm_num⟩
  | 5 => ⟨((544293741319577/4503599627370496), (680743819251839/2251799813685248)), (102908097/4503599627370496), by norm_num⟩
  | 6 => ⟨((-345810694070949/4503599627370496), (658183907839247/9007199254740992)), (174189855/9007199254740992), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-75307241/33554432), (-592540237/16777216)), (1/16777216), by norm_num⟩, -6, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-77483061/33554432), (-1219320491/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((186764202145045/9007199254740992), (109386976147251/1125899906842624)), (33663511/2251799813685248), by norm_num⟩
  | 1 => ⟨((-235024183/4294967296), (-1101221089/4294967296)), (43/1073741824), by norm_num⟩
  | 2 => ⟨((155060573/2147483648), (1453092793/4294967296)), (229/4294967296), by norm_num⟩
  | 3 => ⟨((-272809161/4294967296), (-639132531/2147483648)), (203/4294967296), by norm_num⟩
  | 4 => ⟨((89994877/2147483648), (843353695/4294967296)), (135/4294967296), by norm_num⟩
  | 5 => ⟨((-5937541/268435456), (-222565875/2147483648)), (9/536870912), by norm_num⟩
  | 6 => ⟨((334282903/34359738368), (391576069/8589934592)), (1/134217728), by norm_num⟩
  | 7 => ⟨((-984589/268435456), (-147627385/8589934592)), (195/68719476736), by norm_num⟩
  | 8 => ⟨((332593513/274877906944), (1558388529/274877906944)), (65/68719476736), by norm_num⟩
  | 9 => ⟨((-195051855/549755813888), (-913928149/549755813888)), (77/274877906944), by norm_num⟩
  | 10 => ⟨((205901211/2199023255552), (120595439/274877906944)), (41/549755813888), by norm_num⟩
  | 11 => ⟨((-98797291/4398046511104), (-925842261/8796093022208)), (159/8796093022208), by norm_num⟩
  | 12 => ⟨((347642287/70368744177664), (203612567/8796093022208)), (141/35184372088832), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580967808634167/10141204801825835211973625643008), (1772241546881/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444601303935677/158456325028528675187087900672), (2096543836601/633825300114114700748351602688)), (92407/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889332848996537/39614081257132168796771975168), (2358136162105/39614081257132168796771975168)), (103971/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944541176822621/1237940039285380274899124224), (626232344307/618970019642690137449562112)), (110485/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((55335893636179/4835703278458516698824704), (1252132765979/77371252455336267181195264)), (55251/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387284739465979/2417851639229258349412352), (1173521910557/4835703278458516698824704)), (51807/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258426017438493/604462909807314587353088), (2052958476437/604462909807314587353088)), (90681/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943601349608523/37778931862957161709568), (208421026591/4722366482869645213696)), (73695/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648548716094153/2361183241434822606848), (1249948442209/2361183241434822606848)), (110573/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810420158078633/295147905179352825856), (3435481621919/590295810358705651712)), (76043/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911357420394293/36893488147419103232), (4291538862869/73786976294838206464)), (190181/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821802090144967/9223372036854775808), (4824115923749/9223372036854775808)), (26757/1152921504606846976), by norm_num⟩
  | 6 => ⟨((199131315594133/144115188075855872), (1204822126505/288230376151711744)), (214183/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596881132454699/72057594037927936), (1052863093239/36028797018963968)), (5861/4503599627370496), by norm_num⟩
  | 4 => ⟨((372602375218681/9007199254740992), (6306342843627/36028797018963968)), (281615/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487722545445625/9007199254740992), (1965999616737/2251799813685248)), (352519/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112438535147899/2251799813685248), (489729254345/140737488355328)), (44159/281474976710656), by norm_num⟩
  | 1 => ⟨((2211495499721689/2251799813685248), (11682902247077/1125899906842624)), (531797/1125899906842624), by norm_num⟩
  | 0 => ⟨((2171510433249009/2251799813685248), (46169516856615/2251799813685248)), (2142363/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2171510433249009/2251799813685248), (46169516856615/2251799813685248)), (8172466286666106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2093137191315775/2251799813685248), (89046625675065/2251799813685248)), (4219803/2251799813685248), by norm_num⟩
  | 2 => ⟨((1942132676957609/2251799813685248), (82772368497809/1125899906842624)), (4089345/1125899906842624), by norm_num⟩
  | 3 => ⟨((831440311035343/1125899906842624), (17847381529187/140737488355328)), (1913807/281474976710656), by norm_num⟩
  | 4 => ⟨((595885237204865/1125899906842624), (105437667129093/562949953421312)), (13247841/1125899906842624), by norm_num⟩
  | 5 => ⟨((275877817763789/1125899906842624), (55803139253949/281474976710656)), (75941643/4503599627370496), by norm_num⟩
  | 6 => ⟨((186764202145045/9007199254740992), (109386976147251/1125899906842624)), (33663511/2251799813685248), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-77483061/33554432), (-1219320491/33554432)), (1/16777216), by norm_num⟩, -6, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-79508701/33554432), (-1251197185/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1544778991463065/18014398509481984), (672382709209839/18014398509481984)), (4668155/562949953421312), by norm_num⟩
  | 1 => ⟨((-498692877/2147483648), (-434123547/4294967296)), (49/2147483648), by norm_num⟩
  | 2 => ⟨((675242673/2147483648), (587814179/4294967296)), (135/4294967296), by norm_num⟩
  | 3 => ⟨((-38095647/134217728), (-265305051/2147483648)), (31/1073741824), by norm_num⟩
  | 4 => ⟨((206329849/1073741824), (179614849/2147483648)), (43/2147483648), by norm_num⟩
  | 5 => ⟨((-447001271/4294967296), (-194562411/4294967296)), (95/8589934592), by norm_num⟩
  | 6 => ⟨((403500627/8589934592), (351256517/17179869184)), (11/2147483648), by norm_num⟩
  | 7 => ⟨((-1248799947/68719476736), (-271777223/34359738368)), (139/68719476736), by norm_num⟩
  | 8 => ⟨((845453237/137438953472), (183996591/68719476736)), (3/4294967296), by norm_num⟩
  | 9 => ⟨((-254392201/137438953472), (-442908449/549755813888)), (117/549755813888), by norm_num⟩
  | 10 => ⟨((551125481/1099511627776), (239883663/1099511627776)), (129/2199023255552), by norm_num⟩
  | 11 => ⟨((-1085436705/8796093022208), (-472448729/8796093022208)), (129/8796093022208), by norm_num⟩
  | 12 => ⟨((1913683/68719476736), (426471625/35184372088832)), (59/17592186044416), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580889171562799/10141204801825835211973625643008), (534761115491/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((55572322931333/19807040628566084398385987584), (632553941911/633825300114114700748351602688)), (92263/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118076921710319/2475880078570760549798248448), (711477008875/39614081257132168796771975168)), (12975/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944487027141601/1237940039285380274899124224), (755761676567/2475880078570760549798248448)), (27573/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885320251693257/77371252455336267181195264), (755556291149/154742504910672534362390528)), (110297/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96814864990621/604462909807314587353088), (708115879183/9671406556917033397649408)), (103409/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258337758161005/604462909807314587353088), (154845834641/151115727451828646838272)), (90489/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943529844071973/37778931862957161709568), (1006089257703/75557863725914323419136)), (73527/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296990532511367/4722366482869645213696), (377104773081/2361183241434822606848)), (27575/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620693911228577/590295810358705651712), (1036457705913/590295810358705651712)), (75839/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822532706693819/73786976294838206464), (1294702114821/73786976294838206464)), (189619/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113849899159613/576460752303423488), (1455344599567/9223372036854775808)), (26669/1152921504606846976), by norm_num⟩
  | 6 => ⟨((199106039376133/144115188075855872), (1453851990503/1152921504606846976)), (213391/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596793504103465/72057594037927936), (1270443353605/144115188075855872)), (186761/144115188075855872), by norm_num⟩
  | 4 => ⟨((745074980049339/18014398509481984), (951157932637/18014398509481984)), (280229/36028797018963968), by norm_num⟩
  | 3 => ⟨((743701975463337/4503599627370496), (593011318485/2251799813685248)), (43805/1125899906842624), by norm_num⟩
  | 2 => ⟨((1112128645851767/2251799813685248), (2363293853927/2251799813685248)), (701343/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105304532654877/1125899906842624), (3523142231037/1125899906842624)), (1053185/2251799813685248), by norm_num⟩
  | 0 => ⟨((542477187698851/562949953421312), (869946076029/140737488355328)), (1055551/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((542477187698851/562949953421312), (869946076029/140737488355328)), (4026607517722701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1045454888081747/1125899906842624), (26825881648953/2251799813685248)), (4094755/2251799813685248), by norm_num⟩
  | 2 => ⟨((1941195677148601/2251799813685248), (12454592511535/562949953421312)), (7701937/2251799813685248), by norm_num⟩
  | 3 => ⟨((104520802762419/140737488355328), (85893252134067/2251799813685248)), (851245/140737488355328), by norm_num⟩
  | 4 => ⟨((19354792012313/35184372088832), (63789909638441/1125899906842624)), (166165/17592186044416), by norm_num⟩
  | 5 => ⟨((674179667897285/2251799813685248), (140362366611983/2251799813685248)), (51620419/4503599627370496), by norm_num⟩
  | 6 => ⟨((1544778991463065/18014398509481984), (672382709209839/18014398509481984)), (4668155/562949953421312), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-79508701/33554432), (-1251197185/33554432)), (1/16777216), by norm_num⟩, -6, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨42,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile042Terms1
